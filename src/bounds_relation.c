/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds_relation.h"
#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>

#define BOUNDS_RELATION_WALK_INIT_CAP 16u
#define BOUNDS_RELATION_PROJECTION_INIT_CAP 64u

enum {
  BOUNDS_PROJECTION_COMPLETE_RANGE = 1u << 0,
  BOUNDS_PROJECTION_COMPLETE_INTEGER = 1u << 1,
  BOUNDS_PROJECTION_COMPLETE_DEFINED_COMPONENT = 1u << 2,
  BOUNDS_PROJECTION_COMPLETE_DEFINED_WITH_EQUALITY = 1u << 3,
  BOUNDS_PROJECTION_COMPLETE_DEFINED_WITHOUT_EQUALITY = 1u << 4
};

typedef struct {
  size_t endpoint_index;
  size_t defined_component;
  ixs_relation_offset defined_offset;
  ixs_interval range;
  ixs_check_result integer;
  ixs_check_result defined_with_equality;
  ixs_check_result defined_without_equality;
  uint8_t completion;
  uint32_t generation;
} bounds_equality_projection_cache_entry;

typedef struct {
  uint64_t lo;
  uint64_t mid;
  uint64_t hi;
  bool negative;
} bounds_relation_projection_integer;

IXS_STATIC void bounds_relation_projection_reset(ixs_bounds *b,
                                                 bool transient) {
  b->equality_projection_cache = NULL;
  b->equality_projection_cache_count = 0;
  b->equality_projection_cache_capacity = 0;
  b->equality_projection_cache_generation = 1u;
  b->equality_projection_cache_transient = transient;
}

IXS_STATIC void bounds_relation_init(ixs_bounds *b, ixs_arena *arena,
                                     bool transient) {
  ixs_relation_algebra_init(&b->relations, arena);
  bounds_relation_projection_reset(b, transient);
}

IXS_STATIC ixs_relation_status
bounds_relation_clone_fork(ixs_bounds *dst, const ixs_bounds *src) {
  return ixs_relation_algebra_clone(&dst->relations, &src->relations,
                                    dst->scratch);
}

IXS_STATIC void bounds_relation_destroy(ixs_bounds *b) {
  bounds_relation_projection_reset(b, false);
}

IXS_STATIC void bounds_relation_projection_invalidate(ixs_bounds *b) {
  bounds_equality_projection_cache_entry *cache;
  if (!b)
    return;
  b->equality_projection_cache_count = 0;
  b->equality_projection_cache_generation++;
  if (b->equality_projection_cache_generation != 0)
    return;
  /* Zero denotes a cleared slot. Only generation wrap touches retained rows. */
  cache =
      (bounds_equality_projection_cache_entry *)b->equality_projection_cache;
  if (cache)
    memset(cache, 0, b->equality_projection_cache_capacity * sizeof(*cache));
  b->equality_projection_cache_generation = 1u;
}

IXS_STATIC void bounds_relation_projection_commit(ixs_bounds *destination,
                                                  ixs_bounds *candidate) {
  void *cache = destination->equality_projection_cache;
  size_t capacity = destination->equality_projection_cache_capacity;
  uint32_t generation = destination->equality_projection_cache_generation;
  bounds_relation_projection_reset(destination, false);
  bounds_relation_projection_reset(candidate, false);
  candidate->equality_projection_cache = cache;
  candidate->equality_projection_cache_capacity = capacity;
  candidate->equality_projection_cache_generation = generation;
}

/* Pointer-index hashing and 75%-load growth keep lookup expected O(1). */
static size_t bounds_relation_projection_hash(size_t endpoint_index) {
  uint64_t mixed = (uint64_t)endpoint_index;
  mixed ^= mixed >> 33;
  mixed *= UINT64_C(0xff51afd7ed558ccd);
  mixed ^= mixed >> 33;
  return (size_t)mixed;
}

static size_t bounds_relation_projection_probe(const ixs_bounds *b,
                                               size_t endpoint_index,
                                               bool *found) {
  const bounds_equality_projection_cache_entry *cache =
      (const bounds_equality_projection_cache_entry *)
          b->equality_projection_cache;
  size_t slot;
  if (!b->equality_projection_cache_capacity) {
    *found = false;
    return SIZE_MAX;
  }
  slot = bounds_relation_projection_hash(endpoint_index) &
         (b->equality_projection_cache_capacity - 1u);
  while (cache[slot].generation == b->equality_projection_cache_generation) {
    const bounds_equality_projection_cache_entry *entry = &cache[slot];
    if (entry->endpoint_index == endpoint_index) {
      *found = true;
      return slot;
    }
    slot = (slot + 1u) & (b->equality_projection_cache_capacity - 1u);
  }
  *found = false;
  return slot;
}

static bool bounds_relation_projection_grow(ixs_bounds *b) {
  bounds_equality_projection_cache_entry *grown;
  bounds_equality_projection_cache_entry *cache =
      (bounds_equality_projection_cache_entry *)b->equality_projection_cache;
  ixs_arena *arena;
  size_t capacity = b->equality_projection_cache_capacity
                        ? b->equality_projection_cache_capacity * 2u
                        : BOUNDS_RELATION_PROJECTION_INIT_CAP;
  size_t bytes;
  size_t i;
  if (capacity < b->equality_projection_cache_capacity ||
      capacity > SIZE_MAX / sizeof(*grown))
    return false;
  bytes = capacity * sizeof(*grown);
  arena = b->equality_projection_cache_transient ? &b->query_arena
          : b->store_ctx                         ? &b->store_ctx->arena
                                                 : &b->query_arena;
  grown = ixs_arena_alloc(arena, bytes, sizeof(void *));
  if (!grown)
    return false;
  memset(grown, 0, bytes);
  for (i = 0; i < b->equality_projection_cache_capacity; i++) {
    bounds_equality_projection_cache_entry entry = cache[i];
    size_t slot;
    if (entry.generation != b->equality_projection_cache_generation)
      continue;
    slot =
        bounds_relation_projection_hash(entry.endpoint_index) & (capacity - 1u);
    while (grown[slot].generation == b->equality_projection_cache_generation)
      slot = (slot + 1u) & (capacity - 1u);
    grown[slot] = entry;
  }
  b->equality_projection_cache = grown;
  b->equality_projection_cache_capacity = capacity;
  return true;
}

static bounds_equality_projection_cache_entry *
bounds_relation_projection_row(ixs_bounds *b, size_t endpoint_index) {
  bounds_equality_projection_cache_entry *cache =
      (bounds_equality_projection_cache_entry *)b->equality_projection_cache;
  bounds_equality_projection_cache_entry *entry;
  size_t slot;
  bool found;
  slot = bounds_relation_projection_probe(b, endpoint_index, &found);
  entry = slot == SIZE_MAX ? NULL : &cache[slot];
  if (found)
    return entry;
  assert(entry != NULL && b->equality_projection_cache_capacity != 0 &&
         b->equality_projection_cache_count + 1u <=
             b->equality_projection_cache_capacity -
                 b->equality_projection_cache_capacity / 4u);
  if (!entry)
    abort();
  memset(entry, 0, sizeof(*entry));
  entry->endpoint_index = endpoint_index;
  entry->generation = b->equality_projection_cache_generation;
  b->equality_projection_cache_count++;
  return entry;
}

static bounds_equality_projection_cache_entry *
bounds_relation_projection_existing(ixs_bounds *b, size_t endpoint_index) {
  bounds_equality_projection_cache_entry *cache =
      (bounds_equality_projection_cache_entry *)b->equality_projection_cache;
  bounds_equality_projection_cache_entry *entry;
  size_t slot;
  bool found;
  slot = bounds_relation_projection_probe(b, endpoint_index, &found);
  entry = slot == SIZE_MAX ? NULL : &cache[slot];
  assert(found && entry != NULL);
  if (!found || !entry)
    abort();
  return entry;
}

static const bounds_equality_projection_cache_entry *
bounds_relation_projection_find(const ixs_bounds *b, size_t endpoint_index) {
  const bounds_equality_projection_cache_entry *cache =
      (const bounds_equality_projection_cache_entry *)
          b->equality_projection_cache;
  size_t slot;
  bool found;
  slot = bounds_relation_projection_probe(b, endpoint_index, &found);
  return found ? &cache[slot] : NULL;
}

static bool bounds_relation_projection_reserve(ixs_bounds *b,
                                               size_t additional) {
  size_t needed;
  if (additional > SIZE_MAX - b->equality_projection_cache_count)
    return false;
  needed = b->equality_projection_cache_count + additional;
  while (!b->equality_projection_cache_capacity ||
         needed > b->equality_projection_cache_capacity -
                      b->equality_projection_cache_capacity / 4u) {
    if (!bounds_relation_projection_grow(b))
      return false;
  }
  return true;
}

IXS_STATIC bool bounds_relation_projection_lookup_integer(
    const ixs_bounds *b, size_t endpoint_index, ixs_check_result *result) {
  const bounds_equality_projection_cache_entry *entry =
      bounds_relation_projection_find(b, endpoint_index);
  if (!entry || !(entry->completion & BOUNDS_PROJECTION_COMPLETE_INTEGER))
    return false;
  *result = entry->integer;
  return true;
}

IXS_STATIC bool bounds_relation_projection_lookup_range(const ixs_bounds *b,
                                                        size_t endpoint_index,
                                                        ixs_interval *result) {
  const bounds_equality_projection_cache_entry *entry =
      bounds_relation_projection_find(b, endpoint_index);
  if (!entry || !(entry->completion & BOUNDS_PROJECTION_COMPLETE_RANGE))
    return false;
  *result = entry->range;
  return true;
}

IXS_STATIC bool bounds_relation_projection_lookup_defined(
    const ixs_bounds *b, size_t endpoint_index, bool without_equality,
    ixs_check_result *result) {
  const bounds_equality_projection_cache_entry *entry =
      bounds_relation_projection_find(b, endpoint_index);
  uint8_t completion = without_equality
                           ? BOUNDS_PROJECTION_COMPLETE_DEFINED_WITHOUT_EQUALITY
                           : BOUNDS_PROJECTION_COMPLETE_DEFINED_WITH_EQUALITY;
  if (!entry || !(entry->completion & completion))
    return false;
  *result = without_equality ? entry->defined_without_equality
                             : entry->defined_with_equality;
  return true;
}

IXS_STATIC void bounds_relation_projection_complete_integer_component(
    ixs_bounds *b, const bounds_relation_component *component,
    ixs_check_result result) {
  size_t i;
  assert(component != NULL && component->count != 0);
  for (i = 0; i < component->count; i++) {
    bounds_equality_projection_cache_entry *entry =
        bounds_relation_projection_existing(
            b, component->entries[i].endpoint_index);
    entry->integer = result;
    entry->completion |= BOUNDS_PROJECTION_COMPLETE_INTEGER;
  }
}

IXS_STATIC void bounds_relation_projection_stage_range(ixs_bounds *b,
                                                       size_t endpoint_index,
                                                       ixs_interval range) {
  bounds_equality_projection_cache_entry *entry =
      bounds_relation_projection_existing(b, endpoint_index);
  entry->range = range;
}

IXS_STATIC ixs_interval bounds_relation_projection_complete_range(
    ixs_bounds *b, size_t endpoint_index, ixs_relation_offset endpoint_offset,
    const bounds_relation_projection_bound *lower,
    const bounds_relation_projection_bound *upper, bool project) {
  bounds_equality_projection_cache_entry *entry =
      bounds_relation_projection_existing(b, endpoint_index);
  ixs_interval result =
      project ? bounds_relation_projection_apply(entry->range, endpoint_offset,
                                                 lower, upper)
              : ixs_interval_unknown();
  entry->range = result;
  entry->completion |= BOUNDS_PROJECTION_COMPLETE_RANGE;
  return result;
}

IXS_STATIC bool bounds_relation_projection_complete_defined(
    ixs_bounds *b, size_t endpoint_index, bool without_equality,
    ixs_check_result result) {
  bounds_equality_projection_cache_entry *cache =
      (bounds_equality_projection_cache_entry *)b->equality_projection_cache;
  bounds_equality_projection_cache_entry *entry;
  size_t slot;
  uint8_t completion;
  bool found;
  slot = bounds_relation_projection_probe(b, endpoint_index, &found);
  entry = slot == SIZE_MAX ? NULL : &cache[slot];
  if (!found) {
    if (!bounds_relation_projection_reserve(b, 1u))
      return false;
    entry = bounds_relation_projection_row(b, endpoint_index);
  }
  if (without_equality) {
    entry->defined_without_equality = result;
    completion = BOUNDS_PROJECTION_COMPLETE_DEFINED_WITHOUT_EQUALITY;
  } else {
    entry->defined_with_equality = result;
    completion = BOUNDS_PROJECTION_COMPLETE_DEFINED_WITH_EQUALITY;
  }
  entry->completion |= completion;
  return true;
}

static bool
bounds_relation_component_grow(bounds_relation_component *component) {
  bounds_relation_component_entry *entries;
  size_t capacity;
  size_t old_bytes;
  size_t new_bytes;
  if (component->count < component->capacity)
    return true;
  capacity =
      component->capacity ? component->capacity : BOUNDS_RELATION_WALK_INIT_CAP;
  if (component->capacity) {
    if (capacity > SIZE_MAX / 2u)
      return false;
    capacity *= 2u;
  }
  if (capacity > ixs_relation_algebra_endpoint_count(component->relations))
    capacity = ixs_relation_algebra_endpoint_count(component->relations);
  if (capacity <= component->capacity ||
      component->capacity > SIZE_MAX / sizeof(*component->entries) ||
      capacity > SIZE_MAX / sizeof(*component->entries))
    return false;
  old_bytes = component->capacity * sizeof(*component->entries);
  new_bytes = capacity * sizeof(*component->entries);
  if (component->entries) {
    entries = ixs_arena_grow(component->scratch, component->entries, old_bytes,
                             new_bytes, sizeof(void *));
  } else {
    entries = ixs_arena_alloc(component->scratch, new_bytes, sizeof(void *));
  }
  if (!entries)
    return false;
  component->entries = entries;
  component->capacity = capacity;
  return true;
}

static size_t bounds_relation_seen_hash(size_t endpoint_index) {
  uint64_t x = (uint64_t)endpoint_index + UINT64_C(0x9e3779b97f4a7c15);
  x ^= x >> 33;
  x *= UINT64_C(0xff51afd7ed558ccd);
  x ^= x >> 33;
  return (size_t)x;
}

static size_t
bounds_relation_seen_slot(const size_t *seen, size_t capacity,
                          const bounds_relation_component_entry *entries,
                          size_t endpoint_index) {
  size_t slot = bounds_relation_seen_hash(endpoint_index) & (capacity - 1u);
  while (seen[slot] &&
         entries[seen[slot] - 1u].endpoint_index != endpoint_index)
    slot = (slot + 1u) & (capacity - 1u);
  return slot;
}

IXS_STATIC bool
bounds_relation_component_find(const bounds_relation_component *component,
                               size_t endpoint_index, size_t *entry_index) {
  size_t slot;
  if (!component->seen_capacity)
    return false;
  slot = bounds_relation_seen_slot(component->seen, component->seen_capacity,
                                   component->entries, endpoint_index);
  if (!component->seen[slot])
    return false;
  *entry_index = component->seen[slot] - 1u;
  assert(*entry_index < component->count);
  return true;
}

static bool
bounds_relation_component_prepare_seen(bounds_relation_component *component) {
  size_t *seen;
  size_t capacity = component->seen_capacity;
  size_t bytes;
  size_t i;
  if (capacity && component->count < capacity - capacity / 4u)
    return true;
  if (!capacity)
    capacity = BOUNDS_RELATION_WALK_INIT_CAP;
  else {
    if (capacity > SIZE_MAX / 2u)
      return false;
    capacity *= 2u;
  }
  if (capacity > SIZE_MAX / sizeof(*seen))
    return false;
  bytes = capacity * sizeof(*seen);
  seen = ixs_arena_alloc(component->scratch, bytes, sizeof(void *));
  if (!seen)
    return false;
  memset(seen, 0, bytes);
  for (i = 0; i < component->seen_capacity; i++) {
    size_t entry_index;
    size_t endpoint_index;
    size_t slot;
    if (!component->seen[i])
      continue;
    entry_index = component->seen[i] - 1u;
    assert(entry_index < component->count);
    endpoint_index = component->entries[entry_index].endpoint_index;
    slot = bounds_relation_seen_slot(seen, capacity, component->entries,
                                     endpoint_index);
    seen[slot] = component->seen[i];
  }
  component->seen = seen;
  component->seen_capacity = capacity;
  return true;
}

static bounds_relation_cursor_step
bounds_relation_component_insert(bounds_relation_component *component,
                                 size_t endpoint_index,
                                 ixs_relation_offset offset) {
  size_t slot;
  assert(endpoint_index <
         ixs_relation_algebra_endpoint_count(component->relations));
  /* Entry storage grows before the seen table, matching the retained query
   * allocation order. */
  if (!bounds_relation_component_grow(component) ||
      !bounds_relation_component_prepare_seen(component))
    return BOUNDS_RELATION_CURSOR_OOM;
  component->entries[component->count].node =
      ixs_relation_algebra_endpoint_expr(component->relations, endpoint_index);
  component->entries[component->count].endpoint_index = endpoint_index;
  component->entries[component->count].offset = offset;
  slot = bounds_relation_seen_slot(component->seen, component->seen_capacity,
                                   component->entries, endpoint_index);
  assert(!component->seen[slot]);
  component->seen[slot] = component->count + 1u;
  component->count++;
  return BOUNDS_RELATION_CURSOR_READY;
}

IXS_STATIC bounds_relation_cursor_step bounds_relation_component_begin(
    ixs_relation_algebra *relations, ixs_arena *scratch, size_t root_endpoint,
    bounds_relation_component *component) {
  bounds_relation_cursor_step status;
  ixs_relation_offset zero = {0, 0, false};
  memset(component, 0, sizeof(*component));
  component->relations = relations;
  component->scratch = scratch;
  component->mark = ixs_arena_save(scratch);
  status = bounds_relation_component_insert(component, root_endpoint, zero);
  if (status != BOUNDS_RELATION_CURSOR_READY)
    return status;
  component->next_edge =
      ixs_relation_algebra_first_edge(relations, root_endpoint);
  return BOUNDS_RELATION_CURSOR_READY;
}

IXS_STATIC bounds_relation_cursor_step bounds_relation_component_pull(
    bounds_relation_component *component, ixs_node **candidate) {
  assert(component->scratch != NULL && !component->pending &&
         candidate != NULL);
  while (component->head < component->count) {
    const ixs_relation_edge *next;
    size_t neighbor_endpoint;
    size_t neighbor_entry;
    ixs_relation_offset step;
    ixs_relation_offset neighbor_offset;
    if (!component->next_edge) {
      component->head++;
      if (component->head == component->count)
        break;
      component->next_edge = ixs_relation_algebra_first_edge(
          component->relations,
          component->entries[component->head].endpoint_index);
      continue;
    }
    if (ixs_relation_algebra_edge_neighbor(
            component->relations,
            component->entries[component->head].endpoint_index,
            component->next_edge, &neighbor_endpoint, &step,
            &next) != IXS_RELATION_QUERY_FOUND ||
        neighbor_endpoint >=
            ixs_relation_algebra_endpoint_count(component->relations))
      return BOUNDS_RELATION_CURSOR_INVALID;
    component->next_edge = next;
    *candidate = ixs_relation_algebra_endpoint_expr(component->relations,
                                                    neighbor_endpoint);
    if (!*candidate)
      return BOUNDS_RELATION_CURSOR_INVALID;
    if (!bounds_relation_component_find(component, neighbor_endpoint,
                                        &neighbor_entry)) {
      component->pending_endpoint = neighbor_endpoint;
      component->pending_step = step;
      component->pending = true;
      return BOUNDS_RELATION_CURSOR_ADMISSION;
    }
    if (!ixs_relation_offset_add(component->entries[component->head].offset,
                                 step, &neighbor_offset))
      return BOUNDS_RELATION_CURSOR_INVALID;
    if (!ixs_relation_offset_equal(component->entries[neighbor_entry].offset,
                                   neighbor_offset))
      return BOUNDS_RELATION_CURSOR_INVALID;
  }
  return BOUNDS_RELATION_CURSOR_COMPLETE;
}

IXS_STATIC bounds_relation_cursor_step bounds_relation_component_resolve(
    bounds_relation_component *component, bool admitted) {
  ixs_relation_offset neighbor_offset;
  assert(component->scratch != NULL && component->pending);
  component->pending = false;
  if (!admitted)
    return BOUNDS_RELATION_CURSOR_READY;
  if (!ixs_relation_offset_add(component->entries[component->head].offset,
                               component->pending_step, &neighbor_offset))
    return BOUNDS_RELATION_CURSOR_INVALID;
  return bounds_relation_component_insert(
      component, component->pending_endpoint, neighbor_offset);
}

IXS_STATIC void
bounds_relation_component_destroy(bounds_relation_component *component) {
  if (component->scratch) {
    ixs_arena_restore(component->scratch, component->mark);
    component->scratch = NULL;
  }
}

IXS_STATIC bool bounds_relation_component_publish_defined(
    ixs_bounds *b, const bounds_relation_component *component) {
  size_t root;
  size_t i;
  assert(component != NULL && component->count != 0);
  /* Reserve the full component before publishing its first cache column. */
  if (!bounds_relation_projection_reserve(b, component->count))
    return false;
  root = component->entries[0].endpoint_index;
  for (i = 0; i < component->count; i++) {
    bounds_equality_projection_cache_entry *entry =
        bounds_relation_projection_row(b, component->entries[i].endpoint_index);
    entry->defined_component = root;
    entry->defined_offset = component->entries[i].offset;
    entry->completion |= BOUNDS_PROJECTION_COMPLETE_DEFINED_COMPONENT;
  }
  return true;
}

IXS_STATIC ixs_relation_query_status bounds_relation_cached_offset(
    ixs_bounds *b, size_t lhs_endpoint, size_t rhs_endpoint,
    ixs_relation_offset *offset) {
  const bounds_equality_projection_cache_entry *lhs;
  const bounds_equality_projection_cache_entry *rhs;
  lhs = bounds_relation_projection_find(b, lhs_endpoint);
  rhs = bounds_relation_projection_find(b, rhs_endpoint);
  if (!lhs || !rhs ||
      !(lhs->completion & BOUNDS_PROJECTION_COMPLETE_DEFINED_COMPONENT) ||
      !(rhs->completion & BOUNDS_PROJECTION_COMPLETE_DEFINED_COMPONENT) ||
      lhs->defined_component != rhs->defined_component)
    return IXS_RELATION_QUERY_NONE;
  if (!ixs_relation_offset_add(lhs->defined_offset,
                               ixs_relation_offset_negate(rhs->defined_offset),
                               offset))
    return IXS_RELATION_QUERY_INVALID;
  return IXS_RELATION_QUERY_FOUND;
}

static void bounds_relation_u64_mul_wide(uint64_t lhs, uint64_t rhs,
                                         uint64_t *lo, uint64_t *hi) {
  const uint64_t mask = UINT64_C(0xffffffff);
  uint64_t lhs_lo = lhs & mask;
  uint64_t lhs_hi = lhs >> 32;
  uint64_t rhs_lo = rhs & mask;
  uint64_t rhs_hi = rhs >> 32;
  uint64_t p0 = lhs_lo * rhs_lo;
  uint64_t p1 = lhs_lo * rhs_hi;
  uint64_t p2 = lhs_hi * rhs_lo;
  uint64_t p3 = lhs_hi * rhs_hi;
  uint64_t middle = (p0 >> 32) + (p1 & mask) + (p2 & mask);
  *lo = (p0 & mask) | (middle << 32);
  *hi = p3 + (p1 >> 32) + (p2 >> 32) + (middle >> 32);
}

static bool bounds_relation_offset_add_rational(ixs_relation_offset offset,
                                                int64_t p, int64_t q,
                                                int64_t *result_p) {
  ixs_relation_offset scaled;
  ixs_relation_offset sum;
  if (q <= 0 || offset.hi != 0)
    return false;
  bounds_relation_u64_mul_wide(offset.lo, (uint64_t)q, &scaled.lo, &scaled.hi);
  scaled.negative = offset.negative;
  if (!ixs_relation_offset_add(scaled, ixs_relation_offset_from_int64(p), &sum))
    return false;
  return ixs_relation_offset_to_int64(sum, result_p);
}

static int bounds_relation_projection_integer_magnitude_cmp(
    bounds_relation_projection_integer lhs,
    bounds_relation_projection_integer rhs) {
  if (lhs.hi != rhs.hi)
    return lhs.hi < rhs.hi ? -1 : 1;
  if (lhs.mid != rhs.mid)
    return lhs.mid < rhs.mid ? -1 : 1;
  if (lhs.lo != rhs.lo)
    return lhs.lo < rhs.lo ? -1 : 1;
  return 0;
}

static void bounds_relation_projection_integer_subtract_magnitudes(
    bounds_relation_projection_integer larger,
    bounds_relation_projection_integer smaller,
    bounds_relation_projection_integer *result) {
  bool borrow_lo = larger.lo < smaller.lo;
  uint64_t mid_subtrahend = smaller.mid + (borrow_lo ? 1u : 0u);
  bool mid_subtrahend_overflow = mid_subtrahend < smaller.mid;
  bool borrow_mid = mid_subtrahend_overflow || larger.mid < mid_subtrahend;
  result->lo = larger.lo - smaller.lo;
  result->mid = larger.mid - mid_subtrahend;
  result->hi = larger.hi - smaller.hi - (borrow_mid ? 1u : 0u);
}

static void bounds_relation_projection_integer_add(
    bounds_relation_projection_integer lhs,
    bounds_relation_projection_integer rhs,
    bounds_relation_projection_integer *result) {
  int magnitude_cmp;
  if (lhs.negative == rhs.negative) {
    bool carry_lo;
    bool carry_mid;
    result->lo = lhs.lo + rhs.lo;
    carry_lo = result->lo < lhs.lo;
    result->mid = lhs.mid + rhs.mid;
    carry_mid = result->mid < lhs.mid;
    if (carry_lo) {
      uint64_t old_mid = result->mid;
      result->mid++;
      if (result->mid < old_mid)
        carry_mid = true;
    }
    result->hi = lhs.hi + rhs.hi + (carry_mid ? 1u : 0u);
    result->negative = lhs.negative;
  } else {
    magnitude_cmp = bounds_relation_projection_integer_magnitude_cmp(lhs, rhs);
    if (magnitude_cmp >= 0) {
      bounds_relation_projection_integer_subtract_magnitudes(lhs, rhs, result);
      result->negative = lhs.negative;
    } else {
      bounds_relation_projection_integer_subtract_magnitudes(rhs, lhs, result);
      result->negative = rhs.negative;
    }
  }
  if (result->lo == 0 && result->mid == 0 && result->hi == 0)
    result->negative = false;
}

static int
bounds_relation_projection_integer_cmp(bounds_relation_projection_integer lhs,
                                       bounds_relation_projection_integer rhs) {
  int magnitude_cmp;
  if (lhs.negative != rhs.negative)
    return lhs.negative ? -1 : 1;
  magnitude_cmp = bounds_relation_projection_integer_magnitude_cmp(lhs, rhs);
  return lhs.negative ? -magnitude_cmp : magnitude_cmp;
}

static bool bounds_relation_projection_coordinate(
    int64_t p, int64_t q, ixs_relation_offset peer_offset,
    bounds_relation_projection_integer *integer, uint64_t *remainder) {
  bounds_relation_projection_integer quotient = {0, 0, 0, false};
  bounds_relation_projection_integer offset = {0, 0, 0, false};
  uint64_t magnitude;
  uint64_t denominator;
  uint64_t quotient_magnitude;
  uint64_t truncated_remainder;
  if (q <= 0)
    return false;
  denominator = (uint64_t)q;
  magnitude = ixs_int64_magnitude(p);
  quotient_magnitude = magnitude / denominator;
  truncated_remainder = magnitude % denominator;
  if (p < 0 && truncated_remainder != 0) {
    quotient_magnitude++;
    *remainder = denominator - truncated_remainder;
  } else {
    *remainder = truncated_remainder;
  }
  quotient.lo = quotient_magnitude;
  quotient.negative = p < 0 && quotient_magnitude != 0;
  offset.lo = peer_offset.lo;
  offset.mid = peer_offset.hi;
  offset.negative =
      !peer_offset.negative && (peer_offset.lo != 0 || peer_offset.hi != 0);
  if (peer_offset.negative)
    offset.negative = false;
  bounds_relation_projection_integer_add(quotient, offset, integer);
  return true;
}

IXS_STATIC bool bounds_relation_projection_bound_cmp(
    int64_t lhs_p, int64_t lhs_q, ixs_relation_offset lhs_offset, int64_t rhs_p,
    int64_t rhs_q, ixs_relation_offset rhs_offset, int *result) {
  bounds_relation_projection_integer lhs_integer;
  bounds_relation_projection_integer rhs_integer;
  uint64_t lhs_remainder;
  uint64_t rhs_remainder;
  uint64_t lhs_product_lo;
  uint64_t lhs_product_hi;
  uint64_t rhs_product_lo;
  uint64_t rhs_product_hi;
  int integer_cmp;
  if (!bounds_relation_projection_coordinate(lhs_p, lhs_q, lhs_offset,
                                             &lhs_integer, &lhs_remainder) ||
      !bounds_relation_projection_coordinate(rhs_p, rhs_q, rhs_offset,
                                             &rhs_integer, &rhs_remainder))
    return false;
  integer_cmp =
      bounds_relation_projection_integer_cmp(lhs_integer, rhs_integer);
  if (integer_cmp != 0) {
    *result = integer_cmp;
    return true;
  }
  bounds_relation_u64_mul_wide(lhs_remainder, (uint64_t)rhs_q, &lhs_product_lo,
                               &lhs_product_hi);
  bounds_relation_u64_mul_wide(rhs_remainder, (uint64_t)lhs_q, &rhs_product_lo,
                               &rhs_product_hi);
  if (lhs_product_hi != rhs_product_hi)
    *result = lhs_product_hi < rhs_product_hi ? -1 : 1;
  else if (lhs_product_lo != rhs_product_lo)
    *result = lhs_product_lo < rhs_product_lo ? -1 : 1;
  else
    *result = 0;
  return true;
}

static ixs_interval bounds_relation_unbounded_interval(void) {
  ixs_interval result = ixs_interval_exact(0, 1);
  ixs_interval_set_lo_neg_inf(&result);
  ixs_interval_set_hi_pos_inf(&result);
  return result;
}

IXS_STATIC ixs_interval bounds_relation_projection_apply(
    ixs_interval intrinsic, ixs_relation_offset endpoint_offset,
    const bounds_relation_projection_bound *lower,
    const bounds_relation_projection_bound *upper) {
  ixs_interval result =
      intrinsic.valid ? intrinsic : bounds_relation_unbounded_interval();
  ixs_relation_offset delta;
  int64_t shifted;
  if (lower->present) {
    if (!ixs_relation_offset_add(endpoint_offset,
                                 ixs_relation_offset_negate(lower->peer_offset),
                                 &delta) ||
        !bounds_relation_offset_add_rational(delta, lower->p, lower->q,
                                             &shifted))
      return ixs_interval_unknown();
    if (result.lo_inf ||
        ixs_rat_cmp(shifted, lower->q, result.lo_p, result.lo_q) > 0) {
      result.lo_inf = false;
      result.lo_p = shifted;
      result.lo_q = lower->q;
    }
  }
  if (upper->present) {
    if (!ixs_relation_offset_add(endpoint_offset,
                                 ixs_relation_offset_negate(upper->peer_offset),
                                 &delta) ||
        !bounds_relation_offset_add_rational(delta, upper->p, upper->q,
                                             &shifted))
      return ixs_interval_unknown();
    if (result.hi_inf ||
        ixs_rat_cmp(shifted, upper->q, result.hi_p, result.hi_q) < 0) {
      result.hi_inf = false;
      result.hi_p = shifted;
      result.hi_q = upper->q;
    }
  }
  return ixs_interval_is_empty(result) ? ixs_interval_unknown() : result;
}

#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
IXS_STATIC void
bounds_relation_projection_force_generation_wrap(ixs_bounds *b) {
  b->equality_projection_cache_generation = UINT32_MAX;
}

IXS_STATIC size_t bounds_relation_projection_entry_size(void) {
  return sizeof(bounds_equality_projection_cache_entry);
}

IXS_STATIC size_t bounds_relation_projection_generation_count(
    const ixs_bounds *b, uint32_t generation) {
  const bounds_equality_projection_cache_entry *cache =
      (const bounds_equality_projection_cache_entry *)
          b->equality_projection_cache;
  size_t count = 0;
  size_t i;
  for (i = 0; i < b->equality_projection_cache_capacity; i++)
    if (cache[i].generation == generation)
      count++;
  return count;
}
#endif
