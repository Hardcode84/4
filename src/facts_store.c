/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "facts_store.h"

#include "bounds_assume.h"
#include "bounds_defined.h"
#include "bounds_difference.h"
#include "bounds_query.h"
#include "bounds_range.h"
#include "bounds_relation.h"
#include "hash.h"
#include "query_walk.h"
#include "rational.h"
#include "simplify.h"

#include <assert.h>
#include <limits.h>
#include <string.h>

#define FACT_WORK_INIT_CAP 64u

/* Fact handles live in the context arena, but their bounds own a heap-backed
 * query arena.  Release each one before its session epoch and scratch die. */
IXS_STATIC void facts_store_destroy_session(ixs_session_impl *impl) {
  ixs_facts *facts = impl->facts_head;
  impl->facts_head = NULL;
  while (facts) {
    ixs_facts *next = facts->session_next;
    assert(facts->impl == impl);
    facts->session_next = NULL;
    ixs_bounds_destroy(&facts->bounds);
    facts->impl = NULL;
    facts->epoch = 0;
    facts->usable = false;
    facts = next;
  }
}

static bool range_result_to_interval(const ixs_range_result *range,
                                     ixs_interval *out) {
  ixs_interval iv;
  if (!range || !out)
    return false;
  iv.valid = true;
  iv.lo_inf = false;
  iv.hi_inf = false;
  if (range->has_lower) {
    if (!ixs_rat_normalize(range->lower_p, range->lower_q, &iv.lo_p, &iv.lo_q))
      return false;
  } else {
    ixs_interval_set_lo_neg_inf(&iv);
  }
  if (range->has_upper) {
    if (!ixs_rat_normalize(range->upper_p, range->upper_q, &iv.hi_p, &iv.hi_q))
      return false;
  } else {
    ixs_interval_set_hi_pos_inf(&iv);
  }
  if (ixs_interval_is_empty(iv))
    return false;
  *out = iv;
  return true;
}

static void facts_poison(ixs_facts *facts) {
  if (facts)
    facts->usable = false;
}

static void facts_commit(ixs_facts *facts, ixs_bounds *candidate) {
  /* A fork's projection memo is query-local and cannot be transferred into the
   * committed bounds.  Destroy it, then reuse the destination's persistent
   * table allocation after advancing its semantic generation once. */
  assert(candidate->store_ctx != NULL);
  assert(candidate->query_tracking_depth == 0);
  assert(!candidate->query_state_owner && !candidate->query_state_borrowed);
  /* Read queries restore their temporary allocations but may retain arena
   * chunks for reuse.  A commit replaces the complete bounds object, so
   * release that old workspace before overwriting its arena owner. */
  bounds_query_reset_arena(&facts->bounds);
  bounds_query_reset_arena(candidate);
  bounds_relation_projection_commit(&facts->bounds, candidate);
  assert(candidate->query_state_arena.current == NULL &&
         candidate->query_state_arena.spare == NULL &&
         candidate->query_state_arena.inline_chunk == NULL);
  assert(candidate->query_arena.current == NULL &&
         candidate->query_arena.spare == NULL &&
         candidate->query_arena.inline_chunk == NULL);
  assert(facts->bounds.query_state_arena.current == NULL &&
         facts->bounds.query_state_arena.spare == NULL &&
         facts->bounds.query_state_arena.inline_chunk == NULL);
  assert(facts->bounds.query_arena.current == NULL &&
         facts->bounds.query_arena.spare == NULL &&
         facts->bounds.query_arena.inline_chunk == NULL);
  candidate->cache = facts->bounds.cache;
  candidate->cache_cap = facts->bounds.cache_cap;
  bounds_store_invalidate_reads(candidate);
  bounds_store_retarget_scratch(candidate, NULL);
  facts->bounds = *candidate;
}

static bool facts_node_ok(ixs_ctx *ctx, ixs_node *node) {
  return node && !ixs_node_is_sentinel(node) && ixs_ctx_owns_node(ctx, node);
}

static void bounds_add_var_fact(ixs_bounds *dst, const ixs_var_bound *src) {
  ixs_var_bound *v = bounds_store_find_var(dst, src->name);
  bool changed;
  bounds_store_invalidate_reads(dst);
  if (!v) {
    v = bounds_store_get_or_create_var(dst, src->name);
    if (!v)
      return;
    bounds_store_import_var(dst, v, src);
    bounds_store_refine_var_bits(dst, v);
    bounds_difference_propagate_symbol(dst, src->name);
    return;
  }

  changed = bounds_store_set_var_interval(dst, v, iv_intersect(v->iv, src->iv));
  if (src->modulus > 0)
    apply_modrem(dst, src->name, src->modulus, src->remainder);
  bounds_store_apply_var_known_bits(dst, v, src->bits.known_zero,
                                    src->bits.known_one);
  bounds_store_apply_pow2(dst, v, src->bits.pow2);
  if (changed)
    bounds_difference_propagate_symbol(dst, src->name);
}

static bool bounds_interval_contains_rational(ixs_interval iv, int64_t p,
                                              int64_t q) {
  if (!iv.valid)
    return true;
  if (!iv.lo_inf && ixs_rat_cmp(p, q, iv.lo_p, iv.lo_q) < 0)
    return false;
  if (!iv.hi_inf && ixs_rat_cmp(p, q, iv.hi_p, iv.hi_q) > 0)
    return false;
  return true;
}

static void bounds_transfer_inverse_congruence(ixs_bounds *dst,
                                               const char *name, int64_t scale,
                                               int64_t offset, int64_t modulus,
                                               int64_t residue) {
  uint64_t m, a, rhs, g, reduced, inverse, result;
  if (modulus <= 0)
    return;
  m = (uint64_t)modulus;
  a = ixs_int64_normalize_residue(scale, m);
  rhs = ixs_u64_sub_mod(ixs_int64_normalize_residue(residue, m),
                        ixs_int64_normalize_residue(offset, m), m);
  g = ixs_u64_gcd(a, m);
  if (rhs % g != 0) {
    bounds_store_mark_contradiction(dst);
    return;
  }
  reduced = m / g;
  if (reduced == 1u)
    return;
  if (!ixs_u64_mod_inverse((a / g) % reduced, reduced, &inverse)) {
    bounds_store_mark_contradiction(dst);
    return;
  }
  result = ixs_u64_mul_mod((rhs / g) % reduced, inverse, reduced);
  apply_modrem(dst, name, (int64_t)reduced, (int64_t)result);
}

static void bounds_transfer_affine_range(ixs_bounds *dst, const char *name,
                                         int64_t scale, int64_t offset,
                                         ixs_interval iv) {
  int64_t neg_offset, denominator;
  ixs_interval shifted, inverse;
  ixs_var_bound fact;
  if (!iv.valid || !ixs_safe_neg(offset, &neg_offset))
    return;
  shifted = iv_add(iv, ixs_interval_exact(neg_offset, 1));
  if (scale > 0) {
    denominator = scale;
    inverse = iv_mul_const(shifted, 1, denominator);
  } else {
    if (!ixs_safe_neg(scale, &denominator))
      return;
    inverse = iv_mul_const(shifted, -1, denominator);
  }
  if (!inverse.valid)
    return;
  memset(&fact, 0, sizeof(fact));
  fact.name = name;
  fact.iv = inverse;
  bounds_add_var_fact(dst, &fact);
}

static void bounds_check_constant_var_fact(ixs_bounds *dst,
                                           const ixs_var_bound *src, int64_t p,
                                           int64_t q) {
  uint64_t value;
  if (!bounds_interval_contains_rational(src->iv, p, q))
    bounds_store_mark_contradiction(dst);
  if (src->modulus > 0 &&
      (q != 1 || ixs_int64_normalize_residue(p, (uint64_t)src->modulus) !=
                     (uint64_t)src->remainder))
    bounds_store_mark_contradiction(dst);
  if (src->bits.known_zero != 0 || src->bits.known_one != 0) {
    if (q != 1) {
      bounds_store_mark_contradiction(dst);
    } else {
      value = (uint64_t)p;
      if ((src->bits.known_zero & value) != 0 ||
          (src->bits.known_one & ~value) != 0)
        bounds_store_mark_contradiction(dst);
    }
  }
  if (src->bits.pow2 != IXS_POW2_UNKNOWN) {
    if (q != 1 ||
        (src->bits.pow2 == IXS_POW2_POSITIVE &&
         !ixs_int64_is_positive_pow2(p)) ||
        (src->bits.pow2 == IXS_POW2_OR_ZERO && p != 0 &&
         !ixs_int64_is_positive_pow2(p)))
      bounds_store_mark_contradiction(dst);
  }
}

static void bounds_transfer_range(ixs_bounds *dst, ixs_node *replacement,
                                  ixs_interval iv) {
  const char *name;
  int64_t scale, offset, p, q;
  if (!iv.valid)
    return;
  if (ixs_node_is_const(replacement)) {
    ixs_node_get_rat(replacement, &p, &q);
    if (!bounds_interval_contains_rational(iv, p, q))
      bounds_store_mark_contradiction(dst);
    return;
  }
  if (bounds_extract_integer_affine(replacement, &name, &scale, &offset))
    bounds_transfer_affine_range(dst, name, scale, offset, iv);
}

static void bounds_transfer_var_fact(ixs_bounds *dst, const ixs_var_bound *src,
                                     ixs_node *replacement) {
  const char *name;
  int64_t scale, offset, p, q;
  unsigned low_bits = 0;
  uint64_t known, modulus, mask, residue;
  ixs_var_bound renamed;
  ixs_var_bound *var;

  if (replacement->tag == IXS_SYM) {
    renamed = *src;
    renamed.name = replacement->u.name;
    bounds_add_var_fact(dst, &renamed);
    return;
  }
  if (ixs_node_is_const(replacement)) {
    ixs_node_get_rat(replacement, &p, &q);
    bounds_check_constant_var_fact(dst, src, p, q);
    return;
  }
  if (!bounds_extract_integer_affine(replacement, &name, &scale, &offset))
    return;

  bounds_transfer_affine_range(dst, name, scale, offset, src->iv);
  if (src->modulus > 0)
    bounds_transfer_inverse_congruence(dst, name, scale, offset, src->modulus,
                                       src->remainder);

  known = src->bits.known_zero | src->bits.known_one;
  while (low_bits < 62u && (known & (UINT64_C(1) << low_bits)) != 0)
    low_bits++;
  if (low_bits != 0) {
    modulus = UINT64_C(1) << low_bits;
    mask = modulus - 1u;
    residue = src->bits.known_one & mask;
    bounds_transfer_inverse_congruence(dst, name, scale, offset,
                                       (int64_t)modulus, (int64_t)residue);
  }

  if (offset == 0 && ixs_int64_is_positive_pow2(scale) &&
      src->bits.pow2 != IXS_POW2_UNKNOWN) {
    var = bounds_store_get_or_create_var(dst, name);
    bounds_store_apply_pow2(dst, var, src->bits.pow2);
  }
}

/* Build a fixed-capacity table at no more than half load. Initialization is
 * O(count); predicate processing never grows the table. */
static bool facts_predicate_set_init(ixs_arena *arena, size_t count,
                                     ixs_node ***slots, size_t *capacity) {
  size_t needed;
  *slots = NULL;
  *capacity = 0;
  if (count < 2)
    return true;
  if (count > SIZE_MAX / 2u)
    return false;
  needed = count * 2u;
  *capacity = 2u;
  while (*capacity < needed) {
    if (*capacity > SIZE_MAX / 2u)
      return false;
    *capacity *= 2u;
  }
  if (*capacity > SIZE_MAX / sizeof(**slots))
    return false;
  *slots = ixs_arena_alloc(arena, *capacity * sizeof(**slots), sizeof(void *));
  if (!*slots)
    return false;
  memset(*slots, 0, *capacity * sizeof(**slots));
  return true;
}

/* Expected O(1) at the fixed half-load bound; collisions probe linearly. */
#define FACTS_CLOSURE_CACHE_CAP 32u
#define FACTS_CLOSURE_CACHE_SLOT_BYTES (3u * 1024u)
#define FACTS_CLOSURE_CACHE_RETAINED_LIMIT (128u * 1024u)
#define FACTS_CLOSURE_CACHE_SLOT_NODES                                         \
  (FACTS_CLOSURE_CACHE_SLOT_BYTES / sizeof(ixs_node *))

typedef struct {
  uint64_t hash;
  size_t n_predicates;
  size_t n_replay;
  ixs_node *nodes[FACTS_CLOSURE_CACHE_SLOT_NODES];
  bool valid;
} facts_closure_cache_entry;

typedef struct {
  facts_closure_cache_entry *entries[FACTS_CLOSURE_CACHE_CAP];
#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
  size_t lookups;
  size_t hits;
  size_t stores;
  size_t bypasses;
  size_t entry_count;
#endif
} facts_closure_cache;

typedef char facts_closure_cache_must_fit_retained_limit
    [(sizeof(facts_closure_cache) +
          FACTS_CLOSURE_CACHE_CAP * sizeof(facts_closure_cache_entry) <=
      FACTS_CLOSURE_CACHE_RETAINED_LIMIT)
         ? 1
         : -1];

typedef struct {
  ixs_node *replay[FACTS_CLOSURE_CACHE_SLOT_NODES];
  size_t n_replay;
  size_t replay_limit;
  bool overflow;
} facts_closure_capture;

typedef struct {
  facts_closure_capture capture;
  uint64_t hash;
  bool store;
} facts_closure_cache_result;

static facts_closure_cache *facts_closure_cache_get(ixs_ctx *ctx) {
  facts_closure_cache *cache;
  if (!ctx)
    return NULL;
  cache = ctx->facts_closure_cache;
  if (cache)
    return cache;
  cache = ixs_arena_alloc(&ctx->arena, sizeof(*cache), sizeof(void *));
  if (!cache)
    return NULL;
  memset(cache, 0, sizeof(*cache));
  ctx->facts_closure_cache = cache;
  return cache;
}

static uint64_t facts_closure_hash(ixs_node *const *predicates,
                                   size_t n_predicates) {
  uint64_t hash = UINT64_C(0x9e3779b97f4a7c15) ^ (uint64_t)n_predicates;
  size_t i;
  for (i = 0; i < n_predicates; i++) {
    uint64_t value = (uint64_t)(uintptr_t)predicates[i];
    hash ^= value + UINT64_C(0x9e3779b97f4a7c15) + (hash << 6) + (hash >> 2);
  }
  hash ^= hash >> 33;
  hash *= UINT64_C(0xff51afd7ed558ccd);
  hash ^= hash >> 33;
  return hash;
}

/* Lookup is O(n) in the explicit batch size and never scans context state. */
static facts_closure_cache_entry *
facts_closure_cache_lookup(ixs_ctx *ctx, ixs_node *const *predicates,
                           size_t n_predicates, uint64_t *hash_out) {
  facts_closure_cache *cache;
  facts_closure_cache_entry *entry;
  uint64_t hash;
  size_t i;
  if (n_predicates > FACTS_CLOSURE_CACHE_SLOT_NODES) {
#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
    cache = facts_closure_cache_get(ctx);
    if (cache) {
      cache->lookups++;
      cache->bypasses++;
    }
#endif
    return NULL;
  }
  hash = facts_closure_hash(predicates, n_predicates);
  *hash_out = hash;
  cache = facts_closure_cache_get(ctx);
  if (!cache)
    return NULL;
#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
  cache->lookups++;
#endif
  entry = cache->entries[(size_t)hash & (FACTS_CLOSURE_CACHE_CAP - 1u)];
  if (!entry || !entry->valid || entry->hash != hash ||
      entry->n_predicates != n_predicates)
    return NULL;
  for (i = 0; i < n_predicates; i++) {
    if (entry->nodes[i] != predicates[i])
      return NULL;
  }
#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
  cache->hits++;
#endif
  return entry;
}

#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
static void facts_closure_cache_note_bypass(ixs_ctx *ctx) {
  facts_closure_cache *cache = facts_closure_cache_get(ctx);
  if (cache)
    cache->bypasses++;
}
#endif

/* Store is O(n + r) in the exact key and replay sequence. Collisions replace
 * an entry in place, so retained cache memory cannot grow after 32 slots. */
static void facts_closure_cache_store(ixs_ctx *ctx, ixs_node *const *predicates,
                                      size_t n_predicates,
                                      const facts_closure_capture *capture,
                                      uint64_t hash) {
  facts_closure_cache *cache;
  facts_closure_cache_entry *entry;
  size_t slot;
  if (!capture || capture->overflow ||
      n_predicates > FACTS_CLOSURE_CACHE_SLOT_NODES ||
      capture->n_replay > FACTS_CLOSURE_CACHE_SLOT_NODES - n_predicates) {
#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
    facts_closure_cache_note_bypass(ctx);
#endif
    return;
  }
  cache = facts_closure_cache_get(ctx);
  if (!cache)
    return;
  slot = (size_t)hash & (FACTS_CLOSURE_CACHE_CAP - 1u);
  entry = cache->entries[slot];
  if (!entry) {
    entry = ixs_arena_alloc(&ctx->arena, sizeof(*entry), sizeof(void *));
    if (!entry)
      return;
    memset(entry, 0, sizeof(*entry));
    cache->entries[slot] = entry;
#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
    cache->entry_count++;
#endif
  }
  entry->valid = false;
  if (n_predicates)
    memcpy(entry->nodes, predicates, n_predicates * sizeof(*predicates));
  if (capture->n_replay)
    memcpy(entry->nodes + n_predicates, capture->replay,
           capture->n_replay * sizeof(*capture->replay));
  entry->hash = hash;
  entry->n_predicates = n_predicates;
  entry->n_replay = capture->n_replay;
  entry->valid = true;
#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
  cache->stores++;
#endif
}

#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
IXS_STATIC void
ixs_facts_closure_cache_stats(const ixs_ctx *ctx,
                              ixs_facts_closure_cache_stats_result *stats) {
  const facts_closure_cache *cache = ctx ? ctx->facts_closure_cache : NULL;
  if (!stats)
    return;
  memset(stats, 0, sizeof(*stats));
  stats->retained_limit = FACTS_CLOSURE_CACHE_RETAINED_LIMIT;
  stats->slot_node_capacity = FACTS_CLOSURE_CACHE_SLOT_NODES;
  if (!cache)
    return;
  stats->lookups = cache->lookups;
  stats->hits = cache->hits;
  stats->stores = cache->stores;
  stats->bypasses = cache->bypasses;
  stats->entries = cache->entry_count;
  stats->retained_bytes =
      sizeof(*cache) + cache->entry_count * sizeof(facts_closure_cache_entry);
}
#endif

static void facts_closure_capture_append(facts_closure_capture *capture,
                                         ixs_node *predicate) {
  if (!capture || capture->overflow)
    return;
  if (capture->n_replay >= capture->replay_limit) {
    capture->overflow = true;
    return;
  }
  capture->replay[capture->n_replay++] = predicate;
}

typedef struct {
  const char *name;
  size_t first_occurrence;
} facts_symbol_slot;

typedef struct {
  const char *name;
  size_t predicate;
  size_t next_for_predicate;
  size_t next_for_symbol;
} facts_symbol_occurrence;

typedef struct {
  ixs_arena arena;
  size_t n_predicates;
  bool *active;
  bool *queued;
  size_t *queue;
  size_t queue_head;
  size_t queue_tail;
  size_t queue_count;
  size_t *predicate_occurrences;
  facts_symbol_slot *symbols;
  size_t symbol_capacity;
  size_t symbol_count;
  facts_symbol_occurrence *occurrences;
  size_t occurrence_capacity;
  size_t occurrence_count;
  ixs_node **seen;
  size_t seen_capacity;
} facts_worklist;

typedef union {
  void *align;
  unsigned char bytes[IXS_ARENA_DEFAULT_SIZE];
} facts_work_storage;

static bool facts_worklist_alloc_arrays(facts_worklist *work) {
  size_t count = work->n_predicates;
  size_t i;
  if (count > SIZE_MAX / sizeof(*work->queue) ||
      count > SIZE_MAX / sizeof(*work->predicate_occurrences))
    return false;
  work->active = ixs_arena_alloc(&work->arena, count * sizeof(*work->active),
                                 sizeof(void *));
  work->queued = ixs_arena_alloc(&work->arena, count * sizeof(*work->queued),
                                 sizeof(void *));
  work->queue = ixs_arena_alloc(&work->arena, count * sizeof(*work->queue),
                                sizeof(void *));
  work->predicate_occurrences = ixs_arena_alloc(
      &work->arena, count * sizeof(*work->predicate_occurrences),
      sizeof(void *));
  if (!work->active || !work->queued || !work->queue ||
      !work->predicate_occurrences)
    return false;
  memset(work->active, 0, count * sizeof(*work->active));
  memset(work->queued, 0, count * sizeof(*work->queued));
  for (i = 0; i < count; i++)
    work->predicate_occurrences[i] = SIZE_MAX;
  return true;
}

static bool facts_worklist_init(facts_worklist *work,
                                facts_work_storage *storage,
                                size_t n_predicates) {
  memset(work, 0, sizeof(*work));
  ixs_arena_init_inline(&work->arena, storage->bytes, sizeof(storage->bytes),
                        IXS_ARENA_DEFAULT_SIZE);
  work->n_predicates = n_predicates;
  if (!facts_worklist_alloc_arrays(work) ||
      !facts_predicate_set_init(&work->arena, n_predicates, &work->seen,
                                &work->seen_capacity)) {
    ixs_arena_destroy_transient(&work->arena);
    return false;
  }
  return true;
}

static facts_symbol_slot *facts_symbol_find(facts_worklist *work,
                                            const char *name) {
  size_t index;
  if (!work->symbols)
    return NULL;
  index = ixs_hash_ptr(name) & (work->symbol_capacity - 1u);
  while (work->symbols[index].name && work->symbols[index].name != name)
    index = (index + 1u) & (work->symbol_capacity - 1u);
  return &work->symbols[index];
}

static bool facts_symbol_table_grow(facts_worklist *work) {
  size_t new_capacity =
      work->symbol_capacity ? work->symbol_capacity * 2u : FACT_WORK_INIT_CAP;
  facts_symbol_slot *symbols;
  size_t i;
  if (new_capacity <= work->symbol_capacity ||
      new_capacity > SIZE_MAX / sizeof(*symbols))
    return false;
  symbols = ixs_arena_alloc(&work->arena, new_capacity * sizeof(*symbols),
                            sizeof(void *));
  if (!symbols)
    return false;
  memset(symbols, 0, new_capacity * sizeof(*symbols));
  for (i = 0; i < work->symbol_capacity; i++) {
    if (work->symbols[i].name) {
      size_t index = ixs_hash_ptr(work->symbols[i].name) & (new_capacity - 1u);
      while (symbols[index].name)
        index = (index + 1u) & (new_capacity - 1u);
      symbols[index] = work->symbols[i];
    }
  }
  work->symbols = symbols;
  work->symbol_capacity = new_capacity;
  return true;
}

static bool facts_occurrences_grow(facts_worklist *work) {
  size_t new_capacity = work->occurrence_capacity
                            ? work->occurrence_capacity * 2u
                            : FACT_WORK_INIT_CAP;
  facts_symbol_occurrence *occurrences;
  if (new_capacity <= work->occurrence_capacity ||
      new_capacity > SIZE_MAX / sizeof(*occurrences))
    return false;
  occurrences =
      ixs_arena_grow(&work->arena, work->occurrences,
                     work->occurrence_capacity * sizeof(*work->occurrences),
                     new_capacity * sizeof(*work->occurrences), sizeof(void *));
  if (!occurrences)
    return false;
  work->occurrences = occurrences;
  work->occurrence_capacity = new_capacity;
  return true;
}

static bool facts_worklist_add_symbol(facts_worklist *work, size_t predicate,
                                      const char *name) {
  facts_symbol_slot *slot;
  facts_symbol_occurrence *occurrence;
  size_t index;
  if (!work->symbol_capacity ||
      work->symbol_count >= work->symbol_capacity / 2u) {
    if (!facts_symbol_table_grow(work))
      return false;
  }
  if (work->occurrence_count >= work->occurrence_capacity &&
      !facts_occurrences_grow(work))
    return false;
  slot = facts_symbol_find(work, name);
  if (!slot)
    return false;
  if (!slot->name) {
    slot->name = name;
    slot->first_occurrence = SIZE_MAX;
    work->symbol_count++;
  }
  index = work->occurrence_count++;
  occurrence = &work->occurrences[index];
  occurrence->name = name;
  occurrence->predicate = predicate;
  occurrence->next_for_predicate = work->predicate_occurrences[predicate];
  occurrence->next_for_symbol = slot->first_occurrence;
  work->predicate_occurrences[predicate] = index;
  slot->first_occurrence = index;
  return true;
}

static bool facts_worklist_index_predicate(facts_worklist *work,
                                           size_t predicate, ixs_node *root) {
  facts_work_storage storage;
  ixs_arena traversal;
  query_node_set visited;
  ixs_node **stack = NULL;
  size_t stack_capacity = 0;
  size_t stack_count = 0;
  bool ok = false;
  ixs_arena_init_inline(&traversal, storage.bytes, sizeof(storage.bytes),
                        IXS_ARENA_DEFAULT_SIZE);
  memset(&visited, 0, sizeof(visited));
  if (!query_node_stack_push(&traversal, &stack, &stack_count, &stack_capacity,
                             root))
    goto cleanup;
  while (stack_count > 0) {
    ixs_node *node = stack[--stack_count];
    uint32_t child_count;
    uint32_t i;
    bool inserted;
    if (!query_node_set_insert(&traversal, &visited, node, &inserted))
      goto cleanup;
    if (!inserted)
      continue;
    if (node->tag == IXS_SYM &&
        !facts_worklist_add_symbol(work, predicate, node->u.name))
      goto cleanup;
    child_count = ixs_node_nchildren(node);
    for (i = 0; i < child_count; i++) {
      if (!query_node_stack_push(&traversal, &stack, &stack_count,
                                 &stack_capacity, ixs_node_child(node, i)))
        goto cleanup;
    }
  }
  ok = true;

cleanup:
  ixs_arena_destroy_transient(&traversal);
  return ok;
}

static bool facts_worklist_enqueue(facts_worklist *work, size_t predicate) {
  if (!work->active[predicate] || work->queued[predicate])
    return true;
  if (work->queue_count >= work->n_predicates)
    return false;
  work->queue[work->queue_tail] = predicate;
  work->queue_tail = (work->queue_tail + 1u) % work->n_predicates;
  work->queue_count++;
  work->queued[predicate] = true;
  return true;
}

static bool facts_worklist_build(facts_worklist *work,
                                 ixs_node *const *predicates) {
  size_t i;
  for (i = 0; i < work->n_predicates; i++) {
    if (work->seen) {
      size_t slot = predicates[i]->hash & (work->seen_capacity - 1u);
      while (work->seen[slot] && work->seen[slot] != predicates[i])
        slot = (slot + 1u) & (work->seen_capacity - 1u);
      if (work->seen[slot])
        continue;
      work->seen[slot] = predicates[i];
    }
    work->active[i] = true;
    if (!facts_worklist_index_predicate(work, i, predicates[i]) ||
        !facts_worklist_enqueue(work, i))
      return false;
  }
  return true;
}

static bool facts_worklist_enqueue_all(facts_worklist *work) {
  size_t i;
  for (i = 0; i < work->n_predicates; i++) {
    if (!facts_worklist_enqueue(work, i))
      return false;
  }
  return true;
}

static bool facts_worklist_enqueue_dependencies(facts_worklist *work,
                                                size_t predicate) {
  size_t occurrence_index = work->predicate_occurrences[predicate];
  if (occurrence_index == SIZE_MAX)
    return facts_worklist_enqueue_all(work);
  while (occurrence_index != SIZE_MAX) {
    facts_symbol_occurrence *occurrence = &work->occurrences[occurrence_index];
    facts_symbol_slot *slot = facts_symbol_find(work, occurrence->name);
    size_t dependent;
    if (!slot || !slot->name) {
      assert(slot && slot->name &&
             "group-union dependency index lost an indexed symbol");
      return false;
    }
    dependent = slot->first_occurrence;
    while (dependent != SIZE_MAX) {
      if (!facts_worklist_enqueue(work, work->occurrences[dependent].predicate))
        return false;
      dependent = work->occurrences[dependent].next_for_symbol;
    }
    occurrence_index = occurrence->next_for_predicate;
  }
  return true;
}

static ixs_bounds_build_status facts_ingest_original_predicates(
    ixs_bounds *candidate, ixs_node *const *predicates,
    const facts_worklist *work, facts_closure_capture *capture) {
  size_t i;
  for (i = 0; i < work->n_predicates; i++) {
    ixs_bounds_build_status status;
    if (!work->active[i])
      continue;
    status = bounds_assume_ingest_predicate(candidate, predicates[i]);
    if (status != IXS_BOUNDS_BUILD_OK)
      return status;
    facts_closure_capture_append(capture, predicates[i]);
  }
  return IXS_BOUNDS_BUILD_OK;
}

static ixs_bounds_build_status facts_process_predicate_worklist(
    ixs_ctx *ctx, ixs_bounds *candidate, ixs_node *const *predicates,
    facts_worklist *work, facts_closure_capture *capture) {
  while (work->queue_count > 0) {
    size_t predicate_index = work->queue[work->queue_head];
    ixs_node *predicate;
    ixs_bounds_build_status status;
    bool changed = false;
    bool limited = false;
    bool *old_observer = bounds_store_swap_change_observer(candidate, &changed);
    work->queue_head = (work->queue_head + 1u) % work->n_predicates;
    work->queue_count--;
    work->queued[predicate_index] = false;
    predicate = simp_simplify_bounds_status(ctx, predicates[predicate_index],
                                            candidate, &limited);
    if (limited) {
      (void)bounds_store_swap_change_observer(candidate, old_observer);
      return IXS_BOUNDS_BUILD_LIMIT;
    }
    if (!predicate || candidate->oom) {
      (void)bounds_store_swap_change_observer(candidate, old_observer);
      return IXS_BOUNDS_BUILD_OOM;
    }
    status = bounds_assume_ingest_predicate(candidate, predicate);
    (void)bounds_store_swap_change_observer(candidate, old_observer);
    if (status != IXS_BOUNDS_BUILD_OK)
      return status;
    if (changed)
      facts_closure_capture_append(capture, predicate);
    if (candidate->contradiction || ixs_bounds_has_empty(candidate))
      return IXS_BOUNDS_BUILD_OK;
    if (changed && !facts_worklist_enqueue_dependencies(work, predicate_index))
      return IXS_BOUNDS_BUILD_OOM;
  }
  return IXS_BOUNDS_BUILD_OK;
}

static ixs_bounds_build_status
facts_ingest_predicate_closure(ixs_ctx *ctx, ixs_bounds *candidate,
                               ixs_node *const *predicates, size_t n_predicates,
                               facts_closure_cache_result *cache_result) {
  facts_closure_cache_entry *cached = NULL;
  facts_closure_capture *capture_ptr = NULL;
  facts_work_storage storage;
  facts_worklist work;
  ixs_bounds_build_status status = IXS_BOUNDS_BUILD_OOM;
  bool cacheable =
      cache_result && candidate->nvars == 0 && candidate->nexprs == 0 &&
      candidate->nmod_inverse_watchers == 0 &&
      bounds_difference_is_empty(candidate) &&
      ixs_relation_algebra_endpoint_count(&candidate->relations) == 0 &&
      ixs_relation_algebra_edge_count(&candidate->relations) == 0 &&
      ixs_relation_algebra_total_count(&candidate->relations) == 0 &&
      candidate->nnonzero == 0 && !candidate->has_modrem &&
      !candidate->contradiction && !candidate->oom;

  if (cache_result)
    cache_result->store = false;
  if (cacheable) {
    cached = facts_closure_cache_lookup(ctx, predicates, n_predicates,
                                        &cache_result->hash);
    if (cached)
      return bounds_assume_ingest_predicates(
          candidate, cached->nodes + cached->n_predicates, cached->n_replay);
    if (n_predicates <= FACTS_CLOSURE_CACHE_SLOT_NODES) {
      memset(&cache_result->capture, 0, sizeof(cache_result->capture));
      cache_result->capture.replay_limit =
          FACTS_CLOSURE_CACHE_SLOT_NODES - n_predicates;
      capture_ptr = &cache_result->capture;
    }
  }
  if (!facts_worklist_init(&work, &storage, n_predicates))
    return IXS_BOUNDS_BUILD_OOM;
  if (!facts_worklist_build(&work, predicates))
    goto cleanup;

  /* Preserve original expression identities before fact-conditioned
   * rewrites. */
  status = facts_ingest_original_predicates(candidate, predicates, &work,
                                            capture_ptr);
  if (status != IXS_BOUNDS_BUILD_OK || candidate->contradiction ||
      ixs_bounds_has_empty(candidate))
    goto cleanup;

  /* A rewrite cannot introduce a symbol absent from its original predicate.
   * Revisit only predicates that share a symbol with a semantic refinement. */
  status = facts_process_predicate_worklist(ctx, candidate, predicates, &work,
                                            capture_ptr);

cleanup:
  if (status == IXS_BOUNDS_BUILD_OK && cacheable && capture_ptr)
    cache_result->store = true;
  ixs_arena_destroy_transient(&work.arena);
  return status;
}

IXS_STATIC ixs_bounds_build_status facts_store_ingest_predicate_branch(
    ixs_ctx *ctx, ixs_bounds *bounds, ixs_node *predicate) {
  return facts_ingest_predicate_closure(ctx, bounds, &predicate, 1u, NULL);
}

ixs_facts *ixs_facts_create_preds(ixs_session *s, ixs_node *const *predicates,
                                  size_t n_predicates) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds bounds;
  ixs_bounds_build_status status;
  ixs_facts *facts;
  if (!s)
    return NULL;
  ctx = ixs_session_bind(&binding, s);
  mark = ixs_arena_save(&ctx->scratch);
  status = ixs_bounds_build_ctx(&bounds, ctx, &ctx->scratch, predicates,
                                n_predicates);
  if (status != IXS_BOUNDS_BUILD_OK)
    goto failed;
  facts = ixs_arena_alloc(&ctx->arena, sizeof(*facts), sizeof(void *));
  if (!facts) {
    ixs_bounds_destroy(&bounds);
    goto failed;
  }
  memset(facts, 0, sizeof(*facts));
  facts->impl = binding.impl;
  facts->ctx = ctx;
  facts->epoch = binding.impl->epoch;
  bounds_query_reset_arena(&bounds);
  bounds_relation_projection_reset(&bounds, false);
  bounds_store_retarget_scratch(&bounds, NULL);
  assert(bounds.store_ctx != NULL && bounds.query_tracking_depth == 0 &&
         !bounds.query_state_owner && !bounds.query_state_borrowed &&
         bounds.query_state_arena.current == NULL &&
         bounds.query_state_arena.spare == NULL &&
         bounds.query_state_arena.inline_chunk == NULL &&
         bounds.query_arena.current == NULL &&
         bounds.query_arena.spare == NULL &&
         bounds.query_arena.inline_chunk == NULL);
  facts->bounds = bounds;
  facts->usable = true;
  facts->session_next = binding.impl->facts_head;
  binding.impl->facts_head = facts;
  ixs_session_unbind(&binding);
  return facts;

failed:
  ixs_arena_restore(&ctx->scratch, mark);
  ixs_session_unbind(&binding);
  return NULL;
}

ixs_facts *ixs_facts_create(ixs_session *s) {
  return ixs_facts_create_preds(s, NULL, 0);
}

static ixs_bounds_build_status facts_validate_closed_predicates(
    ixs_bounds *candidate, ixs_node *const *predicates, size_t n_predicates) {
  size_t i;
  if (candidate->contradiction || ixs_bounds_has_empty(candidate))
    return IXS_BOUNDS_BUILD_OK;
  for (i = 0; i < n_predicates; i++) {
    ixs_check_result defined;
    bool oom = false;
    bool limited = false;
    bool query_held = false;
    if (!ixs_bounds_query_hold_begin(candidate, predicates[i], &query_held))
      return candidate->oom ? IXS_BOUNDS_BUILD_OOM : IXS_BOUNDS_BUILD_LIMIT;
    defined =
        bounds_defined_check_detail(candidate, predicates[i], &oom, &limited);
    if (query_held)
      ixs_bounds_query_hold_end(candidate);
    if (defined == IXS_CHECK_TRUE)
      continue;
    if (oom || candidate->oom)
      return IXS_BOUNDS_BUILD_OOM;
    if (limited)
      return IXS_BOUNDS_BUILD_LIMIT;
    return assumption_invalid(candidate, "batch does not form a closed domain");
  }
  return IXS_BOUNDS_BUILD_OK;
}

static bool facts_assume_predicates(ixs_facts *facts,
                                    ixs_node *const *predicates,
                                    size_t n_predicates, bool require_closed) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds candidate;
  ixs_bounds_build_status status;
  facts_closure_cache_result closure_cache;
  bool candidate_ready = false;
  if (!facts_store_bind(facts, &binding, &ctx))
    return false;
  if (!facts_store_ready(facts)) {
    facts_store_unbind(facts, &binding);
    return false;
  }
  if (n_predicates == 0) {
    facts_store_unbind(facts, &binding);
    return true;
  }
  if (!predicates) {
    (void)assumption_invalid(&facts->bounds, "NULL array with nonzero count");
    facts_poison(facts);
    facts_store_unbind(facts, &binding);
    return false;
  }
  mark = ixs_arena_save(&ctx->scratch);
  if (!ixs_bounds_fork(&candidate, &facts->bounds)) {
    ixs_arena_restore(&ctx->scratch, mark);
    facts_poison(facts);
    facts_store_unbind(facts, &binding);
    return false;
  }
  candidate_ready = true;
  status =
      bounds_assume_validate_predicates(&candidate, predicates, n_predicates);
  if (status == IXS_BOUNDS_BUILD_OK)
    status = facts_ingest_predicate_closure(ctx, &candidate, predicates,
                                            n_predicates, &closure_cache);
  if (status == IXS_BOUNDS_BUILD_OK && require_closed)
    status =
        facts_validate_closed_predicates(&candidate, predicates, n_predicates);
  if (status == IXS_BOUNDS_BUILD_OK) {
    if (closure_cache.store)
      facts_closure_cache_store(ctx, predicates, n_predicates,
                                &closure_cache.capture, closure_cache.hash);
    facts_commit(facts, &candidate);
  } else {
    if (candidate_ready)
      ixs_bounds_destroy(&candidate);
    ixs_arena_restore(&ctx->scratch, mark);
    facts_poison(facts);
  }
  facts_store_unbind(facts, &binding);
  return status == IXS_BOUNDS_BUILD_OK;
}

bool ixs_facts_assume_preds(ixs_facts *facts, ixs_node *const *predicates,
                            size_t n_predicates) {
  return facts_assume_predicates(facts, predicates, n_predicates, true);
}

bool ixs_facts_assume_pred(ixs_facts *facts, ixs_node *pred) {
  return facts_assume_predicates(facts, &pred, 1, false);
}

bool ixs_facts_assume_range(ixs_facts *facts, ixs_node *expr,
                            const ixs_range_result *range) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds candidate;
  ixs_interval iv;
  bool candidate_ready = false;
  bool ok = false;
  if (!facts_store_bind(facts, &binding, &ctx))
    return false;
  if (!facts_store_ready(facts))
    goto cleanup;
  mark = ixs_arena_save(&ctx->scratch);
  if (!facts_node_ok(ctx, expr) || !range_result_to_interval(range, &iv))
    goto failed;
  if (!ixs_bounds_fork(&candidate, &facts->bounds))
    goto failed;
  candidate_ready = true;
  ixs_bounds_add_expr(&candidate, expr, iv);
  if (candidate.oom)
    goto failed;
  facts_commit(facts, &candidate);
  ok = true;
  goto cleanup;

failed:
  if (candidate_ready)
    ixs_bounds_destroy(&candidate);
  ixs_arena_restore(&ctx->scratch, mark);
  facts_poison(facts);

cleanup:
  facts_store_unbind(facts, &binding);
  return ok;
}

bool ixs_facts_derive_affine(ixs_facts *facts, ixs_node *base, int64_t scale,
                             int64_t offset, ixs_node *derived) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds candidate;
  ixs_interval iv, shifted;
  bool candidate_ready = false;
  bool query_held = false;
  bool ok = false;
  if (!facts_store_bind(facts, &binding, &ctx))
    return false;
  if (!facts_store_ready(facts))
    goto cleanup;
  mark = ixs_arena_save(&ctx->scratch);
  if (!facts_node_ok(ctx, base) || !facts_node_ok(ctx, derived))
    goto failed;
  if (!ixs_bounds_fork(&candidate, &facts->bounds))
    goto failed;
  candidate_ready = true;
  if (!ixs_bounds_query_hold_begin(&candidate, base, &query_held))
    goto failed;
  iv = ixs_bounds_get(&candidate, base);
  if (candidate.oom || !iv.valid || ixs_interval_is_empty(iv))
    goto failed;
  shifted = iv_add(iv_mul_const(iv, scale, 1), ixs_interval_exact(offset, 1));
  if (!shifted.valid || ixs_interval_is_empty(shifted))
    goto failed;
  ixs_bounds_add_expr(&candidate, derived, shifted);
  if (candidate.oom)
    goto failed;
  if (query_held) {
    ixs_bounds_query_hold_end(&candidate);
    query_held = false;
  }
  facts_commit(facts, &candidate);
  ok = true;
  goto cleanup;

failed:
  if (query_held)
    ixs_bounds_query_hold_end(&candidate);
  if (candidate_ready)
    ixs_bounds_destroy(&candidate);
  ixs_arena_restore(&ctx->scratch, mark);
  facts_poison(facts);

cleanup:
  facts_store_unbind(facts, &binding);
  return ok;
}

bool ixs_facts_substitute(ixs_facts *dst, const ixs_facts *src,
                          ixs_node *target, ixs_node *replacement) {
  return ixs_facts_substitute_multi(dst, src, 1, &target, &replacement);
}

static bool facts_substitution_inputs_ok(const ixs_facts *dst,
                                         const ixs_facts *src, ixs_ctx *ctx,
                                         uint32_t nsubs,
                                         ixs_node *const *targets,
                                         ixs_node *const *replacements) {
  uint32_t i;
  if (!src || src->impl != dst->impl || src->ctx != ctx ||
      src->epoch != dst->epoch || !facts_store_ready(src) ||
      (nsubs != 0 && (!targets || !replacements)))
    return false;
  for (i = 0; i < nsubs; i++) {
    if (!facts_node_ok(ctx, targets[i]) || !facts_node_ok(ctx, replacements[i]))
      return false;
  }
  return true;
}

static bool bounds_transfer_substituted_exprs(ixs_bounds *dst,
                                              const ixs_bounds *src,
                                              ixs_ctx *ctx, uint32_t nsubs,
                                              ixs_node *const *targets,
                                              ixs_node *const *replacements) {
  size_t i;
  for (i = 0; i < src->nexprs; i++) {
    if (!src->exprs[i].iv.valid) {
      bounds_store_mark_contradiction(dst);
      continue;
    }
    ixs_node *subst =
        simp_subs_multi(ctx, src->exprs[i].expr, nsubs, targets, replacements);
    if (!subst || ixs_node_is_sentinel(subst))
      return false;
    ixs_bounds_add_expr(dst, subst, src->exprs[i].iv);
    if (subst != src->exprs[i].expr)
      bounds_transfer_range(dst, subst, src->exprs[i].iv);
    if (dst->oom)
      return false;
  }
  return true;
}

static bool bounds_transfer_substituted_equalities(
    ixs_bounds *dst, const ixs_bounds *src, ixs_ctx *ctx, uint32_t nsubs,
    ixs_node *const *targets, ixs_node *const *replacements) {
  size_t i;
  for (i = 0; i < ixs_relation_algebra_edge_slot_count(&src->relations); i++) {
    const ixs_relation_edge *edge =
        ixs_relation_algebra_edge_at_slot(&src->relations, i);
    ixs_node *lhs;
    ixs_node *rhs;
    if (!edge)
      continue;
    lhs = simp_subs_multi(ctx, ixs_relation_edge_lhs(edge), nsubs, targets,
                          replacements);
    rhs = simp_subs_multi(ctx, ixs_relation_edge_rhs(edge), nsubs, targets,
                          replacements);
    if (!lhs || !rhs || ixs_node_is_sentinel(lhs) || ixs_node_is_sentinel(rhs))
      return false;
    bounds_admit_exact_relation(dst, lhs, rhs, ixs_relation_edge_offset(edge));
    if (dst->oom)
      return false;
  }
  return true;
}

static bool bounds_transfer_substituted_vars(ixs_bounds *dst,
                                             const ixs_bounds *src,
                                             ixs_ctx *ctx, uint32_t nsubs,
                                             ixs_node *const *targets,
                                             ixs_node *const *replacements) {
  size_t i;
  for (i = 0; i < src->nvars; i++) {
    ixs_node *sym =
        ixs_node_sym(ctx, src->vars[i].name, strlen(src->vars[i].name));
    ixs_node *subst;
    if (!sym || ixs_node_is_sentinel(sym))
      return false;
    subst = simp_subs_multi(ctx, sym, nsubs, targets, replacements);
    if (!subst || ixs_node_is_sentinel(subst))
      return false;
    if (subst == sym) {
      bounds_add_var_fact(dst, &src->vars[i]);
    } else {
      ixs_bounds_add_expr(dst, subst, src->vars[i].iv);
      bounds_transfer_var_fact(dst, &src->vars[i], subst);
    }
    if (dst->oom)
      return false;
  }
  return true;
}

static bool bounds_transfer_substituted_nonzero(ixs_bounds *dst,
                                                const ixs_bounds *src,
                                                ixs_ctx *ctx, uint32_t nsubs,
                                                ixs_node *const *targets,
                                                ixs_node *const *replacements) {
  size_t i;
  for (i = 0; i < src->nnonzero; i++) {
    ixs_node *subst =
        simp_subs_multi(ctx, src->nonzero[i], nsubs, targets, replacements);
    if (!subst || ixs_node_is_sentinel(subst))
      return false;
    bounds_add_nonzero(dst, subst);
    if (dst->oom)
      return false;
  }
  return true;
}

bool ixs_facts_substitute_multi(ixs_facts *dst, const ixs_facts *src,
                                uint32_t nsubs, ixs_node *const *targets,
                                ixs_node *const *replacements) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds candidate;
  bool candidate_ready = false;
  bool ok = false;

  if (!facts_store_bind(dst, &binding, &ctx))
    return false;
  if (!facts_store_ready(dst))
    goto cleanup;
  mark = ixs_arena_save(&ctx->scratch);
  if (!facts_substitution_inputs_ok(dst, src, ctx, nsubs, targets,
                                    replacements))
    goto failed;
  if (src == dst && nsubs == 0) {
    ok = true;
    goto cleanup;
  }
  if (!ixs_bounds_fork(&candidate, &dst->bounds))
    goto failed;
  candidate_ready = true;
  if (src->bounds.contradiction)
    bounds_store_mark_contradiction(&candidate);
  if (!bounds_transfer_substituted_exprs(&candidate, &src->bounds, ctx, nsubs,
                                         targets, replacements) ||
      !bounds_transfer_substituted_equalities(&candidate, &src->bounds, ctx,
                                              nsubs, targets, replacements) ||
      !bounds_transfer_substituted_vars(&candidate, &src->bounds, ctx, nsubs,
                                        targets, replacements) ||
      !bounds_transfer_substituted_nonzero(&candidate, &src->bounds, ctx, nsubs,
                                           targets, replacements))
    goto failed;
  facts_commit(dst, &candidate);
  ok = true;
  goto cleanup;

failed:
  if (candidate_ready)
    ixs_bounds_destroy(&candidate);
  ixs_arena_restore(&ctx->scratch, mark);
  facts_poison(dst);

cleanup:
  facts_store_unbind(dst, &binding);
  return ok;
}
