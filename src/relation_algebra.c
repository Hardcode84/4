/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "relation_algebra.h"

#include "rational.h"

#include <assert.h>
#include <limits.h>
#include <string.h>

#define RELATION_ENDPOINT_INDEX_INIT_CAP 8u
#define RELATION_EDGE_INDEX_INIT_CAP 8u

typedef enum {
  RELATION_CLOSURE_ASSERTED,
  RELATION_CLOSURE_TOTAL
} relation_closure_kind;

struct ixs_relation_endpoint {
  ixs_node *expr;
  ixs_relation_edge *edges;
  size_t asserted_parent, asserted_size, total_plus_one;
  ixs_relation_offset asserted_offset;
};

struct ixs_relation_total_node {
  size_t endpoint_index, parent, size;
  int64_t offset;
};

/* Immutable asserted edge lhs - rhs == offset. */
struct ixs_relation_edge {
  ixs_node *lhs, *rhs;
  ixs_relation_edge *next_lhs, *next_rhs;
  size_t lhs_endpoint, rhs_endpoint;
  int64_t offset;
};

IXS_STATIC ixs_relation_offset ixs_relation_offset_from_int64(int64_t value) {
  ixs_relation_offset result;
  result.lo = value >= 0 ? (uint64_t)value : (uint64_t)(-(value + 1)) + 1u;
  result.hi = 0;
  result.negative = value < 0;
  return result;
}

IXS_STATIC ixs_relation_offset
ixs_relation_offset_negate(ixs_relation_offset value) {
  if (value.lo || value.hi)
    value.negative = !value.negative;
  return value;
}

static int relation_offset_cmp(ixs_relation_offset lhs,
                               ixs_relation_offset rhs) {
  if (lhs.hi != rhs.hi)
    return lhs.hi < rhs.hi ? -1 : 1;
  if (lhs.lo != rhs.lo)
    return lhs.lo < rhs.lo ? -1 : 1;
  return 0;
}

IXS_STATIC bool ixs_relation_offset_add(ixs_relation_offset lhs,
                                        ixs_relation_offset rhs,
                                        ixs_relation_offset *result) {
  int cmp;
  bool carry, borrow;
  if (lhs.negative == rhs.negative) {
    result->lo = lhs.lo + rhs.lo;
    carry = result->lo < lhs.lo;
    result->hi = lhs.hi + rhs.hi;
    if (result->hi < lhs.hi || (carry && result->hi == UINT64_MAX))
      return false;
    result->hi += carry ? 1u : 0u;
    result->negative = lhs.negative;
  } else {
    cmp = relation_offset_cmp(lhs, rhs);
    if (cmp < 0) {
      ixs_relation_offset swap = lhs;
      lhs = rhs;
      rhs = swap;
    }
    borrow = lhs.lo < rhs.lo;
    result->lo = lhs.lo - rhs.lo;
    result->hi = lhs.hi - rhs.hi - (borrow ? 1u : 0u);
    result->negative = lhs.negative;
  }
  if (!result->lo && !result->hi)
    result->negative = false;
  return true;
}

IXS_STATIC bool ixs_relation_offset_equal(ixs_relation_offset lhs,
                                          ixs_relation_offset rhs) {
  return lhs.lo == rhs.lo && lhs.hi == rhs.hi && lhs.negative == rhs.negative;
}

IXS_STATIC bool ixs_relation_offset_to_int64(ixs_relation_offset value,
                                             int64_t *result) {
  uint64_t negative_limit = (uint64_t)INT64_MAX + 1u;
  if (value.hi || (!value.negative && value.lo > (uint64_t)INT64_MAX) ||
      (value.negative && value.lo > negative_limit))
    return false;
  if (!value.negative)
    *result = (int64_t)value.lo;
  else if (value.lo == negative_limit)
    *result = INT64_MIN;
  else
    *result = -(int64_t)value.lo;
  return true;
}

IXS_STATIC void ixs_relation_algebra_init(ixs_relation_algebra *algebra,
                                          ixs_arena *arena) {
  memset(algebra, 0, sizeof(*algebra));
  algebra->arena = arena;
}

static size_t relation_hash_pointer(const void *pointer) {
  uint64_t value = (uint64_t)(uintptr_t)pointer;
  value ^= value >> 33;
  value *= UINT64_C(0xff51afd7ed558ccd);
  value ^= value >> 33;
  return (size_t)value;
}

static size_t relation_endpoint_slot(const size_t *index, size_t capacity,
                                     const ixs_relation_endpoint *endpoints,
                                     const ixs_node *expr) {
  size_t slot = relation_hash_pointer(expr) & (capacity - 1u);
  while (index[slot] && endpoints[index[slot] - 1u].expr != expr)
    slot = (slot + 1u) & (capacity - 1u);
  return slot;
}

/* Endpoint lookup is expected O(1). */
IXS_STATIC bool
ixs_relation_algebra_find_endpoint(const ixs_relation_algebra *algebra,
                                   const ixs_node *expr,
                                   size_t *endpoint_index) {
  size_t slot;
  if (!algebra->endpoint_index_capacity)
    return false;
  slot = relation_endpoint_slot(algebra->endpoint_index,
                                algebra->endpoint_index_capacity,
                                algebra->endpoints, expr);
  if (!algebra->endpoint_index[slot])
    return false;
  *endpoint_index = algebra->endpoint_index[slot] - 1u;
  return true;
}

static size_t relation_edge_hash(ixs_node *lhs, ixs_node *rhs, int64_t offset) {
  uint64_t value = (uint64_t)relation_hash_pointer(lhs);
  value ^= (uint64_t)relation_hash_pointer(rhs) + UINT64_C(0x9e3779b97f4a7c15) +
           (value << 6) + (value >> 2);
  value ^= (uint64_t)offset + UINT64_C(0x9e3779b97f4a7c15) + (value << 6) +
           (value >> 2);
  value ^= value >> 33;
  value *= UINT64_C(0xff51afd7ed558ccd);
  return (size_t)(value ^ (value >> 33));
}

static size_t relation_edge_slot(ixs_relation_edge *const *index,
                                 size_t capacity, ixs_node *lhs, ixs_node *rhs,
                                 int64_t offset) {
  size_t slot = relation_edge_hash(lhs, rhs, offset) & (capacity - 1u);
  while (index[slot] && (index[slot]->lhs != lhs || index[slot]->rhs != rhs ||
                         index[slot]->offset != offset))
    slot = (slot + 1u) & (capacity - 1u);
  return slot;
}

static ixs_relation_edge *
relation_find_edge(const ixs_relation_algebra *algebra, ixs_node *lhs,
                   ixs_node *rhs, int64_t offset) {
  int64_t reverse;
  size_t slot;
  if (!algebra->edge_index_capacity)
    return NULL;
  slot = relation_edge_slot(algebra->edge_index, algebra->edge_index_capacity,
                            lhs, rhs, offset);
  if (algebra->edge_index[slot])
    return algebra->edge_index[slot];
  if (!ixs_safe_neg(offset, &reverse))
    return NULL;
  slot = relation_edge_slot(algebra->edge_index, algebra->edge_index_capacity,
                            rhs, lhs, reverse);
  return algebra->edge_index[slot];
}

static void *relation_grow(ixs_arena *arena, void *old, size_t old_capacity,
                           size_t needed, size_t initial, size_t element_size,
                           size_t *capacity) {
  size_t grown = old_capacity;
  if (needed <= old_capacity) {
    *capacity = old_capacity;
    return old;
  }
  if (!grown)
    grown = initial;
  while (grown < needed) {
    if (grown > SIZE_MAX / 2u)
      return NULL;
    grown *= 2u;
  }
  if (old_capacity > SIZE_MAX / element_size || grown > SIZE_MAX / element_size)
    return NULL;
  old = ixs_arena_grow(arena, old, old_capacity * element_size,
                       grown * element_size, sizeof(void *));
  if (old)
    *capacity = grown;
  return old;
}

static void *relation_prepare_index(const ixs_relation_algebra *algebra,
                                    const ixs_relation_endpoint *endpoints,
                                    size_t count, bool endpoint_index,
                                    size_t *capacity) {
  size_t current = endpoint_index ? algebra->endpoint_index_capacity
                                  : algebra->edge_index_capacity;
  size_t grown = current ? current
                         : (endpoint_index ? RELATION_ENDPOINT_INDEX_INIT_CAP
                                           : RELATION_EDGE_INDEX_INIT_CAP);
  size_t element_size =
      endpoint_index ? sizeof(size_t) : sizeof(ixs_relation_edge *);
  void *storage;
  size_t i;
  while (count > grown - grown / 4u) {
    if (grown > SIZE_MAX / 2u)
      return NULL;
    grown *= 2u;
  }
  *capacity = grown;
  if (grown == current)
    return endpoint_index ? (void *)algebra->endpoint_index
                          : (void *)algebra->edge_index;
  if (grown > SIZE_MAX / element_size)
    return NULL;
  storage =
      ixs_arena_alloc(algebra->arena, grown * element_size, sizeof(void *));
  if (!storage)
    return NULL;
  memset(storage, 0, grown * element_size);
  if (endpoint_index) {
    size_t *index = storage;
    for (i = 0; i < algebra->endpoint_count; i++) {
      size_t slot =
          relation_endpoint_slot(index, grown, endpoints, endpoints[i].expr);
      index[slot] = i + 1u;
    }
  } else {
    ixs_relation_edge **index = storage;
    for (i = 0; i < current; i++) {
      ixs_relation_edge *edge = algebra->edge_index[i];
      size_t slot;
      if (!edge)
        continue;
      slot =
          relation_edge_slot(index, grown, edge->lhs, edge->rhs, edge->offset);
      index[slot] = edge;
    }
  }
  return storage;
}

static void relation_forest_node(const ixs_relation_algebra *algebra,
                                 relation_closure_kind kind, size_t id,
                                 size_t *parent, ixs_relation_offset *offset) {
  if (kind == RELATION_CLOSURE_ASSERTED) {
    assert(id < algebra->endpoint_count);
    *parent = algebra->endpoints[id].asserted_parent;
    *offset = algebra->endpoints[id].asserted_offset;
  } else {
    assert(id < algebra->total_count);
    *parent = algebra->total_nodes[id].parent;
    *offset = ixs_relation_offset_from_int64(algebra->total_nodes[id].offset);
  }
}

static bool relation_forest_arithmetic(relation_closure_kind kind,
                                       ixs_relation_offset lhs,
                                       ixs_relation_offset rhs, bool subtract,
                                       ixs_relation_offset *result) {
  int64_t lhs_value, rhs_value, value;
  if (kind == RELATION_CLOSURE_ASSERTED)
    return ixs_relation_offset_add(
        lhs, subtract ? ixs_relation_offset_negate(rhs) : rhs, result);
  if (!ixs_relation_offset_to_int64(lhs, &lhs_value) ||
      !ixs_relation_offset_to_int64(rhs, &rhs_value))
    return false;
  if (subtract ? !ixs_safe_sub(lhs_value, rhs_value, &value)
               : !ixs_safe_add(lhs_value, rhs_value, &value))
    return false;
  *result = ixs_relation_offset_from_int64(value);
  return true;
}

static void relation_forest_link(ixs_relation_algebra *algebra,
                                 relation_closure_kind kind, size_t id,
                                 size_t parent, ixs_relation_offset offset) {
  if (kind == RELATION_CLOSURE_ASSERTED) {
    algebra->endpoints[id].asserted_parent = parent;
    algebra->endpoints[id].asserted_offset = offset;
  } else {
    int64_t narrow = 0;
    bool representable = ixs_relation_offset_to_int64(offset, &narrow);
    assert(representable);
    (void)representable;
    algebra->total_nodes[id].parent = parent;
    algebra->total_nodes[id].offset = narrow;
  }
}

/* Checked total arithmetic preserves the former forest's int64 admission.
 * Successful operations are inverse-Ackermann amortized by size and path
 * compression. */
static bool relation_forest_find(ixs_relation_algebra *algebra,
                                 relation_closure_kind kind, size_t id,
                                 size_t *root, ixs_relation_offset *offset,
                                 bool compress) {
  ixs_relation_offset total = {0, 0, false};
  size_t count = kind == RELATION_CLOSURE_ASSERTED ? algebra->endpoint_count
                                                   : algebra->total_count;
  size_t current = id;
  size_t hops = 0;
  assert(id < count && root != NULL && offset != NULL);
  (void)count;
  for (;;) {
    ixs_relation_offset edge;
    size_t parent;
    relation_forest_node(algebra, kind, current, &parent, &edge);
    hops++;
    assert(parent < count && hops <= count);
    (void)hops;
    if (parent == current)
      break;
    if (!relation_forest_arithmetic(kind, total, edge, false, &total))
      return false;
    current = parent;
  }
  *root = current;
  *offset = total;
  if (!compress)
    return true;
  current = id;
  while (current != *root) {
    ixs_relation_offset edge;
    ixs_relation_offset remaining;
    size_t parent;
    relation_forest_node(algebra, kind, current, &parent, &edge);
    if (!relation_forest_arithmetic(kind, total, edge, true, &remaining))
      break;
    /* Compression changes links, not root cardinality. Union-by-size owns the
     * only component-size updates. */
    relation_forest_link(algebra, kind, current, *root, total);
    current = parent;
    total = remaining;
  }
  return true;
}

static ixs_relation_status relation_forest_union(ixs_relation_algebra *algebra,
                                                 relation_closure_kind kind,
                                                 size_t lhs, size_t rhs,
                                                 int64_t offset) {
  ixs_relation_offset lhs_offset, rhs_offset, implied, delta, reverse;
  ixs_relation_offset requested = ixs_relation_offset_from_int64(offset);
  size_t lhs_root, rhs_root, lhs_size, rhs_size;
  bool found;

  /* Total first runs without compression: UNREPRESENTABLE is transactional. */
  found = relation_forest_find(algebra, kind, lhs, &lhs_root, &lhs_offset,
                               kind == RELATION_CLOSURE_ASSERTED);
  if (found)
    found = relation_forest_find(algebra, kind, rhs, &rhs_root, &rhs_offset,
                                 kind == RELATION_CLOSURE_ASSERTED);
  if (!found) {
    assert(kind == RELATION_CLOSURE_TOTAL);
    return IXS_RELATION_STATUS_UNREPRESENTABLE;
  }
  if (lhs_root == rhs_root) {
    if (!relation_forest_arithmetic(kind, lhs_offset, rhs_offset, true,
                                    &implied))
      return IXS_RELATION_STATUS_UNREPRESENTABLE;
    if (kind == RELATION_CLOSURE_TOTAL) {
      found = relation_forest_find(algebra, kind, lhs, &lhs_root, &lhs_offset,
                                   true) &&
              relation_forest_find(algebra, kind, rhs, &rhs_root, &rhs_offset,
                                   true);
      assert(found);
      (void)found;
    }
    return ixs_relation_offset_equal(implied, requested)
               ? IXS_RELATION_STATUS_UNCHANGED
               : IXS_RELATION_STATUS_CONFLICT;
  }

  if (kind == RELATION_CLOSURE_ASSERTED) {
    lhs_size = algebra->endpoints[lhs_root].asserted_size;
    rhs_size = algebra->endpoints[rhs_root].asserted_size;
  } else {
    lhs_size = algebra->total_nodes[lhs_root].size;
    rhs_size = algebra->total_nodes[rhs_root].size;
  }
  assert(lhs_size && rhs_size && lhs_size <= SIZE_MAX - rhs_size);
  /* Preserve offset - lhs_offset + rhs_offset evaluation order. */
  if (!relation_forest_arithmetic(kind, requested, lhs_offset, true, &delta) ||
      !relation_forest_arithmetic(kind, delta, rhs_offset, false, &delta) ||
      (lhs_size > rhs_size &&
       !relation_forest_arithmetic(kind, ixs_relation_offset_from_int64(0),
                                   delta, true, &reverse))) {
    assert(kind == RELATION_CLOSURE_TOTAL);
    return IXS_RELATION_STATUS_UNREPRESENTABLE;
  }
  if (kind == RELATION_CLOSURE_TOTAL) {
    found =
        relation_forest_find(algebra, kind, lhs, &lhs_root, &lhs_offset,
                             true) &&
        relation_forest_find(algebra, kind, rhs, &rhs_root, &rhs_offset, true);
    assert(found);
    (void)found;
  }
  if (lhs_size <= rhs_size) {
    relation_forest_link(algebra, kind, lhs_root, rhs_root, delta);
    if (kind == RELATION_CLOSURE_ASSERTED)
      algebra->endpoints[rhs_root].asserted_size += lhs_size;
    else
      algebra->total_nodes[rhs_root].size += lhs_size;
  } else {
    relation_forest_link(algebra, kind, rhs_root, lhs_root, reverse);
    if (kind == RELATION_CLOSURE_ASSERTED)
      algebra->endpoints[lhs_root].asserted_size += rhs_size;
    else
      algebra->total_nodes[lhs_root].size += rhs_size;
  }
  return IXS_RELATION_STATUS_ADDED;
}

static void relation_endpoint_init(ixs_relation_algebra *algebra,
                                   ixs_node *expr, size_t *endpoint_index) {
  size_t id = algebra->endpoint_count++;
  algebra->endpoints[id].expr = expr;
  algebra->endpoints[id].edges = NULL;
  algebra->endpoints[id].asserted_parent = id;
  algebra->endpoints[id].asserted_size = 1u;
  algebra->endpoints[id].asserted_offset = ixs_relation_offset_from_int64(0);
  algebra->endpoints[id].total_plus_one = 0;
  *endpoint_index = id;
}

IXS_STATIC ixs_relation_status
ixs_relation_algebra_assert(ixs_relation_algebra *algebra, ixs_node *lhs,
                            ixs_node *rhs, int64_t offset) {
  ixs_relation_algebra staged;
  ixs_relation_endpoint *endpoints;
  ixs_relation_edge **edge_index;
  ixs_relation_edge *edge;
  ixs_arena_mark mark;
  ixs_relation_status status;
  size_t lhs_endpoint = 0, rhs_endpoint = 0;
  size_t endpoint_capacity, endpoint_index_capacity, edge_index_capacity;
  size_t *endpoint_index;
  size_t missing, slot;
  bool new_lhs, new_rhs;

  assert(algebra != NULL && algebra->arena != NULL && lhs != NULL &&
         rhs != NULL);
  if (lhs == rhs)
    return offset ? IXS_RELATION_STATUS_CONFLICT
                  : IXS_RELATION_STATUS_UNCHANGED;
  if (relation_find_edge(algebra, lhs, rhs, offset))
    return IXS_RELATION_STATUS_UNCHANGED;
  if (algebra->edge_count == SIZE_MAX)
    return IXS_RELATION_STATUS_OOM;

  mark = ixs_arena_save(algebra->arena);
  new_lhs = !ixs_relation_algebra_find_endpoint(algebra, lhs, &lhs_endpoint);
  new_rhs = !ixs_relation_algebra_find_endpoint(algebra, rhs, &rhs_endpoint);
  missing = (new_lhs ? 1u : 0u) + (new_rhs ? 1u : 0u);
  if (algebra->endpoint_count > SIZE_MAX - missing)
    goto oom;
  endpoints = relation_grow(algebra->arena, algebra->endpoints,
                            algebra->endpoint_capacity,
                            algebra->endpoint_count + missing, 4u,
                            sizeof(*endpoints), &endpoint_capacity);
  if (!endpoints)
    goto oom;
  endpoint_index = relation_prepare_index(algebra, endpoints,
                                          algebra->endpoint_count + missing,
                                          true, &endpoint_index_capacity);
  edge_index = relation_prepare_index(algebra, NULL, algebra->edge_count + 1u,
                                      false, &edge_index_capacity);
  if (!endpoint_index || !edge_index)
    goto oom;
  edge = ixs_arena_alloc(algebra->arena, sizeof(*edge), sizeof(void *));
  if (!edge)
    goto oom;

  staged = *algebra;
  staged.endpoints = endpoints;
  staged.endpoint_capacity = endpoint_capacity;
  staged.endpoint_index = endpoint_index;
  staged.endpoint_index_capacity = endpoint_index_capacity;
  staged.edge_index = edge_index;
  staged.edge_index_capacity = edge_index_capacity;
  if (new_lhs)
    relation_endpoint_init(&staged, lhs, &lhs_endpoint);
  if (new_rhs)
    relation_endpoint_init(&staged, rhs, &rhs_endpoint);
  status = relation_forest_union(&staged, RELATION_CLOSURE_ASSERTED,
                                 lhs_endpoint, rhs_endpoint, offset);
  if (status == IXS_RELATION_STATUS_CONFLICT) {
    ixs_arena_restore(algebra->arena, mark);
    return status;
  }
  assert(status == IXS_RELATION_STATUS_ADDED ||
         status == IXS_RELATION_STATUS_UNCHANGED);
  if (new_lhs) {
    slot = relation_endpoint_slot(staged.endpoint_index,
                                  staged.endpoint_index_capacity,
                                  staged.endpoints, lhs);
    staged.endpoint_index[slot] = lhs_endpoint + 1u;
  }
  if (new_rhs) {
    slot = relation_endpoint_slot(staged.endpoint_index,
                                  staged.endpoint_index_capacity,
                                  staged.endpoints, rhs);
    staged.endpoint_index[slot] = rhs_endpoint + 1u;
  }
  edge->lhs = lhs;
  edge->rhs = rhs;
  edge->lhs_endpoint = lhs_endpoint;
  edge->rhs_endpoint = rhs_endpoint;
  edge->offset = offset;
  edge->next_lhs = staged.endpoints[lhs_endpoint].edges;
  edge->next_rhs = staged.endpoints[rhs_endpoint].edges;
  staged.endpoints[lhs_endpoint].edges = edge;
  staged.endpoints[rhs_endpoint].edges = edge;
  slot = relation_edge_slot(staged.edge_index, staged.edge_index_capacity, lhs,
                            rhs, offset);
  staged.edge_index[slot] = edge;
  staged.edge_count++;
  *algebra = staged;
  return IXS_RELATION_STATUS_ADDED;

oom:
  ixs_arena_restore(algebra->arena, mark);
  return IXS_RELATION_STATUS_OOM;
}

static bool relation_total_lookup(const ixs_relation_algebra *algebra,
                                  size_t endpoint, size_t *total) {
  size_t plus_one = algebra->endpoints[endpoint].total_plus_one;
  if (!plus_one)
    return false;
  *total = plus_one - 1u;
  assert(*total < algebra->total_count &&
         algebra->total_nodes[*total].endpoint_index == endpoint);
  return true;
}

static void relation_total_init(ixs_relation_algebra *algebra, size_t endpoint,
                                size_t *total) {
  size_t id = algebra->total_count++;
  algebra->total_nodes[id].endpoint_index = endpoint;
  algebra->total_nodes[id].parent = id;
  algebra->total_nodes[id].size = 1u;
  algebra->total_nodes[id].offset = 0;
  algebra->endpoints[endpoint].total_plus_one = id + 1u;
  *total = id;
}

IXS_STATIC ixs_relation_status
ixs_relation_algebra_certify_total(ixs_relation_algebra *algebra, ixs_node *lhs,
                                   ixs_node *rhs, int64_t offset) {
  ixs_relation_algebra staged;
  ixs_relation_total_node *nodes;
  ixs_relation_edge *edge;
  ixs_relation_status status;
  ixs_arena_mark mark;
  size_t lhs_endpoint, rhs_endpoint, lhs_total = 0, rhs_total = 0;
  size_t total_capacity, missing;
  bool new_lhs, new_rhs;

  assert(algebra != NULL && lhs != NULL && rhs != NULL);
  if (lhs == rhs)
    return offset ? IXS_RELATION_STATUS_CONFLICT
                  : IXS_RELATION_STATUS_UNCHANGED;
  edge = relation_find_edge(algebra, lhs, rhs, offset);
  assert(edge != NULL);
  if (edge->lhs == lhs) {
    lhs_endpoint = edge->lhs_endpoint;
    rhs_endpoint = edge->rhs_endpoint;
  } else {
    assert(edge->rhs == lhs);
    lhs_endpoint = edge->rhs_endpoint;
    rhs_endpoint = edge->lhs_endpoint;
  }

  new_lhs = !relation_total_lookup(algebra, lhs_endpoint, &lhs_total);
  new_rhs = !relation_total_lookup(algebra, rhs_endpoint, &rhs_total);
  missing = (new_lhs ? 1u : 0u) + (new_rhs ? 1u : 0u);
  if (algebra->total_count > SIZE_MAX - missing)
    return IXS_RELATION_STATUS_OOM;
  mark = ixs_arena_save(algebra->arena);
  nodes = relation_grow(algebra->arena, algebra->total_nodes,
                        algebra->total_capacity, algebra->total_count + missing,
                        2u, sizeof(*nodes), &total_capacity);
  if (!nodes) {
    ixs_arena_restore(algebra->arena, mark);
    return IXS_RELATION_STATUS_OOM;
  }
  staged = *algebra;
  staged.total_nodes = nodes;
  staged.total_capacity = total_capacity;
  if (new_lhs)
    relation_total_init(&staged, lhs_endpoint, &lhs_total);
  if (new_rhs)
    relation_total_init(&staged, rhs_endpoint, &rhs_total);
  status = relation_forest_union(&staged, RELATION_CLOSURE_TOTAL, lhs_total,
                                 rhs_total, offset);
  if (status == IXS_RELATION_STATUS_UNREPRESENTABLE) {
    if (new_lhs)
      staged.endpoints[lhs_endpoint].total_plus_one = 0;
    if (new_rhs)
      staged.endpoints[rhs_endpoint].total_plus_one = 0;
    ixs_arena_restore(algebra->arena, mark);
    return status;
  }
  assert(status == IXS_RELATION_STATUS_ADDED ||
         status == IXS_RELATION_STATUS_UNCHANGED ||
         status == IXS_RELATION_STATUS_CONFLICT);
  *algebra = staged;
  return status;
}

IXS_STATIC ixs_relation_query_status ixs_relation_algebra_total_offset(
    ixs_relation_algebra *algebra, const ixs_node *lhs, const ixs_node *rhs,
    int64_t *offset) {
  ixs_relation_offset lhs_offset, rhs_offset, difference;
  size_t lhs_endpoint, rhs_endpoint, lhs_total, rhs_total;
  size_t lhs_root, rhs_root;
  assert(algebra != NULL && lhs != NULL && rhs != NULL && offset != NULL);
  if (lhs == rhs) {
    *offset = 0;
    return IXS_RELATION_QUERY_FOUND;
  }
  if (!ixs_relation_algebra_find_endpoint(algebra, lhs, &lhs_endpoint) ||
      !ixs_relation_algebra_find_endpoint(algebra, rhs, &rhs_endpoint) ||
      !relation_total_lookup(algebra, lhs_endpoint, &lhs_total) ||
      !relation_total_lookup(algebra, rhs_endpoint, &rhs_total))
    return IXS_RELATION_QUERY_NONE;
  if (!relation_forest_find(algebra, RELATION_CLOSURE_TOTAL, lhs_total,
                            &lhs_root, &lhs_offset, true) ||
      !relation_forest_find(algebra, RELATION_CLOSURE_TOTAL, rhs_total,
                            &rhs_root, &rhs_offset, true) ||
      (lhs_root == rhs_root &&
       !relation_forest_arithmetic(RELATION_CLOSURE_TOTAL, lhs_offset,
                                   rhs_offset, true, &difference)))
    return IXS_RELATION_QUERY_UNREPRESENTABLE;
  if (lhs_root != rhs_root)
    return IXS_RELATION_QUERY_NONE;
  if (!ixs_relation_offset_to_int64(difference, offset)) {
    assert(!"certified total offset did not narrow");
    return IXS_RELATION_QUERY_UNREPRESENTABLE;
  }
  return IXS_RELATION_QUERY_FOUND;
}

IXS_STATIC size_t
ixs_relation_algebra_endpoint_count(const ixs_relation_algebra *algebra) {
  return algebra->endpoint_count;
}

IXS_STATIC ixs_node *
ixs_relation_algebra_endpoint_expr(const ixs_relation_algebra *algebra,
                                   size_t endpoint_index) {
  return algebra->endpoints[endpoint_index].expr;
}

IXS_STATIC const ixs_relation_edge *
ixs_relation_algebra_first_edge(const ixs_relation_algebra *algebra,
                                size_t endpoint_index) {
  return algebra->endpoints[endpoint_index].edges;
}

IXS_STATIC ixs_relation_query_status ixs_relation_algebra_edge_neighbor(
    const ixs_relation_algebra *algebra, size_t endpoint_index,
    const ixs_relation_edge *edge, size_t *neighbor_endpoint,
    ixs_relation_offset *step, const ixs_relation_edge **next) {
  (void)algebra;
  if (edge->lhs_endpoint == endpoint_index) {
    *neighbor_endpoint = edge->rhs_endpoint;
    *step = ixs_relation_offset_negate(
        ixs_relation_offset_from_int64(edge->offset));
    *next = edge->next_lhs;
    return IXS_RELATION_QUERY_FOUND;
  }
  if (edge->rhs_endpoint == endpoint_index) {
    *neighbor_endpoint = edge->lhs_endpoint;
    *step = ixs_relation_offset_from_int64(edge->offset);
    *next = edge->next_rhs;
    return IXS_RELATION_QUERY_FOUND;
  }
  return IXS_RELATION_QUERY_INVALID;
}

IXS_STATIC size_t
ixs_relation_algebra_edge_slot_count(const ixs_relation_algebra *algebra) {
  return algebra->edge_index_capacity;
}

IXS_STATIC const ixs_relation_edge *
ixs_relation_algebra_edge_at_slot(const ixs_relation_algebra *algebra,
                                  size_t slot) {
  return algebra->edge_index[slot];
}

IXS_STATIC size_t
ixs_relation_algebra_edge_count(const ixs_relation_algebra *algebra) {
  return algebra->edge_count;
}

IXS_STATIC size_t
ixs_relation_algebra_total_count(const ixs_relation_algebra *algebra) {
  return algebra->total_count;
}

IXS_STATIC ixs_node *ixs_relation_edge_lhs(const ixs_relation_edge *edge) {
  return edge->lhs;
}

IXS_STATIC ixs_node *ixs_relation_edge_rhs(const ixs_relation_edge *edge) {
  return edge->rhs;
}

IXS_STATIC int64_t ixs_relation_edge_offset(const ixs_relation_edge *edge) {
  return edge->offset;
}

static void *relation_clone_array(ixs_arena *arena, size_t capacity,
                                  size_t used, size_t element_size,
                                  const void *source) {
  void *copy;
  if (!capacity)
    return NULL;
  if (capacity > SIZE_MAX / element_size)
    return NULL;
  copy = ixs_arena_alloc(arena, capacity * element_size, sizeof(void *));
  if (!copy)
    return NULL;
  memset(copy, 0, capacity * element_size);
  if (used)
    memcpy(copy, source, used * element_size);
  return copy;
}

/* Clone is O(V + E) and never borrows source-arena storage. */
IXS_STATIC ixs_relation_status
ixs_relation_algebra_clone(ixs_relation_algebra *dst,
                           const ixs_relation_algebra *src, ixs_arena *arena) {
  ixs_relation_algebra staged = *src;
  ixs_relation_edge *edge_storage;
  ixs_arena_mark mark;
  size_t edge_count = 0;
  size_t i;
  assert(dst != NULL && src != NULL && arena != NULL && dst != src);
  ixs_relation_algebra_init(dst, arena);
  mark = ixs_arena_save(arena);
  staged.arena = arena;
  staged.endpoints =
      relation_clone_array(arena, src->endpoint_capacity, src->endpoint_count,
                           sizeof(*staged.endpoints), src->endpoints);
  staged.endpoint_index = relation_clone_array(
      arena, src->endpoint_index_capacity, src->endpoint_index_capacity,
      sizeof(*staged.endpoint_index), src->endpoint_index);
  staged.total_nodes =
      relation_clone_array(arena, src->total_capacity, src->total_count,
                           sizeof(*staged.total_nodes), src->total_nodes);
  staged.edge_index = relation_clone_array(arena, src->edge_index_capacity, 0,
                                           sizeof(*staged.edge_index), NULL);
  edge_storage = relation_clone_array(arena, src->edge_count, 0,
                                      sizeof(*edge_storage), NULL);
  if ((src->endpoint_capacity && !staged.endpoints) ||
      (src->endpoint_index_capacity && !staged.endpoint_index) ||
      (src->total_capacity && !staged.total_nodes) ||
      (src->edge_index_capacity && !staged.edge_index) ||
      (src->edge_count && !edge_storage))
    goto oom;
  for (i = 0; i < src->endpoint_count; i++)
    staged.endpoints[i].edges = NULL;
  for (i = 0; i < src->edge_index_capacity; i++) {
    const ixs_relation_edge *source = src->edge_index[i];
    ixs_relation_edge *edge;
    if (!source)
      continue;
    assert(edge_count < src->edge_count &&
           source->lhs_endpoint < src->endpoint_count &&
           source->rhs_endpoint < src->endpoint_count);
    edge = &edge_storage[edge_count++];
    *edge = *source;
    edge->next_lhs = staged.endpoints[edge->lhs_endpoint].edges;
    edge->next_rhs = staged.endpoints[edge->rhs_endpoint].edges;
    staged.endpoints[edge->lhs_endpoint].edges = edge;
    staged.endpoints[edge->rhs_endpoint].edges = edge;
    staged.edge_index[i] = edge;
  }
  assert(edge_count == src->edge_count);
  *dst = staged;
  return IXS_RELATION_STATUS_OK;

oom:
  ixs_arena_restore(arena, mark);
  ixs_relation_algebra_init(dst, arena);
  return IXS_RELATION_STATUS_OOM;
}
