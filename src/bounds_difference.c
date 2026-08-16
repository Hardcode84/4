/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds_difference.h"

#include "additive_row.h"
#include "bounds_store.h"
#include "hash.h"

#include <assert.h>
#include <stdlib.h>
#include <string.h>

#define BOUNDS_DIFFERENCE_INDEX_INIT_CAP 8u

typedef struct {
  ixs_arena_mark mark;
  size_t *queue;
  size_t epoch;
  size_t capacity;
  size_t head;
  size_t tail;
  size_t count;
} difference_worklist;

IXS_STATIC void bounds_difference_init(ixs_bounds *b) {
  b->difference_index = NULL;
  b->difference_vars = NULL;
  b->ndifferences = 0;
  b->ndifference_vars = 0;
  b->difference_index_cap = 0;
  b->difference_var_cap = 0;
  b->difference_epoch = 0;
}

IXS_STATIC void bounds_difference_inherit_fork(ixs_bounds *dst,
                                               const ixs_bounds *src) {
  dst->difference_index = NULL;
  dst->difference_vars = NULL;
  dst->ndifferences = src->ndifferences;
  dst->ndifference_vars = src->ndifference_vars;
  dst->difference_index_cap = src->difference_index_cap;
  dst->difference_var_cap = src->difference_var_cap;
  dst->difference_epoch = src->difference_epoch;
}

IXS_STATIC bool bounds_difference_clone_fork(ixs_bounds *dst,
                                             const ixs_bounds *src) {
  if (src->difference_index_cap) {
    if (!src->difference_index ||
        src->difference_index_cap > SIZE_MAX / sizeof(*dst->difference_index))
      return false;
    dst->difference_index = ixs_arena_alloc(dst->scratch,
                                            src->difference_index_cap *
                                                sizeof(*dst->difference_index),
                                            sizeof(void *));
    if (!dst->difference_index)
      return false;
    memcpy(dst->difference_index, src->difference_index,
           src->difference_index_cap * sizeof(*src->difference_index));
  }
  if (src->difference_var_cap) {
    if (!src->difference_vars ||
        src->difference_var_cap > SIZE_MAX / sizeof(*dst->difference_vars))
      return false;
    dst->difference_vars = ixs_arena_alloc(
        dst->scratch, src->difference_var_cap * sizeof(*dst->difference_vars),
        sizeof(void *));
    if (!dst->difference_vars)
      return false;
    memcpy(dst->difference_vars, src->difference_vars,
           src->difference_var_cap * sizeof(*src->difference_vars));
  }
  return true;
}

IXS_STATIC bool bounds_difference_is_empty(const ixs_bounds *b) {
  return b->ndifferences == 0 && b->ndifference_vars == 0;
}

static size_t difference_hash(ixs_node *lhs, ixs_node *rhs, int64_t offset) {
  uint64_t x = (uint64_t)ixs_hash_ptr(lhs);
  x ^= (uint64_t)ixs_hash_ptr(rhs) + UINT64_C(0x9e3779b97f4a7c15) + (x << 6) +
       (x >> 2);
  x ^= (uint64_t)offset + UINT64_C(0x9e3779b97f4a7c15) + (x << 6) + (x >> 2);
  x ^= x >> 33;
  x *= UINT64_C(0xff51afd7ed558ccd);
  x ^= x >> 33;
  return (size_t)x;
}

/* Exact-edge lookup is expected O(1); growth rehashes at 75% load. */
static size_t difference_index_slot(ixs_difference_constraint *const *index,
                                    size_t capacity, ixs_node *lhs,
                                    ixs_node *rhs, int64_t offset) {
  size_t slot = difference_hash(lhs, rhs, offset) & (capacity - 1u);
  while (index[slot] && (index[slot]->lhs != lhs || index[slot]->rhs != rhs ||
                         index[slot]->offset != offset))
    slot = (slot + 1u) & (capacity - 1u);
  return slot;
}

static bool difference_prepare_index(ixs_bounds *b, size_t count,
                                     ixs_difference_constraint ***prepared,
                                     size_t *prepared_capacity) {
  size_t capacity = b->difference_index_cap;
  ixs_difference_constraint **index;
  size_t i;

  if (capacity && count <= capacity - capacity / 4u) {
    *prepared = b->difference_index;
    *prepared_capacity = capacity;
    return true;
  }
  if (!capacity)
    capacity = BOUNDS_DIFFERENCE_INDEX_INIT_CAP;
  while (count > capacity - capacity / 4u) {
    if (capacity > SIZE_MAX / 2u)
      return false;
    capacity *= 2u;
  }
  if (capacity > SIZE_MAX / sizeof(*index))
    return false;
  index =
      ixs_arena_alloc(b->scratch, capacity * sizeof(*index), sizeof(void *));
  if (!index)
    return false;
  memset(index, 0, capacity * sizeof(*index));
  for (i = 0; i < b->difference_index_cap; i++) {
    ixs_difference_constraint *edge = b->difference_index[i];
    size_t slot;
    if (!edge)
      continue;
    slot = difference_index_slot(index, capacity, edge->lhs, edge->rhs,
                                 edge->offset);
    index[slot] = edge;
  }
  *prepared = index;
  *prepared_capacity = capacity;
  return true;
}

/* Relation metadata is absent from non-relational fact sets. Geometric growth
 * keeps appending graph variables amortized O(1) while stable var indices keep
 * the parallel table independent of var-array relocation. */
static bool difference_prepare_vars(ixs_bounds *b, size_t count) {
  ixs_difference_var *vars;
  size_t capacity = b->difference_var_cap;
  size_t old_bytes;
  size_t new_bytes;

  if (count <= capacity)
    return true;
  if (!capacity)
    capacity = 1u;
  while (capacity < count) {
    if (capacity > SIZE_MAX / 2u)
      return false;
    capacity *= 2u;
  }
  if (b->difference_var_cap > SIZE_MAX / sizeof(*vars) ||
      capacity > SIZE_MAX / sizeof(*vars))
    return false;
  old_bytes = b->difference_var_cap * sizeof(*vars);
  new_bytes = capacity * sizeof(*vars);
  vars = ixs_arena_grow(b->scratch, b->difference_vars, old_bytes, new_bytes,
                        sizeof(void *));
  if (!vars)
    return false;
  memset(vars + b->difference_var_cap, 0,
         (capacity - b->difference_var_cap) * sizeof(*vars));
  b->difference_vars = vars;
  b->difference_var_cap = capacity;
  return true;
}

static bool difference_worklist_init(ixs_bounds *b, difference_worklist *work) {
  size_t count = b->ndifference_vars;
  memset(work, 0, sizeof(*work));
  work->mark = ixs_arena_save(b->scratch);
  work->capacity = count;
  if (count == 0)
    return true;
  if (b->difference_epoch == SIZE_MAX ||
      count > SIZE_MAX / sizeof(*work->queue)) {
    b->oom = true;
    return false;
  }
  work->epoch = ++b->difference_epoch;
  work->queue =
      ixs_arena_alloc(b->scratch, count * sizeof(*work->queue), sizeof(void *));
  if (!work->queue) {
    ixs_arena_restore(b->scratch, work->mark);
    b->oom = true;
    return false;
  }
  return true;
}

static void difference_worklist_destroy(ixs_bounds *b,
                                        difference_worklist *work) {
  ixs_arena_restore(b->scratch, work->mark);
}

static bool difference_var_active(const ixs_bounds *b, size_t var_index) {
  const ixs_difference_var *var;
  if (var_index >= b->nvars || var_index >= b->difference_var_cap)
    return false;
  var = &b->difference_vars[var_index];
  return var->incoming || var->outgoing;
}

static bool difference_enqueue(ixs_bounds *b, difference_worklist *work,
                               size_t var_index) {
  ixs_difference_var *var;
  if (var_index >= b->nvars)
    return false;
  if (!difference_var_active(b, var_index))
    return true;
  var = &b->difference_vars[var_index];
  if (var->queue_epoch == work->epoch)
    return true;
  if (work->count >= work->capacity)
    return false;
  work->queue[work->tail] = var_index;
  work->tail = (work->tail + 1u) % work->capacity;
  work->count++;
  var->queue_epoch = work->epoch;
  return true;
}

static size_t difference_pop(ixs_bounds *b, difference_worklist *work) {
  size_t var_index = work->queue[work->head];
  work->head = (work->head + 1u) % work->capacity;
  work->count--;
  b->difference_vars[var_index].queue_epoch = 0;
  return var_index;
}

/* Existing potentials satisfy every published edge. Adding one edge can only
 * invalidate paths containing that edge. A strictly improving path of nvars
 * edges repeats a vertex, so its repeated segment is a negative cycle. The
 * work is proportional to the affected directed component and has no semantic
 * iteration cap. */
static bool difference_validate_edge(ixs_bounds *b, size_t lhs_var,
                                     size_t rhs_var, int64_t offset) {
  difference_worklist work;
  int64_t candidate;

  if (!ixs_safe_add(b->difference_vars[rhs_var].potential, offset,
                    &candidate)) {
    b->oom = true;
    return false;
  }
  if (b->difference_vars[lhs_var].potential <= candidate)
    return true;
  if (!difference_worklist_init(b, &work))
    return false;

  b->difference_vars[lhs_var].potential = candidate;
  b->difference_vars[lhs_var].hops = 1u;
  if (!difference_enqueue(b, &work, lhs_var)) {
    b->oom = true;
    difference_worklist_destroy(b, &work);
    return false;
  }

  while (work.count && !b->contradiction && !b->oom) {
    size_t source = difference_pop(b, &work);
    ixs_difference_constraint *edge = b->difference_vars[source].outgoing;
    while (edge) {
      size_t target = edge->lhs_var;
      if (!ixs_safe_add(b->difference_vars[source].potential, edge->offset,
                        &candidate)) {
        b->oom = true;
        break;
      }
      if (b->difference_vars[target].potential > candidate) {
        if (b->difference_vars[source].hops >= b->ndifference_vars - 1u) {
          bounds_store_mark_contradiction(b);
          break;
        }
        b->difference_vars[target].potential = candidate;
        b->difference_vars[target].hops = b->difference_vars[source].hops + 1u;
        if (!difference_enqueue(b, &work, target)) {
          b->oom = true;
          break;
        }
      }
      edge = edge->next_rhs;
    }
  }
  difference_worklist_destroy(b, &work);
  return !b->oom;
}

static bool difference_refine_upper(ixs_bounds *b, ixs_var_bound *var,
                                    int64_t upper) {
  ixs_interval refined;
  if (!var || (!var->iv.hi_inf &&
               ixs_rat_cmp(upper, 1, var->iv.hi_p, var->iv.hi_q) >= 0))
    return false;
  refined = var->iv;
  refined.hi_p = upper;
  refined.hi_q = 1;
  refined.hi_inf = false;
  (void)bounds_store_set_var_interval(b, var, refined);
  bounds_store_invalidate_reads(b);
  bounds_store_refine_var_bits(b, var);
  return true;
}

static bool difference_refine_lower(ixs_bounds *b, ixs_var_bound *var,
                                    int64_t lower) {
  ixs_interval refined;
  if (!var || (!var->iv.lo_inf &&
               ixs_rat_cmp(lower, 1, var->iv.lo_p, var->iv.lo_q) <= 0))
    return false;
  refined = var->iv;
  refined.lo_p = lower;
  refined.lo_q = 1;
  refined.lo_inf = false;
  (void)bounds_store_set_var_interval(b, var, refined);
  bounds_store_invalidate_reads(b);
  bounds_store_refine_var_bits(b, var);
  return true;
}

static ixs_interval difference_symbol_interval(ixs_bounds *b,
                                               ixs_var_bound *var,
                                               ixs_node *symbol) {
  ixs_interval interval = var->iv;
  assert(symbol != NULL && symbol->tag == IXS_SYM);
  /* A graph endpoint's canonical alias is therefore the endpoint itself. */
  if (b->nexprs)
    interval = iv_intersect(interval, bounds_store_expr_interval(b, symbol));
  if (var->modulus > 0)
    interval = ixs_interval_intersect_congruence(interval, var->modulus,
                                                 var->remainder);
  return interval;
}

static bool difference_propagate_upper(ixs_bounds *b, difference_worklist *work,
                                       size_t var_index) {
  ixs_difference_constraint *edge = b->difference_vars[var_index].outgoing;
  ixs_var_bound *var = &b->vars[var_index];
  ixs_interval interval;
  int64_t endpoint;
  int64_t derived;
  if (!edge)
    return true;
  interval = difference_symbol_interval(b, var, edge->rhs);
  if (!interval.valid || interval.hi_inf)
    return !b->oom;
  endpoint = ixs_rat_floor(interval.hi_p, interval.hi_q);
  while (edge && !b->contradiction) {
    if (ixs_safe_add(endpoint, edge->offset, &derived) &&
        difference_refine_upper(b, &b->vars[edge->lhs_var], derived) &&
        !difference_enqueue(b, work, edge->lhs_var)) {
      b->oom = true;
      return false;
    }
    edge = edge->next_rhs;
  }
  return !b->oom;
}

static bool difference_propagate_lower(ixs_bounds *b, difference_worklist *work,
                                       size_t var_index) {
  ixs_difference_constraint *edge = b->difference_vars[var_index].incoming;
  ixs_var_bound *var = &b->vars[var_index];
  ixs_interval interval;
  int64_t endpoint;
  int64_t derived;
  if (!edge)
    return true;
  interval = difference_symbol_interval(b, var, edge->lhs);
  if (!interval.valid || interval.lo_inf)
    return !b->oom;
  endpoint = ixs_rat_ceil(interval.lo_p, interval.lo_q);
  while (edge && !b->contradiction) {
    if (ixs_safe_sub(endpoint, edge->offset, &derived) &&
        difference_refine_lower(b, &b->vars[edge->rhs_var], derived) &&
        !difference_enqueue(b, work, edge->rhs_var)) {
      b->oom = true;
      return false;
    }
    edge = edge->next_lhs;
  }
  return !b->oom;
}

/* Existing edges are already closed. An insertion needs an endpoint worklist
 * only when the new edge itself can tighten one of its endpoints. */
static bool difference_edge_can_refine(ixs_bounds *b,
                                       const ixs_difference_constraint *edge) {
  ixs_interval interval;
  int64_t endpoint;
  int64_t derived;

  interval = difference_symbol_interval(b, &b->vars[edge->rhs_var], edge->rhs);
  if (interval.valid && !interval.hi_inf) {
    endpoint = ixs_rat_floor(interval.hi_p, interval.hi_q);
    if (ixs_safe_add(endpoint, edge->offset, &derived) &&
        (b->vars[edge->lhs_var].iv.hi_inf ||
         ixs_rat_cmp(derived, 1, b->vars[edge->lhs_var].iv.hi_p,
                     b->vars[edge->lhs_var].iv.hi_q) < 0))
      return true;
  }

  interval = difference_symbol_interval(b, &b->vars[edge->lhs_var], edge->lhs);
  if (!interval.valid || interval.lo_inf)
    return false;
  endpoint = ixs_rat_ceil(interval.lo_p, interval.lo_q);
  return ixs_safe_sub(endpoint, edge->offset, &derived) &&
         (b->vars[edge->rhs_var].iv.lo_inf ||
          ixs_rat_cmp(derived, 1, b->vars[edge->rhs_var].iv.lo_p,
                      b->vars[edge->rhs_var].iv.lo_q) > 0);
}

static bool difference_propagate_indices(ixs_bounds *b, size_t first,
                                         size_t second, bool have_second) {
  difference_worklist work;
  bool first_active;
  bool second_active;

  if (!b || b->oom || b->contradiction || b->ndifferences == 0)
    return true;
  first_active = difference_var_active(b, first);
  second_active =
      have_second && second != first && difference_var_active(b, second);
  if (!first_active && !second_active)
    return true;
  if (!difference_worklist_init(b, &work))
    return false;
  if ((first_active && !difference_enqueue(b, &work, first)) ||
      (second_active && !difference_enqueue(b, &work, second))) {
    b->oom = true;
    difference_worklist_destroy(b, &work);
    return false;
  }

  /* Each strict interval refinement schedules only its adjacent variable.
   * With a feasible graph, closure is finite and costs the successful
   * relaxations plus the incident edges they inspect. */
  while (work.count && !b->oom && !b->contradiction) {
    size_t var_index = difference_pop(b, &work);
    if (!difference_propagate_upper(b, &work, var_index) || b->contradiction ||
        !difference_propagate_lower(b, &work, var_index))
      break;
  }
  difference_worklist_destroy(b, &work);
  return !b->oom;
}

IXS_STATIC void bounds_difference_propagate_symbol(ixs_bounds *b,
                                                   const char *name) {
  ixs_var_bound *var;
  size_t index;
  if (!b || b->oom || !name || b->ndifferences == 0)
    return;
  var = bounds_store_find_var(b, name);
  if (!var)
    return;
  index = (size_t)(var - b->vars);
  (void)difference_propagate_indices(b, index, 0, false);
}

static bool difference_register_exact_reverse(
    ixs_bounds *b, ixs_difference_constraint *const *index,
    size_t index_capacity, ixs_node *lhs, ixs_node *rhs, int64_t offset) {
  ixs_relation_status status;
  int64_t reverse_offset;
  size_t slot;
  if (!ixs_safe_neg(offset, &reverse_offset))
    return true;
  slot = difference_index_slot(index, index_capacity, rhs, lhs, reverse_offset);
  if (!index[slot])
    return true;
  bounds_store_publish_relation_status(
      b, ixs_relation_algebra_assert(&b->relations, lhs, rhs, offset));
  if (b->oom || b->contradiction)
    return false;
  status = ixs_relation_algebra_certify_total(&b->relations, lhs, rhs, offset);
  switch (status) {
  case IXS_RELATION_STATUS_ADDED:
    bounds_store_mark_semantic_changed(b);
    bounds_store_invalidate_reads(b);
    return true;
  case IXS_RELATION_STATUS_OK:
  case IXS_RELATION_STATUS_UNCHANGED:
  case IXS_RELATION_STATUS_UNREPRESENTABLE:
    return true;
  case IXS_RELATION_STATUS_CONFLICT:
    bounds_store_mark_contradiction(b);
    return false;
  case IXS_RELATION_STATUS_OOM:
    b->oom = true;
    return false;
  }
  assert(0 && "unknown certified exact-relation insertion result");
  abort();
}

static void difference_add_constraint(ixs_bounds *b, ixs_node *lhs,
                                      ixs_node *rhs, int64_t offset) {
  ixs_difference_constraint **index;
  ixs_difference_constraint *edge;
  size_t lhs_var;
  size_t rhs_var;
  size_t index_capacity;
  size_t new_vertices;
  size_t slot;

  if (!b || !lhs || !rhs || lhs == rhs || lhs->tag != IXS_SYM ||
      rhs->tag != IXS_SYM || b->oom || b->contradiction)
    return;
  if (b->difference_index_cap) {
    slot = difference_index_slot(b->difference_index, b->difference_index_cap,
                                 lhs, rhs, offset);
    if (b->difference_index[slot])
      return;
  }
  if (!bounds_store_get_or_create_var_index(b, lhs->u.name, &lhs_var) ||
      !bounds_store_get_or_create_var_index(b, rhs->u.name, &rhs_var) ||
      b->ndifferences == SIZE_MAX || !difference_prepare_vars(b, b->nvars) ||
      !difference_prepare_index(b, b->ndifferences + 1u, &index,
                                &index_capacity)) {
    b->oom = true;
    return;
  }
  new_vertices = (!b->difference_vars[lhs_var].incoming &&
                  !b->difference_vars[lhs_var].outgoing) +
                 (!b->difference_vars[rhs_var].incoming &&
                  !b->difference_vars[rhs_var].outgoing);
  if (b->ndifference_vars > SIZE_MAX - new_vertices) {
    b->oom = true;
    return;
  }
  edge = ixs_arena_alloc(b->scratch, sizeof(*edge), sizeof(void *));
  if (!edge) {
    b->oom = true;
    return;
  }
  edge->lhs = lhs;
  edge->rhs = rhs;
  edge->next_lhs = b->difference_vars[lhs_var].incoming;
  edge->next_rhs = b->difference_vars[rhs_var].outgoing;
  edge->lhs_var = lhs_var;
  edge->rhs_var = rhs_var;
  edge->offset = offset;
  b->difference_vars[lhs_var].incoming = edge;
  b->difference_vars[rhs_var].outgoing = edge;
  b->difference_index = index;
  b->difference_index_cap = index_capacity;
  slot = difference_index_slot(index, index_capacity, lhs, rhs, offset);
  index[slot] = edge;
  b->ndifferences++;
  b->ndifference_vars += new_vertices;
  bounds_store_mark_semantic_changed(b);
  bounds_store_invalidate_reads(b);
  if (!difference_validate_edge(b, lhs_var, rhs_var, offset) ||
      b->contradiction)
    return;
  if (!difference_register_exact_reverse(b, index, index_capacity, lhs, rhs,
                                         offset) ||
      b->contradiction)
    return;
  if (difference_edge_can_refine(b, edge))
    (void)difference_propagate_indices(b, lhs_var, rhs_var, true);
}

static bool difference_extract_unit(ixs_node *expr, ixs_node **lhs,
                                    ixs_node **rhs, int64_t *constant) {
  ixs_node *positive;
  ixs_node *negative;
  if (!expr || expr->tag != IXS_ADD)
    return false;
  if (!ixs_additive_row_unit_pair(expr, &positive, &negative, constant) ||
      positive->tag != IXS_SYM || negative->tag != IXS_SYM)
    return false;
  *lhs = positive;
  *rhs = negative;
  return true;
}

IXS_STATIC bool bounds_difference_exact_unit_value(ixs_bounds *b,
                                                   ixs_node *expr,
                                                   int64_t *value) {
  ixs_node *lhs;
  ixs_node *rhs;
  int64_t constant;
  int64_t difference;
  return difference_extract_unit(expr, &lhs, &rhs, &constant) && !b->oom &&
         !b->contradiction &&
         ixs_relation_algebra_total_symbol_difference(&b->relations, lhs, rhs,
                                                      &difference) &&
         ixs_safe_add(constant, difference, value);
}

IXS_STATIC void bounds_difference_add_range(ixs_bounds *b, ixs_node *expr,
                                            ixs_interval interval) {
  ixs_node *lhs;
  ixs_node *rhs;
  int64_t constant;
  int64_t endpoint;
  int64_t offset;
  if (!interval.valid || !difference_extract_unit(expr, &lhs, &rhs, &constant))
    return;
  if (!interval.hi_inf) {
    endpoint = ixs_rat_floor(interval.hi_p, interval.hi_q);
    if (ixs_safe_sub(endpoint, constant, &offset))
      difference_add_constraint(b, lhs, rhs, offset);
  }
  if (!b->oom && !b->contradiction && !interval.lo_inf) {
    endpoint = ixs_rat_ceil(interval.lo_p, interval.lo_q);
    if (ixs_safe_sub(constant, endpoint, &offset))
      difference_add_constraint(b, rhs, lhs, offset);
  }
}
