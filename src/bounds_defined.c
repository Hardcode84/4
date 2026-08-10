/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds_defined.h"
#include "bounds_assume.h"
#include "bounds_query.h"
#include "bounds_range.h"
#include "bounds_relation.h"
#include "bounds_store.h"
#include "query_walk.h"
#include "simplify.h"

#include <assert.h>
#include <limits.h>
#include <string.h>

/* Definedness is a proof query, not an evaluator.  All expression traversal
 * uses growable work stacks.  The branch-sensitive Piecewise pass invokes a
 * structural-only subquery for its conditions and values, so C recursion is
 * statically bounded while nested Piecewise DAGs remain unbounded in size. */
#define DEFINED_BOUNDS_CACHE_MIN_CAP 32u
#define DEFINED_BOUNDS_CACHE_CAP 8192u

typedef struct {
  ixs_ctx *ctx;
  ixs_arena *arena;
  ixs_arena_mark arena_mark;
  ixs_node **active_piecewise;
  size_t active_piecewise_count;
  size_t active_piecewise_capacity;
  size_t visited;
  bool oom;
  bool limited;
  bool invalid;
} defined_state;

typedef struct {
  ixs_node *node;
  ixs_node *selected_condition;
  ixs_node *selected_value;
  uint32_t next_child;
  uint32_t nchildren;
  ixs_check_result result;
  bool started;
  bool selected_piecewise_case;
} defined_frame;

typedef struct {
  defined_state *state;
  ixs_bounds *bounds;
  ixs_query_walk walk;
  ixs_query_node_memo memo;
  ixs_check_result answer;
  unsigned pw_depth;
} defined_query;

typedef struct {
  ixs_node *node;
  uint32_t next_child;
  uint32_t nchildren;
} defined_depth_frame;

typedef struct {
  defined_state *state;
  ixs_query_walk walk;
  ixs_query_node_memo memo;
  bool *shared;
  size_t visited;
} defined_depth_query;

typedef struct {
  ixs_arena_mark mark;
  ixs_ctx *old_ctx;
  ixs_bounds_cache_entry *old_cache;
  size_t old_cache_cap;
  bool active;
} defined_cache_scope;

static void defined_state_init(defined_state *state, ixs_ctx *ctx,
                               ixs_bounds *bounds) {
  memset(state, 0, sizeof(*state));
  state->ctx = ctx;
  state->arena = &bounds->query_arena;
  state->arena_mark = ixs_arena_save(state->arena);
}

static void defined_state_destroy(defined_state *state) {
  ixs_arena_restore(state->arena, state->arena_mark);
}

static bool defined_piecewise_enter(defined_state *state, ixs_node *expr) {
  size_t i;
  for (i = 0; i < state->active_piecewise_count; i++) {
    if (state->active_piecewise[i] == expr) {
      state->invalid = true;
      return false;
    }
  }
  if (state->active_piecewise_count == state->active_piecewise_capacity) {
    size_t next_capacity = state->active_piecewise_capacity
                               ? state->active_piecewise_capacity * 2u
                               : 8u;
    ixs_node **grown;
    if (next_capacity <= state->active_piecewise_capacity ||
        next_capacity > SIZE_MAX / sizeof(*grown)) {
      state->oom = true;
      return false;
    }
    grown = ixs_arena_grow(state->arena, state->active_piecewise,
                           state->active_piecewise_capacity * sizeof(*grown),
                           next_capacity * sizeof(*grown), sizeof(void *));
    if (!grown) {
      state->oom = true;
      return false;
    }
    state->active_piecewise = grown;
    state->active_piecewise_capacity = next_capacity;
  }
  state->active_piecewise[state->active_piecewise_count++] = expr;
  return true;
}

static void defined_piecewise_leave(defined_state *state) {
  assert(state->active_piecewise_count != 0);
  state->active_piecewise_count--;
}

static ixs_check_result defined_combine(ixs_check_result lhs,
                                        ixs_check_result rhs) {
  if (lhs == IXS_CHECK_FALSE || rhs == IXS_CHECK_FALSE)
    return IXS_CHECK_FALSE;
  if (lhs == IXS_CHECK_UNKNOWN || rhs == IXS_CHECK_UNKNOWN)
    return IXS_CHECK_UNKNOWN;
  return IXS_CHECK_TRUE;
}

static int defined_fixed_child_count(ixs_tag tag) {
  switch (tag) {
  case IXS_INT:
  case IXS_RAT:
  case IXS_SYM:
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    return 0;
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
  case IXS_NOT:
    return 1;
  case IXS_MOD:
  case IXS_CMP:
    return 2;
  default:
    return -1;
  }
}

/* Keep this local walker independent of the public assert-based accessors.
 * It also gives malformed internal nodes the required conservative result. */
IXS_STATIC bool defined_child_count(ixs_node *node, uint32_t *out) {
  int fixed;
  if (!node || !out)
    return false;
  fixed = defined_fixed_child_count(node->tag);
  if (fixed >= 0) {
    *out = (uint32_t)fixed;
    return true;
  }
  switch (node->tag) {
  case IXS_ADD:
    if (!node->u.add.coeff || (node->u.add.nterms > 0 && !node->u.add.terms) ||
        node->u.add.nterms > (UINT32_MAX - 1u) / 2u)
      return false;
    *out = 1u + 2u * node->u.add.nterms;
    return true;
  case IXS_MUL:
    if (!node->u.mul.coeff ||
        (node->u.mul.nfactors > 0 && !node->u.mul.factors) ||
        node->u.mul.nfactors == UINT32_MAX)
      return false;
    *out = 1u + node->u.mul.nfactors;
    return true;
  case IXS_PIECEWISE:
    if ((node->u.pw.ncases > 0 && !node->u.pw.cases) ||
        node->u.pw.ncases > UINT32_MAX / 2u)
      return false;
    *out = 2u * node->u.pw.ncases;
    return true;
  case IXS_AND:
  case IXS_OR:
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
    if (node->u.assoc.nargs < 2 || !node->u.assoc.args)
      return false;
    *out = node->u.assoc.nargs;
    return true;
  default:
    return false;
  }
}

IXS_STATIC ixs_node *defined_child_at(ixs_node *node, uint32_t child) {
  switch (node->tag) {
  case IXS_ADD:
    if (child == 0)
      return node->u.add.coeff;
    child--;
    return (child & 1u) == 0u ? node->u.add.terms[child / 2u].coeff
                              : node->u.add.terms[child / 2u].term;
  case IXS_MUL:
    return child == 0 ? node->u.mul.coeff
                      : node->u.mul.factors[child - 1u].base;
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
    return node->u.unary.arg;
  case IXS_NOT:
    return node->u.unary_bool.arg;
  case IXS_MOD:
  case IXS_CMP:
    return child == 0 ? node->u.binary.lhs : node->u.binary.rhs;
  case IXS_PIECEWISE:
    return (child & 1u) == 0u ? node->u.pw.cases[child / 2u].value
                              : node->u.pw.cases[child / 2u].cond;
  case IXS_AND:
  case IXS_OR:
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
    return node->u.assoc.args[child];
  default:
    return NULL;
  }
}

static ixs_query_walk_step defined_depth_push(defined_depth_query *query,
                                              ixs_node *node,
                                              uint32_t nchildren) {
  ixs_query_check_memo_entry *entry =
      ixs_query_node_memo_get(&query->memo, node, true);
  defined_depth_frame *frame;
  ixs_query_walk_step step;
  if (!entry) {
    query->state->oom = true;
    return IXS_QUERY_WALK_OOM;
  }
  if (entry->active) {
    query->state->invalid = true;
    return IXS_QUERY_WALK_STOP;
  }
  if (entry->complete) {
    if (query->shared)
      *query->shared = true;
    return IXS_QUERY_WALK_ADVANCED;
  }
  step = ixs_query_walk_push(&query->walk, node);
  if (step != IXS_QUERY_WALK_ADVANCED)
    return step;
  frame = IXS_QUERY_WALK_TOP(&query->walk);
  frame->nchildren = nchildren;
  entry->active = true;
  query->visited++;
  return step;
}

/* hot */
static ixs_query_walk_step defined_depth_advance(void *state, void *top) {
  defined_depth_query *query = state;
  defined_depth_frame *frame = top;
  ixs_query_check_memo_entry *entry;
  ixs_node *child;
  uint32_t nchildren;
  if (frame->next_child < frame->nchildren) {
    child = defined_child_at(frame->node, frame->next_child++);
    if (!child || !defined_child_count(child, &nchildren)) {
      query->state->invalid = true;
      return IXS_QUERY_WALK_STOP;
    }
    return defined_depth_push(query, child, nchildren);
  }
  entry = ixs_query_node_memo_get(&query->memo, frame->node, false);
  if (!entry || !entry->active) {
    query->state->invalid = true;
    return IXS_QUERY_WALK_STOP;
  }
  entry->active = false;
  entry->complete = true;
  IXS_QUERY_WALK_POP(&query->walk);
  return IXS_QUERY_WALK_ADVANCED;
}

static bool defined_bounds_depth_safe(defined_state *state, ixs_bounds *b,
                                      ixs_node *root, bool *shared,
                                      size_t *node_visits) {
  ixs_arena_mark mark;
  defined_depth_query query;
  ixs_query_walk_step step;
  uint32_t nchildren;

  if (shared)
    *shared = false;
  if (node_visits)
    *node_visits = 0;
  if (!root || !defined_child_count(root, &nchildren)) {
    state->invalid = true;
    return false;
  }
  mark = ixs_arena_save(b->scratch);
  query.state = state;
  query.shared = shared;
  query.visited = 0;
  IXS_QUERY_NODE_MEMO_INIT(&query.memo, b->scratch, ixs_query_check_memo_entry,
                           node);
  IXS_QUERY_WALK_INIT_CAP(&query.walk, b->scratch, &state->oom,
                          defined_depth_frame, node, 32u);
  step = defined_depth_push(&query, root, nchildren);
  if (step == IXS_QUERY_WALK_ADVANCED)
    step =
        ixs_query_walk_drive(&query.walk, &query, defined_depth_advance, NULL);
  if (step == IXS_QUERY_WALK_ADVANCED && node_visits)
    *node_visits = query.visited;
  ixs_arena_restore(b->scratch, mark);
  return step == IXS_QUERY_WALK_ADVANCED;
}

static size_t defined_bounds_cache_capacity(size_t node_visits) {
  size_t cap = DEFINED_BOUNDS_CACHE_MIN_CAP;
  while (cap < DEFINED_BOUNDS_CACHE_CAP && node_visits > cap / 2u)
    cap *= 2u;
  return cap;
}

static bool defined_cache_scope_init(defined_cache_scope *scope,
                                     defined_state *state, ixs_bounds *b,
                                     size_t node_visits) {
  ixs_bounds_cache_entry *cache;
  size_t cache_cap = defined_bounds_cache_capacity(node_visits);
  scope->mark = ixs_arena_save(b->scratch);
  scope->old_cache = b->cache;
  scope->old_cache_cap = b->cache_cap;
  scope->active = false;
  cache =
      ixs_arena_alloc(b->scratch, cache_cap * sizeof(*cache), sizeof(void *));
  if (!cache) {
    state->oom = true;
    ixs_arena_restore(b->scratch, scope->mark);
    return false;
  }
  memset(cache, 0, cache_cap * sizeof(*cache));
  b->cache = cache;
  b->cache_cap = cache_cap;
  /* Direct overrides are enough for a proof query. Canonical aliases expand
   * recursively and can revisit a shared DAG before the interval cache sees
   * it, so disable that optional path inside this bounded scope. */
  scope->old_ctx = bounds_store_swap_active_context(b, NULL);
  scope->active = true;
  return true;
}

static void defined_cache_scope_destroy(defined_cache_scope *scope,
                                        ixs_bounds *b) {
  if (!scope->active)
    return;
  (void)bounds_store_swap_active_context(b, scope->old_ctx);
  b->cache = scope->old_cache;
  b->cache_cap = scope->old_cache_cap;
  ixs_arena_restore(b->scratch, scope->mark);
  scope->active = false;
}

static ixs_check_result defined_relation_zero(defined_state *state,
                                              ixs_bounds *b, ixs_node *expr,
                                              ixs_cmp_op op) {
  ixs_interval iv;
  ixs_interval zero;
  ixs_check_result result;
  ixs_bitfacts bits;
  int64_t modulus, remainder;
  defined_cache_scope cache_scope;
  size_t node_visits;
  bool shared;

  if ((op == IXS_CMP_EQ || op == IXS_CMP_NE) &&
      bounds_store_contains_nonzero(b, expr))
    return op == IXS_CMP_NE ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
  if (!defined_bounds_depth_safe(state, b, expr, &shared, &node_visits) ||
      !defined_cache_scope_init(&cache_scope, state, b, node_visits))
    return IXS_CHECK_UNKNOWN;
  iv = ixs_bounds_get(b, expr);
  if (b->oom) {
    state->oom = true;
    result = IXS_CHECK_UNKNOWN;
    goto cleanup;
  }
  if (iv.valid) {
    zero = ixs_interval_exact(0, 1);
    result = bounds_range_check_relation(&iv, &zero, op);
    if (result != IXS_CHECK_UNKNOWN)
      goto cleanup;
  }

  result = IXS_CHECK_UNKNOWN;
  if (op != IXS_CMP_EQ && op != IXS_CMP_NE)
    goto cleanup;
  if (!shared && ixs_bounds_get_bitfacts(b, expr, &bits) &&
      bits.known_one != 0) {
    result = op == IXS_CMP_NE ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
    goto cleanup;
  }
  if (b->oom) {
    state->oom = true;
    goto cleanup;
  }
  if (expr->tag == IXS_SYM &&
      bounds_store_get_modrem(b, expr->u.name, &modulus, &remainder) &&
      remainder != 0) {
    (void)modulus;
    result = op == IXS_CMP_NE ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
  }

cleanup:
  defined_cache_scope_destroy(&cache_scope, b);
  return result;
}

static ixs_check_result defined_condition_truth(defined_state *state,
                                                ixs_bounds *b, ixs_node *cond) {
  ixs_check_result result;
  defined_cache_scope cache_scope;
  size_t node_visits;
  bool shared;
  if (ixs_node_is_known_false(cond))
    return IXS_CHECK_FALSE;
  if (ixs_node_is_known_true(cond))
    return IXS_CHECK_TRUE;
  if (cond->tag == IXS_CMP) {
    if (ixs_node_is_zero(cond->u.binary.rhs)) {
      result = defined_relation_zero(state, b, cond->u.binary.lhs,
                                     cond->u.binary.cmp_op);
      if (result != IXS_CHECK_UNKNOWN || state->oom)
        return result;
    }
    if (!defined_bounds_depth_safe(state, b, cond, &shared, &node_visits))
      return IXS_CHECK_UNKNOWN;
    if (shared) {
      if (!ixs_node_is_zero(cond->u.binary.rhs))
        return IXS_CHECK_UNKNOWN;
      return defined_relation_zero(state, b, cond->u.binary.lhs,
                                   cond->u.binary.cmp_op);
    }
    if (!defined_cache_scope_init(&cache_scope, state, b, node_visits))
      return IXS_CHECK_UNKNOWN;
    result = bounds_range_check_raw(b, cond);
    if (b->oom)
      state->oom = true;
    defined_cache_scope_destroy(&cache_scope, b);
    return result;
  }
  return defined_relation_zero(state, b, cond, IXS_CMP_NE);
}

static ixs_node *defined_condition_assumption(defined_state *state,
                                              ixs_node *cond, bool value,
                                              struct ixs_node_impl *storage) {
  memset(storage, 0, sizeof(*storage));
  storage->tag = IXS_CMP;
  storage->u.binary.rhs = state->ctx->node_zero;
  if (cond->tag == IXS_CMP) {
    storage->u.binary.lhs = cond->u.binary.lhs;
    storage->u.binary.rhs = cond->u.binary.rhs;
    storage->u.binary.cmp_op = value ? cond->u.binary.cmp_op
                                     : ixs_cmp_op_negate(cond->u.binary.cmp_op);
  } else {
    storage->u.binary.lhs = cond;
    storage->u.binary.cmp_op = value ? IXS_CMP_NE : IXS_CMP_EQ;
  }
  return storage;
}

static ixs_check_result defined_eval(defined_state *state, ixs_bounds *b,
                                     ixs_node *root, unsigned pw_depth);

static bool defined_match_shared_rounding_piecewise(ixs_node *expr,
                                                    ixs_node **condition,
                                                    ixs_node **argument) {
  ixs_node *floor_value;
  ixs_node *ceil_value;

  if (!expr || expr->tag != IXS_PIECEWISE || expr->u.pw.ncases != 2u ||
      !expr->u.pw.cases || !ixs_node_is_known_true(expr->u.pw.cases[1].cond))
    return false;
  floor_value = expr->u.pw.cases[0].value;
  ceil_value = expr->u.pw.cases[1].value;
  if (!floor_value || !ceil_value || floor_value->tag != IXS_FLOOR ||
      ceil_value->tag != IXS_CEIL ||
      floor_value->u.unary.arg != ceil_value->u.unary.arg)
    return false;
  *condition = expr->u.pw.cases[0].cond;
  *argument = floor_value->u.unary.arg;
  return *condition && *argument;
}

static void defined_partition_add(unsigned *partitions,
                                  ixs_check_result result) {
  if (result == IXS_CHECK_TRUE)
    *partitions |= 1u;
  else if (result == IXS_CHECK_FALSE)
    *partitions |= 2u;
  else
    *partitions |= 4u;
}

static ixs_check_result defined_partition_result(unsigned partitions) {
  if (partitions == 1u)
    return IXS_CHECK_TRUE;
  if (partitions == 2u)
    return IXS_CHECK_FALSE;
  return IXS_CHECK_UNKNOWN;
}

typedef enum {
  DEFINED_PW_NEXT,
  DEFINED_PW_STOP,
  DEFINED_PW_FAILED
} defined_pw_step;

static bool defined_piecewise_active(defined_state *state,
                                     ixs_bounds *remaining, ixs_node *cond,
                                     ixs_node *value, unsigned pw_depth,
                                     unsigned *partitions) {
  ixs_arena_mark mark = ixs_arena_save(remaining->scratch);
  ixs_bounds active;
  struct ixs_node_impl assumption;
  bool active_ready = false;
  bool ok = false;
  if (!ixs_bounds_fork(&active, remaining)) {
    state->oom = true;
    goto cleanup;
  }
  active_ready = true;
  if (!ixs_bounds_add_assumption(
          &active,
          defined_condition_assumption(state, cond, true, &assumption))) {
    state->oom = true;
    goto cleanup;
  }
  if (!ixs_bounds_has_empty(&active)) {
    ixs_check_result result = defined_eval(state, &active, value, pw_depth);
    defined_partition_add(partitions, result);
  }
  ok = !state->oom && !state->limited;

cleanup:
  if (active_ready)
    ixs_bounds_destroy(&active);
  ixs_arena_restore(remaining->scratch, mark);
  return ok;
}

static defined_pw_step defined_piecewise_case(defined_state *state,
                                              ixs_bounds *remaining,
                                              const ixs_pwcase *pwcase,
                                              unsigned pw_depth,
                                              unsigned *partitions) {
  ixs_node *cond = pwcase->cond;
  ixs_check_result cond_defined =
      defined_eval(state, remaining, cond, pw_depth);
  ixs_check_result truth;
  struct ixs_node_impl assumption;

  if (state->oom || state->limited)
    return DEFINED_PW_FAILED;
  if (cond_defined != IXS_CHECK_TRUE) {
    defined_partition_add(partitions, cond_defined);
    return DEFINED_PW_STOP;
  }

  truth = defined_condition_truth(state, remaining, cond);
  if (state->oom)
    return DEFINED_PW_FAILED;
  if (truth == IXS_CHECK_FALSE)
    return DEFINED_PW_NEXT;
  if (!defined_bounds_depth_safe(state, remaining, cond, NULL, NULL)) {
    defined_partition_add(partitions, IXS_CHECK_UNKNOWN);
    return DEFINED_PW_STOP;
  }
  if (!defined_piecewise_active(state, remaining, cond, pwcase->value, pw_depth,
                                partitions))
    return DEFINED_PW_FAILED;
  if (truth == IXS_CHECK_TRUE)
    return DEFINED_PW_STOP;

  if (!ixs_bounds_add_assumption(
          remaining,
          defined_condition_assumption(state, cond, false, &assumption))) {
    state->oom = true;
    return DEFINED_PW_FAILED;
  }
  return DEFINED_PW_NEXT;
}

static bool defined_piecewise_shared_result(defined_state *state, ixs_bounds *b,
                                            ixs_node *expr, unsigned pw_depth,
                                            ixs_check_result *result) {
  ixs_node *condition;
  ixs_node *argument;
  ixs_check_result condition_defined;
  ixs_check_result argument_defined;

  if (!defined_match_shared_rounding_piecewise(expr, &condition, &argument))
    return false;
  condition_defined = defined_eval(state, b, condition, pw_depth);
  if (state->oom || state->limited) {
    *result = IXS_CHECK_UNKNOWN;
    return true;
  }
  argument_defined = defined_eval(state, b, argument, pw_depth);
  if (state->oom || state->limited) {
    *result = IXS_CHECK_UNKNOWN;
    return true;
  }
  *result = defined_combine(condition_defined, argument_defined);
  return *result != IXS_CHECK_UNKNOWN;
}

static ixs_check_result defined_piecewise_partitions(defined_state *state,
                                                     ixs_bounds *b,
                                                     ixs_node *expr,
                                                     unsigned pw_depth) {
  ixs_arena_mark outer_mark;
  ixs_bounds remaining;
  unsigned partitions = 0;
  uint32_t i;
  bool stopped = false;
  bool remaining_ready = false;

  outer_mark = ixs_arena_save(b->scratch);
  if (!ixs_bounds_fork(&remaining, b)) {
    state->oom = true;
    ixs_arena_restore(b->scratch, outer_mark);
    return IXS_CHECK_UNKNOWN;
  }
  remaining_ready = true;

  for (i = 0; i < expr->u.pw.ncases; i++) {
    defined_pw_step step;

    if (remaining.oom) {
      state->oom = true;
      break;
    }
    if (ixs_bounds_has_empty(&remaining)) {
      stopped = true;
      break;
    }
    step = defined_piecewise_case(state, &remaining, &expr->u.pw.cases[i],
                                  pw_depth, &partitions);
    if (step == DEFINED_PW_STOP) {
      stopped = true;
      break;
    }
    if (step == DEFINED_PW_FAILED)
      break;
  }

  if (!state->oom && !state->limited && !stopped && !remaining.oom &&
      !ixs_bounds_has_empty(&remaining))
    defined_partition_add(&partitions, IXS_CHECK_FALSE);
  if (remaining.oom)
    state->oom = true;

  if (remaining_ready)
    ixs_bounds_destroy(&remaining);
  ixs_arena_restore(b->scratch, outer_mark);
  if (state->oom || state->limited)
    return IXS_CHECK_UNKNOWN;
  return defined_partition_result(partitions);
}

static ixs_check_result defined_piecewise(defined_state *state, ixs_bounds *b,
                                          ixs_node *expr, unsigned pw_depth) {
  ixs_check_result shared;
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  if (!defined_piecewise_enter(state, expr))
    return IXS_CHECK_UNKNOWN;
  if (defined_piecewise_shared_result(state, b, expr, pw_depth, &shared)) {
    result = shared;
    goto cleanup;
  }
  if ((expr->u.pw.ncases > 0 && !expr->u.pw.cases) ||
      expr->u.pw.ncases > UINT32_MAX / 2u) {
    state->invalid = true;
    goto cleanup;
  }
  result = expr->u.pw.ncases == 0
               ? IXS_CHECK_FALSE
               : defined_piecewise_partitions(state, b, expr, pw_depth);

cleanup:
  defined_piecewise_leave(state);
  return result;
}

static ixs_check_result defined_finalize_node(defined_state *state,
                                              ixs_bounds *b, ixs_node *node,
                                              ixs_check_result result) {
  uint32_t i;
  if (node->tag == IXS_MUL) {
    for (i = 0; i < node->u.mul.nfactors; i++) {
      ixs_check_result guard;
      if (node->u.mul.factors[i].exp == 0)
        result = defined_combine(result, IXS_CHECK_UNKNOWN);
      if (node->u.mul.factors[i].exp >= 0)
        continue;
      guard = defined_relation_zero(state, b, node->u.mul.factors[i].base,
                                    IXS_CMP_NE);
      result = defined_combine(result, guard);
    }
  } else if (node->tag == IXS_MOD) {
    ixs_check_result guard =
        defined_relation_zero(state, b, node->u.binary.rhs, IXS_CMP_GT);
    result = defined_combine(result, guard);
  } else if (node->tag == IXS_XOR || node->tag == IXS_AND ||
             node->tag == IXS_OR) {
    for (i = 0; i < node->u.assoc.nargs; i++) {
      ixs_check_result guard =
          ixs_bounds_check_integer_valued(b, node->u.assoc.args[i]);
      result = defined_combine(result, guard);
    }
  }
  return result;
}

static ixs_query_walk_step defined_complete_frame(defined_query *query,
                                                  ixs_check_result result) {
  defined_frame *frame = IXS_QUERY_WALK_TOP(&query->walk);
  ixs_query_check_memo_entry *entry =
      ixs_query_node_memo_get(&query->memo, frame->node, false);
  if (!entry) {
    query->state->invalid = true;
    result = IXS_CHECK_UNKNOWN;
  } else {
    entry->result = result;
    entry->active = false;
    entry->complete = true;
  }
  IXS_QUERY_WALK_POP(&query->walk);
  if (query->walk.depth == 0) {
    query->answer = result;
    return IXS_QUERY_WALK_ADVANCED;
  }
  frame = IXS_QUERY_WALK_TOP(&query->walk);
  frame->result = defined_combine(frame->result, result);
  frame->next_child++;
  return IXS_QUERY_WALK_ADVANCED;
}

static void defined_start_nested_piecewise(defined_state *state,
                                           defined_frame *frame,
                                           ixs_check_result *direct,
                                           bool *has_direct) {
  ixs_node *node = frame->node;
  uint32_t i;
  if ((node->u.pw.ncases > 0 && !node->u.pw.cases) ||
      node->u.pw.ncases > UINT32_MAX / 2u) {
    state->invalid = true;
    *has_direct = true;
    return;
  }
  for (i = 0; i < node->u.pw.ncases; i++) {
    ixs_node *cond = node->u.pw.cases[i].cond;
    if (!cond || !node->u.pw.cases[i].value) {
      state->invalid = true;
      *has_direct = true;
      return;
    }
    if (ixs_node_is_known_false(cond))
      continue;
    if (!ixs_node_is_known_true(cond)) {
      *has_direct = true;
      return;
    }
    frame->selected_condition = cond;
    frame->selected_value = node->u.pw.cases[i].value;
    frame->selected_piecewise_case = true;
    frame->nchildren = 2u;
    return;
  }
  *direct = IXS_CHECK_FALSE;
  *has_direct = true;
}

static void defined_start_frame(defined_state *state, ixs_bounds *b,
                                defined_frame *frame, unsigned pw_depth,
                                ixs_check_result *direct, bool *has_direct) {
  ixs_node *node = frame->node;
  *direct = IXS_CHECK_UNKNOWN;
  *has_direct = false;

  if (!node || !ixs_ctx_owns_node(state->ctx, node) ||
      ixs_node_is_sentinel(node)) {
    state->invalid = true;
    *has_direct = true;
    return;
  }
  if (ixs_node_is_known_total(node)) {
    *direct = IXS_CHECK_TRUE;
    *has_direct = true;
    return;
  }
  if (state->visited != SIZE_MAX)
    state->visited++;

  /* A range constrains a node only where that node is defined. It cannot skip
   * the structural walk or discharge an operation's domain guards. */

  switch (node->tag) {
  case IXS_INT:
    *direct = IXS_CHECK_TRUE;
    *has_direct = true;
    return;
  case IXS_RAT:
    *direct = node->u.rat.q > 0 ? IXS_CHECK_TRUE : IXS_CHECK_UNKNOWN;
    *has_direct = true;
    return;
  case IXS_SYM:
    *direct = node->u.name ? IXS_CHECK_TRUE : IXS_CHECK_UNKNOWN;
    *has_direct = true;
    return;
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    *has_direct = true;
    return;
  case IXS_PIECEWISE:
    if (pw_depth == 0u) {
      *direct = defined_piecewise(state, b, node, 1u);
      *has_direct = true;
      return;
    }
    /* Nested Piecewise nodes are handled on this work stack when their first
     * reachable case is statically selected.  Unknown selection is a sound
     * UNKNOWN: branch-sensitive environment reasoning is performed only by
     * the statically bounded outer Piecewise pass. */
    defined_start_nested_piecewise(state, frame, direct, has_direct);
    return;
  case IXS_CMP:
    if (!ixs_cmp_op_valid(node->u.binary.cmp_op)) {
      state->invalid = true;
      *has_direct = true;
      return;
    }
    break;
  default:
    break;
  }
  if (!defined_child_count(node, &frame->nchildren)) {
    state->invalid = true;
    *has_direct = true;
  }
}

static ixs_query_walk_step defined_process_child(defined_query *query,
                                                 defined_frame *frame) {
  defined_state *state = query->state;
  ixs_node *child;
  ixs_query_check_memo_entry *entry;
  if (frame->next_child >= frame->nchildren)
    return IXS_QUERY_WALK_NEXT;

  if (frame->selected_piecewise_case)
    child = frame->next_child == 0u ? frame->selected_condition
                                    : frame->selected_value;
  else
    child = defined_child_at(frame->node, frame->next_child);
  if (!child) {
    state->invalid = true;
    frame->result = defined_combine(frame->result, IXS_CHECK_UNKNOWN);
    frame->next_child++;
    return IXS_QUERY_WALK_ADVANCED;
  }
  entry = ixs_query_node_memo_get(&query->memo, child, false);
  if (entry && entry->complete) {
    frame->result = defined_combine(frame->result, entry->result);
    frame->next_child++;
    return IXS_QUERY_WALK_ADVANCED;
  }
  if (entry && entry->active) {
    state->invalid = true;
    return IXS_QUERY_WALK_STOP;
  }
  if (!entry)
    entry = ixs_query_node_memo_get(&query->memo, child, true);
  if (!entry) {
    state->oom = true;
    return IXS_QUERY_WALK_OOM;
  }
  if (ixs_query_walk_push(&query->walk, child) != IXS_QUERY_WALK_ADVANCED)
    return IXS_QUERY_WALK_OOM;
  ((defined_frame *)IXS_QUERY_WALK_TOP(&query->walk))->result = IXS_CHECK_TRUE;
  entry->active = true;
  return IXS_QUERY_WALK_ADVANCED;
}

/* hot */
static ixs_query_walk_step defined_advance(void *state, void *top) {
  defined_query *query = state;
  defined_frame *frame = top;
  ixs_query_walk_step step;
  if (query->state->oom || query->state->limited || query->state->invalid)
    return IXS_QUERY_WALK_STOP;
  if (!frame->started) {
    ixs_check_result direct = IXS_CHECK_UNKNOWN;
    bool has_direct = false;
    defined_start_frame(query->state, query->bounds, frame, query->pw_depth,
                        &direct, &has_direct);
    if (query->state->limited)
      return IXS_QUERY_WALK_STOP;
    if (has_direct)
      return defined_complete_frame(query, direct);
    frame->started = true;
  }
  step = defined_process_child(query, frame);
  if (step != IXS_QUERY_WALK_NEXT)
    return step;
  frame->result = defined_finalize_node(query->state, query->bounds,
                                        frame->node, frame->result);
  return defined_complete_frame(query, frame->result);
}

static ixs_check_result defined_eval(defined_state *state, ixs_bounds *b,
                                     ixs_node *root, unsigned pw_depth) {
  ixs_arena_mark mark;
  defined_query query;
  ixs_query_check_memo_entry *root_entry;
  ixs_query_walk_step step;

  if (!root || state->oom || state->limited || state->invalid)
    return IXS_CHECK_UNKNOWN;
  mark = ixs_arena_save(b->scratch);
  query.state = state;
  query.bounds = b;
  query.answer = IXS_CHECK_UNKNOWN;
  query.pw_depth = pw_depth;
  IXS_QUERY_NODE_MEMO_INIT(&query.memo, b->scratch, ixs_query_check_memo_entry,
                           node);
  IXS_QUERY_WALK_INIT_CAP(&query.walk, b->scratch, &state->oom, defined_frame,
                          node, 32u);
  root_entry = ixs_query_node_memo_get(&query.memo, root, true);
  if (!root_entry) {
    state->oom = true;
    ixs_arena_restore(b->scratch, mark);
    return IXS_CHECK_UNKNOWN;
  }
  step = ixs_query_walk_push(&query.walk, root);
  if (step != IXS_QUERY_WALK_ADVANCED) {
    ixs_arena_restore(b->scratch, mark);
    return IXS_CHECK_UNKNOWN;
  }
  ((defined_frame *)IXS_QUERY_WALK_TOP(&query.walk))->result = IXS_CHECK_TRUE;
  root_entry->active = true;
  step = ixs_query_walk_drive(&query.walk, &query, defined_advance, NULL);
  ixs_arena_restore(b->scratch, mark);
  if (step != IXS_QUERY_WALK_ADVANCED || state->oom || state->limited ||
      state->invalid)
    return IXS_CHECK_UNKNOWN;
  return query.answer;
}

static bool bounds_defined_cache_lookup(ixs_bounds *b, ixs_node *expr,
                                        ixs_check_result *result) {
  size_t endpoint_index;
  bool without_equality;
  if (!bounds_query_is_tracking(b) || !b->query_state ||
      !ixs_relation_algebra_find_endpoint(&b->relations, expr, &endpoint_index))
    return false;
  without_equality = b->equality_disabled_depth != 0;
  return bounds_relation_projection_lookup_defined(b, endpoint_index,
                                                   without_equality, result);
}

static bool bounds_defined_cache_publish(ixs_bounds *b, ixs_node *expr,
                                         ixs_check_result result) {
  size_t endpoint_index;
  if (!bounds_query_is_tracking(b) || !b->query_state ||
      !ixs_relation_algebra_find_endpoint(&b->relations, expr, &endpoint_index))
    return true;
  if (!bounds_relation_projection_complete_defined(
          b, endpoint_index, b->equality_disabled_depth != 0, result)) {
    b->oom = true;
    return false;
  }
  return true;
}

typedef struct {
  ixs_bounds_transport_snapshot transport;
  size_t cycle_blocks;
  bool tracking;
} bounds_defined_query_snapshot;

static bounds_defined_query_snapshot
bounds_defined_query_observe(ixs_bounds *b) {
  bounds_defined_query_snapshot snapshot;
  snapshot.transport = ixs_bounds_query_transport_snapshot(b);
  snapshot.cycle_blocks = bounds_query_cycle_count(b);
  snapshot.tracking = bounds_query_is_tracking(b);
  return snapshot;
}

static bool bounds_defined_query_failed(ixs_bounds *b, defined_state *state,
                                        ixs_check_result result,
                                        bounds_defined_query_snapshot snapshot,
                                        bool *oom, bool *limited) {
  bool query_limited;
  bool query_cycle;
  bool query_invalid;
  if (state->limited && snapshot.tracking)
    bounds_query_note_limit(b);
  if (state->invalid && snapshot.tracking)
    bounds_query_note_invalid(b);
  query_limited = snapshot.tracking && result == IXS_CHECK_UNKNOWN &&
                  bounds_query_limited_since(b, snapshot.transport);
  query_cycle =
      snapshot.tracking && bounds_query_cycle_count(b) != snapshot.cycle_blocks;
  query_invalid =
      snapshot.tracking && bounds_query_invalid_since(b, snapshot.transport);
  if (oom)
    *oom = state->oom || b->oom;
  if (limited)
    *limited = state->limited || query_limited;
  defined_state_destroy(state);
  return state->oom || state->limited || state->invalid || query_limited ||
         query_cycle || query_invalid || b->oom;
}

IXS_STATIC ixs_check_result bounds_defined_check_detail(ixs_bounds *b,
                                                        ixs_node *expr,
                                                        bool *oom,
                                                        bool *limited) {
  defined_state state;
  bounds_defined_query_snapshot snapshot = bounds_defined_query_observe(b);
  ixs_check_result result;
  if (oom)
    *oom = false;
  if (limited)
    *limited = false;
  if (!b || !b->ctx || !b->scratch || !expr || b->oom ||
      ixs_bounds_has_empty(b))
    return IXS_CHECK_UNKNOWN;
  if (ixs_ctx_owns_node(b->ctx, expr) && ixs_node_is_known_total(expr))
    return IXS_CHECK_TRUE;
  if (bounds_defined_cache_lookup(b, expr, &result))
    return result;
  defined_state_init(&state, b->ctx, b);
  result = defined_eval(&state, b, expr, 0);
  if (bounds_defined_query_failed(b, &state, result, snapshot, oom, limited))
    return IXS_CHECK_UNKNOWN;
  if (!bounds_defined_cache_publish(b, expr, result)) {
    if (oom)
      *oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  return result;
}

IXS_STATIC ixs_check_result ixs_bounds_check_defined(ixs_bounds *b,
                                                     ixs_node *expr) {
  return bounds_defined_check_detail(b, expr, NULL, NULL);
}

IXS_STATIC ixs_algebra_status ixs_bounds_check_integer_domain(ixs_bounds *b,
                                                              ixs_node *expr) {
  ixs_check_result check;
  ixs_bounds_transport_snapshot snapshot =
      ixs_bounds_query_transport_snapshot(b);
  ixs_bounds_transport_status transport;
  bool oom = false, limited = false;
  check = bounds_defined_check_detail(b, expr, &oom, &limited);
  if (check == IXS_CHECK_TRUE)
    check = ixs_bounds_check_integer_valued(b, expr);
  transport = ixs_bounds_query_transport_since(b, snapshot);
  if (transport == IXS_BOUNDS_TRANSPORT_INVALID)
    return IXS_ALGEBRA_INVALID;
  if (oom || transport == IXS_BOUNDS_TRANSPORT_OOM)
    return IXS_ALGEBRA_OOM;
  if (limited || transport == IXS_BOUNDS_TRANSPORT_LIMITED)
    return IXS_ALGEBRA_LIMITED;
  return check == IXS_CHECK_TRUE ? IXS_ALGEBRA_MATCH : IXS_ALGEBRA_NO_MATCH;
}
