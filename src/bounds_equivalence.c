/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds_equivalence.h"
#include "additive_row.h"
#include "bounds_defined.h"
#include "bounds_modular.h"
#include "bounds_predicate.h"
#include "bounds_query.h"
#include "bounds_range.h"
#include "bounds_store.h"
#include "division_algebra.h"
#include "expand.h"
#include "facts_store.h"
#include "low_bits_algebra.h"
#include "query_transaction.h"
#include "query_walk.h"
#include "quotient_algebra.h"
#include "simplify.h"
#include <assert.h>
#include <limits.h>
#include <string.h>

typedef struct {
  ixs_node *lhs;
  ixs_node *rhs;
  ixs_check_result result;
  bool active;
  bool complete;
} equivalence_memo_entry;

typedef struct {
  ixs_node *source;
  ixs_node *result;
} equivalence_simplify_entry;

typedef struct {
  ixs_ctx *ctx;
  ixs_bounds *bounds;
  ixs_arena_mark memo_mark;
  equivalence_memo_entry *memo;
  size_t memo_count;
  size_t memo_capacity;
  equivalence_simplify_entry *simplify_cache;
  size_t simplify_cache_count;
  size_t simplify_cache_capacity;
  size_t visited;
  size_t memo_cycles;
  unsigned bounded_subproof_depth;
  bool limited;
  bool invalid;
  bool oom;
  bool arithmetic_unrepresentable;
  bool roots_simplified;
} equivalence_state;

static ixs_check_result
equivalence_quotient_remainder_algebra(equivalence_state *state, ixs_node *lhs,
                                       ixs_node *rhs);

/* Algebraic bridge
 * rules may nest
 * only through this
 * fixed allowance.
 */
#define EQUIVALENCE_BOUNDED_SUBPROOF_DEPTH 4u
/* The Piecewise
 * fallback
 * represents one
 * complete selector
 * domain in a mask.
 */
#define EQUIVALENCE_PIECEWISE_MAX_CASES 16u
#define EQUIVALENCE_PIECEWISE_MAX_POINTS 64u

static size_t equivalence_pair_hash(ixs_node *lhs, ixs_node *rhs) {
  uintptr_t left = (uintptr_t)lhs;
  uintptr_t right = (uintptr_t)rhs;
  left >>= 3u;
  right >>= 3u;
  return (size_t)(left ^ (right + (left << 6u) + (left >> 2u)));
}

static bool equivalence_memo_grow(equivalence_state *state) {
  size_t next_capacity = state->memo_capacity ? state->memo_capacity * 2u : 32u;
  equivalence_memo_entry *grown;
  size_t i;
  if (next_capacity <= state->memo_capacity ||
      next_capacity > SIZE_MAX / sizeof(*grown))
    return false;
  grown = ixs_arena_alloc(&state->bounds->query_arena,
                          next_capacity * sizeof(*grown), sizeof(void *));
  if (!grown)
    return false;
  memset(grown, 0, next_capacity * sizeof(*grown));
  for (i = 0; i < state->memo_capacity; i++) {
    equivalence_memo_entry entry = state->memo[i];
    size_t index;
    if (!entry.lhs)
      continue;
    index = equivalence_pair_hash(entry.lhs, entry.rhs) & (next_capacity - 1u);
    while (grown[index].lhs)
      index = (index + 1u) & (next_capacity - 1u);
    grown[index] = entry;
  }
  state->memo = grown;
  state->memo_capacity = next_capacity;
  return true;
}

static equivalence_memo_entry *equivalence_memo_get(equivalence_state *state,
                                                    ixs_node *lhs,
                                                    ixs_node *rhs,
                                                    bool create) {
  size_t index;
  if (create && (!state->memo_capacity ||
                 state->memo_count + 1u > state->memo_capacity / 2u)) {
    if (!equivalence_memo_grow(state))
      return NULL;
  }
  if (!state->memo_capacity)
    return NULL;
  index = equivalence_pair_hash(lhs, rhs) & (state->memo_capacity - 1u);
  while (state->memo[index].lhs &&
         (state->memo[index].lhs != lhs || state->memo[index].rhs != rhs))
    index = (index + 1u) & (state->memo_capacity - 1u);
  if (!state->memo[index].lhs) {
    if (!create)
      return NULL;
    state->memo[index].lhs = lhs;
    state->memo[index].rhs = rhs;
    state->memo[index].result = IXS_CHECK_UNKNOWN;
    state->memo_count++;
  }
  return &state->memo[index];
}

static bool equivalence_simplify_cache_grow(equivalence_state *state) {
  size_t capacity = state->simplify_cache_capacity
                        ? state->simplify_cache_capacity * 2u
                        : 32u;
  equivalence_simplify_entry *grown;
  size_t i;

  if (capacity <= state->simplify_cache_capacity ||
      capacity > SIZE_MAX / sizeof(*grown))
    return false;
  grown = ixs_arena_alloc(&state->bounds->query_arena,
                          capacity * sizeof(*grown), sizeof(void *));
  if (!grown)
    return false;
  memset(grown, 0, capacity * sizeof(*grown));
  for (i = 0; i < state->simplify_cache_capacity; i++) {
    equivalence_simplify_entry entry = state->simplify_cache[i];
    size_t slot;
    if (!entry.source)
      continue;
    slot = entry.source->hash & (capacity - 1u);
    while (grown[slot].source)
      slot = (slot + 1u) & (capacity - 1u);
    grown[slot] = entry;
  }
  state->simplify_cache = grown;
  state->simplify_cache_capacity = capacity;
  return true;
}

static ixs_node *equivalence_simplify(equivalence_state *state,
                                      ixs_node *source, bool *limited) {
  size_t slot;
  ixs_node *result;

  if (state->simplify_cache_capacity) {
    slot = source->hash & (state->simplify_cache_capacity - 1u);
    while (state->simplify_cache[slot].source &&
           state->simplify_cache[slot].source != source)
      slot = (slot + 1u) & (state->simplify_cache_capacity - 1u);
    if (state->simplify_cache[slot].source)
      return state->simplify_cache[slot].result;
  }
  if (!state->simplify_cache_capacity ||
      state->simplify_cache_count + 1u > state->simplify_cache_capacity / 2u) {
    if (!equivalence_simplify_cache_grow(state)) {
      state->oom = true;
      return NULL;
    }
  }
  slot = source->hash & (state->simplify_cache_capacity - 1u);
  while (state->simplify_cache[slot].source &&
         state->simplify_cache[slot].source != source)
    slot = (slot + 1u) & (state->simplify_cache_capacity - 1u);
  result =
      simp_simplify_bounds_status(state->ctx, source, state->bounds, limited);
  if (!result || *limited)
    return result;
  state->simplify_cache[slot].source = source;
  state->simplify_cache[slot].result = result;
  state->simplify_cache_count++;
  return result;
}

static void equivalence_state_init(equivalence_state *state, ixs_ctx *ctx,
                                   ixs_bounds *bounds) {
  memset(state, 0, sizeof(*state));
  state->ctx = ctx;
  state->bounds = bounds;
  state->memo_mark = ixs_arena_save(&bounds->query_arena);
}

static void equivalence_state_destroy(equivalence_state *state) {
  ixs_arena_restore(&state->bounds->query_arena, state->memo_mark);
}

static ixs_check_result equivalence_core(equivalence_state *state,
                                         ixs_node *lhs, ixs_node *rhs,
                                         unsigned depth);
static ixs_check_result equivalence_core_impl(equivalence_state *state,
                                              ixs_node *lhs, ixs_node *rhs,
                                              unsigned depth,
                                              bool allow_context);
static ixs_check_result equivalence_bounded_core(equivalence_state *state,
                                                 ixs_node *lhs, ixs_node *rhs,
                                                 unsigned depth) {
  ixs_bounds_transport_snapshot transport;
  size_t memo_cycles;
  ixs_check_result result;
  if (state->bounded_subproof_depth >= EQUIVALENCE_BOUNDED_SUBPROOF_DEPTH)
    return IXS_CHECK_UNKNOWN;
  if (facts_equivalence_cache_lookup(state->ctx, state->bounds, lhs, rhs,
                                     &result))
    return result;
  transport = ixs_bounds_query_transport_snapshot(state->bounds);
  memo_cycles = state->memo_cycles;
  state->bounded_subproof_depth++;
  result = equivalence_core(state, lhs, rhs, depth);
  state->bounded_subproof_depth--;
  if (result != IXS_CHECK_UNKNOWN && !state->limited && !state->invalid &&
      !state->oom && !state->arithmetic_unrepresentable &&
      state->memo_cycles == memo_cycles &&
      !bounds_query_limited_since(state->bounds, transport) &&
      !bounds_query_invalid_since(state->bounds, transport))
    facts_equivalence_cache_store(state->ctx, state->bounds, lhs, rhs, result);
  return result;
}

static bool equivalence_context_shape(ixs_node *lhs, ixs_node *rhs,
                                      uint32_t *child_count) {
  uint32_t lhs_children;
  uint32_t rhs_children;
  uint32_t i;

  if (lhs->tag != rhs->tag || !defined_child_count(lhs, &lhs_children) ||
      !defined_child_count(rhs, &rhs_children) || lhs_children == 0u ||
      lhs_children != rhs_children)
    return false;
  /* Piecewise is lazy: root definedness does not make every corresponding
   * arm and later condition available to an eager child proof. */
  if (lhs->tag == IXS_PIECEWISE)
    return false;
  if (lhs->tag == IXS_MUL) {
    if (lhs->u.mul.nfactors != rhs->u.mul.nfactors)
      return false;
    for (i = 0; i < lhs->u.mul.nfactors; i++)
      if (lhs->u.mul.factors[i].exp != rhs->u.mul.factors[i].exp)
        return false;
  }
  if (lhs->tag == IXS_CMP && lhs->u.binary.cmp_op != rhs->u.binary.cmp_op)
    return false;
  *child_count = lhs_children;
  return true;
}

typedef struct {
  ixs_node *lhs;
  ixs_node *rhs;
} equivalence_context_pair;

typedef struct {
  equivalence_context_pair *pairs;
  size_t count;
  size_t capacity;
  equivalence_context_pair *seen;
  size_t seen_count;
  size_t seen_capacity;
} equivalence_context_worklist;

static bool
equivalence_context_seen_grow(equivalence_state *state,
                              equivalence_context_worklist *worklist) {
  size_t capacity =
      worklist->seen_capacity ? worklist->seen_capacity * 2u : 32u;
  equivalence_context_pair *grown;
  size_t i;

  if (capacity <= worklist->seen_capacity ||
      capacity > SIZE_MAX / sizeof(*grown))
    goto oom;
  grown = ixs_arena_alloc(&state->bounds->query_arena,
                          capacity * sizeof(*grown), sizeof(void *));
  if (!grown)
    goto oom;
  memset(grown, 0, capacity * sizeof(*grown));
  for (i = 0; i < worklist->seen_capacity; i++) {
    equivalence_context_pair pair = worklist->seen[i];
    size_t slot;
    if (!pair.lhs)
      continue;
    slot = equivalence_pair_hash(pair.lhs, pair.rhs) & (capacity - 1u);
    while (grown[slot].lhs)
      slot = (slot + 1u) & (capacity - 1u);
    grown[slot] = pair;
  }
  worklist->seen = grown;
  worklist->seen_capacity = capacity;
  return true;

oom:
  state->oom = true;
  return false;
}

static bool equivalence_context_enqueue(equivalence_state *state,
                                        equivalence_context_worklist *worklist,
                                        ixs_node *lhs, ixs_node *rhs) {
  size_t slot;

  if (!lhs || !rhs) {
    state->invalid = true;
    return false;
  }
  if ((uintptr_t)lhs > (uintptr_t)rhs) {
    ixs_node *tmp = lhs;
    lhs = rhs;
    rhs = tmp;
  }
  if (!worklist->seen_capacity ||
      worklist->seen_count + 1u > worklist->seen_capacity / 2u)
    if (!equivalence_context_seen_grow(state, worklist))
      return false;
  slot = equivalence_pair_hash(lhs, rhs) & (worklist->seen_capacity - 1u);
  while (worklist->seen[slot].lhs &&
         (worklist->seen[slot].lhs != lhs || worklist->seen[slot].rhs != rhs))
    slot = (slot + 1u) & (worklist->seen_capacity - 1u);
  if (worklist->seen[slot].lhs)
    return true;
  worklist->seen[slot].lhs = lhs;
  worklist->seen[slot].rhs = rhs;
  worklist->seen_count++;

  if (worklist->count == worklist->capacity) {
    size_t capacity = worklist->capacity ? worklist->capacity * 2u : 32u;
    equivalence_context_pair *grown;
    if (capacity <= worklist->capacity ||
        capacity > SIZE_MAX / sizeof(*grown)) {
      state->oom = true;
      return false;
    }
    grown = ixs_arena_grow(&state->bounds->query_arena, worklist->pairs,
                           worklist->capacity * sizeof(*grown),
                           capacity * sizeof(*grown), sizeof(void *));
    if (!grown) {
      state->oom = true;
      return false;
    }
    worklist->pairs = grown;
    worklist->capacity = capacity;
  }
  worklist->pairs[worklist->count].lhs = lhs;
  worklist->pairs[worklist->count].rhs = rhs;
  worklist->count++;
  return true;
}

static uint32_t equivalence_add_relation_size(ixs_node *node) {
  if (ixs_node_is_zero(node))
    return 0u;
  return node->tag == IXS_ADD ? node->u.add.nterms : 1u;
}

static bool equivalence_cancel_common_add(equivalence_state *state,
                                          ixs_node *lhs, ixs_node *rhs,
                                          ixs_node **lhs_residual,
                                          ixs_node **rhs_residual) {
  struct ixs_node_impl equality;
  ixs_node *relation_lhs;
  ixs_node *relation_rhs;
  int64_t offset;
  uint64_t original_size;
  uint64_t residual_size;

  if (lhs->tag != IXS_ADD || rhs->tag != IXS_ADD ||
      lhs->u.add.nterms == rhs->u.add.nterms)
    return false;
  memset(&equality, 0, sizeof(equality));
  equality.tag = IXS_CMP;
  equality.u.binary.lhs = lhs;
  equality.u.binary.rhs = rhs;
  equality.u.binary.cmp_op = IXS_CMP_EQ;
  if (!bounds_extract_cmp_exact_relation(
          state->bounds, &equality, &relation_lhs, &relation_rhs, &offset)) {
    if (state->bounds->oom)
      state->oom = true;
    return false;
  }
  if (offset != 0) {
    ixs_node *constant = ixs_node_int(state->ctx, offset);
    bool unrepresentable = false;
    if (!constant) {
      state->oom = true;
      return false;
    }
    relation_rhs =
        simp_try_add(state->ctx, relation_rhs, constant, &unrepresentable);
    if (unrepresentable)
      return false;
    if (!relation_rhs) {
      state->oom = true;
      return false;
    }
    if (ixs_node_is_sentinel(relation_rhs))
      return false;
  }
  original_size = (uint64_t)lhs->u.add.nterms + (uint64_t)rhs->u.add.nterms;
  residual_size = (uint64_t)equivalence_add_relation_size(relation_lhs) +
                  (uint64_t)equivalence_add_relation_size(relation_rhs);
  if (residual_size >= original_size ||
      ixs_bounds_check_defined(state->bounds, relation_lhs) != IXS_CHECK_TRUE ||
      ixs_bounds_check_defined(state->bounds, relation_rhs) != IXS_CHECK_TRUE) {
    if (state->bounds->oom)
      state->oom = true;
    return false;
  }
  *lhs_residual = relation_lhs;
  *rhs_residual = relation_rhs;
  return true;
}

static bool equivalence_is_commutative_associative(ixs_tag tag) {
  return tag == IXS_MAX || tag == IXS_MIN || tag == IXS_XOR || tag == IXS_AND ||
         tag == IXS_OR;
}

/* Exact children are committed first. Remaining children use deterministic
 * left-to-right one-to-one matching. The work is O(A^2), and every semantic
 * candidate uses the fixed bounded-subproof allowance. */
static ixs_check_result
equivalence_match_associative_context(equivalence_state *state, ixs_node *lhs,
                                      ixs_node *rhs, unsigned depth) {
  ixs_arena_mark mark = ixs_arena_save(&state->ctx->scratch);
  size_t nargs = lhs->u.assoc.nargs;
  unsigned char *left_matched;
  unsigned char *right_matched;
  size_t i;
  size_t j;
  ixs_check_result result = IXS_CHECK_UNKNOWN;

  left_matched = ixs_arena_alloc(&state->ctx->scratch, nargs, 1);
  right_matched = ixs_arena_alloc(&state->ctx->scratch, nargs, 1);
  if ((!left_matched || !right_matched) && nargs != 0u) {
    state->oom = true;
    goto cleanup;
  }
  memset(left_matched, 0, nargs);
  memset(right_matched, 0, nargs);
  for (i = 0; i < nargs; i++) {
    for (j = 0; j < nargs; j++) {
      if (!right_matched[j] && lhs->u.assoc.args[i] == rhs->u.assoc.args[j]) {
        left_matched[i] = 1;
        right_matched[j] = 1;
        break;
      }
    }
  }
  for (i = 0; i < nargs; i++) {
    if (left_matched[i])
      continue;
    for (j = 0; j < nargs; j++) {
      if (!right_matched[j] &&
          equivalence_bounded_core(state, lhs->u.assoc.args[i],
                                   rhs->u.assoc.args[j],
                                   depth) == IXS_CHECK_TRUE) {
        left_matched[i] = 1;
        right_matched[j] = 1;
        break;
      }
      if (state->limited || state->invalid || state->oom ||
          state->arithmetic_unrepresentable)
        goto cleanup;
    }
    if (!left_matched[i])
      goto cleanup;
  }
  result = IXS_CHECK_TRUE;

cleanup:
  ixs_arena_restore(&state->ctx->scratch, mark);
  return result;
}

static bool
equivalence_context_simplify_pair(equivalence_state *state,
                                  const equivalence_context_pair *pair,
                                  ixs_node **lhs, ixs_node **rhs) {
  bool lhs_limited = false;
  bool rhs_limited = false;

  *lhs = equivalence_simplify(state, pair->lhs, &lhs_limited);
  *rhs = equivalence_simplify(state, pair->rhs, &rhs_limited);
  if (lhs_limited || rhs_limited) {
    state->limited = true;
    return false;
  }
  if (!*lhs || !*rhs) {
    state->oom = true;
    return false;
  }
  if (ixs_node_is_sentinel(*lhs) || ixs_node_is_sentinel(*rhs)) {
    state->invalid = true;
    return false;
  }
  return true;
}

static bool
equivalence_context_enqueue_children(equivalence_state *state,
                                     equivalence_context_worklist *worklist,
                                     ixs_node *lhs, ixs_node *rhs) {
  uint32_t child_count;
  uint32_t i;

  if (!equivalence_context_shape(lhs, rhs, &child_count))
    return false;
  for (i = 0; i < child_count; i++)
    if (!equivalence_context_enqueue(state, worklist, defined_child_at(lhs, i),
                                     defined_child_at(rhs, i)))
      return false;
  return true;
}

static bool equivalence_context_process_pair(
    equivalence_state *state, equivalence_context_worklist *worklist,
    const equivalence_context_pair *pair, unsigned depth) {
  ixs_node *simplified_lhs;
  ixs_node *simplified_rhs;
  ixs_node *lhs_residual;
  ixs_node *rhs_residual;
  ixs_check_result result;

  if (!equivalence_context_simplify_pair(state, pair, &simplified_lhs,
                                         &simplified_rhs))
    return false;
  if (simplified_lhs == simplified_rhs)
    return true;

  result = equivalence_core_impl(state, simplified_lhs, simplified_rhs, depth,
                                 false);
  if (result == IXS_CHECK_TRUE)
    return true;
  if (state->limited || state->invalid || state->oom ||
      state->arithmetic_unrepresentable)
    return false;
  if (simplified_lhs->tag == simplified_rhs->tag &&
      equivalence_is_commutative_associative(simplified_lhs->tag) &&
      simplified_lhs->u.assoc.nargs == simplified_rhs->u.assoc.nargs)
    return equivalence_match_associative_context(
               state, simplified_lhs, simplified_rhs, depth) == IXS_CHECK_TRUE;

  if (equivalence_cancel_common_add(state, simplified_lhs, simplified_rhs,
                                    &lhs_residual, &rhs_residual))
    return equivalence_context_enqueue(state, worklist, lhs_residual,
                                       rhs_residual);
  if (state->oom)
    return false;
  return equivalence_context_enqueue_children(state, worklist, simplified_lhs,
                                              simplified_rhs);
}

/* Worklist insertion and lookup are expected O(N) in the paired canonical DAG.
 * Associative contexts may add O(A^2) bounded child proofs after exact
 * argument pairing. */
static ixs_check_result equivalence_same_context(equivalence_state *state,
                                                 ixs_node *lhs, ixs_node *rhs,
                                                 unsigned depth) {
  equivalence_context_worklist worklist;
  uint32_t child_count;

  memset(&worklist, 0, sizeof(worklist));
  if (!equivalence_context_shape(lhs, rhs, &child_count) ||
      !equivalence_context_enqueue(state, &worklist, lhs, rhs))
    return IXS_CHECK_UNKNOWN;

  while (worklist.count > 0u) {
    equivalence_context_pair pair = worklist.pairs[--worklist.count];
    if (!equivalence_context_process_pair(state, &worklist, &pair, depth))
      return IXS_CHECK_UNKNOWN;
  }
  return IXS_CHECK_TRUE;
}

/* Optional algebraic proofs must not diagnose a valid query merely because an
 * intermediate rational is unrepresentable. Build their small linear forms
 * directly from canonical nodes: overflow is a rule miss; allocation failure
 * remains OOM. */
typedef enum {
  EQUIVALENCE_BUILD_OK,
  EQUIVALENCE_BUILD_NO_MATCH,
  EQUIVALENCE_BUILD_OOM
} equivalence_build_status;

static ixs_node *equivalence_build_const(ixs_ctx *ctx, int64_t p, int64_t q) {
  return q == 1 ? ixs_node_int(ctx, p) : ixs_node_rat(ctx, p, q);
}

static equivalence_build_status
equivalence_build_scale_rat(equivalence_state *state, ixs_node *expr,
                            int64_t scale_p, int64_t scale_q,
                            ixs_node **result) {
  ixs_node *coefficient;
  bool unrepresentable = false;

  *result = NULL;
  if (!expr || ixs_node_is_sentinel(expr) || scale_q <= 0)
    return EQUIVALENCE_BUILD_NO_MATCH;
  coefficient = equivalence_build_const(state->ctx, scale_p, scale_q);
  if (!coefficient) {
    state->oom = true;
    return EQUIVALENCE_BUILD_OOM;
  }
  *result = simp_try_mul(state->ctx, coefficient, expr, &unrepresentable);
  if (unrepresentable) {
    state->arithmetic_unrepresentable = true;
    return EQUIVALENCE_BUILD_NO_MATCH;
  }
  if (!*result) {
    state->oom = true;
    return EQUIVALENCE_BUILD_OOM;
  }
  return EQUIVALENCE_BUILD_OK;
}

static equivalence_build_status equivalence_build_add(equivalence_state *state,
                                                      ixs_node *lhs,
                                                      ixs_node *rhs,
                                                      ixs_node **result) {
  bool unrepresentable = false;
  *result = simp_try_add(state->ctx, lhs, rhs, &unrepresentable);
  if (unrepresentable) {
    state->arithmetic_unrepresentable = true;
    return EQUIVALENCE_BUILD_NO_MATCH;
  }
  if (!*result) {
    state->oom = true;
    return EQUIVALENCE_BUILD_OOM;
  }
  return EQUIVALENCE_BUILD_OK;
}

static equivalence_build_status equivalence_build_neg(equivalence_state *state,
                                                      ixs_node *expr,
                                                      ixs_node **result) {
  equivalence_build_status status =
      equivalence_build_scale_rat(state, expr, -1, 1, result);
  if (status == EQUIVALENCE_BUILD_OOM)
    state->oom = true;
  return status;
}

static equivalence_build_status equivalence_build_sub(equivalence_state *state,
                                                      ixs_node *lhs,
                                                      ixs_node *rhs,
                                                      ixs_node **result) {
  ixs_node *negative;
  equivalence_build_status status =
      equivalence_build_neg(state, rhs, &negative);
  if (status != EQUIVALENCE_BUILD_OK)
    return status;
  return equivalence_build_add(state, lhs, negative, result);
}

static bool equivalence_partition_zero_sum(equivalence_state *state,
                                           ixs_node *lhs, ixs_node *rhs,
                                           ixs_node **positive,
                                           ixs_node **negative) {
  struct ixs_node_impl equality;
  int64_t offset;

  if ((!ixs_node_is_zero(lhs) && !ixs_node_is_zero(rhs)) ||
      (lhs->tag != IXS_ADD && rhs->tag != IXS_ADD))
    return false;
  memset(&equality, 0, sizeof(equality));
  equality.tag = IXS_CMP;
  equality.u.binary.lhs = lhs;
  equality.u.binary.rhs = rhs;
  equality.u.binary.cmp_op = IXS_CMP_EQ;
  if (!bounds_extract_cmp_exact_relation(state->bounds, &equality, positive,
                                         negative, &offset)) {
    if (state->bounds->oom)
      state->oom = true;
    return false;
  }
  if (offset != 0) {
    ixs_node *constant = ixs_node_int(state->ctx, offset);
    if (!constant || equivalence_build_add(state, *negative, constant,
                                           negative) != EQUIVALENCE_BUILD_OK) {
      if (!constant)
        state->oom = true;
      return false;
    }
  }
  return true;
}

static bool equivalence_add_coeff_equal(ixs_node *lhs, ixs_node *rhs) {
  int64_t lhs_p;
  int64_t lhs_q;
  int64_t rhs_p;
  int64_t rhs_q;

  ixs_node_get_rat(lhs, &lhs_p, &lhs_q);
  ixs_node_get_rat(rhs, &rhs_p, &rhs_q);
  return lhs_p == rhs_p && lhs_q == rhs_q;
}

static bool equivalence_build_add_residual(equivalence_state *state,
                                           ixs_node *add,
                                           const unsigned char *matched,
                                           ixs_node **residual) {
  uint32_t i;

  *residual = add->u.add.coeff;
  for (i = 0; i < add->u.add.nterms; i++) {
    ixs_node *scaled;
    int64_t p;
    int64_t q;
    if (matched[i])
      continue;
    ixs_node_get_rat(add->u.add.terms[i].coeff, &p, &q);
    if (equivalence_build_scale_rat(state, add->u.add.terms[i].term, p, q,
                                    &scaled) != EQUIVALENCE_BUILD_OK ||
        equivalence_build_add(state, *residual, scaled, residual) !=
            EQUIVALENCE_BUILD_OK)
      return false;
  }
  return true;
}

static bool equivalence_match_semantic_add_terms(equivalence_state *state,
                                                 ixs_node *lhs, ixs_node *rhs,
                                                 unsigned char *lhs_matched,
                                                 unsigned char *rhs_matched,
                                                 uint32_t *matched_count,
                                                 unsigned depth) {
  uint32_t i;
  uint32_t j;

  for (i = 0; i < lhs->u.add.nterms; i++) {
    if (lhs_matched[i])
      continue;
    for (j = 0; j < rhs->u.add.nterms; j++) {
      if (rhs_matched[j] ||
          !equivalence_add_coeff_equal(lhs->u.add.terms[i].coeff,
                                       rhs->u.add.terms[j].coeff))
        continue;
      if (equivalence_bounded_core(state, lhs->u.add.terms[i].term,
                                   rhs->u.add.terms[j].term,
                                   depth + 1u) == IXS_CHECK_TRUE) {
        lhs_matched[i] = 1;
        rhs_matched[j] = 1;
        (*matched_count)++;
        break;
      }
      if (state->limited || state->invalid || state->oom ||
          state->arithmetic_unrepresentable)
        return false;
    }
  }
  return true;
}

/* Equal-scale terms may cancel after their values are proved equivalent. The
 * two canonical sums are query-local, so deterministic matching is O(L*R).
 * Each semantic candidate uses the fixed bounded-subproof allowance. */
static ixs_check_result
equivalence_cancel_proven_add_terms(equivalence_state *state, ixs_node *lhs,
                                    ixs_node *rhs, unsigned depth,
                                    bool match_semantic) {
  ixs_arena_mark mark;
  unsigned char *lhs_matched;
  unsigned char *rhs_matched;
  ixs_node *lhs_residual;
  ixs_node *rhs_residual;
  uint32_t matched_count = 0u;
  uint32_t i;
  uint32_t j;
  ixs_check_result result = IXS_CHECK_UNKNOWN;

  if (lhs->tag != IXS_ADD || rhs->tag != IXS_ADD)
    return IXS_CHECK_UNKNOWN;
  mark = ixs_arena_save(&state->ctx->scratch);
  lhs_matched = ixs_arena_alloc(&state->ctx->scratch, lhs->u.add.nterms, 1);
  rhs_matched = ixs_arena_alloc(&state->ctx->scratch, rhs->u.add.nterms, 1);
  if ((!lhs_matched && lhs->u.add.nterms != 0u) ||
      (!rhs_matched && rhs->u.add.nterms != 0u)) {
    state->oom = true;
    goto cleanup;
  }
  memset(lhs_matched, 0, lhs->u.add.nterms);
  memset(rhs_matched, 0, rhs->u.add.nterms);
  for (i = 0; i < lhs->u.add.nterms; i++) {
    for (j = 0; j < rhs->u.add.nterms; j++) {
      if (!rhs_matched[j] &&
          equivalence_add_coeff_equal(lhs->u.add.terms[i].coeff,
                                      rhs->u.add.terms[j].coeff) &&
          lhs->u.add.terms[i].term == rhs->u.add.terms[j].term) {
        lhs_matched[i] = 1;
        rhs_matched[j] = 1;
        matched_count++;
        break;
      }
    }
  }
  if (match_semantic &&
      !equivalence_match_semantic_add_terms(state, lhs, rhs, lhs_matched,
                                            rhs_matched, &matched_count, depth))
    goto cleanup;
  if (matched_count == 0u ||
      !equivalence_build_add_residual(state, lhs, lhs_matched, &lhs_residual) ||
      !equivalence_build_add_residual(state, rhs, rhs_matched, &rhs_residual))
    goto cleanup;
  result =
      equivalence_bounded_core(state, lhs_residual, rhs_residual, depth + 1u);
  if (!match_semantic && result != IXS_CHECK_TRUE)
    result = IXS_CHECK_UNKNOWN;

cleanup:
  ixs_arena_restore(&state->ctx->scratch, mark);
  return result;
}

static ixs_check_result equivalence_zero_sum(equivalence_state *state,
                                             ixs_node *lhs, ixs_node *rhs,
                                             unsigned depth) {
  ixs_node *positive;
  ixs_node *negative;

  if (!equivalence_partition_zero_sum(state, lhs, rhs, &positive, &negative))
    return IXS_CHECK_UNKNOWN;
  return equivalence_bounded_core(state, positive, negative, depth + 1u);
}

static ixs_check_result equivalence_difference(equivalence_state *state,
                                               ixs_node *lhs, ixs_node *rhs) {
  struct ixs_node_impl nonzero;
  ixs_node *difference;
  ixs_check_result nonzero_result;
  int64_t delta;
  bool proved;
  if (equivalence_build_sub(state, lhs, rhs, &difference) !=
      EQUIVALENCE_BUILD_OK)
    return IXS_CHECK_UNKNOWN;
  proved = bounds_modular_exact_delta_detail(
      state->ctx, state->bounds, lhs, rhs, false, &delta, NULL, NULL, NULL);
  if (state->bounds->oom) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (proved)
    return delta == 0 ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;

  /* A variable difference need not be constant to prove that two expressions
   * never agree. Query the canonical difference through the ordinary range,
   * bit, and congruence domains instead of duplicating them here. */
  if (ixs_node_is_sentinel(difference))
    return IXS_CHECK_UNKNOWN;
  memset(&nonzero, 0, sizeof(nonzero));
  nonzero.tag = IXS_CMP;
  nonzero.u.binary.lhs = difference;
  nonzero.u.binary.rhs = state->ctx->node_zero;
  nonzero.u.binary.cmp_op = IXS_CMP_NE;
  nonzero_result = ixs_bounds_check(state->bounds, &nonzero);
  if (state->bounds->oom) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (nonzero_result == IXS_CHECK_TRUE)
    return IXS_CHECK_FALSE;

  /* Integer equality is also bitwise equality. Canonical XOR cancels shared
   * subexpressions that an arithmetic difference deliberately preserves. */
  if (ixs_bounds_check_integer_valued(state->bounds, lhs) == IXS_CHECK_TRUE &&
      ixs_bounds_check_integer_valued(state->bounds, rhs) == IXS_CHECK_TRUE) {
    ixs_node *bit_difference = simp_xor(state->ctx, lhs, rhs);
    if (!bit_difference) {
      state->oom = true;
      return IXS_CHECK_UNKNOWN;
    }
    if (!ixs_node_is_sentinel(bit_difference)) {
      if (ixs_node_is_zero(bit_difference))
        return IXS_CHECK_TRUE;
      nonzero.u.binary.lhs = bit_difference;
      nonzero_result = ixs_bounds_check(state->bounds, &nonzero);
      if (state->bounds->oom) {
        state->oom = true;
        return IXS_CHECK_UNKNOWN;
      }
      if (nonzero_result == IXS_CHECK_TRUE)
        return IXS_CHECK_FALSE;
    }
  }
  return IXS_CHECK_UNKNOWN;
}

static bool equivalence_integer_delta(equivalence_state *state, ixs_node *lhs,
                                      ixs_node *rhs, int64_t *delta) {
  bool proved = bounds_modular_exact_delta_detail(
      state->ctx, state->bounds, lhs, rhs, true, delta, NULL, NULL, NULL);
  if (state->bounds->oom)
    state->oom = true;
  return proved && !state->oom;
}

static bool equivalence_no_reachable_integer(equivalence_state *state,
                                             ixs_node *expr, int64_t lo,
                                             int64_t hi) {
  ixs_interval region;
  ixs_interval known;
  uint64_t stride;
  uint64_t residue;
  if (lo > hi)
    return true;
  region = ixs_interval_range(lo, 1, hi, 1);
  known = ixs_bounds_get(state->bounds, expr);
  if (state->bounds->oom) {
    state->oom = true;
    return false;
  }
  if (known.valid) {
    region = iv_intersect(region, known);
    if (!region.valid)
      return true;
  }
  if (!bounds_known_stride(state->bounds, expr, &stride) || stride <= 1u ||
      stride > (uint64_t)INT64_MAX ||
      !bounds_known_residue(state->bounds, expr, stride, &residue)) {
    if (state->bounds->oom)
      state->oom = true;
    return false;
  }
  return !ixs_interval_has_congruent_integer(&region, (int64_t)stride,
                                             (int64_t)residue);
}

static bool equivalence_ordered_cut(ixs_cmp_op op, bool *lower,
                                    int64_t *threshold) {
  switch (op) {
  case IXS_CMP_LT:
    *lower = false;
    *threshold = -1;
    return true;
  case IXS_CMP_LE:
    *lower = false;
    *threshold = 0;
    return true;
  case IXS_CMP_GT:
    *lower = true;
    *threshold = 1;
    return true;
  case IXS_CMP_GE:
    *lower = true;
    *threshold = 0;
    return true;
  default:
    return false;
  }
}

typedef struct {
  int64_t *slots;
  size_t capacity;
  size_t count;
} equivalence_modulus_set;

static size_t equivalence_modulus_hash(int64_t modulus) {
  uint64_t x = (uint64_t)modulus;
  x ^= x >> 33;
  x *= UINT64_C(0xff51afd7ed558ccd);
  x ^= x >> 33;
  return (size_t)x;
}

/* Rehashing is
 * amortized O(1),
 * and storage grows
 * only with distinct
 * moduli in the two
 * queried expression
 * DAGs. */
static bool equivalence_modulus_set_grow(ixs_arena *arena,
                                         equivalence_modulus_set *set) {
  size_t new_capacity = set->capacity ? set->capacity * 2u : 8u;
  int64_t *slots;
  size_t i;
  if (new_capacity <= set->capacity || new_capacity > SIZE_MAX / sizeof(*slots))
    return false;
  slots = ixs_arena_alloc(arena, new_capacity * sizeof(*slots), sizeof(void *));
  if (!slots)
    return false;
  memset(slots, 0, new_capacity * sizeof(*slots));
  for (i = 0; i < set->capacity; i++) {
    if (set->slots[i] != 0) {
      size_t index =
          equivalence_modulus_hash(set->slots[i]) & (new_capacity - 1u);
      while (slots[index] != 0)
        index = (index + 1u) & (new_capacity - 1u);
      slots[index] = set->slots[i];
    }
  }
  set->slots = slots;
  set->capacity = new_capacity;
  return true;
}

static bool equivalence_modulus_set_insert(ixs_arena *arena,
                                           equivalence_modulus_set *set,
                                           int64_t modulus) {
  size_t index;
  if (modulus <= 1)
    return true;
  if (!set->capacity || set->count >= set->capacity / 2u) {
    if (!equivalence_modulus_set_grow(arena, set))
      return false;
  }
  index = equivalence_modulus_hash(modulus) & (set->capacity - 1u);
  while (set->slots[index] != 0 && set->slots[index] != modulus)
    index = (index + 1u) & (set->capacity - 1u);
  if (set->slots[index] == modulus)
    return true;
  set->slots[index] = modulus;
  set->count++;
  return true;
}

/* Discover congruence candidates by visiting each node in both residual DAGs
 * once. Growable query-local storage avoids semantic depth, visit, and
 * candidate-count cutoffs without scanning unrelated context state. */
static bool equivalence_collect_congruences(equivalence_state *state,
                                            ixs_node *lhs, ixs_node *rhs,
                                            equivalence_modulus_set *moduli) {
  query_node_set visited;
  ixs_node **stack = NULL;
  size_t stack_capacity = 0;
  size_t stack_count = 0;

  memset(&visited, 0, sizeof(visited));
  if (!query_node_stack_push(&state->ctx->scratch, &stack, &stack_count,
                             &stack_capacity, lhs) ||
      !query_node_stack_push(&state->ctx->scratch, &stack, &stack_count,
                             &stack_capacity, rhs))
    goto oom;
  while (stack_count > 0) {
    ixs_node *node = stack[--stack_count];
    uint32_t child_count;
    uint32_t i;
    bool inserted;
    if (!query_node_set_insert(&state->ctx->scratch, &visited, node, &inserted))
      goto oom;
    if (!inserted)
      continue;
    if (node->tag == IXS_SYM) {
      int64_t modulus;
      int64_t remainder;
      bool known = bounds_store_get_modrem(state->bounds, node->u.name,
                                           &modulus, &remainder);
      if (state->bounds->oom)
        goto oom;
      if (known && !equivalence_modulus_set_insert(&state->ctx->scratch, moduli,
                                                   modulus))
        goto oom;
      (void)remainder;
    }
    child_count = ixs_node_nchildren(node);
    for (i = 0; i < child_count; i++) {
      if (!query_node_stack_push(&state->ctx->scratch, &stack, &stack_count,
                                 &stack_capacity, ixs_node_child(node, i)))
        goto oom;
    }
  }
  return true;

oom:
  state->oom = true;
  return false;
}

static ixs_node *equivalence_build_rounded_ordered(equivalence_state *state,
                                                   ixs_node *cmp,
                                                   int64_t divisor) {
  ixs_node *scale = ixs_node_int(state->ctx, divisor);
  ixs_node *quotient;
  ixs_node *rounded;
  if (!scale)
    return NULL;
  quotient = simp_div(state->ctx, cmp->u.binary.lhs, scale);
  if (!quotient)
    return NULL;
  switch (cmp->u.binary.cmp_op) {
  case IXS_CMP_LT:
  case IXS_CMP_GE:
    rounded = simp_floor(state->ctx, quotient);
    break;
  case IXS_CMP_LE:
  case IXS_CMP_GT:
    rounded = simp_ceil(state->ctx, quotient);
    break;
  default:
    return cmp;
  }
  if (!rounded)
    return NULL;
  return simp_cmp(state->ctx, rounded, cmp->u.binary.cmp_op,
                  state->ctx->node_zero);
}

static ixs_check_result
equivalence_ordered_congruence_forms(equivalence_state *state, ixs_node *lhs,
                                     ixs_node *rhs) {
  ixs_arena_mark mark = ixs_arena_save(&state->ctx->scratch);
  equivalence_modulus_set moduli;
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  size_t i;

  memset(&moduli, 0, sizeof(moduli));
  if (state->oom || state->limited ||
      !equivalence_collect_congruences(state, lhs->u.binary.lhs,
                                       rhs->u.binary.lhs, &moduli))
    goto cleanup;
  for (i = 0; i < moduli.capacity; i++) {
    ixs_node *normalized[2];
    if (moduli.slots[i] == 0)
      continue;
    normalized[0] =
        equivalence_build_rounded_ordered(state, lhs, moduli.slots[i]);
    normalized[1] =
        equivalence_build_rounded_ordered(state, rhs, moduli.slots[i]);
    if (!normalized[0] || !normalized[1] ||
        !simp_simplify_batch_bounds(state->ctx, normalized, 2, state->bounds) ||
        state->bounds->oom) {
      state->oom = true;
      goto cleanup;
    }
    if (!ixs_node_is_sentinel(normalized[0]) &&
        !ixs_node_is_sentinel(normalized[1]) &&
        normalized[0] == normalized[1]) {
      result = IXS_CHECK_TRUE;
      goto cleanup;
    }
  }

cleanup:
  ixs_arena_restore(&state->ctx->scratch, mark);
  return result;
}

static ixs_check_result
equivalence_ordered_comparisons(equivalence_state *state, ixs_node *lhs,
                                ixs_node *rhs) {
  bool left_lower, right_lower;
  int64_t left_threshold, right_threshold, delta, mapped_threshold;
  int64_t lo, hi;
  if (!lhs || !rhs || lhs->tag != IXS_CMP || rhs->tag != IXS_CMP ||
      !ixs_node_is_zero(lhs->u.binary.rhs) ||
      !ixs_node_is_zero(rhs->u.binary.rhs) ||
      !equivalence_ordered_cut(lhs->u.binary.cmp_op, &left_lower,
                               &left_threshold) ||
      !equivalence_ordered_cut(rhs->u.binary.cmp_op, &right_lower,
                               &right_threshold) ||
      left_lower != right_lower ||
      ixs_bounds_check_integer_valued(state->bounds, lhs->u.binary.lhs) !=
          IXS_CHECK_TRUE ||
      ixs_bounds_check_integer_valued(state->bounds, rhs->u.binary.lhs) !=
          IXS_CHECK_TRUE)
    return IXS_CHECK_UNKNOWN;
  if (equivalence_integer_delta(state, lhs->u.binary.lhs, rhs->u.binary.lhs,
                                &delta) &&
      ixs_safe_add(right_threshold, delta, &mapped_threshold)) {
    bool cut_valid;
    if (left_threshold == mapped_threshold)
      return IXS_CHECK_TRUE;
    lo = left_threshold < mapped_threshold ? left_threshold : mapped_threshold;
    hi = left_threshold < mapped_threshold ? mapped_threshold : left_threshold;
    cut_valid =
        left_lower ? ixs_safe_sub(hi, 1, &hi) : ixs_safe_add(lo, 1, &lo);
    if (cut_valid &&
        equivalence_no_reachable_integer(state, lhs->u.binary.lhs, lo, hi))
      return IXS_CHECK_TRUE;
  }
  return equivalence_ordered_congruence_forms(state, lhs, rhs);
}

static void equivalence_note_algebra_status(equivalence_state *state,
                                            ixs_algebra_status status) {
  if (status == IXS_ALGEBRA_UNREPRESENTABLE)
    state->arithmetic_unrepresentable = true;
  else if (status == IXS_ALGEBRA_LIMITED)
    state->limited = true;
  else if (status == IXS_ALGEBRA_INVALID)
    state->invalid = true;
  else if (status == IXS_ALGEBRA_OOM)
    state->oom = true;
}

static bool equivalence_remainder_integer_proven(equivalence_state *state,
                                                 ixs_node *node) {
  bool proven =
      ixs_bounds_check_integer_valued(state->bounds, node) == IXS_CHECK_TRUE;
  if (state->bounds->oom)
    state->oom = true;
  return proven;
}

static bool equivalence_split_affine_round(equivalence_state *state,
                                           ixs_node *value, bool ceiling,
                                           ixs_node **argument,
                                           ixs_node **residual) {
  ixs_algebra_status status = ixs_additive_row_split_round(
      state->ctx, value, ceiling, argument, residual);
  equivalence_note_algebra_status(state, status);
  return status == IXS_ALGEBRA_MATCH;
}

static ixs_check_result
equivalence_affine_round_context(equivalence_state *state, ixs_node *lhs,
                                 ixs_node *rhs, unsigned depth) {
  size_t i;

  for (i = 0; i < 2u; i++) {
    ixs_node *lhs_argument;
    ixs_node *lhs_residual;
    ixs_node *rhs_argument;
    ixs_node *rhs_residual;
    ixs_node *lhs_shifted;
    ixs_node *rhs_shifted;

    if (!equivalence_split_affine_round(state, lhs, i != 0u, &lhs_argument,
                                        &lhs_residual) ||
        !equivalence_split_affine_round(state, rhs, i != 0u, &rhs_argument,
                                        &rhs_residual) ||
        (ixs_node_is_zero(lhs_residual) && ixs_node_is_zero(rhs_residual)) ||
        !equivalence_remainder_integer_proven(state, lhs_residual) ||
        !equivalence_remainder_integer_proven(state, rhs_residual) ||
        equivalence_build_add(state, lhs_argument, lhs_residual,
                              &lhs_shifted) != EQUIVALENCE_BUILD_OK ||
        equivalence_build_add(state, rhs_argument, rhs_residual,
                              &rhs_shifted) != EQUIVALENCE_BUILD_OK ||
        ixs_node_is_sentinel(lhs_shifted) || ixs_node_is_sentinel(rhs_shifted))
      continue;
    if (equivalence_bounded_core(state, lhs_shifted, rhs_shifted, depth) ==
        IXS_CHECK_TRUE)
      return IXS_CHECK_TRUE;
    if (state->limited || state->invalid || state->oom ||
        state->arithmetic_unrepresentable)
      return IXS_CHECK_UNKNOWN;
  }
  return IXS_CHECK_UNKNOWN;
}

static bool equivalence_project_truncating_rounds(
    equivalence_state *state, ixs_node *source_lhs, ixs_node *root_lhs,
    ixs_node *source_rhs, ixs_node *root_rhs, unsigned depth,
    ixs_node **projected_lhs, ixs_node **projected_rhs) {
  ixs_division_projection_result result = ixs_division_algebra_project(
      state->ctx, state->bounds, source_lhs, root_lhs, source_rhs, root_rhs,
      depth == 0u ? IXS_DIVISION_PROJECT_ALL
                  : IXS_DIVISION_PROJECT_DIRECT_ONLY);
  equivalence_note_algebra_status(state, result.status);
  *projected_lhs = result.lhs;
  *projected_rhs = result.rhs;
  return result.status == IXS_ALGEBRA_MATCH;
}

static bool equivalence_flatten_logic(equivalence_state *state, ixs_node *root,
                                      ixs_tag tag, ixs_node ***terms,
                                      size_t *nterms, size_t *terms_capacity) {
  query_node_set visited;
  ixs_node **stack = NULL;
  size_t stack_capacity = 0;
  size_t nstack = 0;

  memset(&visited, 0, sizeof(visited));
  *nterms = 0;
  if (!query_node_stack_push(&state->ctx->scratch, &stack, &nstack,
                             &stack_capacity, root))
    goto oom;
  while (nstack > 0) {
    ixs_node *node = stack[--nstack];
    bool inserted;
    if (!query_node_set_insert(&state->ctx->scratch, &visited, node, &inserted))
      goto oom;
    /* AND and OR are idempotent, so shared and repeated operands need one
     * visit. This also terminates malformed cyclic nodes. */
    if (!inserted)
      continue;
    if (node->tag == tag && ixs_node_is_bool_valued(node)) {
      uint32_t i;
      for (i = 0; i < node->u.assoc.nargs; i++) {
        if (!query_node_stack_push(&state->ctx->scratch, &stack, &nstack,
                                   &stack_capacity, node->u.assoc.args[i]))
          goto oom;
      }
    } else {
      if (!query_node_stack_push(&state->ctx->scratch, terms, nterms,
                                 terms_capacity, node))
        goto oom;
    }
  }
  return true;

oom:
  state->oom = true;
  return false;
}

static ixs_check_result equivalence_match_logic(equivalence_state *state,
                                                ixs_node *lhs, ixs_node *rhs,
                                                unsigned depth) {
  ixs_arena_mark mark = ixs_arena_save(&state->ctx->scratch);
  ixs_node **left_terms = NULL;
  ixs_node **right_terms = NULL;
  unsigned char *left_matched;
  unsigned char *right_matched;
  size_t left_capacity = 0;
  size_t right_capacity = 0;
  size_t nleft;
  size_t nright;
  size_t i;
  size_t j;
  ixs_check_result result = IXS_CHECK_UNKNOWN;

  if (!equivalence_flatten_logic(state, lhs, lhs->tag, &left_terms, &nleft,
                                 &left_capacity) ||
      !equivalence_flatten_logic(state, rhs, rhs->tag, &right_terms, &nright,
                                 &right_capacity) ||
      nleft != nright)
    goto cleanup;
  left_matched = ixs_arena_alloc(&state->ctx->scratch, nleft, 1);
  right_matched = ixs_arena_alloc(&state->ctx->scratch, nright, 1);
  if ((!left_matched || !right_matched) && nleft != 0) {
    state->oom = true;
    goto cleanup;
  }
  if (nleft != 0) {
    memset(left_matched, 0, nleft);
    memset(right_matched, 0, nright);
  }

  /* Match exact terms first for deterministic pairing and no proof work on
   * the common reordered-tree case. */
  for (i = 0; i < nleft; i++) {
    for (j = 0; j < nright; j++) {
      if (!right_matched[j] && left_terms[i] == right_terms[j]) {
        left_matched[i] = 1;
        right_matched[j] = 1;
        break;
      }
    }
  }
  for (i = 0; i < nleft; i++) {
    if (left_matched[i])
      continue;
    /* Nested associative matching is an optional refinement. Only the outer
     * match starts subproofs, statically bounding C recursion; each subproof
     * still traverses its DAG with growable storage. */
    if (depth != 0u)
      goto cleanup;
    for (j = 0; j < nright; j++) {
      if (!right_matched[j] &&
          equivalence_core(state, left_terms[i], right_terms[j], depth + 1u) ==
              IXS_CHECK_TRUE) {
        left_matched[i] = 1;
        right_matched[j] = 1;
        break;
      }
    }
    if (!left_matched[i])
      goto cleanup;
  }
  result = IXS_CHECK_TRUE;

cleanup:
  ixs_arena_restore(&state->ctx->scratch, mark);
  return result;
}

static ixs_check_result equivalence_predicate_shapes(equivalence_state *state,
                                                     ixs_node *lhs,
                                                     ixs_node *rhs,
                                                     unsigned depth) {
  if (lhs->tag == rhs->tag && (lhs->tag == IXS_AND || lhs->tag == IXS_OR))
    return equivalence_match_logic(state, lhs, rhs, depth);
  if (lhs->tag == IXS_NOT && rhs->tag == IXS_NOT) {
    if (depth != 0u)
      return IXS_CHECK_UNKNOWN;
    do {
      lhs = lhs->u.unary_bool.arg;
      rhs = rhs->u.unary_bool.arg;
    } while (lhs && rhs && lhs->tag == IXS_NOT && rhs->tag == IXS_NOT);
    return equivalence_core(state, lhs, rhs, depth + 1u);
  }
  if (lhs->tag == IXS_CMP && rhs->tag == IXS_CMP) {
    int64_t delta;
    ixs_check_result result = equivalence_ordered_comparisons(state, lhs, rhs);
    /* Comparisons are canonical residuals against a shared right operand. An
     * exact zero delta therefore preserves the common comparison operator. */
    if (result == IXS_CHECK_UNKNOWN &&
        lhs->u.binary.cmp_op == rhs->u.binary.cmp_op &&
        lhs->u.binary.rhs == rhs->u.binary.rhs &&
        equivalence_integer_delta(state, lhs->u.binary.lhs, rhs->u.binary.lhs,
                                  &delta) &&
        delta == 0)
      result = IXS_CHECK_TRUE;
    return result;
  }
  return IXS_CHECK_UNKNOWN;
}

static ixs_check_result equivalence_expanded(equivalence_state *state,
                                             ixs_node *lhs, ixs_node *rhs,
                                             unsigned depth) {
  ixs_node *expanded_lhs = expand_impl(state->ctx, lhs);
  ixs_node *expanded_rhs = expand_impl(state->ctx, rhs);
  ixs_check_result result;
  bool lhs_limited = false;
  bool rhs_limited = false;
  if (!expanded_lhs || !expanded_rhs) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (ixs_node_is_sentinel(expanded_lhs) ||
      ixs_node_is_sentinel(expanded_rhs)) {
    bounds_query_note_invalid(state->bounds);
    return IXS_CHECK_UNKNOWN;
  }
  expanded_lhs = simp_simplify_bounds_status(state->ctx, expanded_lhs,
                                             state->bounds, &lhs_limited);
  expanded_rhs = simp_simplify_bounds_status(state->ctx, expanded_rhs,
                                             state->bounds, &rhs_limited);
  if (lhs_limited || rhs_limited) {
    state->limited = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (!expanded_lhs || !expanded_rhs) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (ixs_node_is_sentinel(expanded_lhs) ||
      ixs_node_is_sentinel(expanded_rhs)) {
    bounds_query_note_invalid(state->bounds);
    return IXS_CHECK_UNKNOWN;
  }
  if (expanded_lhs == expanded_rhs)
    return IXS_CHECK_TRUE;
  result = equivalence_difference(state, expanded_lhs, expanded_rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  result =
      equivalence_quotient_remainder_algebra(state, expanded_lhs, expanded_rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  if (ixs_node_is_bool_valued(expanded_lhs) &&
      ixs_node_is_bool_valued(expanded_rhs))
    return equivalence_predicate_shapes(state, expanded_lhs, expanded_rhs,
                                        depth);
  return IXS_CHECK_UNKNOWN;
}

static bool equivalence_low_bits_modulus(ixs_node *lhs, ixs_node *rhs,
                                         unsigned *bits) {
  uint64_t modulus;
  *bits = 0u;
  if (!lhs || !rhs || lhs->tag != IXS_MOD || rhs->tag != IXS_MOD ||
      lhs->u.binary.rhs->tag != IXS_INT ||
      rhs->u.binary.rhs != lhs->u.binary.rhs || lhs->u.binary.rhs->u.ival <= 0)
    return false;
  modulus = (uint64_t)lhs->u.binary.rhs->u.ival;
  if ((modulus & (modulus - UINT64_C(1))) != 0u)
    return false;
  while (modulus > 1u) {
    modulus >>= 1u;
    (*bits)++;
  }
  return true;
}

static bool equivalence_low_bits_domain(equivalence_state *state,
                                        ixs_node *node) {
  ixs_algebra_status status =
      ixs_bounds_check_integer_domain(state->bounds, node);
  equivalence_note_algebra_status(state, status);
  return status == IXS_ALGEBRA_MATCH;
}

static ixs_node *equivalence_low_bits_rebuild(void *user, ixs_node *root,
                                              uint32_t count,
                                              ixs_node *const *targets,
                                              ixs_node *const *replacements) {
  equivalence_state *state = user;
  return simp_subs_multi(state->ctx, root, count, targets, replacements);
}

/* The original outer operations own the domain certificate. Projection never
 * substitutes a normalized root for that source obligation. */
static ixs_check_result equivalence_low_bits(equivalence_state *state,
                                             ixs_node *lhs, ixs_node *rhs,
                                             unsigned depth) {
  ixs_algebra_status status;
  ixs_node *roots[2];
  ixs_node *projected[2];
  ixs_low_bits_algebra_ops ops;
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  bool saved_unrepresentable;
  unsigned bits;
  if (!equivalence_low_bits_modulus(lhs, rhs, &bits) ||
      !equivalence_low_bits_domain(state, lhs) ||
      !equivalence_low_bits_domain(state, rhs) ||
      !equivalence_low_bits_domain(state, lhs->u.binary.lhs) ||
      !equivalence_low_bits_domain(state, rhs->u.binary.lhs))
    return result;
  roots[0] = lhs->u.binary.lhs;
  roots[1] = rhs->u.binary.lhs;
  ops.user = state;
  ops.rebuild = equivalence_low_bits_rebuild;
  ops.project_leaf = NULL;
  status = ixs_low_bits_algebra_project(state->ctx, state->bounds, roots, 2u,
                                        bits, &ops, projected);
  equivalence_note_algebra_status(state, status);
  if (status != IXS_ALGEBRA_MATCH ||
      !equivalence_low_bits_domain(state, projected[0]) ||
      !equivalence_low_bits_domain(state, projected[1]))
    return result;
  if (projected[0] == projected[1])
    return IXS_CHECK_TRUE;
  saved_unrepresentable = state->arithmetic_unrepresentable;
  state->arithmetic_unrepresentable = false;
  result =
      equivalence_bounded_core(state, projected[0], projected[1], depth + 1u);
  state->arithmetic_unrepresentable =
      saved_unrepresentable || state->arithmetic_unrepresentable;
  return result == IXS_CHECK_TRUE ? result : IXS_CHECK_UNKNOWN;
}

static ixs_check_result equivalence_core(equivalence_state *state,
                                         ixs_node *lhs, ixs_node *rhs,
                                         unsigned depth) {
  equivalence_memo_entry *entry;
  ixs_check_result result;

  if (!lhs || !rhs || state->limited || state->invalid || state->oom ||
      state->arithmetic_unrepresentable)
    return IXS_CHECK_UNKNOWN;
  if ((uintptr_t)lhs > (uintptr_t)rhs) {
    ixs_node *tmp = lhs;
    lhs = rhs;
    rhs = tmp;
  }
  entry = equivalence_memo_get(state, lhs, rhs, true);
  if (!entry) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (entry->complete)
    return entry->result;
  if (entry->active) {
    state->memo_cycles++;
    return IXS_CHECK_UNKNOWN;
  }
  entry->active = true;
  result = equivalence_core_impl(state, lhs, rhs, depth, true);
  entry = equivalence_memo_get(state, lhs, rhs, false);
  if (!entry) {
    state->invalid = true;
    return IXS_CHECK_UNKNOWN;
  }
  entry->active = false;
  if (!state->limited && !state->invalid && !state->oom) {
    entry->result = result;
    entry->complete = true;
  }
  return result;
}

#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
/* Start an ordinary equivalence query with its bounded child-proof budget
 * exhausted. This exercises the production stop condition without a test-only
 * proof branch. */
IXS_STATIC ixs_check_result ixs_bounds_equivalence_subproof_limit_probe(
    ixs_facts *facts, const ixs_node *lhs, const ixs_node *rhs) {
  equivalence_state state;
  ixs_check_result result;

  if (!facts || !facts->usable || !lhs || !rhs)
    return IXS_CHECK_UNKNOWN;
  equivalence_state_init(&state, facts->ctx, &facts->bounds);
  state.bounded_subproof_depth = EQUIVALENCE_BOUNDED_SUBPROOF_DEPTH;
  result = equivalence_core(&state, lhs, rhs, 0);
  if (state.limited || state.invalid || state.oom)
    result = IXS_CHECK_UNKNOWN;
  equivalence_state_destroy(&state);
  return result;
}

/* Exercise the
 * production
 * quotient-algebra
 * budget without a
 * test-only proof
 * branch. */
IXS_STATIC ixs_check_result ixs_bounds_equivalence_quotient_limit_probe(
    ixs_facts *facts, const ixs_node *lhs, const ixs_node *rhs) {
  ixs_quotient_algebra_result result;
  unsigned candidates = IXS_QUOTIENT_ALGEBRA_MAX_CANDIDATES;

  if (!facts || !facts->usable || !lhs || !rhs)
    return IXS_CHECK_UNKNOWN;
  result = ixs_quotient_algebra_check(facts->ctx, &facts->bounds, lhs, rhs,
                                      candidates);
  return result.check;
}
#endif

static ixs_check_result equivalence_predicate_truth(equivalence_state *state,
                                                    ixs_node *lhs,
                                                    ixs_node *rhs) {
  ixs_check_result lhs_truth;
  ixs_check_result rhs_truth;
  bool lhs_limited = false;
  bool rhs_limited = false;

  if (!ixs_node_is_bool_valued(lhs) || !ixs_node_is_bool_valued(rhs))
    return IXS_CHECK_UNKNOWN;
  lhs_truth = bounds_predicate_eval(state->bounds, lhs, &lhs_limited);
  rhs_truth = bounds_predicate_eval(state->bounds, rhs, &rhs_limited);
  if (lhs_limited || rhs_limited) {
    state->limited = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (lhs_truth == IXS_CHECK_UNKNOWN || rhs_truth == IXS_CHECK_UNKNOWN)
    return IXS_CHECK_UNKNOWN;
  return lhs_truth == rhs_truth ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
}

static ixs_check_result equivalence_projected(equivalence_state *state,
                                              ixs_node *lhs, ixs_node *rhs,
                                              unsigned depth) {
  ixs_node *projected_lhs;
  ixs_node *projected_rhs;
  ixs_check_result result;

  if (!equivalence_project_truncating_rounds(state, lhs, lhs, rhs, rhs, depth,
                                             &projected_lhs, &projected_rhs))
    return IXS_CHECK_UNKNOWN;
  if (projected_lhs == projected_rhs)
    return IXS_CHECK_TRUE;
  result = equivalence_difference(state, projected_lhs, projected_rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  result = equivalence_quotient_remainder_algebra(state, projected_lhs,
                                                  projected_rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  return equivalence_expanded(state, projected_lhs, projected_rhs, depth);
}

typedef struct {
  ixs_node *selector;
  const char *name;
  int64_t points[EQUIVALENCE_PIECEWISE_MAX_POINTS];
  size_t count;
  uint64_t remaining;
} equivalence_piecewise_domain;

static ixs_node *equivalence_piecewise_affine_symbol(ixs_node *expr) {
  if (expr->tag == IXS_SYM)
    return expr;
  if (expr->tag == IXS_MUL && expr->u.mul.nfactors == 1u &&
      expr->u.mul.factors[0].exp == 1 &&
      expr->u.mul.factors[0].base->tag == IXS_SYM)
    return expr->u.mul.factors[0].base;
  if (expr->tag == IXS_ADD && expr->u.add.nterms == 1u &&
      expr->u.add.terms[0].term->tag == IXS_SYM)
    return expr->u.add.terms[0].term;
  return NULL;
}

static bool equivalence_piecewise_affine_guard(ixs_node *condition,
                                               ixs_node **selector,
                                               int64_t *scale, int64_t *offset,
                                               ixs_cmp_op *op) {
  ixs_node *affine;
  const char *name;

  if (!condition || condition->tag != IXS_CMP)
    return false;
  *op = condition->u.binary.cmp_op;
  if (ixs_node_is_zero(condition->u.binary.rhs)) {
    affine = condition->u.binary.lhs;
  } else if (ixs_node_is_zero(condition->u.binary.lhs)) {
    affine = condition->u.binary.rhs;
    *op = flip_cmp(*op);
  } else {
    return false;
  }
  if (!bounds_extract_integer_affine(affine, &name, scale, offset))
    return false;
  *selector = equivalence_piecewise_affine_symbol(affine);
  return *selector && (*selector)->u.name == name;
}

static bool equivalence_piecewise_find_selector(ixs_node *piecewise,
                                                ixs_node **selector) {
  uint32_t i;

  *selector = NULL;
  for (i = 0; i < piecewise->u.pw.ncases; i++) {
    ixs_node *condition = piecewise->u.pw.cases[i].cond;
    int64_t scale;
    int64_t offset;
    ixs_cmp_op op;
    if (!condition)
      return false;
    if (ixs_node_is_known_true(condition) || ixs_node_is_known_false(condition))
      continue;
    if (!equivalence_piecewise_affine_guard(condition, selector, &scale,
                                            &offset, &op))
      return false;
    return true;
  }
  return false;
}

static bool
equivalence_piecewise_domain_init(equivalence_state *state, ixs_node *piecewise,
                                  equivalence_piecewise_domain *domain) {
  ixs_var_bound *var;
  int64_t modulus;
  int64_t remainder;
  int64_t lower;
  int64_t upper;
  int64_t point;

  memset(domain, 0, sizeof(*domain));
  if (!equivalence_piecewise_find_selector(piecewise, &domain->selector))
    return false;
  domain->name = domain->selector->u.name;
  var = bounds_store_find_var(state->bounds, domain->name);
  if (!var || !var->iv.valid || var->iv.lo_inf || var->iv.hi_inf)
    return false;
  lower = ixs_rat_ceil(var->iv.lo_p, var->iv.lo_q);
  upper = ixs_rat_floor(var->iv.hi_p, var->iv.hi_q);
  if (lower > upper)
    return false;
  modulus = var->modulus > 0 ? var->modulus : 1;
  remainder = var->modulus > 0 ? var->remainder : 0;
  if (!ixs_integer_align_congruence_up(lower, modulus, remainder, &point) ||
      point > upper)
    return false;

  for (;;) {
    int64_t next;
    if (domain->count == EQUIVALENCE_PIECEWISE_MAX_POINTS)
      return false;
    domain->points[domain->count++] = point;
    if (!ixs_safe_add(point, modulus, &next) || next > upper)
      break;
    point = next;
  }
  domain->remaining = domain->count == EQUIVALENCE_PIECEWISE_MAX_POINTS
                          ? UINT64_MAX
                          : (UINT64_C(1) << domain->count) - UINT64_C(1);
  return true;
}

static bool equivalence_piecewise_cmp_zero(ixs_cmp_op op, int64_t value) {
  switch (op) {
  case IXS_CMP_GT:
    return value > 0;
  case IXS_CMP_GE:
    return value >= 0;
  case IXS_CMP_LT:
    return value < 0;
  case IXS_CMP_LE:
    return value <= 0;
  case IXS_CMP_EQ:
    return value == 0;
  case IXS_CMP_NE:
    return value != 0;
  }
  return false;
}

static bool
equivalence_piecewise_guard_mask(const equivalence_piecewise_domain *domain,
                                 ixs_node *condition, uint64_t *mask) {
  ixs_node *selector;
  int64_t scale;
  int64_t offset;
  ixs_cmp_op op;
  size_t i;

  *mask = 0u;
  if (ixs_node_is_known_false(condition))
    return true;
  if (ixs_node_is_known_true(condition)) {
    *mask = domain->count == EQUIVALENCE_PIECEWISE_MAX_POINTS
                ? UINT64_MAX
                : (UINT64_C(1) << domain->count) - UINT64_C(1);
    return true;
  }
  if (!equivalence_piecewise_affine_guard(condition, &selector, &scale, &offset,
                                          &op) ||
      selector != domain->selector)
    return false;
  for (i = 0; i < domain->count; i++) {
    int64_t product;
    int64_t value;
    if (!ixs_safe_mul(scale, domain->points[i], &product) ||
        !ixs_safe_add(product, offset, &value))
      return false;
    if (equivalence_piecewise_cmp_zero(op, value))
      *mask |= UINT64_C(1) << i;
  }
  return true;
}

static bool equivalence_piecewise_single_point(uint64_t mask, size_t *index) {
  size_t i;

  if (mask == 0u || (mask & (mask - UINT64_C(1))) != 0u)
    return false;
  for (i = 0; i < EQUIVALENCE_PIECEWISE_MAX_POINTS; i++)
    if ((mask & (UINT64_C(1) << i)) != 0u) {
      *index = i;
      return true;
    }
  return false;
}

/* Admit Piecewise arm substitution only for small complete DAGs, preventing
 * branch count from multiplying reconstruction of a large peer. */
static bool equivalence_piecewise_small_operand(ixs_node *root) {
  ixs_node *stack[EQUIVALENCE_PIECEWISE_MAX_POINTS];
  ixs_node *seen[EQUIVALENCE_PIECEWISE_MAX_POINTS];
  size_t stack_count = 0u;
  size_t seen_count = 0u;

  if (!root)
    return false;
  stack[stack_count++] = root;
  while (stack_count != 0u) {
    ixs_node *node = stack[--stack_count];
    uint32_t child_count;
    uint32_t child;
    size_t i;
    for (i = 0; i < seen_count; i++)
      if (seen[i] == node)
        break;
    if (i != seen_count)
      continue;
    if (seen_count == EQUIVALENCE_PIECEWISE_MAX_POINTS ||
        node->tag == IXS_PIECEWISE ||
        !defined_child_count(node, &child_count) ||
        child_count > EQUIVALENCE_PIECEWISE_MAX_POINTS - stack_count)
      return false;
    seen[seen_count++] = node;
    for (child = 0; child < child_count; child++)
      stack[stack_count++] = defined_child_at(node, child);
  }
  return true;
}

static bool
equivalence_piecewise_prove_point(equivalence_state *state, ixs_node *value,
                                  ixs_node *other,
                                  const equivalence_piecewise_domain *domain,
                                  size_t point_index, unsigned depth) {
  ixs_ctx *ctx = state->ctx;
  ixs_query_transaction transaction;
  ixs_node *point;
  ixs_node *substituted_value;
  ixs_node *substituted_other;
  bool value_oom = false;
  bool value_limited = false;
  bool other_oom = false;
  bool other_limited = false;
  ixs_check_result result = IXS_CHECK_UNKNOWN;

  ixs_query_transaction_begin(&transaction, ctx, NULL, NULL);
  point = ixs_node_int(ctx, domain->points[point_index]);
  substituted_value =
      point ? simp_subs(ctx, value, domain->selector, point) : NULL;
  substituted_other =
      point ? simp_subs(ctx, other, domain->selector, point) : NULL;
  (void)ixs_query_transaction_finish(&transaction, false);
  if (!point || !substituted_value || !substituted_other) {
    state->oom = true;
    return false;
  }
  if (ixs_node_is_sentinel(substituted_value) ||
      ixs_node_is_sentinel(substituted_other))
    return false;
  if (bounds_defined_check_detail(state->bounds, substituted_value, &value_oom,
                                  &value_limited) != IXS_CHECK_TRUE ||
      bounds_defined_check_detail(state->bounds, substituted_other, &other_oom,
                                  &other_limited) != IXS_CHECK_TRUE) {
    if (value_oom || other_oom || state->bounds->oom)
      state->oom = true;
    if (value_limited || other_limited)
      state->limited = true;
    return false;
  }
  result = equivalence_bounded_core(state, substituted_value, substituted_other,
                                    depth);
  return result == IXS_CHECK_TRUE;
}

/* Final bounded fallback for an exact root Piecewise. Track first-match
 * reachability in a complete finite congruent selector mask, then prove only
 * single-point arms. No fact-table fork or whole-operand substitution occurs.
 * Work is bounded by 16 arms, 64 selector points, and 64-node arm/peer DAGs. */
static ixs_check_result equivalence_piecewise_root(equivalence_state *state,
                                                   ixs_node *lhs, ixs_node *rhs,
                                                   unsigned depth) {
  equivalence_piecewise_domain domain;
  ixs_node *piecewise;
  ixs_node *other;
  bool have_reachable = false;
  uint32_t i;

  if ((lhs->tag == IXS_PIECEWISE) == (rhs->tag == IXS_PIECEWISE))
    return IXS_CHECK_UNKNOWN;
  piecewise = lhs->tag == IXS_PIECEWISE ? lhs : rhs;
  other = lhs->tag == IXS_PIECEWISE ? rhs : lhs;
  if (piecewise->u.pw.ncases == 0u || !piecewise->u.pw.cases) {
    state->invalid = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (piecewise->u.pw.ncases > EQUIVALENCE_PIECEWISE_MAX_CASES ||
      !equivalence_piecewise_small_operand(other) ||
      !equivalence_piecewise_domain_init(state, piecewise, &domain))
    return IXS_CHECK_UNKNOWN;

  for (i = 0; i < piecewise->u.pw.ncases; i++) {
    ixs_node *condition = piecewise->u.pw.cases[i].cond;
    ixs_node *value = piecewise->u.pw.cases[i].value;
    uint64_t condition_mask;
    uint64_t active;
    size_t point_index;

    if (domain.remaining == 0u)
      return have_reachable ? IXS_CHECK_TRUE : IXS_CHECK_UNKNOWN;
    if (!condition || !value ||
        !equivalence_piecewise_guard_mask(&domain, condition, &condition_mask))
      return IXS_CHECK_UNKNOWN;
    active = domain.remaining & condition_mask;
    if (active != 0u) {
      if (!equivalence_piecewise_single_point(active, &point_index) ||
          !equivalence_piecewise_small_operand(value) ||
          !equivalence_piecewise_prove_point(state, value, other, &domain,
                                             point_index, depth))
        return IXS_CHECK_UNKNOWN;
      have_reachable = true;
    }
    domain.remaining &= ~condition_mask;
  }
  return domain.remaining == 0u && have_reachable ? IXS_CHECK_TRUE
                                                  : IXS_CHECK_UNKNOWN;
}

static ixs_check_result
equivalence_quotient_remainder_algebra(equivalence_state *state, ixs_node *lhs,
                                       ixs_node *rhs) {
  ixs_bounds *bounds = state->bounds;
  ixs_bounds_transport_snapshot transport =
      ixs_bounds_query_transport_snapshot(bounds);
  size_t cycle_blocks = bounds_query_cycle_count(bounds);
  bool blocked;
  ixs_quotient_algebra_result result =
      ixs_quotient_algebra_check(state->ctx, bounds, lhs, rhs, 0u);
  blocked = result.limited || bounds_query_limited_since(bounds, transport) ||
            bounds_query_cycle_count(bounds) != cycle_blocks;
  state->invalid |=
      result.invalid || bounds_query_invalid_since(bounds, transport);
  state->oom |= result.oom;
  if (blocked || state->invalid || state->oom)
    return IXS_CHECK_UNKNOWN;
  return result.check;
}

static ixs_check_result
equivalence_direct_arithmetic(equivalence_state *state, ixs_node *lhs,
                              ixs_node *rhs, ixs_node *simplified_lhs,
                              ixs_node *simplified_rhs, unsigned depth) {
  ixs_check_result result;

  result = equivalence_zero_sum(state, simplified_lhs, simplified_rhs, depth);
  if (result != IXS_CHECK_UNKNOWN)
    return result;

  result = equivalence_cancel_proven_add_terms(state, simplified_lhs,
                                               simplified_rhs, depth, false);
  if (result != IXS_CHECK_UNKNOWN)
    return result;

  result = equivalence_difference(state, simplified_lhs, simplified_rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  if (state->arithmetic_unrepresentable)
    return equivalence_low_bits(state, lhs, rhs, depth);

  result = equivalence_affine_round_context(state, simplified_lhs,
                                            simplified_rhs, depth);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  if (state->arithmetic_unrepresentable)
    return equivalence_low_bits(state, lhs, rhs, depth);

  return IXS_CHECK_UNKNOWN;
}

static ixs_check_result
equivalence_context_composition(equivalence_state *state, ixs_node *lhs,
                                ixs_node *rhs, ixs_node *simplified_lhs,
                                ixs_node *simplified_rhs, unsigned depth,
                                bool allow_context) {
  ixs_check_result result;

  if (!allow_context)
    return IXS_CHECK_UNKNOWN;
  result =
      equivalence_same_context(state, simplified_lhs, simplified_rhs, depth);
  if (result == IXS_CHECK_UNKNOWN && state->arithmetic_unrepresentable)
    return equivalence_low_bits(state, lhs, rhs, depth);
  return result;
}

static ixs_check_result
equivalence_final_fallbacks(equivalence_state *state, ixs_node *lhs,
                            ixs_node *rhs, ixs_node *simplified_lhs,
                            ixs_node *simplified_rhs, unsigned depth,
                            bool allow_context) {
  ixs_check_result result =
      equivalence_expanded(state, simplified_lhs, simplified_rhs, depth);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  result = equivalence_cancel_proven_add_terms(state, simplified_lhs,
                                               simplified_rhs, depth, true);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  result = equivalence_low_bits(state, lhs, rhs, depth);
  if (result != IXS_CHECK_UNKNOWN || !allow_context)
    return result;
  return equivalence_piecewise_root(state, simplified_lhs, simplified_rhs,
                                    depth);
}

static ixs_check_result equivalence_core_impl(equivalence_state *state,
                                              ixs_node *lhs, ixs_node *rhs,
                                              unsigned depth,
                                              bool allow_context) {
  ixs_node *simplified_lhs;
  ixs_node *simplified_rhs;
  ixs_check_result result;
  bool lhs_limited = false;
  bool rhs_limited = false;

  if (state->visited != SIZE_MAX)
    state->visited++;
  if (lhs == rhs)
    return IXS_CHECK_TRUE;

  if (state->roots_simplified) {
    state->roots_simplified = false;
    simplified_lhs = lhs;
    simplified_rhs = rhs;
  } else {
    simplified_lhs = equivalence_simplify(state, lhs, &lhs_limited);
    simplified_rhs = equivalence_simplify(state, rhs, &rhs_limited);
  }
  if (lhs_limited || rhs_limited) {
    state->limited = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (!simplified_lhs || !simplified_rhs) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (ixs_node_is_sentinel(simplified_lhs) ||
      ixs_node_is_sentinel(simplified_rhs)) {
    bounds_query_note_invalid(state->bounds);
    return IXS_CHECK_UNKNOWN;
  }
  if (simplified_lhs == simplified_rhs)
    return IXS_CHECK_TRUE;

  result = equivalence_predicate_truth(state, simplified_lhs, simplified_rhs);
  if (result != IXS_CHECK_UNKNOWN || state->limited)
    return result;

  result = equivalence_quotient_remainder_algebra(state, simplified_lhs,
                                                  simplified_rhs);
  if (result != IXS_CHECK_UNKNOWN || state->limited || state->invalid ||
      state->oom)
    return result;

  result = equivalence_direct_arithmetic(state, lhs, rhs, simplified_lhs,
                                         simplified_rhs, depth);
  if (result != IXS_CHECK_UNKNOWN || state->arithmetic_unrepresentable)
    return result;
  result = equivalence_context_composition(
      state, lhs, rhs, simplified_lhs, simplified_rhs, depth, allow_context);
  if (result != IXS_CHECK_UNKNOWN || state->arithmetic_unrepresentable)
    return result;
  result = equivalence_projected(state, lhs, rhs, depth);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  return equivalence_final_fallbacks(state, lhs, rhs, simplified_lhs,
                                     simplified_rhs, depth, allow_context);
}

static ixs_algebra_status bounds_equivalence_query_detail_impl(
    ixs_bounds *bounds, ixs_ctx *ctx, ixs_node *lhs, ixs_node *rhs,
    ixs_check_result *result, bool roots_simplified) {
  ixs_query_transaction transaction;
  equivalence_state state;
  ixs_bounds_transport_snapshot transport;
  ixs_bounds_transport_snapshot limit_transport;
  bool track_limits = bounds_query_is_tracking(bounds);
  bool lhs_oom = false;
  bool rhs_oom = false;
  bool lhs_limited = false;
  bool rhs_limited = false;
  ixs_algebra_status status = IXS_ALGEBRA_MATCH;

  ixs_query_transaction_begin(&transaction, NULL, bounds, &ctx->scratch);
  transport = transaction.transport;
  limit_transport = transport;
  equivalence_state_init(&state, ctx, bounds);
  state.roots_simplified = roots_simplified;
  *result = IXS_CHECK_UNKNOWN;
  if (bounds_defined_check_detail(bounds, lhs, &lhs_oom, &lhs_limited) !=
          IXS_CHECK_TRUE ||
      bounds_defined_check_detail(bounds, rhs, &rhs_oom, &rhs_limited) !=
          IXS_CHECK_TRUE) {
    if (lhs_oom || rhs_oom || (!transaction.old_oom && bounds->oom))
      status = IXS_ALGEBRA_OOM;
    else if (lhs_limited || rhs_limited)
      status = IXS_ALGEBRA_LIMITED;
    goto restore;
  }
  limit_transport = ixs_bounds_query_transport_snapshot(bounds);
  if (roots_simplified) {
    assert(bounds->exact_projection_depth != UINT_MAX);
    bounds->exact_projection_depth++;
  }
  *result = equivalence_core(&state, lhs, rhs, 0);
  if (roots_simplified)
    bounds->exact_projection_depth--;
  if (state.invalid || bounds_query_invalid_since(bounds, transport)) {
    *result = IXS_CHECK_UNKNOWN;
    status = IXS_ALGEBRA_INVALID;
  } else if (state.oom || (!transaction.old_oom && bounds->oom)) {
    *result = IXS_CHECK_UNKNOWN;
    status = IXS_ALGEBRA_OOM;
  } else if (*result == IXS_CHECK_UNKNOWN &&
             (state.limited ||
              (track_limits &&
               bounds_query_limited_since(bounds, limit_transport)))) {
    *result = IXS_CHECK_UNKNOWN;
    status = IXS_ALGEBRA_LIMITED;
  }

restore:
  equivalence_state_destroy(&state);
  if (!transaction.old_oom && bounds->oom)
    bounds_store_invalidate_reads(bounds);
  (void)ixs_query_transaction_finish(&transaction, true);
  return status;
}

static ixs_algebra_status bounds_equivalence_query_detail_common(
    ixs_bounds *bounds, ixs_ctx *ctx, ixs_node *lhs, ixs_node *rhs,
    ixs_check_result *result, bool roots_simplified) {
  bounds_query_scope scope;
  bounds_query_cache_entry *cached = NULL;
  bounds_query_enter_result enter;
  ixs_algebra_status status;

  /* Exact-integer projection disables itself before entering equivalence.
   * The resulting restricted proof must not populate the full-proof cache:
   * UNKNOWN there may still be provable by a top-level query. */
  if (roots_simplified || bounds->exact_projection_depth != 0)
    return bounds_equivalence_query_detail_impl(bounds, ctx, lhs, rhs, result,
                                                roots_simplified);
  if (!bounds_query_should_track(bounds, lhs))
    return bounds_equivalence_query_detail_impl(bounds, ctx, lhs, rhs, result,
                                                roots_simplified);
  enter = bounds_query_begin_pair(bounds, BOUNDS_QUERY_EQUIVALENCE, lhs, rhs,
                                  &scope, &cached);
  switch (enter) {
  case BOUNDS_QUERY_ENTER_CACHED:
    *result = cached->result.equivalence;
    return IXS_ALGEBRA_MATCH;
  case BOUNDS_QUERY_ENTER_CYCLE:
    *result = IXS_CHECK_UNKNOWN;
    return IXS_ALGEBRA_MATCH;
  case BOUNDS_QUERY_ENTER_LIMIT:
    return IXS_ALGEBRA_LIMITED;
  case BOUNDS_QUERY_ENTER_INVALID:
    return IXS_ALGEBRA_INVALID;
  case BOUNDS_QUERY_ENTER_OOM:
    return IXS_ALGEBRA_OOM;
  case BOUNDS_QUERY_ENTER_STARTED:
    break;
  }

  status = bounds_equivalence_query_detail_impl(bounds, ctx, lhs, rhs, result,
                                                roots_simplified);
  if (status == IXS_ALGEBRA_LIMITED)
    bounds_query_note_limit(bounds);
  else if (status == IXS_ALGEBRA_INVALID)
    bounds_query_note_invalid(bounds);
  else if (status == IXS_ALGEBRA_OOM)
    bounds_query_note_oom(bounds);
  cached = bounds_query_finish(&scope, status == IXS_ALGEBRA_MATCH);
  if (status == IXS_ALGEBRA_MATCH)
    cached->result.equivalence = *result;
  return status;
}

IXS_STATIC ixs_algebra_status
bounds_equivalence_query_detail(ixs_bounds *bounds, ixs_ctx *ctx, ixs_node *lhs,
                                ixs_node *rhs, ixs_check_result *result) {
  return bounds_equivalence_query_detail_common(bounds, ctx, lhs, rhs, result,
                                                false);
}

IXS_STATIC ixs_algebra_status bounds_equivalence_simplified_query_detail(
    ixs_bounds *bounds, ixs_ctx *ctx, ixs_node *lhs, ixs_node *rhs,
    ixs_check_result *result) {
  return bounds_equivalence_query_detail_common(bounds, ctx, lhs, rhs, result,
                                                true);
}

typedef struct {
  ixs_node *unit_piecewise;
  int unit_piecewise_sign;
  bool has_piecewise;
  bool has_nonunit_scaled_mod;
} equivalence_atom_exact_sides;

static void
equivalence_atom_find_exact_sides(ixs_node *difference,
                                  equivalence_atom_exact_sides *sides) {
  uint32_t i;

  memset(sides, 0, sizeof(*sides));
  if (!difference || difference->tag != IXS_ADD)
    return;
  for (i = 0; i < difference->u.add.nterms; i++) {
    int64_t p;
    int64_t q;
    if (difference->u.add.terms[i].term->tag == IXS_PIECEWISE) {
      ixs_node_get_rat(difference->u.add.terms[i].coeff, &p, &q);
      if (!sides->has_piecewise && q == 1 && (p == -1 || p == 1)) {
        sides->unit_piecewise = difference->u.add.terms[i].term;
        sides->unit_piecewise_sign = p < 0 ? -1 : 1;
      } else {
        sides->unit_piecewise = NULL;
        sides->unit_piecewise_sign = 0;
      }
      sides->has_piecewise = true;
      continue;
    }
    if (difference->u.add.terms[i].term->tag != IXS_MOD)
      continue;
    ixs_node_get_rat(difference->u.add.terms[i].coeff, &p, &q);
    if (q == 1 && p != -1 && p != 0 && p != 1)
      sides->has_nonunit_scaled_mod = true;
  }
}

/* Isolate one unit Piecewise term from a normalized zero-sum ADD. Multiplying
 * every other coefficient by the opposite unit preserves canonical term order,
 * so the peer is rebuilt once without distributing into any arm. */
static bool bounds_isolate_piecewise_relation(ixs_bounds *bounds,
                                              ixs_node *difference,
                                              ixs_node *piecewise,
                                              int piecewise_sign,
                                              ixs_node **other) {
  ixs_arena_mark mark = ixs_arena_save(bounds->scratch);
  ixs_addterm *terms;
  ixs_node *constant;
  int64_t constant_p;
  int64_t constant_q;
  size_t bytes;
  uint32_t count = 0u;
  uint32_t i;
  bool ok = false;

  bytes = (size_t)difference->u.add.nterms * sizeof(*terms);
  if (bytes / sizeof(*terms) != difference->u.add.nterms) {
    bounds->oom = true;
    goto cleanup;
  }
  terms = ixs_arena_alloc(bounds->scratch, bytes, sizeof(void *));
  if (!terms) {
    bounds->oom = true;
    goto cleanup;
  }

  for (i = 0; i < difference->u.add.nterms; i++) {
    ixs_node *term = difference->u.add.terms[i].term;
    int64_t coefficient_p;
    int64_t coefficient_q;

    ixs_node_get_rat(difference->u.add.terms[i].coeff, &coefficient_p,
                     &coefficient_q);
    if (term == piecewise)
      continue;
    if (piecewise_sign > 0 && !ixs_rat_neg(coefficient_p, coefficient_q,
                                           &coefficient_p, &coefficient_q))
      goto cleanup;
    terms[count].term = term;
    terms[count].coeff =
        ixs_node_rat(bounds->ctx, coefficient_p, coefficient_q);
    if (!terms[count].coeff) {
      bounds->oom = true;
      goto cleanup;
    }
    count++;
  }

  ixs_node_get_rat(difference->u.add.coeff, &constant_p, &constant_q);
  if (piecewise_sign > 0 &&
      !ixs_rat_neg(constant_p, constant_q, &constant_p, &constant_q))
    goto cleanup;
  constant = ixs_node_rat(bounds->ctx, constant_p, constant_q);
  if (!constant) {
    bounds->oom = true;
    goto cleanup;
  }
  if (count == 0u)
    *other = constant;
  else if (count == 1u && ixs_node_is_zero(constant) &&
           ixs_node_is_one(terms[0].coeff))
    *other = terms[0].term;
  else
    *other = ixs_node_add(bounds->ctx, constant, count, terms);
  if (!*other) {
    bounds->oom = true;
    goto cleanup;
  }
  ok = !ixs_node_is_sentinel(*other);

cleanup:
  ixs_arena_restore(bounds->scratch, mark);
  return ok;
}

/* Predicate construction normalizes equality to a zero-sum ADD. Recover its
 * exact operands so ordinary equivalence sees the same scaled-Mod or exact
 * root-Piecewise relation as the direct API. Each path is O(T) in direct terms
 * and uses O(T) query scratch. */
static void bounds_equivalence_atom_sides(ixs_bounds *bounds, ixs_node *cmp,
                                          ixs_node **lhs, ixs_node **rhs) {
  struct ixs_node_impl equality;
  ixs_node *relation_lhs;
  ixs_node *relation_rhs;
  int64_t offset;
  equivalence_atom_exact_sides sides;

  *lhs = cmp->u.binary.lhs;
  *rhs = cmp->u.binary.rhs;
  if (!ixs_node_is_zero(*rhs) || bounds_extract_unit_equality(*lhs, lhs, rhs))
    return;
  equivalence_atom_find_exact_sides(*lhs, &sides);
  if (sides.has_piecewise) {
    if (sides.unit_piecewise && bounds_isolate_piecewise_relation(
                                    bounds, *lhs, sides.unit_piecewise,
                                    sides.unit_piecewise_sign, &relation_rhs)) {
      *lhs = sides.unit_piecewise;
      *rhs = relation_rhs;
      return;
    }
    if (!sides.has_nonunit_scaled_mod)
      return;
  }
  if (!sides.has_nonunit_scaled_mod)
    return;

  equality = *(const struct ixs_node_impl *)cmp;
  equality.u.binary.cmp_op = IXS_CMP_EQ;
  if (!bounds_extract_cmp_exact_relation(bounds, &equality, &relation_lhs,
                                         &relation_rhs, &offset))
    return;
  if (offset != 0) {
    ixs_node *constant = ixs_node_int(bounds->ctx, offset);
    bool unrepresentable = false;
    relation_rhs = constant ? simp_try_add(bounds->ctx, relation_rhs, constant,
                                           &unrepresentable)
                            : NULL;
    if (!relation_rhs && !unrepresentable)
      bounds->oom = true;
    if (unrepresentable || !relation_rhs || ixs_node_is_sentinel(relation_rhs))
      return;
  }
  *lhs = relation_lhs;
  *rhs = relation_rhs;
}

static ixs_check_result bounds_check_equivalence_atom(ixs_bounds *bounds,
                                                      ixs_node *cmp) {
  bounds_query_owner_scope owner_scope;
  ixs_algebra_status status;
  ixs_check_result equivalent = IXS_CHECK_UNKNOWN;
  ixs_node *lhs;
  ixs_node *rhs;

  if (!bounds || !bounds->ctx || !cmp || cmp->tag != IXS_CMP ||
      (cmp->u.binary.cmp_op != IXS_CMP_EQ &&
       cmp->u.binary.cmp_op != IXS_CMP_NE) ||
      (ixs_node_is_pred_kind(cmp->u.binary.lhs) &&
       cmp->u.binary.lhs->tag != IXS_INT) ||
      (ixs_node_is_pred_kind(cmp->u.binary.rhs) &&
       cmp->u.binary.rhs->tag != IXS_INT))
    return IXS_CHECK_UNKNOWN;

  bounds_equivalence_atom_sides(bounds, cmp, &lhs, &rhs);

  bounds_query_owner_scope_begin(bounds, &owner_scope);
  status = bounds_equivalence_query_detail(bounds, bounds->ctx, lhs, rhs,
                                           &equivalent);
  bounds_query_owner_scope_end(bounds, &owner_scope);

  if (status == IXS_ALGEBRA_LIMITED && bounds->query_state)
    bounds_query_note_limit(bounds);
  else if (status == IXS_ALGEBRA_INVALID && bounds->query_state)
    bounds_query_note_invalid(bounds);
  else if (status == IXS_ALGEBRA_OOM)
    bounds->oom = true;
  if (status != IXS_ALGEBRA_MATCH)
    return IXS_CHECK_UNKNOWN;
  return cmp->u.binary.cmp_op == IXS_CMP_EQ ? equivalent
                                            : bounds_predicate_not(equivalent);
}

IXS_STATIC ixs_check_result ixs_bounds_check_query(ixs_bounds *bounds,
                                                   ixs_node *cmp) {
  ixs_check_result result;
  bool query_held = false;

  if (!ixs_bounds_query_hold_begin(bounds, cmp, &query_held))
    return IXS_CHECK_UNKNOWN;
  result = ixs_bounds_check(bounds, cmp);
  if (result == IXS_CHECK_UNKNOWN && cmp && cmp->tag == IXS_CMP &&
      ixs_node_is_zero(cmp->u.binary.rhs) &&
      (cmp->u.binary.cmp_op == IXS_CMP_EQ ||
       cmp->u.binary.cmp_op == IXS_CMP_NE))
    result = bounds_check_equivalence_atom(bounds, cmp);
  if (query_held)
    ixs_bounds_query_hold_end(bounds);
  return result;
}
