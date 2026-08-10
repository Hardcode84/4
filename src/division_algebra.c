/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "division_algebra.h"

#include "additive_row.h"
#include "bounds_query.h"
#include "query_walk.h"
#include "simplify.h"
#include <string.h>

typedef struct {
  ixs_ctx *ctx;
  ixs_bounds *bounds;
  ixs_algebra_status status;
  ixs_bounds_transport_snapshot transport;
} da_query;

typedef struct {
  ixs_node *numerator, *denominator;
} da_certificate;

static bool da_stopped(const da_query *query) {
  return query->status >= IXS_ALGEBRA_LIMITED;
}

static bool da_note_status(da_query *query, ixs_algebra_status status) {
  if (status != IXS_ALGEBRA_MATCH && status > query->status)
    query->status = status;
  return status == IXS_ALGEBRA_MATCH;
}

static void da_capture_transport(da_query *query) {
  ixs_bounds_transport_status status =
      ixs_bounds_query_transport_since(query->bounds, query->transport);
  /* Both enum tails encode LIMITED < OOM < INVALID. */
  if (status != IXS_BOUNDS_TRANSPORT_CLEAN)
    da_note_status(query, (ixs_algebra_status)(status + 2u));
}

typedef enum { DA_ADD, DA_MUL, DA_DIV } da_op;

static ixs_node *da_node(da_query *query, ixs_node *node,
                         bool unrepresentable) {
  if (unrepresentable) {
    da_note_status(query, IXS_ALGEBRA_UNREPRESENTABLE);
  } else if (!node)
    da_note_status(query, IXS_ALGEBRA_OOM);
  else if (ixs_node_is_sentinel(node))
    da_note_status(query, IXS_ALGEBRA_INVALID);
  return da_stopped(query) ? NULL : node;
}

static ixs_node *da_build(da_query *query, da_op op, ixs_node *lhs,
                          ixs_node *rhs) {
  bool unrepresentable = false;
  ixs_node *result =
      op == DA_ADD   ? simp_try_add(query->ctx, lhs, rhs, &unrepresentable)
      : op == DA_MUL ? simp_try_mul(query->ctx, lhs, rhs, &unrepresentable)
                     : simp_try_div(query->ctx, lhs, rhs, &unrepresentable);
  return da_node(query, result, unrepresentable);
}

static ixs_node *da_neg(da_query *query, ixs_node *value) {
  ixs_node *minus_one = da_node(query, ixs_node_int(query->ctx, -1), false);
  return minus_one ? da_build(query, DA_MUL, minus_one, value) : NULL;
}

static ixs_node *da_sub(da_query *query, ixs_node *lhs, ixs_node *rhs) {
  ixs_node *negative = da_neg(query, rhs);
  return negative ? da_build(query, DA_ADD, lhs, negative) : NULL;
}

static bool da_property(da_query *query, ixs_node *node, bool integer) {
  ixs_check_result result =
      integer ? ixs_bounds_check_integer_valued(query->bounds, node)
              : ixs_bounds_check_defined(query->bounds, node);
  da_capture_transport(query);
  return result == IXS_CHECK_TRUE && !da_stopped(query);
}

static void da_sign_normalize(ixs_node **node, ixs_cmp_op *op);

static ixs_node *da_cmp_canonical(da_query *query, ixs_node *node,
                                  ixs_cmp_op op) {
  da_sign_normalize(&node, &op);
  return da_node(query, simp_cmp(query->ctx, node, op, query->ctx->node_zero),
                 false);
}

static ixs_check_result da_cmp_zero(da_query *query, ixs_node *node,
                                    ixs_cmp_op op) {
  ixs_node *cmp = da_cmp_canonical(query, node, op);
  ixs_check_result result =
      cmp ? ixs_bounds_check(query->bounds, cmp) : IXS_CHECK_UNKNOWN;
  da_capture_transport(query);
  return da_stopped(query) ? IXS_CHECK_UNKNOWN : result;
}

static void da_sign_normalize(ixs_node **node, ixs_cmp_op *op) {
  if ((*node)->tag == IXS_MUL && (*node)->u.mul.nfactors == 1u &&
      (*node)->u.mul.factors[0].exp == 1) {
    int64_t p, q;
    ixs_node_get_rat((*node)->u.mul.coeff, &p, &q);
    /* GT/GE/LT/LE are 0/1/2/3, so xor 2 flips the inequality direction. */
    if (p < 0 && *op <= IXS_CMP_LE)
      *op = (ixs_cmp_op)((unsigned)*op ^ 2u);
    *node = (*node)->u.mul.factors[0].base;
  }
}

static bool da_guard_leaf(ixs_node *node, ixs_node *value, ixs_cmp_op op) {
  ixs_node *lhs;
  ixs_cmp_op actual;
  if (node->tag != IXS_CMP || !ixs_node_is_zero(node->u.binary.rhs))
    return false;
  lhs = node->u.binary.lhs;
  actual = node->u.binary.cmp_op;
  da_sign_normalize(&lhs, &actual);
  da_sign_normalize(&value, &op);
  return lhs == value && actual == op;
}

static bool da_guard_pair(ixs_node *node, ixs_node *numerator,
                          ixs_node *denominator, bool positive) {
  ixs_cmp_op n_op = positive ? IXS_CMP_GE : IXS_CMP_LE;
  ixs_cmp_op d_op = positive ? IXS_CMP_GT : IXS_CMP_LT;
  if (node->tag != IXS_AND || node->u.assoc.nargs != 2u)
    return false;
  return (da_guard_leaf(node->u.assoc.args[0], numerator, n_op) &&
          da_guard_leaf(node->u.assoc.args[1], denominator, d_op)) ||
         (da_guard_leaf(node->u.assoc.args[1], numerator, n_op) &&
          da_guard_leaf(node->u.assoc.args[0], denominator, d_op));
}

/* Accept only the exact two-clause sign protocol, or the clause/atom left
 * after a proved denominator sign. Structural numerator comparisons preserve
 * the strict boundary and reject extra predicates without solver re-entry. */
static bool da_guard_matches(da_query *query, ixs_node *actual,
                             ixs_node *numerator, ixs_node *denominator) {
  /* The total Piecewise already proves its first condition total. */
  if (actual->tag == IXS_OR && actual->u.assoc.nargs == 2u &&
      ((da_guard_pair(actual->u.assoc.args[0], numerator, denominator, true) &&
        da_guard_pair(actual->u.assoc.args[1], numerator, denominator,
                      false)) ||
       (da_guard_pair(actual->u.assoc.args[1], numerator, denominator, true) &&
        da_guard_pair(actual->u.assoc.args[0], numerator, denominator, false))))
    return true;
  if (da_cmp_zero(query, denominator, IXS_CMP_GT) == IXS_CHECK_TRUE)
    return da_guard_leaf(actual, numerator, IXS_CMP_GE) ||
           da_guard_pair(actual, numerator, denominator, true);
  if (da_cmp_zero(query, denominator, IXS_CMP_LT) == IXS_CHECK_TRUE)
    return da_guard_leaf(actual, numerator, IXS_CMP_LE) ||
           da_guard_pair(actual, numerator, denominator, false);
  return false;
}

static ixs_node *da_piecewise_argument(da_query *query, ixs_node *round) {
  ixs_node *floor_argument, *floor_residual;
  ixs_node *ceil_argument, *ceil_residual;
  if (round->u.pw.ncases != 2u ||
      !ixs_node_is_known_true(round->u.pw.cases[1].cond) ||
      !da_note_status(query, ixs_additive_row_split_round(
                                 query->ctx, round->u.pw.cases[0].value, false,
                                 &floor_argument, &floor_residual)) ||
      !da_note_status(query, ixs_additive_row_split_round(
                                 query->ctx, round->u.pw.cases[1].value, true,
                                 &ceil_argument, &ceil_residual)) ||
      floor_argument != ceil_argument || floor_residual != ceil_residual ||
      !da_property(query, floor_residual, false) ||
      !da_property(query, floor_residual, true))
    return NULL;
  return da_build(query, DA_ADD, floor_argument, floor_residual);
}

static bool da_round_parts(da_query *query, ixs_node *round,
                           bool allow_piecewise, da_certificate *certificate) {
  ixs_node *argument = NULL;
  ixs_quotient_parts_status parts_status;
  if (round->tag == IXS_TRUNC) {
    argument = round->u.unary.arg;
  } else if (round->tag == IXS_FLOOR || round->tag == IXS_CEIL) {
    argument = round->u.unary.arg;
    if (da_cmp_zero(query, argument,
                    round->tag == IXS_FLOOR ? IXS_CMP_GE : IXS_CMP_LE) !=
        IXS_CHECK_TRUE)
      return false;
  } else if (allow_piecewise && round->tag == IXS_PIECEWISE) {
    argument = da_piecewise_argument(query, round);
  } else {
    return false;
  }
  if (!argument)
    return false;
  parts_status = simp_exact_quotient_parts(
      query->ctx, argument, &certificate->numerator, &certificate->denominator);
  if (parts_status != IXS_QUOTIENT_PARTS_MATCH) {
    da_note_status(query, parts_status == IXS_QUOTIENT_PARTS_OOM
                              ? IXS_ALGEBRA_OOM
                          : parts_status == IXS_QUOTIENT_PARTS_UNREPRESENTABLE
                              ? IXS_ALGEBRA_UNREPRESENTABLE
                              : IXS_ALGEBRA_NO_MATCH);
    return false;
  }
  if (!da_property(query, round, false) ||
      !da_property(query, certificate->numerator, true) ||
      !da_property(query, certificate->denominator, true))
    return false;
  /* A total rounding node transports the shared quotient argument's complete
   * domain, including numerator definedness and a nonzero denominator. */
  if (round->tag == IXS_PIECEWISE) {
    ixs_node *actual = round->u.pw.cases[0].cond;
    if (!da_guard_matches(query, actual, certificate->numerator,
                          certificate->denominator))
      return false;
  }
  return true;
}

static ixs_node *da_mod_branch(da_query *query, ixs_node *numerator,
                               ixs_node *modulus, bool negative) {
  if (negative)
    numerator = da_neg(query, numerator);
  numerator =
      numerator
          ? da_node(query, simp_mod(query->ctx, numerator, modulus), false)
          : NULL;
  return negative && numerator ? da_neg(query, numerator) : numerator;
}

static ixs_node *da_signed_remainder(da_query *query,
                                     da_certificate *certificate) {
  ixs_node *numerator = certificate->numerator;
  ixs_node *denominator = certificate->denominator;
  ixs_node *magnitude = denominator;
  ixs_node *negative_denominator = NULL;
  ixs_node *positive, *negative, *guard;
  ixs_check_result denominator_positive =
      da_cmp_zero(query, denominator, IXS_CMP_GT);
  ixs_check_result numerator_sign;

  if (denominator_positive != IXS_CHECK_TRUE) {
    negative_denominator = da_neg(query, denominator);
    if (!negative_denominator)
      return NULL;
    magnitude =
        denominator_positive == IXS_CHECK_FALSE
            ? negative_denominator
            : da_node(query,
                      simp_max(query->ctx, denominator, negative_denominator),
                      false);
  }
  numerator_sign = da_cmp_zero(query, numerator, IXS_CMP_GE);
  if (numerator_sign != IXS_CHECK_UNKNOWN)
    return da_mod_branch(query, numerator, magnitude,
                         numerator_sign == IXS_CHECK_FALSE);
  numerator_sign = da_cmp_zero(query, numerator, IXS_CMP_LE);
  if (numerator_sign == IXS_CHECK_TRUE)
    return da_mod_branch(query, numerator, magnitude, true);
  negative = da_stopped(query)
                 ? NULL
                 : da_mod_branch(query, numerator, magnitude, true);
  positive =
      negative ? da_mod_branch(query, numerator, magnitude, false) : NULL;
  guard = positive ? da_cmp_canonical(query, numerator, IXS_CMP_GE) : NULL;
  if (guard) {
    ixs_node *values[2] = {positive, negative};
    ixs_node *conditions[2] = {guard, query->ctx->node_true};
    guard = da_node(query, simp_pw(query->ctx, 2u, values, conditions), false);
  }
  /* Certificate operands are total integers and magnitude is positive. Mod,
   * negation, and the exhaustive sign Piecewise preserve that contract. */
  return guard;
}

static ixs_node *da_replacement(da_query *query, ixs_node *round,
                                bool allow_piecewise) {
  da_certificate certificate;
  ixs_node *remainder;
  if (!da_round_parts(query, round, allow_piecewise, &certificate))
    return NULL;
  remainder = da_signed_remainder(query, &certificate);
  remainder =
      remainder ? da_sub(query, certificate.numerator, remainder) : NULL;
  /* The total source round already proves this exact quotient's domain. */
  return remainder ? da_build(query, DA_DIV, remainder, certificate.denominator)
                   : NULL;
}

static bool da_candidate(ixs_node *node, ixs_division_projection_mode mode) {
  return (node->tag == IXS_PIECEWISE &&
          mode != IXS_DIVISION_PROJECT_DIRECT_ONLY) ||
         ((node->tag == IXS_FLOOR || node->tag == IXS_CEIL ||
           node->tag == IXS_TRUNC) &&
          mode != IXS_DIVISION_PROJECT_PIECEWISE_REDUCING);
}

typedef struct {
  ixs_node **targets, **replacements;
  size_t count, capacity, nodes;
} da_walk;

static bool da_push_substitution(da_query *query, da_walk *walk,
                                 ixs_node *target, ixs_node *replacement) {
  if (walk->count == walk->capacity) {
    size_t next = walk->capacity ? walk->capacity * 2u : 64u;
    ixs_node **storage;
    if (next <= walk->capacity || next > SIZE_MAX / (2u * sizeof(*storage)))
      goto oom;
    storage = ixs_arena_alloc(&query->ctx->scratch,
                              next * 2u * sizeof(*storage), sizeof(void *));
    if (!storage)
      goto oom;
    if (walk->count) {
      memcpy(storage, walk->targets, walk->count * sizeof(*storage));
      memcpy(storage + next, walk->replacements,
             walk->count * sizeof(*storage));
    }
    walk->targets = storage;
    walk->replacements = storage + next;
    walk->capacity = next;
  }
  walk->targets[walk->count] = target;
  walk->replacements[walk->count++] = replacement;
  return true;
oom:
  da_note_status(query, IXS_ALGEBRA_OOM);
  return false;
}

/* The shared pointer set makes projection and cost measurement expected
 * O(N + E + C). A matched node hides descendants reached only through it. */
static bool da_walk_roots(da_query *query, ixs_node *lhs, ixs_node *rhs,
                          ixs_division_projection_mode mode, bool project,
                          da_walk *walk) {
  query_node_set visited;
  ixs_node **stack = NULL;
  size_t count = 0, capacity = 0;
  memset(&visited, 0, sizeof(visited));
  memset(walk, 0, sizeof(*walk));
  if (!query_node_stack_push(&query->ctx->scratch, &stack, &count, &capacity,
                             rhs) ||
      !query_node_stack_push(&query->ctx->scratch, &stack, &count, &capacity,
                             lhs))
    goto oom;
  while (count > 0u) {
    ixs_node *node = stack[--count];
    bool inserted;
    uint32_t children, i;
    if (project && !ixs_node_contains_rounding(node))
      continue;
    if (!query_node_set_insert(&query->ctx->scratch, &visited, node, &inserted))
      goto oom;
    if (!inserted)
      continue;
    if (walk->nodes != SIZE_MAX)
      walk->nodes++;
    if (project && da_candidate(node, mode)) {
      ixs_node *replacement =
          da_replacement(query, node, mode != IXS_DIVISION_PROJECT_DIRECT_ONLY);
      if (da_stopped(query) ||
          (replacement &&
           !da_push_substitution(query, walk, node, replacement)))
        return false;
      if (replacement)
        continue;
    }
    if (project && node->tag == IXS_PIECEWISE)
      continue;
    children = ixs_node_nchildren(node);
    for (i = children; i > 0u; i--)
      if (!query_node_stack_push(&query->ctx->scratch, &stack, &count,
                                 &capacity, ixs_node_child(node, i - 1u)))
        goto oom;
  }
  return true;
oom:
  da_note_status(query, IXS_ALGEBRA_OOM);
  return false;
}

static ixs_node *da_reduce_projection(da_query *query, ixs_node *root,
                                      ixs_node *projected) {
  da_walk original, candidate;
  bool limited = false;
  projected = simp_simplify_bounds_status(query->ctx, projected, query->bounds,
                                          &limited);
  da_capture_transport(query);
  if (!da_stopped(query)) {
    if (limited)
      da_note_status(query, IXS_ALGEBRA_LIMITED);
    else
      projected = da_node(query, projected, false);
  }
  if (!projected || da_stopped(query) ||
      !da_walk_roots(query, root, query->ctx->node_zero,
                     IXS_DIVISION_PROJECT_PIECEWISE_REDUCING, false,
                     &original) ||
      !da_walk_roots(query, projected, query->ctx->node_zero,
                     IXS_DIVISION_PROJECT_PIECEWISE_REDUCING, false,
                     &candidate))
    return NULL;
  /* Construction adds no rounding operator and removes the selected outer
   * round; strict node shrink is the independent non-growth admission rule. */
  return candidate.nodes < original.nodes ? projected : root;
}

IXS_STATIC ixs_division_projection_result ixs_division_algebra_project(
    ixs_ctx *ctx, ixs_bounds *bounds, ixs_node *source_lhs, ixs_node *root_lhs,
    ixs_node *source_rhs, ixs_node *root_rhs,
    ixs_division_projection_mode mode) {
  ixs_division_projection_result result = {IXS_ALGEBRA_NO_MATCH, root_lhs,
                                           root_rhs};
  da_query query = {.ctx = ctx, .bounds = bounds};
  ixs_arena_mark mark;
  da_walk projection;
  bool unrepresentable;
  if (!ctx || !bounds || !source_lhs || !root_lhs || !source_rhs || !root_rhs ||
      mode > IXS_DIVISION_PROJECT_PIECEWISE_REDUCING)
    result.status = IXS_ALGEBRA_INVALID;
  if (result.status != IXS_ALGEBRA_NO_MATCH ||
      (!ixs_node_contains_rounding(root_lhs) &&
       !ixs_node_contains_rounding(root_rhs)))
    return result;
  query.transport = ixs_bounds_query_transport_snapshot(bounds);
  if (!da_property(&query, source_lhs, false) ||
      !da_property(&query, source_rhs, false)) {
    result.status = query.status;
    return result;
  }
  mark = ixs_arena_save(&ctx->scratch);
  if (!da_walk_roots(&query, root_lhs, root_rhs, mode, true, &projection) ||
      projection.count == 0u)
    goto cleanup;
  if (projection.count > UINT32_MAX) {
    da_note_status(&query, IXS_ALGEBRA_OOM);
    goto cleanup;
  }
  result.lhs = simp_subs_multi_outermost(
      ctx, root_lhs, (uint32_t)projection.count, projection.targets,
      projection.replacements, &unrepresentable);
  result.lhs = da_node(&query, result.lhs, unrepresentable);
  if (result.lhs && mode == IXS_DIVISION_PROJECT_PIECEWISE_REDUCING) {
    result.lhs = da_reduce_projection(&query, root_lhs, result.lhs);
    result.rhs = root_rhs;
  } else {
    result.rhs = result.lhs ? simp_subs_multi_outermost(
                                  ctx, root_rhs, (uint32_t)projection.count,
                                  projection.targets, projection.replacements,
                                  &unrepresentable)
                            : NULL;
    result.rhs = da_node(&query, result.rhs, unrepresentable);
  }
  if (result.lhs && result.rhs &&
      (mode != IXS_DIVISION_PROJECT_PIECEWISE_REDUCING ||
       result.lhs != root_lhs))
    result.status = IXS_ALGEBRA_MATCH;

cleanup:
  if (result.status != IXS_ALGEBRA_MATCH) {
    result.status = query.status;
    result.lhs = root_lhs;
    result.rhs = root_rhs;
  }
  ixs_arena_restore(&ctx->scratch, mark);
  return result;
}

static bool da_range_for_round(da_query *query, ixs_node *expr, ixs_node *round,
                               ixs_interval *range) {
  da_certificate certificate;
  ixs_node *product, *raw_remainder, *signed_remainder, *shift;
  ixs_interval remainder_range;
  int64_t shift_p, shift_q;
  if (!da_round_parts(query, round, true, &certificate))
    return false;
  product = da_build(query, DA_MUL, certificate.denominator, round);
  raw_remainder =
      product ? da_sub(query, certificate.numerator, product) : NULL;
  shift = raw_remainder ? da_sub(query, expr, raw_remainder) : NULL;
  if (!shift || !ixs_node_is_const(shift))
    return false;
  ixs_node_get_rat(shift, &shift_p, &shift_q);
  if (shift_q != 1)
    return false;
  signed_remainder = da_signed_remainder(query, &certificate);
  if (!signed_remainder)
    return false;
  remainder_range = ixs_bounds_get(query->bounds, signed_remainder);
  da_capture_transport(query);
  *range = iv_add(remainder_range, ixs_interval_exact(shift_p, 1));
  return range->valid && !da_stopped(query);
}

IXS_STATIC ixs_division_range_result
ixs_division_algebra_range(ixs_ctx *ctx, ixs_bounds *bounds, ixs_node *source,
                           ixs_node *root, bool source_defined) {
  ixs_division_range_result result = {IXS_ALGEBRA_NO_MATCH, {0}};
  da_query query = {.ctx = ctx, .bounds = bounds};
  ixs_node *round = NULL;
  uint32_t i;
  if (!ctx || !bounds || !source || !root) {
    result.status = IXS_ALGEBRA_INVALID;
    return result;
  }
  if (root->tag != IXS_ADD || !ixs_node_contains_rounding(root))
    return result;
  query.transport = ixs_bounds_query_transport_snapshot(bounds);
  if (!source_defined && !da_property(&query, source, false)) {
    result.status = query.status;
    return result;
  }
  for (i = 0; i < root->u.add.nterms; i++) {
    ixs_node *term = root->u.add.terms[i].term;
    uint32_t factor = 0;
    do {
      ixs_node *candidate =
          factor == 0u ? term : term->u.mul.factors[factor - 1u].base;
      bool eligible =
          (factor == 0u || term->u.mul.factors[factor - 1u].exp == 1) &&
          (candidate->tag == IXS_TRUNC || candidate->tag == IXS_PIECEWISE);
      if (eligible && round && round != candidate)
        return result;
      if (eligible)
        round = candidate;
      factor++;
    } while (term->tag == IXS_MUL && factor <= term->u.mul.nfactors);
  }
  if (round && da_range_for_round(&query, root, round, &result.range))
    result.status = IXS_ALGEBRA_MATCH;
  else
    result.status = query.status;
  return result;
}
