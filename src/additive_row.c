/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "additive_row.h"

#include "simplify.h"
#include <string.h>

/* Canonical row recognition is allocation-free and O(1). */
IXS_STATIC bool ixs_additive_row_unit_value(ixs_node *expr, ixs_node **term,
                                            int64_t *value) {
  int64_t constant, cq, coefficient, tq;
  if (expr->tag != IXS_ADD || expr->u.add.nterms != 1)
    return false;
  ixs_node_get_rat(expr->u.add.coeff, &constant, &cq);
  ixs_node_get_rat(expr->u.add.terms[0].coeff, &coefficient, &tq);
  if (cq != 1 || tq != 1 || (coefficient != 1 && coefficient != -1) ||
      (coefficient == 1 && constant == INT64_MIN))
    return false;
  *term = expr->u.add.terms[0].term;
  *value = coefficient == 1 ? -constant : constant;
  return true;
}

IXS_STATIC bool ixs_additive_row_unit_pair(ixs_node *expr, ixs_node **positive,
                                           ixs_node **negative,
                                           int64_t *constant) {
  ixs_node *pos = NULL;
  ixs_node *neg = NULL;
  uint32_t i;
  int64_t p, q, c;
  if (expr->tag != IXS_ADD || expr->u.add.nterms != 2)
    return false;
  ixs_node_get_rat(expr->u.add.coeff, &c, &q);
  if (q != 1)
    return false;
  for (i = 0; i < 2; i++) {
    const ixs_addterm *term = &expr->u.add.terms[i];
    ixs_node_get_rat(term->coeff, &p, &q);
    if (q != 1 || (p != 1 && p != -1))
      return false;
    *(p == 1 ? &pos : &neg) = term->term;
  }
  if (!pos || !neg || pos == neg)
    return false;
  *positive = pos;
  *negative = neg;
  *constant = c;
  return true;
}

static ixs_node *additive_row_build(ixs_ctx *ctx, ixs_node *constant,
                                    const ixs_addterm *terms, uint32_t nterms) {
  if (nterms == 0)
    return constant;
  if (nterms == 1 && ixs_node_is_zero(constant))
    return ixs_node_is_one(terms[0].coeff)
               ? terms[0].term
               : simp_mul(ctx, terms[0].coeff, terms[0].term);
  return ixs_node_add(ctx, constant, nterms, terms);
}

/* Transform-cache hits are expected O(1); a miss rebuilds T immediate terms. */
IXS_STATIC ixs_algebra_status ixs_additive_row_without_constant(
    ixs_ctx *ctx, ixs_node *expr, ixs_node **result) {
  ixs_node *node;
  if (expr->tag != IXS_ADD || expr->u.add.nterms == 0)
    return IXS_ALGEBRA_NO_MATCH;
  node = ixs_node_transform_cache_lookup(ctx, expr,
                                         IXS_NODE_TRANSFORM_ADD_WITHOUT_CONST);
  if (!node) {
    node = additive_row_build(ctx, ctx->node_zero, expr->u.add.terms,
                              expr->u.add.nterms);
    if (!node)
      return IXS_ALGEBRA_OOM;
    if (ixs_node_is_sentinel(node))
      return IXS_ALGEBRA_NO_MATCH;
    ixs_node_transform_cache_store(ctx, expr,
                                   IXS_NODE_TRANSFORM_ADD_WITHOUT_CONST, node);
  }
  *result = node;
  return IXS_ALGEBRA_MATCH;
}

/* Try-builds make unrepresentable arithmetic a diagnostic-free shape miss. */
static ixs_algebra_status additive_row_difference(ixs_ctx *ctx, ixs_node *lhs,
                                                  ixs_node *rhs,
                                                  ixs_node **difference) {
  ixs_node *negative;
  bool unrepresentable;
  if (ixs_node_is_zero(rhs)) {
    *difference = lhs;
    return IXS_ALGEBRA_MATCH;
  }
  negative = ixs_node_int(ctx, -1);
  if (!negative)
    return IXS_ALGEBRA_OOM;
  negative = simp_try_mul(ctx, negative, rhs, &unrepresentable);
  if (!negative)
    return unrepresentable ? IXS_ALGEBRA_UNREPRESENTABLE : IXS_ALGEBRA_OOM;
  *difference = simp_try_add(ctx, lhs, negative, &unrepresentable);
  if (!*difference)
    return unrepresentable ? IXS_ALGEBRA_UNREPRESENTABLE : IXS_ALGEBRA_OOM;
  return ixs_node_is_sentinel(*difference) ? IXS_ALGEBRA_INVALID
                                           : IXS_ALGEBRA_MATCH;
}

IXS_STATIC ixs_algebra_status
ixs_additive_row_split_round(ixs_ctx *ctx, ixs_node *value, bool ceiling,
                             ixs_node **argument, ixs_node **residual) {
  ixs_node *round = NULL;
  ixs_node *candidate_residual;
  ixs_addterm *terms;
  ixs_arena_mark mark;
  ixs_tag tag = ceiling ? IXS_CEIL : IXS_FLOOR;
  bool unrepresentable = false;
  uint32_t i, round_index = UINT32_MAX;
  if (!ctx || !value || !argument || !residual)
    return IXS_ALGEBRA_INVALID;
  if (value->tag == tag) {
    *argument = value->u.unary.arg;
    *residual = ctx->node_zero;
    return IXS_ALGEBRA_MATCH;
  }
  if (value->tag != IXS_ADD)
    return IXS_ALGEBRA_NO_MATCH;
  for (i = 0; i < value->u.add.nterms; i++) {
    int64_t p, q;
    ixs_node *term = value->u.add.terms[i].term;
    ixs_node_get_rat(value->u.add.terms[i].coeff, &p, &q);
    if (term->tag != tag || p != 1 || q != 1)
      continue;
    if (round)
      return IXS_ALGEBRA_NO_MATCH;
    round = term;
    round_index = i;
  }
  if (!round)
    return IXS_ALGEBRA_NO_MATCH;
  mark = ixs_arena_save(&ctx->scratch);
  terms = ixs_arena_alloc(&ctx->scratch,
                          (value->u.add.nterms - 1u) * sizeof(*terms),
                          sizeof(void *));
  if (!terms && value->u.add.nterms != 1u)
    goto oom;
  /* Removing one known term preserves the canonical order of both slices. */
  if (round_index)
    memcpy(terms, value->u.add.terms, round_index * sizeof(*terms));
  if (round_index + 1u < value->u.add.nterms)
    memcpy(terms + round_index, value->u.add.terms + round_index + 1u,
           (value->u.add.nterms - round_index - 1u) * sizeof(*terms));
  candidate_residual =
      value->u.add.nterms == 2u && ixs_node_is_zero(value->u.add.coeff) &&
              !ixs_node_is_one(terms[0].coeff)
          ? simp_try_mul(ctx, terms[0].coeff, terms[0].term, &unrepresentable)
          : additive_row_build(ctx, value->u.add.coeff, terms,
                               value->u.add.nterms - 1u);
  ixs_arena_restore(&ctx->scratch, mark);
  if (!candidate_residual)
    return unrepresentable ? IXS_ALGEBRA_UNREPRESENTABLE : IXS_ALGEBRA_OOM;
  if (ixs_node_is_sentinel(candidate_residual))
    return IXS_ALGEBRA_INVALID;
  *argument = round->u.unary.arg;
  *residual = candidate_residual;
  return IXS_ALGEBRA_MATCH;
oom:
  ixs_arena_restore(&ctx->scratch, mark);
  return IXS_ALGEBRA_OOM;
}

/* The source ADD is sorted and has no zero coefficients. Stable sign
 * partitioning preserves canonical order, so each side is hash-consed once.
 * Partitioning is O(T) time and O(T) scratch; constructing lhs-rhs first
 * inherits the simplifier's O(T^2) worst case. No expression DAG is walked. */
IXS_STATIC ixs_algebra_status ixs_additive_row_relation(
    ixs_ctx *ctx, ixs_arena *scratch, ixs_node *lhs, ixs_node *rhs,
    ixs_node **positive, ixs_node **negative, int64_t *offset) {
  ixs_arena_mark mark;
  ixs_node *difference, *positive_result, *negative_result;
  ixs_addterm *terms, *positive_terms, *negative_terms;
  size_t bytes;
  uint32_t positive_count = 0, negative_count = 0, i;
  int64_t constant, q;
  ixs_algebra_status status;
  status = additive_row_difference(ctx, lhs, rhs, &difference);
  if (status != IXS_ALGEBRA_MATCH || difference->tag != IXS_ADD ||
      difference->u.add.nterms < 2)
    return status == IXS_ALGEBRA_MATCH ? IXS_ALGEBRA_NO_MATCH : status;
  ixs_node_get_rat(difference->u.add.coeff, &constant, &q);
  if (q != 1)
    return IXS_ALGEBRA_NO_MATCH;
  mark = ixs_arena_save(scratch);
  bytes = (size_t)difference->u.add.nterms * sizeof(*terms);
  if (bytes / sizeof(*terms) != difference->u.add.nterms ||
      bytes > SIZE_MAX / 2)
    goto oom;
  terms = ixs_arena_alloc(scratch, bytes * 2, sizeof(void *));
  if (!terms)
    goto oom;
  positive_terms = terms;
  negative_terms = terms + difference->u.add.nterms;
  for (i = 0; i < difference->u.add.nterms; i++) {
    ixs_node *coefficient = difference->u.add.terms[i].coeff;
    int64_t p;
    ixs_node_get_rat(coefficient, &p, &q);
    if (p > 0) {
      positive_terms[positive_count++] = difference->u.add.terms[i];
    } else {
      /* Canonical ADD coefficients are nonzero, so this arm is negative. */
      if (!ixs_rat_neg(p, q, &p, &q))
        goto no_match;
      coefficient = ixs_node_rat(ctx, p, q);
      if (!coefficient)
        goto oom;
      negative_terms[negative_count].term = difference->u.add.terms[i].term;
      negative_terms[negative_count++].coeff = coefficient;
    }
  }
  if (positive_count == 0 || negative_count == 0)
    goto no_match;
  positive_result =
      additive_row_build(ctx, ctx->node_zero, positive_terms, positive_count);
  negative_result =
      additive_row_build(ctx, ctx->node_zero, negative_terms, negative_count);
  if (!positive_result || !negative_result)
    goto oom;
  /* A one-term side may become an unrepresentable simplifier sentinel. */
  if (ixs_node_is_sentinel(positive_result) ||
      ixs_node_is_sentinel(negative_result))
    goto no_match;
  if (constant != INT64_MIN) {
    *offset = -constant;
  } else {
    /* Reversing the relation represents -constant without overflowing. */
    difference = positive_result;
    positive_result = negative_result;
    negative_result = difference;
    *offset = INT64_MIN;
  }
  *positive = positive_result;
  *negative = negative_result;
  status = IXS_ALGEBRA_MATCH;
  goto cleanup;
oom:
  status = IXS_ALGEBRA_OOM;
  goto cleanup;
no_match:
  status = IXS_ALGEBRA_NO_MATCH;
cleanup:
  ixs_arena_restore(scratch, mark);
  return status;
}
