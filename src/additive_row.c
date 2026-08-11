/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "additive_row.h"

#include "simplify.h"
#include <assert.h>
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

IXS_STATIC void ixs_euclidean_row_borrow(ixs_ctx *ctx, ixs_node *expr,
                                         ixs_euclidean_row *row) {
  assert(ctx && expr && row);
  if (expr->tag == IXS_ADD) {
    row->terms = expr->u.add.terms;
    row->nterms = expr->u.add.nterms;
    return;
  }
  row->singleton.term = expr;
  row->singleton.coeff = ctx->node_one;
  row->terms = &row->singleton;
  row->nterms = 1u;
}

IXS_STATIC void ixs_euclidean_row_borrow_terms(const ixs_addterm *terms,
                                               uint32_t nterms,
                                               ixs_euclidean_row *row) {
  assert(row && (terms || nterms == 0u));
  row->terms = terms;
  row->nterms = nterms;
}

static ixs_node *euclidean_build_product(ixs_ctx *ctx, ixs_node *coefficient,
                                         uint32_t nfactors,
                                         const ixs_mulfactor *factors) {
  if (nfactors == 0u)
    return coefficient;
  if (nfactors == 1u && factors[0].exp == 1 && ixs_node_is_one(coefficient))
    return factors[0].base;
  return ixs_node_mul(ctx, coefficient, nfactors, factors);
}

/* Partition one canonical product in two linear passes. Reusing the sorted
 * factor array avoids repeated multiplication and supports every representable
 * exponent magnitude. */
static ixs_algebra_status euclidean_product_parts(ixs_ctx *ctx, ixs_node *expr,
                                                  ixs_node **numerator,
                                                  ixs_node **denominator) {
  ixs_arena_mark mark;
  ixs_mulfactor *factors;
  ixs_mulfactor *positive;
  ixs_mulfactor *negative;
  ixs_node *num_coefficient;
  ixs_node *denom_coefficient;
  ixs_node *num;
  ixs_node *denom;
  int64_t p, q;
  uint32_t npositive = 0;
  uint32_t nnegative = 0;
  uint32_t i;

  if (ixs_node_is_const(expr)) {
    ixs_node_get_rat(expr, &p, &q);
    if (q == 1)
      return IXS_ALGEBRA_NO_MATCH;
    num = ixs_node_int(ctx, p);
    denom = ixs_node_int(ctx, q);
    if (!num || !denom)
      return IXS_ALGEBRA_OOM;
    *numerator = num;
    *denominator = denom;
    return IXS_ALGEBRA_MATCH;
  }
  if (expr->tag != IXS_MUL)
    return IXS_ALGEBRA_NO_MATCH;
  ixs_node_get_rat(expr->u.mul.coeff, &p, &q);
  for (i = 0; i < expr->u.mul.nfactors; i++) {
    int32_t exponent = expr->u.mul.factors[i].exp;
    if (exponent == INT32_MIN)
      return IXS_ALGEBRA_NO_MATCH;
    if (exponent > 0)
      npositive++;
    else
      nnegative++;
  }
  if (q == 1 && nnegative == 0)
    return IXS_ALGEBRA_NO_MATCH;

  mark = ixs_arena_save(&ctx->scratch);
  factors = ixs_arena_alloc(
      &ctx->scratch, expr->u.mul.nfactors * sizeof(*factors), sizeof(void *));
  if (!factors) {
    ixs_arena_restore(&ctx->scratch, mark);
    return IXS_ALGEBRA_OOM;
  }
  positive = factors;
  negative = factors + npositive;
  npositive = 0;
  nnegative = 0;
  for (i = 0; i < expr->u.mul.nfactors; i++) {
    ixs_mulfactor factor = expr->u.mul.factors[i];
    if (factor.exp > 0) {
      positive[npositive++] = factor;
    } else {
      factor.exp = -factor.exp;
      negative[nnegative++] = factor;
    }
  }
  num_coefficient = ixs_node_int(ctx, p);
  denom_coefficient = ixs_node_int(ctx, q);
  if (!num_coefficient || !denom_coefficient) {
    ixs_arena_restore(&ctx->scratch, mark);
    return IXS_ALGEBRA_OOM;
  }
  num = euclidean_build_product(ctx, num_coefficient, npositive, positive);
  denom = euclidean_build_product(ctx, denom_coefficient, nnegative, negative);
  ixs_arena_restore(&ctx->scratch, mark);
  if (!num || !denom)
    return IXS_ALGEBRA_OOM;
  *numerator = num;
  *denominator = denom;
  return IXS_ALGEBRA_MATCH;
}

static ixs_algebra_status euclidean_exact_parts(ixs_ctx *ctx, ixs_node *expr,
                                                ixs_node **numerator,
                                                ixs_node **denominator) {
  ixs_node *num;
  ixs_node *denom = NULL;
  ixs_node *constant_numerator;
  uint32_t i;

  if (expr->tag != IXS_ADD)
    return euclidean_product_parts(ctx, expr, numerator, denominator);
  if (expr->u.add.nterms == 0u)
    return IXS_ALGEBRA_NO_MATCH;
  num = ixs_node_int(ctx, 0);
  if (!num)
    return IXS_ALGEBRA_OOM;
  for (i = 0; i < expr->u.add.nterms; i++) {
    ixs_algebra_status status;
    bool unrepresentable = false;
    ixs_node *scaled =
        simp_try_mul(ctx, expr->u.add.terms[i].coeff, expr->u.add.terms[i].term,
                     &unrepresentable);
    ixs_node *term_numerator;
    ixs_node *term_denominator;
    if (unrepresentable)
      return IXS_ALGEBRA_UNREPRESENTABLE;
    if (!scaled)
      return IXS_ALGEBRA_OOM;
    if (ixs_node_is_sentinel(scaled))
      return IXS_ALGEBRA_NO_MATCH;
    status = euclidean_product_parts(ctx, scaled, &term_numerator,
                                     &term_denominator);
    if (status != IXS_ALGEBRA_MATCH)
      return status;
    if (denom && term_denominator != denom)
      return IXS_ALGEBRA_NO_MATCH;
    denom = term_denominator;
    num = simp_try_add(ctx, num, term_numerator, &unrepresentable);
    if (unrepresentable)
      return IXS_ALGEBRA_UNREPRESENTABLE;
    if (!num)
      return IXS_ALGEBRA_OOM;
    if (ixs_node_is_sentinel(num))
      return IXS_ALGEBRA_NO_MATCH;
  }
  if (!denom)
    return IXS_ALGEBRA_NO_MATCH;
  {
    bool unrepresentable = false;
    constant_numerator =
        simp_try_mul(ctx, expr->u.add.coeff, denom, &unrepresentable);
    if (unrepresentable)
      return IXS_ALGEBRA_UNREPRESENTABLE;
  }
  if (!constant_numerator)
    return IXS_ALGEBRA_OOM;
  if (ixs_node_is_sentinel(constant_numerator))
    return IXS_ALGEBRA_NO_MATCH;
  {
    bool unrepresentable = false;
    num = simp_try_add(ctx, num, constant_numerator, &unrepresentable);
    if (unrepresentable)
      return IXS_ALGEBRA_UNREPRESENTABLE;
  }
  if (!num)
    return IXS_ALGEBRA_OOM;
  if (ixs_node_is_sentinel(num))
    return IXS_ALGEBRA_NO_MATCH;
  *numerator = num;
  *denominator = denom;
  return IXS_ALGEBRA_MATCH;
}

IXS_STATIC ixs_algebra_status
ixs_euclidean_quotient_parts(ixs_ctx *ctx, ixs_node *expr, ixs_node **numerator,
                             ixs_node **denominator) {
  ixs_arena_mark mark;
  ixs_node *result_numerator = NULL;
  ixs_node *result_denominator = NULL;
  ixs_algebra_status status;
  assert(ctx && expr && numerator && denominator);
  mark = ixs_arena_save(&ctx->scratch);
  *numerator = NULL;
  *denominator = NULL;
  status =
      euclidean_exact_parts(ctx, expr, &result_numerator, &result_denominator);
  ixs_arena_restore(&ctx->scratch, mark);
  if (status == IXS_ALGEBRA_MATCH) {
    *numerator = result_numerator;
    *denominator = result_denominator;
  }
  return status;
}

static unsigned euclidean_atom_mask(ixs_tag tag) {
  if (tag == IXS_FLOOR)
    return IXS_EUCLIDEAN_FLOOR;
  if (tag == IXS_CEIL)
    return IXS_EUCLIDEAN_CEIL;
  if (tag == IXS_MOD)
    return IXS_EUCLIDEAN_MOD;
  return 0u;
}

static bool euclidean_term_atom(ixs_node *term, unsigned mask,
                                uint32_t *factor_index, ixs_node **atom) {
  uint32_t found = UINT32_MAX;
  uint32_t i;
  unsigned selected;
  if (!term)
    return false;
  selected = euclidean_atom_mask(term->tag);
  if (selected && (selected & mask)) {
    *factor_index = UINT32_MAX;
    *atom = term;
    return true;
  }
  if (term->tag != IXS_MUL)
    return false;
  for (i = 0; i < term->u.mul.nfactors; i++) {
    ixs_node *base = term->u.mul.factors[i].base;
    selected = euclidean_atom_mask(base->tag);
    if (!(selected & mask))
      continue;
    if (found != UINT32_MAX || term->u.mul.factors[i].exp != 1)
      return false;
    found = i;
  }
  if (found == UINT32_MAX)
    return false;
  *factor_index = found;
  *atom = term->u.mul.factors[found].base;
  return true;
}

static ixs_algebra_status euclidean_term_scale(ixs_ctx *ctx,
                                               const ixs_addterm *term,
                                               uint32_t factor_index,
                                               ixs_node **scale) {
  ixs_arena_mark mark;
  ixs_mulfactor *factors;
  ixs_node *coefficient;
  bool unrepresentable = false;
  uint32_t i;
  uint32_t write = 0;
  if (factor_index == UINT32_MAX) {
    *scale = term->coeff;
    return IXS_ALGEBRA_MATCH;
  }
  coefficient =
      simp_try_mul(ctx, term->coeff, term->term->u.mul.coeff, &unrepresentable);
  if (unrepresentable)
    return IXS_ALGEBRA_UNREPRESENTABLE;
  if (!coefficient)
    return IXS_ALGEBRA_OOM;
  if (ixs_node_is_sentinel(coefficient))
    return IXS_ALGEBRA_INVALID;
  if (term->term->u.mul.nfactors == 1u) {
    *scale = coefficient;
    return IXS_ALGEBRA_MATCH;
  }
  mark = ixs_arena_save(&ctx->scratch);
  factors = ixs_arena_alloc(
      &ctx->scratch, (term->term->u.mul.nfactors - 1u) * sizeof(*factors),
      sizeof(void *));
  if (!factors) {
    ixs_arena_restore(&ctx->scratch, mark);
    return IXS_ALGEBRA_OOM;
  }
  for (i = 0; i < term->term->u.mul.nfactors; i++)
    if (i != factor_index)
      factors[write++] = term->term->u.mul.factors[i];
  *scale = euclidean_build_product(ctx, coefficient, write, factors);
  ixs_arena_restore(&ctx->scratch, mark);
  if (!*scale)
    return IXS_ALGEBRA_OOM;
  return ixs_node_is_sentinel(*scale) ? IXS_ALGEBRA_INVALID : IXS_ALGEBRA_MATCH;
}

IXS_STATIC ixs_algebra_status
ixs_euclidean_plan_addterm(ixs_ctx *ctx, const ixs_addterm *term, unsigned mask,
                           ixs_euclidean_term_plan *plan) {
  ixs_euclidean_term_plan result;
  uint32_t factor_index;
  ixs_algebra_status status;
  assert(ctx && term && plan);
  if (!euclidean_term_atom(term->term, mask, &factor_index, &result.atom))
    return IXS_ALGEBRA_NO_MATCH;
  status = euclidean_term_scale(ctx, term, factor_index, &result.scale);
  if (status != IXS_ALGEBRA_MATCH)
    return status;
  if (result.atom->tag == IXS_MOD) {
    result.numerator = result.atom->u.binary.lhs;
    result.denominator = result.atom->u.binary.rhs;
  } else {
    status = ixs_euclidean_quotient_parts(
        ctx, result.atom->u.unary.arg, &result.numerator, &result.denominator);
    if (status == IXS_ALGEBRA_UNREPRESENTABLE)
      return IXS_ALGEBRA_NO_MATCH;
    if (status != IXS_ALGEBRA_MATCH)
      return status;
  }
  result.source = term;
  result.factor_index = factor_index;
  *plan = result;
  return IXS_ALGEBRA_MATCH;
}

IXS_STATIC ixs_algebra_status ixs_euclidean_plan_outer(
    ixs_ctx *ctx, const ixs_euclidean_term_plan *plan, ixs_node **outer) {
  ixs_arena_mark mark;
  ixs_mulfactor *factors;
  uint32_t i;
  uint32_t write = 0;
  assert(ctx && plan && plan->source && outer);
  if (plan->factor_index == UINT32_MAX) {
    *outer = ctx->node_one;
    return IXS_ALGEBRA_MATCH;
  }
  if (plan->source->term->u.mul.nfactors == 1u) {
    *outer = plan->source->term->u.mul.coeff;
    return IXS_ALGEBRA_MATCH;
  }
  mark = ixs_arena_save(&ctx->scratch);
  factors = ixs_arena_alloc(&ctx->scratch,
                            (plan->source->term->u.mul.nfactors - 1u) *
                                sizeof(*factors),
                            sizeof(void *));
  if (!factors) {
    ixs_arena_restore(&ctx->scratch, mark);
    return IXS_ALGEBRA_OOM;
  }
  for (i = 0; i < plan->source->term->u.mul.nfactors; i++)
    if (i != plan->factor_index)
      factors[write++] = plan->source->term->u.mul.factors[i];
  *outer = euclidean_build_product(ctx, plan->source->term->u.mul.coeff, write,
                                   factors);
  ixs_arena_restore(&ctx->scratch, mark);
  if (!*outer)
    return IXS_ALGEBRA_OOM;
  return ixs_node_is_sentinel(*outer) ? IXS_ALGEBRA_INVALID : IXS_ALGEBRA_MATCH;
}

IXS_STATIC bool ixs_euclidean_row_contains(const ixs_euclidean_row *row,
                                           unsigned mask) {
  uint32_t i;
  assert(row);
  for (i = 0; i < row->nterms; i++) {
    uint32_t factor_index;
    ixs_node *atom;
    if (euclidean_term_atom(row->terms[i].term, mask, &factor_index, &atom))
      return true;
  }
  return false;
}
