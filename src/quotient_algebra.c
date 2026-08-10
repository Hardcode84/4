/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "quotient_algebra.h"

#include "simplify.h"
#include <string.h>

typedef enum { QA_REMAINDER_BASIS, QA_QUOTIENT_BASIS } qa_basis;

typedef enum { QA_ADD, QA_MUL, QA_DIV } qa_op;

typedef struct {
  ixs_ctx *ctx;
  ixs_bounds *bounds;
  ixs_node *minus_one;
  unsigned candidates;
  bool exhausted;
  bool limited;
  bool invalid;
  bool oom;
  bool unrepresentable;
} qa_query;

/* Canonical ADD is already a sorted sparse affine row. Non-ADD expressions
 * borrow one synthetic coefficient-one term instead of changing form. */
typedef struct {
  ixs_node *constant;
  const ixs_addterm *terms;
  ixs_addterm one;
  uint32_t nterms;
} qa_row;

typedef struct {
  ixs_node *atom;
  ixs_node *numerator;
  ixs_node *denominator;
  ixs_node *scale;
} qa_pivot;

static bool qa_stopped(const qa_query *query) {
  return query->exhausted || query->limited || query->invalid || query->oom ||
         query->unrepresentable;
}

static bool qa_has_capacity(qa_query *query, unsigned count) {
  if (count < IXS_QUOTIENT_ALGEBRA_MAX_CANDIDATES)
    return true;
  query->exhausted = true;
  return false;
}

/* Operands are total. Speculative construction reports representability
 * through simp_try_*, and nested optional rewrites preserve valid input on
 * representability failure. Any remaining sentinel is therefore an invalid
 * internal result; keep its diagnostic attached. */
static ixs_node *qa_node(qa_query *query, ixs_node *node, bool null_is_oom) {
  query->oom |= node == NULL && null_is_oom;
  query->invalid |= node != NULL && ixs_node_is_sentinel(node);
  return node && !ixs_node_is_sentinel(node) ? node : NULL;
}

static ixs_node *qa_build(qa_query *query, qa_op op, ixs_node *lhs,
                          ixs_node *rhs) {
  bool unrepresentable = false;
  ixs_node *result;
  if (op == QA_DIV && ixs_node_is_zero(rhs)) {
    query->unrepresentable = true;
    return NULL;
  }
  if (op == QA_ADD)
    result = simp_try_add(query->ctx, lhs, rhs, &unrepresentable);
  else if (op == QA_MUL)
    result = simp_try_mul(query->ctx, lhs, rhs, &unrepresentable);
  else
    result = simp_try_div(query->ctx, lhs, rhs, &unrepresentable);
  query->unrepresentable |= unrepresentable;
  return qa_node(query, result, !unrepresentable);
}

static ixs_node *qa_sub(qa_query *query, ixs_node *lhs, ixs_node *rhs) {
  ixs_node *negative = qa_build(query, QA_MUL, query->minus_one, rhs);
  return negative ? qa_build(query, QA_ADD, lhs, negative) : NULL;
}

static bool qa_cmp(qa_query *query, ixs_node *lhs, ixs_cmp_op op,
                   ixs_node *rhs) {
  struct ixs_node_impl cmp;
  memset(&cmp, 0, sizeof(cmp));
  cmp.tag = IXS_CMP;
  cmp.u.binary.lhs = lhs;
  cmp.u.binary.rhs = rhs;
  cmp.u.binary.cmp_op = op;
  bool result = ixs_bounds_check(query->bounds, &cmp) == IXS_CHECK_TRUE;
  query->oom |= query->bounds->oom;
  return result;
}

static bool qa_integer_defined(qa_query *query, ixs_node *node) {
  bool result =
      ixs_bounds_check_defined(query->bounds, node) == IXS_CHECK_TRUE &&
      ixs_bounds_check_integer_valued(query->bounds, node) == IXS_CHECK_TRUE;
  query->oom |= query->bounds->oom;
  return result && !query->oom;
}

static ixs_node *qa_simplify(qa_query *query, ixs_node *expr) {
  bool limited = false;
  if (!expr)
    return NULL;
  if (ixs_node_is_sentinel(expr))
    return qa_node(query, expr, false);
  expr = simp_simplify_bounds_status(query->ctx, expr, query->bounds, &limited);
  query->limited |= limited;
  return qa_node(query, expr, !limited);
}

static void qa_row_init(qa_query *query, ixs_node *expr, qa_row *row) {
  if (expr->tag == IXS_ADD) {
    row->constant = expr->u.add.coeff;
    row->terms = expr->u.add.terms;
    row->nterms = expr->u.add.nterms;
    return;
  }
  row->constant = query->ctx->node_zero;
  row->one.term = expr;
  row->one.coeff = query->ctx->node_one;
  row->terms = &row->one;
  row->nterms = 1u;
}

static bool qa_parts(qa_query *query, ixs_node *atom, ixs_node **numerator,
                     ixs_node **denominator) {
  ixs_quotient_parts_status status;
  if (atom->tag == IXS_MOD) {
    *numerator = atom->u.binary.lhs;
    *denominator = atom->u.binary.rhs;
  } else if (atom->tag == IXS_FLOOR) {
    status = simp_exact_quotient_parts(query->ctx, atom->u.unary.arg, numerator,
                                       denominator);
    if (status == IXS_QUOTIENT_PARTS_OOM)
      query->oom = true;
    /* Representability rejects only this floor pivot; another row pivot may
     * still supply a complete certificate. */
    if (status != IXS_QUOTIENT_PARTS_MATCH)
      return false;
  } else {
    return false;
  }
  return qa_integer_defined(query, *numerator) &&
         qa_integer_defined(query, *denominator) &&
         qa_cmp(query, *denominator, IXS_CMP_GT, query->ctx->node_zero);
}

static bool qa_basis_matches(ixs_node *node, qa_basis basis, bool either) {
  if (either)
    return node->tag == IXS_MOD || node->tag == IXS_FLOOR;
  /* The enum names the destination basis: eliminating Floor leaves a
   * remainder basis, while eliminating Mod leaves a quotient basis. */
  return node->tag == (basis == QA_REMAINDER_BASIS ? IXS_FLOOR : IXS_MOD);
}

/* Remove the unique quotient/remainder factor from a canonical product. The
 * remaining sorted factors are its exact algebraic scale; division by the
 * atom would add a spurious nonzero obligation. */
static bool qa_row_pivot(qa_query *query, const qa_row *row, uint32_t index,
                         qa_basis basis, bool either, qa_pivot *pivot) {
  ixs_node *term = row->terms[index].term;
  ixs_node *outer = row->terms[index].coeff;
  ixs_node *coefficient;
  ixs_arena_mark mark;
  ixs_mulfactor *factors;
  uint32_t found = UINT32_MAX;
  uint32_t i;
  uint32_t write = 0;
  if (qa_basis_matches(term, basis, either)) {
    pivot->atom = term;
    if (either)
      return true;
    pivot->scale = outer;
    return qa_parts(query, term, &pivot->numerator, &pivot->denominator);
  }
  if (term->tag != IXS_MUL)
    return false;
  for (i = 0; i < term->u.mul.nfactors; i++) {
    ixs_node *base = term->u.mul.factors[i].base;
    if (base->tag != IXS_MOD && base->tag != IXS_FLOOR)
      continue;
    if (found != UINT32_MAX || term->u.mul.factors[i].exp != 1)
      return false;
    found = i;
  }
  if (found == UINT32_MAX ||
      !qa_basis_matches(term->u.mul.factors[found].base, basis, either))
    return false;
  if (either)
    return true;
  coefficient = qa_build(query, QA_MUL, outer, term->u.mul.coeff);
  if (!coefficient)
    return false;
  pivot->atom = term->u.mul.factors[found].base;
  if (term->u.mul.nfactors == 1u) {
    pivot->scale = coefficient;
  } else {
    mark = ixs_arena_save(&query->ctx->scratch);
    factors = ixs_arena_alloc(&query->ctx->scratch,
                              (term->u.mul.nfactors - 1u) * sizeof(*factors),
                              sizeof(void *));
    if (!factors) {
      query->oom = true;
      ixs_arena_restore(&query->ctx->scratch, mark);
      return false;
    }
    for (i = 0; i < term->u.mul.nfactors; i++)
      if (i != found)
        factors[write++] = term->u.mul.factors[i];
    pivot->scale = ixs_node_mul(query->ctx, coefficient, write, factors);
    ixs_arena_restore(&query->ctx->scratch, mark);
    if (!pivot->scale) {
      query->oom = true;
      return false;
    }
  }
  return qa_parts(query, pivot->atom, &pivot->numerator, &pivot->denominator);
}

static ixs_node *qa_replacement(qa_query *query, const qa_pivot *pivot) {
  ixs_node *opposite = qa_node(
      query, simp_mod(query->ctx, pivot->numerator, pivot->denominator), true);
  ixs_node *residual;
  if (!opposite)
    return NULL;
  residual = qa_sub(query, pivot->numerator, opposite);
  return residual ? qa_build(query, QA_DIV, residual, pivot->denominator)
                  : NULL;
}

/* Substitute each eligible row atom once. Exact Euclidean replacements are
 * valid in every occurrence, so one iterative multi-substitution replaces the
 * old sequence of growing ADD rebuilds. */
static bool qa_project(qa_query *query, ixs_node *expr, ixs_node **projected) {
  ixs_node *targets[IXS_QUOTIENT_ALGEBRA_MAX_CANDIDATES];
  ixs_node *replacements[IXS_QUOTIENT_ALGEBRA_MAX_CANDIDATES];
  qa_row row;
  uint32_t count = 0;
  uint32_t i;
  uint32_t j;
  *projected = expr;
  qa_row_init(query, expr, &row);
  for (i = 0; i < row.nterms && !qa_stopped(query); i++) {
    qa_pivot pivot;
    if (!qa_row_pivot(query, &row, i, QA_REMAINDER_BASIS, false, &pivot))
      continue;
    for (j = 0; j < count && targets[j] != pivot.atom; j++)
      ;
    if (j != count)
      continue;
    if (!qa_has_capacity(query, count))
      return false;
    targets[count] = pivot.atom;
    replacements[count] = qa_replacement(query, &pivot);
    if (!replacements[count])
      return false;
    count++;
  }
  if (count == 0u || qa_stopped(query))
    return false;
  *projected = qa_node(
      query, simp_subs_multi(query->ctx, expr, count, targets, replacements),
      true);
  *projected = qa_simplify(query, *projected);
  return *projected && *projected != expr;
}

/* Prove a symbolic affine remainder range. Positive c*Mod(n,m) digits add
 * [0,c*(m-1)]; the ordinary interval engine bounds the residual once. */
static bool qa_affine_remainder_range(qa_query *query, ixs_node *expr,
                                      ixs_node *denominator) {
  qa_row row;
  ixs_node *residual = expr;
  ixs_node *digit_upper = query->ctx->node_zero;
  ixs_interval range;
  uint32_t digits = 0;
  uint32_t i;
  qa_row_init(query, expr, &row);
  for (i = 0; i < row.nterms && !qa_stopped(query); i++) {
    qa_pivot pivot;
    ixs_node *digit;
    ixs_node *width;
    ixs_node *upper;
    if (!qa_row_pivot(query, &row, i, QA_QUOTIENT_BASIS, false, &pivot) ||
        !qa_integer_defined(query, pivot.scale) ||
        !qa_cmp(query, pivot.scale, IXS_CMP_GT, query->ctx->node_zero))
      continue;
    if (!qa_has_capacity(query, digits))
      return false;
    digit = qa_build(query, QA_MUL, pivot.scale, pivot.atom);
    width = qa_sub(query, pivot.denominator, query->ctx->node_one);
    upper = width ? qa_build(query, QA_MUL, pivot.scale, width) : NULL;
    residual = digit ? qa_sub(query, residual, digit) : NULL;
    digit_upper = upper ? qa_build(query, QA_ADD, digit_upper, upper) : NULL;
    if (!residual || !digit_upper)
      return false;
    digits++;
  }
  if (digits == 0u || qa_stopped(query))
    return false;
  residual = qa_simplify(query, residual);
  if (!residual)
    return false;
  range = ixs_bounds_get(query->bounds, residual);
  query->oom |= query->bounds->oom;
  if (!range.valid || range.lo_inf || range.hi_inf ||
      ixs_rat_cmp(range.lo_p, range.lo_q, 0, 1) < 0)
    return false;
  residual = ixs_node_rat(query->ctx, range.hi_p, range.hi_q);
  if (!residual) {
    query->oom = true;
    return false;
  }
  digit_upper = qa_build(query, QA_ADD, digit_upper, residual);
  digit_upper = qa_simplify(query, digit_upper);
  digit_upper = digit_upper ? qa_sub(query, digit_upper, denominator) : NULL;
  digit_upper = digit_upper ? qa_simplify(query, digit_upper) : NULL;
  return digit_upper &&
         qa_cmp(query, digit_upper, IXS_CMP_LT, query->ctx->node_zero);
}

static bool qa_canonical_remainder(qa_query *query, ixs_node *expr,
                                   ixs_node *denominator) {
  ixs_node *upper;
  ixs_node *quotient;
  /* qa_parts already proved the pivot denominator positive and total. */
  if (!qa_integer_defined(query, expr))
    return false;
  upper = qa_sub(query, expr, denominator);
  if (upper && qa_cmp(query, expr, IXS_CMP_GE, query->ctx->node_zero) &&
      qa_cmp(query, upper, IXS_CMP_LT, query->ctx->node_zero))
    return true;
  if (!qa_stopped(query) && qa_affine_remainder_range(query, expr, denominator))
    return true;
  quotient = qa_build(query, QA_DIV, expr, denominator);
  if (!quotient)
    return false;
  quotient = qa_node(query, simp_floor(query->ctx, quotient), true);
  return quotient && qa_cmp(query, quotient, IXS_CMP_EQ, query->ctx->node_zero);
}

static bool qa_multiple(qa_query *query, ixs_node *expr,
                        ixs_node *denominator) {
  ixs_node *quotient;
  if (denominator->tag == IXS_INT) {
    ixs_check_result result =
        ixs_bounds_check_congruent(query->bounds, expr, denominator->u.ival, 0);
    query->oom |= query->bounds->oom;
    if (result == IXS_CHECK_TRUE)
      return true;
  }
  quotient = qa_build(query, QA_DIV, expr, denominator);
  return quotient && qa_integer_defined(query, quotient);
}

/* Replace only the admitted direct occurrence. The congruence equation is
 * s*(n-Mod(n,m)) = s*m*floor(n/m), so replacing s*Mod(n,m) by s*n modulo d
 * requires d to divide s*m. Nested occurrences lack a checked coefficient.
 * At most four row deltas are built, keeping this O(T). */
static bool qa_reduce_congruence(qa_query *query, ixs_node *expr,
                                 ixs_node *denominator, ixs_node **reduced) {
  qa_row row;
  ixs_node *result = expr;
  unsigned reductions = 0;
  uint32_t i;
  qa_row_init(query, expr, &row);
  for (i = 0; i < row.nterms && !qa_stopped(query); i++) {
    qa_pivot pivot;
    ixs_node *covered;
    ixs_node *coverage;
    ixs_node *scaled;
    ixs_node *replacement;
    ixs_node *delta;
    if (!qa_row_pivot(query, &row, i, QA_QUOTIENT_BASIS, false, &pivot))
      continue;
    covered = qa_build(query, QA_MUL, pivot.scale, pivot.denominator);
    coverage = covered ? qa_build(query, QA_DIV, covered, denominator) : NULL;
    if (!coverage || !qa_integer_defined(query, coverage))
      continue;
    if (!qa_has_capacity(query, reductions))
      return false;
    scaled = qa_build(query, QA_MUL, pivot.scale, pivot.atom);
    replacement = qa_build(query, QA_MUL, pivot.scale, pivot.numerator);
    delta = scaled && replacement ? qa_sub(query, replacement, scaled) : NULL;
    result = delta ? qa_build(query, QA_ADD, result, delta) : NULL;
    if (!result)
      return false;
    reductions++;
  }
  if (reductions == 0u || qa_stopped(query))
    return false;
  *reduced = qa_simplify(query, result);
  return *reduced != NULL;
}

static bool qa_exact_zero(qa_query *query, ixs_node *expr) {
  ixs_node *projected;
  if (ixs_node_is_zero(expr) ||
      qa_cmp(query, expr, IXS_CMP_EQ, query->ctx->node_zero))
    return true;
  return !qa_stopped(query) && qa_project(query, expr, &projected) &&
         (ixs_node_is_zero(projected) ||
          qa_cmp(query, projected, IXS_CMP_EQ, query->ctx->node_zero));
}

/* Euclidean uniqueness gives Mod(n,d)=r iff r is in [0,d) and d divides
 * n-r, with all operands defined and integer-valued. */
static bool qa_remainder_value(qa_query *query, const qa_pivot *pivot,
                               ixs_node *candidate) {
  ixs_node *difference;
  ixs_node *reduced;
  if (!qa_canonical_remainder(query, candidate, pivot->denominator))
    return false;
  difference = qa_sub(query, pivot->numerator, candidate);
  if (!difference)
    return false;
  if (qa_exact_zero(query, difference) ||
      qa_multiple(query, difference, pivot->denominator))
    return true;
  reduced = difference;
  return !qa_stopped(query) &&
         qa_reduce_congruence(query, difference, pivot->denominator,
                              &reduced) &&
         (qa_exact_zero(query, reduced) ||
          qa_multiple(query, reduced, pivot->denominator));
}

/* Euclidean uniqueness gives floor(n/d)=q iff n-d*q is in [0,d). */
static bool qa_quotient_value(qa_query *query, const qa_pivot *pivot,
                              ixs_node *candidate) {
  ixs_node *product;
  ixs_node *residual;
  if (!qa_integer_defined(query, candidate))
    return false;
  product = qa_build(query, QA_MUL, pivot->denominator, candidate);
  residual = product ? qa_sub(query, pivot->numerator, product) : NULL;
  return residual &&
         qa_canonical_remainder(query, residual, pivot->denominator);
}

/* Divide a borrowed affine row by a rational pivot scale in one canonical
 * rebuild. This preserves sparsity when simplification does not distribute a
 * common rational factor. */
static ixs_node *qa_row_candidate(qa_query *query, const qa_row *row,
                                  uint32_t index, const qa_pivot *pivot,
                                  ixs_node *difference) {
  ixs_node *inverse;
  ixs_node *constant;
  ixs_addterm *terms;
  ixs_node *candidate;
  ixs_arena_mark mark;
  uint32_t i;
  uint32_t write = 0;
  if (difference->tag != IXS_ADD ||
      (pivot->scale->tag != IXS_INT && pivot->scale->tag != IXS_RAT)) {
    ixs_node *scaled = qa_build(query, QA_MUL, pivot->scale, pivot->atom);
    ixs_node *rest = scaled ? qa_sub(query, difference, scaled) : NULL;
    rest = rest ? qa_sub(query, query->ctx->node_zero, rest) : NULL;
    return rest ? qa_build(query, QA_DIV, rest, pivot->scale) : NULL;
  }
  inverse = qa_build(query, QA_DIV, query->minus_one, pivot->scale);
  constant = inverse ? qa_build(query, QA_MUL, inverse, row->constant) : NULL;
  if (!constant)
    return NULL;
  mark = ixs_arena_save(&query->ctx->scratch);
  terms = ixs_arena_alloc(&query->ctx->scratch,
                          (row->nterms - 1u) * sizeof(*terms), sizeof(void *));
  if (!terms && row->nterms != 1u) {
    query->oom = true;
    ixs_arena_restore(&query->ctx->scratch, mark);
    return NULL;
  }
  for (i = 0; i < row->nterms; i++) {
    if (i == index)
      continue;
    terms[write] = row->terms[i];
    terms[write].coeff = qa_build(query, QA_MUL, inverse, row->terms[i].coeff);
    if (!terms[write].coeff)
      break;
    write++;
  }
  candidate = i == row->nterms
                  ? (write ? ixs_node_add(query->ctx, constant, write, terms)
                           : constant)
                  : NULL;
  ixs_arena_restore(&query->ctx->scratch, mark);
  if (!candidate && i == row->nterms && !query->unrepresentable)
    query->oom = true;
  return candidate;
}

static bool qa_solve_row(qa_query *query, ixs_node *difference) {
  qa_row row;
  unsigned pass;
  uint32_t i;
  qa_row_init(query, difference, &row);
  for (pass = 0; pass < 2u; pass++)
    for (i = 0; i < row.nterms && !qa_stopped(query); i++) {
      qa_pivot pivot;
      ixs_node *candidate;
      qa_basis match = pass == 0u ? QA_QUOTIENT_BASIS : QA_REMAINDER_BASIS;
      if (!qa_row_pivot(query, &row, i, match, false, &pivot))
        continue;
      if (!qa_has_capacity(query, query->candidates))
        return false;
      query->candidates++;
      candidate = qa_row_candidate(query, &row, i, &pivot, difference);
      candidate = candidate ? qa_simplify(query, candidate) : NULL;
      if (!candidate || candidate == pivot.atom)
        continue;
      if (qa_cmp(query, pivot.atom, IXS_CMP_EQ, candidate))
        return true;
      if (pivot.atom->tag == IXS_MOD
              ? qa_remainder_value(query, &pivot, candidate)
              : qa_quotient_value(query, &pivot, candidate))
        return true;
    }
  return false;
}

static bool qa_contains_atom(qa_query *query, ixs_node *expr) {
  qa_row row;
  qa_pivot pivot;
  uint32_t i;
  qa_row_init(query, expr, &row);
  for (i = 0; i < row.nterms; i++)
    if (qa_row_pivot(query, &row, i, QA_REMAINDER_BASIS, true, &pivot))
      return true;
  return false;
}

/* The row engine adds a fixed number of O(T) scans. Simplification,
 * substitution, and bounds queries keep their existing reachable-DAG costs,
 * including the rewrite's expression-depth recursion. This component adds no
 * recursive call edge. */
static ixs_check_result qa_check_impl(qa_query *query, ixs_node *lhs,
                                      ixs_node *rhs) {
  if (!qa_contains_atom(query, lhs) && !qa_contains_atom(query, rhs))
    return IXS_CHECK_UNKNOWN;
  ixs_node *difference = qa_sub(query, lhs, rhs);
  difference = difference ? qa_simplify(query, difference) : NULL;
  if (!difference || qa_stopped(query))
    return IXS_CHECK_UNKNOWN;
  if (ixs_node_is_zero(difference) || qa_solve_row(query, difference) ||
      (!qa_stopped(query) && qa_exact_zero(query, difference)))
    return IXS_CHECK_TRUE;
  return IXS_CHECK_UNKNOWN;
}

IXS_STATIC ixs_quotient_algebra_result ixs_quotient_algebra_check(
    ixs_ctx *ctx, ixs_bounds *bounds, const ixs_node *lhs, const ixs_node *rhs,
    unsigned candidates) {
  ixs_quotient_algebra_result result = {IXS_CHECK_UNKNOWN, false, false, false};
  qa_query query = {.ctx = ctx, .bounds = bounds, .candidates = candidates};
  if (!ctx || !bounds || !lhs || !rhs) {
    result.invalid = true;
    return result;
  }
  if (bounds->oom || !(query.minus_one = ixs_node_int(ctx, -1))) {
    result.oom = true;
    return result;
  }
  result.check = qa_check_impl(&query, (ixs_node *)lhs, (ixs_node *)rhs);
  result.invalid = query.invalid;
  result.limited = query.limited || query.exhausted;
  result.oom = query.oom || bounds->oom;
  /* Intermediate coefficient overflow is a local rule miss. Propagating it
   * would suppress independent exact and low-bit strategies. */
  if (result.limited || result.invalid || result.oom || query.unrepresentable)
    result.check = IXS_CHECK_UNKNOWN;
  return result;
}
