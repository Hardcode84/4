/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "radix_algebra.h"

#include "bounds_query.h"
#include <string.h>

#define RADIX_ALGEBRA_MAX_INPUT_TERMS 8u
#define RADIX_ALGEBRA_MAX_SLOTS 16u
#define RADIX_ALGEBRA_MAX_TRANSFERS 16u

typedef struct {
  const ixs_node *expr;
  int64_t constant_p;
  int64_t constant_q;
  uint32_t nterms;
} radix_row;

typedef struct {
  const ixs_node *node;
  int64_t coefficient;
} radix_term;

typedef struct {
  const ixs_node *node;
  const ixs_node *floor_base;
  int64_t coefficient;
  int64_t floor_divisor;
} radix_slot;

/* Borrow one bounded canonical ADD row and validate its scalar coefficients.
 * The row owns no storage and remains valid while its interned expression does.
 */
static bool radix_row_borrow(const ixs_node *expr, uint32_t max_terms,
                             radix_row *row) {
  uint32_t i;

  memset(row, 0, sizeof(*row));
  if (!expr || expr->tag != IXS_ADD || expr->u.add.nterms == 0u ||
      expr->u.add.nterms > max_terms)
    return false;
  ixs_node_get_rat(expr->u.add.coeff, &row->constant_p, &row->constant_q);
  if (row->constant_q <= 0)
    return false;
  for (i = 0; i < expr->u.add.nterms; i++) {
    int64_t coefficient;
    int64_t denominator;
    ixs_node_get_rat(expr->u.add.terms[i].coeff, &coefficient, &denominator);
    (void)coefficient;
    if (denominator != 1)
      return false;
  }
  row->expr = expr;
  row->nterms = expr->u.add.nterms;
  return true;
}

static radix_term radix_row_term(const radix_row *row, uint32_t index) {
  radix_term term;
  int64_t denominator;

  term.node = row->expr->u.add.terms[index].term;
  ixs_node_get_rat(row->expr->u.add.terms[index].coeff, &term.coefficient,
                   &denominator);
  (void)denominator;
  return term;
}

static bool radix_floor_parts(const ixs_node *node, const ixs_node **base,
                              int64_t *divisor) {
  const ixs_node *argument;
  int64_t numerator;
  int64_t denominator;

  if (!node || node->tag != IXS_FLOOR)
    return false;
  argument = node->u.unary.arg;
  if (!argument || argument->tag != IXS_MUL || argument->u.mul.nfactors != 1u ||
      argument->u.mul.factors[0].exp != 1)
    return false;
  ixs_node_get_rat(argument->u.mul.coeff, &numerator, &denominator);
  if (numerator != 1 || denominator <= 1)
    return false;
  *base = argument->u.mul.factors[0].base;
  *divisor = denominator;
  return true;
}

static bool radix_orient_coefficient(int64_t coefficient, int orientation,
                                     int64_t *oriented) {
  if (coefficient == INT64_MIN)
    return false;
  *oriented = orientation > 0 ? coefficient : -coefficient;
  return true;
}

/* Admit the early order path only for a syntactic Euclidean split. This is
 * dispatch control, not the proof: the row reducer still performs all domain
 * checks and may cancel several scaled pairs after its floor transfers. */
static bool radix_row_has_oriented_mod_pair(const radix_row *row,
                                            int orientation) {
  uint32_t mod_index;

  for (mod_index = 0; mod_index < row->nterms; mod_index++) {
    radix_term mod_term = radix_row_term(row, mod_index);
    const ixs_node *mod = mod_term.node;
    int64_t mod_coefficient;
    uint32_t dividend_index;

    if (!radix_orient_coefficient(mod_term.coefficient, orientation,
                                  &mod_coefficient))
      return false;
    if (mod_coefficient >= 0 || mod->tag != IXS_MOD)
      continue;
    for (dividend_index = 0; dividend_index < row->nterms; dividend_index++) {
      radix_term dividend_term = radix_row_term(row, dividend_index);
      int64_t dividend_coefficient;

      if (!radix_orient_coefficient(dividend_term.coefficient, orientation,
                                    &dividend_coefficient))
        return false;
      if (dividend_coefficient > 0 && dividend_term.node == mod->u.binary.lhs)
        return true;
    }
  }
  return false;
}

static bool radix_init(const radix_row *row, int orientation, radix_slot *slots,
                       size_t *nslots) {
  uint32_t i;
  int64_t constant;
  bool has_reducible_negative = false;

  if (!radix_orient_coefficient(row->constant_p, orientation, &constant) ||
      constant < 0)
    return false;

  memset(slots, 0, RADIX_ALGEBRA_MAX_SLOTS * sizeof(*slots));
  *nslots = row->nterms;
  for (i = 0; i < row->nterms; i++) {
    radix_term term = radix_row_term(row, i);
    if (!radix_orient_coefficient(term.coefficient, orientation,
                                  &slots[i].coefficient))
      return false;
    slots[i].node = term.node;
    has_reducible_negative |=
        slots[i].coefficient < 0 && slots[i].node->tag == IXS_MOD;
  }
  for (i = 0; i < row->nterms; i++) {
    size_t base_slot;
    if (!radix_floor_parts(slots[i].node, &slots[i].floor_base,
                           &slots[i].floor_divisor))
      continue;
    has_reducible_negative |= slots[i].coefficient < 0;
    for (base_slot = 0; base_slot < *nslots; base_slot++)
      if (slots[base_slot].node == slots[i].floor_base)
        break;
    if (base_slot == *nslots) {
      if (*nslots == RADIX_ALGEBRA_MAX_SLOTS)
        return false;
      slots[(*nslots)++].node = slots[i].floor_base;
    }
  }
  return has_reducible_negative;
}

static int64_t radix_edge(const radix_slot *parent, const radix_slot *child) {
  if (child->floor_divisor == 0)
    return 0;
  if (child->floor_base == parent->node)
    return child->floor_divisor;
  /* floor(floor(x/d1)/r) == floor(x/(d1*r)) for positive integers. */
  if (parent->floor_divisor <= 0 || child->floor_base != parent->floor_base ||
      child->floor_divisor <= parent->floor_divisor ||
      child->floor_divisor % parent->floor_divisor != 0)
    return 0;
  return child->floor_divisor / parent->floor_divisor;
}

static bool radix_find_transfer(const radix_slot *slots, size_t nslots,
                                size_t *parent_index, size_t *child_index,
                                int64_t *child_radix) {
  size_t parent;
  for (parent = 0; parent < nslots; parent++) {
    size_t child;
    size_t best_child = nslots;
    int64_t best_radix = 0;
    /* Splitting a positive parent coefficient discards only a nonnegative
     * remainder. A negative coefficient would reverse that lower bound. */
    if (slots[parent].coefficient <= 0)
      continue;
    for (child = 0; child < nslots; child++) {
      int64_t radix = radix_edge(&slots[parent], &slots[child]);
      if (radix > 1 && (best_child == nslots || radix < best_radix)) {
        best_child = child;
        best_radix = radix;
      }
    }
    if (best_child == nslots)
      continue;
    *parent_index = parent;
    *child_index = best_child;
    *child_radix = best_radix;
    return true;
  }
  return false;
}

/* Mod(parent, radix) >= Mod(parent, d) when positive d divides radix. */
static size_t radix_residual(const radix_slot *slots, size_t nslots,
                             size_t parent_index, int64_t child_radix) {
  size_t residual_index = nslots;
  int64_t residual_modulus = 0;
  size_t candidate;
  for (candidate = 0; candidate < nslots; candidate++) {
    const ixs_node *node = slots[candidate].node;
    int64_t modulus;
    if (node->tag != IXS_MOD ||
        node->u.binary.lhs != slots[parent_index].node ||
        node->u.binary.rhs->tag != IXS_INT)
      continue;
    modulus = node->u.binary.rhs->u.ival;
    if (modulus > residual_modulus && modulus > 0 &&
        child_radix % modulus == 0) {
      residual_index = candidate;
      residual_modulus = modulus;
    }
  }
  return residual_index;
}

static bool radix_transfer(radix_slot *slots, size_t nslots,
                           size_t parent_index, size_t child_index,
                           int64_t child_radix) {
  size_t residual_index =
      radix_residual(slots, nslots, parent_index, child_radix);
  int64_t coefficient = slots[parent_index].coefficient;
  int64_t transferred;
  int64_t child_combined;
  int64_t residual_combined = 0;

  if (!ixs_safe_mul(coefficient, child_radix, &transferred) ||
      !ixs_safe_add(slots[child_index].coefficient, transferred,
                    &child_combined) ||
      (residual_index != nslots &&
       !ixs_safe_add(slots[residual_index].coefficient, coefficient,
                     &residual_combined)))
    return false;
  slots[parent_index].coefficient = 0;
  slots[child_index].coefficient = child_combined;
  if (residual_index != nslots)
    slots[residual_index].coefficient = residual_combined;
  return true;
}

static bool radix_residuals_nonnegative(ixs_bounds *bounds,
                                        const radix_slot *slots,
                                        size_t nslots) {
  size_t slot;
  for (slot = 0; slot < nslots; slot++) {
    ixs_interval range;
    if (slots[slot].coefficient < 0)
      return false;
    if (slots[slot].coefficient == 0)
      continue;
    range = ixs_bounds_get(bounds, (ixs_node *)slots[slot].node);
    if (!ixs_bounds_query_transport_clean(bounds) || !range.valid ||
        range.lo_inf || ixs_rat_cmp(range.lo_p, range.lo_q, 0, 1) < 0)
      return false;
  }
  return ixs_bounds_query_transport_clean(bounds);
}

static bool radix_mod_domain(ixs_bounds *bounds, const ixs_node *mod) {
  ixs_interval modulus_range;
  ixs_interval dividend_range;
  const ixs_node *dividend = mod->u.binary.lhs;

  if (ixs_bounds_check_integer_valued(bounds, (ixs_node *)dividend) !=
      IXS_CHECK_TRUE)
    return false;
  modulus_range = ixs_bounds_get(bounds, mod->u.binary.rhs);
  dividend_range = ixs_bounds_get(bounds, (ixs_node *)dividend);
  if (!ixs_bounds_query_transport_clean(bounds) || !modulus_range.valid ||
      modulus_range.lo_inf ||
      ixs_rat_cmp(modulus_range.lo_p, modulus_range.lo_q, 0, 1) <= 0 ||
      !dividend_range.valid || dividend_range.lo_inf ||
      ixs_rat_cmp(dividend_range.lo_p, dividend_range.lo_q, 0, 1) < 0)
    return false;
  return true;
}

/* Drop row-wide k*(x-Mod(x,m)) lower bounds after literal floor transfers have
 * retained every useful remainder. Each negative Mod scans the fixed row once.
 */
static void radix_cancel_mod_splits(ixs_bounds *bounds, radix_slot *slots,
                                    size_t nslots) {
  size_t mod_index;

  for (mod_index = 0; mod_index < nslots; mod_index++) {
    const ixs_node *mod = slots[mod_index].node;
    size_t dividend_index;
    int64_t amount;

    if (slots[mod_index].coefficient >= 0 ||
        slots[mod_index].coefficient == INT64_MIN || mod->tag != IXS_MOD)
      continue;
    for (dividend_index = 0; dividend_index < nslots; dividend_index++)
      if (slots[dividend_index].node == mod->u.binary.lhs &&
          slots[dividend_index].coefficient > 0)
        break;
    if (dividend_index == nslots || !radix_mod_domain(bounds, mod)) {
      if (!ixs_bounds_query_transport_clean(bounds))
        return;
      continue;
    }
    amount = -slots[mod_index].coefficient;
    if (amount > slots[dividend_index].coefficient)
      amount = slots[dividend_index].coefficient;
    slots[dividend_index].coefficient -= amount;
    slots[mod_index].coefficient += amount;
  }
}

static ixs_radix_algebra_result radix_reduce_nonnegative(ixs_bounds *bounds,
                                                         const radix_row *row,
                                                         int orientation) {
  ixs_radix_algebra_result result = {IXS_CHECK_UNKNOWN, false, false};
  radix_slot slots[RADIX_ALGEBRA_MAX_SLOTS];
  size_t nslots;
  size_t step;

  if (!radix_init(row, orientation, slots, &nslots))
    return result;

  for (step = 0; step < RADIX_ALGEBRA_MAX_TRANSFERS; step++) {
    size_t parent_index;
    size_t child_index;
    int64_t child_radix;
    if (!radix_find_transfer(slots, nslots, &parent_index, &child_index,
                             &child_radix))
      break;
    /* Checked arithmetic failure is an ordinary unsupported certificate. */
    if (!radix_transfer(slots, nslots, parent_index, child_index, child_radix))
      return result;
  }
  if (step == RADIX_ALGEBRA_MAX_TRANSFERS) {
    result.limited = true;
    return result;
  }
  radix_cancel_mod_splits(bounds, slots, nslots);
  if (radix_residuals_nonnegative(bounds, slots, nslots))
    result.check = IXS_CHECK_TRUE;
  if (!ixs_bounds_query_transport_clean(bounds))
    result.check = IXS_CHECK_UNKNOWN;
  result.oom = bounds->oom;
  return result;
}

/* With T <= 8 input terms, N <= 16 slots, and K < 16 floor transfers,
 * intrinsic work is O(T*N + K*N^2 + N^2) in one fixed row. Mod cancellation
 * makes at most 3*N inherited domain-oracle calls; final residual validation
 * makes at most N ordinary range-oracle calls. */
/* hot */
IXS_STATIC ixs_radix_algebra_result
ixs_radix_algebra_nonnegative(ixs_bounds *bounds, const ixs_node *expr) {
  ixs_radix_algebra_result result = {IXS_CHECK_UNKNOWN, false, false};
  radix_row row;

  if (!bounds || !expr || !bounds->scratch)
    return result;
  if (!ixs_bounds_query_transport_clean(bounds)) {
    result.oom = bounds->oom;
    return result;
  }
  if (!radix_row_borrow(expr, RADIX_ALGEBRA_MAX_INPUT_TERMS, &row))
    return result;
  return radix_reduce_nonnegative(bounds, &row, 1);
}

/* Polarity is a coefficient view over the borrowed row. No negated expression
 * is constructed, and INT64_MIN is rejected before orientation. */
/* hot */
IXS_STATIC ixs_radix_algebra_result ixs_radix_algebra_order(
    ixs_bounds *bounds, const ixs_node *expr, ixs_cmp_op op) {
  ixs_radix_algebra_result result = {IXS_CHECK_UNKNOWN, false, false};
  ixs_check_result proven;
  radix_row row;
  int orientation;

  if (!bounds || !expr || !bounds->scratch)
    return result;
  switch (op) {
  case IXS_CMP_GE:
    orientation = 1;
    proven = IXS_CHECK_TRUE;
    break;
  case IXS_CMP_LT:
    orientation = 1;
    proven = IXS_CHECK_FALSE;
    break;
  case IXS_CMP_LE:
    orientation = -1;
    proven = IXS_CHECK_TRUE;
    break;
  case IXS_CMP_GT:
    orientation = -1;
    proven = IXS_CHECK_FALSE;
    break;
  case IXS_CMP_EQ:
  case IXS_CMP_NE:
  default:
    return result;
  }
  if (!ixs_bounds_query_transport_clean(bounds)) {
    result.oom = bounds->oom;
    return result;
  }
  if (!radix_row_borrow(expr, RADIX_ALGEBRA_MAX_INPUT_TERMS, &row))
    return result;
  if (!radix_row_has_oriented_mod_pair(&row, orientation))
    return result;
  result = radix_reduce_nonnegative(bounds, &row, orientation);
  if (result.check == IXS_CHECK_TRUE)
    result.check = proven;
  return result;
}
