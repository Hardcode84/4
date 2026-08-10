/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds_assume.h"

#include "additive_row.h"
#include "bounds.h"
#include "bounds_difference.h"
#include "bounds_query.h"
#include "bounds_store.h"
#include "query_walk.h"
#include "simplify.h"

#include <assert.h>
#include <limits.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* Record sym == rem (mod m).  Merges with existing info via CRT.
 * Overflowing constraints are silently ignored.  Direct contradictions are
 * recorded on the bounds object so query APIs can decline concrete answers. */
IXS_STATIC void apply_modrem(ixs_bounds *b, const char *name, int64_t modulus,
                             int64_t remainder) {
  if (bounds_store_merge_modrem(b, name, modulus, remainder))
    bounds_difference_propagate_symbol(b, name);
}

/* Recognize Mod(sym, M) == R as a modular congruence.
 *
 * Depends on the CMP normalizer in simp_cmp (cmp_normalize_to_zero):
 * "Mod(sym,M) == R" is rewritten to "(Mod(sym,M) - R) == 0", producing an
 * ADD node.  We must handle both the direct form (R == 0, no normalization)
 * and the normalized ADD form (R != 0). */
static void extract_modrem(ixs_bounds *b, ixs_node *a) {
  ixs_node *mod_node;
  int64_t rem_val;

  if (a->tag != IXS_CMP || a->u.binary.cmp_op != IXS_CMP_EQ)
    return;

  ixs_node *lhs = a->u.binary.lhs;
  ixs_node *rhs = a->u.binary.rhs;

  /* Direct: Mod(sym, M) == 0 */
  if (lhs->tag == IXS_MOD && ixs_node_is_zero(rhs)) {
    mod_node = lhs;
    rem_val = 0;
  } else if (rhs->tag == IXS_MOD && ixs_node_is_zero(lhs)) {
    mod_node = rhs;
    rem_val = 0;
  }
  /* Normalized: ADD(k, c*Mod(sym, M)) == 0, where c = +/-1 and k is integer.
   * c=1:  Mod(sym,M) == -k;   c=-1: Mod(sym,M) == k. */
  else if (ixs_node_is_zero(rhs) && lhs->tag == IXS_ADD &&
           lhs->u.add.nterms == 1 && lhs->u.add.terms[0].term->tag == IXS_MOD) {
    int64_t cp, cq, kp, kq;
    ixs_node_get_rat(lhs->u.add.terms[0].coeff, &cp, &cq);
    ixs_node_get_rat(lhs->u.add.coeff, &kp, &kq);
    if (cq != 1 || kq != 1)
      return;
    if (cp == 1) {
      if (kp == INT64_MIN)
        return;
      rem_val = -kp;
    } else if (cp == -1) {
      rem_val = kp;
    } else {
      return;
    }
    mod_node = lhs->u.add.terms[0].term;
  } else {
    return;
  }

  /* Validate Mod operands and record the congruence. */
  {
    ixs_node *dividend = mod_node->u.binary.lhs;
    ixs_node *modulus = mod_node->u.binary.rhs;
    if (dividend->tag != IXS_SYM || modulus->tag != IXS_INT ||
        modulus->u.ival <= 0)
      return;
    rem_val = (int64_t)ixs_int64_normalize_residue(rem_val,
                                                   (uint64_t)modulus->u.ival);
    apply_modrem(b, dividend->u.name, modulus->u.ival, rem_val);
  }
}

IXS_STATIC ixs_cmp_op flip_cmp(ixs_cmp_op op) {
  switch (op) {
  case IXS_CMP_GE:
    return IXS_CMP_LE;
  case IXS_CMP_GT:
    return IXS_CMP_LT;
  case IXS_CMP_LE:
    return IXS_CMP_GE;
  case IXS_CMP_LT:
    return IXS_CMP_GT;
  default:
    return op;
  }
}

static ixs_interval interval_from_integer_zero_cmp(ixs_cmp_op op) {
  ixs_interval iv = ixs_interval_unknown();
  iv.lo_inf = false;
  iv.hi_inf = false;
  switch (op) {
  case IXS_CMP_GT:
    iv.valid = true;
    iv.lo_p = 1;
    iv.lo_q = 1;
    ixs_interval_set_hi_pos_inf(&iv);
    break;
  case IXS_CMP_GE:
    iv.valid = true;
    iv.lo_p = 0;
    iv.lo_q = 1;
    ixs_interval_set_hi_pos_inf(&iv);
    break;
  case IXS_CMP_LT:
    iv.valid = true;
    ixs_interval_set_lo_neg_inf(&iv);
    iv.hi_p = -1;
    iv.hi_q = 1;
    break;
  case IXS_CMP_LE:
    iv.valid = true;
    ixs_interval_set_lo_neg_inf(&iv);
    iv.hi_p = 0;
    iv.hi_q = 1;
    break;
  case IXS_CMP_EQ:
    iv = ixs_interval_exact(0, 1);
    break;
  case IXS_CMP_NE:
    break;
  }
  return iv;
}

static ixs_interval interval_from_sym_cmp_const(ixs_cmp_op op, int64_t cp,
                                                int64_t cq) {
  ixs_interval iv = ixs_interval_unknown();
  iv.lo_inf = false;
  iv.hi_inf = false;
  switch (op) {
  case IXS_CMP_GE:
    iv.valid = true;
    iv.lo_p = cp;
    iv.lo_q = cq;
    ixs_interval_set_hi_pos_inf(&iv);
    break;
  case IXS_CMP_GT: {
    int64_t lo;
    if (!ixs_safe_add(ixs_rat_floor(cp, cq), 1, &lo))
      break;
    iv.valid = true;
    iv.lo_p = lo;
    iv.lo_q = 1;
    ixs_interval_set_hi_pos_inf(&iv);
    break;
  }
  case IXS_CMP_LE:
    iv.valid = true;
    ixs_interval_set_lo_neg_inf(&iv);
    iv.hi_p = cp;
    iv.hi_q = cq;
    break;
  case IXS_CMP_LT: {
    int64_t hi;
    if (!ixs_safe_sub(ixs_rat_ceil(cp, cq), 1, &hi))
      break;
    iv.valid = true;
    ixs_interval_set_lo_neg_inf(&iv);
    iv.hi_p = hi;
    iv.hi_q = 1;
    break;
  }
  case IXS_CMP_EQ:
    iv = ixs_interval_exact(cp, cq);
    break;
  case IXS_CMP_NE:
    break;
  }
  return iv;
}

/*
 * Write an ADD as offset + scale * primitive, using its first canonical term
 * coefficient as scale. The transform cache makes repeated range queries
 * O(1); a miss is linear only in the immediate ADD terms.
 */
static bool bounds_get_proportional_primitive(
    ixs_bounds *b, ixs_node *expr, ixs_node **primitive, int64_t *scale_p,
    int64_t *scale_q, int64_t *offset_p, int64_t *offset_q) {
  ixs_node *normalized;
  ixs_addterm *terms;
  ixs_arena_mark mark;
  size_t term_bytes;
  uint32_t i;
  /* Context-free proof scopes intentionally disable canonical alias creation.
   */
  if (!b->ctx)
    return false;

  if (expr->tag == IXS_MUL && expr->u.mul.nfactors == 1u &&
      expr->u.mul.factors[0].exp == 1) {
    ixs_node_get_rat(expr->u.mul.coeff, scale_p, scale_q);
    if (*scale_p == 0)
      return false;
    *primitive = expr->u.mul.factors[0].base;
    *offset_p = 0;
    *offset_q = 1;
    return true;
  }

  if (expr->tag != IXS_ADD || expr->u.add.nterms == 0)
    return false;
  ixs_node_get_rat(expr->u.add.terms[0].coeff, scale_p, scale_q);
  ixs_node_get_rat(expr->u.add.coeff, offset_p, offset_q);
  if (*scale_p == 0)
    return false;

  normalized = ixs_node_transform_cache_lookup(
      b->ctx, expr, IXS_NODE_TRANSFORM_PROPORTIONAL_PRIMITIVE);
  if (!normalized) {
    mark = ixs_arena_save(b->scratch);
    term_bytes = (size_t)expr->u.add.nterms * sizeof(*terms);
    if (term_bytes / sizeof(*terms) != expr->u.add.nterms) {
      b->oom = true;
      ixs_arena_restore(b->scratch, mark);
      return false;
    }
    terms = ixs_arena_alloc(b->scratch, term_bytes, sizeof(void *));
    if (!terms) {
      b->oom = true;
      ixs_arena_restore(b->scratch, mark);
      return false;
    }
    for (i = 0; i < expr->u.add.nterms; i++) {
      int64_t coeff_p, coeff_q, normalized_p, normalized_q;
      ixs_node_get_rat(expr->u.add.terms[i].coeff, &coeff_p, &coeff_q);
      if (!ixs_rat_div(coeff_p, coeff_q, *scale_p, *scale_q, &normalized_p,
                       &normalized_q)) {
        ixs_arena_restore(b->scratch, mark);
        return false;
      }
      terms[i].term = expr->u.add.terms[i].term;
      terms[i].coeff = ixs_node_rat(b->ctx, normalized_p, normalized_q);
      if (!terms[i].coeff) {
        b->oom = true;
        ixs_arena_restore(b->scratch, mark);
        return false;
      }
    }
    /* Dividing by the first coefficient makes this coefficient exactly one. */
    normalized = expr->u.add.nterms == 1
                     ? terms[0].term
                     : ixs_node_add(b->ctx, b->ctx->node_zero,
                                    expr->u.add.nterms, terms);
    ixs_arena_restore(b->scratch, mark);
    if (!normalized) {
      b->oom = true;
      return false;
    }
    if (ixs_node_is_sentinel(normalized))
      return false;
    ixs_node_transform_cache_store(
        b->ctx, expr, IXS_NODE_TRANSFORM_PROPORTIONAL_PRIMITIVE, normalized);
  }
  *primitive = normalized;
  return true;
}

static ixs_interval bounds_apply_affine(ixs_interval iv, int64_t scale_p,
                                        int64_t scale_q, int64_t offset_p,
                                        int64_t offset_q) {
  return iv_add(iv_mul_const(iv, scale_p, scale_q),
                ixs_interval_exact(offset_p, offset_q));
}

static ixs_interval bounds_invert_affine(ixs_interval iv, int64_t scale_p,
                                         int64_t scale_q, int64_t offset_p,
                                         int64_t offset_q) {
  int64_t neg_p, neg_q, inverse_p, inverse_q;
  if (!ixs_rat_neg(offset_p, offset_q, &neg_p, &neg_q) ||
      !ixs_rat_div(1, 1, scale_p, scale_q, &inverse_p, &inverse_q))
    return ixs_interval_unknown();
  return iv_mul_const(iv_add(iv, ixs_interval_exact(neg_p, neg_q)), inverse_p,
                      inverse_q);
}

static void add_shifted_add_range(ixs_bounds *b, ixs_node *expr,
                                  ixs_interval iv) {
  ixs_node *base;
  ixs_algebra_status status;
  int64_t cp, cq, np, nq;
  ixs_interval offset, shifted;

  if (!b->ctx)
    return;
  status = ixs_additive_row_without_constant(b->ctx, expr, &base);
  if (status == IXS_ALGEBRA_OOM)
    b->oom = true;
  if (status != IXS_ALGEBRA_MATCH || base == expr)
    return;
  ixs_node_get_rat(expr->u.add.coeff, &cp, &cq);
  if (!ixs_rat_neg(cp, cq, &np, &nq))
    return;
  offset = ixs_interval_exact(np, nq);
  shifted = iv_add(iv, offset);
  if (shifted.valid)
    ixs_bounds_add_expr(b, base, shifted);
}

static void add_expr_integer_zero_cmp(ixs_bounds *b, ixs_node *expr,
                                      ixs_cmp_op op) {
  ixs_interval iv;
  if (!ixs_node_is_integer_valued(expr))
    return;
  iv = interval_from_integer_zero_cmp(op);
  if (!iv.valid)
    return;
  ixs_bounds_add_expr(b, expr, iv);
  add_shifted_add_range(b, expr, iv);
}

/*
 * Apply "sym op const" bound to the variable's interval.
 */
static void apply_sym_cmp_const(ixs_bounds *b, const char *name, ixs_cmp_op op,
                                int64_t cp, int64_t cq) {
  ixs_var_bound *v = bounds_store_get_or_create_var(b, name);
  ixs_interval next;
  bool changed;
  bool exact_integer = false;
  if (!v)
    return;
  next = v->iv;
  switch (op) {
  case IXS_CMP_GE:
    if (next.lo_inf || ixs_rat_cmp(cp, cq, next.lo_p, next.lo_q) > 0) {
      next.lo_p = cp;
      next.lo_q = cq;
      next.lo_inf = false;
    }
    break;
  case IXS_CMP_GT: {
    int64_t lo;
    if (!ixs_safe_add(ixs_rat_floor(cp, cq), 1, &lo))
      break;
    if (next.lo_inf || ixs_rat_cmp(lo, 1, next.lo_p, next.lo_q) > 0) {
      next.lo_p = lo;
      next.lo_q = 1;
      next.lo_inf = false;
    }
    break;
  }
  case IXS_CMP_LE:
    if (next.hi_inf || ixs_rat_cmp(cp, cq, next.hi_p, next.hi_q) < 0) {
      next.hi_p = cp;
      next.hi_q = cq;
      next.hi_inf = false;
    }
    break;
  case IXS_CMP_LT: {
    int64_t hi;
    if (!ixs_safe_sub(ixs_rat_ceil(cp, cq), 1, &hi))
      break;
    if (next.hi_inf || ixs_rat_cmp(hi, 1, next.hi_p, next.hi_q) < 0) {
      next.hi_p = hi;
      next.hi_q = 1;
      next.hi_inf = false;
    }
    break;
  }
  case IXS_CMP_EQ:
    next.lo_p = cp;
    next.lo_q = cq;
    next.hi_p = cp;
    next.hi_q = cq;
    next.lo_inf = false;
    next.hi_inf = false;
    exact_integer = cq == 1;
    break;
  case IXS_CMP_NE:
    break;
  }
  changed = bounds_store_set_var_interval(b, v, next);
  if (exact_integer)
    bounds_store_apply_exact_int_bits(b, v, cp);
  bounds_store_refine_var_bits(b, v);
  if (changed)
    bounds_difference_propagate_symbol(b, name);
}

static bool node_get_int_const(ixs_node *n, int64_t *out) {
  if (!n || !out)
    return false;
  if (n->tag == IXS_INT) {
    *out = n->u.ival;
    return true;
  }
  if (n->tag == IXS_RAT && n->u.rat.q == 1) {
    *out = n->u.rat.p;
    return true;
  }
  return false;
}

IXS_STATIC bool node_coeff_is(ixs_node *n, int64_t value) {
  int64_t p, q;
  if (!n)
    return false;
  ixs_node_get_rat(n, &p, &q);
  return p == value && q == 1;
}

/* Recover "expr == integer" from either direct comparisons or the normalized
 * ADD(k, +/-expr) == 0 form produced by cmp_normalize_to_zero. */
IXS_STATIC bool extract_cmp_expr_const(ixs_node *cmp, ixs_node **expr,
                                       int64_t *value) {
  int64_t c;
  if (!cmp || cmp->tag != IXS_CMP || !expr || !value)
    return false;

  if (ixs_node_is_zero(cmp->u.binary.rhs) &&
      ixs_additive_row_unit_value(cmp->u.binary.lhs, expr, value))
    return true;
  if (ixs_node_is_zero(cmp->u.binary.lhs) &&
      ixs_additive_row_unit_value(cmp->u.binary.rhs, expr, value))
    return true;

  if (node_get_int_const(cmp->u.binary.rhs, &c) &&
      !ixs_node_is_const(cmp->u.binary.lhs)) {
    *expr = cmp->u.binary.lhs;
    *value = c;
    return true;
  }
  if (node_get_int_const(cmp->u.binary.lhs, &c) &&
      !ixs_node_is_const(cmp->u.binary.rhs)) {
    *expr = cmp->u.binary.rhs;
    *value = c;
    return true;
  }

  return false;
}

IXS_STATIC bool bounds_extract_unit_equality(ixs_node *expr, ixs_node **lhs,
                                             ixs_node **rhs) {
  ixs_node *positive;
  ixs_node *negative;
  int64_t constant;
  if (!ixs_additive_row_unit_pair(expr, &positive, &negative, &constant) ||
      constant != 0)
    return false;
  *lhs = positive;
  *rhs = negative;
  return true;
}

static bool extract_cmp_node_equality(ixs_node *cmp, ixs_node **a,
                                      ixs_node **b) {
  if (!cmp || cmp->tag != IXS_CMP || cmp->u.binary.cmp_op != IXS_CMP_EQ)
    return false;
  if (ixs_node_is_zero(cmp->u.binary.rhs))
    return bounds_extract_unit_equality(cmp->u.binary.lhs, a, b);
  if (ixs_node_is_zero(cmp->u.binary.lhs))
    return bounds_extract_unit_equality(cmp->u.binary.rhs, a, b);
  if (!ixs_node_is_const(cmp->u.binary.lhs) &&
      !ixs_node_is_const(cmp->u.binary.rhs)) {
    *a = cmp->u.binary.lhs;
    *b = cmp->u.binary.rhs;
    return true;
  }
  return false;
}

/* Split an exact comparison residual
 *
 *   constant + positive - negative == 0
 *
 * into the arbitrary-expression relation positive == negative + offset.
 * Query-time use is guarded by independent endpoint-definedness proofs. */
IXS_STATIC bool bounds_extract_cmp_exact_relation(ixs_bounds *b, ixs_node *cmp,
                                                  ixs_node **lhs,
                                                  ixs_node **rhs,
                                                  int64_t *offset) {
  ixs_algebra_status status;

  if (!b || !b->ctx || !cmp || cmp->tag != IXS_CMP ||
      cmp->u.binary.cmp_op != IXS_CMP_EQ || !lhs || !rhs || !offset)
    return false;
  status = ixs_additive_row_relation(b->ctx, b->scratch, cmp->u.binary.lhs,
                                     cmp->u.binary.rhs, lhs, rhs, offset);
  if (status == IXS_ALGEBRA_OOM)
    b->oom = true;
  return status == IXS_ALGEBRA_MATCH;
}

static bool sym_name_matches(ixs_node *n, const char *name) {
  return n && n->tag == IXS_SYM && n->u.name == name;
}

static bool node_is_sym_minus_one(ixs_node *n, const char *name) {
  int64_t kp, kq, cp, cq;
  if (!n || n->tag != IXS_ADD || n->u.add.nterms != 1 ||
      !sym_name_matches(n->u.add.terms[0].term, name))
    return false;
  ixs_node_get_rat(n->u.add.coeff, &kp, &kq);
  ixs_node_get_rat(n->u.add.terms[0].coeff, &cp, &cq);
  return kp == -1 && kq == 1 && cp == 1 && cq == 1;
}

IXS_STATIC bool extract_pow2_and(ixs_node *expr, const char **name) {
  ixs_node *a, *b;
  if (!expr || expr->tag != IXS_AND || expr->u.assoc.nargs != 2 || !name)
    return false;
  a = expr->u.assoc.args[0];
  b = expr->u.assoc.args[1];
  if (a->tag == IXS_SYM && node_is_sym_minus_one(b, a->u.name)) {
    *name = a->u.name;
    return true;
  }
  if (b->tag == IXS_SYM && node_is_sym_minus_one(a, b->u.name)) {
    *name = b->u.name;
    return true;
  }
  return false;
}

IXS_STATIC bool extract_bitop_sym_mask(ixs_node *expr, ixs_tag tag,
                                       const char **name, int64_t *mask) {
  ixs_node *a, *b;
  if (!expr || expr->tag != tag || expr->u.assoc.nargs != 2 || !name || !mask)
    return false;
  a = expr->u.assoc.args[0];
  b = expr->u.assoc.args[1];
  if (a->tag == IXS_SYM && node_get_int_const(b, mask)) {
    *name = a->u.name;
    return true;
  }
  if (b->tag == IXS_SYM && node_get_int_const(a, mask)) {
    *name = b->u.name;
    return true;
  }
  return false;
}

static void apply_pow2_or_zero(ixs_bounds *b, const char *name) {
  ixs_var_bound *v = bounds_store_get_or_create_var(b, name);
  if (!v)
    return;
  bounds_store_apply_pow2(b, v, IXS_POW2_OR_ZERO);
  apply_sym_cmp_const(b, name, IXS_CMP_GE, 0, 1);
}

static void extract_bitfacts_from_const_eq(ixs_bounds *b, ixs_node *expr,
                                           int64_t value) {
  const char *name;
  int64_t mask;
  uint64_t mask_bits, value_bits;

  if (extract_pow2_and(expr, &name)) {
    if (value == 0)
      apply_pow2_or_zero(b, name);
    return;
  }

  if (extract_bitop_sym_mask(expr, IXS_AND, &name, &mask)) {
    mask_bits = (uint64_t)mask;
    value_bits = (uint64_t)value;
    if ((value_bits & ~mask_bits) != 0) {
      bounds_store_mark_contradiction(b);
      return;
    }
    bounds_store_apply_known_bits(b, name, (~value_bits) & mask_bits,
                                  value_bits & mask_bits);
    return;
  }

  if (extract_bitop_sym_mask(expr, IXS_OR, &name, &mask)) {
    mask_bits = (uint64_t)mask;
    value_bits = (uint64_t)value;
    if ((value_bits & mask_bits) != mask_bits) {
      bounds_store_mark_contradiction(b);
      return;
    }
    bounds_store_apply_known_bits(b, name, ~value_bits,
                                  value_bits & ~mask_bits);
  }
}

static void extract_bitfacts_from_node_eq(ixs_bounds *b, ixs_node *a,
                                          ixs_node *other) {
  const char *name;
  int64_t mask;
  uint64_t mask_bits;

  if (other->tag != IXS_SYM)
    return;
  if (extract_bitop_sym_mask(a, IXS_OR, &name, &mask) &&
      name == other->u.name) {
    bounds_store_apply_known_bits(b, name, 0, (uint64_t)mask);
    return;
  }
  if (extract_bitop_sym_mask(a, IXS_AND, &name, &mask) &&
      name == other->u.name) {
    mask_bits = (uint64_t)mask;
    bounds_store_apply_known_bits(b, name, ~mask_bits, 0);
  }
}

static void extract_bitfacts(ixs_bounds *b, ixs_node *a) {
  ixs_node *expr, *lhs, *rhs;
  int64_t value;
  if (a->tag != IXS_CMP || a->u.binary.cmp_op != IXS_CMP_EQ)
    return;

  if (extract_cmp_expr_const(a, &expr, &value))
    extract_bitfacts_from_const_eq(b, expr, value);

  if (extract_cmp_node_equality(a, &lhs, &rhs)) {
    extract_bitfacts_from_node_eq(b, lhs, rhs);
    extract_bitfacts_from_node_eq(b, rhs, lhs);
  }
}

static void bounds_add_proportional_range(ixs_bounds *b, ixs_node *expr,
                                          ixs_interval iv) {
  ixs_node *primitive, *canonical;
  ixs_interval primitive_iv;
  int64_t scale_p, scale_q, offset_p, offset_q;
  if (!bounds_get_proportional_primitive(b, expr, &primitive, &scale_p,
                                         &scale_q, &offset_p, &offset_q) ||
      (primitive == expr && scale_p == 1 && scale_q == 1 && offset_p == 0))
    return;
  primitive_iv = bounds_invert_affine(iv, scale_p, scale_q, offset_p, offset_q);
  if (!primitive_iv.valid)
    return;
  bounds_store_add_expr_raw(b, primitive, primitive_iv);
  if (b->oom)
    return;
  canonical = bounds_canonical_expr(b, primitive);
  if (canonical && canonical != primitive)
    bounds_store_add_expr_raw(b, canonical, primitive_iv);
}

typedef struct {
  ixs_node *symbol;
  ixs_var_bound *var;
  int64_t modulus;
  int64_t lower;
  int64_t upper;
  int64_t residue_lower;
  int64_t residue_upper;
} bounds_mod_lift_domain;

static bool bounds_prepare_mod_lift_domain(ixs_bounds *b, ixs_node *mod,
                                           ixs_interval residue,
                                           bounds_mod_lift_domain *domain) {
  if (!b || !mod || mod->tag != IXS_MOD || mod->u.binary.lhs->tag != IXS_SYM ||
      mod->u.binary.rhs->tag != IXS_INT || mod->u.binary.rhs->u.ival <= 0 ||
      !residue.valid || residue.lo_inf || residue.hi_inf)
    return false;
  domain->symbol = mod->u.binary.lhs;
  domain->modulus = mod->u.binary.rhs->u.ival;
  domain->var = bounds_store_find_var(b, domain->symbol->u.name);
  if (!domain->var || !domain->var->iv.valid || domain->var->iv.lo_inf ||
      domain->var->iv.hi_inf)
    return false;
  domain->lower = ixs_rat_ceil(domain->var->iv.lo_p, domain->var->iv.lo_q);
  domain->upper = ixs_rat_floor(domain->var->iv.hi_p, domain->var->iv.hi_q);
  if (domain->lower > domain->upper || domain->lower <= -domain->modulus ||
      domain->upper >= domain->modulus)
    return false;
  domain->residue_lower = ixs_rat_ceil(residue.lo_p, residue.lo_q);
  domain->residue_upper = ixs_rat_floor(residue.hi_p, residue.hi_q);
  if (domain->residue_lower < 0)
    domain->residue_lower = 0;
  if (domain->residue_upper >= domain->modulus)
    domain->residue_upper = domain->modulus - 1;
  return domain->residue_lower <= domain->residue_upper;
}

/* Invert a residue interval only when a raw integer symbol is known to occupy
 * one lift on either side of zero.  Within (-m,m), Mod(x,m) can come only from
 * x itself or x+m; if exactly one lift misses the stored residue interval, the
 * other lift safely narrows x. */
static bool bounds_refine_symbol_from_mod_range(ixs_bounds *b, ixs_node *mod,
                                                ixs_interval residue) {
  bounds_mod_lift_domain domain;
  ixs_interval original;
  ixs_interval lifted;
  ixs_interval refined;
  int64_t negative_lower;
  int64_t negative_upper;
  int64_t positive_lower;
  int64_t positive_upper;
  bool negative_possible;
  bool positive_possible;

  if (!bounds_prepare_mod_lift_domain(b, mod, residue, &domain))
    return false;

  negative_lower = domain.lower;
  negative_upper = domain.upper < -1 ? domain.upper : -1;
  negative_possible = negative_lower <= negative_upper &&
                      negative_lower + domain.modulus <= domain.residue_upper &&
                      negative_upper + domain.modulus >= domain.residue_lower;
  positive_lower = domain.lower > 0 ? domain.lower : 0;
  positive_upper = domain.upper;
  positive_possible = positive_lower <= positive_upper &&
                      positive_lower <= domain.residue_upper &&
                      positive_upper >= domain.residue_lower;
  if (negative_possible == positive_possible)
    return false;

  if (positive_possible) {
    if (positive_lower < domain.residue_lower)
      positive_lower = domain.residue_lower;
    if (positive_upper > domain.residue_upper)
      positive_upper = domain.residue_upper;
    lifted = ixs_interval_range(positive_lower, 1, positive_upper, 1);
  } else {
    negative_lower = domain.residue_lower - domain.modulus;
    negative_upper = domain.residue_upper - domain.modulus;
    if (negative_lower < domain.lower)
      negative_lower = domain.lower;
    if (negative_upper > domain.upper)
      negative_upper = domain.upper;
    lifted = ixs_interval_range(negative_lower, 1, negative_upper, 1);
  }
  original = domain.var->iv;
  refined = iv_intersect(original, lifted);
  if (!refined.valid || ixs_interval_is_empty(refined) ||
      ixs_interval_equal(original, refined))
    return false;
  (void)bounds_store_set_var_interval(b, domain.var, refined);
  bounds_store_refine_var_bits(b, domain.var);
  bounds_store_add_expr_raw(b, domain.symbol, refined);
  if (!b->oom)
    bounds_difference_propagate_symbol(b, domain.symbol->u.name);
  return !b->oom;
}

typedef struct {
  size_t watcher_index;
  int64_t modulus;
} bounds_mod_inverse_incident;

static int bounds_mod_inverse_incident_compare(const void *lhs,
                                               const void *rhs) {
  const bounds_mod_inverse_incident *a = lhs;
  const bounds_mod_inverse_incident *b = rhs;
  if (a->modulus > b->modulus)
    return -1;
  if (a->modulus < b->modulus)
    return 1;
  return a->watcher_index < b->watcher_index
             ? -1
             : a->watcher_index != b->watcher_index;
}

/* A crossing interval can change only by selecting one wholly negative or
 * nonnegative lift, which fixes its sign.  Once the sign is fixed, descending
 * modulus order is a topological order: a larger modulus can enable a smaller
 * one, never the reverse.  Thus one crossing scan plus one sorted pass reaches
 * the same fixed point in O(k log k) for k incident watchers. */
static bool bounds_mod_inverse_sign_fixed(ixs_bounds *b,
                                          const char *symbol_name) {
  ixs_var_bound *var = bounds_store_find_var(b, symbol_name);
  if (!var || !var->iv.valid || var->iv.lo_inf || var->iv.hi_inf)
    return false;
  return ixs_rat_cmp(var->iv.hi_p, var->iv.hi_q, 0, 1) < 0 ||
         ixs_rat_cmp(var->iv.lo_p, var->iv.lo_q, 0, 1) >= 0;
}

static bool bounds_visit_mod_inverse_watcher(ixs_bounds *b,
                                             size_t watcher_index) {
  ixs_mod_inverse_watcher *watcher;
  ixs_expr_bound *bound;
  assert(watcher_index < b->nmod_inverse_watchers);
  watcher = &b->mod_inverse_watchers[watcher_index];
  assert(watcher->expr_index < b->nexprs);
  bound = &b->exprs[watcher->expr_index];
  bounds_store_note_mod_inverse_visit(b);
  return bounds_refine_symbol_from_mod_range(b, bound->expr, bound->iv);
}

static bool
bounds_refine_mod_inverse_sign(ixs_bounds *b, const char *symbol_name,
                               const bounds_mod_inverse_incident *incident,
                               size_t incident_count) {
  size_t i;

  if (bounds_mod_inverse_sign_fixed(b, symbol_name))
    return true;
  for (i = 0; i < incident_count && !b->oom && !b->contradiction; i++) {
    if (bounds_visit_mod_inverse_watcher(b, incident[i].watcher_index))
      break;
  }
  return bounds_mod_inverse_sign_fixed(b, symbol_name);
}

static void bounds_refine_mod_inverse_symbol(ixs_bounds *b, ixs_node *symbol) {
  ixs_var_bound *var;
  size_t var_index;
  size_t watcher_link;
  size_t incident_count = 0;
  bounds_mod_inverse_incident *incident;
  ixs_arena_mark work_mark;
  size_t i;

  if (!b || !symbol || symbol->tag != IXS_SYM || b->oom)
    return;
  var = bounds_store_find_var(b, symbol->u.name);
  if (!var || !var->iv.valid || var->iv.lo_inf || var->iv.hi_inf ||
      !b->mod_inverse_heads)
    return;
  var_index = (size_t)(var - b->vars);
  if (var_index >= b->mod_inverse_head_cap)
    return;
  watcher_link = b->mod_inverse_heads[var_index];
  while (watcher_link) {
    size_t watcher_index = watcher_link - 1u;
    assert(watcher_index < b->nmod_inverse_watchers);
    incident_count++;
    assert(incident_count <= b->nmod_inverse_watchers);
    watcher_link = b->mod_inverse_watchers[watcher_index].next;
  }
  if (!incident_count)
    return;
  if (incident_count > SIZE_MAX / sizeof(*incident)) {
    b->oom = true;
    return;
  }
  work_mark = ixs_arena_save(&b->query_arena);
  incident = ixs_arena_alloc(
      &b->query_arena, incident_count * sizeof(*incident), sizeof(void *));
  if (!incident) {
    ixs_arena_restore(&b->query_arena, work_mark);
    b->oom = true;
    return;
  }
  watcher_link = b->mod_inverse_heads[var_index];
  for (i = 0; i < incident_count; i++) {
    size_t watcher_index = watcher_link - 1u;
    ixs_mod_inverse_watcher *watcher = &b->mod_inverse_watchers[watcher_index];
    ixs_node *mod;
    assert(watcher->expr_index < b->nexprs);
    mod = b->exprs[watcher->expr_index].expr;
    assert(mod->tag == IXS_MOD && mod->u.binary.rhs->tag == IXS_INT &&
           mod->u.binary.rhs->u.ival > 0);
    incident[i].watcher_index = watcher_index;
    incident[i].modulus = mod->u.binary.rhs->u.ival;
    watcher_link = b->mod_inverse_watchers[watcher_index].next;
  }
  if (!bounds_refine_mod_inverse_sign(b, symbol->u.name, incident,
                                      incident_count)) {
    ixs_arena_restore(&b->query_arena, work_mark);
    return;
  }
  qsort(incident, incident_count, sizeof(*incident),
        bounds_mod_inverse_incident_compare);
  for (i = 0; i < incident_count && !b->oom && !b->contradiction; i++)
    (void)bounds_visit_mod_inverse_watcher(b, incident[i].watcher_index);
  ixs_arena_restore(&b->query_arena, work_mark);
}

static void bounds_refine_mod_inverse_for_expr(ixs_bounds *b, ixs_node *expr) {
  if (!b || !expr || b->oom)
    return;
  if (expr->tag == IXS_MOD && expr->u.binary.lhs->tag == IXS_SYM) {
    bounds_refine_mod_inverse_symbol(b, expr->u.binary.lhs);
    return;
  }
  if (expr->tag == IXS_SYM)
    bounds_refine_mod_inverse_symbol(b, expr);
}

static bool bounds_lift_floor_symbol_range(ixs_node *round,
                                           ixs_interval quotient,
                                           ixs_node **symbol,
                                           ixs_interval *lifted) {
  ixs_node *argument;
  int64_t coefficient_p;
  int64_t denominator;
  int64_t quotient_lower;
  int64_t quotient_upper;
  int64_t upper_successor;
  int64_t lower;
  int64_t upper;

  if (!round || round->tag != IXS_FLOOR || !quotient.valid || quotient.lo_inf ||
      quotient.hi_inf)
    return false;
  argument = round->u.unary.arg;
  if (argument->tag != IXS_MUL || argument->u.mul.nfactors != 1u ||
      argument->u.mul.factors[0].exp != 1 ||
      argument->u.mul.factors[0].base->tag != IXS_SYM)
    return false;
  ixs_node_get_rat(argument->u.mul.coeff, &coefficient_p, &denominator);
  if (coefficient_p != 1 || denominator <= 0)
    return false;
  *symbol = argument->u.mul.factors[0].base;
  if (!ixs_node_is_integer_valued(*symbol))
    return false;
  quotient_lower = ixs_rat_ceil(quotient.lo_p, quotient.lo_q);
  quotient_upper = ixs_rat_floor(quotient.hi_p, quotient.hi_q);
  if (quotient_lower > quotient_upper ||
      !ixs_safe_mul(quotient_lower, denominator, &lower) ||
      !ixs_safe_add(quotient_upper, 1, &upper_successor) ||
      !ixs_safe_mul(upper_successor, denominator, &upper) ||
      !ixs_safe_sub(upper, 1, &upper))
    return false;
  *lifted = ixs_interval_range(lower, 1, upper, 1);
  return true;
}

/* A finite range for floor(x/d), with raw integer x and positive literal d,
 * maps back to the exact inclusive integer band for x. */
static void bounds_refine_symbol_from_floor_range(ixs_bounds *b,
                                                  ixs_node *round,
                                                  ixs_interval quotient) {
  ixs_node *symbol;
  ixs_var_bound *var;
  ixs_interval original;
  ixs_interval lifted;
  ixs_interval refined;

  if (!b || !bounds_lift_floor_symbol_range(round, quotient, &symbol, &lifted))
    return;
  var = bounds_store_get_or_create_var(b, symbol->u.name);
  if (!var)
    return;
  original = var->iv;
  refined = iv_intersect(original, lifted);
  if (!refined.valid || ixs_interval_is_empty(refined) ||
      ixs_interval_equal(original, refined))
    return;
  (void)bounds_store_set_var_interval(b, var, refined);
  bounds_store_refine_var_bits(b, var);
  bounds_store_add_expr_raw(b, symbol, refined);
  if (!b->oom)
    bounds_difference_propagate_symbol(b, symbol->u.name);
  if (!b->oom && !b->contradiction)
    bounds_refine_mod_inverse_symbol(b, symbol);
}

static void bounds_sync_raw_symbol_range(ixs_bounds *b, ixs_node *symbol) {
  ixs_var_bound *var;
  ixs_interval stored;
  ixs_interval refined;
  if (!b || !symbol || symbol->tag != IXS_SYM || b->oom)
    return;
  stored = bounds_store_expr_interval(b, symbol);
  if (!stored.valid)
    return;
  var = bounds_store_get_or_create_var(b, symbol->u.name);
  if (!var)
    return;
  refined = iv_intersect(var->iv, stored);
  if (ixs_interval_equal(var->iv, refined))
    return;
  (void)bounds_store_set_var_interval(b, var, refined);
  bounds_store_invalidate_reads(b);
  bounds_store_refine_var_bits(b, var);
}

static bool bounds_propagate_added_expr_ranges(ixs_bounds *b, ixs_node *expr,
                                               ixs_node *canon, ixs_interval iv,
                                               size_t first_expr,
                                               size_t added_expr_end) {
  size_t i;

  for (i = first_expr; i < added_expr_end; i++)
    if (b->exprs[i].expr->tag == IXS_SYM && b->exprs[i].expr != expr &&
        b->exprs[i].expr != canon)
      bounds_sync_raw_symbol_range(b, b->exprs[i].expr);
  if (expr->tag == IXS_SYM)
    bounds_sync_raw_symbol_range(b, expr);
  if (canon && canon != expr && canon->tag == IXS_SYM)
    bounds_sync_raw_symbol_range(b, canon);
  if (b->oom || b->contradiction)
    return false;
  bounds_difference_add_range(b, expr, iv);
  if (canon && canon != expr)
    bounds_difference_add_range(b, canon, iv);
  if (b->oom || b->contradiction)
    return false;
  if (expr->tag == IXS_SYM)
    bounds_difference_propagate_symbol(b, expr->u.name);
  if (canon && canon != expr && canon->tag == IXS_SYM)
    bounds_difference_propagate_symbol(b, canon->u.name);
  return !b->oom && !b->contradiction;
}

IXS_STATIC void ixs_bounds_add_expr(ixs_bounds *b, ixs_node *expr,
                                    ixs_interval iv) {
  ixs_node *canon = NULL;
  size_t first_expr = b ? b->nexprs : 0u;
  size_t added_expr_end;
  size_t i;
  bounds_store_add_expr_raw(b, expr, iv);
  if (b->oom)
    return;
  bounds_add_proportional_range(b, expr, iv);
  if (b->oom)
    return;
  canon = bounds_canonical_expr(b, expr);
  if (canon && canon != expr) {
    bounds_store_add_expr_raw(b, canon, iv);
    if (!b->oom)
      bounds_add_proportional_range(b, canon, iv);
  }
  if (b->oom || b->contradiction)
    return;
  added_expr_end = b->nexprs;
  if (!bounds_propagate_added_expr_ranges(b, expr, canon, iv, first_expr,
                                          added_expr_end))
    return;
  for (i = first_expr; i < added_expr_end; i++)
    if (b->exprs[i].expr != expr && b->exprs[i].expr != canon)
      bounds_refine_mod_inverse_for_expr(b, b->exprs[i].expr);
  bounds_refine_mod_inverse_for_expr(b, expr);
  if (canon && canon != expr)
    bounds_refine_mod_inverse_for_expr(b, canon);
  if (b->oom || b->contradiction)
    return;
  if (expr->tag == IXS_FLOOR)
    bounds_refine_symbol_from_floor_range(b, expr,
                                          bounds_store_expr_interval(b, expr));
  if (canon && canon != expr && canon->tag == IXS_FLOOR)
    bounds_refine_symbol_from_floor_range(b, canon,
                                          bounds_store_expr_interval(b, canon));
}

/* apply_sym_cmp_const has already intersected the raw symbol table and
 * propagated difference constraints.  Record the parallel expression range
 * without repeating those operations on the assumption-ingestion hot path. */
static void bounds_record_applied_symbol_range(ixs_bounds *b, ixs_node *symbol,
                                               ixs_interval iv) {
  assert(symbol != NULL && symbol->tag == IXS_SYM);
  bounds_store_add_expr_raw(b, symbol, iv);
  if (!b->oom && !b->contradiction)
    bounds_refine_mod_inverse_symbol(b, symbol);
}

static void bounds_add_nonzero_product_bases(ixs_bounds *b, ixs_node *expr) {
  uint32_t i;
  if (!b || !expr || b->oom || expr->tag != IXS_MUL)
    return;
  for (i = 0; i < expr->u.mul.nfactors; i++) {
    const ixs_mulfactor *factor = &expr->u.mul.factors[i];
    ixs_node *canonical;
    if (factor->exp <= 0)
      continue;
    bounds_store_add_nonzero(b, factor->base);
    if (b->oom)
      return;
    canonical = bounds_canonical_expr(b, factor->base);
    if (canonical && canonical != factor->base &&
        !ixs_node_is_sentinel(canonical))
      bounds_store_add_nonzero(b, canonical);
    if (b->oom)
      return;
  }
}

IXS_STATIC void bounds_add_nonzero(ixs_bounds *b, ixs_node *expr) {
  ixs_node *canonical;
  if (!b || !expr || b->oom)
    return;
  bounds_store_add_nonzero(b, expr);
  if (b->oom || (expr->tag != IXS_MUL && expr->tag != IXS_PIECEWISE))
    return;

  canonical = bounds_canonical_expr(b, expr);
  if (b->oom)
    return;
  if (canonical && canonical != expr && !ixs_node_is_sentinel(canonical))
    bounds_store_add_nonzero(b, canonical);
  if (b->oom)
    return;

  bounds_add_nonzero_product_bases(b, expr);
  if (canonical && canonical != expr && !ixs_node_is_sentinel(canonical))
    bounds_add_nonzero_product_bases(b, canonical);
}

/*
 * Extract interval bounds and modular congruence from a comparison.
 * Patterns: sym >= 0, sym < N, Mod(sym, M) == R, etc.
 */
static bool bounds_add_sym_cmp_const(ixs_bounds *b, ixs_node *lhs,
                                     ixs_node *rhs, ixs_cmp_op op) {
  ixs_node *sym;
  ixs_node *constant;
  ixs_cmp_op effective_op;
  ixs_interval sym_iv;
  int64_t p;
  int64_t q;

  if (lhs->tag == IXS_SYM && ixs_node_is_const(rhs)) {
    sym = lhs;
    constant = rhs;
    effective_op = op;
  } else if (rhs->tag == IXS_SYM && ixs_node_is_const(lhs)) {
    sym = rhs;
    constant = lhs;
    effective_op = flip_cmp(op);
  } else {
    return false;
  }

  ixs_node_get_rat(constant, &p, &q);
  apply_sym_cmp_const(b, sym->u.name, effective_op, p, q);
  sym_iv = interval_from_sym_cmp_const(effective_op, p, q);
  if (sym_iv.valid)
    bounds_record_applied_symbol_range(b, sym, sym_iv);
  return true;
}

static bool bounds_add_affine_zero_cmp(ixs_bounds *b, ixs_node *lhs,
                                       ixs_node *rhs, ixs_cmp_op op) {
  ixs_node *sym;
  ixs_cmp_op effective_op;
  ixs_interval sym_iv;
  int64_t tp;
  int64_t tq;
  int64_t kp;
  int64_t kq;
  int64_t np;
  int64_t nq;
  int64_t raw_p;
  int64_t raw_q;
  int64_t p;
  int64_t q;

  if (!ixs_node_is_zero(rhs) || lhs->tag != IXS_ADD || lhs->u.add.nterms != 1 ||
      lhs->u.add.terms[0].term->tag != IXS_SYM)
    return false;

  sym = lhs->u.add.terms[0].term;
  ixs_node_get_rat(lhs->u.add.terms[0].coeff, &tp, &tq);
  ixs_node_get_rat(lhs->u.add.coeff, &kp, &kq);

  /* tp/tq * sym + kp/kq OP 0, so divide -kp/kq by tp/tq. */
  if (tp == 0 || !ixs_rat_neg(kp, kq, &np, &nq) ||
      !ixs_rat_mul(np, nq, tq, tp, &raw_p, &raw_q) ||
      !ixs_rat_normalize(raw_p, raw_q, &p, &q))
    return true;

  effective_op = (ixs_rat_cmp(tp, tq, 0, 1) < 0) ? flip_cmp(op) : op;
  apply_sym_cmp_const(b, sym->u.name, effective_op, p, q);
  sym_iv = interval_from_sym_cmp_const(effective_op, p, q);
  if (sym_iv.valid)
    bounds_record_applied_symbol_range(b, sym, sym_iv);
  return true;
}

static void bounds_add_assumption_impl(ixs_bounds *b, ixs_node *a) {
  ixs_node *equality_lhs;
  ixs_node *equality_rhs;
  int64_t equality_offset;
  ixs_node *lhs;
  ixs_node *rhs;
  ixs_cmp_op op;

  if (a->tag != IXS_CMP)
    return;
  bounds_store_invalidate_reads(b);

  extract_modrem(b, a);
  extract_bitfacts(b, a);

  lhs = a->u.binary.lhs;
  rhs = a->u.binary.rhs;
  op = a->u.binary.cmp_op;

  if (op == IXS_CMP_EQ) {
    if (bounds_extract_cmp_exact_relation(b, a, &equality_lhs, &equality_rhs,
                                          &equality_offset)) {
      bounds_admit_exact_relation(b, equality_lhs, equality_rhs,
                                  equality_offset);
    } else if (!b->oom &&
               extract_cmp_node_equality(a, &equality_lhs, &equality_rhs)) {
      bounds_admit_exact_relation(b, equality_lhs, equality_rhs, 0);
    }
    if (b->oom || b->contradiction)
      return;
  }

  if (op == IXS_CMP_NE) {
    if (ixs_node_is_zero(rhs))
      bounds_add_nonzero(b, lhs);
    else if (ixs_node_is_zero(lhs))
      bounds_add_nonzero(b, rhs);
  }

  if (bounds_add_sym_cmp_const(b, lhs, rhs, op))
    return;

  if (bounds_add_affine_zero_cmp(b, lhs, rhs, op))
    return;

  /* Fallback: expr op 0 for non-symbol lhs. Store as expression bound. */
  if (ixs_node_is_zero(rhs)) {
    add_expr_integer_zero_cmp(b, lhs, op);
  } else if (ixs_bounds_check_defined(b, lhs) == IXS_CHECK_TRUE &&
             ixs_bounds_check_defined(b, rhs) == IXS_CHECK_TRUE) {
    ixs_node *difference = simp_sub(b->ctx, lhs, rhs);
    if (!difference) {
      b->oom = true;
      return;
    }
    if (!ixs_node_is_sentinel(difference))
      add_expr_integer_zero_cmp(b, difference, op);
  }
}

IXS_STATIC bool ixs_bounds_add_assumption(ixs_bounds *b, ixs_node *a) {
  if (!b || !a || b->oom)
    return false;
  bounds_add_assumption_impl(b, a);
  return !b->oom;
}

IXS_STATIC ixs_interval bounds_assume_get_proportional_range(ixs_bounds *b,
                                                             ixs_node *expr) {
  ixs_node *primitive, *canonical;
  ixs_interval primitive_iv;
  int64_t scale_p, scale_q, offset_p, offset_q;
  if (!bounds_get_proportional_primitive(b, expr, &primitive, &scale_p,
                                         &scale_q, &offset_p, &offset_q) ||
      (primitive == expr && scale_p == 1 && scale_q == 1 && offset_p == 0))
    return ixs_interval_unknown();
  primitive_iv = bounds_store_expr_interval(b, primitive);
  canonical = bounds_canonical_expr(b, primitive);
  if (canonical && canonical != primitive)
    primitive_iv =
        iv_intersect(primitive_iv, bounds_store_expr_interval(b, canonical));
  if (!primitive_iv.valid)
    return ixs_interval_unknown();
  return bounds_apply_affine(primitive_iv, scale_p, scale_q, offset_p,
                             offset_q);
}

IXS_STATIC ixs_bounds_build_status assumption_invalid(ixs_bounds *b,
                                                      const char *message) {
  if (b && b->ctx)
    ixs_ctx_push_error(b->ctx, "assumptions: %s", message);
  return IXS_BOUNDS_BUILD_INVALID;
}

static bool assumption_cmp_op_valid(ixs_cmp_op op) {
  switch (op) {
  case IXS_CMP_GT:
  case IXS_CMP_GE:
  case IXS_CMP_LT:
  case IXS_CMP_LE:
  case IXS_CMP_EQ:
  case IXS_CMP_NE:
    return true;
  }
  return false;
}

static void bounds_ingest_validated_leaf(ixs_bounds *b, ixs_node *pred,
                                         bool ingest) {
  if (!ingest)
    return;
  if (pred == b->ctx->node_false) {
    bounds_store_mark_contradiction(b);
    bounds_store_invalidate_reads(b);
    return;
  }
  (void)ixs_bounds_add_assumption(b, pred);
}

typedef struct {
  ixs_node *node;
  bool active;
  bool complete;
} assumption_memo_entry;

typedef struct {
  ixs_node *node;
  uint32_t next_child;
  uint32_t nchildren;
  bool started;
} assumption_predicate_frame;

typedef struct {
  ixs_bounds *bounds;
  ixs_arena *arena;
  ixs_query_walk walk;
  ixs_query_node_memo memo;
  ixs_node **leaves;
  size_t leaf_count;
  size_t leaf_capacity;
  ixs_bounds_build_status status;
  bool oom;
} assumption_predicate_query;

static ixs_bounds_build_status bounds_validate_cmp_leaf(ixs_bounds *b,
                                                        ixs_node *cmp) {
  ixs_node *lhs = cmp->u.binary.lhs;
  ixs_node *rhs = cmp->u.binary.rhs;
  if (!lhs || !rhs || !assumption_cmp_op_valid(cmp->u.binary.cmp_op))
    return assumption_invalid(b, "malformed CMP predicate");
  if (!ixs_ctx_owns_node(b->ctx, lhs) || !ixs_ctx_owns_node(b->ctx, rhs))
    return assumption_invalid(b, "CMP child belongs to a different context");
  if (ixs_node_is_sentinel(lhs) || ixs_node_is_sentinel(rhs))
    return assumption_invalid(b, "sentinel CMP children are not accepted");
  return IXS_BOUNDS_BUILD_OK;
}

static ixs_bounds_build_status bounds_start_predicate_frame(
    ixs_bounds *b, ixs_arena *traversal, assumption_predicate_frame *frame,
    ixs_node ***leaves, size_t *leaf_count, size_t *leaf_capacity) {
  ixs_node *cur = frame->node;
  ixs_bounds_build_status status;
  frame->started = true;
  if (!cur)
    return assumption_invalid(b, "NULL predicate child");
  if (!ixs_ctx_owns_node(b->ctx, cur))
    return assumption_invalid(b, "predicate belongs to a different context");
  if (ixs_node_is_sentinel(cur))
    return assumption_invalid(b, "sentinel predicates are not accepted");
  if (cur == b->ctx->node_true) {
    frame->nchildren = 0u;
    return IXS_BOUNDS_BUILD_OK;
  }
  if (cur == b->ctx->node_false) {
    frame->nchildren = 0u;
  } else if (cur->tag == IXS_CMP) {
    status = bounds_validate_cmp_leaf(b, cur);
    if (status != IXS_BOUNDS_BUILD_OK)
      return status;
    frame->nchildren = 0u;
  } else if (cur->tag == IXS_AND) {
    if (cur->u.assoc.nargs < 2 || !cur->u.assoc.args)
      return assumption_invalid(b, "malformed AND predicate");
    frame->nchildren = cur->u.assoc.nargs;
    return IXS_BOUNDS_BUILD_OK;
  } else if (cur->tag == IXS_OR) {
    return assumption_invalid(b, "OR predicates are not supported");
  } else if (cur->tag == IXS_NOT) {
    return assumption_invalid(b, "NOT predicates are not supported");
  } else {
    return assumption_invalid(
        b, "expected a CMP, AND, or boolean constant predicate");
  }
  return ixs_query_node_vector_push(traversal, leaves, leaf_count,
                                    leaf_capacity, cur, 32u)
             ? IXS_BOUNDS_BUILD_OK
             : IXS_BOUNDS_BUILD_OOM;
}

/* hot */
static ixs_query_walk_step assumption_predicate_advance(void *state,
                                                        void *top) {
  assumption_predicate_query *query = state;
  assumption_predicate_frame *frame = top;
  assumption_memo_entry *entry;
  ixs_node *child;
  if (!frame->started) {
    query->status = bounds_start_predicate_frame(
        query->bounds, query->arena, frame, &query->leaves, &query->leaf_count,
        &query->leaf_capacity);
    if (query->status != IXS_BOUNDS_BUILD_OK)
      return query->status == IXS_BOUNDS_BUILD_OOM ? IXS_QUERY_WALK_OOM
                                                   : IXS_QUERY_WALK_STOP;
  }
  if (frame->next_child < frame->nchildren) {
    child = frame->node->u.assoc.args[frame->next_child++];
    if (!child) {
      query->status = assumption_invalid(query->bounds, "NULL predicate child");
      return IXS_QUERY_WALK_STOP;
    }
    entry = ixs_query_node_memo_get(&query->memo, child, true);
    if (!entry) {
      query->status = IXS_BOUNDS_BUILD_OOM;
      return IXS_QUERY_WALK_OOM;
    }
    if (entry->active) {
      query->status =
          assumption_invalid(query->bounds, "cyclic predicate tree");
      return IXS_QUERY_WALK_STOP;
    }
    if (entry->complete)
      return IXS_QUERY_WALK_ADVANCED;
    entry->active = true;
    return ixs_query_walk_push(&query->walk, child);
  }
  entry = ixs_query_node_memo_get(&query->memo, frame->node, false);
  if (!entry || !entry->active) {
    query->status =
        assumption_invalid(query->bounds, "invalid predicate traversal state");
    return IXS_QUERY_WALK_STOP;
  }
  entry->active = false;
  entry->complete = true;
  IXS_QUERY_WALK_POP(&query->walk);
  return IXS_QUERY_WALK_ADVANCED;
}

/* False means the validated root is an AND and needs the iterative walker. */
static bool bounds_process_flat_predicate(ixs_bounds *b, ixs_node *pred,
                                          bool ingest,
                                          ixs_bounds_build_status *status) {
  if (!pred)
    *status = assumption_invalid(b, "NULL predicate");
  else if (!ixs_ctx_owns_node(b->ctx, pred))
    *status = assumption_invalid(b, "predicate belongs to a different context");
  else if (ixs_node_is_sentinel(pred))
    *status = assumption_invalid(b, "sentinel predicates are not accepted");
  else if (pred == b->ctx->node_true)
    *status = IXS_BOUNDS_BUILD_OK;
  else if (pred == b->ctx->node_false) {
    bounds_ingest_validated_leaf(b, pred, ingest);
    *status = b->oom ? IXS_BOUNDS_BUILD_OOM : IXS_BOUNDS_BUILD_OK;
  } else if (pred->tag == IXS_CMP) {
    *status = bounds_validate_cmp_leaf(b, pred);
    if (*status == IXS_BOUNDS_BUILD_OK) {
      bounds_ingest_validated_leaf(b, pred, ingest);
      *status = b->oom ? IXS_BOUNDS_BUILD_OOM : IXS_BOUNDS_BUILD_OK;
    }
  } else if (pred->tag == IXS_AND) {
    return false;
  } else if (pred->tag == IXS_OR) {
    *status = assumption_invalid(b, "OR predicates are not supported");
  } else if (pred->tag == IXS_NOT) {
    *status = assumption_invalid(b, "NOT predicates are not supported");
  } else {
    *status = assumption_invalid(
        b, "expected a CMP, AND, or boolean constant predicate");
  }
  return true;
}

static ixs_bounds_build_status
bounds_process_predicate(ixs_bounds *b, ixs_node *pred, bool ingest) {
  ixs_arena traversal;
  assumption_predicate_query query;
  assumption_memo_entry *entry;
  ixs_query_walk_step step;
  size_t i;
  ixs_bounds_build_status status = IXS_BOUNDS_BUILD_OK;

  /* Published assumptions are almost always individual CMP leaves.  Validate
   * those without constructing the growable cycle-detection worklist needed
   * only for AND DAGs. */
  if (bounds_process_flat_predicate(b, pred, ingest, &status))
    return status;

  assert(pred != NULL && pred->tag == IXS_AND);

  ixs_arena_init(&traversal, IXS_ARENA_DEFAULT_SIZE);
  memset(&query, 0, sizeof(query));
  query.bounds = b;
  query.arena = &traversal;
  query.status = IXS_BOUNDS_BUILD_OK;
  IXS_QUERY_NODE_MEMO_INIT(&query.memo, &traversal, assumption_memo_entry,
                           node);
  IXS_QUERY_WALK_INIT_CAP(&query.walk, &traversal, &query.oom,
                          assumption_predicate_frame, node, 32u);
  entry = ixs_query_node_memo_get(&query.memo, pred, true);
  if (!entry ||
      ixs_query_walk_push(&query.walk, pred) != IXS_QUERY_WALK_ADVANCED) {
    status = IXS_BOUNDS_BUILD_OOM;
    goto cleanup;
  }
  entry->active = true;
  step = ixs_query_walk_drive(&query.walk, &query, assumption_predicate_advance,
                              NULL);
  status = query.status;
  if (step == IXS_QUERY_WALK_OOM)
    status = IXS_BOUNDS_BUILD_OOM;
  for (i = 0; status == IXS_BOUNDS_BUILD_OK && ingest && i < query.leaf_count;
       i++) {
    bounds_ingest_validated_leaf(b, query.leaves[i], true);
    if (b->oom) {
      status = IXS_BOUNDS_BUILD_OOM;
      break;
    }
  }

cleanup:
  ixs_arena_destroy_transient(&traversal);
  return status;
}

IXS_STATIC ixs_bounds_build_status
bounds_assume_validate_predicate(ixs_bounds *b, ixs_node *pred) {
  return bounds_process_predicate(b, pred, false);
}

IXS_STATIC ixs_bounds_build_status
bounds_assume_ingest_predicate(ixs_bounds *b, ixs_node *pred) {
  ixs_bounds_build_status status;
  bool query_held = false;
  /* One published predicate owns the complete proof scope used while its CMP
   * leaves are ingested.  Synthetic branch assumptions are added below an
   * already-active Piecewise scope and therefore do not enter here. */
  if (!ixs_bounds_query_hold_begin(b, pred, &query_held))
    return b && b->oom ? IXS_BOUNDS_BUILD_OOM : IXS_BOUNDS_BUILD_LIMIT;
  status = bounds_process_predicate(b, pred, true);
  if (query_held)
    ixs_bounds_query_hold_end(b);
  return status;
}

IXS_STATIC ixs_bounds_build_status bounds_assume_validate_predicates(
    ixs_bounds *b, ixs_node *const *predicates, size_t n_predicates) {
  size_t i;
  ixs_bounds_build_status status;

  if (n_predicates > 0 && !predicates)
    return assumption_invalid(b, "NULL array with nonzero count");
  for (i = 0; i < n_predicates; i++) {
    status = bounds_assume_validate_predicate(b, predicates[i]);
    if (status != IXS_BOUNDS_BUILD_OK)
      return status;
  }
  return IXS_BOUNDS_BUILD_OK;
}

IXS_STATIC ixs_bounds_build_status bounds_assume_ingest_predicates(
    ixs_bounds *b, ixs_node *const *predicates, size_t n_predicates) {
  size_t i;
  ixs_bounds_build_status status;

  if (n_predicates > 0 && !predicates)
    return assumption_invalid(b, "NULL array with nonzero count");
  for (i = 0; i < n_predicates; i++) {
    status = bounds_assume_ingest_predicate(b, predicates[i]);
    if (status != IXS_BOUNDS_BUILD_OK)
      return status;
  }
  return IXS_BOUNDS_BUILD_OK;
}

IXS_STATIC bool bounds_extract_integer_affine(ixs_node *expr, const char **name,
                                              int64_t *scale, int64_t *offset) {
  int64_t p, q;
  if (!expr || !name || !scale || !offset)
    return false;
  if (expr->tag == IXS_SYM) {
    *name = expr->u.name;
    *scale = 1;
    *offset = 0;
    return true;
  }
  if (expr->tag == IXS_MUL && expr->u.mul.nfactors == 1 &&
      expr->u.mul.factors[0].exp == 1 &&
      expr->u.mul.factors[0].base->tag == IXS_SYM) {
    ixs_node_get_rat(expr->u.mul.coeff, &p, &q);
    if (q != 1 || p == 0)
      return false;
    *name = expr->u.mul.factors[0].base->u.name;
    *scale = p;
    *offset = 0;
    return true;
  }
  if (expr->tag == IXS_ADD && expr->u.add.nterms == 1 &&
      expr->u.add.terms[0].term->tag == IXS_SYM) {
    ixs_node_get_rat(expr->u.add.coeff, offset, &q);
    if (q != 1)
      return false;
    ixs_node_get_rat(expr->u.add.terms[0].coeff, scale, &q);
    if (q != 1 || *scale == 0)
      return false;
    *name = expr->u.add.terms[0].term->u.name;
    return true;
  }
  return false;
}

IXS_STATIC ixs_bounds_build_status
ixs_bounds_build_ctx(ixs_bounds *b, ixs_ctx *ctx, ixs_arena *scratch,
                     ixs_node *const *assumptions, size_t n_assumptions) {
  ixs_bounds_cache_entry *interval_cache;
  ixs_bounds_build_status status;
  if (n_assumptions > 0 && !assumptions) {
    ixs_ctx_push_error(ctx, "assumptions: NULL array with nonzero count");
    return IXS_BOUNDS_BUILD_INVALID;
  }
  if (!ixs_bounds_init_ctx(b, ctx, scratch))
    return IXS_BOUNDS_BUILD_OOM;
  /* A fresh bounds object has no interval result to invalidate while its
   * assumptions are loaded.  Keep the zeroed query cache detached so each
   * published fact does not clear the same empty table. */
  interval_cache = b->cache;
  b->cache = NULL;
  status = bounds_assume_ingest_predicates(b, assumptions, n_assumptions);
  b->cache = interval_cache;
  if (status != IXS_BOUNDS_BUILD_OK)
    ixs_bounds_destroy(b);
  return status;
}
