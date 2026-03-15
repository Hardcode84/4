/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds.h"
#include <limits.h>
#include <string.h>

#ifndef INT64_MIN
#define INT64_MIN (-9223372036854775807LL - 1)
#endif
#ifndef INT64_MAX
#define INT64_MAX 9223372036854775807LL
#endif

#define BOUNDS_INIT_CAP 16

bool ixs_bounds_init(ixs_bounds *b, ixs_arena *scratch) {
  b->scratch = scratch;
  b->nvars = 0;
  b->cap = BOUNDS_INIT_CAP;
  b->vars = ixs_arena_alloc(scratch, BOUNDS_INIT_CAP * sizeof(*b->vars),
                            sizeof(void *));
  b->nexprs = 0;
  b->expr_cap = 0;
  b->exprs = NULL;
  return b->vars != NULL;
}

void ixs_bounds_destroy(ixs_bounds *b) { (void)b; }

bool ixs_bounds_fork(ixs_bounds *dst, const ixs_bounds *src) {
  dst->scratch = src->scratch;
  dst->nvars = src->nvars;
  dst->cap = src->nvars ? src->nvars : 1;
  dst->vars = ixs_arena_alloc(dst->scratch, dst->cap * sizeof(*dst->vars),
                              sizeof(void *));
  if (!dst->vars)
    return false;
  if (src->nvars)
    memcpy(dst->vars, src->vars, src->nvars * sizeof(*src->vars));
  dst->nexprs = src->nexprs;
  dst->expr_cap = src->nexprs ? src->nexprs : 0;
  dst->exprs = NULL;
  if (src->nexprs) {
    dst->exprs = ixs_arena_alloc(
        dst->scratch, dst->expr_cap * sizeof(*dst->exprs), sizeof(void *));
    if (!dst->exprs)
      return false;
    memcpy(dst->exprs, src->exprs, src->nexprs * sizeof(*src->exprs));
  }
  return true;
}

static ixs_var_bound *find_var(ixs_bounds *b, const char *name) {
  size_t i;
  if (!b->vars)
    return NULL;
  for (i = 0; i < b->nvars; i++) {
    if (b->vars[i].name == name)
      return &b->vars[i];
  }
  return NULL;
}

static ixs_var_bound *get_or_create_var(ixs_bounds *b, const char *name) {
  ixs_var_bound *v = find_var(b, name);
  if (v)
    return v;
  if (!b->vars)
    return NULL;
  if (b->nvars >= b->cap) {
    b->vars = ixs_arena_grow(b->scratch, b->vars, b->cap * sizeof(*b->vars),
                             b->cap * 2 * sizeof(*b->vars), sizeof(void *));
    if (!b->vars)
      return NULL;
    b->cap *= 2;
  }
  v = &b->vars[b->nvars++];
  v->name = name;
  v->iv.valid = true;
  v->iv.lo_p = INT64_MIN;
  v->iv.lo_q = 1;
  v->iv.hi_p = INT64_MAX;
  v->iv.hi_q = 1;
  v->divisor = 0;
  return v;
}

/* Record that sym is divisible by d (combine with lcm if existing). */
static void apply_divisor(ixs_bounds *b, const char *name, int64_t d) {
  ixs_var_bound *v = get_or_create_var(b, name);
  if (!v)
    return;
  if (v->divisor == 0) {
    v->divisor = d;
  } else {
    int64_t g = ixs_gcd(v->divisor, d);
    if (g > 0 && v->divisor <= INT64_MAX / (d / g))
      v->divisor = v->divisor / g * d;
  }
}

/* Recognize Mod(sym, const) == 0 as a divisibility assumption. */
static void extract_divisibility(ixs_bounds *b, ixs_node *a) {
  ixs_node *mod_node;

  if (a->tag != IXS_CMP || a->u.binary.cmp_op != IXS_CMP_EQ)
    return;

  if (a->u.binary.lhs->tag == IXS_MOD && ixs_node_is_zero(a->u.binary.rhs))
    mod_node = a->u.binary.lhs;
  else if (a->u.binary.rhs->tag == IXS_MOD && ixs_node_is_zero(a->u.binary.lhs))
    mod_node = a->u.binary.rhs;
  else
    return;

  ixs_node *dividend = mod_node->u.binary.lhs;
  ixs_node *modulus = mod_node->u.binary.rhs;
  if (dividend->tag == IXS_SYM && modulus->tag == IXS_INT &&
      modulus->u.ival > 0)
    apply_divisor(b, dividend->u.name, modulus->u.ival);
}

/*
 * Extract interval bounds and divisibility info from a comparison.
 * Patterns: sym >= 0, sym < N, Mod(sym, d) == 0, etc.
 */
void ixs_bounds_add_assumption(ixs_bounds *b, ixs_node *a) {
  if (a->tag != IXS_CMP)
    return;

  extract_divisibility(b, a);

  ixs_node *lhs = a->u.binary.lhs;
  ixs_node *rhs = a->u.binary.rhs;
  ixs_cmp_op op = a->u.binary.cmp_op;
  ixs_var_bound *v;

  /* Pattern: sym op const */
  if (lhs->tag == IXS_SYM && ixs_node_is_const(rhs)) {
    int64_t rp, rq;
    ixs_node_get_rat(rhs, &rp, &rq);
    v = get_or_create_var(b, lhs->u.name);
    if (!v)
      return;
    switch (op) {
    case IXS_CMP_GE:
      if (ixs_rat_cmp(rp, rq, v->iv.lo_p, v->iv.lo_q) > 0) {
        v->iv.lo_p = rp;
        v->iv.lo_q = rq;
      }
      break;
    case IXS_CMP_GT: {
      /* sym > p/q -> sym >= floor(p/q) + 1 (integer-valued sym) */
      int64_t lo = ixs_rat_floor(rp, rq) + 1;
      if (ixs_rat_cmp(lo, 1, v->iv.lo_p, v->iv.lo_q) > 0) {
        v->iv.lo_p = lo;
        v->iv.lo_q = 1;
      }
      break;
    }
    case IXS_CMP_LE:
      if (ixs_rat_cmp(rp, rq, v->iv.hi_p, v->iv.hi_q) < 0) {
        v->iv.hi_p = rp;
        v->iv.hi_q = rq;
      }
      break;
    case IXS_CMP_LT: {
      /* sym < p/q -> sym <= ceil(p/q) - 1 (integer-valued sym) */
      int64_t hi = ixs_rat_ceil(rp, rq) - 1;
      if (ixs_rat_cmp(hi, 1, v->iv.hi_p, v->iv.hi_q) < 0) {
        v->iv.hi_p = hi;
        v->iv.hi_q = 1;
      }
      break;
    }
    case IXS_CMP_EQ:
      v->iv.lo_p = rp;
      v->iv.lo_q = rq;
      v->iv.hi_p = rp;
      v->iv.hi_q = rq;
      break;
    case IXS_CMP_NE:
      break;
    }
    return;
  }

  /* Pattern: const op sym (flip) */
  if (rhs->tag == IXS_SYM && ixs_node_is_const(lhs)) {
    int64_t lp, lq;
    ixs_node_get_rat(lhs, &lp, &lq);
    v = get_or_create_var(b, rhs->u.name);
    if (!v)
      return;
    switch (op) {
    case IXS_CMP_GE: /* const >= sym -> sym <= const */
      if (ixs_rat_cmp(lp, lq, v->iv.hi_p, v->iv.hi_q) < 0) {
        v->iv.hi_p = lp;
        v->iv.hi_q = lq;
      }
      break;
    case IXS_CMP_GT: {
      /* const > sym -> sym <= ceil(const) - 1 */
      int64_t hi = ixs_rat_ceil(lp, lq) - 1;
      if (ixs_rat_cmp(hi, 1, v->iv.hi_p, v->iv.hi_q) < 0) {
        v->iv.hi_p = hi;
        v->iv.hi_q = 1;
      }
      break;
    }
    case IXS_CMP_LE:
      if (ixs_rat_cmp(lp, lq, v->iv.lo_p, v->iv.lo_q) > 0) {
        v->iv.lo_p = lp;
        v->iv.lo_q = lq;
      }
      break;
    case IXS_CMP_LT: {
      /* const < sym -> sym >= floor(const) + 1 */
      int64_t lo = ixs_rat_floor(lp, lq) + 1;
      if (ixs_rat_cmp(lo, 1, v->iv.lo_p, v->iv.lo_q) > 0) {
        v->iv.lo_p = lo;
        v->iv.lo_q = 1;
      }
      break;
    }
    case IXS_CMP_EQ:
      v->iv.lo_p = lp;
      v->iv.lo_q = lq;
      v->iv.hi_p = lp;
      v->iv.hi_q = lq;
      break;
    case IXS_CMP_NE:
      break;
    }
    return;
  }

  /*
   * Pattern: (sym - const) cmp 0  (from comparison normalization).
   * The lhs is an ADD with one SYM term and a constant offset.
   */
  if (ixs_node_is_zero(rhs) && lhs->tag == IXS_ADD && lhs->u.add.nterms == 1 &&
      lhs->u.add.terms[0].term->tag == IXS_SYM) {
    int64_t tp, tq, kp, kq;
    ixs_node_get_rat(lhs->u.add.terms[0].coeff, &tp, &tq);
    ixs_node_get_rat(lhs->u.add.coeff, &kp, &kq);

    /* We have: tp/tq * sym + kp/kq  OP  0, i.e. sym OP' (-kp/kq) / (tp/tq).
     * Dividing by tp/tq flips the comparison when tp/tq < 0. */
    if (tp == 0)
      return;

    /* Compute bound = -k / c = (-kp/kq) / (tp/tq) = (-kp * tq) / (kq * tp) */
    int64_t np, nq;
    if (!ixs_rat_neg(kp, kq, &np, &nq))
      return;
    int64_t raw_p, raw_q;
    if (!ixs_rat_mul(np, nq, tq, tp, &raw_p, &raw_q))
      return;
    int64_t rp2, rq2;
    if (!ixs_rat_normalize(raw_p, raw_q, &rp2, &rq2))
      return;

    /* Negative coefficient flips the comparison direction */
    ixs_cmp_op eff_op = op;
    if (ixs_rat_cmp(tp, tq, 0, 1) < 0) {
      switch (op) {
      case IXS_CMP_GE:
        eff_op = IXS_CMP_LE;
        break;
      case IXS_CMP_GT:
        eff_op = IXS_CMP_LT;
        break;
      case IXS_CMP_LE:
        eff_op = IXS_CMP_GE;
        break;
      case IXS_CMP_LT:
        eff_op = IXS_CMP_GT;
        break;
      default:
        break;
      }
    }

    v = get_or_create_var(b, lhs->u.add.terms[0].term->u.name);
    if (!v)
      return;
    switch (eff_op) {
    case IXS_CMP_GE:
      if (ixs_rat_cmp(rp2, rq2, v->iv.lo_p, v->iv.lo_q) > 0) {
        v->iv.lo_p = rp2;
        v->iv.lo_q = rq2;
      }
      break;
    case IXS_CMP_GT: {
      int64_t lo = ixs_rat_floor(rp2, rq2) + 1;
      if (ixs_rat_cmp(lo, 1, v->iv.lo_p, v->iv.lo_q) > 0) {
        v->iv.lo_p = lo;
        v->iv.lo_q = 1;
      }
      break;
    }
    case IXS_CMP_LE:
      if (ixs_rat_cmp(rp2, rq2, v->iv.hi_p, v->iv.hi_q) < 0) {
        v->iv.hi_p = rp2;
        v->iv.hi_q = rq2;
      }
      break;
    case IXS_CMP_LT: {
      int64_t hi = ixs_rat_ceil(rp2, rq2) - 1;
      if (ixs_rat_cmp(hi, 1, v->iv.hi_p, v->iv.hi_q) < 0) {
        v->iv.hi_p = hi;
        v->iv.hi_q = 1;
      }
      break;
    }
    default: /* EQ/NE: not useful here; EQ already handled by sym-op-const */
      break;
    }
    return;
  }

  /* Fallback: expr op 0 for non-symbol lhs. Store as expression bound. */
  if (ixs_node_is_zero(rhs) && ixs_node_is_integer_valued(lhs) &&
      (op == IXS_CMP_GT || op == IXS_CMP_GE)) {
    ixs_expr_bound *eb;
    if (b->nexprs >= b->expr_cap) {
      size_t new_cap = b->expr_cap ? b->expr_cap * 2 : 4;
      ixs_expr_bound *new_arr = ixs_arena_alloc(
          b->scratch, new_cap * sizeof(*new_arr), sizeof(void *));
      if (!new_arr)
        return;
      if (b->nexprs)
        memcpy(new_arr, b->exprs, b->nexprs * sizeof(*b->exprs));
      b->exprs = new_arr;
      b->expr_cap = new_cap;
    }
    eb = &b->exprs[b->nexprs++];
    eb->expr = lhs;
    eb->iv.valid = true;
    eb->iv.hi_p = INT64_MAX;
    eb->iv.hi_q = 1;
    if (op == IXS_CMP_GT) {
      eb->iv.lo_p = 1;
      eb->iv.lo_q = 1;
    } else {
      eb->iv.lo_p = 0;
      eb->iv.lo_q = 1;
    }
  }
}

/* ------------------------------------------------------------------ */
/*  Interval propagation                                              */
/* ------------------------------------------------------------------ */

static ixs_interval iv_add(ixs_interval a, ixs_interval b) {
  ixs_interval r;
  if (!a.valid || !b.valid)
    return ixs_interval_unknown();
  r.valid = true;
  if (!ixs_rat_add(a.lo_p, a.lo_q, b.lo_p, b.lo_q, &r.lo_p, &r.lo_q))
    return ixs_interval_unknown();
  if (!ixs_rat_add(a.hi_p, a.hi_q, b.hi_p, b.hi_q, &r.hi_p, &r.hi_q))
    return ixs_interval_unknown();
  return r;
}

static ixs_interval iv_mul_const(ixs_interval a, int64_t cp, int64_t cq) {
  ixs_interval r;
  if (!a.valid)
    return ixs_interval_unknown();
  r.valid = true;
  if (!ixs_rat_mul(a.lo_p, a.lo_q, cp, cq, &r.lo_p, &r.lo_q) ||
      !ixs_rat_mul(a.hi_p, a.hi_q, cp, cq, &r.hi_p, &r.hi_q))
    return ixs_interval_unknown();
  /* If multiplier is negative, swap lo and hi. */
  if (ixs_rat_is_neg(cp)) {
    int64_t tmp_p = r.lo_p, tmp_q = r.lo_q;
    r.lo_p = r.hi_p;
    r.lo_q = r.hi_q;
    r.hi_p = tmp_p;
    r.hi_q = tmp_q;
  }
  return r;
}

static ixs_interval iv_intersect(ixs_interval a, ixs_interval b) {
  ixs_interval r;
  if (!a.valid)
    return b;
  if (!b.valid)
    return a;
  r.valid = true;
  if (ixs_rat_cmp(a.lo_p, a.lo_q, b.lo_p, b.lo_q) >= 0) {
    r.lo_p = a.lo_p;
    r.lo_q = a.lo_q;
  } else {
    r.lo_p = b.lo_p;
    r.lo_q = b.lo_q;
  }
  if (ixs_rat_cmp(a.hi_p, a.hi_q, b.hi_p, b.hi_q) <= 0) {
    r.hi_p = a.hi_p;
    r.hi_q = a.hi_q;
  } else {
    r.hi_p = b.hi_p;
    r.hi_q = b.hi_q;
  }
  return r;
}

static ixs_interval bounds_get_propagated(ixs_bounds *b, ixs_node *expr) {
  uint32_t i;
  if (!expr)
    return ixs_interval_unknown();

  switch (expr->tag) {
  case IXS_INT:
    return ixs_interval_exact(expr->u.ival, 1);
  case IXS_RAT:
    return ixs_interval_exact(expr->u.rat.p, expr->u.rat.q);
  case IXS_SYM: {
    ixs_var_bound *v = find_var(b, expr->u.name);
    if (v)
      return v->iv;
    return ixs_interval_unknown();
  }
  case IXS_ADD: {
    /* Start with constant term. */
    ixs_interval result = ixs_bounds_get(b, expr->u.add.coeff);
    for (i = 0; i < expr->u.add.nterms; i++) {
      ixs_interval ti = ixs_bounds_get(b, expr->u.add.terms[i].term);
      int64_t cp, cq;
      ixs_node_get_rat(expr->u.add.terms[i].coeff, &cp, &cq);
      ixs_interval scaled = iv_mul_const(ti, cp, cq);
      result = iv_add(result, scaled);
    }
    return result;
  }
  case IXS_MUL: {
    /* Only handle simple cases: const * single factor. */
    if (expr->u.mul.nfactors == 1 && expr->u.mul.factors[0].exp == 1) {
      int64_t cp, cq;
      ixs_node_get_rat(expr->u.mul.coeff, &cp, &cq);
      ixs_interval fi = ixs_bounds_get(b, expr->u.mul.factors[0].base);
      return iv_mul_const(fi, cp, cq);
    }
    return ixs_interval_unknown();
  }
  case IXS_MOD: {
    /* Mod(x, m) in [0, m-1] only when x is integer-valued and m is a
     * positive integer.  For non-integer dividends the range is the
     * half-open [0, m) which we cannot represent tightly. */
    ixs_node *m = expr->u.binary.rhs;
    if (m->tag == IXS_INT && m->u.ival > 0) {
      ixs_interval pi = ixs_bounds_get(b, expr->u.binary.lhs);
      if (pi.valid && pi.lo_q == 1 && pi.hi_q == 1 && pi.lo_p >= 0 &&
          pi.hi_p < m->u.ival)
        return pi;
      if (ixs_node_is_integer_valued(expr->u.binary.lhs))
        return ixs_interval_range(0, 1, m->u.ival - 1, 1);
    }
    return ixs_interval_unknown();
  }
  case IXS_FLOOR: {
    ixs_interval ai = ixs_bounds_get(b, expr->u.unary.arg);
    if (!ai.valid)
      return ixs_interval_unknown();
    return ixs_interval_range(ixs_rat_floor(ai.lo_p, ai.lo_q), 1,
                              ixs_rat_floor(ai.hi_p, ai.hi_q), 1);
  }
  case IXS_CEIL: {
    ixs_interval ai = ixs_bounds_get(b, expr->u.unary.arg);
    if (!ai.valid)
      return ixs_interval_unknown();
    return ixs_interval_range(ixs_rat_ceil(ai.lo_p, ai.lo_q), 1,
                              ixs_rat_ceil(ai.hi_p, ai.hi_q), 1);
  }
  case IXS_MAX: {
    ixs_interval li = ixs_bounds_get(b, expr->u.binary.lhs);
    ixs_interval ri = ixs_bounds_get(b, expr->u.binary.rhs);
    if (!li.valid || !ri.valid)
      return ixs_interval_unknown();
    ixs_interval result;
    result.valid = true;
    /* max(lo_l, lo_r) <= max(l, r) <= max(hi_l, hi_r) */
    result.lo_p = ixs_rat_cmp(li.lo_p, li.lo_q, ri.lo_p, ri.lo_q) >= 0
                      ? li.lo_p
                      : ri.lo_p;
    result.lo_q = ixs_rat_cmp(li.lo_p, li.lo_q, ri.lo_p, ri.lo_q) >= 0
                      ? li.lo_q
                      : ri.lo_q;
    result.hi_p = ixs_rat_cmp(li.hi_p, li.hi_q, ri.hi_p, ri.hi_q) >= 0
                      ? li.hi_p
                      : ri.hi_p;
    result.hi_q = ixs_rat_cmp(li.hi_p, li.hi_q, ri.hi_p, ri.hi_q) >= 0
                      ? li.hi_q
                      : ri.hi_q;
    return result;
  }
  case IXS_MIN: {
    ixs_interval li = ixs_bounds_get(b, expr->u.binary.lhs);
    ixs_interval ri = ixs_bounds_get(b, expr->u.binary.rhs);
    if (!li.valid || !ri.valid)
      return ixs_interval_unknown();
    ixs_interval result;
    result.valid = true;
    result.lo_p = ixs_rat_cmp(li.lo_p, li.lo_q, ri.lo_p, ri.lo_q) <= 0
                      ? li.lo_p
                      : ri.lo_p;
    result.lo_q = ixs_rat_cmp(li.lo_p, li.lo_q, ri.lo_p, ri.lo_q) <= 0
                      ? li.lo_q
                      : ri.lo_q;
    result.hi_p = ixs_rat_cmp(li.hi_p, li.hi_q, ri.hi_p, ri.hi_q) <= 0
                      ? li.hi_p
                      : ri.hi_p;
    result.hi_q = ixs_rat_cmp(li.hi_p, li.hi_q, ri.hi_p, ri.hi_q) <= 0
                      ? li.hi_q
                      : ri.hi_q;
    return result;
  }
  default:
    return ixs_interval_unknown();
  }
}

ixs_interval ixs_bounds_get(ixs_bounds *b, ixs_node *expr) {
  ixs_interval iv = bounds_get_propagated(b, expr);
  if (b->nexprs && expr) {
    size_t j;
    for (j = 0; j < b->nexprs; j++) {
      if (b->exprs[j].expr == expr)
        iv = iv_intersect(iv, b->exprs[j].iv);
    }
  }
  return iv;
}

int64_t ixs_bounds_get_divisor(ixs_bounds *b, const char *name) {
  ixs_var_bound *v = find_var(b, name);
  return v ? v->divisor : 0;
}
