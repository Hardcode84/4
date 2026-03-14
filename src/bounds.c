#include "bounds.h"
#include <limits.h>
#include <string.h>

#ifndef INT64_MIN
#define INT64_MIN (-9223372036854775807LL - 1)
#endif
#ifndef INT64_MAX
#define INT64_MAX 9223372036854775807LL
#endif

void ixs_bounds_init(ixs_bounds *b) { memset(b, 0, sizeof(*b)); }

void ixs_bounds_destroy(ixs_bounds *b) { (void)b; }

static ixs_var_bound *find_var(ixs_bounds *b, const char *name) {
  size_t i;
  for (i = 0; i < b->nvars; i++) {
    if (strcmp(b->vars[i].name, name) == 0)
      return &b->vars[i];
  }
  return NULL;
}

static ixs_var_bound *get_or_create_var(ixs_bounds *b, const char *name) {
  ixs_var_bound *v = find_var(b, name);
  if (v)
    return v;
  if (b->nvars >= IXS_BOUNDS_MAX_VARS)
    return NULL;
  v = &b->vars[b->nvars++];
  v->name = name;
  v->iv.valid = true;
  v->iv.lo_p = INT64_MIN;
  v->iv.lo_q = 1;
  v->iv.hi_p = INT64_MAX;
  v->iv.hi_q = 1;
  return v;
}

/*
 * Extract a bound from a comparison assumption normalized to (expr cmp 0).
 * Pattern: sym >= 0, sym < N, sym - N >= 0, N - sym > 0, etc.
 *
 * This handles common patterns from the corpus:
 *   sym >= 0          → lo = 0
 *   sym < N           → hi = N - 1 (integer context)
 *   sym >= N          → lo = N
 */
void ixs_bounds_add_assumption(ixs_bounds *b, ixs_node *a) {
  /* Only handle comparisons. */
  if (a->tag != IXS_CMP)
    return;

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
    case IXS_CMP_GT:
      /* sym > c  →  sym >= c + 1 (integer context) */
      if (rq == 1) {
        int64_t lo = rp + 1;
        if (ixs_rat_cmp(lo, 1, v->iv.lo_p, v->iv.lo_q) > 0) {
          v->iv.lo_p = lo;
          v->iv.lo_q = 1;
        }
      }
      break;
    case IXS_CMP_LE:
      if (ixs_rat_cmp(rp, rq, v->iv.hi_p, v->iv.hi_q) < 0) {
        v->iv.hi_p = rp;
        v->iv.hi_q = rq;
      }
      break;
    case IXS_CMP_LT:
      if (rq == 1) {
        int64_t hi = rp - 1;
        if (ixs_rat_cmp(hi, 1, v->iv.hi_p, v->iv.hi_q) < 0) {
          v->iv.hi_p = hi;
          v->iv.hi_q = 1;
        }
      }
      break;
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
    case IXS_CMP_GE: /* const >= sym → sym <= const */
      if (ixs_rat_cmp(lp, lq, v->iv.hi_p, v->iv.hi_q) < 0) {
        v->iv.hi_p = lp;
        v->iv.hi_q = lq;
      }
      break;
    case IXS_CMP_GT:
      if (lq == 1) {
        int64_t hi = lp - 1;
        if (ixs_rat_cmp(hi, 1, v->iv.hi_p, v->iv.hi_q) < 0) {
          v->iv.hi_p = hi;
          v->iv.hi_q = 1;
        }
      }
      break;
    case IXS_CMP_LE:
      if (ixs_rat_cmp(lp, lq, v->iv.lo_p, v->iv.lo_q) > 0) {
        v->iv.lo_p = lp;
        v->iv.lo_q = lq;
      }
      break;
    case IXS_CMP_LT:
      if (lq == 1) {
        int64_t lo = lp + 1;
        if (ixs_rat_cmp(lo, 1, v->iv.lo_p, v->iv.lo_q) > 0) {
          v->iv.lo_p = lo;
          v->iv.lo_q = 1;
        }
      }
      break;
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

    /* We have: tp/tq * sym + kp/kq  OP  0 */
    if (tp == 1 && tq == 1) {
      /* sym + k OP 0  →  sym OP -k */
      int64_t rp2, rq2;
      if (!ixs_rat_neg(kp, kq, &rp2, &rq2))
        return;
      v = get_or_create_var(b, lhs->u.add.terms[0].term->u.name);
      if (!v)
        return;
      switch (op) {
      case IXS_CMP_GE:
        if (ixs_rat_cmp(rp2, rq2, v->iv.lo_p, v->iv.lo_q) > 0) {
          v->iv.lo_p = rp2;
          v->iv.lo_q = rq2;
        }
        break;
      case IXS_CMP_GT:
        if (rq2 == 1) {
          int64_t lo = rp2 + 1;
          if (ixs_rat_cmp(lo, 1, v->iv.lo_p, v->iv.lo_q) > 0) {
            v->iv.lo_p = lo;
            v->iv.lo_q = 1;
          }
        }
        break;
      case IXS_CMP_LE:
        if (ixs_rat_cmp(rp2, rq2, v->iv.hi_p, v->iv.hi_q) < 0) {
          v->iv.hi_p = rp2;
          v->iv.hi_q = rq2;
        }
        break;
      case IXS_CMP_LT:
        if (rq2 == 1) {
          int64_t hi = rp2 - 1;
          if (ixs_rat_cmp(hi, 1, v->iv.hi_p, v->iv.hi_q) < 0) {
            v->iv.hi_p = hi;
            v->iv.hi_q = 1;
          }
        }
        break;
      default:
        break;
      }
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

ixs_interval ixs_bounds_get(ixs_bounds *b, ixs_node *expr) {
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
    /* Mod(x, m) ∈ [0, m-1] only when x is integer-valued and m is a
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
