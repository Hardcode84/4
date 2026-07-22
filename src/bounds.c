/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds.h"
#include "expand.h"
#include "simplify.h"
#include <limits.h>
#include <string.h>

#define BOUNDS_INIT_CAP 16
#define BOUNDS_CACHE_CAP 32u
#define BOUNDS_CACHE_DISABLED ((size_t)-1)
#define ASSUMPTION_NODE_LIMIT 1024u

static void bounds_cache_clear(ixs_bounds *b) {
  if (b && b->cache && b->cache_cap != BOUNDS_CACHE_DISABLED)
    memset(b->cache, 0, b->cache_cap * sizeof(*b->cache));
}

static void bounds_cache_alloc(ixs_bounds *b) {
  if (!b || b->cache_cap == BOUNDS_CACHE_DISABLED)
    return;
  if (b->cache)
    return;
  b->cache = ixs_arena_alloc(b->scratch, BOUNDS_CACHE_CAP * sizeof(*b->cache),
                             sizeof(void *));
  if (!b->cache) {
    b->cache_cap = BOUNDS_CACHE_DISABLED;
    return;
  }
  b->cache_cap = BOUNDS_CACHE_CAP;
  memset(b->cache, 0, b->cache_cap * sizeof(*b->cache));
}

static bool bounds_cache_lookup(ixs_bounds *b, ixs_node *expr,
                                ixs_interval *out) {
  size_t idx;
  if (!b || !expr || !out || !b->cache || b->cache_cap == BOUNDS_CACHE_DISABLED)
    return false;
  idx = expr->hash & (b->cache_cap - 1u);
  if (b->cache[idx].expr != expr)
    return false;
  *out = b->cache[idx].iv;
  return true;
}

static void bounds_cache_store(ixs_bounds *b, ixs_node *expr, ixs_interval iv) {
  size_t idx;
  if (!expr || !b || !b->cache || b->cache_cap == BOUNDS_CACHE_DISABLED)
    return;
  idx = expr->hash & (b->cache_cap - 1u);
  b->cache[idx].expr = expr;
  b->cache[idx].iv = iv;
}

static bool bounds_cacheable_expr(ixs_node *expr) {
  return expr && expr->tag != IXS_INT && expr->tag != IXS_RAT &&
         expr->tag != IXS_SYM;
}

IXS_STATIC bool ixs_bounds_init(ixs_bounds *b, ixs_arena *scratch) {
  b->ctx = NULL;
  b->scratch = scratch;
  b->nvars = 0;
  b->cap = BOUNDS_INIT_CAP;
  b->vars = ixs_arena_alloc(scratch, BOUNDS_INIT_CAP * sizeof(*b->vars),
                            sizeof(void *));
  b->nexprs = 0;
  b->expr_cap = 0;
  b->exprs = NULL;
  b->cache = NULL;
  b->cache_cap = 0;
  b->contradiction = false;
  b->oom = false;
  if (b->vars)
    bounds_cache_alloc(b);
  return b->vars != NULL;
}

IXS_STATIC bool ixs_bounds_init_ctx(ixs_bounds *b, ixs_ctx *ctx,
                                    ixs_arena *scratch) {
  if (!ixs_bounds_init(b, scratch))
    return false;
  b->ctx = ctx;
  return true;
}

/* All bounds storage lives in the scratch arena; no per-object cleanup. */
IXS_STATIC void ixs_bounds_destroy(ixs_bounds *b) { (void)b; }

IXS_STATIC bool ixs_bounds_fork(ixs_bounds *dst, const ixs_bounds *src) {
  if (!dst || !src || src->oom)
    return false;
  dst->ctx = src->ctx;
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
  dst->cache = NULL;
  dst->cache_cap = BOUNDS_CACHE_DISABLED;
  dst->contradiction = src->contradiction;
  dst->oom = false;
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
  if (!b->vars) {
    b->oom = true;
    return NULL;
  }
  if (b->nvars >= b->cap) {
    ixs_var_bound *grown =
        ixs_arena_grow(b->scratch, b->vars, b->cap * sizeof(*b->vars),
                       b->cap * 2 * sizeof(*b->vars), sizeof(void *));
    if (!grown) {
      b->oom = true;
      return NULL;
    }
    b->vars = grown;
    b->cap *= 2;
  }
  v = &b->vars[b->nvars++];
  v->name = name;
  v->iv.valid = true;
  v->iv.lo_inf = false;
  v->iv.hi_inf = false;
  ixs_interval_set_lo_neg_inf(&v->iv);
  ixs_interval_set_hi_pos_inf(&v->iv);
  v->modulus = 0;
  v->remainder = 0;
  v->bits.known_zero = 0;
  v->bits.known_one = 0;
  v->bits.pow2 = IXS_POW2_UNKNOWN;
  return v;
}

static void bitfacts_unknown(ixs_bitfacts *bits) {
  bits->known_zero = 0;
  bits->known_one = 0;
  bits->pow2 = IXS_POW2_UNKNOWN;
}

static unsigned bit_popcount64(uint64_t v) {
  unsigned n = 0;
  while (v) {
    n += (unsigned)(v & 1u);
    v >>= 1;
  }
  return n;
}

static bool uint64_is_pow2(uint64_t v) { return v != 0 && (v & (v - 1u)) == 0; }

static bool int64_is_positive_pow2(int64_t v) {
  return v > 0 && uint64_is_pow2((uint64_t)v);
}

static bool int64_modulus_is_pow2(int64_t v) {
  return v > 0 && uint64_is_pow2((uint64_t)v);
}

static unsigned bit_ctz64(uint64_t v) {
  unsigned n = 0;
  while (v != 0 && (v & 1u) == 0) {
    n++;
    v >>= 1;
  }
  return n;
}

static uint64_t low_mask(unsigned nbits) {
  if (nbits >= 64u)
    return ~(uint64_t)0;
  return (((uint64_t)1) << nbits) - 1u;
}

static uint64_t value_span_mask(uint64_t hi) {
  uint64_t mask = 0;
  while (hi) {
    mask = (mask << 1) | 1u;
    hi >>= 1;
  }
  return mask;
}

static bool bitfacts_conflict(const ixs_bitfacts *bits) {
  if ((bits->known_zero & bits->known_one) != 0)
    return true;
  if ((bits->pow2 == IXS_POW2_OR_ZERO || bits->pow2 == IXS_POW2_POSITIVE) &&
      bit_popcount64(bits->known_one) > 1)
    return true;
  return false;
}

static bool interval_lower_at_least(const ixs_interval *iv, int64_t p,
                                    int64_t q) {
  return iv->valid && !iv->lo_inf && ixs_rat_cmp(iv->lo_p, iv->lo_q, p, q) >= 0;
}

static bool interval_upper_less_than(const ixs_interval *iv, int64_t p,
                                     int64_t q) {
  return iv->valid && !iv->hi_inf && ixs_rat_cmp(iv->hi_p, iv->hi_q, p, q) < 0;
}

static bool interval_exact_int(const ixs_interval *iv, int64_t *value) {
  if (!iv->valid || iv->lo_inf || iv->hi_inf || iv->lo_q != 1 ||
      iv->hi_q != 1 || iv->lo_p != iv->hi_p)
    return false;
  *value = iv->lo_p;
  return true;
}

static void refine_var_bit_consistency(ixs_bounds *b, ixs_var_bound *v) {
  int64_t exact;
  if (!v)
    return;
  if (v->bits.pow2 == IXS_POW2_OR_ZERO && interval_lower_at_least(&v->iv, 1, 1))
    v->bits.pow2 = IXS_POW2_POSITIVE;
  if ((v->bits.pow2 == IXS_POW2_OR_ZERO &&
       interval_upper_less_than(&v->iv, 0, 1)) ||
      (v->bits.pow2 == IXS_POW2_POSITIVE &&
       interval_upper_less_than(&v->iv, 1, 1)))
    b->contradiction = true;
  if (interval_exact_int(&v->iv, &exact)) {
    uint64_t u = (uint64_t)exact;
    if ((v->bits.known_zero & u) != 0 || (v->bits.known_one & ~u) != 0)
      b->contradiction = true;
    if ((v->bits.pow2 == IXS_POW2_OR_ZERO ||
         v->bits.pow2 == IXS_POW2_POSITIVE) &&
        exact != 0 && !int64_is_positive_pow2(exact))
      b->contradiction = true;
    if (v->bits.pow2 == IXS_POW2_POSITIVE && exact == 0)
      b->contradiction = true;
  }
  if (bitfacts_conflict(&v->bits))
    b->contradiction = true;
}

static void apply_var_known_bits(ixs_bounds *b, ixs_var_bound *v,
                                 uint64_t known_zero, uint64_t known_one) {
  if (!v)
    return;
  v->bits.known_zero |= known_zero;
  v->bits.known_one |= known_one;
  refine_var_bit_consistency(b, v);
}

static void apply_known_bits(ixs_bounds *b, const char *name,
                             uint64_t known_zero, uint64_t known_one) {
  ixs_var_bound *v = get_or_create_var(b, name);
  apply_var_known_bits(b, v, known_zero, known_one);
}

static void apply_pow2_fact(ixs_bounds *b, ixs_var_bound *v,
                            ixs_pow2_fact pow2) {
  if (!v)
    return;
  if (pow2 == IXS_POW2_POSITIVE) {
    if (v->bits.pow2 == IXS_POW2_UNKNOWN || v->bits.pow2 == IXS_POW2_OR_ZERO) {
      v->bits.pow2 = IXS_POW2_POSITIVE;
    }
  } else if (pow2 == IXS_POW2_OR_ZERO && v->bits.pow2 == IXS_POW2_UNKNOWN) {
    v->bits.pow2 = IXS_POW2_OR_ZERO;
  }
  refine_var_bit_consistency(b, v);
}

static void apply_exact_int_bits(ixs_bounds *b, ixs_var_bound *v, int64_t val) {
  uint64_t u = (uint64_t)val;
  if (!v)
    return;
  apply_var_known_bits(b, v, ~u, u);
  if (val == 0) {
    if (v->bits.pow2 == IXS_POW2_POSITIVE)
      b->contradiction = true;
    else
      v->bits.pow2 = IXS_POW2_OR_ZERO;
  } else if (int64_is_positive_pow2(val)) {
    v->bits.pow2 = IXS_POW2_POSITIVE;
  } else if (v->bits.pow2 == IXS_POW2_OR_ZERO ||
             v->bits.pow2 == IXS_POW2_POSITIVE) {
    b->contradiction = true;
  }
  refine_var_bit_consistency(b, v);
}

static void apply_congruence_known_bits(ixs_bounds *b, ixs_var_bound *v) {
  uint64_t mask, rem;
  if (!v || !int64_modulus_is_pow2(v->modulus))
    return;
  mask = (uint64_t)v->modulus - 1u;
  rem = (uint64_t)v->remainder & mask;
  apply_var_known_bits(b, v, (~rem) & mask, rem & mask);
}

/* Record sym ≡ rem (mod m).  Merges with existing info via CRT.
 * Overflowing constraints are silently ignored.  Direct contradictions are
 * recorded on the bounds object so query APIs can decline concrete answers. */
static void apply_modrem(ixs_bounds *b, const char *name, int64_t m,
                         int64_t rem) {
  ixs_var_bound *v;
  int64_t g, new_mod, old_mod, step, m_div_g, target, k;
  if (m <= 0)
    return;
  rem = ((rem % m) + m) % m;
  v = get_or_create_var(b, name);
  if (!v)
    return;
  if (v->modulus == 0) {
    v->modulus = m;
    v->remainder = rem;
    apply_congruence_known_bits(b, v);
    return;
  }
  old_mod = v->modulus;
  g = ixs_gcd(old_mod, m);
  if (((rem - v->remainder) % g + g) % g != 0) {
    b->contradiction = true;
    return;
  }
  if (old_mod > INT64_MAX / (m / g))
    return;
  new_mod = old_mod / g * m;
  /* Solve old_mod/g * k ≡ (rem - v->remainder)/g  (mod m/g) by brute search.
   * gcd(old_mod/g, m/g) == 1 guarantees a unique solution.  Moduli are
   * small in practice (thread tile sizes), so the linear scan is fine. */
  step = old_mod / g;
  m_div_g = m / g;
  target = ((((rem - v->remainder) / g) % m_div_g) + m_div_g) % m_div_g;
  for (k = 0; k < m_div_g; k++) {
    if (((uint64_t)step * (uint64_t)k) % (uint64_t)m_div_g == (uint64_t)target)
      break;
  }
  if (k >= m_div_g)
    return;
  v->modulus = new_mod;
  v->remainder =
      (int64_t)(((uint64_t)v->remainder + (uint64_t)old_mod * (uint64_t)k) %
                (uint64_t)new_mod);
  apply_congruence_known_bits(b, v);
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
  /* Normalized: ADD(k, c*Mod(sym, M)) == 0, where c = ±1 and k is integer.
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
    rem_val = ((rem_val % modulus->u.ival) + modulus->u.ival) % modulus->u.ival;
    apply_modrem(b, dividend->u.name, modulus->u.ival, rem_val);
  }
}

static ixs_cmp_op flip_cmp(ixs_cmp_op op) {
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

static ixs_node *bounds_expr_without_add_const(ixs_bounds *b, ixs_node *expr) {
  ixs_node *result;
  uint32_t i;
  if (!b || !b->ctx || !expr || expr->tag != IXS_ADD ||
      ixs_node_is_zero(expr->u.add.coeff) || expr->u.add.nterms == 0)
    return NULL;

  result = b->ctx->node_zero;
  for (i = 0; i < expr->u.add.nterms; i++) {
    ixs_node *term = expr->u.add.terms[i].term;
    ixs_node *coeff = expr->u.add.terms[i].coeff;
    ixs_node *scaled =
        ixs_node_is_one(coeff) ? term : simp_mul(b->ctx, coeff, term);
    if (!scaled) {
      b->oom = true;
      return NULL;
    }
    result = simp_add(b->ctx, result, scaled);
    if (!result) {
      b->oom = true;
      return NULL;
    }
  }
  return result;
}

static void add_shifted_add_range(ixs_bounds *b, ixs_node *expr,
                                  ixs_interval iv) {
  ixs_node *base;
  int64_t cp, cq, np, nq;
  ixs_interval offset, shifted;

  base = bounds_expr_without_add_const(b, expr);
  if (!base || base == expr)
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
  ixs_var_bound *v = get_or_create_var(b, name);
  if (!v)
    return;
  switch (op) {
  case IXS_CMP_GE:
    if (v->iv.lo_inf || ixs_rat_cmp(cp, cq, v->iv.lo_p, v->iv.lo_q) > 0) {
      v->iv.lo_p = cp;
      v->iv.lo_q = cq;
      v->iv.lo_inf = false;
    }
    break;
  case IXS_CMP_GT: {
    int64_t lo;
    if (!ixs_safe_add(ixs_rat_floor(cp, cq), 1, &lo))
      break;
    if (v->iv.lo_inf || ixs_rat_cmp(lo, 1, v->iv.lo_p, v->iv.lo_q) > 0) {
      v->iv.lo_p = lo;
      v->iv.lo_q = 1;
      v->iv.lo_inf = false;
    }
    break;
  }
  case IXS_CMP_LE:
    if (v->iv.hi_inf || ixs_rat_cmp(cp, cq, v->iv.hi_p, v->iv.hi_q) < 0) {
      v->iv.hi_p = cp;
      v->iv.hi_q = cq;
      v->iv.hi_inf = false;
    }
    break;
  case IXS_CMP_LT: {
    int64_t hi;
    if (!ixs_safe_sub(ixs_rat_ceil(cp, cq), 1, &hi))
      break;
    if (v->iv.hi_inf || ixs_rat_cmp(hi, 1, v->iv.hi_p, v->iv.hi_q) < 0) {
      v->iv.hi_p = hi;
      v->iv.hi_q = 1;
      v->iv.hi_inf = false;
    }
    break;
  }
  case IXS_CMP_EQ:
    v->iv.lo_p = cp;
    v->iv.lo_q = cq;
    v->iv.hi_p = cp;
    v->iv.hi_q = cq;
    v->iv.lo_inf = false;
    v->iv.hi_inf = false;
    if (cq == 1)
      apply_exact_int_bits(b, v, cp);
    break;
  case IXS_CMP_NE:
    break;
  }
  refine_var_bit_consistency(b, v);
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

static bool node_coeff_is(ixs_node *n, int64_t value) {
  int64_t p, q;
  if (!n)
    return false;
  ixs_node_get_rat(n, &p, &q);
  return p == value && q == 1;
}

static bool extract_add_term_eq_const(ixs_node *n, ixs_node **expr,
                                      int64_t *value) {
  int64_t kp, kq, cp, cq;
  if (!n || n->tag != IXS_ADD || n->u.add.nterms != 1)
    return false;
  ixs_node_get_rat(n->u.add.coeff, &kp, &kq);
  ixs_node_get_rat(n->u.add.terms[0].coeff, &cp, &cq);
  if (kq != 1 || cq != 1)
    return false;
  if (cp == 1) {
    if (kp == INT64_MIN)
      return false;
    *value = -kp;
  } else if (cp == -1) {
    *value = kp;
  } else {
    return false;
  }
  *expr = n->u.add.terms[0].term;
  return true;
}

/* Recover "expr == integer" from either direct comparisons or the normalized
 * ADD(k, +/-expr) == 0 form produced by cmp_normalize_to_zero. */
static bool extract_cmp_expr_const(ixs_node *cmp, ixs_node **expr,
                                   int64_t *value) {
  int64_t c;
  if (!cmp || cmp->tag != IXS_CMP || !expr || !value)
    return false;

  if (ixs_node_is_zero(cmp->u.binary.rhs) &&
      extract_add_term_eq_const(cmp->u.binary.lhs, expr, value))
    return true;
  if (ixs_node_is_zero(cmp->u.binary.lhs) &&
      extract_add_term_eq_const(cmp->u.binary.rhs, expr, value))
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

static bool extract_add_node_equality(ixs_node *n, ixs_node **a, ixs_node **b) {
  int64_t kp, kq;
  ixs_addterm *t0, *t1;
  if (!n || n->tag != IXS_ADD || n->u.add.nterms != 2)
    return false;
  ixs_node_get_rat(n->u.add.coeff, &kp, &kq);
  if (kp != 0 || kq != 1)
    return false;
  t0 = &n->u.add.terms[0];
  t1 = &n->u.add.terms[1];
  if (node_coeff_is(t0->coeff, 1) && node_coeff_is(t1->coeff, -1)) {
    *a = t0->term;
    *b = t1->term;
    return true;
  }
  if (node_coeff_is(t0->coeff, -1) && node_coeff_is(t1->coeff, 1)) {
    *a = t0->term;
    *b = t1->term;
    return true;
  }
  return false;
}

static bool extract_cmp_node_equality(ixs_node *cmp, ixs_node **a,
                                      ixs_node **b) {
  if (!cmp || cmp->tag != IXS_CMP || cmp->u.binary.cmp_op != IXS_CMP_EQ)
    return false;
  if (ixs_node_is_zero(cmp->u.binary.rhs))
    return extract_add_node_equality(cmp->u.binary.lhs, a, b);
  if (ixs_node_is_zero(cmp->u.binary.lhs))
    return extract_add_node_equality(cmp->u.binary.rhs, a, b);
  if (!ixs_node_is_const(cmp->u.binary.lhs) &&
      !ixs_node_is_const(cmp->u.binary.rhs)) {
    *a = cmp->u.binary.lhs;
    *b = cmp->u.binary.rhs;
    return true;
  }
  return false;
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

static bool extract_pow2_and(ixs_node *expr, const char **name) {
  ixs_node *a, *b;
  if (!expr || expr->tag != IXS_AND || expr->u.logic.nargs != 2 || !name)
    return false;
  a = expr->u.logic.args[0];
  b = expr->u.logic.args[1];
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

static bool extract_bitop_sym_mask(ixs_node *expr, ixs_tag tag,
                                   const char **name, int64_t *mask) {
  ixs_node *a, *b;
  if (!expr || expr->tag != tag || expr->u.logic.nargs != 2 || !name || !mask)
    return false;
  a = expr->u.logic.args[0];
  b = expr->u.logic.args[1];
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
  ixs_var_bound *v = get_or_create_var(b, name);
  if (!v)
    return;
  if (v->bits.pow2 == IXS_POW2_UNKNOWN)
    v->bits.pow2 = IXS_POW2_OR_ZERO;
  refine_var_bit_consistency(b, v);
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
      b->contradiction = true;
      return;
    }
    apply_known_bits(b, name, (~value_bits) & mask_bits,
                     value_bits & mask_bits);
    return;
  }

  if (extract_bitop_sym_mask(expr, IXS_OR, &name, &mask)) {
    mask_bits = (uint64_t)mask;
    value_bits = (uint64_t)value;
    if ((value_bits & mask_bits) != mask_bits) {
      b->contradiction = true;
      return;
    }
    apply_known_bits(b, name, ~value_bits, value_bits & ~mask_bits);
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
    apply_known_bits(b, name, 0, (uint64_t)mask);
    return;
  }
  if (extract_bitop_sym_mask(a, IXS_AND, &name, &mask) &&
      name == other->u.name) {
    mask_bits = (uint64_t)mask;
    apply_known_bits(b, name, ~mask_bits, 0);
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

static ixs_node *bounds_canonical_expr(ixs_bounds *b, ixs_node *expr) {
  ixs_node *expanded;
  ixs_arena_mark diag_mark;
  const char **saved_errors;
  size_t saved_nerrors, saved_errors_cap;
  if (!b || !b->ctx || !expr || ixs_node_is_sentinel(expr))
    return expr;
  if (expr->tag == IXS_INT || expr->tag == IXS_RAT || expr->tag == IXS_SYM)
    return expr;

  /* Canonical aliases are optional.  Expansion failures must not become
   * user-visible diagnostics for otherwise successful bounds queries. */
  diag_mark = ixs_arena_save(&b->ctx->diag);
  saved_errors = b->ctx->errors;
  saved_nerrors = b->ctx->nerrors;
  saved_errors_cap = b->ctx->errors_cap;
  expanded = expand_impl(b->ctx, expr);
  ixs_arena_restore(&b->ctx->diag, diag_mark);
  b->ctx->errors = saved_errors;
  b->ctx->nerrors = saved_nerrors;
  b->ctx->errors_cap = saved_errors_cap;

  if (!expanded) {
    b->oom = true;
    return expr;
  }
  if (ixs_node_is_sentinel(expanded))
    return expr;
  return expanded;
}

static void bounds_add_expr_raw(ixs_bounds *b, ixs_node *expr,
                                ixs_interval iv) {
  ixs_expr_bound *eb;
  if (!b || !expr || !iv.valid)
    return;
  if (b->nexprs >= b->expr_cap) {
    size_t new_cap = b->expr_cap ? b->expr_cap * 2 : 4;
    ixs_expr_bound *new_arr =
        ixs_arena_alloc(b->scratch, new_cap * sizeof(*new_arr), sizeof(void *));
    if (!new_arr) {
      b->oom = true;
      return;
    }
    if (b->nexprs)
      memcpy(new_arr, b->exprs, b->nexprs * sizeof(*b->exprs));
    b->exprs = new_arr;
    b->expr_cap = new_cap;
  }
  eb = &b->exprs[b->nexprs++];
  eb->expr = expr;
  eb->iv = iv;
  bounds_cache_clear(b);
}

IXS_STATIC void ixs_bounds_add_expr(ixs_bounds *b, ixs_node *expr,
                                    ixs_interval iv) {
  ixs_node *canon;
  bounds_add_expr_raw(b, expr, iv);
  if (b->oom)
    return;
  canon = bounds_canonical_expr(b, expr);
  if (canon && canon != expr)
    bounds_add_expr_raw(b, canon, iv);
}

/*
 * Extract interval bounds and modular congruence from a comparison.
 * Patterns: sym >= 0, sym < N, Mod(sym, M) == R, etc.
 */
static void bounds_add_assumption_impl(ixs_bounds *b, ixs_node *a) {
  if (a->tag != IXS_CMP)
    return;
  bounds_cache_clear(b);

  extract_modrem(b, a);
  extract_bitfacts(b, a);

  ixs_node *lhs = a->u.binary.lhs;
  ixs_node *rhs = a->u.binary.rhs;
  ixs_cmp_op op = a->u.binary.cmp_op;

  /* Normalize to "sym op const" form. */
  if (lhs->tag == IXS_SYM && ixs_node_is_const(rhs)) {
    int64_t rp, rq;
    ixs_interval sym_iv;
    ixs_node_get_rat(rhs, &rp, &rq);
    apply_sym_cmp_const(b, lhs->u.name, op, rp, rq);
    sym_iv = interval_from_sym_cmp_const(op, rp, rq);
    if (sym_iv.valid)
      ixs_bounds_add_expr(b, lhs, sym_iv);
    return;
  }
  if (rhs->tag == IXS_SYM && ixs_node_is_const(lhs)) {
    int64_t lp, lq;
    ixs_cmp_op eff_op = flip_cmp(op);
    ixs_interval sym_iv;
    ixs_node_get_rat(lhs, &lp, &lq);
    apply_sym_cmp_const(b, rhs->u.name, eff_op, lp, lq);
    sym_iv = interval_from_sym_cmp_const(eff_op, lp, lq);
    if (sym_iv.valid)
      ixs_bounds_add_expr(b, rhs, sym_iv);
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

    ixs_cmp_op eff_op = (ixs_rat_cmp(tp, tq, 0, 1) < 0) ? flip_cmp(op) : op;
    apply_sym_cmp_const(b, lhs->u.add.terms[0].term->u.name, eff_op, rp2, rq2);
    {
      ixs_interval sym_iv = interval_from_sym_cmp_const(eff_op, rp2, rq2);
      if (sym_iv.valid)
        ixs_bounds_add_expr(b, lhs->u.add.terms[0].term, sym_iv);
    }
    return;
  }

  /* Fallback: expr op 0 for non-symbol lhs. Store as expression bound. */
  if (ixs_node_is_zero(rhs))
    add_expr_integer_zero_cmp(b, lhs, op);
}

IXS_STATIC bool ixs_bounds_add_assumption(ixs_bounds *b, ixs_node *a) {
  if (!b || !a || b->oom)
    return false;
  bounds_add_assumption_impl(b, a);
  return !b->oom;
}

/* GCD of a positive modulus and a conservative dividend step.  Computing the
 * GCD directly keeps the result representable when a coefficient is
 * INT64_MIN, whose magnitude is one past INT64_MAX. */
static int64_t mod_dividend_gcd(ixs_node *expr, int64_t modulus) {
  int64_t p, q, g;
  uint32_t i;
  switch (expr->tag) {
  case IXS_MUL:
    ixs_node_get_rat(expr->u.mul.coeff, &p, &q);
    return (q == 1) ? ixs_gcd(p, modulus) : 1;
  case IXS_ADD:
    ixs_node_get_rat(expr->u.add.coeff, &p, &q);
    if (q != 1)
      return 1;
    g = ixs_gcd(p, modulus);
    for (i = 0; i < expr->u.add.nterms; i++) {
      ixs_node_get_rat(expr->u.add.terms[i].coeff, &p, &q);
      if (q != 1)
        return 1;
      g = ixs_gcd(g, p);
    }
    return g;
  default:
    return 1;
  }
}

#define BITFACTS_DEPTH_LIMIT 64u

static bool bounds_get_bitfacts_depth(ixs_bounds *b, ixs_node *expr,
                                      ixs_bitfacts *out, unsigned depth);

static void bitfacts_apply_exact(ixs_bitfacts *bits, int64_t val) {
  uint64_t u = (uint64_t)val;
  bits->known_zero |= ~u;
  bits->known_one |= u;
  if (val == 0)
    bits->pow2 = IXS_POW2_OR_ZERO;
  else if (int64_is_positive_pow2(val))
    bits->pow2 = IXS_POW2_POSITIVE;
}

static void bitfacts_apply_interval(ixs_bitfacts *bits,
                                    const ixs_interval *iv) {
  int64_t exact;
  if (interval_exact_int(iv, &exact)) {
    bitfacts_apply_exact(bits, exact);
    return;
  }
  if (!iv->valid || iv->lo_inf || iv->hi_inf || iv->hi_q != 1 || iv->hi_p < 0 ||
      !interval_lower_at_least(iv, 0, 1))
    return;
  bits->known_zero |= ~value_span_mask((uint64_t)iv->hi_p);
}

static bool bitfacts_low_value(const ixs_bitfacts *bits, unsigned nbits,
                               uint64_t *value) {
  uint64_t mask = low_mask(nbits);
  if (((bits->known_zero | bits->known_one) & mask) != mask)
    return false;
  *value = bits->known_one & mask;
  return true;
}

static void bitfacts_set_low_value(ixs_bitfacts *bits, unsigned nbits,
                                   uint64_t value) {
  uint64_t mask = low_mask(nbits);
  bits->known_one |= value & mask;
  bits->known_zero |= (~value) & mask;
}

static void bitfacts_apply_modrem(ixs_bitfacts *bits, int64_t modulus,
                                  int64_t remainder) {
  uint64_t mask, rem;
  if (!int64_modulus_is_pow2(modulus))
    return;
  mask = (uint64_t)modulus - 1u;
  rem = (uint64_t)remainder & mask;
  bits->known_zero |= (~rem) & mask;
  bits->known_one |= rem & mask;
}

static bool bounds_get_symbol_bitfacts(ixs_bounds *b, const char *name,
                                       ixs_bitfacts *out) {
  int64_t exact;
  ixs_var_bound *v = find_var(b, name);
  bitfacts_unknown(out);
  if (v) {
    *out = v->bits;
    bitfacts_apply_modrem(out, v->modulus, v->remainder);
    if (interval_exact_int(&v->iv, &exact))
      bitfacts_apply_exact(out, exact);
    if (out->pow2 == IXS_POW2_OR_ZERO && interval_lower_at_least(&v->iv, 1, 1))
      out->pow2 = IXS_POW2_POSITIVE;
  }
  return true;
}

static void bitfacts_apply_and(ixs_bitfacts *out, const ixs_bitfacts *a,
                               const ixs_bitfacts *b) {
  out->known_one = a->known_one & b->known_one;
  out->known_zero = a->known_zero | b->known_zero;
  out->pow2 = IXS_POW2_UNKNOWN;
}

static void bitfacts_apply_or(ixs_bitfacts *out, const ixs_bitfacts *a,
                              const ixs_bitfacts *b) {
  out->known_one = a->known_one | b->known_one;
  out->known_zero = a->known_zero & b->known_zero;
  out->pow2 = IXS_POW2_UNKNOWN;
}

static void bitfacts_apply_xor(ixs_bitfacts *out, const ixs_bitfacts *a,
                               const ixs_bitfacts *b) {
  out->known_one =
      (a->known_one & b->known_zero) | (a->known_zero & b->known_one);
  out->known_zero =
      (a->known_zero & b->known_zero) | (a->known_one & b->known_one);
  out->pow2 = IXS_POW2_UNKNOWN;
}

static bool bitfacts_apply_add(ixs_bounds *b, ixs_node *expr, ixs_bitfacts *out,
                               unsigned depth) {
  unsigned nbits;
  int64_t cp, cq;

  ixs_node_get_rat(expr->u.add.coeff, &cp, &cq);
  if (cq != 1)
    return true;

  for (nbits = 1; nbits <= 64u; nbits++) {
    uint64_t mask = low_mask(nbits);
    uint64_t sum = (uint64_t)cp & mask;
    uint32_t i;
    bool known = true;

    for (i = 0; i < expr->u.add.nterms; i++) {
      ixs_bitfacts term_bits;
      uint64_t term_value;
      int64_t tp, tq;

      ixs_node_get_rat(expr->u.add.terms[i].coeff, &tp, &tq);
      if (tq != 1 ||
          !bounds_get_bitfacts_depth(b, expr->u.add.terms[i].term, &term_bits,
                                     depth - 1) ||
          !bitfacts_low_value(&term_bits, nbits, &term_value)) {
        known = false;
        break;
      }
      sum = (sum + (((uint64_t)tp * term_value) & mask)) & mask;
    }

    if (!known)
      break;
    bitfacts_set_low_value(out, nbits, sum);
    if (nbits == 64u)
      break;
  }
  return true;
}

static bool bitfacts_apply_mul(ixs_bounds *b, ixs_node *expr, ixs_bitfacts *out,
                               unsigned depth) {
  ixs_bitfacts base_bits;
  uint64_t coeff;
  unsigned shift, i;

  if (expr->u.mul.coeff->tag != IXS_INT || expr->u.mul.coeff->u.ival <= 0 ||
      expr->u.mul.nfactors != 1 || expr->u.mul.factors[0].exp != 1 ||
      !ixs_node_is_integer_valued(expr))
    return true;

  coeff = (uint64_t)expr->u.mul.coeff->u.ival;
  if (!uint64_is_pow2(coeff) ||
      !bounds_get_bitfacts_depth(b, expr->u.mul.factors[0].base, &base_bits,
                                 depth - 1))
    return true;

  shift = bit_ctz64(coeff);
  out->known_zero |= low_mask(shift);
  for (i = shift; i < 64u; i++) {
    uint64_t src = ((uint64_t)1) << (i - shift);
    uint64_t dst = ((uint64_t)1) << i;
    if (base_bits.known_zero & src)
      out->known_zero |= dst;
    if (base_bits.known_one & src)
      out->known_one |= dst;
  }
  return true;
}

static bool extract_pow2_dividend(ixs_node *expr, ixs_node **dividend,
                                  uint64_t *denom) {
  int64_t cp, cq;
  if (!expr || expr->tag != IXS_MUL || expr->u.mul.nfactors != 1 ||
      expr->u.mul.factors[0].exp != 1)
    return false;
  ixs_node_get_rat(expr->u.mul.coeff, &cp, &cq);
  if (cp != 1 || cq <= 0 || !int64_modulus_is_pow2(cq))
    return false;
  *dividend = expr->u.mul.factors[0].base;
  *denom = (uint64_t)cq;
  return true;
}

static bool bitfacts_apply_floor_div(ixs_bounds *b, ixs_node *expr,
                                     ixs_bitfacts *out, unsigned depth) {
  ixs_node *dividend;
  ixs_interval iv;
  ixs_bitfacts bits;
  uint64_t denom;
  unsigned shift, i;

  if (!extract_pow2_dividend(expr->u.unary.arg, &dividend, &denom))
    return true;

  iv = ixs_bounds_get(b, dividend);
  if (!interval_lower_at_least(&iv, 0, 1) ||
      !bounds_get_bitfacts_depth(b, dividend, &bits, depth - 1))
    return true;

  shift = bit_ctz64(denom);
  for (i = 0; i + shift < 64u; i++) {
    uint64_t src = ((uint64_t)1) << (i + shift);
    uint64_t dst = ((uint64_t)1) << i;
    if (bits.known_zero & src)
      out->known_zero |= dst;
    if (bits.known_one & src)
      out->known_one |= dst;
  }
  return true;
}

static bool bitfacts_apply_mod(ixs_bounds *b, ixs_node *expr, ixs_bitfacts *out,
                               unsigned depth) {
  ixs_bitfacts lhs;
  uint64_t mask;
  int64_t modulus;

  if (expr->u.binary.rhs->tag != IXS_INT ||
      !int64_modulus_is_pow2(expr->u.binary.rhs->u.ival) ||
      !ixs_node_is_integer_valued(expr->u.binary.lhs))
    return true;

  modulus = expr->u.binary.rhs->u.ival;
  mask = (uint64_t)modulus - 1u;
  out->known_zero |= ~mask;
  if (bounds_get_bitfacts_depth(b, expr->u.binary.lhs, &lhs, depth - 1)) {
    out->known_zero |= lhs.known_zero & mask;
    out->known_one |= lhs.known_one & mask;
  }
  return true;
}

static inline bool bitfacts_apply_logic(ixs_bounds *b, ixs_node *expr,
                                        ixs_bitfacts *out, unsigned depth) {
  ixs_bitfacts lhs, rhs;
  if (expr->u.logic.nargs != 2)
    return false;
  if (!bounds_get_bitfacts_depth(b, expr->u.logic.args[0], &lhs, depth - 1) ||
      !bounds_get_bitfacts_depth(b, expr->u.logic.args[1], &rhs, depth - 1))
    return false;
  if (expr->tag == IXS_AND)
    bitfacts_apply_and(out, &lhs, &rhs);
  else
    bitfacts_apply_or(out, &lhs, &rhs);
  return true;
}

static inline bool bitfacts_apply_xor_node(ixs_bounds *b, ixs_node *expr,
                                           ixs_bitfacts *out, unsigned depth) {
  ixs_bitfacts lhs, rhs;
  if (!bounds_get_bitfacts_depth(b, expr->u.binary.lhs, &lhs, depth - 1) ||
      !bounds_get_bitfacts_depth(b, expr->u.binary.rhs, &rhs, depth - 1))
    return false;
  bitfacts_apply_xor(out, &lhs, &rhs);
  return true;
}

static inline bool bitfacts_apply_bool_value(ixs_bitfacts *out) {
  out->known_zero = ~(uint64_t)1;
  out->known_one = 0;
  return true;
}

static bool bounds_get_bitfacts_depth(ixs_bounds *b, ixs_node *expr,
                                      ixs_bitfacts *out, unsigned depth) {
  ixs_interval iv;

  bitfacts_unknown(out);
  if (!expr || depth == 0)
    return false;

  iv = ixs_bounds_get(b, expr);
  bitfacts_apply_interval(out, &iv);

  switch (expr->tag) {
  case IXS_INT:
    bitfacts_apply_exact(out, expr->u.ival);
    return true;
  case IXS_RAT:
    if (expr->u.rat.q != 1)
      return false;
    bitfacts_apply_exact(out, expr->u.rat.p);
    return true;
  case IXS_SYM: {
    return bounds_get_symbol_bitfacts(b, expr->u.name, out);
  }
  case IXS_CMP:
  case IXS_NOT:
    return bitfacts_apply_bool_value(out);
  case IXS_AND:
  case IXS_OR:
    return bitfacts_apply_logic(b, expr, out, depth);
  case IXS_XOR:
    return bitfacts_apply_xor_node(b, expr, out, depth);
  case IXS_ADD:
    return bitfacts_apply_add(b, expr, out, depth);
  case IXS_MUL:
    return bitfacts_apply_mul(b, expr, out, depth);
  case IXS_FLOOR:
    return bitfacts_apply_floor_div(b, expr, out, depth);
  case IXS_MOD:
    return bitfacts_apply_mod(b, expr, out, depth);
  case IXS_CEIL:
  case IXS_PIECEWISE:
  case IXS_MAX:
  case IXS_MIN:
    return ixs_node_is_integer_valued(expr);
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    return false;
  }
  return false;
}

IXS_STATIC bool ixs_bounds_get_bitfacts(ixs_bounds *b, ixs_node *expr,
                                        ixs_bitfacts *out) {
  if (!b || !out)
    return false;
  return bounds_get_bitfacts_depth(b, expr, out, BITFACTS_DEPTH_LIMIT);
}

IXS_STATIC bool ixs_bounds_is_pow2_positive(ixs_bounds *b, ixs_node *expr) {
  ixs_bitfacts bits;
  if (!ixs_bounds_get_bitfacts(b, expr, &bits))
    return false;
  return bits.pow2 == IXS_POW2_POSITIVE;
}

IXS_STATIC bool ixs_bounds_is_pow2_or_zero(ixs_bounds *b, ixs_node *expr) {
  ixs_bitfacts bits;
  if (!ixs_bounds_get_bitfacts(b, expr, &bits))
    return false;
  return bits.pow2 == IXS_POW2_OR_ZERO || ixs_bounds_is_pow2_positive(b, expr);
}

static inline bool bounds_symbol_divisible(ixs_bounds *b, const char *name,
                                           int64_t m) {
  int64_t sym_mod, sym_rem;
  if (!ixs_bounds_get_modrem(b, name, &sym_mod, &sym_rem))
    return false;
  return sym_mod % m == 0 && sym_rem % m == 0;
}

static inline bool bounds_mul_divisible(ixs_bounds *b, ixs_node *expr,
                                        int64_t m) {
  int64_t c = expr->u.mul.coeff->u.ival;
  int64_t remain;
  uint32_t i;
  if (c == 0)
    return true;
  for (i = 0; i < expr->u.mul.nfactors; i++) {
    if (!ixs_node_is_integer_valued(expr->u.mul.factors[i].base))
      return false;
  }
  remain = m / ixs_gcd(c, m);
  if (remain == 1)
    return true;
  for (i = 0; i < expr->u.mul.nfactors; i++) {
    if (expr->u.mul.factors[i].exp >= 1 &&
        ixs_bounds_is_known_divisible(b, expr->u.mul.factors[i].base, remain))
      return true;
  }
  return false;
}

static inline bool bounds_add_divisible(ixs_bounds *b, ixs_node *expr,
                                        int64_t m) {
  int64_t cp, cq;
  uint32_t i;
  ixs_node_get_rat(expr->u.add.coeff, &cp, &cq);
  if (cq != 1 || cp % m != 0)
    return false;
  for (i = 0; i < expr->u.add.nterms; i++) {
    int64_t tp, tq, g, remain;
    ixs_node_get_rat(expr->u.add.terms[i].coeff, &tp, &tq);
    if (tq != 1)
      return false;
    g = ixs_gcd(tp, m);
    remain = m / g;
    if (!ixs_bounds_is_known_divisible(b, expr->u.add.terms[i].term, remain))
      return false;
  }
  return true;
}

IXS_STATIC bool ixs_bounds_is_known_divisible(ixs_bounds *b, ixs_node *expr,
                                              int64_t m) {
  ixs_bitfacts bits;
  uint64_t low_mask;
  if (!b || !expr || m <= 0)
    return false;

  if (int64_modulus_is_pow2(m)) {
    low_mask = (uint64_t)m - 1u;
    if (ixs_bounds_get_bitfacts(b, expr, &bits) &&
        (bits.known_zero & low_mask) == low_mask)
      return true;
  }

  if (expr->tag == IXS_INT)
    return expr->u.ival % m == 0;

  if (expr->tag == IXS_SYM) {
    return bounds_symbol_divisible(b, expr->u.name, m);
  }

  if (expr->tag == IXS_MUL && expr->u.mul.coeff->tag == IXS_INT) {
    return bounds_mul_divisible(b, expr, m);
  }

  if (expr->tag == IXS_ADD) {
    return bounds_add_divisible(b, expr, m);
  }

  if (expr->tag == IXS_MAX || expr->tag == IXS_MIN) {
    return ixs_bounds_is_known_divisible(b, expr->u.binary.lhs, m) &&
           ixs_bounds_is_known_divisible(b, expr->u.binary.rhs, m);
  }

  return false;
}

static bool bounds_piecewise_is_integer_with_divinfo(ixs_bounds *b,
                                                     ixs_node *expr) {
  uint32_t i;
  bool reachable = false;
  for (i = 0; i < expr->u.pw.ncases; i++) {
    ixs_node *cond = expr->u.pw.cases[i].cond;
    ixs_check_result truth = IXS_CHECK_UNKNOWN;
    if (ixs_node_is_known_false(cond))
      truth = IXS_CHECK_FALSE;
    else if (ixs_node_is_known_true(cond))
      truth = IXS_CHECK_TRUE;
    else if (cond && cond->tag == IXS_CMP)
      truth = ixs_bounds_check(b, cond);
    /* An unknown condition leaves both this value and later values reachable.
     */
    if (truth == IXS_CHECK_FALSE)
      continue;
    reachable = true;
    if (!ixs_bounds_is_integer_with_divinfo(b, expr->u.pw.cases[i].value))
      return false;
    if (truth == IXS_CHECK_TRUE)
      return true;
  }
  return reachable;
}

IXS_STATIC bool ixs_bounds_is_integer_with_divinfo(ixs_bounds *b,
                                                   ixs_node *expr) {
  if (!expr)
    return false;
  if (ixs_node_is_integer_valued(expr))
    return true;
  if (!b)
    return false;

  if (expr->tag == IXS_MUL) {
    uint32_t i;
    int64_t cp, cq, g, denom;
    ixs_node_get_rat(expr->u.mul.coeff, &cp, &cq);
    for (i = 0; i < expr->u.mul.nfactors; i++) {
      if (expr->u.mul.factors[i].exp < 0)
        return false;
      if (!ixs_bounds_is_integer_with_divinfo(b, expr->u.mul.factors[i].base))
        return false;
    }
    if (cq <= 1)
      return true;
    g = ixs_gcd(cp, cq);
    denom = cq / g;
    for (i = 0; i < expr->u.mul.nfactors; i++) {
      if (expr->u.mul.factors[i].exp >= 1 &&
          ixs_bounds_is_known_divisible(b, expr->u.mul.factors[i].base, denom))
        return true;
    }
    return false;
  }

  if (expr->tag == IXS_ADD) {
    uint32_t i;
    if (!ixs_bounds_is_integer_with_divinfo(b, expr->u.add.coeff))
      return false;
    for (i = 0; i < expr->u.add.nterms; i++) {
      int64_t cp, cq;
      ixs_node_get_rat(expr->u.add.terms[i].coeff, &cp, &cq);
      if (cq == 1) {
        if (!ixs_bounds_is_integer_with_divinfo(b, expr->u.add.terms[i].term))
          return false;
      } else {
        int64_t g = ixs_gcd(cp, cq);
        int64_t denom = cq / g;
        if (!ixs_bounds_is_known_divisible(b, expr->u.add.terms[i].term, denom))
          return false;
      }
    }
    return true;
  }

  if (expr->tag == IXS_PIECEWISE)
    return bounds_piecewise_is_integer_with_divinfo(b, expr);

  return false;
}

static bool bounds_interval_point_rational(ixs_interval iv, int64_t *p,
                                           int64_t *q) {
  if (!iv.valid || iv.lo_inf || iv.hi_inf ||
      ixs_rat_cmp(iv.lo_p, iv.lo_q, iv.hi_p, iv.hi_q) != 0)
    return false;
  if (p)
    *p = iv.lo_p;
  if (q)
    *q = iv.lo_q;
  return true;
}

IXS_STATIC ixs_check_result ixs_bounds_check_integer_valued(ixs_bounds *b,
                                                            ixs_node *expr) {
  ixs_interval iv;
  int64_t p, q;
  bool proven;
  if (!b || !expr || b->oom || ixs_bounds_has_empty(b))
    return IXS_CHECK_UNKNOWN;
  proven = ixs_bounds_is_integer_with_divinfo(b, expr);
  if (b->oom)
    return IXS_CHECK_UNKNOWN;
  if (proven)
    return IXS_CHECK_TRUE;
  iv = ixs_bounds_get(b, expr);
  if (b->oom || !bounds_interval_point_rational(iv, &p, &q))
    return IXS_CHECK_UNKNOWN;
  (void)p;
  return q == 1 ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
}

static uint64_t bounds_int64_magnitude(int64_t value) {
  if (value >= 0)
    return (uint64_t)value;
  return (uint64_t)(-(value + 1)) + 1u;
}

static bool bounds_int64_divisible_by_u64(int64_t value, uint64_t modulus) {
  return bounds_int64_magnitude(value) % modulus == 0;
}

IXS_STATIC ixs_check_result ixs_bounds_check_divisible(ixs_bounds *b,
                                                       ixs_node *expr,
                                                       int64_t modulus) {
  ixs_check_result integer_result;
  ixs_interval iv;
  ixs_bitfacts bits;
  uint64_t magnitude;
  int64_t exact;

  if (!b || !expr || modulus == 0 || b->oom || ixs_bounds_has_empty(b))
    return IXS_CHECK_UNKNOWN;

  integer_result = ixs_bounds_check_integer_valued(b, expr);
  if (integer_result != IXS_CHECK_TRUE)
    return integer_result;

  magnitude = bounds_int64_magnitude(modulus);
  if (magnitude == 1u)
    return IXS_CHECK_TRUE;

  iv = ixs_bounds_get(b, expr);
  if (b->oom)
    return IXS_CHECK_UNKNOWN;
  if (ixs_interval_is_point_int(iv, &exact))
    return bounds_int64_divisible_by_u64(exact, magnitude) ? IXS_CHECK_TRUE
                                                           : IXS_CHECK_FALSE;

  if (magnitude <= (uint64_t)INT64_MAX) {
    bool proven = ixs_bounds_is_known_divisible(b, expr, (int64_t)magnitude);
    if (b->oom)
      return IXS_CHECK_UNKNOWN;
    if (proven)
      return IXS_CHECK_TRUE;
  }

  if (magnitude == (uint64_t)INT64_MAX + 1u) {
    bool has_bits = ixs_bounds_get_bitfacts(b, expr, &bits);
    if (b->oom)
      return IXS_CHECK_UNKNOWN;
    if (has_bits && (bits.known_zero & (magnitude - 1u)) == magnitude - 1u)
      return IXS_CHECK_TRUE;
  }

  return IXS_CHECK_UNKNOWN;
}

static ixs_interval bounds_get_and_mask(ixs_node *expr) {
  int64_t mask;
  if (expr->u.logic.nargs != 2)
    return ixs_interval_unknown();
  if (expr->u.logic.args[0]->tag == IXS_INT &&
      expr->u.logic.args[0]->u.ival >= 0) {
    mask = expr->u.logic.args[0]->u.ival;
    return ixs_interval_range(0, 1, mask, 1);
  }
  if (expr->u.logic.args[1]->tag == IXS_INT &&
      expr->u.logic.args[1]->u.ival >= 0) {
    mask = expr->u.logic.args[1]->u.ival;
    return ixs_interval_range(0, 1, mask, 1);
  }
  return ixs_interval_unknown();
}

static inline ixs_interval bounds_get_symbol(ixs_bounds *b, ixs_node *expr) {
  ixs_var_bound *v = find_var(b, expr->u.name);
  return v ? v->iv : ixs_interval_unknown();
}

static inline ixs_interval bounds_get_add(ixs_bounds *b, ixs_node *expr) {
  uint32_t i;
  ixs_interval result = ixs_bounds_get(b, expr->u.add.coeff);
  for (i = 0; i < expr->u.add.nterms; i++) {
    int64_t cp, cq;
    ixs_interval ti = ixs_bounds_get(b, expr->u.add.terms[i].term);
    ixs_interval scaled;
    ixs_node_get_rat(expr->u.add.terms[i].coeff, &cp, &cq);
    scaled = iv_mul_const(ti, cp, cq);
    result = iv_add(result, scaled);
  }
  return result;
}

static inline ixs_interval bounds_get_mul(ixs_bounds *b, ixs_node *expr) {
  uint32_t i;
  int64_t cp, cq;
  ixs_interval result;
  ixs_node_get_rat(expr->u.mul.coeff, &cp, &cq);
  result = ixs_interval_exact(cp, cq);
  for (i = 0; i < expr->u.mul.nfactors; i++) {
    int32_t exp = expr->u.mul.factors[i].exp;
    ixs_interval fi = ixs_bounds_get(b, expr->u.mul.factors[i].base);
    if (!fi.valid)
      return ixs_interval_unknown();
    if (exp == 1) {
      result = iv_mul(result, fi);
    } else if (exp == -1) {
      ixs_interval ri = iv_recip(fi);
      if (!ri.valid)
        return ixs_interval_unknown();
      result = iv_mul(result, ri);
    } else {
      return ixs_interval_unknown();
    }
  }
  return result;
}

static inline ixs_interval bounds_get_mod(ixs_bounds *b, ixs_node *expr) {
  ixs_node *m = expr->u.binary.rhs;
  ixs_interval mi = ixs_bounds_get(b, m);
  int64_t exact_m;

  if (interval_exact_int(&mi, &exact_m) && exact_m > 0) {
    ixs_interval pi = ixs_bounds_get(b, expr->u.binary.lhs);
    if (pi.valid && pi.lo_q == 1 && pi.hi_q == 1 && pi.lo_p >= 0 &&
        pi.hi_p < exact_m)
      return pi;
    if (ixs_node_is_integer_valued(expr->u.binary.lhs)) {
      int64_t g = mod_dividend_gcd(expr->u.binary.lhs, exact_m);
      return ixs_interval_range(0, 1, exact_m - g, 1);
    }
  }

  if (ixs_node_is_integer_valued(expr->u.binary.lhs) &&
      ixs_node_is_integer_valued(m) && interval_lower_at_least(&mi, 1, 1)) {
    ixs_interval result = ixs_interval_unknown();
    result.valid = true;
    result.lo_inf = false;
    result.lo_p = 0;
    result.lo_q = 1;
    if (mi.hi_inf) {
      ixs_interval_set_hi_pos_inf(&result);
    } else {
      int64_t upper = ixs_rat_floor(mi.hi_p, mi.hi_q);
      if (!ixs_safe_sub(upper, 1, &result.hi_p))
        ixs_interval_set_hi_pos_inf(&result);
      else {
        result.hi_q = 1;
        result.hi_inf = false;
      }
    }
    return result;
  }
  return ixs_interval_unknown();
}

static inline ixs_interval bounds_get_round(ixs_bounds *b, ixs_node *expr,
                                            bool is_ceil) {
  ixs_interval ai = ixs_bounds_get(b, expr->u.unary.arg);
  ixs_interval result;
  if (!ai.valid)
    return ixs_interval_unknown();
  if (is_ceil) {
    result = ixs_interval_range(ixs_rat_ceil(ai.lo_p, ai.lo_q), 1,
                                ixs_rat_ceil(ai.hi_p, ai.hi_q), 1);
  } else {
    result = ixs_interval_range(ixs_rat_floor(ai.lo_p, ai.lo_q), 1,
                                ixs_rat_floor(ai.hi_p, ai.hi_q), 1);
  }
  result.lo_inf = ai.lo_inf;
  result.hi_inf = ai.hi_inf;
  return result;
}

static inline void interval_set_max_lower(ixs_interval *result,
                                          const ixs_interval *li,
                                          const ixs_interval *ri) {
  if (li->lo_inf && !ri->lo_inf) {
    result->lo_p = ri->lo_p;
    result->lo_q = ri->lo_q;
  } else if (!li->lo_inf && ri->lo_inf) {
    result->lo_p = li->lo_p;
    result->lo_q = li->lo_q;
  } else if (ixs_rat_cmp(li->lo_p, li->lo_q, ri->lo_p, ri->lo_q) >= 0) {
    result->lo_p = li->lo_p;
    result->lo_q = li->lo_q;
    result->lo_inf = li->lo_inf;
  } else {
    result->lo_p = ri->lo_p;
    result->lo_q = ri->lo_q;
    result->lo_inf = ri->lo_inf;
  }
}

static inline void interval_set_max_upper(ixs_interval *result,
                                          const ixs_interval *li,
                                          const ixs_interval *ri) {
  if (li->hi_inf || ri->hi_inf) {
    ixs_interval_set_hi_pos_inf(result);
  } else if (ixs_rat_cmp(li->hi_p, li->hi_q, ri->hi_p, ri->hi_q) >= 0) {
    result->hi_p = li->hi_p;
    result->hi_q = li->hi_q;
  } else {
    result->hi_p = ri->hi_p;
    result->hi_q = ri->hi_q;
  }
}

static inline void interval_set_min_lower(ixs_interval *result,
                                          const ixs_interval *li,
                                          const ixs_interval *ri) {
  if (li->lo_inf || ri->lo_inf) {
    ixs_interval_set_lo_neg_inf(result);
  } else if (ixs_rat_cmp(li->lo_p, li->lo_q, ri->lo_p, ri->lo_q) <= 0) {
    result->lo_p = li->lo_p;
    result->lo_q = li->lo_q;
  } else {
    result->lo_p = ri->lo_p;
    result->lo_q = ri->lo_q;
  }
}

static inline void interval_set_min_upper(ixs_interval *result,
                                          const ixs_interval *li,
                                          const ixs_interval *ri) {
  if (li->hi_inf && !ri->hi_inf) {
    result->hi_p = ri->hi_p;
    result->hi_q = ri->hi_q;
  } else if (!li->hi_inf && ri->hi_inf) {
    result->hi_p = li->hi_p;
    result->hi_q = li->hi_q;
  } else if (ixs_rat_cmp(li->hi_p, li->hi_q, ri->hi_p, ri->hi_q) <= 0) {
    result->hi_p = li->hi_p;
    result->hi_q = li->hi_q;
    result->hi_inf = li->hi_inf;
  } else {
    result->hi_p = ri->hi_p;
    result->hi_q = ri->hi_q;
    result->hi_inf = ri->hi_inf;
  }
}

static inline ixs_interval bounds_get_extrema(ixs_bounds *b, ixs_node *expr,
                                              bool is_max) {
  ixs_interval li = ixs_bounds_get(b, expr->u.binary.lhs);
  ixs_interval ri = ixs_bounds_get(b, expr->u.binary.rhs);
  ixs_interval result;
  if (!li.valid || !ri.valid)
    return ixs_interval_unknown();
  result.valid = true;
  result.lo_inf = false;
  result.hi_inf = false;
  if (is_max) {
    interval_set_max_lower(&result, &li, &ri);
    interval_set_max_upper(&result, &li, &ri);
  } else {
    interval_set_min_lower(&result, &li, &ri);
    interval_set_min_upper(&result, &li, &ri);
  }
  return result;
}

static inline ixs_interval bounds_get_propagated(ixs_bounds *b,
                                                 ixs_node *expr) {
  if (!expr)
    return ixs_interval_unknown();

  switch (expr->tag) {
  case IXS_INT:
    return ixs_interval_exact(expr->u.ival, 1);
  case IXS_RAT:
    return ixs_interval_exact(expr->u.rat.p, expr->u.rat.q);
  case IXS_SYM:
    return bounds_get_symbol(b, expr);
  case IXS_ADD:
    return bounds_get_add(b, expr);
  case IXS_MUL:
    return bounds_get_mul(b, expr);
  case IXS_MOD:
    return bounds_get_mod(b, expr);
  case IXS_FLOOR:
    return bounds_get_round(b, expr, false);
  case IXS_CEIL:
    return bounds_get_round(b, expr, true);
  case IXS_MAX:
    return bounds_get_extrema(b, expr, true);
  case IXS_MIN:
    return bounds_get_extrema(b, expr, false);
  case IXS_AND:
    return bounds_get_and_mask(expr);
  default:
    return ixs_interval_unknown();
  }
}

static ixs_interval bounds_get_expr_overrides(ixs_bounds *b, ixs_node *expr) {
  ixs_interval iv = ixs_interval_unknown();
  size_t j;
  if (!b || !expr)
    return iv;
  for (j = 0; j < b->nexprs; j++) {
    if (b->exprs[j].expr == expr)
      iv = iv_intersect(iv, b->exprs[j].iv);
  }
  return iv;
}

IXS_STATIC ixs_interval ixs_bounds_get(ixs_bounds *b, ixs_node *expr) {
  ixs_interval iv;
  ixs_node *canon;
  if (!b)
    return ixs_interval_unknown();
  if (bounds_cacheable_expr(expr) && bounds_cache_lookup(b, expr, &iv))
    return iv;

  iv = bounds_get_propagated(b, expr);
  if (b->nexprs && expr) {
    iv = iv_intersect(iv, bounds_get_expr_overrides(b, expr));
    canon = bounds_canonical_expr(b, expr);
    if (canon && canon != expr)
      iv = iv_intersect(iv, bounds_get_expr_overrides(b, canon));
  }
  if (bounds_cacheable_expr(expr))
    bounds_cache_store(b, expr, iv);
  return iv;
}

IXS_STATIC bool ixs_bounds_has_empty(ixs_bounds *b) {
  size_t i, j;

  if (b->contradiction)
    return true;

  for (i = 0; i < b->nvars; i++) {
    refine_var_bit_consistency(b, &b->vars[i]);
    if (b->contradiction)
      return true;
    if (ixs_interval_is_empty(b->vars[i].iv))
      return true;
  }

  for (i = 0; i < b->nexprs; i++) {
    ixs_interval iv = b->exprs[i].iv;
    for (j = i + 1; j < b->nexprs; j++) {
      if (b->exprs[j].expr == b->exprs[i].expr) {
        iv = iv_intersect(iv, b->exprs[j].iv);
        if (!iv.valid || ixs_interval_is_empty(iv))
          return true;
      }
    }
  }

  return false;
}

typedef struct {
  ixs_node *dividend;
  int64_t modulus;
  int64_t remainder;
} ixs_mod_query;

static bool bounds_extract_mod_query(ixs_node *expr, ixs_mod_query *out) {
  ixs_node *mod_node;
  int64_t rem_val;

  if (!expr || !out)
    return false;

  if (expr->tag == IXS_MOD) {
    mod_node = expr;
    rem_val = 0;
  } else if (expr->tag == IXS_ADD && expr->u.add.nterms == 1 &&
             expr->u.add.terms[0].term->tag == IXS_MOD) {
    int64_t cp, cq, kp, kq;
    ixs_node_get_rat(expr->u.add.terms[0].coeff, &cp, &cq);
    ixs_node_get_rat(expr->u.add.coeff, &kp, &kq);
    if (cq != 1 || kq != 1)
      return false;
    if (cp == 1) {
      if (kp == INT64_MIN)
        return false;
      rem_val = -kp;
    } else if (cp == -1) {
      rem_val = kp;
    } else {
      return false;
    }
    mod_node = expr->u.add.terms[0].term;
  } else {
    return false;
  }

  if (mod_node->u.binary.rhs->tag != IXS_INT ||
      mod_node->u.binary.rhs->u.ival <= 0)
    return false;

  out->dividend = mod_node->u.binary.lhs;
  out->modulus = mod_node->u.binary.rhs->u.ival;
  out->remainder = rem_val;
  return true;
}

static ixs_check_result bounds_check_mod_query(ixs_bounds *b, ixs_node *cmp) {
  ixs_mod_query q;
  int64_t actual;
  bool known = false;
  bool equal;

  if (cmp->u.binary.cmp_op != IXS_CMP_EQ && cmp->u.binary.cmp_op != IXS_CMP_NE)
    return IXS_CHECK_UNKNOWN;
  if (!bounds_extract_mod_query(cmp->u.binary.lhs, &q))
    return IXS_CHECK_UNKNOWN;

  if (q.remainder < 0 || q.remainder >= q.modulus) {
    if (cmp->u.binary.cmp_op == IXS_CMP_EQ)
      return IXS_CHECK_FALSE;
    return IXS_CHECK_TRUE;
  }

  if (q.dividend->tag == IXS_INT) {
    actual = ((q.dividend->u.ival % q.modulus) + q.modulus) % q.modulus;
    known = true;
  } else if (q.dividend->tag == IXS_SYM) {
    int64_t sym_mod, sym_rem;
    if (ixs_bounds_get_modrem(b, q.dividend->u.name, &sym_mod, &sym_rem) &&
        sym_mod % q.modulus == 0) {
      actual = sym_rem % q.modulus;
      known = true;
    }
  }

  if (!known && q.remainder == 0 &&
      ixs_bounds_is_known_divisible(b, q.dividend, q.modulus)) {
    actual = 0;
    known = true;
  }

  if (!known)
    return IXS_CHECK_UNKNOWN;

  equal = actual == q.remainder;
  if (cmp->u.binary.cmp_op == IXS_CMP_EQ)
    return equal ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
  return equal ? IXS_CHECK_FALSE : IXS_CHECK_TRUE;
}

static ixs_check_result check_equal_result(ixs_cmp_op op, bool equal) {
  if (op == IXS_CMP_EQ)
    return equal ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
  if (op == IXS_CMP_NE)
    return equal ? IXS_CHECK_FALSE : IXS_CHECK_TRUE;
  return IXS_CHECK_UNKNOWN;
}

static ixs_check_result bounds_check_pow2_query(ixs_bounds *b, ixs_node *cmp,
                                                ixs_node *expr, int64_t value) {
  const char *name;
  ixs_node sym_tmp;
  if (!extract_pow2_and(expr, &name))
    return IXS_CHECK_UNKNOWN;
  memset(&sym_tmp, 0, sizeof(sym_tmp));
  sym_tmp.tag = IXS_SYM;
  sym_tmp.u.name = name;
  if (!ixs_bounds_is_pow2_or_zero(b, &sym_tmp))
    return IXS_CHECK_UNKNOWN;
  return check_equal_result(cmp->u.binary.cmp_op, value == 0);
}

static ixs_check_result bounds_check_and_mask_query(ixs_bounds *b,
                                                    ixs_node *cmp,
                                                    ixs_node *expr,
                                                    int64_t value) {
  const char *name;
  int64_t mask;
  uint64_t mask_bits, value_bits, known;
  ixs_node sym_tmp;
  ixs_bitfacts bits;
  bool equal;

  if (!extract_bitop_sym_mask(expr, IXS_AND, &name, &mask))
    return IXS_CHECK_UNKNOWN;

  /* A non-negative constant mask makes the result a finite int64 value whose
   * high bits are all zero.  Negative masks leave untracked high bits live. */
  if (mask < 0)
    return IXS_CHECK_UNKNOWN;

  mask_bits = (uint64_t)mask;
  value_bits = (uint64_t)value;
  if (value < 0 || (value_bits & ~mask_bits) != 0)
    return check_equal_result(cmp->u.binary.cmp_op, false);

  sym_tmp.tag = IXS_SYM;
  sym_tmp.hash = 0;
  sym_tmp.u.name = name;
  if (!ixs_bounds_get_bitfacts(b, &sym_tmp, &bits))
    return IXS_CHECK_UNKNOWN;

  if ((bits.known_one & mask_bits & ~value_bits) != 0 ||
      (bits.known_zero & mask_bits & value_bits) != 0)
    return check_equal_result(cmp->u.binary.cmp_op, false);

  known = (bits.known_zero | bits.known_one) & mask_bits;
  if (known != mask_bits)
    return IXS_CHECK_UNKNOWN;

  equal = (bits.known_one & mask_bits) == (value_bits & mask_bits);
  return check_equal_result(cmp->u.binary.cmp_op, equal);
}

static ixs_check_result bounds_check_bit_query(ixs_bounds *b, ixs_node *cmp) {
  ixs_node *expr;
  int64_t value;
  ixs_check_result r;

  if (cmp->u.binary.cmp_op != IXS_CMP_EQ && cmp->u.binary.cmp_op != IXS_CMP_NE)
    return IXS_CHECK_UNKNOWN;
  if (!extract_cmp_expr_const(cmp, &expr, &value))
    return IXS_CHECK_UNKNOWN;

  r = bounds_check_pow2_query(b, cmp, expr, value);
  if (r != IXS_CHECK_UNKNOWN)
    return r;

  return bounds_check_and_mask_query(b, cmp, expr, value);
}

static ixs_check_result interval_check_zero(const ixs_interval *iv,
                                            ixs_cmp_op op) {
  int lo_cmp = ixs_rat_cmp(iv->lo_p, iv->lo_q, 0, 1);
  int hi_cmp = ixs_rat_cmp(iv->hi_p, iv->hi_q, 0, 1);
  switch (op) {
  case IXS_CMP_GT:
    if (lo_cmp > 0)
      return IXS_CHECK_TRUE;
    if (hi_cmp <= 0)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_GE:
    if (lo_cmp >= 0)
      return IXS_CHECK_TRUE;
    if (hi_cmp < 0)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_LT:
    if (hi_cmp < 0)
      return IXS_CHECK_TRUE;
    if (lo_cmp >= 0)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_LE:
    if (hi_cmp <= 0)
      return IXS_CHECK_TRUE;
    if (lo_cmp > 0)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_EQ:
    if (lo_cmp == 0 && hi_cmp == 0)
      return IXS_CHECK_TRUE;
    if (lo_cmp > 0 || hi_cmp < 0)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_NE:
    if (lo_cmp > 0 || hi_cmp < 0)
      return IXS_CHECK_TRUE;
    if (lo_cmp == 0 && hi_cmp == 0)
      return IXS_CHECK_FALSE;
    break;
  }
  return IXS_CHECK_UNKNOWN;
}

IXS_STATIC ixs_check_result ixs_bounds_check(ixs_bounds *b, ixs_node *cmp) {
  ixs_interval iv;
  ixs_check_result mod_result, bit_result;

  if (!cmp || cmp->tag != IXS_CMP || !ixs_node_is_zero(cmp->u.binary.rhs))
    return IXS_CHECK_UNKNOWN;

  if (ixs_bounds_has_empty(b))
    return IXS_CHECK_UNKNOWN;

  mod_result = bounds_check_mod_query(b, cmp);
  if (mod_result != IXS_CHECK_UNKNOWN)
    return mod_result;

  bit_result = bounds_check_bit_query(b, cmp);
  if (bit_result != IXS_CHECK_UNKNOWN)
    return bit_result;

  iv = ixs_bounds_get(b, cmp->u.binary.lhs);
  if (!iv.valid)
    return IXS_CHECK_UNKNOWN;

  return interval_check_zero(&iv, cmp->u.binary.cmp_op);
}

static ixs_bounds_build_status assumption_invalid(ixs_bounds *b,
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

static ixs_bounds_build_status bounds_ingest_predicate(ixs_bounds *b,
                                                       ixs_node *pred) {
  ixs_node *stack[ASSUMPTION_NODE_LIMIT];
  size_t nstack = 0;
  size_t visited = 0;

  if (!pred)
    return assumption_invalid(b, "NULL predicate");
  stack[nstack++] = pred;

  while (nstack > 0) {
    ixs_node *cur = stack[--nstack];
    uint32_t i;

    if (++visited > ASSUMPTION_NODE_LIMIT)
      return assumption_invalid(b, "predicate node limit (1024) exceeded");
    if (!cur)
      return assumption_invalid(b, "NULL predicate child");
    if (!ixs_ctx_owns_node(b->ctx, cur))
      return assumption_invalid(b, "predicate belongs to a different context");
    if (ixs_node_is_sentinel(cur))
      return assumption_invalid(b, "sentinel predicates are not accepted");

    if (cur == b->ctx->node_true)
      continue;
    if (cur == b->ctx->node_false) {
      b->contradiction = true;
      bounds_cache_clear(b);
      continue;
    }

    if (cur->tag == IXS_CMP) {
      ixs_node *lhs = cur->u.binary.lhs;
      ixs_node *rhs = cur->u.binary.rhs;
      if (!lhs || !rhs || !assumption_cmp_op_valid(cur->u.binary.cmp_op))
        return assumption_invalid(b, "malformed CMP predicate");
      if (!ixs_ctx_owns_node(b->ctx, lhs) || !ixs_ctx_owns_node(b->ctx, rhs))
        return assumption_invalid(b,
                                  "CMP child belongs to a different context");
      if (ixs_node_is_sentinel(lhs) || ixs_node_is_sentinel(rhs))
        return assumption_invalid(b, "sentinel CMP children are not accepted");
      if (!ixs_bounds_add_assumption(b, cur))
        return IXS_BOUNDS_BUILD_OOM;
      continue;
    }

    if (cur->tag == IXS_AND) {
      if (cur->u.logic.nargs < 2 || !cur->u.logic.args)
        return assumption_invalid(b, "malformed AND predicate");
      if ((size_t)cur->u.logic.nargs > ASSUMPTION_NODE_LIMIT - nstack)
        return assumption_invalid(b, "predicate node limit (1024) exceeded");
      for (i = cur->u.logic.nargs; i > 0; i--)
        stack[nstack++] = cur->u.logic.args[i - 1];
      continue;
    }

    if (cur->tag == IXS_OR)
      return assumption_invalid(b, "OR predicates are not supported");
    if (cur->tag == IXS_NOT)
      return assumption_invalid(b, "NOT predicates are not supported");
    return assumption_invalid(
        b, "expected a CMP, AND, or boolean constant predicate");
  }

  return IXS_BOUNDS_BUILD_OK;
}

IXS_STATIC ixs_bounds_build_status
ixs_bounds_build_ctx(ixs_bounds *b, ixs_ctx *ctx, ixs_arena *scratch,
                     ixs_node *const *assumptions, size_t n_assumptions) {
  size_t i;
  ixs_bounds_build_status status;

  if (n_assumptions > 0 && !assumptions) {
    ixs_ctx_push_error(ctx, "assumptions: NULL array with nonzero count");
    return IXS_BOUNDS_BUILD_INVALID;
  }
  if (!ixs_bounds_init_ctx(b, ctx, scratch))
    return IXS_BOUNDS_BUILD_OOM;
  for (i = 0; i < n_assumptions; i++) {
    status = bounds_ingest_predicate(b, assumptions[i]);
    if (status != IXS_BOUNDS_BUILD_OK)
      return status;
  }
  return IXS_BOUNDS_BUILD_OK;
}

static bool range_result_to_interval(const ixs_range_result *range,
                                     ixs_interval *out) {
  ixs_interval iv;
  if (!range || !out)
    return false;
  iv.valid = true;
  iv.lo_inf = false;
  iv.hi_inf = false;
  if (range->has_lower) {
    if (!ixs_rat_normalize(range->lower_p, range->lower_q, &iv.lo_p, &iv.lo_q))
      return false;
  } else {
    ixs_interval_set_lo_neg_inf(&iv);
  }
  if (range->has_upper) {
    if (!ixs_rat_normalize(range->upper_p, range->upper_q, &iv.hi_p, &iv.hi_q))
      return false;
  } else {
    ixs_interval_set_hi_pos_inf(&iv);
  }
  if (ixs_interval_is_empty(iv))
    return false;
  *out = iv;
  return true;
}

static void interval_to_range_result(ixs_interval iv, ixs_range_result *out) {
  out->has_lower = !iv.lo_inf;
  out->has_upper = !iv.hi_inf;
  out->lower_p = iv.lo_inf ? 0 : iv.lo_p;
  out->lower_q = iv.lo_inf ? 1 : iv.lo_q;
  out->upper_p = iv.hi_inf ? 0 : iv.hi_p;
  out->upper_q = iv.hi_inf ? 1 : iv.hi_q;
}

static bool facts_bind(ixs_facts *facts, ixs_session_binding *binding,
                       ixs_ctx **ctx) {
  if (!facts || !facts->impl || !binding || !ctx)
    return false;
  *ctx = ixs_session_bind_impl(binding, facts->impl);
  facts->bounds.ctx = *ctx;
  facts->bounds.scratch = &(*ctx)->scratch;
  return true;
}

static bool facts_node_ok(ixs_ctx *ctx, ixs_node *node) {
  return node && !ixs_node_is_sentinel(node) && ixs_ctx_owns_node(ctx, node);
}

static void bounds_add_var_fact(ixs_bounds *dst, const ixs_var_bound *src) {
  ixs_var_bound *v = find_var(dst, src->name);
  bounds_cache_clear(dst);
  if (!v) {
    v = get_or_create_var(dst, src->name);
    if (!v)
      return;
    *v = *src;
    refine_var_bit_consistency(dst, v);
    return;
  }

  v->iv = iv_intersect(v->iv, src->iv);
  if (src->modulus > 0)
    apply_modrem(dst, src->name, src->modulus, src->remainder);
  apply_var_known_bits(dst, v, src->bits.known_zero, src->bits.known_one);
  apply_pow2_fact(dst, v, src->bits.pow2);
}

static void bounds_add_all_facts(ixs_bounds *dst, const ixs_bounds *src) {
  size_t i;
  dst->contradiction = dst->contradiction || src->contradiction;
  for (i = 0; i < src->nvars; i++)
    bounds_add_var_fact(dst, &src->vars[i]);
  for (i = 0; i < src->nexprs; i++)
    ixs_bounds_add_expr(dst, src->exprs[i].expr, src->exprs[i].iv);
}

ixs_facts *ixs_facts_create(ixs_session *s) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_facts *facts;
  if (!s)
    return NULL;
  ctx = ixs_session_bind(&binding, s);
  facts = ixs_arena_alloc(&ctx->scratch, sizeof(*facts), sizeof(void *));
  if (!facts) {
    ixs_session_unbind(&binding);
    return NULL;
  }
  memset(facts, 0, sizeof(*facts));
  facts->impl = binding.impl;
  if (!ixs_bounds_init_ctx(&facts->bounds, ctx, &ctx->scratch)) {
    ixs_session_unbind(&binding);
    return NULL;
  }
  ixs_session_unbind(&binding);
  return facts;
}

bool ixs_facts_assume_pred(ixs_facts *facts, ixs_node *pred) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds candidate;
  ixs_bounds_build_status status;
  if (!facts_bind(facts, &binding, &ctx))
    return false;
  mark = ixs_arena_save(&ctx->scratch);
  if (!ixs_bounds_fork(&candidate, &facts->bounds)) {
    ixs_arena_restore(&ctx->scratch, mark);
    ixs_session_unbind(&binding);
    return false;
  }
  status = bounds_ingest_predicate(&candidate, pred);
  if (status == IXS_BOUNDS_BUILD_OK) {
    facts->bounds = candidate;
  } else {
    ixs_arena_restore(&ctx->scratch, mark);
  }
  ixs_session_unbind(&binding);
  return status == IXS_BOUNDS_BUILD_OK;
}

bool ixs_facts_assume_range(ixs_facts *facts, ixs_node *expr,
                            const ixs_range_result *range) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_interval iv;
  bool ok;
  if (!facts_bind(facts, &binding, &ctx))
    return false;
  ok = facts_node_ok(ctx, expr) && range_result_to_interval(range, &iv);
  if (ok)
    ixs_bounds_add_expr(&facts->bounds, expr, iv);
  ixs_session_unbind(&binding);
  return ok;
}

bool ixs_facts_derive_affine(ixs_facts *facts, ixs_node *base, int64_t scale,
                             int64_t offset, ixs_node *derived) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_interval iv, shifted;
  bool ok = false;
  if (!facts_bind(facts, &binding, &ctx))
    return false;
  if (!facts_node_ok(ctx, base) || !facts_node_ok(ctx, derived))
    goto cleanup;
  iv = ixs_bounds_get(&facts->bounds, base);
  if (!iv.valid || ixs_interval_is_empty(iv))
    goto cleanup;
  shifted = iv_add(iv_mul_const(iv, scale, 1), ixs_interval_exact(offset, 1));
  if (!shifted.valid || ixs_interval_is_empty(shifted))
    goto cleanup;
  ixs_bounds_add_expr(&facts->bounds, derived, shifted);
  ok = true;

cleanup:
  ixs_session_unbind(&binding);
  return ok;
}

bool ixs_facts_substitute(ixs_facts *dst, const ixs_facts *src,
                          ixs_node *target, ixs_node *replacement) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  size_t nexprs, nvars, i;
  bool ok = false;

  if (!dst || !dst->impl || !src || !src->impl ||
      dst->impl->ctx != src->impl->ctx)
    return false;
  if (!facts_bind(dst, &binding, &ctx))
    return false;
  if (!facts_node_ok(ctx, target) || !facts_node_ok(ctx, replacement))
    goto cleanup;

  nexprs = src->bounds.nexprs;
  nvars = src->bounds.nvars;

  if (dst->bounds.nexprs == 0 && dst->bounds.nvars == 0) {
    ixs_bounds forked;
    if (!ixs_bounds_fork(&forked, &src->bounds))
      goto cleanup;
    forked.ctx = ctx;
    forked.scratch = &ctx->scratch;
    dst->bounds = forked;
  } else {
    /* Source symbol facts carry pow2, bit, and modular information; copying
     * expression ranges alone loses public facts for non-empty destinations. */
    bounds_add_all_facts(&dst->bounds, &src->bounds);
  }

  for (i = 0; i < nexprs; i++) {
    ixs_node *subst =
        simp_subs(ctx, src->bounds.exprs[i].expr, target, replacement);
    if (!subst)
      goto cleanup;
    ixs_bounds_add_expr(&dst->bounds, subst, src->bounds.exprs[i].iv);
  }
  for (i = 0; i < nvars; i++) {
    ixs_node *sym = ixs_node_sym(ctx, src->bounds.vars[i].name,
                                 strlen(src->bounds.vars[i].name));
    ixs_node *subst;
    if (!sym)
      goto cleanup;
    subst = simp_subs(ctx, sym, target, replacement);
    if (!subst)
      goto cleanup;
    ixs_bounds_add_expr(&dst->bounds, subst, src->bounds.vars[i].iv);
  }
  ok = true;

cleanup:
  ixs_session_unbind(&binding);
  return ok;
}

ixs_check_result ixs_check_facts(ixs_facts *facts, ixs_node *expr) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  if (!facts_bind(facts, &binding, &ctx))
    return IXS_CHECK_UNKNOWN;
  if (facts_node_ok(ctx, expr))
    result = ixs_bounds_check(&facts->bounds, expr);
  ixs_session_unbind(&binding);
  return result;
}

ixs_check_result ixs_check_integer_valued_facts(ixs_facts *facts,
                                                ixs_node *expr) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  if (!facts_bind(facts, &binding, &ctx))
    return IXS_CHECK_UNKNOWN;
  if (facts_node_ok(ctx, expr))
    result = ixs_bounds_check_integer_valued(&facts->bounds, expr);
  ixs_session_unbind(&binding);
  return result;
}

ixs_check_result ixs_check_divisible_facts(ixs_facts *facts, ixs_node *expr,
                                           int64_t modulus) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  if (!facts_bind(facts, &binding, &ctx))
    return IXS_CHECK_UNKNOWN;
  if (modulus == 0) {
    ixs_ctx_push_error(ctx, "divisibility: modulus must be nonzero");
    goto cleanup;
  }
  if (facts_node_ok(ctx, expr))
    result = ixs_bounds_check_divisible(&facts->bounds, expr, modulus);

cleanup:
  ixs_session_unbind(&binding);
  return result;
}

static ixs_pow2_fact bounds_pow2_fact_from_int64(int64_t value) {
  uint64_t u;
  if (value == 0)
    return IXS_POW2_OR_ZERO;
  if (value < 0)
    return IXS_POW2_UNKNOWN;
  u = (uint64_t)value;
  return (u & (u - 1u)) == 0 ? IXS_POW2_POSITIVE : IXS_POW2_UNKNOWN;
}

ixs_pow2_fact ixs_get_pow2_fact_facts(ixs_facts *facts, ixs_node *expr) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_bitfacts bits;
  ixs_interval iv;
  int64_t exact;
  ixs_pow2_fact result = IXS_POW2_UNKNOWN;
  if (!facts_bind(facts, &binding, &ctx))
    return IXS_POW2_UNKNOWN;
  if (!facts_node_ok(ctx, expr) || ixs_bounds_has_empty(&facts->bounds))
    goto cleanup;
  if (ixs_bounds_get_bitfacts(&facts->bounds, expr, &bits))
    result = bits.pow2;
  if (result == IXS_POW2_UNKNOWN) {
    iv = ixs_bounds_get(&facts->bounds, expr);
    if (ixs_interval_is_point_int(iv, &exact))
      result = bounds_pow2_fact_from_int64(exact);
  }

cleanup:
  ixs_session_unbind(&binding);
  return result;
}

bool ixs_range_facts(ixs_facts *facts, ixs_node *expr, ixs_range_result *out) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_interval iv;
  bool ok = false;
  if (!out)
    return false;
  out->has_lower = false;
  out->has_upper = false;
  out->lower_p = 0;
  out->lower_q = 1;
  out->upper_p = 0;
  out->upper_q = 1;
  if (!facts_bind(facts, &binding, &ctx))
    return false;
  if (!facts_node_ok(ctx, expr) || ixs_bounds_has_empty(&facts->bounds))
    goto cleanup;
  iv = ixs_bounds_get(&facts->bounds, expr);
  if (!iv.valid || ixs_interval_is_empty(iv))
    goto cleanup;
  interval_to_range_result(iv, out);
  ok = true;

cleanup:
  ixs_session_unbind(&binding);
  return ok;
}

IXS_STATIC bool ixs_bounds_get_modrem(ixs_bounds *b, const char *name,
                                      int64_t *mod, int64_t *rem) {
  ixs_var_bound *v;
  if (!mod || !rem)
    return false;
  v = find_var(b, name);
  if (!v || v->modulus <= 0)
    return false;
  *mod = v->modulus;
  *rem = v->remainder;
  return true;
}
