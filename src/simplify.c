/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "simplify.h"
#include "bounds.h"
#include <stdlib.h>
#include <string.h>

#define SIMPLIFY_ITER_LIMIT 64

/* ---- Rule-chain dispatch ----------------------------------------- */
/* Each simplification rule: (ctx, bnds, node) -> node.               */
/* Returns n unchanged = didn't fire; different node = fired; NULL=OOM */

typedef ixs_node *(*ixs_rule_fn)(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *n);

typedef struct {
  ixs_rule_fn fn;
  const char *name;
  bool needs_bounds;
} ixs_rule;

static ixs_node *try_rules(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *n,
                           const ixs_rule *rules) {
  size_t i;
  for (i = 0; rules[i].fn; i++) {
    ixs_node *r;
    if (rules[i].needs_bounds && !bnds)
      continue;
    r = rules[i].fn(ctx, bnds, n);
    if (!r)
      return NULL;
    if (r != n) {
#ifdef IXS_STATS
      ixs_stat_hit(ctx->stats, rules[i].name);
#endif
      return r;
    }
  }
  return n;
}

/* Forward declarations: bounds-dependent helpers defined later. */
static ixs_node *try_floor_ceil_collapse(ixs_ctx *ctx, ixs_bounds *bnds,
                                         ixs_node *arg, bool is_ceil);
static bool is_integer_with_divinfo(ixs_bounds *bnds, ixs_node *expr);
static ixs_node *mod_bounds_elim(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *l,
                                 ixs_node *r);
static ixs_node *max_bounds_collapse(ixs_ctx *ctx, ixs_bounds *bnds,
                                     ixs_node *l, ixs_node *r);
static ixs_node *min_bounds_collapse(ixs_ctx *ctx, ixs_bounds *bnds,
                                     ixs_node *l, ixs_node *r);
static ixs_node *cmp_bounds_resolve(ixs_ctx *ctx, ixs_bounds *bnds,
                                    ixs_node *cmp_node);

/* ------------------------------------------------------------------ */
/*  Helpers                                                           */
/* ------------------------------------------------------------------ */

static ixs_node *simp_err(ixs_ctx *ctx, const char *msg) {
  ixs_ctx_push_error(ctx, "%s", msg);
  return ctx->sentinel_error;
}

/*
 * Double a scratch-allocated array.  Returns the (possibly moved)
 * pointer and updates *cap, or NULL on overflow/OOM.
 */
static void *scratch_grow(ixs_arena *a, void *ptr, size_t *cap,
                          size_t elem_size) {
  size_t old = *cap;
  size_t next = old * 2;
  if (next <= old || next > (size_t)-1 / elem_size)
    return NULL;
  void *p =
      ixs_arena_grow(a, ptr, old * elem_size, next * elem_size, sizeof(void *));
  if (p)
    *cap = next;
  return p;
}

static ixs_node *make_const(ixs_ctx *ctx, int64_t p, int64_t q) {
  if (q == 1)
    return ixs_node_int(ctx, p);
  return ixs_node_rat(ctx, p, q);
}

/*
 * Extract the additive coefficient and base from a node.
 * For MUL(coeff, factors): coefficient = coeff, base = MUL(1, factors)
 * For INT/RAT: pure constant.
 * For anything else: coefficient = 1, base = node.
 */
static void add_decompose(ixs_ctx *ctx, ixs_node *n, int64_t *cp, int64_t *cq,
                          ixs_node **base) {
  if (!n) {
    *cp = 0;
    *cq = 1;
    *base = NULL;
    return;
  }

  if (n->tag == IXS_INT) {
    *cp = n->u.ival;
    *cq = 1;
    *base = NULL;
    return;
  }
  if (n->tag == IXS_RAT) {
    *cp = n->u.rat.p;
    *cq = n->u.rat.q;
    *base = NULL;
    return;
  }
  if (n->tag == IXS_MUL && ixs_node_is_const(n->u.mul.coeff)) {
    ixs_node_get_rat(n->u.mul.coeff, cp, cq);
    if (n->u.mul.nfactors == 1 && n->u.mul.factors[0].exp == 1) {
      *base = n->u.mul.factors[0].base;
    } else {
      *base = ixs_node_mul(ctx, ixs_node_int(ctx, 1), n->u.mul.nfactors,
                           n->u.mul.factors);
      if (!*base) {
        *cp = 1;
        *cq = 1;
        *base = n;
      }
    }
    return;
  }
  *cp = 1;
  *cq = 1;
  *base = n;
}

/* Sorting comparator for addterms by their base node. */
static int addterm_cmp(const void *a, const void *b) {
  const ixs_addterm *ta = (const ixs_addterm *)a;
  const ixs_addterm *tb = (const ixs_addterm *)b;
  return ixs_node_cmp(ta->term, tb->term);
}

/* Sorting comparator for mulfactors by their base node. */
static int mulfactor_cmp(const void *a, const void *b) {
  const ixs_mulfactor *fa = (const ixs_mulfactor *)a;
  const ixs_mulfactor *fb = (const ixs_mulfactor *)b;
  return ixs_node_cmp(fa->base, fb->base);
}

/* Sorting comparator for logic args. */
static int nodeptr_cmp(const void *a, const void *b) {
  const ixs_node *na = *(const ixs_node *const *)a;
  const ixs_node *nb = *(const ixs_node *const *)b;
  return ixs_node_cmp(na, nb);
}

/* ------------------------------------------------------------------ */
/*  simp_add                                                          */
/* ------------------------------------------------------------------ */

/*
 * Mod recognition pass over additive terms.
 *
 *   floor: c*E + d*floor(E/N) where d == -c*N  ->  c*Mod(E, N)
 *   ceil:  c*E + d*ceil(E/N)  where d == -c*N  -> -c*Mod(-E, N)
 *
 * Scans for FLOOR/CEIL terms whose arg is MUL(1/N, [(B, exp=1)]) and a
 * matching base term B with the right coefficient ratio.  Matched
 * terms are NULLed and the result is rebuilt through simp_add.
 * Returns the simplified node, or NULL if no pattern matched.
 */
static ixs_node *recognize_mod(ixs_ctx *ctx, ixs_addterm *terms,
                               uint32_t nterms, int64_t const_p,
                               int64_t const_q) {
  bool found = false;
  uint32_t i, j;

  for (i = 0; i < nterms; i++) {
    int64_t fp, fq, N;
    ixs_node *farg, *fbase;
    bool is_ceil;
    if (!terms[i].term)
      continue;
    if (terms[i].term->tag == IXS_FLOOR)
      is_ceil = false;
    else if (terms[i].term->tag == IXS_CEIL)
      is_ceil = true;
    else
      continue;
    farg = terms[i].term->u.unary.arg;
    if (farg->tag != IXS_MUL)
      continue;
    ixs_node_get_rat(farg->u.mul.coeff, &fp, &fq);
    if (fp != 1 || fq <= 1)
      continue;
    N = fq;
    if (farg->u.mul.nfactors == 1 && farg->u.mul.factors[0].exp == 1) {
      fbase = farg->u.mul.factors[0].base;
    } else {
      fbase = ixs_node_mul(ctx, ixs_node_int(ctx, 1), farg->u.mul.nfactors,
                           farg->u.mul.factors);
      if (!fbase)
        continue;
    }
    if (N == INT64_MIN)
      continue;
    for (j = 0; j < nterms; j++) {
      int64_t bp, bq, rp, rq, want_p, want_q;
      ixs_node *mod_node;
      if (j == i || !terms[j].term || terms[j].term != fbase)
        continue;
      ixs_node_get_rat(terms[j].coeff, &bp, &bq);
      ixs_node_get_rat(terms[i].coeff, &rp, &rq);
      if (!ixs_rat_mul(-N, 1, bp, bq, &want_p, &want_q))
        continue;
      if (rp != want_p || rq != want_q)
        continue;
      if (is_ceil) {
        ixs_node *neg_base;
        if (bp == INT64_MIN)
          continue;
        neg_base = simp_mul(ctx, ixs_node_int(ctx, -1), fbase);
        if (!neg_base)
          return NULL;
        mod_node = simp_mod(ctx, neg_base, ixs_node_int(ctx, N));
        if (!mod_node)
          return NULL;
        terms[j].term = mod_node;
        terms[j].coeff = make_const(ctx, -bp, bq);
        if (!terms[j].coeff)
          return NULL;
      } else {
        mod_node = simp_mod(ctx, fbase, ixs_node_int(ctx, N));
        if (!mod_node)
          return NULL;
        terms[j].term = mod_node;
      }
      terms[i].term = NULL;
      found = true;
      break;
    }
  }

  if (!found)
    return NULL;

  IXS_STAT_HIT(ctx);
  ixs_node *result = make_const(ctx, const_p, const_q);
  if (!result)
    return NULL;
  for (i = 0; i < nterms; i++) {
    ixs_node *t;
    if (!terms[i].term)
      continue;
    t = simp_mul(ctx, terms[i].coeff, terms[i].term);
    if (!t)
      return NULL;
    result = simp_add(ctx, result, t);
    if (!result)
      return NULL;
  }
  return result;
}

static ixs_node *simp_add_impl(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  ixs_node *prop;
  int64_t const_p = 0, const_q = 1;
  size_t cap = 16;
  ixs_addterm *terms =
      ixs_arena_alloc(&ctx->scratch, cap * sizeof(*terms), sizeof(void *));
  if (!terms)
    return NULL;
  uint32_t nterms = 0;
  uint32_t i, j;

  if (!a || !b)
    return NULL;
  prop = ixs_propagate2(a, b);
  if (prop)
    return prop;

  /* Gather all additive components from a and b. */
  ixs_node *inputs[2];
  inputs[0] = a;
  inputs[1] = b;

  for (i = 0; i < 2; i++) {
    ixs_node *x = inputs[i];
    if (x->tag == IXS_ADD) {
      int64_t cp, cq;
      ixs_node_get_rat(x->u.add.coeff, &cp, &cq);
      if (!ixs_rat_add(const_p, const_q, cp, cq, &const_p, &const_q))
        goto overflow;
      for (j = 0; j < x->u.add.nterms; j++) {
        if (nterms >= cap) {
          terms = scratch_grow(&ctx->scratch, terms, &cap, sizeof(*terms));
          if (!terms)
            return NULL;
        }
        terms[nterms++] = x->u.add.terms[j];
      }
    } else {
      int64_t cp, cq;
      ixs_node *base;
      add_decompose(ctx, x, &cp, &cq, &base);
      if (!base) {
        if (!ixs_rat_add(const_p, const_q, cp, cq, &const_p, &const_q))
          goto overflow;
      } else if (base->tag == IXS_ADD) {
        /* Distribute coefficient: cp/cq * ADD(c, [ci*bi, ...]) */
        int64_t bp, bq;
        ixs_node_get_rat(base->u.add.coeff, &bp, &bq);
        int64_t rp, rq;
        if (!ixs_rat_mul(cp, cq, bp, bq, &rp, &rq))
          goto overflow;
        if (!ixs_rat_add(const_p, const_q, rp, rq, &const_p, &const_q))
          goto overflow;
        for (j = 0; j < base->u.add.nterms; j++) {
          int64_t tp, tq;
          ixs_node_get_rat(base->u.add.terms[j].coeff, &tp, &tq);
          int64_t np, nq;
          if (!ixs_rat_mul(cp, cq, tp, tq, &np, &nq))
            goto overflow;
          if (nterms >= cap) {
            terms = scratch_grow(&ctx->scratch, terms, &cap, sizeof(*terms));
            if (!terms)
              return NULL;
          }
          terms[nterms].term = base->u.add.terms[j].term;
          terms[nterms].coeff = make_const(ctx, np, nq);
          if (!terms[nterms].coeff)
            return NULL;
          nterms++;
        }
      } else {
        if (nterms >= cap) {
          terms = scratch_grow(&ctx->scratch, terms, &cap, sizeof(*terms));
          if (!terms)
            return NULL;
        }
        terms[nterms].term = base;
        terms[nterms].coeff = make_const(ctx, cp, cq);
        if (!terms[nterms].coeff)
          return NULL;
        nterms++;
      }
    }
  }

  /* Sort terms by base. */
  if (nterms > 1)
    qsort(terms, nterms, sizeof(ixs_addterm), addterm_cmp);

  /* Collect like terms. */
  j = 0;
  for (i = 0; i < nterms; i++) {
    if (j > 0 && terms[j - 1].term == terms[i].term) {
      int64_t ap2, aq2, bp2, bq2, rp, rq;
      ixs_node_get_rat(terms[j - 1].coeff, &ap2, &aq2);
      ixs_node_get_rat(terms[i].coeff, &bp2, &bq2);
      if (!ixs_rat_add(ap2, aq2, bp2, bq2, &rp, &rq))
        goto overflow;
      if (ixs_rat_is_zero(rp)) {
        j--;
      } else {
        terms[j - 1].coeff = make_const(ctx, rp, rq);
        if (!terms[j - 1].coeff)
          return NULL;
      }
    } else {
      if (j != i)
        terms[j] = terms[i];
      j++;
    }
  }
  nterms = j;

  {
    ixs_node *mod_result = recognize_mod(ctx, terms, nterms, const_p, const_q);
    if (mod_result)
      return mod_result;
  }

  /* Result cases. */
  if (nterms == 0)
    return make_const(ctx, const_p, const_q);

  if (nterms == 1 && ixs_rat_is_zero(const_p)) {
    int64_t cp, cq;
    ixs_node_get_rat(terms[0].coeff, &cp, &cq);
    if (ixs_rat_is_one(cp, cq))
      return terms[0].term;
    return simp_mul(ctx, make_const(ctx, cp, cq), terms[0].term);
  }

  {
    ixs_node *coeff = make_const(ctx, const_p, const_q);
    if (!coeff)
      return NULL;
    return ixs_node_add(ctx, coeff, nterms, terms);
  }

overflow:
  return simp_err(ctx, "rational overflow in add");
}

ixs_node *simp_add(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  ixs_arena_mark m = ixs_arena_save(&ctx->scratch);
  ixs_node *result = simp_add_impl(ctx, a, b);
  ixs_arena_restore(&ctx->scratch, m);
  return result;
}

/* ------------------------------------------------------------------ */
/*  simp_mul                                                          */
/* ------------------------------------------------------------------ */

static ixs_node *simp_mul_impl(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  ixs_node *prop;
  int64_t coeff_p = 1, coeff_q = 1;
  size_t cap = 16;
  ixs_mulfactor *factors =
      ixs_arena_alloc(&ctx->scratch, cap * sizeof(*factors), sizeof(void *));
  if (!factors)
    return NULL;
  uint32_t nfactors = 0;
  uint32_t i, j;

  if (!a || !b)
    return NULL;
  prop = ixs_propagate2(a, b);
  if (prop)
    return prop;

  /* Gather multiplicative components. */
  ixs_node *inputs[2];
  inputs[0] = a;
  inputs[1] = b;

  for (i = 0; i < 2; i++) {
    ixs_node *x = inputs[i];
    if (ixs_node_is_const(x)) {
      int64_t xp, xq;
      ixs_node_get_rat(x, &xp, &xq);
      if (!ixs_rat_mul(coeff_p, coeff_q, xp, xq, &coeff_p, &coeff_q))
        goto overflow;
    } else if (x->tag == IXS_MUL) {
      int64_t cp, cq;
      ixs_node_get_rat(x->u.mul.coeff, &cp, &cq);
      if (!ixs_rat_mul(coeff_p, coeff_q, cp, cq, &coeff_p, &coeff_q))
        goto overflow;
      for (j = 0; j < x->u.mul.nfactors; j++) {
        if (nfactors >= cap) {
          factors =
              scratch_grow(&ctx->scratch, factors, &cap, sizeof(*factors));
          if (!factors)
            return NULL;
        }
        factors[nfactors++] = x->u.mul.factors[j];
      }
    } else {
      if (nfactors >= cap) {
        factors = scratch_grow(&ctx->scratch, factors, &cap, sizeof(*factors));
        if (!factors)
          return NULL;
      }
      factors[nfactors].base = x;
      factors[nfactors].exp = 1;
      nfactors++;
    }
  }

  /* Short-circuit: coeff is zero -> result is zero. */
  if (ixs_rat_is_zero(coeff_p))
    return ixs_node_int(ctx, 0);

  /* Sort factors by base. */
  if (nfactors > 1)
    qsort(factors, nfactors, sizeof(ixs_mulfactor), mulfactor_cmp);

  /* Collect like bases. */
  j = 0;
  for (i = 0; i < nfactors; i++) {
    if (j > 0 && factors[j - 1].base == factors[i].base) {
      int64_t new_exp = (int64_t)factors[j - 1].exp + (int64_t)factors[i].exp;
      if (new_exp > INT32_MAX || new_exp < INT32_MIN)
        goto overflow;
      if (new_exp == 0) {
        j--;
      } else {
        factors[j - 1].exp = (int32_t)new_exp;
      }
    } else {
      if (j != i)
        factors[j] = factors[i];
      j++;
    }
  }
  nfactors = j;

  /* Result cases. */
  if (nfactors == 0)
    return make_const(ctx, coeff_p, coeff_q);

  if (nfactors == 1 && factors[0].exp == 1 && ixs_rat_is_one(coeff_p, coeff_q))
    return factors[0].base;

  {
    ixs_node *coeff = make_const(ctx, coeff_p, coeff_q);
    if (!coeff)
      return NULL;
    return ixs_node_mul(ctx, coeff, nfactors, factors);
  }

overflow:
  return simp_err(ctx, "rational overflow in multiply");
}

ixs_node *simp_mul(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  ixs_arena_mark m = ixs_arena_save(&ctx->scratch);
  ixs_node *result = simp_mul_impl(ctx, a, b);
  ixs_arena_restore(&ctx->scratch, m);
  return result;
}

/* ------------------------------------------------------------------ */
/*  simp_neg / simp_sub / simp_div                                    */
/* ------------------------------------------------------------------ */

ixs_node *simp_neg(ixs_ctx *ctx, ixs_node *a) {
  ixs_node *prop = ixs_propagate1(a);
  if (prop)
    return prop;
  return simp_mul(ctx, ixs_node_int(ctx, -1), a);
}

ixs_node *simp_sub(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  if (!a || !b)
    return NULL;
  ixs_node *prop = ixs_propagate2(a, b);
  if (prop)
    return prop;
  return simp_add(ctx, a, simp_neg(ctx, b));
}

ixs_node *simp_div(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  if (!a || !b)
    return NULL;
  ixs_node *prop = ixs_propagate2(a, b);
  if (prop)
    return prop;

  /* Division by zero */
  if (ixs_node_is_zero(b))
    return simp_err(ctx, "division by zero");

  /* Constant / constant -> rational fold */
  if (ixs_node_is_const(a) && ixs_node_is_const(b)) {
    int64_t ap, aq, bp, bq, rp, rq;
    ixs_node_get_rat(a, &ap, &aq);
    ixs_node_get_rat(b, &bp, &bq);
    if (!ixs_rat_div(ap, aq, bp, bq, &rp, &rq))
      return simp_err(ctx, "rational overflow in division");
    return make_const(ctx, rp, rq);
  }

  /* expr / constant -> multiply by reciprocal */
  if (ixs_node_is_const(b)) {
    int64_t bp, bq, rp, rq;
    ixs_node_get_rat(b, &bp, &bq);
    if (!ixs_rat_div(1, 1, bp, bq, &rp, &rq))
      return simp_err(ctx, "rational overflow in division");
    return simp_mul(ctx, make_const(ctx, rp, rq), a);
  }

  /* General: a * b^(-1) */
  {
    ixs_mulfactor f;
    f.base = b;
    f.exp = -1;
    ixs_node *binv = ixs_node_mul(ctx, ixs_node_int(ctx, 1), 1, &f);
    if (!binv)
      return NULL;
    return simp_mul(ctx, a, binv);
  }
}

/* ------------------------------------------------------------------ */
/*  simp_floor / simp_ceil                                            */
/* ------------------------------------------------------------------ */

typedef ixs_node *(*round_fn)(ixs_ctx *, ixs_node *);

/* Multiply acc by base^exp via repeated simp_mul/simp_div.
 * Caps magnitude at 64 (matching EXPAND_MAX_EXP) to prevent runaway
 * loops on degenerate exponents.  Returns NULL on OOM or overflow. */
static ixs_node *apply_pow(ixs_ctx *ctx, ixs_node *acc, ixs_node *base,
                           int32_t exp) {
  if (!acc || exp == 0)
    return acc;
  bool pos = (exp > 0);
  int32_t mag = pos ? exp : (exp == INT32_MIN) ? INT32_MAX : -exp;
  if (mag > 64)
    return NULL;
  int32_t i;
  for (i = 0; i < mag && acc; i++)
    acc = pos ? simp_mul(ctx, acc, base) : simp_div(ctx, acc, base);
  return acc;
}

/*
 * Extract integer-valued addends from round(ADD).
 *   round(n + intval_terms + rest) -> n + intval_terms + round(rest)
 * Returns the simplified node, x unchanged if nothing to extract,
 * or NULL on OOM.
 */
static ixs_node *round_extract_add(ixs_ctx *ctx, ixs_node *x, round_fn rnd) {
  if (x->tag != IXS_ADD)
    return x;

  bool have_int = false;
  int64_t rat_fl = 0;
  if (x->u.add.coeff->tag == IXS_INT && x->u.add.coeff->u.ival != 0)
    have_int = true;
  if (!have_int && x->u.add.coeff->tag == IXS_RAT) {
    rat_fl = ixs_rat_floor(x->u.add.coeff->u.rat.p, x->u.add.coeff->u.rat.q);
    if (rat_fl != 0)
      have_int = true;
  }

  uint32_t i;
  for (i = 0; i < x->u.add.nterms && !have_int; i++) {
    int64_t cp, cq;
    ixs_node_get_rat(x->u.add.terms[i].coeff, &cp, &cq);
    if (cq == 1 && ixs_node_is_integer_valued(x->u.add.terms[i].term))
      have_int = true;
  }
  if (!have_int)
    return x;

  ixs_arena_mark m = ixs_arena_save(&ctx->scratch);
  ixs_addterm *kept = ixs_arena_alloc(
      &ctx->scratch, x->u.add.nterms * sizeof(*kept), sizeof(void *));
  if (!kept) {
    ixs_arena_restore(&ctx->scratch, m);
    return NULL;
  }

  uint32_t nk = 0;
  ixs_node *int_sum;
  ixs_node *rem_coeff;
  if (x->u.add.coeff->tag == IXS_INT) {
    int_sum = x->u.add.coeff;
    rem_coeff = ixs_node_int(ctx, 0);
  } else if (x->u.add.coeff->tag == IXS_RAT && rat_fl != 0) {
    int64_t p = x->u.add.coeff->u.rat.p;
    int64_t q = x->u.add.coeff->u.rat.q;
    int64_t prod;
    if (ixs_safe_mul(rat_fl, q, &prod)) {
      int64_t rem_p = p - prod;
      int64_t rp, rq;
      int_sum = ixs_node_int(ctx, rat_fl);
      if (rem_p == 0) {
        rem_coeff = ixs_node_int(ctx, 0);
      } else if (ixs_rat_normalize(rem_p, q, &rp, &rq)) {
        rem_coeff = make_const(ctx, rp, rq);
      } else {
        int_sum = ixs_node_int(ctx, 0);
        rem_coeff = x->u.add.coeff;
      }
    } else {
      int_sum = ixs_node_int(ctx, 0);
      rem_coeff = x->u.add.coeff;
    }
  } else {
    int_sum = ixs_node_int(ctx, 0);
    rem_coeff = x->u.add.coeff;
  }
  if (!int_sum || !rem_coeff) {
    ixs_arena_restore(&ctx->scratch, m);
    return NULL;
  }

  for (i = 0; i < x->u.add.nterms; i++) {
    int64_t cp, cq;
    ixs_node_get_rat(x->u.add.terms[i].coeff, &cp, &cq);
    if (cq == 1 && ixs_node_is_integer_valued(x->u.add.terms[i].term)) {
      int_sum = simp_add(
          ctx, int_sum,
          simp_mul(ctx, x->u.add.terms[i].coeff, x->u.add.terms[i].term));
      if (!int_sum) {
        ixs_arena_restore(&ctx->scratch, m);
        return NULL;
      }
    } else {
      kept[nk++] = x->u.add.terms[i];
    }
  }

  ixs_node *remainder = rem_coeff;
  for (i = 0; i < nk && remainder; i++)
    remainder =
        simp_add(ctx, remainder, simp_mul(ctx, kept[i].coeff, kept[i].term));
  ixs_arena_restore(&ctx->scratch, m);
  if (!remainder)
    return NULL;
  return simp_add(ctx, int_sum, rnd(ctx, remainder));
}

/*
 * Extract integer-valued terms from round(MUL(..., ADD^1)).
 * Distributes the outer (non-ADD) factors into the ADD, then delegates
 * to round_extract_add via recursion through rnd.
 *
 * Decomposes compound MUL bases (e.g. (2*K)^-1 -> 1/2 * K^-1) so that
 * symbolic factor cancellation works through simp_mul/simp_div.
 *
 * Returns the simplified node, x unchanged if nothing to extract,
 * or NULL on OOM.
 */
static ixs_node *round_extract_mul_add(ixs_ctx *ctx, ixs_node *x,
                                       round_fn rnd) {
  if (x->tag != IXS_MUL)
    return x;

  int add_idx = -1;
  uint32_t j;
  for (j = 0; j < x->u.mul.nfactors; j++) {
    if (x->u.mul.factors[j].base->tag == IXS_ADD &&
        x->u.mul.factors[j].exp == 1) {
      add_idx = (int)j;
      break;
    }
  }
  if (add_idx < 0)
    return x;

  ixs_node *add_node = x->u.mul.factors[add_idx].base;

  /* Build outer = coeff * product of non-ADD factors, decomposing
   * any MUL-typed bases so symbolic cancellation works properly. */
  ixs_node *outer = x->u.mul.coeff;
  for (j = 0; j < x->u.mul.nfactors && outer; j++) {
    if ((int)j == add_idx)
      continue;
    ixs_node *fbase = x->u.mul.factors[j].base;
    int32_t fexp = x->u.mul.factors[j].exp;
    if (fbase->tag == IXS_MUL && fexp == -1) {
      /* Decompose MUL base: (c * f1^e1 * ...)^-1 -> 1/c * f1^-e1 * ... */
      int64_t cp, cq;
      ixs_node_get_rat(fbase->u.mul.coeff, &cp, &cq);
      if (cq == 1 && cp != 0) {
        outer = simp_div(ctx, outer, make_const(ctx, cp, cq));
        uint32_t k;
        for (k = 0; k < fbase->u.mul.nfactors && outer; k++) {
          outer = apply_pow(ctx, outer, fbase->u.mul.factors[k].base,
                            -fbase->u.mul.factors[k].exp);
        }
        continue;
      }
    }
    outer = apply_pow(ctx, outer, fbase, fexp);
  }
  if (!outer)
    return NULL;

  /* Check whether distributing outer makes any ADD term integer-valued,
   * OR whether the ADD has a nonzero integer constant and outer is
   * non-integer (distribution exposes the constant for floor_drop_const
   * or floor_drop_const_sym). */
  bool any_int = false;
  ixs_node *coeff_product = simp_mul(ctx, outer, add_node->u.add.coeff);
  if (coeff_product && ixs_node_is_integer_valued(coeff_product))
    any_int = true;
  for (j = 0; j < add_node->u.add.nterms && !any_int; j++) {
    ixs_node *tc = add_node->u.add.terms[j].coeff;
    ixs_node *tt = add_node->u.add.terms[j].term;
    ixs_node *product = simp_mul(ctx, outer, simp_mul(ctx, tc, tt));
    if (product && ixs_node_is_integer_valued(product))
      any_int = true;
  }
  if (!any_int) {
    int64_t ac_p, ac_q;
    ixs_node_get_rat(add_node->u.add.coeff, &ac_p, &ac_q);
    if (ac_p == 0)
      return x;
    if (ixs_node_is_integer_valued(outer))
      return x;
  }

  /* Expand outer * ADD and recurse through rnd(ADD). */
  ixs_node *expanded = simp_mul(ctx, outer, add_node->u.add.coeff);
  for (j = 0; j < add_node->u.add.nterms && expanded; j++) {
    ixs_node *tc = add_node->u.add.terms[j].coeff;
    ixs_node *tt = add_node->u.add.terms[j].term;
    expanded =
        simp_add(ctx, expanded, simp_mul(ctx, outer, simp_mul(ctx, tc, tt)));
  }
  if (!expanded)
    return NULL;
  return rnd(ctx, expanded);
}

/*
 * Drop a small positive constant from floor(ADD(c, [ci*bi, ...])) when
 * every bi is integer-valued and 0 < c < 1/lcm(qi).
 *
 * Proof: each ci*bi lies on a grid with spacing 1/qi.  Their sum lies
 * on a grid with spacing 1/L where L = lcm(qi).  Adding c < 1/L cannot
 * push past the next grid point, so floor is unchanged.
 *
 * Returns the ADD rebuilt without c, x unchanged if rule doesn't apply,
 * or NULL on OOM.
 */
static ixs_node *floor_drop_const(ixs_ctx *ctx, ixs_node *x) {
  if (x->tag != IXS_ADD || x->u.add.nterms == 0)
    return x;
  int64_t cp, cq;
  ixs_node_get_rat(x->u.add.coeff, &cp, &cq);
  if (cp <= 0 || cq <= 0)
    return x;
  int64_t lcm = 1;
  uint32_t i;
  for (i = 0; i < x->u.add.nterms; i++) {
    if (!ixs_node_is_integer_valued(x->u.add.terms[i].term))
      return x;
    int64_t tp, tq;
    ixs_node_get_rat(x->u.add.terms[i].coeff, &tp, &tq);
    if (tq <= 0)
      return x;
    int64_t g = ixs_gcd(lcm, tq);
    if (tq / g > (1LL << 30) / lcm) /* cap lcm to avoid overflow */
      return x;
    lcm = lcm / g * tq;
  }
  /* c < 1/lcm  <=>  cp * lcm < cq (guarded against overflow) */
  int64_t cl;
  if (!ixs_safe_mul(cp, lcm, &cl) || cl >= cq)
    return x;
  ixs_node *sum = ixs_node_int(ctx, 0);
  for (i = 0; i < x->u.add.nterms && sum; i++)
    sum = simp_add(
        ctx, sum,
        simp_mul(ctx, x->u.add.terms[i].coeff, x->u.add.terms[i].term));
  return sum;
}

/*
 * Drop a small positive constant from floor(ADD) when all terms share
 * a common symbolic denominator D^-1.
 *
 * Given floor(c1*t1/D + c2*t2/D + ... + k/D) where the ti are
 * integer-valued: clear rational denominators to get integer numerator
 * coefficients ni, compute g = gcd(|ni|) for the non-constant terms,
 * and reduce the constant modulo gcd(g, lcm_of_rational_denoms).
 *
 * Proof sketch: let N = sum(ni*ti).  N is always a multiple of g.
 * The effective denominator is L*D (concrete L, symbolic D).  Since
 * gcd(g, L*D) >= gcd(g, L) for any positive integer D, adding r < gcd(g,L)
 * to N cannot push past the next multiple of gcd(g,L*D), so the floor
 * is unchanged.  Therefore floor((N+C)/(L*D)) = floor((N+C')/(L*D))
 * whenever C ≡ C' (mod gcd(g, L)).
 */

/* Check that every term in an ADD is MUL and contains denom^-1. */
static bool all_terms_share_denom(ixs_node *x, ixs_node *denom) {
  uint32_t i;
  for (i = 1; i < x->u.add.nterms; i++) {
    ixs_node *t = x->u.add.terms[i].term;
    uint32_t k;
    bool found = false;
    if (t->tag != IXS_MUL)
      return false;
    for (k = 0; k < t->u.mul.nfactors; k++) {
      if (t->u.mul.factors[k].base == denom && t->u.mul.factors[k].exp == -1) {
        found = true;
        break;
      }
    }
    if (!found)
      return false;
  }
  return true;
}

/* Compute the lcm of effective rational coefficient denominators.
 * Returns 0 on overflow or invalid input. */
static int64_t compute_lcm_denom(ixs_node *x) {
  int64_t lcm = 1;
  uint32_t i;
  for (i = 0; i < x->u.add.nterms; i++) {
    int64_t cp, cq, mp, mq, ep, eq, g;
    ixs_node_get_rat(x->u.add.terms[i].coeff, &cp, &cq);
    ixs_node_get_rat(x->u.add.terms[i].term->u.mul.coeff, &mp, &mq);
    if (!ixs_rat_mul(cp, cq, mp, mq, &ep, &eq))
      return 0;
    if (eq <= 0)
      return 0;
    g = ixs_gcd(lcm, eq);
    /* Cap lcm to avoid overflow. */
    if (eq / g > (1LL << 30) / lcm)
      return 0;
    lcm = lcm / g * eq;
  }
  return lcm;
}

typedef struct {
  int64_t g_bases;
  int64_t const_num;
  uint32_t n_const_terms;
  bool ok;
} sym_term_info;

/* Classify ADD terms into "base" (symbolic factors beyond denom^-1) and
 * "const" (only denom^-1).  Computes integer numerator gcd and constant
 * sum, scaled by lcm_denom. */
static sym_term_info classify_sym_terms(ixs_node *x, ixs_node *denom,
                                        int64_t lcm_denom, ixs_bounds *bnds) {
  sym_term_info info = {0, 0, 0, true};
  uint32_t i;
  for (i = 0; i < x->u.add.nterms; i++) {
    int64_t cp, cq, mp, mq, ep, eq, scale, num;
    ixs_node *t;
    bool has_other_sym, other_ok;
    uint32_t k;

    ixs_node_get_rat(x->u.add.terms[i].coeff, &cp, &cq);
    ixs_node_get_rat(x->u.add.terms[i].term->u.mul.coeff, &mp, &mq);
    if (!ixs_rat_mul(cp, cq, mp, mq, &ep, &eq)) {
      info.ok = false;
      return info;
    }
    scale = lcm_denom / eq;
    if (!ixs_safe_mul(ep, scale, &num)) {
      info.ok = false;
      return info;
    }

    t = x->u.add.terms[i].term;
    has_other_sym = false;
    other_ok = true;
    for (k = 0; k < t->u.mul.nfactors; k++) {
      bool iv;
      if (t->u.mul.factors[k].base == denom)
        continue;
      if (t->u.mul.factors[k].base->tag == IXS_INT) {
        int64_t vp, vq;
        ixs_node_get_rat(t->u.mul.factors[k].base, &vp, &vq);
        if (vp == 1 && vq == 1)
          continue;
      }
      has_other_sym = true;
      if (t->u.mul.factors[k].exp < 0) {
        other_ok = false;
        break;
      }
      iv = bnds ? is_integer_with_divinfo(bnds, t->u.mul.factors[k].base)
                : ixs_node_is_integer_valued(t->u.mul.factors[k].base);
      if (!iv) {
        other_ok = false;
        break;
      }
    }
    if (!other_ok) {
      info.ok = false;
      return info;
    }

    if (has_other_sym) {
      int64_t anum = (num > 0) ? num : ((num > -INT64_MAX) ? -num : 0);
      if (anum == 0) {
        info.ok = false;
        return info;
      }
      info.g_bases = (info.g_bases == 0) ? anum : ixs_gcd(info.g_bases, anum);
    } else {
      if (!ixs_safe_add(info.const_num, num, &info.const_num)) {
        info.ok = false;
        return info;
      }
      info.n_const_terms++;
    }
  }
  return info;
}

/* Rebuild ADD with non-constant terms preserved and constant replaced
 * by new_const/lcm_denom (or omitted if zero). Returns NULL on OOM. */
static ixs_node *rebuild_reduced_add(ixs_ctx *ctx, ixs_node *x, ixs_node *denom,
                                     int64_t new_const, int64_t lcm_denom) {
  uint32_t i;
  ixs_node *result = x->u.add.coeff;
  for (i = 0; i < x->u.add.nterms; i++) {
    ixs_node *t = x->u.add.terms[i].term;
    bool has_other_sym = false;
    uint32_t k;
    for (k = 0; k < t->u.mul.nfactors; k++) {
      if (t->u.mul.factors[k].base == denom)
        continue;
      if (t->u.mul.factors[k].base->tag == IXS_INT &&
          t->u.mul.factors[k].base->u.ival == 1)
        continue;
      has_other_sym = true;
      break;
    }
    if (!has_other_sym)
      continue;
    result = simp_add(ctx, result, simp_mul(ctx, x->u.add.terms[i].coeff, t));
    if (!result)
      return NULL;
  }

  if (new_const != 0) {
    int64_t rp, rq;
    ixs_node *cnode, *dinv, *cterm;
    ixs_mulfactor f;
    if (!ixs_rat_normalize(new_const, lcm_denom, &rp, &rq))
      return result;
    cnode = make_const(ctx, rp, rq);
    if (!cnode)
      return NULL;
    f.base = denom;
    f.exp = -1;
    dinv = ixs_node_mul(ctx, ixs_node_int(ctx, 1), 1, &f);
    if (!dinv)
      return NULL;
    cterm = simp_mul(ctx, cnode, dinv);
    if (!cterm)
      return NULL;
    result = simp_add(ctx, result, cterm);
    if (!result)
      return NULL;
  }
  return result;
}

static ixs_node *floor_drop_const_sym(ixs_ctx *ctx, ixs_node *x,
                                      ixs_bounds *bnds) {
  uint32_t j;

  if (x->tag != IXS_ADD || x->u.add.nterms < 2)
    return x;
  if (!ixs_node_is_zero(x->u.add.coeff))
    return x;

  ixs_node *first = x->u.add.terms[0].term;
  if (first->tag != IXS_MUL)
    return x;

  for (j = 0; j < first->u.mul.nfactors; j++) {
    ixs_node *denom;
    int64_t lcm, gc, k_drop, new_const;
    sym_term_info info;

    if (first->u.mul.factors[j].exp != -1)
      continue;
    if (ixs_node_is_const(first->u.mul.factors[j].base))
      continue;

    denom = first->u.mul.factors[j].base;

    if (!all_terms_share_denom(x, denom))
      continue;

    lcm = compute_lcm_denom(x);
    if (lcm == 0)
      continue;

    info = classify_sym_terms(x, denom, lcm, bnds);
    if (!info.ok || info.g_bases == 0 || info.n_const_terms == 0 ||
        info.const_num <= 0)
      continue;

    gc = ixs_gcd(info.g_bases, lcm);
    if (gc <= 0)
      continue;
    k_drop = info.const_num % gc;
    if (k_drop <= 0)
      continue;

    new_const = info.const_num - k_drop;
    return rebuild_reduced_add(ctx, x, denom, new_const, lcm);
  }

  return x;
}

/* rnd(rnd(y)/b) -> rnd(y/b) for positive integer b.
 * E.g. floor(floor(x)/3) -> floor(x/3). */
static ixs_node *round_pull_in_denom(ixs_ctx *ctx, ixs_node *x,
                                     ixs_tag self_tag, round_fn rnd) {
  if (x->tag != IXS_MUL || x->u.mul.nfactors != 1 ||
      x->u.mul.factors[0].exp != 1 || x->u.mul.factors[0].base->tag != self_tag)
    return x;

  int64_t cp, cq;
  ixs_node_get_rat(x->u.mul.coeff, &cp, &cq);
  if (cp != 1 || cq <= 1)
    return x;

  ixs_node *inner_arg = x->u.mul.factors[0].base->u.unary.arg;
  ixs_node *scaled = simp_mul(ctx, x->u.mul.coeff, inner_arg);
  if (!scaled)
    return NULL;
  return rnd(ctx, scaled);
}

/* floor(Mod(X, M) / K) -> 0 when K >= M > 0.
 * Proof: 0 <= Mod(X, M) < M <= K, so 0 <= Mod(X, M)/K < 1. */
static ixs_node *floor_mod_div_zero(ixs_ctx *ctx, ixs_node *x) {
  if (x->tag != IXS_MUL || x->u.mul.nfactors != 1 ||
      x->u.mul.factors[0].exp != 1 || x->u.mul.factors[0].base->tag != IXS_MOD)
    return x;

  int64_t cp, cq;
  ixs_node_get_rat(x->u.mul.coeff, &cp, &cq);
  if (cp != 1 || cq <= 1)
    return x;

  ixs_node *mrhs = x->u.mul.factors[0].base->u.binary.rhs;
  if (mrhs->tag == IXS_INT && mrhs->u.ival > 0 && mrhs->u.ival <= cq)
    return ixs_node_int(ctx, 0);

  return x;
}

/* ---- Floor/ceil rule wrappers ------------------------------------ */

static ixs_node *rule_floor_collapse(ixs_ctx *ctx, ixs_bounds *bnds,
                                     ixs_node *n) {
  ixs_node *r = try_floor_ceil_collapse(ctx, bnds, n->u.unary.arg, false);
  return r ? r : n;
}

static ixs_node *rule_ceil_collapse(ixs_ctx *ctx, ixs_bounds *bnds,
                                    ixs_node *n) {
  ixs_node *r = try_floor_ceil_collapse(ctx, bnds, n->u.unary.arg, true);
  return r ? r : n;
}

static ixs_node *rule_round_integer_divinfo(ixs_ctx *ctx, ixs_bounds *bnds,
                                            ixs_node *n) {
  (void)ctx;
  return is_integer_with_divinfo(bnds, n->u.unary.arg) ? n->u.unary.arg : n;
}

static ixs_node *rule_round_extract_add(ixs_ctx *ctx, ixs_bounds *bnds,
                                        ixs_node *n) {
  round_fn rnd = (n->tag == IXS_FLOOR) ? simp_floor : simp_ceil;
  ixs_node *x = n->u.unary.arg;
  ixs_node *r;
  (void)bnds;
  r = round_extract_add(ctx, x, rnd);
  if (!r)
    return NULL;
  return (r == x) ? n : r;
}

static ixs_node *rule_round_extract_mul_add(ixs_ctx *ctx, ixs_bounds *bnds,
                                            ixs_node *n) {
  round_fn rnd = (n->tag == IXS_FLOOR) ? simp_floor : simp_ceil;
  ixs_node *x = n->u.unary.arg;
  ixs_node *r;
  (void)bnds;
  r = round_extract_mul_add(ctx, x, rnd);
  if (!r)
    return NULL;
  return (r == x) ? n : r;
}

static ixs_node *rule_round_pull_in_denom(ixs_ctx *ctx, ixs_bounds *bnds,
                                          ixs_node *n) {
  round_fn rnd = (n->tag == IXS_FLOOR) ? simp_floor : simp_ceil;
  ixs_node *x = n->u.unary.arg;
  ixs_node *r;
  (void)bnds;
  r = round_pull_in_denom(ctx, x, n->tag, rnd);
  if (!r)
    return NULL;
  return (r == x) ? n : r;
}

static ixs_node *rule_floor_drop_const(ixs_ctx *ctx, ixs_bounds *bnds,
                                       ixs_node *n) {
  ixs_node *x = n->u.unary.arg;
  ixs_node *r;
  (void)bnds;
  r = floor_drop_const(ctx, x);
  if (!r)
    return NULL;
  if (r == x)
    return n;
  return simp_floor(ctx, r);
}

static ixs_node *rule_floor_drop_const_sym(ixs_ctx *ctx, ixs_bounds *bnds,
                                           ixs_node *n) {
  ixs_node *x = n->u.unary.arg;
  ixs_node *r = floor_drop_const_sym(ctx, x, bnds);
  if (!r)
    return NULL;
  if (r == x)
    return n;
  return simp_floor(ctx, r);
}

static ixs_node *rule_floor_mod_div_zero(ixs_ctx *ctx, ixs_bounds *bnds,
                                         ixs_node *n) {
  ixs_node *x = n->u.unary.arg;
  ixs_node *r;
  (void)bnds;
  r = floor_mod_div_zero(ctx, x);
  if (!r)
    return NULL;
  return (r == x) ? n : r;
}

/* ---- Floor/ceil rule tables -------------------------------------- */

static const ixs_rule floor_rules[] = {
    {rule_floor_collapse, "floor_collapse", true},
    {rule_round_integer_divinfo, "round_integer_divinfo", true},
    {rule_round_extract_add, "round_extract_add", false},
    {rule_round_extract_mul_add, "round_extract_mul_add", false},
    {rule_round_pull_in_denom, "round_pull_in_denom", false},
    {rule_floor_drop_const, "floor_drop_const", false},
    {rule_floor_drop_const_sym, "floor_drop_const_sym", false},
    {rule_floor_mod_div_zero, "floor_mod_div_zero", false},
    {NULL, NULL, false},
};

static const ixs_rule ceil_rules[] = {
    {rule_ceil_collapse, "ceil_collapse", true},
    {rule_round_integer_divinfo, "round_integer_divinfo", true},
    {rule_round_extract_add, "round_extract_add", false},
    {rule_round_extract_mul_add, "round_extract_mul_add", false},
    {rule_round_pull_in_denom, "round_pull_in_denom", false},
    {NULL, NULL, false},
};

/* ---- simp_floor / simp_ceil -------------------------------------- */

static ixs_node *simp_floor_bnds(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *x) {
  ixs_node *prop = ixs_propagate1(x);
  if (prop)
    return prop;
  if (x->tag == IXS_INT)
    return x;
  if (x->tag == IXS_RAT)
    return ixs_node_int(ctx, ixs_rat_floor(x->u.rat.p, x->u.rat.q));
  if (x->tag == IXS_FLOOR || x->tag == IXS_CEIL)
    return x;
  if (ixs_node_is_integer_valued(x))
    return x;
  {
    ixs_node *node = ixs_node_floor(ctx, x);
    if (!node)
      return NULL;
    return try_rules(ctx, bnds, node, floor_rules);
  }
}

ixs_node *simp_floor(ixs_ctx *ctx, ixs_node *x) {
  return simp_floor_bnds(ctx, NULL, x);
}

static ixs_node *simp_ceil_bnds(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *x) {
  ixs_node *prop = ixs_propagate1(x);
  if (prop)
    return prop;
  if (x->tag == IXS_INT)
    return x;
  if (x->tag == IXS_RAT)
    return ixs_node_int(ctx, ixs_rat_ceil(x->u.rat.p, x->u.rat.q));
  if (x->tag == IXS_FLOOR || x->tag == IXS_CEIL)
    return x;
  if (ixs_node_is_integer_valued(x))
    return x;
  {
    ixs_node *node = ixs_node_ceil(ctx, x);
    if (!node)
      return NULL;
    return try_rules(ctx, bnds, node, ceil_rules);
  }
}

ixs_node *simp_ceil(ixs_ctx *ctx, ixs_node *x) {
  return simp_ceil_bnds(ctx, NULL, x);
}

/* ------------------------------------------------------------------ */
/*  simp_mod                                                          */
/* ------------------------------------------------------------------ */

/* Mod(c*t, m) -> 0 when all factors are integer-valued and m | c. */
static ixs_node *mod_mul_zero(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  if (a->tag != IXS_MUL || b->tag != IXS_INT || b->u.ival <= 0)
    return NULL;

  int64_t cp, cq;
  uint32_t i;
  ixs_node_get_rat(a->u.mul.coeff, &cp, &cq);
  if (cq != 1 || cp == 0 || cp % b->u.ival != 0)
    return NULL;

  for (i = 0; i < a->u.mul.nfactors; i++) {
    if (a->u.mul.factors[i].exp < 0 ||
        !ixs_node_is_integer_valued(a->u.mul.factors[i].base))
      return NULL;
  }
  return ixs_node_int(ctx, 0);
}

/* Mod(x + k*m, m) -> Mod(x, m): strip additive multiples of m. */
static ixs_node *mod_strip_multiples(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  if (a->tag != IXS_ADD || b->tag != IXS_INT || b->u.ival <= 0)
    return NULL;

  int64_t m = b->u.ival;
  int64_t const_p, const_q;
  ixs_node_get_rat(a->u.add.coeff, &const_p, &const_q);

  int64_t new_const_p = const_p, new_const_q = const_q;
  if (const_q == 1) {
    new_const_p = const_p % m;
    if (new_const_p < 0)
      new_const_p += m;
  }

  ixs_arena_mark sm = ixs_arena_save(&ctx->scratch);
  ixs_addterm *reduced = ixs_arena_alloc(
      &ctx->scratch, a->u.add.nterms * sizeof(*reduced), sizeof(void *));
  if (!reduced) {
    ixs_arena_restore(&ctx->scratch, sm);
    return NULL;
  }
  uint32_t nr = 0;
  uint32_t i;
  bool changed = (new_const_p != const_p || new_const_q != const_q);

  for (i = 0; i < a->u.add.nterms; i++) {
    int64_t cp, cq;
    ixs_node_get_rat(a->u.add.terms[i].coeff, &cp, &cq);
    if (cq == 1 && cp % m == 0 &&
        ixs_node_is_integer_valued(a->u.add.terms[i].term)) {
      changed = true;
      continue;
    }
    reduced[nr++] = a->u.add.terms[i];
  }

  if (!changed) {
    ixs_arena_restore(&ctx->scratch, sm);
    return NULL;
  }

  ixs_node *new_a;
  if (nr == 0) {
    new_a = make_const(ctx, new_const_p, new_const_q);
  } else {
    ixs_node *c = make_const(ctx, new_const_p, new_const_q);
    if (!c) {
      ixs_arena_restore(&ctx->scratch, sm);
      return NULL;
    }
    if (nr == 1 && ixs_rat_is_zero(new_const_p)) {
      int64_t rcp, rcq;
      ixs_node_get_rat(reduced[0].coeff, &rcp, &rcq);
      if (ixs_rat_is_one(rcp, rcq))
        new_a = reduced[0].term;
      else
        new_a = simp_mul(ctx, make_const(ctx, rcp, rcq), reduced[0].term);
    } else {
      new_a = ixs_node_add(ctx, c, nr, reduced);
    }
  }
  ixs_arena_restore(&ctx->scratch, sm);
  if (!new_a)
    return NULL;
  return simp_mod(ctx, new_a, b);
}

/* Extract a small constant addend from Mod when every other term's
 * coefficient divides the modulus.  Uses gcd(|ci|) for the bound.
 *
 *   Mod(4*floor(a) + 3, 16)  ->  Mod(4*floor(a), 16) + 3
 *
 * Proof: each |ci| | q, so sum = Sigma ci*ti is a multiple of g = gcd(|ci|).
 * Then (sum mod q) in {0, g, 2g, ..., q-g}.  If 0 < c < g, then
 * (sum mod q) + c < q, so Mod(sum + c, q) = (sum mod q) + c. */
static ixs_node *mod_extract_small_const(ixs_ctx *ctx, ixs_node *a,
                                         ixs_node *b) {
  if (a->tag != IXS_ADD || b->tag != IXS_INT || b->u.ival <= 0)
    return NULL;

  int64_t m = b->u.ival;
  int64_t const_p, const_q;
  ixs_node_get_rat(a->u.add.coeff, &const_p, &const_q);

  if (const_q != 1 || const_p <= 0 || a->u.add.nterms == 0)
    return NULL;

  int64_t g = 0;
  bool ok = true;
  uint32_t i;

  for (i = 0; i < a->u.add.nterms; i++) {
    int64_t cp, cq;
    ixs_node_get_rat(a->u.add.terms[i].coeff, &cp, &cq);
    int64_t acp = (cp > 0) ? cp : (cp >= -INT64_MAX) ? -cp : 0;
    if (cq != 1 || acp == 0 || m % acp != 0 ||
        !ixs_node_is_integer_valued(a->u.add.terms[i].term)) {
      ok = false;
      break;
    }
    g = (g == 0) ? acp : ixs_gcd(g, acp);
  }

  if (!ok || g <= 1 || const_p >= g)
    return NULL;

  ixs_node *zero = ixs_node_int(ctx, 0);
  if (!zero)
    return NULL;
  ixs_node *inner = ixs_node_add(ctx, zero, a->u.add.nterms, a->u.add.terms);
  if (!inner)
    return NULL;
  ixs_node *moded = simp_mod(ctx, inner, b);
  if (!moded)
    return NULL;
  return simp_add(ctx, moded, ixs_node_int(ctx, const_p));
}

/* ---- Mod rule wrappers ------------------------------------------- */

static ixs_node *rule_mod_const_fold(ixs_ctx *ctx, ixs_bounds *bnds,
                                     ixs_node *n) {
  int64_t ap, aq, bp, bq, rp, rq;
  (void)bnds;
  if (!ixs_node_is_const(n->u.binary.lhs) ||
      !ixs_node_is_const(n->u.binary.rhs))
    return n;
  ixs_node_get_rat(n->u.binary.lhs, &ap, &aq);
  ixs_node_get_rat(n->u.binary.rhs, &bp, &bq);
  if (ixs_rat_is_neg(bp))
    return simp_err(ctx, "Mod: divisor is negative");
  if (!ixs_rat_mod(ap, aq, bp, bq, &rp, &rq))
    return simp_err(ctx, "rational overflow in Mod");
  return make_const(ctx, rp, rq);
}

static ixs_node *rule_mod_one(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *n) {
  (void)bnds;
  if (ixs_node_is_one(n->u.binary.rhs) &&
      ixs_node_is_integer_valued(n->u.binary.lhs))
    return ixs_node_int(ctx, 0);
  return n;
}

static ixs_node *rule_mod_mul_zero(ixs_ctx *ctx, ixs_bounds *bnds,
                                   ixs_node *n) {
  ixs_node *r;
  (void)bnds;
  r = mod_mul_zero(ctx, n->u.binary.lhs, n->u.binary.rhs);
  return r ? r : n;
}

static ixs_node *rule_mod_idempotent(ixs_ctx *ctx, ixs_bounds *bnds,
                                     ixs_node *n) {
  (void)ctx;
  (void)bnds;
  if (n->u.binary.lhs->tag == IXS_MOD &&
      n->u.binary.lhs->u.binary.rhs == n->u.binary.rhs)
    return n->u.binary.lhs;
  return n;
}

static ixs_node *rule_mod_strip_multiples(ixs_ctx *ctx, ixs_bounds *bnds,
                                          ixs_node *n) {
  ixs_node *r;
  (void)bnds;
  r = mod_strip_multiples(ctx, n->u.binary.lhs, n->u.binary.rhs);
  return r ? r : n;
}

static ixs_node *rule_mod_extract_small_const(ixs_ctx *ctx, ixs_bounds *bnds,
                                              ixs_node *n) {
  ixs_node *r;
  (void)bnds;
  r = mod_extract_small_const(ctx, n->u.binary.lhs, n->u.binary.rhs);
  return r ? r : n;
}

static ixs_node *rule_mod_bounds_elim(ixs_ctx *ctx, ixs_bounds *bnds,
                                      ixs_node *n) {
  ixs_node *r = mod_bounds_elim(ctx, bnds, n->u.binary.lhs, n->u.binary.rhs);
  return r ? r : n;
}

static const ixs_rule mod_rules[] = {
    {rule_mod_const_fold, "mod_const_fold", false},
    {rule_mod_one, "mod_one", false},
    {rule_mod_mul_zero, "mod_mul_zero", false},
    {rule_mod_idempotent, "mod_idempotent", false},
    {rule_mod_strip_multiples, "mod_strip_multiples", false},
    {rule_mod_extract_small_const, "mod_extract_small_const", false},
    {rule_mod_bounds_elim, "mod_bounds_elim", true},
    {NULL, NULL, false},
};

static ixs_node *simp_mod_bnds(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *a,
                               ixs_node *b) {
  ixs_node *node;
  if (!a || !b)
    return NULL;
  {
    ixs_node *prop = ixs_propagate2(a, b);
    if (prop)
      return prop;
  }
  if (ixs_node_is_zero(b))
    return simp_err(ctx, "Mod: divisor is zero");
  node = ixs_node_binary(ctx, IXS_MOD, a, b, (ixs_cmp_op)0);
  if (!node)
    return NULL;
  return try_rules(ctx, bnds, node, mod_rules);
}

ixs_node *simp_mod(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  return simp_mod_bnds(ctx, NULL, a, b);
}

/* ------------------------------------------------------------------ */
/*  simp_max / simp_min                                               */
/* ------------------------------------------------------------------ */

/* ---- Max/min rule wrappers --------------------------------------- */

static ixs_node *rule_max_const_fold(ixs_ctx *ctx, ixs_bounds *bnds,
                                     ixs_node *n) {
  int64_t ap, aq, bp, bq;
  (void)ctx;
  (void)bnds;
  if (!ixs_node_is_const(n->u.binary.lhs) ||
      !ixs_node_is_const(n->u.binary.rhs))
    return n;
  ixs_node_get_rat(n->u.binary.lhs, &ap, &aq);
  ixs_node_get_rat(n->u.binary.rhs, &bp, &bq);
  return ixs_rat_cmp(ap, aq, bp, bq) >= 0 ? n->u.binary.lhs : n->u.binary.rhs;
}

static ixs_node *rule_min_const_fold(ixs_ctx *ctx, ixs_bounds *bnds,
                                     ixs_node *n) {
  int64_t ap, aq, bp, bq;
  (void)ctx;
  (void)bnds;
  if (!ixs_node_is_const(n->u.binary.lhs) ||
      !ixs_node_is_const(n->u.binary.rhs))
    return n;
  ixs_node_get_rat(n->u.binary.lhs, &ap, &aq);
  ixs_node_get_rat(n->u.binary.rhs, &bp, &bq);
  return ixs_rat_cmp(ap, aq, bp, bq) <= 0 ? n->u.binary.lhs : n->u.binary.rhs;
}

static ixs_node *rule_max_bounds_collapse(ixs_ctx *ctx, ixs_bounds *bnds,
                                          ixs_node *n) {
  ixs_node *r =
      max_bounds_collapse(ctx, bnds, n->u.binary.lhs, n->u.binary.rhs);
  return r ? r : n;
}

static ixs_node *rule_min_bounds_collapse(ixs_ctx *ctx, ixs_bounds *bnds,
                                          ixs_node *n) {
  ixs_node *r =
      min_bounds_collapse(ctx, bnds, n->u.binary.lhs, n->u.binary.rhs);
  return r ? r : n;
}

static const ixs_rule max_rules[] = {
    {rule_max_const_fold, "max_const_fold", false},
    {rule_max_bounds_collapse, "max_bounds_collapse", true},
    {NULL, NULL, false},
};

static const ixs_rule min_rules[] = {
    {rule_min_const_fold, "min_const_fold", false},
    {rule_min_bounds_collapse, "min_bounds_collapse", true},
    {NULL, NULL, false},
};

static ixs_node *simp_max_bnds(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *a,
                               ixs_node *b) {
  ixs_node *node;
  if (!a || !b)
    return NULL;
  {
    ixs_node *prop = ixs_propagate2(a, b);
    if (prop)
      return prop;
  }
  if (a == b)
    return a;
  if (ixs_node_cmp(a, b) > 0) {
    ixs_node *t = a;
    a = b;
    b = t;
  }
  node = ixs_node_binary(ctx, IXS_MAX, a, b, (ixs_cmp_op)0);
  if (!node)
    return NULL;
  return try_rules(ctx, bnds, node, max_rules);
}

ixs_node *simp_max(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  return simp_max_bnds(ctx, NULL, a, b);
}

static ixs_node *simp_min_bnds(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *a,
                               ixs_node *b) {
  ixs_node *node;
  if (!a || !b)
    return NULL;
  {
    ixs_node *prop = ixs_propagate2(a, b);
    if (prop)
      return prop;
  }
  if (a == b)
    return a;
  if (ixs_node_cmp(a, b) > 0) {
    ixs_node *t = a;
    a = b;
    b = t;
  }
  node = ixs_node_binary(ctx, IXS_MIN, a, b, (ixs_cmp_op)0);
  if (!node)
    return NULL;
  return try_rules(ctx, bnds, node, min_rules);
}

ixs_node *simp_min(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  return simp_min_bnds(ctx, NULL, a, b);
}

/* ------------------------------------------------------------------ */
/*  simp_xor                                                          */
/* ------------------------------------------------------------------ */

ixs_node *simp_xor(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  if (!a || !b)
    return NULL;
  ixs_node *prop = ixs_propagate2(a, b);
  if (prop)
    return prop;

  if (a == b)
    return ixs_node_int(ctx, 0);
  if (ixs_node_is_zero(a))
    return b;
  if (ixs_node_is_zero(b))
    return a;

  if (a->tag == IXS_INT && b->tag == IXS_INT)
    return ixs_node_int(ctx, a->u.ival ^ b->u.ival);

  if (ixs_node_cmp(a, b) > 0)
    return ixs_node_binary(ctx, IXS_XOR, b, a, (ixs_cmp_op)0);

  return ixs_node_binary(ctx, IXS_XOR, a, b, (ixs_cmp_op)0);
}

/* ------------------------------------------------------------------ */
/*  simp_cmp                                                          */
/* ------------------------------------------------------------------ */

/* Normalize: (a op b) -> ((a - b) op 0) so all comparisons have zero RHS. */
static ixs_node *cmp_normalize_to_zero(ixs_ctx *ctx, ixs_node *a, ixs_cmp_op op,
                                       ixs_node *b) {
  ixs_node *diff;
  if (ixs_node_is_zero(b))
    return NULL;
  diff = simp_sub(ctx, a, b);
  if (!diff)
    return diff; /* propagate NULL */
  if (ixs_node_is_sentinel(diff))
    return diff;
  return simp_cmp(ctx, diff, op, ixs_node_int(ctx, 0));
}

/* ---- CMP rule wrappers ------------------------------------------- */

static ixs_node *rule_cmp_const_fold(ixs_ctx *ctx, ixs_bounds *bnds,
                                     ixs_node *n) {
  int64_t ap, aq, bp, bq;
  int c;
  bool result = false;
  (void)bnds;
  if (!ixs_node_is_const(n->u.binary.lhs) ||
      !ixs_node_is_const(n->u.binary.rhs))
    return n;
  ixs_node_get_rat(n->u.binary.lhs, &ap, &aq);
  ixs_node_get_rat(n->u.binary.rhs, &bp, &bq);
  c = ixs_rat_cmp(ap, aq, bp, bq);
  switch (n->u.binary.cmp_op) {
  case IXS_CMP_GT:
    result = c > 0;
    break;
  case IXS_CMP_GE:
    result = c >= 0;
    break;
  case IXS_CMP_LT:
    result = c < 0;
    break;
  case IXS_CMP_LE:
    result = c <= 0;
    break;
  case IXS_CMP_EQ:
    result = c == 0;
    break;
  case IXS_CMP_NE:
    result = c != 0;
    break;
  }
  return result ? ctx->node_true : ctx->node_false;
}

static ixs_node *rule_cmp_identity(ixs_ctx *ctx, ixs_bounds *bnds,
                                   ixs_node *n) {
  (void)bnds;
  if (n->u.binary.lhs != n->u.binary.rhs)
    return n;
  switch (n->u.binary.cmp_op) {
  case IXS_CMP_GE:
  case IXS_CMP_LE:
  case IXS_CMP_EQ:
    return ctx->node_true;
  case IXS_CMP_GT:
  case IXS_CMP_LT:
  case IXS_CMP_NE:
    return ctx->node_false;
  }
  return n;
}

static ixs_node *rule_cmp_normalize(ixs_ctx *ctx, ixs_bounds *bnds,
                                    ixs_node *n) {
  ixs_node *r;
  (void)bnds;
  r = cmp_normalize_to_zero(ctx, n->u.binary.lhs, n->u.binary.cmp_op,
                            n->u.binary.rhs);
  return r ? r : n;
}

static ixs_node *rule_cmp_bounds_resolve(ixs_ctx *ctx, ixs_bounds *bnds,
                                         ixs_node *n) {
  ixs_node *r = cmp_bounds_resolve(ctx, bnds, n);
  return r ? r : n;
}

static const ixs_rule cmp_rules[] = {
    {rule_cmp_const_fold, "cmp_const_fold", false},
    {rule_cmp_identity, "cmp_identity", false},
    {rule_cmp_normalize, "cmp_normalize", false},
    {rule_cmp_bounds_resolve, "cmp_bounds_resolve", true},
    {NULL, NULL, false},
};

static ixs_node *simp_cmp_bnds(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *a,
                               ixs_cmp_op op, ixs_node *b) {
  ixs_node *node;
  if (!a || !b)
    return NULL;
  {
    ixs_node *prop = ixs_propagate2(a, b);
    if (prop)
      return prop;
  }
  node = ixs_node_binary(ctx, IXS_CMP, a, b, op);
  if (!node)
    return NULL;
  return try_rules(ctx, bnds, node, cmp_rules);
}

ixs_node *simp_cmp(ixs_ctx *ctx, ixs_node *a, ixs_cmp_op op, ixs_node *b) {
  return simp_cmp_bnds(ctx, NULL, a, op, b);
}

/* ------------------------------------------------------------------ */
/*  simp_and / simp_or / simp_not                                     */
/* ------------------------------------------------------------------ */

/* ~(a > b) -> a <= b, etc.  Returns NULL if a is not a CMP node. */
static ixs_node *not_cmp_flip(ixs_ctx *ctx, ixs_node *a) {
  ixs_cmp_op flipped;
  if (a->tag != IXS_CMP)
    return NULL;
  switch (a->u.binary.cmp_op) {
  case IXS_CMP_GT:
    flipped = IXS_CMP_LE;
    break;
  case IXS_CMP_GE:
    flipped = IXS_CMP_LT;
    break;
  case IXS_CMP_LT:
    flipped = IXS_CMP_GE;
    break;
  case IXS_CMP_LE:
    flipped = IXS_CMP_GT;
    break;
  case IXS_CMP_EQ:
    flipped = IXS_CMP_NE;
    break;
  case IXS_CMP_NE:
    flipped = IXS_CMP_EQ;
    break;
  default:
    flipped = a->u.binary.cmp_op;
    break;
  }
  IXS_STAT_HIT(ctx);
  return ixs_node_binary(ctx, IXS_CMP, a->u.binary.lhs, a->u.binary.rhs,
                         flipped);
}

ixs_node *simp_not(ixs_ctx *ctx, ixs_node *a) {
  ixs_node *r;
  ixs_node *prop = ixs_propagate1(a);
  if (prop)
    return prop;

  if (a->tag == IXS_TRUE)
    return ctx->node_false;
  if (a->tag == IXS_FALSE)
    return ctx->node_true;

  if (a->tag == IXS_NOT)
    return a->u.unary_bool.arg;

  r = not_cmp_flip(ctx, a);
  if (r)
    return r;

  return ixs_node_not(ctx, a);
}

static ixs_node *simp_logic_impl(ixs_ctx *ctx, ixs_tag tag, ixs_node *a,
                                 ixs_node *b) {
  size_t cap = 16;
  ixs_node **args =
      ixs_arena_alloc(&ctx->scratch, cap * sizeof(*args), sizeof(void *));
  if (!args)
    return NULL;
  uint32_t nargs = 0;
  uint32_t i;

  ixs_node *inputs[2];
  inputs[0] = a;
  inputs[1] = b;

  for (i = 0; i < 2; i++) {
    ixs_node *x = inputs[i];
    if (x->tag == tag) {
      uint32_t j;
      for (j = 0; j < x->u.logic.nargs; j++) {
        if (nargs >= cap) {
          args = scratch_grow(&ctx->scratch, args, &cap, sizeof(*args));
          if (!args)
            return NULL;
        }
        args[nargs++] = x->u.logic.args[j];
      }
    } else {
      if (nargs >= cap) {
        args = scratch_grow(&ctx->scratch, args, &cap, sizeof(*args));
        if (!args)
          return NULL;
      }
      args[nargs++] = x;
    }
  }

  qsort(args, nargs, sizeof(ixs_node *), nodeptr_cmp);
  {
    uint32_t j2 = 0;
    for (i = 0; i < nargs; i++) {
      if (j2 > 0 && args[j2 - 1] == args[i])
        continue;
      args[j2++] = args[i];
    }
    nargs = j2;
  }

  if (nargs == 1)
    return args[0];

  return ixs_node_logic(ctx, tag, nargs, args);
}

ixs_node *simp_and(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  if (!a || !b)
    return NULL;
  ixs_node *prop = ixs_propagate2(a, b);
  if (prop)
    return prop;

  if (a->tag == IXS_FALSE || b->tag == IXS_FALSE)
    return ctx->node_false;
  if (a->tag == IXS_TRUE)
    return b;
  if (b->tag == IXS_TRUE)
    return a;
  if (a == b)
    return a;

  ixs_arena_mark m = ixs_arena_save(&ctx->scratch);
  ixs_node *result = simp_logic_impl(ctx, IXS_AND, a, b);
  ixs_arena_restore(&ctx->scratch, m);
  return result;
}

ixs_node *simp_or(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  if (!a || !b)
    return NULL;
  ixs_node *prop = ixs_propagate2(a, b);
  if (prop)
    return prop;

  if (a->tag == IXS_TRUE || b->tag == IXS_TRUE)
    return ctx->node_true;
  if (a->tag == IXS_FALSE)
    return b;
  if (b->tag == IXS_FALSE)
    return a;
  if (a == b)
    return a;

  ixs_arena_mark m = ixs_arena_save(&ctx->scratch);
  ixs_node *result = simp_logic_impl(ctx, IXS_OR, a, b);
  ixs_arena_restore(&ctx->scratch, m);
  return result;
}

/* ------------------------------------------------------------------ */
/*  simp_pw (Piecewise)                                               */
/* ------------------------------------------------------------------ */

static ixs_node *simp_pw_impl(ixs_ctx *ctx, uint32_t n, ixs_node **values,
                              ixs_node **conds) {
  size_t cap = n > 16 ? n : 16;
  ixs_pwcase *cases =
      ixs_arena_alloc(&ctx->scratch, cap * sizeof(*cases), sizeof(void *));
  if (!cases)
    return NULL;
  uint32_t ncases = 0;
  uint32_t i;

  if (n == 0)
    return simp_err(ctx, "Piecewise: zero cases");

  for (i = 0; i < n; i++) {
    ixs_node *v = values[i];
    ixs_node *c = conds[i];

    if (!v || !c)
      return NULL;

    if (c->tag == IXS_FALSE)
      continue;

    if (ixs_node_is_sentinel(c)) {
      if (ncases > 0 && cases[ncases - 1].cond->tag == IXS_TRUE)
        continue;
      return c;
    }

    if (c->tag == IXS_TRUE) {
      if (ixs_node_is_sentinel(v)) {
        if (ncases > 0 && cases[ncases - 1].cond->tag == IXS_TRUE)
          break;
        return v;
      }
      cases[ncases].value = v;
      cases[ncases].cond = c;
      ncases++;
      break;
    }

    if (ncases > 0 && cases[ncases - 1].value == v) {
      cases[ncases - 1].cond = simp_or(ctx, cases[ncases - 1].cond, c);
      if (!cases[ncases - 1].cond)
        return NULL;
      continue;
    }

    if (ncases >= cap) {
      cases = scratch_grow(&ctx->scratch, cases, &cap, sizeof(*cases));
      if (!cases)
        return NULL;
    }
    cases[ncases].value = v;
    cases[ncases].cond = c;
    ncases++;
  }

  if (ncases == 0)
    return simp_err(ctx, "Piecewise: all conditions are False");

  if (ncases == 1 && cases[0].cond->tag == IXS_TRUE)
    return cases[0].value;

  return ixs_node_pw(ctx, ncases, cases);
}

ixs_node *simp_pw(ixs_ctx *ctx, uint32_t n, ixs_node **values,
                  ixs_node **conds) {
  ixs_arena_mark m = ixs_arena_save(&ctx->scratch);
  ixs_node *result = simp_pw_impl(ctx, n, values, conds);
  ixs_arena_restore(&ctx->scratch, m);
  return result;
}

/* ------------------------------------------------------------------ */
/*  simp_subs (substitution with memoization)                         */
/* ------------------------------------------------------------------ */

#define SUBS_MEMO_SIZE 256u
#define SUBS_MEMO_MASK (SUBS_MEMO_SIZE - 1u)

typedef struct {
  ixs_node *key;
  ixs_node *val;
} subs_memo_slot;

static size_t subs_memo_idx(ixs_node *n) {
  uint32_t h = n->hash;
  return (size_t)((h ^ (h >> 8)) & SUBS_MEMO_MASK);
}

static ixs_node *subs_rec(ixs_ctx *ctx, ixs_node *expr, ixs_node *target,
                          ixs_node *replacement, subs_memo_slot *memo) {
  uint32_t i;
  size_t slot;
  ixs_node *result;

  if (!expr)
    return NULL;
  if (ixs_node_is_sentinel(expr))
    return expr;

  if (expr == target)
    return replacement;

  switch (expr->tag) {
  case IXS_INT:
  case IXS_RAT:
  case IXS_SYM:
  case IXS_TRUE:
  case IXS_FALSE:
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    return expr;
  default:
    break;
  }

  slot = subs_memo_idx(expr);
  if (memo[slot].key == expr)
    return memo[slot].val;

  result = NULL;

  switch (expr->tag) {
  case IXS_ADD: {
    ixs_node *nc = subs_rec(ctx, expr->u.add.coeff, target, replacement, memo);
    if (!nc)
      return NULL;
    result = nc;
    for (i = 0; i < expr->u.add.nterms; i++) {
      ixs_node *nt =
          subs_rec(ctx, expr->u.add.terms[i].term, target, replacement, memo);
      if (!nt)
        return NULL;
      ixs_node *ncoeff =
          subs_rec(ctx, expr->u.add.terms[i].coeff, target, replacement, memo);
      if (!ncoeff)
        return NULL;
      ixs_node *term = simp_mul(ctx, ncoeff, nt);
      if (!term)
        return NULL;
      result = simp_add(ctx, result, term);
      if (!result)
        return NULL;
    }
    break;
  }
  case IXS_MUL: {
    ixs_node *nc = subs_rec(ctx, expr->u.mul.coeff, target, replacement, memo);
    if (!nc)
      return NULL;
    result = nc;
    for (i = 0; i < expr->u.mul.nfactors; i++) {
      ixs_node *nb =
          subs_rec(ctx, expr->u.mul.factors[i].base, target, replacement, memo);
      if (!nb)
        return NULL;
      int32_t e = expr->u.mul.factors[i].exp;
      ixs_node *power;
      if (e == 1) {
        power = nb;
      } else if ((nb->tag == IXS_INT || nb->tag == IXS_RAT) && e > 0 &&
                 e <= 64) {
        int32_t j;
        power = ixs_node_int(ctx, 1);
        for (j = 0; j < e && power; j++)
          power = simp_mul(ctx, power, nb);
      } else {
        ixs_mulfactor f;
        f.base = nb;
        f.exp = e;
        power = ixs_node_mul(ctx, ixs_node_int(ctx, 1), 1, &f);
      }
      if (!power)
        return NULL;
      result = simp_mul(ctx, result, power);
      if (!result)
        return NULL;
    }
    break;
  }
  case IXS_FLOOR: {
    ixs_node *na = subs_rec(ctx, expr->u.unary.arg, target, replacement, memo);
    result = na ? simp_floor(ctx, na) : NULL;
    break;
  }
  case IXS_CEIL: {
    ixs_node *na = subs_rec(ctx, expr->u.unary.arg, target, replacement, memo);
    result = na ? simp_ceil(ctx, na) : NULL;
    break;
  }
  case IXS_MOD:
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR: {
    ixs_node *nl = subs_rec(ctx, expr->u.binary.lhs, target, replacement, memo);
    ixs_node *nr = subs_rec(ctx, expr->u.binary.rhs, target, replacement, memo);
    if (!nl || !nr)
      return NULL;
    switch (expr->tag) {
    case IXS_MOD:
      result = simp_mod(ctx, nl, nr);
      break;
    case IXS_MAX:
      result = simp_max(ctx, nl, nr);
      break;
    case IXS_MIN:
      result = simp_min(ctx, nl, nr);
      break;
    case IXS_XOR:
      result = simp_xor(ctx, nl, nr);
      break;
    default:
      break;
    }
    break;
  }
  case IXS_CMP: {
    ixs_node *nl = subs_rec(ctx, expr->u.binary.lhs, target, replacement, memo);
    ixs_node *nr = subs_rec(ctx, expr->u.binary.rhs, target, replacement, memo);
    if (!nl || !nr)
      return NULL;
    result = simp_cmp(ctx, nl, expr->u.binary.cmp_op, nr);
    break;
  }
  case IXS_PIECEWISE: {
    uint32_t nc = expr->u.pw.ncases;
    ixs_arena_mark sm = ixs_arena_save(&ctx->scratch);
    ixs_node **vals =
        ixs_arena_alloc(&ctx->scratch, nc * sizeof(*vals), sizeof(void *));
    ixs_node **cds =
        ixs_arena_alloc(&ctx->scratch, nc * sizeof(*cds), sizeof(void *));
    if (!vals || !cds) {
      ixs_arena_restore(&ctx->scratch, sm);
      return NULL;
    }
    for (i = 0; i < nc; i++) {
      vals[i] =
          subs_rec(ctx, expr->u.pw.cases[i].value, target, replacement, memo);
      cds[i] =
          subs_rec(ctx, expr->u.pw.cases[i].cond, target, replacement, memo);
      if (!vals[i] || !cds[i]) {
        ixs_arena_restore(&ctx->scratch, sm);
        return NULL;
      }
    }
    result = simp_pw(ctx, nc, vals, cds);
    ixs_arena_restore(&ctx->scratch, sm);
    break;
  }
  case IXS_AND: {
    result = ctx->node_true;
    for (i = 0; i < expr->u.logic.nargs; i++) {
      ixs_node *na =
          subs_rec(ctx, expr->u.logic.args[i], target, replacement, memo);
      if (!na)
        return NULL;
      result = simp_and(ctx, result, na);
      if (!result)
        return NULL;
    }
    break;
  }
  case IXS_OR: {
    result = ctx->node_false;
    for (i = 0; i < expr->u.logic.nargs; i++) {
      ixs_node *na =
          subs_rec(ctx, expr->u.logic.args[i], target, replacement, memo);
      if (!na)
        return NULL;
      result = simp_or(ctx, result, na);
      if (!result)
        return NULL;
    }
    break;
  }
  case IXS_NOT: {
    ixs_node *na =
        subs_rec(ctx, expr->u.unary_bool.arg, target, replacement, memo);
    result = na ? simp_not(ctx, na) : NULL;
    break;
  }
  default:
    result = expr;
    break;
  }

  if (result) {
    memo[slot].key = expr;
    memo[slot].val = result;
  }
  return result;
}

ixs_node *simp_subs(ixs_ctx *ctx, ixs_node *expr, ixs_node *target,
                    ixs_node *replacement) {
  subs_memo_slot memo[SUBS_MEMO_SIZE];

  if (!expr)
    return NULL;
  if (ixs_node_is_sentinel(expr))
    return expr;
  if (!target || !replacement)
    return NULL;
  if (expr == target)
    return replacement;

  memset(memo, 0, sizeof(memo));
  return subs_rec(ctx, expr, target, replacement, memo);
}

/* ------------------------------------------------------------------ */
/*  simp_simplify (top-down with assumptions)                         */
/* ------------------------------------------------------------------ */

/* Memo cache for rewrite (same direct-mapped scheme as subs). */
#define REWRITE_MEMO_SIZE 256u
#define REWRITE_MEMO_MASK (REWRITE_MEMO_SIZE - 1u)

typedef struct {
  ixs_node *key;
  ixs_node *val;
} rewrite_memo_slot;

static void add_cond_to_bounds(ixs_bounds *bnds, ixs_node *cond) {
  if (cond->tag == IXS_CMP) {
    ixs_bounds_add_assumption(bnds, cond);
  } else if (cond->tag == IXS_AND) {
    uint32_t j;
    for (j = 0; j < cond->u.logic.nargs; j++) {
      if (cond->u.logic.args[j]->tag == IXS_CMP)
        ixs_bounds_add_assumption(bnds, cond->u.logic.args[j]);
    }
  }
}

static ixs_node *rewrite_impl(ixs_ctx *ctx, ixs_node *n, ixs_bounds *bnds,
                              rewrite_memo_slot *memo);

static ixs_node *rewrite(ixs_ctx *ctx, ixs_node *n, ixs_bounds *bnds,
                         rewrite_memo_slot *memo) {
  if (!n || ixs_node_is_sentinel(n))
    return n;
  uint32_t slot = n->hash & REWRITE_MEMO_MASK;
  if (memo[slot].key == n)
    return memo[slot].val;
  ixs_node *result = rewrite_impl(ctx, n, bnds, memo);
  memo[slot].key = n;
  memo[slot].val = result;
  return result;
}

/* Collapse floor or ceil to a constant when bounds pin it to one value.
 * Returns the constant node, or NULL if bounds don't collapse. */
static ixs_node *try_floor_ceil_collapse(ixs_ctx *ctx, ixs_bounds *bnds,
                                         ixs_node *arg, bool is_ceil) {
  ixs_interval iv;
  int64_t lo_val, hi_val;
  if (!bnds)
    return NULL;
  iv = ixs_bounds_get(bnds, arg);
  if (!iv.valid)
    return NULL;
  lo_val = is_ceil ? ixs_rat_ceil(iv.lo_p, iv.lo_q)
                   : ixs_rat_floor(iv.lo_p, iv.lo_q);
  hi_val = is_ceil ? ixs_rat_ceil(iv.hi_p, iv.hi_q)
                   : ixs_rat_floor(iv.hi_p, iv.hi_q);
  if (lo_val == hi_val)
    return ixs_node_int(ctx, lo_val);
  return NULL;
}

/* True when expr is provably divisible by m (m > 0) given bounds.
 * Handles: sym with known congruence, c*sym, sums of divisible terms. */
static bool is_known_divisible(ixs_bounds *bnds, ixs_node *expr, int64_t m) {
  if (!bnds || m <= 0)
    return false;

  /* Integer constant: m | val */
  if (expr->tag == IXS_INT)
    return expr->u.ival % m == 0;

  /* Symbol with known congruence: x ≡ r (mod M), divisible by m iff
   * M % m == 0 && r % m == 0. */
  if (expr->tag == IXS_SYM) {
    int64_t sym_mod, sym_rem;
    if (!ixs_bounds_get_modrem(bnds, expr->u.name, &sym_mod, &sym_rem))
      return false;
    return sym_mod % m == 0 && sym_rem % m == 0;
  }

  /* c * base^1: m | (c * divisor(base)) when c is integer */
  if (expr->tag == IXS_MUL && expr->u.mul.nfactors == 1 &&
      expr->u.mul.factors[0].exp == 1 && expr->u.mul.coeff->tag == IXS_INT) {
    int64_t c = expr->u.mul.coeff->u.ival;
    if (c == 0)
      return true;
    int64_t g = ixs_gcd(c, m);
    int64_t remain = m / g;
    return is_known_divisible(bnds, expr->u.mul.factors[0].base, remain);
  }

  /* ADD: every term c_i * t_i must be divisible by m, and the constant
   * term must also be divisible by m. */
  if (expr->tag == IXS_ADD) {
    int64_t cp, cq;
    uint32_t i;
    ixs_node_get_rat(expr->u.add.coeff, &cp, &cq);
    if (cq != 1 || cp % m != 0)
      return false;
    for (i = 0; i < expr->u.add.nterms; i++) {
      int64_t tp, tq;
      ixs_node_get_rat(expr->u.add.terms[i].coeff, &tp, &tq);
      if (tq != 1)
        return false;
      int64_t g = ixs_gcd(tp, m);
      int64_t remain = m / g;
      if (!is_known_divisible(bnds, expr->u.add.terms[i].term, remain))
        return false;
    }
    return true;
  }

  return false;
}

/* True when expr is provably integer-valued given congruence info.
 * Extends ixs_node_is_integer_valued with modular reasoning:
 * p/q * sym is integer when the symbol's known congruence absorbs q. */
static bool is_integer_with_divinfo(ixs_bounds *bnds, ixs_node *expr) {
  if (ixs_node_is_integer_valued(expr))
    return true;
  if (!bnds)
    return false;

  /* MUL: p/q * base^1 is integer if base's congruence absorbs q */
  if (expr->tag == IXS_MUL && expr->u.mul.nfactors == 1 &&
      expr->u.mul.factors[0].exp == 1) {
    int64_t cp, cq;
    ixs_node_get_rat(expr->u.mul.coeff, &cp, &cq);
    if (cq <= 1)
      return is_integer_with_divinfo(bnds, expr->u.mul.factors[0].base);
    int64_t g = ixs_gcd(cp, cq);
    int64_t denom = cq / g;
    return is_known_divisible(bnds, expr->u.mul.factors[0].base, denom);
  }

  /* ADD: integer coeff + all integer-valued terms */
  if (expr->tag == IXS_ADD) {
    uint32_t i;
    if (!is_integer_with_divinfo(bnds, expr->u.add.coeff))
      return false;
    for (i = 0; i < expr->u.add.nterms; i++) {
      int64_t cp, cq;
      ixs_node_get_rat(expr->u.add.terms[i].coeff, &cp, &cq);
      if (cq == 1) {
        if (!is_integer_with_divinfo(bnds, expr->u.add.terms[i].term))
          return false;
      } else {
        /* c_i/q_i * t_i: integer if t_i divisible by q_i/gcd(|c_i|,q_i) */
        int64_t g = ixs_gcd(cp, cq);
        int64_t denom = cq / g;
        if (!is_known_divisible(bnds, expr->u.add.terms[i].term, denom))
          return false;
      }
    }
    return true;
  }

  return false;
}

/* Mod(x, M) -> x when 0 <= x < M; -> r when x ≡ r (mod m) and m % M == 0;
 * -> 0 when M | x.  Returns NULL if bounds don't resolve. */
static ixs_node *mod_bounds_elim(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *l,
                                 ixs_node *r) {
  if (!bnds || r->tag != IXS_INT || r->u.ival <= 0)
    return NULL;

  ixs_interval iv = ixs_bounds_get(bnds, l);
  if (iv.valid && iv.lo_q == 1 && iv.hi_q == 1 && iv.lo_p >= 0 &&
      iv.hi_p < r->u.ival)
    return l;

  /* x ≡ rem (mod m) with m % M == 0  ⟹  Mod(x, M) == rem % M */
  if (l->tag == IXS_SYM) {
    int64_t sym_mod, sym_rem;
    if (ixs_bounds_get_modrem(bnds, l->u.name, &sym_mod, &sym_rem) &&
        sym_mod % r->u.ival == 0)
      return ixs_node_int(ctx, sym_rem % r->u.ival);
  }

  if (is_known_divisible(bnds, l, r->u.ival))
    return ixs_node_int(ctx, 0);

  return NULL;
}

/* max(l, r) -> l or r when bounds prove one always dominates. */
static ixs_node *max_bounds_collapse(ixs_ctx *ctx, ixs_bounds *bnds,
                                     ixs_node *l, ixs_node *r) {
  ixs_interval il, ir;
  (void)ctx;
  if (!bnds)
    return NULL;
  il = ixs_bounds_get(bnds, l);
  ir = ixs_bounds_get(bnds, r);
  if (!il.valid || !ir.valid)
    return NULL;
  if (ixs_rat_cmp(il.lo_p, il.lo_q, ir.hi_p, ir.hi_q) >= 0)
    return l;
  if (ixs_rat_cmp(ir.lo_p, ir.lo_q, il.hi_p, il.hi_q) >= 0)
    return r;
  return NULL;
}

/* min(l, r) -> l or r when bounds prove one always dominates. */
static ixs_node *min_bounds_collapse(ixs_ctx *ctx, ixs_bounds *bnds,
                                     ixs_node *l, ixs_node *r) {
  ixs_interval il, ir;
  (void)ctx;
  if (!bnds)
    return NULL;
  il = ixs_bounds_get(bnds, l);
  ir = ixs_bounds_get(bnds, r);
  if (!il.valid || !ir.valid)
    return NULL;
  if (ixs_rat_cmp(il.hi_p, il.hi_q, ir.lo_p, ir.lo_q) <= 0)
    return l;
  if (ixs_rat_cmp(ir.hi_p, ir.hi_q, il.lo_p, il.lo_q) <= 0)
    return r;
  return NULL;
}

/* Resolve (expr cmp 0) to TRUE/FALSE when bounds determine the outcome. */
static ixs_node *cmp_bounds_resolve(ixs_ctx *ctx, ixs_bounds *bnds,
                                    ixs_node *cmp_node) {
  ixs_interval iv;
  bool known = false;
  bool val = false;

  if (!bnds || cmp_node->tag != IXS_CMP ||
      !ixs_node_is_zero(cmp_node->u.binary.rhs))
    return NULL;

  iv = ixs_bounds_get(bnds, cmp_node->u.binary.lhs);
  if (!iv.valid)
    return NULL;

  switch (cmp_node->u.binary.cmp_op) {
  case IXS_CMP_GT:
    if (ixs_rat_cmp(iv.lo_p, iv.lo_q, 0, 1) > 0) {
      known = true;
      val = true;
    } else if (ixs_rat_cmp(iv.hi_p, iv.hi_q, 0, 1) <= 0) {
      known = true;
      val = false;
    }
    break;
  case IXS_CMP_GE:
    if (ixs_rat_cmp(iv.lo_p, iv.lo_q, 0, 1) >= 0) {
      known = true;
      val = true;
    } else if (ixs_rat_cmp(iv.hi_p, iv.hi_q, 0, 1) < 0) {
      known = true;
      val = false;
    }
    break;
  case IXS_CMP_LT:
    if (ixs_rat_cmp(iv.hi_p, iv.hi_q, 0, 1) < 0) {
      known = true;
      val = true;
    } else if (ixs_rat_cmp(iv.lo_p, iv.lo_q, 0, 1) >= 0) {
      known = true;
      val = false;
    }
    break;
  case IXS_CMP_LE:
    if (ixs_rat_cmp(iv.hi_p, iv.hi_q, 0, 1) <= 0) {
      known = true;
      val = true;
    } else if (ixs_rat_cmp(iv.lo_p, iv.lo_q, 0, 1) > 0) {
      known = true;
      val = false;
    }
    break;
  case IXS_CMP_EQ:
    if (ixs_rat_cmp(iv.lo_p, iv.lo_q, 0, 1) == 0 &&
        ixs_rat_cmp(iv.hi_p, iv.hi_q, 0, 1) == 0) {
      known = true;
      val = true;
    } else if (ixs_rat_cmp(iv.lo_p, iv.lo_q, 0, 1) > 0 ||
               ixs_rat_cmp(iv.hi_p, iv.hi_q, 0, 1) < 0) {
      known = true;
      val = false;
    }
    break;
  case IXS_CMP_NE:
    if (ixs_rat_cmp(iv.lo_p, iv.lo_q, 0, 1) > 0 ||
        ixs_rat_cmp(iv.hi_p, iv.hi_q, 0, 1) < 0) {
      known = true;
      val = true;
    }
    break;
  }
  if (known)
    return val ? ctx->node_true : ctx->node_false;
  return NULL;
}

static ixs_node *rewrite_impl(ixs_ctx *ctx, ixs_node *n, ixs_bounds *bnds,
                              rewrite_memo_slot *memo) {
  uint32_t i;

  switch (n->tag) {
  case IXS_INT:
  case IXS_RAT:
  case IXS_SYM:
  case IXS_TRUE:
  case IXS_FALSE:
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    return n;

  case IXS_ADD: {
    ixs_node *result = rewrite(ctx, n->u.add.coeff, bnds, memo);
    if (!result)
      return NULL;
    for (i = 0; i < n->u.add.nterms; i++) {
      ixs_node *t = rewrite(ctx, n->u.add.terms[i].term, bnds, memo);
      if (!t)
        return NULL;
      ixs_node *c = n->u.add.terms[i].coeff;
      result = simp_add(ctx, result, simp_mul(ctx, c, t));
      if (!result)
        return NULL;
    }
    return result;
  }
  case IXS_MUL: {
    ixs_node *result = rewrite(ctx, n->u.mul.coeff, bnds, memo);
    if (!result)
      return NULL;
    for (i = 0; i < n->u.mul.nfactors; i++) {
      ixs_node *b = rewrite(ctx, n->u.mul.factors[i].base, bnds, memo);
      if (!b)
        return NULL;
      ixs_mulfactor f;
      f.base = b;
      f.exp = n->u.mul.factors[i].exp;
      ixs_node *pw = ixs_node_mul(ctx, ixs_node_int(ctx, 1), 1, &f);
      if (!pw)
        return NULL;
      result = simp_mul(ctx, result, pw);
      if (!result)
        return NULL;
    }
    return result;
  }
  case IXS_FLOOR: {
    ixs_node *arg = rewrite(ctx, n->u.unary.arg, bnds, memo);
    return arg ? simp_floor_bnds(ctx, bnds, arg) : NULL;
  }
  case IXS_CEIL: {
    ixs_node *arg = rewrite(ctx, n->u.unary.arg, bnds, memo);
    return arg ? simp_ceil_bnds(ctx, bnds, arg) : NULL;
  }
  case IXS_MOD: {
    ixs_node *l = rewrite(ctx, n->u.binary.lhs, bnds, memo);
    ixs_node *r = rewrite(ctx, n->u.binary.rhs, bnds, memo);
    return (l && r) ? simp_mod_bnds(ctx, bnds, l, r) : NULL;
  }
  case IXS_MAX: {
    ixs_node *l = rewrite(ctx, n->u.binary.lhs, bnds, memo);
    ixs_node *r = rewrite(ctx, n->u.binary.rhs, bnds, memo);
    return (l && r) ? simp_max_bnds(ctx, bnds, l, r) : NULL;
  }
  case IXS_MIN: {
    ixs_node *l = rewrite(ctx, n->u.binary.lhs, bnds, memo);
    ixs_node *r = rewrite(ctx, n->u.binary.rhs, bnds, memo);
    return (l && r) ? simp_min_bnds(ctx, bnds, l, r) : NULL;
  }
  case IXS_XOR: {
    ixs_node *l = rewrite(ctx, n->u.binary.lhs, bnds, memo);
    ixs_node *r = rewrite(ctx, n->u.binary.rhs, bnds, memo);
    return (l && r) ? simp_xor(ctx, l, r) : NULL;
  }
  case IXS_CMP: {
    ixs_node *l = rewrite(ctx, n->u.binary.lhs, bnds, memo);
    ixs_node *r = rewrite(ctx, n->u.binary.rhs, bnds, memo);
    return (l && r) ? simp_cmp_bnds(ctx, bnds, l, n->u.binary.cmp_op, r) : NULL;
  }
  case IXS_PIECEWISE: {
    uint32_t nc = n->u.pw.ncases;
    ixs_arena_mark sm = ixs_arena_save(&ctx->scratch);
    ixs_node **vals =
        ixs_arena_alloc(&ctx->scratch, nc * sizeof(*vals), sizeof(void *));
    ixs_node **cds =
        ixs_arena_alloc(&ctx->scratch, nc * sizeof(*cds), sizeof(void *));
    if (!vals || !cds) {
      ixs_arena_restore(&ctx->scratch, sm);
      return NULL;
    }
    for (i = 0; i < nc; i++) {
      cds[i] = rewrite(ctx, n->u.pw.cases[i].cond, bnds, memo);
      if (!cds[i]) {
        ixs_arena_restore(&ctx->scratch, sm);
        return NULL;
      }
      /* For guarded branches, fork bounds with condition assumptions so
       * that e.g. Max(1, E) collapses when the condition proves E >= 1. */
      if (bnds && cds[i] != ctx->node_true && cds[i] != ctx->node_false) {
        ixs_arena_mark bm = ixs_arena_save(&ctx->scratch);
        ixs_bounds bbnds;
        if (ixs_bounds_fork(&bbnds, bnds)) {
          rewrite_memo_slot *bmemo =
              ixs_arena_alloc(&ctx->scratch, REWRITE_MEMO_SIZE * sizeof(*bmemo),
                              sizeof(void *));
          if (bmemo) {
            add_cond_to_bounds(&bbnds, cds[i]);
            memset(bmemo, 0, REWRITE_MEMO_SIZE * sizeof(*bmemo));
            vals[i] = rewrite(ctx, n->u.pw.cases[i].value, &bbnds, bmemo);
          } else {
            vals[i] = rewrite(ctx, n->u.pw.cases[i].value, bnds, memo);
          }
        } else {
          vals[i] = rewrite(ctx, n->u.pw.cases[i].value, bnds, memo);
        }
        ixs_arena_restore(&ctx->scratch, bm);
      } else {
        vals[i] = rewrite(ctx, n->u.pw.cases[i].value, bnds, memo);
      }
      if (!vals[i]) {
        ixs_arena_restore(&ctx->scratch, sm);
        return NULL;
      }
    }
    {
      ixs_node *pw = simp_pw(ctx, nc, vals, cds);
      ixs_arena_restore(&ctx->scratch, sm);
      return pw;
    }
  }
  case IXS_AND: {
    ixs_node *result = ctx->node_true;
    for (i = 0; i < n->u.logic.nargs; i++) {
      ixs_node *a = rewrite(ctx, n->u.logic.args[i], bnds, memo);
      if (!a)
        return NULL;
      result = simp_and(ctx, result, a);
      if (!result)
        return NULL;
    }
    return result;
  }
  case IXS_OR: {
    ixs_node *result = ctx->node_false;
    for (i = 0; i < n->u.logic.nargs; i++) {
      ixs_node *a = rewrite(ctx, n->u.logic.args[i], bnds, memo);
      if (!a)
        return NULL;
      result = simp_or(ctx, result, a);
      if (!result)
        return NULL;
    }
    return result;
  }
  case IXS_NOT: {
    ixs_node *a = rewrite(ctx, n->u.unary_bool.arg, bnds, memo);
    return a ? simp_not(ctx, a) : NULL;
  }
  }
  return n;
}

static ixs_node *simp_simplify_with_bounds(ixs_ctx *ctx, ixs_node *expr,
                                           ixs_bounds *bnds) {
  int iter;
  rewrite_memo_slot memo[REWRITE_MEMO_SIZE];

  if (!expr)
    return NULL;
  if (ixs_node_is_sentinel(expr))
    return expr;

  for (iter = 0; iter < SIMPLIFY_ITER_LIMIT; iter++) {
    ixs_node *prev = expr;
    memset(memo, 0, sizeof(memo));
    expr = rewrite(ctx, expr, bnds, memo);
    if (!expr)
      return NULL;
    if (expr == prev)
      break;
  }

  if (iter == SIMPLIFY_ITER_LIMIT)
    ixs_ctx_push_error(ctx, "simplify: iteration limit reached");

  return expr;
}

static bool build_bounds(ixs_bounds *bnds, ixs_arena *scratch,
                         ixs_node *const *assumptions, size_t n_assumptions) {
  if (!ixs_bounds_init(bnds, scratch))
    return false;
  if (assumptions) {
    size_t i;
    for (i = 0; i < n_assumptions; i++) {
      ixs_node *a = assumptions[i];
      if (!a || ixs_node_is_sentinel(a))
        continue;
      ixs_bounds_add_assumption(bnds, a);
    }
  }
  return true;
}

ixs_node *simp_simplify(ixs_ctx *ctx, ixs_node *expr,
                        ixs_node *const *assumptions, size_t n_assumptions) {
  ixs_arena_mark m = ixs_arena_save(&ctx->scratch);
  ixs_bounds bnds;
  if (!build_bounds(&bnds, &ctx->scratch, assumptions, n_assumptions)) {
    ixs_arena_restore(&ctx->scratch, m);
    return NULL;
  }
  expr = simp_simplify_with_bounds(ctx, expr, &bnds);
  ixs_bounds_destroy(&bnds);
  ixs_arena_restore(&ctx->scratch, m);
  return expr;
}

void simp_simplify_batch(ixs_ctx *ctx, ixs_node **exprs, size_t n,
                         ixs_node *const *assumptions, size_t n_assumptions) {
  ixs_arena_mark m = ixs_arena_save(&ctx->scratch);
  ixs_bounds bnds;
  size_t i;
  if (!build_bounds(&bnds, &ctx->scratch, assumptions, n_assumptions)) {
    for (i = 0; i < n; i++)
      exprs[i] = NULL;
    ixs_arena_restore(&ctx->scratch, m);
    return;
  }
  for (i = 0; i < n; i++) {
    if (!exprs[i] || ixs_node_is_sentinel(exprs[i]))
      continue;
    exprs[i] = simp_simplify_with_bounds(ctx, exprs[i], &bnds);
    if (!exprs[i]) {
      size_t j;
      for (j = 0; j < n; j++)
        exprs[j] = NULL;
      ixs_bounds_destroy(&bnds);
      ixs_arena_restore(&ctx->scratch, m);
      return;
    }
  }
  ixs_bounds_destroy(&bnds);
  ixs_arena_restore(&ctx->scratch, m);
}
