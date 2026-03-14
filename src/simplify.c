#include "simplify.h"
#include "bounds.h"
#include <stdlib.h>
#include <string.h>

/* Max terms/factors in a single flattened add/mul before we bail. */
#include "ixs_limits.h"
#define SIMPLIFY_ITER_LIMIT 64

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
      /* Rebuild MUL with coeff=1 */
      *base = ixs_node_mul(ctx, ixs_node_int(ctx, 1), n->u.mul.nfactors,
                           n->u.mul.factors);
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

  /* Constant / constant → rational fold */
  if (ixs_node_is_const(a) && ixs_node_is_const(b)) {
    int64_t ap, aq, bp, bq, rp, rq;
    ixs_node_get_rat(a, &ap, &aq);
    ixs_node_get_rat(b, &bp, &bq);
    if (!ixs_rat_div(ap, aq, bp, bq, &rp, &rq))
      return simp_err(ctx, "rational overflow in division");
    return make_const(ctx, rp, rq);
  }

  /* expr / constant → multiply by reciprocal */
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

ixs_node *simp_floor(ixs_ctx *ctx, ixs_node *x) {
  ixs_node *prop = ixs_propagate1(x);
  if (prop)
    return prop;

  /* floor(integer) → identity */
  if (x->tag == IXS_INT)
    return x;

  /* floor(p/q) → constant fold */
  if (x->tag == IXS_RAT)
    return ixs_node_int(ctx, ixs_rat_floor(x->u.rat.p, x->u.rat.q));

  /* floor(floor(x)) → floor(x), floor(ceil(x)) → ceil(x) */
  if (x->tag == IXS_FLOOR || x->tag == IXS_CEIL)
    return x;

  /* floor(x) → x when x is structurally integer-valued */
  if (ixs_node_is_integer_valued(x))
    return x;

  /* floor(x + n) where n is integer → floor(x) + n
   * Applies when x is ADD and has an integer constant part. */
  if (x->tag == IXS_ADD && x->u.add.coeff->tag == IXS_INT &&
      x->u.add.coeff->u.ival != 0) {
    int64_t n = x->u.add.coeff->u.ival;
    /* Build the ADD without the integer constant. */
    ixs_node *zero = ixs_node_int(ctx, 0);
    if (!zero)
      return NULL;
    ixs_node *inner;
    if (x->u.add.nterms == 1) {
      int64_t cp, cq;
      ixs_node_get_rat(x->u.add.terms[0].coeff, &cp, &cq);
      if (ixs_rat_is_one(cp, cq))
        inner = x->u.add.terms[0].term;
      else
        inner = ixs_node_add(ctx, zero, x->u.add.nterms, x->u.add.terms);
    } else {
      inner = ixs_node_add(ctx, zero, x->u.add.nterms, x->u.add.terms);
    }
    if (!inner)
      return NULL;
    return simp_add(ctx, simp_floor(ctx, inner), ixs_node_int(ctx, n));
  }

  /* floor(floor(y)/b) → floor(y/b) for positive integer b. */
  if (x->tag == IXS_MUL && x->u.mul.nfactors == 1 &&
      x->u.mul.factors[0].exp == 1 &&
      x->u.mul.factors[0].base->tag == IXS_FLOOR) {
    int64_t cp, cq;
    ixs_node_get_rat(x->u.mul.coeff, &cp, &cq);
    if (cp == 1 && cq > 1) {
      ixs_node *inner_arg = x->u.mul.factors[0].base->u.unary.arg;
      ixs_node *scaled = simp_mul(ctx, x->u.mul.coeff, inner_arg);
      if (!scaled)
        return NULL;
      return simp_floor(ctx, scaled);
    }
  }

  return ixs_node_floor(ctx, x);
}

ixs_node *simp_ceil(ixs_ctx *ctx, ixs_node *x) {
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

  /* ceiling(x + n) where n is integer → ceiling(x) + n */
  if (x->tag == IXS_ADD && x->u.add.coeff->tag == IXS_INT &&
      x->u.add.coeff->u.ival != 0) {
    int64_t n = x->u.add.coeff->u.ival;
    ixs_node *zero = ixs_node_int(ctx, 0);
    if (!zero)
      return NULL;
    ixs_node *inner;
    if (x->u.add.nterms == 1) {
      int64_t cp, cq;
      ixs_node_get_rat(x->u.add.terms[0].coeff, &cp, &cq);
      if (ixs_rat_is_one(cp, cq))
        inner = x->u.add.terms[0].term;
      else
        inner = ixs_node_add(ctx, zero, x->u.add.nterms, x->u.add.terms);
    } else {
      inner = ixs_node_add(ctx, zero, x->u.add.nterms, x->u.add.terms);
    }
    if (!inner)
      return NULL;
    return simp_add(ctx, simp_ceil(ctx, inner), ixs_node_int(ctx, n));
  }

  /* ceiling(ceiling(y)/b) → ceiling(y/b) for positive integer b. */
  if (x->tag == IXS_MUL && x->u.mul.nfactors == 1 &&
      x->u.mul.factors[0].exp == 1 &&
      x->u.mul.factors[0].base->tag == IXS_CEIL) {
    int64_t cp, cq;
    ixs_node_get_rat(x->u.mul.coeff, &cp, &cq);
    if (cp == 1 && cq > 1) {
      ixs_node *inner_arg = x->u.mul.factors[0].base->u.unary.arg;
      ixs_node *scaled = simp_mul(ctx, x->u.mul.coeff, inner_arg);
      if (!scaled)
        return NULL;
      return simp_ceil(ctx, scaled);
    }
  }

  return ixs_node_ceil(ctx, x);
}

/* ------------------------------------------------------------------ */
/*  simp_mod                                                          */
/* ------------------------------------------------------------------ */

ixs_node *simp_mod(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  if (!a || !b)
    return NULL;
  ixs_node *prop = ixs_propagate2(a, b);
  if (prop)
    return prop;

  /* Mod(x, 0) → error */
  if (ixs_node_is_zero(b))
    return simp_err(ctx, "Mod: divisor is zero");

  /* Mod(c1, c2) → constant fold */
  if (ixs_node_is_const(a) && ixs_node_is_const(b)) {
    int64_t ap, aq, bp, bq, rp, rq;
    ixs_node_get_rat(a, &ap, &aq);
    ixs_node_get_rat(b, &bp, &bq);
    if (ixs_rat_is_neg(bp))
      return simp_err(ctx, "Mod: divisor is negative");
    if (!ixs_rat_mod(ap, aq, bp, bq, &rp, &rq))
      return simp_err(ctx, "rational overflow in Mod");
    return make_const(ctx, rp, rq);
  }

  /* Mod(x, 1) → 0 when x is known integer-valued. */
  if (ixs_node_is_one(b) && ixs_node_is_integer_valued(a))
    return ixs_node_int(ctx, 0);

  /* Mod(c*t, m) → 0 when t is integer-valued and m divides c.
   * Catches Mod(a*floor(x/a), a) and similar. */
  if (a->tag == IXS_MUL && b->tag == IXS_INT && b->u.ival > 0) {
    int64_t cp, cq;
    ixs_node_get_rat(a->u.mul.coeff, &cp, &cq);
    if (cq == 1 && cp != 0 && cp % b->u.ival == 0) {
      uint32_t i;
      bool all_int = true;
      for (i = 0; i < a->u.mul.nfactors; i++) {
        if (a->u.mul.factors[i].exp < 0 ||
            !ixs_node_is_integer_valued(a->u.mul.factors[i].base)) {
          all_int = false;
          break;
        }
      }
      if (all_int)
        return ixs_node_int(ctx, 0);
    }
  }

  /* Mod(Mod(x, m), m) → Mod(x, m) */
  if (a->tag == IXS_MOD && a->u.binary.rhs == b)
    return a;

  /* Mod(x + k*m, m) -> Mod(x, m) when b is a constant integer.
   * Look for multiples of m in the additive terms of a. */
  if (a->tag == IXS_ADD && b->tag == IXS_INT && b->u.ival > 0) {
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

    if (changed) {
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
    ixs_arena_restore(&ctx->scratch, sm);
  }

  /* Extract a small constant addend from Mod when every other term's
   * coefficient divides the modulus.  Corrected from the Wave compiler:
   * use gcd(|ci|) not min(|ci|) for the bound on the extractable constant.
   *
   *   Mod(4*floor(a) + 3, 16)  →  Mod(4*floor(a), 16) + 3
   *
   * Proof: each |ci| | q, so sum = Σ ci*ti is a multiple of g = gcd(|ci|).
   * Then (sum mod q) ∈ {0, g, 2g, ..., q-g}.  If 0 < c < g, then
   * (sum mod q) + c < q, so Mod(sum + c, q) = (sum mod q) + c. */
  if (a->tag == IXS_ADD && b->tag == IXS_INT && b->u.ival > 0) {
    int64_t m = b->u.ival;
    int64_t const_p, const_q;
    ixs_node_get_rat(a->u.add.coeff, &const_p, &const_q);

    if (const_q == 1 && const_p > 0 && a->u.add.nterms > 0) {
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

      if (ok && g > 1 && const_p < g) {
        ixs_node *zero = ixs_node_int(ctx, 0);
        if (!zero)
          return NULL;
        ixs_node *inner =
            ixs_node_add(ctx, zero, a->u.add.nterms, a->u.add.terms);
        if (!inner)
          return NULL;
        ixs_node *moded = simp_mod(ctx, inner, b);
        if (!moded)
          return NULL;
        return simp_add(ctx, moded, ixs_node_int(ctx, const_p));
      }
    }
  }

  return ixs_node_binary(ctx, IXS_MOD, a, b, (ixs_cmp_op)0);
}

/* ------------------------------------------------------------------ */
/*  simp_max / simp_min                                               */
/* ------------------------------------------------------------------ */

ixs_node *simp_max(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  if (!a || !b)
    return NULL;
  ixs_node *prop = ixs_propagate2(a, b);
  if (prop)
    return prop;

  if (a == b)
    return a;

  if (ixs_node_is_const(a) && ixs_node_is_const(b)) {
    int64_t ap, aq, bp, bq;
    ixs_node_get_rat(a, &ap, &aq);
    ixs_node_get_rat(b, &bp, &bq);
    return ixs_rat_cmp(ap, aq, bp, bq) >= 0 ? a : b;
  }

  /* Canonical ordering: put smaller node on left. */
  if (ixs_node_cmp(a, b) > 0)
    return ixs_node_binary(ctx, IXS_MAX, b, a, (ixs_cmp_op)0);

  return ixs_node_binary(ctx, IXS_MAX, a, b, (ixs_cmp_op)0);
}

ixs_node *simp_min(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  if (!a || !b)
    return NULL;
  ixs_node *prop = ixs_propagate2(a, b);
  if (prop)
    return prop;

  if (a == b)
    return a;

  if (ixs_node_is_const(a) && ixs_node_is_const(b)) {
    int64_t ap, aq, bp, bq;
    ixs_node_get_rat(a, &ap, &aq);
    ixs_node_get_rat(b, &bp, &bq);
    return ixs_rat_cmp(ap, aq, bp, bq) <= 0 ? a : b;
  }

  if (ixs_node_cmp(a, b) > 0)
    return ixs_node_binary(ctx, IXS_MIN, b, a, (ixs_cmp_op)0);

  return ixs_node_binary(ctx, IXS_MIN, a, b, (ixs_cmp_op)0);
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

ixs_node *simp_cmp(ixs_ctx *ctx, ixs_node *a, ixs_cmp_op op, ixs_node *b) {
  if (!a || !b)
    return NULL;
  ixs_node *prop = ixs_propagate2(a, b);
  if (prop)
    return prop;

  /* Constant fold */
  if (ixs_node_is_const(a) && ixs_node_is_const(b)) {
    int64_t ap, aq, bp, bq;
    ixs_node_get_rat(a, &ap, &aq);
    ixs_node_get_rat(b, &bp, &bq);
    int c = ixs_rat_cmp(ap, aq, bp, bq);
    bool result = false;
    switch (op) {
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

  /* a op a → fold */
  if (a == b) {
    switch (op) {
    case IXS_CMP_GE:
    case IXS_CMP_LE:
    case IXS_CMP_EQ:
      return ctx->node_true;
    case IXS_CMP_GT:
    case IXS_CMP_LT:
    case IXS_CMP_NE:
      return ctx->node_false;
    }
  }

  /* Normalize: (a op b) → ((a - b) op 0) */
  if (!ixs_node_is_zero(b)) {
    ixs_node *diff = simp_sub(ctx, a, b);
    if (!diff)
      return NULL;
    if (ixs_node_is_sentinel(diff))
      return diff;
    return simp_cmp(ctx, diff, op, ixs_node_int(ctx, 0));
  }

  return ixs_node_binary(ctx, IXS_CMP, a, b, op);
}

/* ------------------------------------------------------------------ */
/*  simp_and / simp_or / simp_not                                     */
/* ------------------------------------------------------------------ */

ixs_node *simp_not(ixs_ctx *ctx, ixs_node *a) {
  ixs_node *prop = ixs_propagate1(a);
  if (prop)
    return prop;

  if (a->tag == IXS_TRUE)
    return ctx->node_false;
  if (a->tag == IXS_FALSE)
    return ctx->node_true;

  /* ~~x → x */
  if (a->tag == IXS_NOT)
    return a->u.unary_bool.arg;

  /* ~(a > b) → a <= b, etc. */
  if (a->tag == IXS_CMP) {
    ixs_cmp_op flipped;
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
    return ixs_node_binary(ctx, IXS_CMP, a->u.binary.lhs, a->u.binary.rhs,
                           flipped);
  }

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
 * Handles: sym with known divisor, c*sym, sums of divisible terms. */
static bool is_known_divisible(ixs_bounds *bnds, ixs_node *expr, int64_t m) {
  if (!bnds || m <= 0)
    return false;

  /* Integer constant: m | val */
  if (expr->tag == IXS_INT)
    return expr->u.ival % m == 0;

  /* Symbol with known divisor d: m | d */
  if (expr->tag == IXS_SYM) {
    int64_t d = ixs_bounds_get_divisor(bnds, expr->u.name);
    return d > 0 && d % m == 0;
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

/* True when expr is provably integer-valued given divisibility info.
 * Extends ixs_node_is_integer_valued with divisibility reasoning:
 * p/q * sym is integer when q divides the known divisor of sym. */
static bool is_integer_with_divinfo(ixs_bounds *bnds, ixs_node *expr) {
  if (ixs_node_is_integer_valued(expr))
    return true;
  if (!bnds)
    return false;

  /* MUL: p/q * base^1 is integer if base's divisor absorbs q */
  if (expr->tag == IXS_MUL && expr->u.mul.nfactors == 1 &&
      expr->u.mul.factors[0].exp == 1) {
    int64_t cp, cq;
    ixs_node_get_rat(expr->u.mul.coeff, &cp, &cq);
    if (cq <= 1)
      return true;
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
    if (!arg)
      return NULL;

    if (bnds) {
      ixs_node *collapsed = try_floor_ceil_collapse(ctx, bnds, arg, false);
      if (collapsed)
        return collapsed;

      /* floor(x) → x when x is provably integer via divisibility */
      if (is_integer_with_divinfo(bnds, arg))
        return arg;

      /* Drop a small rational constant from floor's argument when every
       * term is a non-negative-integer-valued multiple of 1/qi.
       *
       *   floor(floor(a)/3 + 1/6)  →  floor(floor(a)/3)
       *
       * Each ti/qi has fractional part in {0, 1/L, ..., (L-1)/L} where
       * L = lcm(qi).  If 0 < r < 1/L, adding r can't cross an integer
       * boundary, so floor(sum + r) = floor(sum). */
      if (arg->tag == IXS_ADD && arg->u.add.coeff->tag == IXS_RAT &&
          arg->u.add.nterms > 0) {
        int64_t rp = arg->u.add.coeff->u.rat.p;
        int64_t rq = arg->u.add.coeff->u.rat.q;

        if (rp > 0 && rq > 1) {
          int64_t L = 1;
          bool ok = true;
          uint32_t j;

          for (j = 0; j < arg->u.add.nterms; j++) {
            int64_t cp, cq;
            ixs_node_get_rat(arg->u.add.terms[j].coeff, &cp, &cq);
            if (cq <= 1) {
              ok = false;
              break;
            }
            if (!ixs_node_is_integer_valued(arg->u.add.terms[j].term)) {
              ok = false;
              break;
            }
            ixs_interval ti = ixs_bounds_get(bnds, arg->u.add.terms[j].term);
            if (!ti.valid || ti.lo_q != 1 || ti.lo_p < 0) {
              ok = false;
              break;
            }
            int64_t g = ixs_gcd(L, cq);
            if (g == 0 || L > INT64_MAX / (cq / g)) {
              ok = false;
              break;
            }
            L = L / g * cq;
          }

          /* r < 1/L  ⟺  rp * L < rq  (since rp, rq, L > 0) */
          if (ok && L > 0 && rp <= INT64_MAX / L && rp * L < rq) {
            ixs_node *zero = ixs_node_int(ctx, 0);
            if (!zero)
              return NULL;
            ixs_node *inner =
                ixs_node_add(ctx, zero, arg->u.add.nterms, arg->u.add.terms);
            if (!inner)
              return NULL;
            return simp_floor(ctx, inner);
          }
        }
      }
    }
    return simp_floor(ctx, arg);
  }
  case IXS_CEIL: {
    ixs_node *arg = rewrite(ctx, n->u.unary.arg, bnds, memo);
    if (!arg)
      return NULL;

    if (bnds) {
      ixs_node *collapsed = try_floor_ceil_collapse(ctx, bnds, arg, true);
      if (collapsed)
        return collapsed;

      /* ceil(x) → x when x is provably integer via divisibility */
      if (is_integer_with_divinfo(bnds, arg))
        return arg;
    }
    return simp_ceil(ctx, arg);
  }
  case IXS_MOD: {
    ixs_node *l = rewrite(ctx, n->u.binary.lhs, bnds, memo);
    ixs_node *r = rewrite(ctx, n->u.binary.rhs, bnds, memo);
    if (!l || !r)
      return NULL;

    if (bnds && r->tag == IXS_INT && r->u.ival > 0) {
      /* Mod(x, m) where 0 <= x < m → x */
      ixs_interval iv = ixs_bounds_get(bnds, l);
      if (iv.valid && iv.lo_q == 1 && iv.hi_q == 1 && iv.lo_p >= 0 &&
          iv.hi_p < r->u.ival)
        return l;

      /* Mod(x, m) → 0 when x is known divisible by m */
      if (is_known_divisible(bnds, l, r->u.ival))
        return ixs_node_int(ctx, 0);
    }
    return simp_mod(ctx, l, r);
  }
  case IXS_MAX: {
    ixs_node *l = rewrite(ctx, n->u.binary.lhs, bnds, memo);
    ixs_node *r = rewrite(ctx, n->u.binary.rhs, bnds, memo);
    if (!l || !r)
      return NULL;

    if (bnds) {
      ixs_interval il = ixs_bounds_get(bnds, l);
      ixs_interval ir = ixs_bounds_get(bnds, r);
      /* If lo(l) >= hi(r), l is always >= r. */
      if (il.valid && ir.valid) {
        if (ixs_rat_cmp(il.lo_p, il.lo_q, ir.hi_p, ir.hi_q) >= 0)
          return l;
        if (ixs_rat_cmp(ir.lo_p, ir.lo_q, il.hi_p, il.hi_q) >= 0)
          return r;
      }
    }
    return simp_max(ctx, l, r);
  }
  case IXS_MIN: {
    ixs_node *l = rewrite(ctx, n->u.binary.lhs, bnds, memo);
    ixs_node *r = rewrite(ctx, n->u.binary.rhs, bnds, memo);
    if (!l || !r)
      return NULL;
    if (bnds) {
      ixs_interval il = ixs_bounds_get(bnds, l);
      ixs_interval ir = ixs_bounds_get(bnds, r);
      if (il.valid && ir.valid) {
        if (ixs_rat_cmp(il.hi_p, il.hi_q, ir.lo_p, ir.lo_q) <= 0)
          return l;
        if (ixs_rat_cmp(ir.hi_p, ir.hi_q, il.lo_p, il.lo_q) <= 0)
          return r;
      }
    }
    return simp_min(ctx, l, r);
  }
  case IXS_XOR: {
    ixs_node *l = rewrite(ctx, n->u.binary.lhs, bnds, memo);
    ixs_node *r = rewrite(ctx, n->u.binary.rhs, bnds, memo);
    return (l && r) ? simp_xor(ctx, l, r) : NULL;
  }
  case IXS_CMP: {
    ixs_node *l = rewrite(ctx, n->u.binary.lhs, bnds, memo);
    ixs_node *r = rewrite(ctx, n->u.binary.rhs, bnds, memo);
    if (!l || !r)
      return NULL;
    ixs_node *result = simp_cmp(ctx, l, n->u.binary.cmp_op, r);

    /* Bound-dependent: if diff = l - r is normalized to (expr cmp 0),
     * try to resolve using bounds. */
    if (result && result->tag == IXS_CMP && bnds &&
        ixs_node_is_zero(result->u.binary.rhs)) {
      ixs_interval iv = ixs_bounds_get(bnds, result->u.binary.lhs);
      if (iv.valid) {
        bool known = false;
        bool val = false;
        switch (result->u.binary.cmp_op) {
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
      }
    }
    return result;
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
      vals[i] = rewrite(ctx, n->u.pw.cases[i].value, bnds, memo);
      cds[i] = rewrite(ctx, n->u.pw.cases[i].cond, bnds, memo);
      if (!vals[i] || !cds[i]) {
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

static void build_bounds(ixs_bounds *bnds, ixs_node *const *assumptions,
                         size_t n_assumptions) {
  ixs_bounds_init(bnds);
  if (assumptions) {
    size_t i;
    for (i = 0; i < n_assumptions; i++) {
      ixs_node *a = assumptions[i];
      if (!a || ixs_node_is_sentinel(a))
        continue;
      ixs_bounds_add_assumption(bnds, a);
    }
  }
}

ixs_node *simp_simplify(ixs_ctx *ctx, ixs_node *expr,
                        ixs_node *const *assumptions, size_t n_assumptions) {
  ixs_bounds bnds;
  build_bounds(&bnds, assumptions, n_assumptions);
  expr = simp_simplify_with_bounds(ctx, expr, &bnds);
  ixs_bounds_destroy(&bnds);
  return expr;
}

void simp_simplify_batch(ixs_ctx *ctx, ixs_node **exprs, size_t n,
                         ixs_node *const *assumptions, size_t n_assumptions) {
  ixs_bounds bnds;
  size_t i;
  build_bounds(&bnds, assumptions, n_assumptions);
  for (i = 0; i < n; i++) {
    if (!exprs[i] || ixs_node_is_sentinel(exprs[i]))
      continue;
    exprs[i] = simp_simplify_with_bounds(ctx, exprs[i], &bnds);
    if (!exprs[i]) {
      size_t j;
      for (j = 0; j < n; j++)
        exprs[j] = NULL;
      ixs_bounds_destroy(&bnds);
      return;
    }
  }
  ixs_bounds_destroy(&bnds);
}
