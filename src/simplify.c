/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "simplify.h"
#include "bounds.h"
#include <assert.h>
#include <stdlib.h>
#include <string.h>

#define EQUAL_FLOOR_PAIR_LIMIT 256u
#define FLOOR_MOD_PAIR_LIMIT 256u

/* ---- Rule-chain dispatch ----------------------------------------- */
/* Rule-chain functions (rules and the helpers they call):
 *   return n    = rule didn't fire (no change)
 *   return new  = rule fired, use new node
 *   return NULL = OOM (propagated to caller) */

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

/* Forward declarations for helpers defined later in this file. */
static ixs_node *try_floor_ceil_collapse(ixs_ctx *ctx, ixs_bounds *bnds,
                                         ixs_node *n, bool is_ceil);
static ixs_node *simp_floor_bnds(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *x);
static ixs_node *simp_ceil_bnds(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *x);
static ixs_node *simp_trunc_bnds(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *x);
static ixs_node *simp_xor_many_bnds(ixs_ctx *ctx, ixs_bounds *bnds, uint32_t n,
                                    ixs_node *const *args);
static bool bounds_int_nonnegative_finite(ixs_bounds *bnds, ixs_node *expr);
static ixs_node *mod_bounds_elim(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *n);
static ixs_node *cmp_bounds_resolve(ixs_ctx *ctx, ixs_bounds *bnds,
                                    ixs_node *n);
static bool node_is_known_total_integer(const ixs_node *node);
static inline ixs_node *apply_pow(ixs_ctx *ctx, ixs_node *acc, ixs_node *base,
                                  int32_t exp);
IXS_STATIC ixs_node *simp_floor(ixs_ctx *ctx, ixs_node *x);
IXS_STATIC ixs_node *simp_ceil(ixs_ctx *ctx, ixs_node *x);
IXS_STATIC ixs_node *simp_trunc(ixs_ctx *ctx, ixs_node *x);
IXS_STATIC ixs_node *simp_div(ixs_ctx *ctx, ixs_node *a, ixs_node *b);

/* ------------------------------------------------------------------ */
/*  Helpers                                                           */
/* ------------------------------------------------------------------ */

static ixs_node *simp_err(ixs_ctx *ctx, const char *msg) {
  ixs_ctx_push_error(ctx, "%s", msg);
  return ctx->sentinel_error;
}

static ixs_node *simp_undefined(ixs_ctx *ctx, const char *msg) {
  ixs_ctx_push_error(ctx, "%s", msg);
  return ctx->transport_undefined ? ctx->sentinel_undefined
                                  : ctx->sentinel_error;
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

static inline ixs_node *make_const(ixs_ctx *ctx, int64_t p, int64_t q) {
  if (q == 1)
    return ixs_node_int(ctx, p);
  return ixs_node_rat(ctx, p, q);
}

static bool uint64_pow2(uint64_t v) { return v != 0 && (v & (v - 1u)) == 0; }

static bool int64_positive_pow2(int64_t v) {
  return v > 0 && uint64_pow2((uint64_t)v);
}

/*
 * Extract the additive coefficient and base from a node.
 * For MUL(coeff, factors): coefficient = coeff, base = MUL(1, factors)
 * For INT/RAT: pure constant.
 * For anything else: coefficient = 1, base = node.
 */
static inline void add_decompose(ixs_ctx *ctx, ixs_node *n, int64_t *cp,
                                 int64_t *cq, ixs_node **base) {
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

typedef const ixs_node *(*node_sort_key_fn)(const void *item);

static const ixs_node *addterm_sort_key(const void *item) {
  return ((const ixs_addterm *)item)->term;
}

static const ixs_node *mulfactor_sort_key(const void *item) {
  return ((const ixs_mulfactor *)item)->base;
}

static const ixs_node *node_ptr_sort_key(const void *item) {
  return *(ixs_node *const *)item;
}

static bool node_sort_merge(ixs_ctx *ctx, const unsigned char *src,
                            unsigned char *dst, size_t elem_size, size_t left,
                            size_t mid, size_t right, node_sort_key_fn key) {
  size_t i = left;
  size_t j = mid;
  size_t out = left;

  while (i < mid && j < right) {
    int order =
        ixs_node_cmp(ctx, key(src + i * elem_size), key(src + j * elem_size));
    if (order == IXS_NODE_CMP_OOM)
      return false;
    if (order <= 0) {
      memcpy(dst + out * elem_size, src + i * elem_size, elem_size);
      i++;
    } else {
      memcpy(dst + out * elem_size, src + j * elem_size, elem_size);
      j++;
    }
    out++;
  }
  if (i < mid)
    memcpy(dst + out * elem_size, src + i * elem_size, (mid - i) * elem_size);
  else if (j < right)
    memcpy(dst + out * elem_size, src + j * elem_size, (right - j) * elem_size);
  return true;
}

/* Stable O(n log n) sort with O(n) scratch. Canonical arrays and the common
 * sorted-prefix-plus-one case take one linear scan. */
static bool node_key_sort(ixs_ctx *ctx, void *items, size_t count,
                          size_t elem_size, node_sort_key_fn key) {
  unsigned char *base = (unsigned char *)items;
  unsigned char *temp;
  unsigned char *src;
  unsigned char *dst;
  ixs_arena_mark mark;
  size_t first_break = 0;
  size_t breaks = 0;
  size_t i;
  size_t width;

  if (count < 2u)
    return true;
  if (count > (size_t)-1 / elem_size)
    return false;
  for (i = 1; i < count; i++) {
    int order = ixs_node_cmp(ctx, key(base + (i - 1u) * elem_size),
                             key(base + i * elem_size));
    if (order == IXS_NODE_CMP_OOM)
      return false;
    if (order > 0) {
      if (breaks == 0)
        first_break = i;
      breaks++;
    }
  }
  if (breaks == 0)
    return true;

  mark = ixs_arena_save(&ctx->scratch);
  temp = ixs_arena_alloc(&ctx->scratch, count * elem_size, sizeof(void *));
  if (!temp) {
    ixs_arena_restore(&ctx->scratch, mark);
    return false;
  }
  if (breaks == 1u) {
    bool ok =
        node_sort_merge(ctx, base, temp, elem_size, 0, first_break, count, key);
    if (ok)
      memcpy(base, temp, count * elem_size);
    ixs_arena_restore(&ctx->scratch, mark);
    return ok;
  }

  src = base;
  dst = temp;
  width = 1u;
  while (width < count) {
    size_t left;
    for (left = 0; left < count; left += width * 2u) {
      size_t mid = left + width;
      size_t right;
      if (mid > count)
        mid = count;
      right = mid + width;
      if (right > count)
        right = count;
      if (!node_sort_merge(ctx, src, dst, elem_size, left, mid, right, key)) {
        ixs_arena_restore(&ctx->scratch, mark);
        return false;
      }
    }
    {
      unsigned char *swap = src;
      src = dst;
      dst = swap;
    }
    if (width > count / 2u)
      width = count;
    else
      width *= 2u;
  }
  if (src != base)
    memcpy(base, src, count * elem_size);
  ixs_arena_restore(&ctx->scratch, mark);
  return true;
}

static bool node_ptr_insert_last(ixs_ctx *ctx, ixs_node **items, size_t count) {
  ixs_node *value;
  size_t lo = 0;
  size_t hi;

  if (count < 2u)
    return true;
  value = items[count - 1u];
  hi = count - 1u;
  while (lo < hi) {
    size_t mid = lo + (hi - lo) / 2u;
    int order = ixs_node_cmp(ctx, items[mid], value);
    if (order == IXS_NODE_CMP_OOM)
      return false;
    if (order <= 0)
      lo = mid + 1u;
    else
      hi = mid;
  }
  if (lo != count - 1u) {
    memmove(items + lo + 1u, items + lo, (count - lo - 1u) * sizeof(*items));
    items[lo] = value;
  }
  return true;
}

/* Sort addterms by base, then merge like terms by summing coefficients.
 * Returns 1 on success, 0 on OOM, and -1 on rational overflow. */
static int coalesce_addterms(ixs_ctx *ctx, ixs_addterm *terms, uint32_t nterms,
                             uint32_t *result_count) {
  if (!node_key_sort(ctx, terms, nterms, sizeof(ixs_addterm), addterm_sort_key))
    return 0;
  uint32_t w = 0;
  for (uint32_t k = 0; k < nterms; k++) {
    if (w > 0 && terms[w - 1].term == terms[k].term) {
      int64_t ap, aq, bp, bq, rp, rq;
      ixs_node_get_rat(terms[w - 1].coeff, &ap, &aq);
      ixs_node_get_rat(terms[k].coeff, &bp, &bq);
      if (!ixs_rat_add(ap, aq, bp, bq, &rp, &rq))
        return -1;
      if (ixs_rat_is_zero(rp)) {
        w--;
      } else {
        terms[w - 1].coeff = make_const(ctx, rp, rq);
        if (!terms[w - 1].coeff)
          return 0;
      }
    } else {
      if (w != k)
        terms[w] = terms[k];
      w++;
    }
  }
  *result_count = w;
  return 1;
}

typedef struct {
  ixs_addterm *terms;
  size_t cap;
  uint32_t nterms;
  int64_t const_p;
  int64_t const_q;
} add_accum;

static uint32_t flatten_mul_add_terms(ixs_ctx *ctx, ixs_addterm **terms_p,
                                      size_t *cap_p, uint32_t nterms,
                                      int64_t *const_p, int64_t *const_q);
static ixs_node *recognize_mod(ixs_ctx *ctx, ixs_addterm *terms,
                               uint32_t nterms, int64_t const_p,
                               int64_t const_q);
static ixs_node *cancel_floor_mod_pairs(ixs_ctx *ctx, ixs_addterm *terms,
                                        uint32_t nterms, int64_t const_p,
                                        int64_t const_q, bool allow_wide);
static ixs_node *xor_difference_in_add(ixs_ctx *ctx, ixs_addterm *terms,
                                       uint32_t nterms, int64_t const_p,
                                       int64_t const_q);
static ixs_node *pw_fold_in_add(ixs_ctx *ctx, ixs_addterm *terms,
                                uint32_t nterms, int64_t const_p,
                                int64_t const_q);

static inline int32_t find_pow1_factor(ixs_node *mul, ixs_tag tag) {
  uint32_t k;
  if (mul->tag != IXS_MUL)
    return -1;
  if (mul->u.mul.nfactors == 0 || mul->u.mul.factors[0].base->tag > tag ||
      mul->u.mul.factors[mul->u.mul.nfactors - 1].base->tag < tag)
    return -1;
  for (k = 0; k < mul->u.mul.nfactors; k++) {
    if (mul->u.mul.factors[k].base->tag < tag)
      continue;
    if (mul->u.mul.factors[k].base->tag > tag)
      break;
    if (mul->u.mul.factors[k].base->tag == tag &&
        mul->u.mul.factors[k].exp == 1)
      return (int32_t)k;
  }
  return -1;
}

/* Optional arithmetic folding may reject an unrepresentable flattened form,
 * but allocation failure must never be mistaken for that no-match. */
static ixs_node *try_mul_power(ixs_ctx *ctx, ixs_node *result, ixs_node *base,
                               int32_t exp, bool *no_match) {
  ixs_arena_mark diag_mark = ixs_arena_save(&ctx->diag);
  const char **saved_errors = ctx->errors;
  size_t saved_nerrors = ctx->nerrors;
  size_t saved_errors_cap = ctx->errors_cap;
  ixs_node *power = apply_pow(ctx, ixs_node_int(ctx, 1), base, exp);

  if (power && !ixs_node_is_sentinel(power))
    power = simp_mul(ctx, result, power);
  *no_match = power && ixs_node_is_sentinel(power);
  ixs_arena_restore(&ctx->diag, diag_mark);
  ctx->errors = saved_errors;
  ctx->nerrors = saved_nerrors;
  ctx->errors_cap = saved_errors_cap;
  return *no_match ? NULL : power;
}

static ixs_node *mul_power_or_raw(ixs_ctx *ctx, ixs_node *result,
                                  ixs_node *base, int32_t exp, bool try_fold) {
  ixs_node *power;
  ixs_mulfactor factor;

  if (try_fold) {
    bool no_match = false;
    if (exp < 0 && ixs_node_is_zero(base))
      return simp_div(ctx, result, base);
    power = try_mul_power(ctx, result, base, exp, &no_match);
    if (power)
      return power;
    if (!no_match)
      return NULL;
  }
  factor.base = base;
  factor.exp = exp;
  power = ixs_node_int(ctx, 1);
  power = power ? ixs_node_mul(ctx, power, 1, &factor) : NULL;
  return power ? simp_mul(ctx, result, power) : NULL;
}

static inline ixs_node *mul_without_factor(ixs_ctx *ctx, ixs_node *mul,
                                           int32_t skip_idx) {
  uint32_t k;
  ixs_node *outer = mul->u.mul.coeff;
  for (k = 0; k < mul->u.mul.nfactors && outer; k++) {
    if ((int32_t)k == skip_idx)
      continue;
    outer = mul_power_or_raw(ctx, outer, mul->u.mul.factors[k].base,
                             mul->u.mul.factors[k].exp, false);
  }
  return outer;
}

static inline bool add_accum_push(ixs_ctx *ctx, add_accum *acc, int64_t cp,
                                  int64_t cq, ixs_node *base) {
  if (!base)
    return ixs_rat_add(acc->const_p, acc->const_q, cp, cq, &acc->const_p,
                       &acc->const_q);
  if (acc->nterms >= acc->cap) {
    acc->terms =
        scratch_grow(&ctx->scratch, acc->terms, &acc->cap, sizeof(*acc->terms));
    if (!acc->terms)
      return false;
  }
  acc->terms[acc->nterms].coeff = make_const(ctx, cp, cq);
  if (!acc->terms[acc->nterms].coeff)
    return false;
  acc->terms[acc->nterms].term = base;
  acc->nterms++;
  return true;
}

static inline bool add_accum_scaled_node(ixs_ctx *ctx, add_accum *acc,
                                         int64_t sp, int64_t sq,
                                         ixs_node *node) {
  int64_t np, nq, rp, rq;
  ixs_node *base;
  if (!node)
    return false;
  add_decompose(ctx, node, &np, &nq, &base);
  if (!ixs_rat_mul(sp, sq, np, nq, &rp, &rq))
    return false;
  return add_accum_push(ctx, acc, rp, rq, base);
}

static inline int add_accum_push_checked(ixs_ctx *ctx, add_accum *acc,
                                         int64_t cp, int64_t cq,
                                         ixs_node *base) {
  if (!base) {
    return ixs_rat_add(acc->const_p, acc->const_q, cp, cq, &acc->const_p,
                       &acc->const_q)
               ? 1
               : -1;
  }
  if (acc->nterms >= acc->cap) {
    acc->terms =
        scratch_grow(&ctx->scratch, acc->terms, &acc->cap, sizeof(*acc->terms));
    if (!acc->terms)
      return 0;
  }
  acc->terms[acc->nterms].term = base;
  acc->terms[acc->nterms].coeff = make_const(ctx, cp, cq);
  if (!acc->terms[acc->nterms].coeff)
    return 0;
  acc->nterms++;
  return 1;
}

static inline int add_accum_absorb_scaled_add(ixs_ctx *ctx, add_accum *acc,
                                              int64_t sp, int64_t sq,
                                              ixs_node *add) {
  uint32_t j;
  int64_t bp, bq, rp, rq;
  ixs_node_get_rat(add->u.add.coeff, &bp, &bq);
  if (!ixs_rat_mul(sp, sq, bp, bq, &rp, &rq))
    return -1;
  int rc = add_accum_push_checked(ctx, acc, rp, rq, NULL);
  if (rc <= 0)
    return rc;
  for (j = 0; j < add->u.add.nterms; j++) {
    int64_t tp, tq, np, nq;
    ixs_node_get_rat(add->u.add.terms[j].coeff, &tp, &tq);
    if (!ixs_rat_mul(sp, sq, tp, tq, &np, &nq))
      return -1;
    rc = add_accum_push_checked(ctx, acc, np, nq, add->u.add.terms[j].term);
    if (rc <= 0)
      return rc;
  }
  return 1;
}

static inline int add_accum_absorb_node(ixs_ctx *ctx, add_accum *acc,
                                        ixs_node *x) {
  int64_t cp, cq;
  ixs_node *base;
  if (x->tag == IXS_ADD)
    return add_accum_absorb_scaled_add(ctx, acc, 1, 1, x);
  add_decompose(ctx, x, &cp, &cq, &base);
  if (!base)
    return add_accum_push_checked(ctx, acc, cp, cq, NULL);
  if (base->tag == IXS_ADD)
    return add_accum_absorb_scaled_add(ctx, acc, cp, cq, base);
  return add_accum_push_checked(ctx, acc, cp, cq, base);
}

static inline bool add_accum_has_tag(add_accum *acc, ixs_tag tag) {
  uint32_t i;
  for (i = 0; i < acc->nterms; i++) {
    if (acc->terms[i].term && acc->terms[i].term->tag == tag)
      return true;
  }
  return false;
}

static inline int add_accum_coalesce(ixs_ctx *ctx, add_accum *acc) {
  return coalesce_addterms(ctx, acc->terms, acc->nterms, &acc->nterms);
}

static inline int add_accum_flatten_mod_terms(ixs_ctx *ctx, add_accum *acc) {
  uint32_t flattened;
  if (!add_accum_has_tag(acc, IXS_MOD))
    return 1;
  flattened = flatten_mul_add_terms(ctx, &acc->terms, &acc->cap, acc->nterms,
                                    &acc->const_p, &acc->const_q);
  if (flattened == (uint32_t)-1)
    return -1;
  acc->nterms = flattened;
  return add_accum_coalesce(ctx, acc);
}

static ixs_node *add_try_rewrites(ixs_ctx *ctx, add_accum *acc) {
  ixs_node *result;
  result =
      recognize_mod(ctx, acc->terms, acc->nterms, acc->const_p, acc->const_q);
  if (result)
    return result;
  result = cancel_floor_mod_pairs(ctx, acc->terms, acc->nterms, acc->const_p,
                                  acc->const_q, false);
  if (result)
    return result;
  result = xor_difference_in_add(ctx, acc->terms, acc->nterms, acc->const_p,
                                 acc->const_q);
  if (result)
    return result;
  return pw_fold_in_add(ctx, acc->terms, acc->nterms, acc->const_p,
                        acc->const_q);
}

static ixs_node *add_build_result(ixs_ctx *ctx, add_accum *acc) {
  if (acc->nterms == 0)
    return make_const(ctx, acc->const_p, acc->const_q);

  if (acc->nterms == 1 && ixs_rat_is_zero(acc->const_p)) {
    int64_t cp, cq;
    ixs_node_get_rat(acc->terms[0].coeff, &cp, &cq);
    if (ixs_rat_is_one(cp, cq))
      return acc->terms[0].term;
    return simp_mul(ctx, make_const(ctx, cp, cq), acc->terms[0].term);
  }

  {
    ixs_node *coeff = make_const(ctx, acc->const_p, acc->const_q);
    if (!coeff)
      return NULL;
    return ixs_node_add(ctx, coeff, acc->nterms, acc->terms);
  }
}

static uint32_t compact_addterms(ixs_addterm *terms, uint32_t nterms) {
  uint32_t r, w = 0;
  for (r = 0; r < nterms; r++) {
    if (terms[r].term) {
      if (w != r)
        terms[w] = terms[r];
      w++;
    }
  }
  return w;
}

static bool addterm_coeffs_cancel(const ixs_addterm *terms, uint32_t i,
                                  uint32_t j, int64_t *ci_p, int64_t *ci_q) {
  int64_t cj_p, cj_q, sp, sq;
  ixs_node_get_rat(terms[i].coeff, ci_p, ci_q);
  ixs_node_get_rat(terms[j].coeff, &cj_p, &cj_q);
  if (!ixs_rat_add(*ci_p, *ci_q, cj_p, cj_q, &sp, &sq))
    return false;
  return ixs_rat_is_zero(sp);
}

static int replace_opposite_mul_add_pair(
    ixs_ctx *ctx, ixs_addterm *terms, uint32_t nterms, uint32_t i, uint32_t j,
    ixs_node *outer, int32_t ai, int32_t aj, int64_t ci_p, int64_t ci_q,
    int64_t *const_p, int64_t *const_q, uint32_t *result_count) {
  int64_t np, nq, rp, rq;
  ixs_node *nbase;
  ixs_node *add_a = terms[i].term->u.mul.factors[ai].base;
  ixs_node *add_b = terms[j].term->u.mul.factors[aj].base;
  ixs_node *neg_b = simp_mul(ctx, ixs_node_int(ctx, -1), add_b);
  ixs_node *diff = neg_b ? simp_add(ctx, add_a, neg_b) : NULL;
  ixs_node *new_term = diff ? simp_mul(ctx, outer, diff) : NULL;
  if (!new_term)
    return 0;

  add_decompose(ctx, new_term, &np, &nq, &nbase);
  if (!ixs_rat_mul(ci_p, ci_q, np, nq, &rp, &rq))
    return -1;
  if (!nbase) {
    if (!ixs_rat_add(*const_p, *const_q, rp, rq, const_p, const_q))
      return -1;
    terms[j] = terms[nterms - 1];
    nterms--;
    terms[i] = terms[nterms - 1];
    nterms--;
  } else {
    terms[i].coeff = make_const(ctx, rp, rq);
    if (!terms[i].coeff)
      return 0;
    terms[i].term = nbase;
    terms[j] = terms[nterms - 1];
    nterms--;
  }
  return coalesce_addterms(ctx, terms, nterms, result_count);
}

static bool flatten_one_mul_add(ixs_ctx *ctx, add_accum *acc, uint32_t idx,
                                int32_t add_idx, ixs_node *outer) {
  uint32_t j;
  int64_t orig_cp, orig_cq;
  ixs_node *add = acc->terms[idx].term->u.mul.factors[add_idx].base;
  ixs_node_get_rat(acc->terms[idx].coeff, &orig_cp, &orig_cq);

  if (!add_accum_scaled_node(ctx, acc, orig_cp, orig_cq,
                             simp_mul(ctx, outer, add->u.add.coeff)))
    return false;

  for (j = 0; j < add->u.add.nterms; j++) {
    ixs_node *child =
        simp_mul(ctx, add->u.add.terms[j].coeff, add->u.add.terms[j].term);
    ixs_node *product = child ? simp_mul(ctx, outer, child) : NULL;
    if (!add_accum_scaled_node(ctx, acc, orig_cp, orig_cq, product))
      return false;
  }

  acc->terms[idx].term = NULL;
  return true;
}

/* Reduce opposite-coefficient MUL pairs that share all factors except
 * one ADD^1 base.  c*K*(PW+A) - c*K*(PW+B) -> c*K*(A-B).
 * Enables cancellation of shared Piecewise sub-expressions.
 * Canonical factor ordering can put the ADD^1 factor at different positions;
 * compare the outer product instead.
 * Returns 1 on success, 0 on OOM, and -1 on rational overflow. */
static int reduce_opposite_mul_add(ixs_ctx *ctx, ixs_addterm *terms,
                                   uint32_t *nterms_ptr, int64_t *const_p,
                                   int64_t *const_q) {
  uint32_t nterms = *nterms_ptr;
  uint32_t i, j;
  bool changed = true;
  while (changed) {
    changed = false;
    for (i = 0; i < nterms && !changed; i++) {
      ixs_node *mi = terms[i].term;
      int32_t ai;
      ixs_node *outer_i;
      if (mi->tag != IXS_MUL || mi->u.mul.nfactors < 2)
        continue;
      ai = find_pow1_factor(mi, IXS_ADD);
      if (ai < 0)
        continue;
      outer_i = mul_without_factor(ctx, mi, ai);
      if (!outer_i)
        return 0;
      for (j = i + 1; j < nterms; j++) {
        ixs_node *mj = terms[j].term;
        int32_t aj;
        int64_t ci_p, ci_q;
        ixs_node *outer_j;
        if (mj->tag != IXS_MUL || mj->u.mul.nfactors != mi->u.mul.nfactors)
          continue;
        if (!addterm_coeffs_cancel(terms, i, j, &ci_p, &ci_q))
          continue;
        aj = find_pow1_factor(mj, IXS_ADD);
        if (aj < 0)
          continue;
        outer_j = mul_without_factor(ctx, mj, aj);
        if (!outer_j || outer_i != outer_j)
          continue;
        {
          uint32_t reduced;
          int rc = replace_opposite_mul_add_pair(ctx, terms, nterms, i, j,
                                                 outer_i, ai, aj, ci_p, ci_q,
                                                 const_p, const_q, &reduced);
          if (rc <= 0)
            return rc;
          nterms = reduced;
        }
        changed = true;
        break;
      }
    }
  }
  *nterms_ptr = nterms;
  return 1;
}

/* Distribute MUL-over-ADD for addterms whose base is MUL(..., ADD^1).
 * Expands  c * outer * (a1 + a2 + ...)  into  c*outer*a1, c*outer*a2, ...
 * so that floor/Mod nodes hidden inside the ADD become separate addterms
 * visible to cancel_floor_mod_pairs.
 * Returns new nterms, or (uint32_t)-1 on overflow/OOM. */
static uint32_t flatten_mul_add_terms(ixs_ctx *ctx, ixs_addterm **terms_p,
                                      size_t *cap_p, uint32_t nterms,
                                      int64_t *const_p, int64_t *const_q) {
  add_accum acc;
  uint32_t orig_n = nterms;
  uint32_t i;

  acc.terms = *terms_p;
  acc.cap = *cap_p;
  acc.nterms = nterms;
  acc.const_p = *const_p;
  acc.const_q = *const_q;

  for (i = 0; i < orig_n; i++) {
    ixs_node *base = acc.terms[i].term;
    int32_t add_idx;
    ixs_node *outer;
    if (base->tag != IXS_MUL)
      continue;
    add_idx = find_pow1_factor(base, IXS_ADD);
    if (add_idx < 0)
      continue;
    outer = mul_without_factor(ctx, base, add_idx);
    if (!outer)
      return (uint32_t)-1;
    if (!flatten_one_mul_add(ctx, &acc, i, add_idx, outer))
      return (uint32_t)-1;
  }

  acc.nterms = compact_addterms(acc.terms, acc.nterms);
  *terms_p = acc.terms;
  *cap_p = acc.cap;
  *const_p = acc.const_p;
  *const_q = acc.const_q;
  return acc.nterms;
}

/* ------------------------------------------------------------------ */
/*  simp_add                                                          */
/* ------------------------------------------------------------------ */

/*
 * Mod recognition pass over additive terms.
 *
 * Pass 1 — constant divisor (N is integer, embedded in MUL coeff):
 *   floor: c*E + d*floor(E/N) where d == -c*N  ->  c*Mod(E, N)
 *   ceil:  c*E + d*ceil(E/N)  where d == -c*N  -> -c*Mod(-E, N)
 *
 * Pass 2 — symbolic divisor (D is a factor product in the outer MUL):
 *   floor: c*E - c*(D*floor(E/D))              ->  c*Mod(E, D)
 *   ceil:  c*(D*ceil(E/D)) - c*E               -> -c*Mod(-E, D)
 *
 * Matched terms are NULLed and the result is rebuilt through simp_add.
 * Returns the simplified node, or NULL if no pattern matched.
 */
/* Pass 1: constant-divisor Mod recognition.  Returns 1 if any pair was
 * matched, 0 if none, -1 on allocation failure. */
static int recognize_mod_const_div(ixs_ctx *ctx, ixs_addterm *terms,
                                   uint32_t nterms) {
  uint32_t i, j;
  int found = 0;

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
          return -1;
        mod_node = simp_mod(ctx, neg_base, ixs_node_int(ctx, N));
        if (!mod_node)
          return -1;
        terms[j].term = mod_node;
        terms[j].coeff = make_const(ctx, -bp, bq);
        if (!terms[j].coeff)
          return -1;
      } else {
        mod_node = simp_mod(ctx, fbase, ixs_node_int(ctx, N));
        if (!mod_node)
          return -1;
        terms[j].term = mod_node;
      }
      terms[i].term = NULL;
      found = 1;
      break;
    }
  }
  return found;
}

static int32_t find_unique_round_factor(ixs_node *mul_term, bool *is_ceil) {
  int32_t fl_idx = -1;
  uint32_t k;
  for (k = 0; k < mul_term->u.mul.nfactors; k++) {
    ixs_tag tag = mul_term->u.mul.factors[k].base->tag;
    if ((tag == IXS_FLOOR || tag == IXS_CEIL) &&
        mul_term->u.mul.factors[k].exp == 1) {
      if (fl_idx >= 0)
        return -1;
      fl_idx = (int32_t)k;
      *is_ceil = (tag == IXS_CEIL);
    }
  }
  return fl_idx;
}

static int recognize_mod_sym_match(ixs_ctx *ctx, ixs_addterm *terms, uint32_t i,
                                   uint32_t j, ixs_node *candidate_E,
                                   ixs_node *D, bool is_ceil) {
  int64_t bp, bq, rp, rq, sp, sq;
  ixs_node *mod_node;
  if (j == i || !terms[j].term || terms[j].term != candidate_E)
    return 0;
  ixs_node_get_rat(terms[j].coeff, &bp, &bq);
  ixs_node_get_rat(terms[i].coeff, &rp, &rq);
  if (!ixs_rat_add(bp, bq, rp, rq, &sp, &sq) || sp != 0)
    return 0;

  if (is_ceil) {
    ixs_node *neg_E;
    if (bp == INT64_MIN)
      return 0;
    neg_E = simp_mul(ctx, ixs_node_int(ctx, -1), candidate_E);
    if (!neg_E)
      return -1;
    mod_node = simp_mod(ctx, neg_E, D);
    if (!mod_node)
      return -1;
    terms[j].term = mod_node;
    terms[j].coeff = make_const(ctx, -bp, bq);
    if (!terms[j].coeff)
      return -1;
  } else {
    mod_node = simp_mod(ctx, candidate_E, D);
    if (!mod_node)
      return -1;
    terms[j].term = mod_node;
  }
  terms[i].term = NULL;
  return 1;
}

/* Pass 2: symbolic-divisor Mod recognition.  Same return convention. */
static int recognize_mod_sym_div(ixs_ctx *ctx, ixs_addterm *terms,
                                 uint32_t nterms) {
  uint32_t i, j;
  int found = 0;

  for (i = 0; i < nterms; i++) {
    ixs_node *mul_term, *round_arg, *D, *candidate_E;
    int32_t fl_idx;
    bool is_ceil;

    if (!terms[i].term || terms[i].term->tag != IXS_MUL)
      continue;
    mul_term = terms[i].term;

    fl_idx = find_unique_round_factor(mul_term, &is_ceil);
    if (fl_idx < 0)
      continue;

    round_arg = mul_term->u.mul.factors[fl_idx].base->u.unary.arg;
    D = mul_without_factor(ctx, mul_term, fl_idx);
    if (!D)
      return -1;

    candidate_E = simp_mul(ctx, D, round_arg);
    if (!candidate_E)
      return -1;

    for (j = 0; j < nterms; j++) {
      int rc =
          recognize_mod_sym_match(ctx, terms, i, j, candidate_E, D, is_ceil);
      if (rc < 0)
        return -1;
      if (rc > 0) {
        found = 1;
        break;
      }
    }
  }
  return found;
}

static ixs_node *recognize_mod(ixs_ctx *ctx, ixs_addterm *terms,
                               uint32_t nterms, int64_t const_p,
                               int64_t const_q) {
  uint32_t i;
  int rc1, rc2;
  ixs_node *result;
  ixs_addterm *snap = NULL;

  /* Snapshot terms so we can roll back if a pass hits OOM after
   * partially rewriting entries (NULLing matched floor/ceil terms
   * and replacing their partners with Mod nodes). */
  if (nterms > 0) {
    snap =
        ixs_arena_alloc(&ctx->scratch, nterms * sizeof(*snap), sizeof(void *));
    if (!snap)
      return NULL;
    memcpy(snap, terms, nterms * sizeof(*terms));
  }

  rc1 = recognize_mod_const_div(ctx, terms, nterms);
  if (rc1 < 0)
    goto rollback;
  rc2 = recognize_mod_sym_div(ctx, terms, nterms);
  if (rc2 < 0)
    goto rollback;
  if (!rc1 && !rc2)
    return NULL;

  IXS_STAT_HIT(ctx);
  result = make_const(ctx, const_p, const_q);
  if (!result)
    goto rollback;
  for (i = 0; i < nterms; i++) {
    ixs_node *t;
    if (!terms[i].term)
      continue;
    t = simp_mul(ctx, terms[i].coeff, terms[i].term);
    if (!t)
      goto rollback;
    result = simp_add(ctx, result, t);
    if (!result)
      goto rollback;
  }
  return result;

rollback:
  if (snap)
    memcpy(terms, snap, nterms * sizeof(*terms));
  return NULL;
}

/*
 * simp_mul with compound-base decomposition for inverse factors:
 *   (c * g1^e1 * ...)^{-1}  ->  (1/c) * g1^{-e1} * ...
 *
 * Enables symbolic cancellation like K * (K/2)^{-1} -> 2 that plain
 * simp_mul misses because it treats compound MUL bases as opaque.
 * Restricted to exp == -1 to avoid exponent-overflow headaches.
 */
static ixs_node *simp_mul_decompose(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  ixs_node *r = simp_mul(ctx, a, b);
  uint32_t i, j, k;
  if (!r || r->tag != IXS_MUL)
    return r;

  for (i = 0; i < r->u.mul.nfactors; i++) {
    ixs_node *mb, *acc;
    int64_t cp, cq;
    bool safe;

    if (r->u.mul.factors[i].base->tag != IXS_MUL ||
        r->u.mul.factors[i].exp != -1)
      continue;

    mb = r->u.mul.factors[i].base;
    if (mb->u.mul.nfactors == 0)
      continue;

    safe = true;
    for (k = 0; k < mb->u.mul.nfactors; k++) {
      if (mb->u.mul.factors[k].exp == INT32_MIN) {
        safe = false;
        break;
      }
    }
    if (!safe)
      continue;

    ixs_node_get_rat(mb->u.mul.coeff, &cp, &cq);
    if (cp == 0)
      continue;

    acc = simp_div(ctx, r->u.mul.coeff, make_const(ctx, cp, cq));
    if (!acc)
      return NULL;

    for (j = 0; j < r->u.mul.nfactors && acc; j++) {
      if (j == i) {
        for (k = 0; k < mb->u.mul.nfactors && acc; k++)
          acc = apply_pow(ctx, acc, mb->u.mul.factors[k].base,
                          -mb->u.mul.factors[k].exp);
      } else {
        acc = apply_pow(ctx, acc, r->u.mul.factors[j].base,
                        r->u.mul.factors[j].exp);
      }
    }
    return acc ? acc : r;
  }
  return r;
}

/*
 * Distribute factor over an ADD with compound-base decomposition.
 * factor * (c + sum ci*ti)  ->  factor*c + sum factor*ci*ti
 *
 * Uses simp_mul_decompose for each product so that symbolic factors
 * cancel through compound MUL bases (e.g. (K/2) * (2/K)*term -> term).
 * The individual simp_add calls may trigger cancel_floor_mod_pairs
 * recursively, handling nested floor/Mod pairs that become exposed
 * once compound bases are resolved.
 */
static ixs_node *distribute_mul_decompose(ixs_ctx *ctx, ixs_node *factor,
                                          ixs_node *x) {
  uint32_t i;
  ixs_node *result;
  if (x->tag != IXS_ADD)
    return simp_mul_decompose(ctx, factor, x);
  result = simp_mul_decompose(ctx, factor, x->u.add.coeff);
  if (!result)
    return NULL;
  for (i = 0; i < x->u.add.nterms; i++) {
    ixs_node *term =
        simp_mul(ctx, x->u.add.terms[i].coeff, x->u.add.terms[i].term);
    if (!term)
      return NULL;
    term = simp_mul_decompose(ctx, factor, term);
    if (!term)
      return NULL;
    result = simp_add(ctx, result, term);
    if (!result)
      return NULL;
  }
  return result;
}

typedef struct {
  ixs_node *node;
  ixs_node *arg;
  ixs_node *mul;
} floor_term_parts;

typedef struct {
  ixs_node *node;
  ixs_node *arg;
  ixs_node *modulus;
  ixs_node *outer;
} mod_term_parts;

static bool floor_parts_from_addterm(ixs_ctx *ctx, ixs_addterm *term,
                                     floor_term_parts *parts) {
  int32_t floor_idx;
  ixs_node *mul_rest;
  parts->node = NULL;
  parts->arg = NULL;
  parts->mul = NULL;

  if (term->term->tag == IXS_FLOOR) {
    parts->node = term->term;
    parts->arg = term->term->u.unary.arg;
    parts->mul = term->coeff;
    return true;
  }

  if (term->term->tag != IXS_MUL)
    return false;
  floor_idx = find_pow1_factor(term->term, IXS_FLOOR);
  if (floor_idx < 0)
    return false;
  mul_rest = mul_without_factor(ctx, term->term, floor_idx);
  if (!mul_rest || ixs_node_is_sentinel(mul_rest))
    return false;
  parts->node = term->term->u.mul.factors[floor_idx].base;
  parts->arg = parts->node->u.unary.arg;
  parts->mul = simp_mul(ctx, term->coeff, mul_rest);
  return parts->mul != NULL;
}

static bool mod_parts_from_addterm(ixs_ctx *ctx, ixs_addterm *term,
                                   mod_term_parts *parts) {
  int32_t mod_idx;
  parts->node = NULL;
  parts->arg = NULL;
  parts->modulus = NULL;
  parts->outer = NULL;

  if (term->term->tag == IXS_MOD) {
    parts->node = term->term;
    parts->outer = ixs_node_int(ctx, 1);
  } else {
    if (term->term->tag != IXS_MUL)
      return false;
    mod_idx = find_pow1_factor(term->term, IXS_MOD);
    if (mod_idx < 0)
      return false;
    parts->node = term->term->u.mul.factors[mod_idx].base;
    parts->outer = mul_without_factor(ctx, term->term, mod_idx);
  }
  if (!parts->outer || ixs_node_is_sentinel(parts->outer))
    return false;
  parts->arg = parts->node->u.binary.lhs;
  parts->modulus = parts->node->u.binary.rhs;
  return true;
}

static bool floor_mul_matches(ixs_ctx *ctx, ixs_node *floor_mul,
                              ixs_node *ci_times_m) {
  ixs_node *ratio;
  ixs_node *inv;
  if (floor_mul == ci_times_m)
    return true;
  inv = simp_div(ctx, ixs_node_int(ctx, 1), ci_times_m);
  ratio = inv ? simp_mul_decompose(ctx, floor_mul, inv) : NULL;
  return ratio && ratio == ixs_node_int(ctx, 1);
}

static bool floor_pair_matches(ixs_ctx *ctx, ixs_node *expected_floor,
                               floor_term_parts *parts, ixs_node *m,
                               ixs_node *A) {
  ixs_node *E;
  if (expected_floor && expected_floor == parts->node)
    return true;
  E = distribute_mul_decompose(ctx, m, parts->arg);
  return E && !ixs_node_is_sentinel(E) && E == A;
}

static ixs_node *rebuild_add_from_terms(ixs_ctx *ctx, ixs_addterm *terms,
                                        uint32_t nterms, int64_t const_p,
                                        int64_t const_q) {
  uint32_t i;
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

static ixs_node *rebuild_add_without_pair(ixs_ctx *ctx, ixs_node *add,
                                          uint32_t skip_a, uint32_t skip_b) {
  uint32_t i;
  ixs_node *result = add->u.add.coeff;
  for (i = 0; i < add->u.add.nterms && result; i++) {
    ixs_node *term;
    if (i == skip_a || i == skip_b)
      continue;
    term = simp_mul(ctx, add->u.add.terms[i].coeff, add->u.add.terms[i].term);
    result = term ? simp_add(ctx, result, term) : NULL;
  }
  return result;
}

typedef struct {
  ixs_node *modulus;
  int64_t coefficient_p;
  int64_t coefficient_q;
  uint32_t term_index;
  size_t next_plus_one;
} congruent_mod_index_entry;

static bool congruent_mod_term(const ixs_addterm *term, ixs_node **modulus,
                               int64_t *coefficient_p, int64_t *coefficient_q) {
  if (term->term->tag != IXS_MOD || term->term->u.binary.rhs->tag != IXS_INT ||
      term->term->u.binary.rhs->u.ival <= 0)
    return false;
  *modulus = term->term->u.binary.rhs;
  ixs_node_get_rat(term->coeff, coefficient_p, coefficient_q);
  return true;
}

static size_t congruent_mod_key_hash(const ixs_node *modulus,
                                     int64_t coefficient_p,
                                     int64_t coefficient_q) {
  uint64_t mixed = (uint64_t)((uintptr_t)modulus >> 3);
  mixed ^= (uint64_t)coefficient_p + UINT64_C(0x9e3779b97f4a7c15) +
           (mixed << 6) + (mixed >> 2);
  mixed ^= (uint64_t)coefficient_q + UINT64_C(0x9e3779b97f4a7c15) +
           (mixed << 6) + (mixed >> 2);
  mixed ^= mixed >> 33;
  mixed *= UINT64_C(0xff51afd7ed558ccd);
  mixed ^= mixed >> 33;
  return (size_t)mixed;
}

static bool congruent_mod_bucket_capacity(size_t count, size_t *capacity) {
  size_t target;
  size_t result = 16u;
  if (count > SIZE_MAX / 2u)
    return false;
  target = count * 2u;
  while (result < target) {
    if (result > SIZE_MAX / 2u)
      return false;
    result *= 2u;
  }
  *capacity = result;
  return true;
}

/* Index eligible terms by (modulus, rational coefficient).  Each term probes
 * only the chain for its exact opposite coefficient, so unrelated wide ADDs
 * remain linear without an arbitrary pair ceiling hiding later proofs. */
static ixs_node *cancel_congruent_mod_difference(ixs_ctx *ctx, ixs_bounds *bnds,
                                                 ixs_node *add) {
  ixs_arena_mark mark;
  congruent_mod_index_entry *entries;
  size_t *buckets;
  size_t bucket_capacity;
  size_t eligible = 0;
  size_t entry_count = 0;
  ixs_node *result = add;
  uint32_t i;

  if (!bnds || add->tag != IXS_ADD || ixs_bounds_has_empty(bnds))
    return add;
  for (i = 0; i < add->u.add.nterms; i++) {
    ixs_node *modulus;
    int64_t coefficient_p;
    int64_t coefficient_q;
    if (congruent_mod_term(&add->u.add.terms[i], &modulus, &coefficient_p,
                           &coefficient_q))
      eligible++;
  }
  if (eligible < 2u)
    return add;
  if (!congruent_mod_bucket_capacity(eligible, &bucket_capacity) ||
      eligible > SIZE_MAX / sizeof(*entries) ||
      bucket_capacity > SIZE_MAX / sizeof(*buckets))
    return NULL;

  mark = ixs_arena_save(&ctx->scratch);
  entries = ixs_arena_alloc(&ctx->scratch, eligible * sizeof(*entries),
                            sizeof(void *));
  buckets = ixs_arena_alloc(&ctx->scratch, bucket_capacity * sizeof(*buckets),
                            sizeof(void *));
  if (!entries || !buckets) {
    result = NULL;
    goto cleanup;
  }
  memset(buckets, 0, bucket_capacity * sizeof(*buckets));

  for (i = 0; i < add->u.add.nterms; i++) {
    ixs_node *current = add->u.add.terms[i].term;
    ixs_node *modulus;
    int64_t coefficient_p;
    int64_t coefficient_q;
    int64_t opposite_p;
    size_t slot;
    size_t link;
    if (!congruent_mod_term(&add->u.add.terms[i], &modulus, &coefficient_p,
                            &coefficient_q))
      continue;
    if (ixs_safe_neg(coefficient_p, &opposite_p)) {
      slot = congruent_mod_key_hash(modulus, opposite_p, coefficient_q) &
             (bucket_capacity - 1u);
      for (link = buckets[slot]; link != 0u;
           link = entries[link - 1u].next_plus_one) {
        congruent_mod_index_entry *candidate = &entries[link - 1u];
        ixs_node *previous;
        ixs_node *difference;
        if (candidate->modulus != modulus ||
            candidate->coefficient_p != opposite_p ||
            candidate->coefficient_q != coefficient_q)
          continue;
        previous = add->u.add.terms[candidate->term_index].term;
        /* Preserve the original left-to-right proof orientation.  Exact
         * relation projection may know `previous - current` directly even
         * though divisibility is mathematically sign-symmetric. */
        difference =
            simp_sub(ctx, previous->u.binary.lhs, current->u.binary.lhs);
        if (!difference || ixs_node_is_sentinel(difference)) {
          result = difference;
          goto cleanup;
        }
        if (ixs_bounds_check_congruent(bnds, difference, modulus->u.ival, 0) !=
            IXS_CHECK_TRUE) {
          if (bnds->oom) {
            result = NULL;
            goto cleanup;
          }
          continue;
        }
        IXS_STAT_HIT(ctx);
        result = rebuild_add_without_pair(ctx, add, candidate->term_index, i);
        goto cleanup;
      }
    }
    slot = congruent_mod_key_hash(modulus, coefficient_p, coefficient_q) &
           (bucket_capacity - 1u);
    entries[entry_count].modulus = modulus;
    entries[entry_count].coefficient_p = coefficient_p;
    entries[entry_count].coefficient_q = coefficient_q;
    entries[entry_count].term_index = i;
    entries[entry_count].next_plus_one = buckets[slot];
    buckets[slot] = ++entry_count;
  }

cleanup:
  ixs_arena_restore(&ctx->scratch, mark);
  return result;
}

static int cancel_floor_mod_at_impl(ixs_ctx *ctx, ixs_addterm *terms,
                                    uint32_t nterms, uint32_t i,
                                    size_t *inspected) {
  uint32_t j;
  mod_term_parts mod;
  ixs_node *ci_outer, *ci_outer_times_m, *expected_floor;
  int64_t ci_p, ci_q;

  if (!terms[i].term || !mod_parts_from_addterm(ctx, &terms[i], &mod))
    return 0;

  ixs_node_get_rat(terms[i].coeff, &ci_p, &ci_q);

  ci_outer = simp_mul(ctx, terms[i].coeff, mod.outer);
  ci_outer_times_m = ci_outer ? simp_mul(ctx, ci_outer, mod.modulus) : NULL;
  if (!ci_outer_times_m || ixs_node_is_sentinel(ci_outer_times_m))
    return 0;

  expected_floor = simp_floor(ctx, simp_div(ctx, mod.arg, mod.modulus));
  if (!expected_floor || ixs_node_is_sentinel(expected_floor))
    expected_floor = NULL;

  for (j = 0; j < nterms; j++) {
    floor_term_parts parts;
    ixs_node *replacement;
    if (j == i || !terms[j].term)
      continue;
    if (*inspected >= FLOOR_MOD_PAIR_LIMIT)
      return 0;
    (*inspected)++;
    if (!floor_parts_from_addterm(ctx, &terms[j], &parts))
      continue;
    if (!floor_mul_matches(ctx, parts.mul, ci_outer_times_m))
      continue;
    if (!floor_pair_matches(ctx, expected_floor, &parts, mod.modulus, mod.arg))
      continue;
    replacement = simp_mul(ctx, mod.outer, mod.arg);
    if (!replacement)
      return -1;
    if (ixs_node_is_sentinel(replacement))
      return 0;
    terms[i].term = NULL;
    terms[j].term = replacement;
    terms[j].coeff = make_const(ctx, ci_p, ci_q);
    return terms[j].coeff ? 1 : -1;
  }
  return 0;
}

/* Cancellation probes never own user-visible diagnostics. */
static int cancel_floor_mod_at(ixs_ctx *ctx, ixs_addterm *terms,
                               uint32_t nterms, uint32_t i, size_t *inspected,
                               bool allow_wide) {
  ixs_node *term = terms[i].term;
  ixs_arena_mark diag_mark;
  const char **saved_errors;
  size_t saved_nerrors;
  size_t saved_errors_cap;
  int result;

  if (!term || (term->tag != IXS_MOD && nterms > 2u && !allow_wide) ||
      (term->tag != IXS_MOD &&
       (term->tag != IXS_MUL || find_pow1_factor(term, IXS_MOD) < 0)))
    return 0;
  diag_mark = ixs_arena_save(&ctx->diag);
  saved_errors = ctx->errors;
  saved_nerrors = ctx->nerrors;
  saved_errors_cap = ctx->errors_cap;
  result = cancel_floor_mod_at_impl(ctx, terms, nterms, i, inspected);

  ixs_arena_restore(&ctx->diag, diag_mark);
  ctx->errors = saved_errors;
  ctx->nerrors = saved_nerrors;
  ctx->errors_cap = saved_errors_cap;
  return result;
}

/* O(total ADD structure + FLOOR_MOD_PAIR_LIMIT pair probes).
 * c*o*m*floor(E/m) + c*o*Mod(E,m) -> c*o*E. */
static ixs_node *cancel_floor_mod_pairs(ixs_ctx *ctx, ixs_addterm *terms,
                                        uint32_t nterms, int64_t const_p,
                                        int64_t const_q, bool allow_wide) {
  bool found = false;
  uint32_t i;
  size_t inspected = 0;

  for (i = 0; i < nterms; i++) {
    int rc = cancel_floor_mod_at(ctx, terms, nterms, i, &inspected, allow_wide);
    if (rc < 0)
      return NULL;
    if (rc > 0)
      found = true;
    if (inspected >= FLOOR_MOD_PAIR_LIMIT)
      break;
  }

  if (!found)
    return NULL;

  IXS_STAT_HIT(ctx);
  return rebuild_add_from_terms(ctx, terms, nterms, const_p, const_q);
}

/* Wide nested-factor scans run once per completed rewrite, not per term added.
 */
static ixs_node *cancel_wide_floor_mod_node(ixs_ctx *ctx, ixs_node *add) {
  ixs_arena_mark mark;
  ixs_addterm *terms;
  ixs_node *result;
  int64_t const_p, const_q;
  uint32_t i;

  if (!add || add->tag != IXS_ADD || add->u.add.nterms <= 2u)
    return add;
  for (i = 0; i < add->u.add.nterms; i++) {
    ixs_node *term = add->u.add.terms[i].term;
    if (term->tag == IXS_MUL && find_pow1_factor(term, IXS_MOD) >= 0)
      break;
  }
  if (i == add->u.add.nterms)
    return add;
  mark = ixs_arena_save(&ctx->scratch);
  terms = ixs_arena_alloc(&ctx->scratch, add->u.add.nterms * sizeof(*terms),
                          sizeof(void *));
  if (!terms) {
    ixs_arena_restore(&ctx->scratch, mark);
    return add;
  }
  memcpy(terms, add->u.add.terms, add->u.add.nterms * sizeof(*terms));
  ixs_node_get_rat(add->u.add.coeff, &const_p, &const_q);
  result = cancel_floor_mod_pairs(ctx, terms, add->u.add.nterms, const_p,
                                  const_q, true);
  ixs_arena_restore(&ctx->scratch, mark);
  return result ? result : add;
}

static bool split_const_offset(ixs_node *expr, ixs_node **base,
                               int64_t *offset) {
  int64_t cp, cq, tp, tq;
  if (expr->tag != IXS_ADD) {
    *base = expr;
    *offset = 0;
    return true;
  }
  ixs_node_get_rat(expr->u.add.coeff, &cp, &cq);
  if (cq != 1)
    return false;
  if (expr->u.add.nterms == 0) {
    return false;
  }
  if (expr->u.add.nterms != 1)
    return false;
  ixs_node_get_rat(expr->u.add.terms[0].coeff, &tp, &tq);
  if (tp != 1 || tq != 1)
    return false;
  *base = expr->u.add.terms[0].term;
  *offset = cp;
  return true;
}

static bool xor_offset_delta(ixs_node *a, ixs_node *b, ixs_node **selector,
                             ixs_node **toggle_operand, int64_t *delta) {
  ixs_node *base_a, *base_b;
  int64_t off_a, off_b;
  int side_a, side_b;

  if (a->tag != IXS_XOR || b->tag != IXS_XOR || a->u.assoc.nargs != 2u ||
      b->u.assoc.nargs != 2u)
    return false;

  for (side_a = 0; side_a < 2; side_a++) {
    ixs_node *common_a = a->u.assoc.args[side_a];
    ixs_node *other_a = a->u.assoc.args[1 - side_a];
    for (side_b = 0; side_b < 2; side_b++) {
      ixs_node *common_b = b->u.assoc.args[side_b];
      ixs_node *other_b = b->u.assoc.args[1 - side_b];
      if (common_a != common_b)
        continue;
      if (!split_const_offset(other_a, &base_a, &off_a) ||
          !split_const_offset(other_b, &base_b, &off_b) || base_a != base_b)
        continue;
      if (!ixs_safe_sub(off_a, off_b, delta))
        return false;
      *selector = common_a;
      *toggle_operand = *delta > 0 ? other_b : other_a;
      return *delta != 0;
    }
  }
  return false;
}

static bool bit_known_zero_without_assumptions(ixs_ctx *ctx, ixs_node *expr,
                                               uint64_t bit) {
  ixs_bounds bnds;
  ixs_bitfacts bits;
  bool query_held = false;
  bool result;
  if (!ixs_bounds_init_ctx(&bnds, ctx, &ctx->scratch))
    return false;
  if (!ixs_bounds_query_hold_begin(&bnds, expr, &query_held)) {
    ixs_bounds_destroy(&bnds);
    return false;
  }
  result = ixs_bounds_get_bitfacts(&bnds, expr, &bits) &&
           (bits.known_zero & bit) != 0;
  if (query_held)
    ixs_bounds_query_hold_end(&bnds);
  ixs_bounds_destroy(&bnds);
  return result;
}

static ixs_node *xor_delta_expr(ixs_ctx *ctx, ixs_node *selector, int64_t delta,
                                ixs_node *scale) {
  ixs_node *mask_node, *selected, *twice_selected, *inner, *scaled;
  int64_t mag;
  bool negate = false;

  if (delta == INT64_MIN)
    return NULL;
  if (delta < 0) {
    negate = true;
    mag = -delta;
  } else {
    mag = delta;
  }
  if (!int64_positive_pow2(mag))
    return NULL;

  mask_node = ixs_node_int(ctx, mag);
  selected = simp_and(ctx, selector, mask_node);
  twice_selected =
      selected ? simp_mul(ctx, ixs_node_int(ctx, 2), selected) : NULL;
  inner = twice_selected ? simp_sub(ctx, mask_node, twice_selected) : NULL;
  if (inner && negate)
    inner = simp_neg(ctx, inner);
  scaled = inner ? simp_mul(ctx, scale, inner) : NULL;
  return scaled;
}

static ixs_node *xor_difference_in_add(ixs_ctx *ctx, ixs_addterm *terms,
                                       uint32_t nterms, int64_t const_p,
                                       int64_t const_q) {
  uint32_t i, j, k;

  for (i = 0; i < nterms; i++) {
    int64_t ci_p, ci_q;
    if (!terms[i].term || terms[i].term->tag != IXS_XOR)
      continue;
    ixs_node_get_rat(terms[i].coeff, &ci_p, &ci_q);

    for (j = i + 1; j < nterms; j++) {
      int64_t cj_p, cj_q, sum_p, sum_q, delta;
      ixs_node *selector, *toggle_operand, *replacement, *result;
      uint64_t bit;
      if (!terms[j].term || terms[j].term->tag != IXS_XOR)
        continue;
      ixs_node_get_rat(terms[j].coeff, &cj_p, &cj_q);
      if (!ixs_rat_add(ci_p, ci_q, cj_p, cj_q, &sum_p, &sum_q) ||
          !ixs_rat_is_zero(sum_p))
        continue;
      if (!xor_offset_delta(terms[i].term, terms[j].term, &selector,
                            &toggle_operand, &delta))
        continue;
      if (delta == INT64_MIN || delta == 0)
        continue;
      bit = (uint64_t)(delta < 0 ? -delta : delta);
      if (bit > (uint64_t)(INT64_MAX / 2))
        continue;
      if (!node_is_known_total_integer(toggle_operand) || !uint64_pow2(bit) ||
          !bit_known_zero_without_assumptions(ctx, toggle_operand, bit))
        continue;

      replacement = xor_delta_expr(ctx, selector, delta, terms[i].coeff);
      if (!replacement)
        return NULL;

      IXS_STAT_HIT(ctx);
      result = make_const(ctx, const_p, const_q);
      if (!result)
        return NULL;
      for (k = 0; k < nterms; k++) {
        ixs_node *t;
        if (k == i || k == j || !terms[k].term)
          continue;
        t = simp_mul(ctx, terms[k].coeff, terms[k].term);
        if (!t)
          return NULL;
        result = simp_add(ctx, result, t);
        if (!result)
          return NULL;
      }
      result = simp_add(ctx, result, replacement);
      return result;
    }
  }
  return NULL;
}

/* Fold PW terms in an ADD when 2+ share the same condition structure.
 * Distributes non-PW addends into each branch and merges PW values.
 * Returns the merged PW, or NULL if inapplicable or OOM. */
static ixs_node *pw_fold_in_add(ixs_ctx *ctx, ixs_addterm *terms,
                                uint32_t nterms, int64_t const_p,
                                int64_t const_q) {
  uint32_t i, j;
  int32_t first_pw = -1;
  uint32_t pw_count = 0;
  ixs_node *ref;
  uint32_t nc;

  for (i = 0; i < nterms; i++) {
    if (terms[i].term->tag == IXS_PIECEWISE) {
      if (first_pw < 0)
        first_pw = (int32_t)i;
      pw_count++;
    }
  }
  if (pw_count < 2)
    return NULL;

  ref = terms[first_pw].term;
  nc = ref->u.pw.ncases;

  for (i = (uint32_t)first_pw + 1; i < nterms; i++) {
    if (terms[i].term->tag != IXS_PIECEWISE)
      continue;
    if (terms[i].term->u.pw.ncases != nc)
      return NULL;
    for (j = 0; j < nc; j++) {
      if (terms[i].term->u.pw.cases[j].cond != ref->u.pw.cases[j].cond)
        return NULL;
    }
  }

  /* Build the non-PW portion of the sum. */
  ixs_node *non_pw = make_const(ctx, const_p, const_q);
  if (!non_pw)
    return NULL;
  for (i = 0; i < nterms; i++) {
    if (terms[i].term->tag == IXS_PIECEWISE)
      continue;
    ixs_node *scaled = simp_mul(ctx, terms[i].coeff, terms[i].term);
    non_pw = scaled ? simp_add(ctx, non_pw, scaled) : NULL;
    if (!non_pw)
      return NULL;
  }

  ixs_node **vals =
      ixs_arena_alloc(&ctx->scratch, nc * sizeof(*vals), sizeof(void *));
  ixs_node **cds =
      ixs_arena_alloc(&ctx->scratch, nc * sizeof(*cds), sizeof(void *));
  if (!vals || !cds)
    return NULL;

  for (j = 0; j < nc; j++) {
    ixs_node *branch = non_pw;
    for (i = 0; i < nterms; i++) {
      ixs_node *pw;
      ixs_node *scaled;
      if (terms[i].term->tag != IXS_PIECEWISE)
        continue;
      pw = terms[i].term;
      scaled = simp_mul(ctx, terms[i].coeff, pw->u.pw.cases[j].value);
      branch = scaled ? simp_add(ctx, branch, scaled) : NULL;
      if (!branch)
        return NULL;
    }
    vals[j] = branch;
    cds[j] = ref->u.pw.cases[j].cond;
  }

  return simp_pw(ctx, nc, vals, cds);
}

static ixs_node *simp_add_impl(ixs_ctx *ctx, ixs_node *a, ixs_node *b,
                               bool *unrepresentable) {
  ixs_node *prop;
  add_accum acc;
  int rc;

  if (!a || !b)
    return NULL;
  prop = ixs_propagate2(a, b);
  if (prop)
    return prop;

  acc.cap = 16;
  acc.nterms = 0;
  acc.const_p = 0;
  acc.const_q = 1;
  acc.terms = ixs_arena_alloc(&ctx->scratch, acc.cap * sizeof(*acc.terms),
                              sizeof(void *));
  if (!acc.terms)
    return NULL;

  rc = add_accum_absorb_node(ctx, &acc, a);
  if (rc < 0)
    goto overflow;
  if (rc == 0)
    return NULL;
  rc = add_accum_absorb_node(ctx, &acc, b);
  if (rc < 0)
    goto overflow;
  if (rc == 0)
    return NULL;

  rc = add_accum_coalesce(ctx, &acc);
  if (rc < 0)
    goto overflow;
  if (rc == 0)
    return NULL;

  rc = reduce_opposite_mul_add(ctx, acc.terms, &acc.nterms, &acc.const_p,
                               &acc.const_q);
  if (rc < 0)
    goto overflow;
  if (rc == 0)
    return NULL;

  rc = add_accum_flatten_mod_terms(ctx, &acc);
  if (rc < 0)
    goto overflow;
  if (rc == 0)
    return NULL;

  prop = add_try_rewrites(ctx, &acc);
  if (prop)
    return prop;
  return add_build_result(ctx, &acc);

overflow:
  if (unrepresentable) {
    *unrepresentable = true;
    return NULL;
  }
  return simp_err(ctx, "rational overflow in add");
}

IXS_STATIC ixs_node *simp_add(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  ixs_arena_mark m = ixs_arena_save(&ctx->scratch);
  ixs_node *result = simp_add_impl(ctx, a, b, NULL);
  ixs_arena_restore(&ctx->scratch, m);
  return result;
}

IXS_STATIC ixs_node *simp_try_add(ixs_ctx *ctx, ixs_node *a, ixs_node *b,
                                  bool *unrepresentable) {
  ixs_arena_mark m = ixs_arena_save(&ctx->scratch);
  ixs_node *result;
  *unrepresentable = false;
  result = simp_add_impl(ctx, a, b, unrepresentable);
  ixs_arena_restore(&ctx->scratch, m);
  return result;
}

/* ------------------------------------------------------------------ */
/*  simp_mul                                                          */
/* ------------------------------------------------------------------ */

typedef struct {
  ixs_mulfactor *factors;
  size_t cap;
  uint32_t nfactors;
  int64_t coeff_p;
  int64_t coeff_q;
} mul_accum;

static inline int mul_accum_scale(mul_accum *acc, int64_t cp, int64_t cq) {
  return ixs_rat_mul(acc->coeff_p, acc->coeff_q, cp, cq, &acc->coeff_p,
                     &acc->coeff_q)
             ? 1
             : -1;
}

static inline int mul_accum_push(ixs_ctx *ctx, mul_accum *acc, ixs_node *base,
                                 int32_t exp) {
  if (acc->nfactors >= acc->cap) {
    acc->factors = scratch_grow(&ctx->scratch, acc->factors, &acc->cap,
                                sizeof(*acc->factors));
    if (!acc->factors)
      return 0;
  }
  acc->factors[acc->nfactors].base = base;
  acc->factors[acc->nfactors].exp = exp;
  acc->nfactors++;
  return 1;
}

static inline bool mul_base_inverse_safe(ixs_node *base) {
  uint32_t k;
  for (k = 0; k < base->u.mul.nfactors; k++) {
    if (base->u.mul.factors[k].exp == INT32_MIN)
      return false;
  }
  return true;
}

static inline int mul_accum_try_flatten_factor(ixs_ctx *ctx, mul_accum *acc,
                                               ixs_mulfactor factor) {
  uint32_t k;
  int32_t ej = factor.exp;
  ixs_node *mb = factor.base;
  int64_t mp, mq;
  if ((ej != 1 && ej != -1) || mb->tag != IXS_MUL)
    return 1;

  ixs_node_get_rat(mb->u.mul.coeff, &mp, &mq);
  if (ej == -1) {
    int64_t tmp;
    if (mp == 0 || !mul_base_inverse_safe(mb))
      return 1;
    tmp = mp;
    mp = mq;
    mq = tmp;
    if (mq < 0) {
      mp = -mp;
      mq = -mq;
    }
  }

  if (mul_accum_scale(acc, mp, mq) < 0)
    return -1;
  for (k = 0; k < mb->u.mul.nfactors; k++) {
    int64_t flat_exp = (int64_t)mb->u.mul.factors[k].exp * (int64_t)ej;
    int rc;
    if (flat_exp > INT32_MAX || flat_exp < INT32_MIN)
      return -1;
    rc = mul_accum_push(ctx, acc, mb->u.mul.factors[k].base, (int32_t)flat_exp);
    if (rc <= 0)
      return rc;
  }
  return 2;
}

static inline int mul_accum_absorb_factor(ixs_ctx *ctx, mul_accum *acc,
                                          ixs_mulfactor factor) {
  int rc = mul_accum_try_flatten_factor(ctx, acc, factor);
  if (rc <= 0 || rc == 2)
    return rc;
  return mul_accum_push(ctx, acc, factor.base, factor.exp);
}

static inline int mul_accum_absorb_mul(ixs_ctx *ctx, mul_accum *acc,
                                       ixs_node *x) {
  uint32_t j;
  int64_t cp, cq;
  int rc;
  ixs_node_get_rat(x->u.mul.coeff, &cp, &cq);
  rc = mul_accum_scale(acc, cp, cq);
  if (rc < 0)
    return rc;
  for (j = 0; j < x->u.mul.nfactors; j++) {
    rc = mul_accum_absorb_factor(ctx, acc, x->u.mul.factors[j]);
    if (rc <= 0)
      return rc;
  }
  return 1;
}

static inline int mul_accum_absorb_node(ixs_ctx *ctx, mul_accum *acc,
                                        ixs_node *x) {
  if (ixs_node_is_const(x)) {
    int64_t xp, xq;
    ixs_node_get_rat(x, &xp, &xq);
    return mul_accum_scale(acc, xp, xq);
  }
  if (x->tag == IXS_MUL)
    return mul_accum_absorb_mul(ctx, acc, x);
  return mul_accum_push(ctx, acc, x, 1);
}

static inline int mul_accum_coalesce(ixs_ctx *ctx, mul_accum *acc) {
  uint32_t i, j;
  if (!node_key_sort(ctx, acc->factors, acc->nfactors, sizeof(ixs_mulfactor),
                     mulfactor_sort_key))
    return 0;

  j = 0;
  for (i = 0; i < acc->nfactors; i++) {
    if (j > 0 && acc->factors[j - 1].base == acc->factors[i].base) {
      int64_t new_exp =
          (int64_t)acc->factors[j - 1].exp + (int64_t)acc->factors[i].exp;
      if (new_exp > INT32_MAX || new_exp < INT32_MIN)
        return -1;
      if (new_exp == 0)
        j--;
      else
        acc->factors[j - 1].exp = (int32_t)new_exp;
    } else {
      if (j != i)
        acc->factors[j] = acc->factors[i];
      j++;
    }
  }
  acc->nfactors = j;
  return 1;
}

static ixs_node *mul_build_result(ixs_ctx *ctx, mul_accum *acc) {
  if (acc->nfactors == 0)
    return make_const(ctx, acc->coeff_p, acc->coeff_q);
  if (acc->nfactors == 1 && acc->factors[0].exp == 1 &&
      ixs_rat_is_one(acc->coeff_p, acc->coeff_q))
    return acc->factors[0].base;
  {
    ixs_node *coeff = make_const(ctx, acc->coeff_p, acc->coeff_q);
    if (!coeff)
      return NULL;
    return ixs_node_mul(ctx, coeff, acc->nfactors, acc->factors);
  }
}

static ixs_node *simp_mul_impl(ixs_ctx *ctx, ixs_node *a, ixs_node *b,
                               bool *unrepresentable) {
  ixs_node *prop;
  mul_accum acc;
  int rc;

  if (!a || !b)
    return NULL;
  prop = ixs_propagate2(a, b);
  if (prop)
    return prop;

  acc.cap = 16;
  acc.nfactors = 0;
  acc.coeff_p = 1;
  acc.coeff_q = 1;
  acc.factors = ixs_arena_alloc(&ctx->scratch, acc.cap * sizeof(*acc.factors),
                                sizeof(void *));
  if (!acc.factors)
    return NULL;

  rc = mul_accum_absorb_node(ctx, &acc, a);
  if (rc < 0)
    goto overflow;
  if (rc == 0)
    return NULL;
  rc = mul_accum_absorb_node(ctx, &acc, b);
  if (rc < 0)
    goto overflow;
  if (rc == 0)
    return NULL;

  if (ixs_rat_is_zero(acc.coeff_p))
    return ixs_node_int(ctx, 0);

  rc = mul_accum_coalesce(ctx, &acc);
  if (rc < 0)
    goto overflow;
  if (rc == 0)
    return NULL;

  return mul_build_result(ctx, &acc);

overflow:
  if (unrepresentable) {
    *unrepresentable = true;
    return NULL;
  }
  return simp_err(ctx, "rational overflow in multiply");
}

IXS_STATIC ixs_node *simp_mul(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  ixs_arena_mark m = ixs_arena_save(&ctx->scratch);
  ixs_node *result = simp_mul_impl(ctx, a, b, NULL);
  ixs_arena_restore(&ctx->scratch, m);
  return result;
}

IXS_STATIC ixs_node *simp_try_mul(ixs_ctx *ctx, ixs_node *a, ixs_node *b,
                                  bool *unrepresentable) {
  ixs_arena_mark m = ixs_arena_save(&ctx->scratch);
  ixs_node *result;
  *unrepresentable = false;
  result = simp_mul_impl(ctx, a, b, unrepresentable);
  ixs_arena_restore(&ctx->scratch, m);
  return result;
}

/* ------------------------------------------------------------------ */
/*  simp_neg / simp_sub / simp_div                                    */
/* ------------------------------------------------------------------ */

IXS_STATIC ixs_node *simp_neg(ixs_ctx *ctx, ixs_node *a) {
  ixs_node *prop;
  if (!a)
    return NULL;
  prop = ixs_propagate1(a);
  if (prop)
    return prop;
  return simp_mul(ctx, ixs_node_int(ctx, -1), a);
}

IXS_STATIC ixs_node *simp_sub(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  if (!a || !b)
    return NULL;
  ixs_node *prop = ixs_propagate2(a, b);
  if (prop)
    return prop;
  return simp_add(ctx, a, simp_neg(ctx, b));
}

static ixs_node *simp_div_impl(ixs_ctx *ctx, ixs_node *a, ixs_node *b,
                               bool *unrepresentable) {
  if (!a || !b)
    return NULL;
  ixs_node *prop = ixs_propagate2(a, b);
  if (prop)
    return prop;

  /* Division by zero */
  if (ixs_node_is_zero(b))
    return simp_undefined(ctx, "division by zero");

  /* Constant / constant -> rational fold */
  if (ixs_node_is_const(a) && ixs_node_is_const(b)) {
    int64_t ap, aq, bp, bq, rp, rq;
    ixs_node_get_rat(a, &ap, &aq);
    ixs_node_get_rat(b, &bp, &bq);
    if (!ixs_rat_div(ap, aq, bp, bq, &rp, &rq)) {
      if (unrepresentable) {
        *unrepresentable = true;
        return NULL;
      }
      return simp_err(ctx, "rational overflow in division");
    }
    return make_const(ctx, rp, rq);
  }

  /* expr / constant -> multiply by reciprocal */
  if (ixs_node_is_const(b)) {
    int64_t bp, bq, rp, rq;
    ixs_node_get_rat(b, &bp, &bq);
    if (!ixs_rat_div(1, 1, bp, bq, &rp, &rq)) {
      if (unrepresentable) {
        *unrepresentable = true;
        return NULL;
      }
      return simp_err(ctx, "rational overflow in division");
    }
    if (unrepresentable)
      return simp_try_mul(ctx, make_const(ctx, rp, rq), a, unrepresentable);
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
    if (unrepresentable)
      return simp_try_mul(ctx, a, binv, unrepresentable);
    return simp_mul(ctx, a, binv);
  }
}

IXS_STATIC ixs_node *simp_div(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  return simp_div_impl(ctx, a, b, NULL);
}

IXS_STATIC ixs_node *simp_try_div(ixs_ctx *ctx, ixs_node *a, ixs_node *b,
                                  bool *unrepresentable) {
  *unrepresentable = false;
  return simp_div_impl(ctx, a, b, unrepresentable);
}

/* ------------------------------------------------------------------ */
/*  simp_floor / simp_ceil                                            */
/* ------------------------------------------------------------------ */

typedef ixs_node *(*round_fn)(ixs_ctx *, ixs_node *);

/* Multiply acc by base^exp exactly. Positive exponents take logarithmic
 * multiply steps. Negative exponents retain the signed int32 exponent as a
 * structural factor, so INT32_MIN never passes through signed negation. NULL
 * means allocation failure; arithmetic/domain errors remain sentinels. */
static inline ixs_node *apply_pow(ixs_ctx *ctx, ixs_node *acc, ixs_node *base,
                                  int32_t exp) {
  uint32_t magnitude;
  ixs_node *power;
  if (!acc || !base)
    return NULL;
  if (exp == 0)
    return acc;
  if (ixs_node_is_sentinel(acc))
    return acc;
  if (exp < 0) {
    ixs_mulfactor factor;
    ixs_node *one;
    if (ixs_node_is_zero(base))
      return simp_div(ctx, acc, base);
    if (exp == -1)
      return simp_div(ctx, acc, base);
    factor.base = base;
    factor.exp = exp;
    one = ixs_node_int(ctx, 1);
    power = one ? ixs_node_mul(ctx, one, 1, &factor) : NULL;
    return power ? simp_mul(ctx, acc, power) : NULL;
  }

  magnitude = (uint32_t)exp;
  power = base;
  while (magnitude != 0u) {
    if ((magnitude & 1u) != 0u) {
      acc = simp_mul(ctx, acc, power);
      if (!acc || ixs_node_is_sentinel(acc))
        return acc;
    }
    magnitude >>= 1u;
    if (magnitude != 0u) {
      power = simp_mul(ctx, power, power);
      if (!power || ixs_node_is_sentinel(power))
        return power;
    }
  }
  return acc;
}

/* Apply base^(-exp) without evaluating -INT32_MIN. The inverse of
 * base^INT32_MIN cannot be rewritten to a positive int32 exponent, and a
 * nested reciprocal would change definedness at base == 0. Report that shape
 * as an optional no-match instead. */
static ixs_node *apply_inverse_power(ixs_ctx *ctx, ixs_node *acc,
                                     ixs_node *base, int32_t exp,
                                     bool *unsupported) {
  if (exp == INT32_MIN) {
    *unsupported = true;
    return acc;
  }
  return apply_pow(ctx, acc, base, -exp);
}

/*
 * True when the ADD product coeff*term is provably integer-valued.
 * With bounds: handles rational coefficients whose reduced denominator
 * divides the term per congruence info (e.g. (1/32)*K when 32|K).
 */
static bool addterm_is_integer_valued(ixs_bounds *bnds, ixs_node *coeff,
                                      ixs_node *term) {
  int64_t cp, cq;
  ixs_node_get_rat(coeff, &cp, &cq);
  if (cq == 1)
    return bnds ? ixs_bounds_is_integer_with_divinfo(bnds, term)
                : ixs_node_is_integer_valued(term);
  if (!bnds)
    return false;
  int64_t g = ixs_gcd(cp, cq);
  int64_t denom = cq / g;
  return ixs_bounds_is_known_divisible(bnds, term, denom);
}

static bool round_add_has_extractable(ixs_bounds *bnds, ixs_node *x,
                                      int64_t *rat_fl) {
  uint32_t i;
  *rat_fl = 0;
  if (x->u.add.coeff->tag == IXS_INT && x->u.add.coeff->u.ival != 0)
    return true;
  if (x->u.add.coeff->tag == IXS_RAT) {
    *rat_fl = ixs_rat_floor(x->u.add.coeff->u.rat.p, x->u.add.coeff->u.rat.q);
    if (*rat_fl != 0)
      return true;
  }
  for (i = 0; i < x->u.add.nterms; i++) {
    if (addterm_is_integer_valued(bnds, x->u.add.terms[i].coeff,
                                  x->u.add.terms[i].term))
      return true;
  }
  return false;
}

static bool round_split_constant(ixs_ctx *ctx, ixs_node *coeff, int64_t rat_fl,
                                 ixs_node **int_sum, ixs_node **rem_coeff) {
  if (coeff->tag == IXS_INT) {
    *int_sum = coeff;
    *rem_coeff = ixs_node_int(ctx, 0);
    return *rem_coeff != NULL;
  }
  if (coeff->tag == IXS_RAT && rat_fl != 0) {
    int64_t p = coeff->u.rat.p;
    int64_t q = coeff->u.rat.q;
    int64_t prod;
    if (ixs_safe_mul(rat_fl, q, &prod)) {
      int64_t rem_p = p - prod;
      int64_t rp, rq;
      *int_sum = ixs_node_int(ctx, rat_fl);
      if (rem_p == 0) {
        *rem_coeff = ixs_node_int(ctx, 0);
      } else if (ixs_rat_normalize(rem_p, q, &rp, &rq)) {
        *rem_coeff = make_const(ctx, rp, rq);
      } else {
        *int_sum = ixs_node_int(ctx, 0);
        *rem_coeff = coeff;
      }
      return *int_sum && *rem_coeff;
    }
  }
  *int_sum = ixs_node_int(ctx, 0);
  *rem_coeff = coeff;
  return *int_sum != NULL;
}

/*
 * Extract integer-valued addends from round(ADD).
 *   round(n + intval_terms + rest) -> n + intval_terms + round(rest)
 * When bnds is non-NULL, also extracts terms with rational coefficients
 * that are integer per congruence info (e.g. (1/32)*K when 32|K).
 * Returns the simplified node, x unchanged if nothing to extract,
 * or NULL on OOM.
 */
static ixs_node *round_extract_add(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *x,
                                   round_fn rnd) {
  bool extracted;
  uint32_t i;
  uint32_t nk = 0;
  int64_t rat_fl;
  ixs_node *int_sum;
  ixs_node *rem_coeff;
  ixs_node *remainder;
  ixs_arena_mark m;
  ixs_addterm *kept;

  if (x->tag != IXS_ADD)
    return x;
  if (!round_add_has_extractable(bnds, x, &rat_fl))
    return x;

  m = ixs_arena_save(&ctx->scratch);
  kept = ixs_arena_alloc(&ctx->scratch, x->u.add.nterms * sizeof(*kept),
                         sizeof(void *));
  if (!kept) {
    ixs_arena_restore(&ctx->scratch, m);
    return NULL;
  }

  if (!round_split_constant(ctx, x->u.add.coeff, rat_fl, &int_sum,
                            &rem_coeff)) {
    ixs_arena_restore(&ctx->scratch, m);
    return NULL;
  }
  extracted = !ixs_node_is_zero(int_sum);

  for (i = 0; i < x->u.add.nterms; i++) {
    if (addterm_is_integer_valued(bnds, x->u.add.terms[i].coeff,
                                  x->u.add.terms[i].term)) {
      extracted = true;
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

  /* A rational floor can be nonzero even when floor(p/q) * q does not fit
   * int64_t.  In that case the split conservatively keeps the original
   * coefficient.  Do not recursively round the unchanged ADD. */
  if (!extracted) {
    ixs_arena_restore(&ctx->scratch, m);
    return x;
  }

  remainder = rem_coeff;
  for (i = 0; i < nk && remainder; i++)
    remainder =
        simp_add(ctx, remainder, simp_mul(ctx, kept[i].coeff, kept[i].term));
  ixs_arena_restore(&ctx->scratch, m);
  if (!remainder)
    return NULL;
  return simp_add(ctx, int_sum, rnd(ctx, remainder));
}

/* Bounds-aware integer-valued check for a fully constructed node. */
static bool node_is_integer(ixs_bounds *bnds, ixs_node *n) {
  return bnds ? ixs_bounds_is_integer_with_divinfo(bnds, n)
              : ixs_node_is_integer_valued(n);
}

static ixs_node *round_mul_outer(ixs_ctx *ctx, ixs_node *x, int add_idx,
                                 bool *unsupported) {
  uint32_t j;
  ixs_node *outer = x->u.mul.coeff;
  for (j = 0; j < x->u.mul.nfactors && outer; j++) {
    ixs_node *fbase;
    int32_t fexp;
    if ((int)j == add_idx)
      continue;
    fbase = x->u.mul.factors[j].base;
    fexp = x->u.mul.factors[j].exp;
    if (fbase->tag == IXS_MUL && fexp == -1) {
      int64_t cp, cq;
      ixs_node_get_rat(fbase->u.mul.coeff, &cp, &cq);
      if (cq == 1 && cp != 0) {
        uint32_t k;
        outer = simp_div(ctx, outer, make_const(ctx, cp, cq));
        for (k = 0; k < fbase->u.mul.nfactors && outer; k++) {
          outer = apply_inverse_power(ctx, outer, fbase->u.mul.factors[k].base,
                                      fbase->u.mul.factors[k].exp, unsupported);
          if (*unsupported)
            return outer;
        }
        continue;
      }
    }
    outer = apply_pow(ctx, outer, fbase, fexp);
  }
  return outer;
}

static bool round_mul_add_extractable(ixs_ctx *ctx, ixs_bounds *bnds,
                                      ixs_node *outer, ixs_node *add_node) {
  uint32_t j;
  ixs_node *coeff_product = simp_mul(ctx, outer, add_node->u.add.coeff);
  if (coeff_product && node_is_integer(bnds, coeff_product))
    return true;
  for (j = 0; j < add_node->u.add.nterms; j++) {
    ixs_node *tc = add_node->u.add.terms[j].coeff;
    ixs_node *tt = add_node->u.add.terms[j].term;
    ixs_node *product = simp_mul(ctx, outer, simp_mul(ctx, tc, tt));
    if (product && node_is_integer(bnds, product))
      return true;
  }
  {
    int64_t ac_p, ac_q;
    ixs_node_get_rat(add_node->u.add.coeff, &ac_p, &ac_q);
    return ac_p != 0 && !node_is_integer(bnds, outer);
  }
}

static ixs_node *round_mul_add_expand(ixs_ctx *ctx, ixs_node *outer,
                                      ixs_node *add_node) {
  uint32_t j;
  ixs_node *expanded = simp_mul(ctx, outer, add_node->u.add.coeff);
  for (j = 0; j < add_node->u.add.nterms && expanded; j++) {
    ixs_node *tc = add_node->u.add.terms[j].coeff;
    ixs_node *tt = add_node->u.add.terms[j].term;
    expanded =
        simp_add(ctx, expanded, simp_mul(ctx, outer, simp_mul(ctx, tc, tt)));
  }
  return expanded;
}

/*
 * Extract integer-valued terms from round(MUL(..., ADD^1)).
 * Distributes the outer (non-ADD) factors into the ADD, then resumes
 * full floor/ceil simplification (including bounds-aware rules) via
 * simp_floor_bnds / simp_ceil_bnds on the expanded sum.
 *
 * Decomposes compound MUL bases (e.g. (2*K)^-1 -> 1/2 * K^-1) so that
 * symbolic factor cancellation works through simp_mul/simp_div.
 *
 * Returns the simplified node, x unchanged if nothing to extract,
 * or NULL on OOM.
 */
static ixs_node *round_extract_mul_add(ixs_ctx *ctx, ixs_bounds *bnds,
                                       ixs_node *x, bool is_floor) {
  int add_idx;
  ixs_node *add_node;
  ixs_node *outer;
  ixs_node *expanded;
  bool unsupported = false;
  if (x->tag != IXS_MUL)
    return x;

  add_idx = find_pow1_factor(x, IXS_ADD);
  if (add_idx < 0)
    return x;

  add_node = x->u.mul.factors[add_idx].base;
  outer = round_mul_outer(ctx, x, add_idx, &unsupported);
  if (!outer)
    return NULL;
  if (unsupported)
    return x;

  if (!round_mul_add_extractable(ctx, bnds, outer, add_node))
    return x;

  expanded = round_mul_add_expand(ctx, outer, add_node);
  if (!expanded)
    return NULL;
  return is_floor ? simp_floor_bnds(ctx, bnds, expanded)
                  : simp_ceil_bnds(ctx, bnds, expanded);
}

static int64_t floor_term_effective_denom(ixs_bounds *bnds,
                                          const ixs_addterm *term) {
  int64_t tp, tq, atp, eff_num, g;
  ixs_node_get_rat(term->coeff, &tp, &tq);
  if (tq <= 0)
    return 0;
  atp = tp > 0 ? tp : (tp > -INT64_MAX ? -tp : 0);
  eff_num = atp;
  if (bnds && ixs_node_is_integer_valued(term->term)) {
    int64_t sym_mod, sym_rem;
    if (term->term->tag == IXS_SYM &&
        ixs_bounds_get_modrem(bnds, term->term->u.name, &sym_mod, &sym_rem) &&
        sym_rem == 0 && sym_mod > 0) {
      int64_t prod;
      if (ixs_safe_mul(atp, sym_mod, &prod))
        eff_num = prod;
    }
  } else if (!ixs_node_is_integer_valued(term->term)) {
    if (bnds && tq > 1) {
      int64_t g2 = ixs_gcd(atp, tq);
      int64_t denom = tq / g2;
      if (!ixs_bounds_is_known_divisible(bnds, term->term, denom))
        return 0;
      eff_num = tq;
    } else {
      return 0;
    }
  }
  g = ixs_gcd(eff_num, tq);
  return tq / g;
}

static bool floor_update_lcm(int64_t *lcm, int64_t denom) {
  int64_t g;
  if (denom <= 1)
    return true;
  g = ixs_gcd(*lcm, denom);
  if (denom / g > (1LL << 30) / *lcm)
    return false;
  *lcm = *lcm / g * denom;
  return true;
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
static ixs_node *floor_drop_const(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *x) {
  if (x->tag != IXS_ADD || x->u.add.nterms == 0)
    return x;
  int64_t cp, cq;
  ixs_node_get_rat(x->u.add.coeff, &cp, &cq);
  if (cp <= 0 || cq <= 0)
    return x;
  int64_t lcm = 1;
  uint32_t i;
  for (i = 0; i < x->u.add.nterms; i++) {
    int64_t denom = floor_term_effective_denom(bnds, &x->u.add.terms[i]);
    if (denom == 0 || !floor_update_lcm(&lcm, denom))
      return x;
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

static bool interval_nonnegative_below(ixs_interval iv, int64_t p, int64_t q) {
  return iv.valid && !iv.lo_inf && !iv.hi_inf &&
         ixs_rat_cmp(iv.lo_p, iv.lo_q, 0, 1) >= 0 &&
         ixs_rat_cmp(iv.hi_p, iv.hi_q, p, q) < 0;
}

static ixs_node *floor_rebuild_without_term(ixs_ctx *ctx, ixs_node *x,
                                            uint32_t skip) {
  ixs_node *sum = x->u.add.coeff;
  uint32_t i;
  for (i = 0; i < x->u.add.nterms && sum; i++) {
    if (i == skip)
      continue;
    sum = simp_add(
        ctx, sum,
        simp_mul(ctx, x->u.add.terms[i].coeff, x->u.add.terms[i].term));
  }
  return sum;
}

static ixs_node *floor_drop_small_bounded_term(ixs_ctx *ctx, ixs_bounds *bnds,
                                               ixs_node *x) {
  uint32_t drop, i;

  if (!bnds || x->tag != IXS_ADD || x->u.add.nterms < 2 ||
      !ixs_node_is_integer_valued(x->u.add.coeff))
    return x;

  for (drop = 0; drop < x->u.add.nterms; drop++) {
    int64_t lcm = 1;
    ixs_node *candidate;
    ixs_interval iv;

    for (i = 0; i < x->u.add.nterms; i++) {
      int64_t denom;
      if (i == drop)
        continue;
      denom = floor_term_effective_denom(bnds, &x->u.add.terms[i]);
      if (denom == 0 || !floor_update_lcm(&lcm, denom))
        break;
    }
    if (i != x->u.add.nterms)
      continue;

    candidate =
        simp_mul(ctx, x->u.add.terms[drop].coeff, x->u.add.terms[drop].term);
    if (!candidate)
      return NULL;
    iv = ixs_bounds_get(bnds, candidate);
    if (interval_nonnegative_below(iv, 1, lcm))
      return floor_rebuild_without_term(ctx, x, drop);
  }

  return x;
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
 * whenever C == C' (mod gcd(g, L)).
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
      iv = bnds ? ixs_bounds_is_integer_with_divinfo(bnds,
                                                     t->u.mul.factors[k].base)
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
  return try_floor_ceil_collapse(ctx, bnds, n, false);
}

static ixs_node *rule_ceil_collapse(ixs_ctx *ctx, ixs_bounds *bnds,
                                    ixs_node *n) {
  return try_floor_ceil_collapse(ctx, bnds, n, true);
}

static ixs_node *rule_round_integer_divinfo(ixs_ctx *ctx, ixs_bounds *bnds,
                                            ixs_node *n) {
  (void)ctx;
  return ixs_bounds_is_integer_with_divinfo(bnds, n->u.unary.arg)
             ? n->u.unary.arg
             : n;
}

static ixs_node *rule_round_extract_add(ixs_ctx *ctx, ixs_bounds *bnds,
                                        ixs_node *n) {
  round_fn rnd = (n->tag == IXS_FLOOR) ? simp_floor : simp_ceil;
  ixs_node *x = n->u.unary.arg;
  ixs_node *r;
  r = round_extract_add(ctx, bnds, x, rnd);
  if (!r)
    return NULL;
  return (r == x) ? n : r;
}

static ixs_node *rule_round_extract_mul_add(ixs_ctx *ctx, ixs_bounds *bnds,
                                            ixs_node *n) {
  ixs_node *x = n->u.unary.arg;
  ixs_node *r;
  r = round_extract_mul_add(ctx, bnds, x, n->tag == IXS_FLOOR);
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
  r = floor_drop_const(ctx, bnds, x);
  if (!r)
    return NULL;
  if (r == x)
    return n;
  return simp_floor(ctx, r);
}

static ixs_node *rule_floor_drop_small_bounded_term(ixs_ctx *ctx,
                                                    ixs_bounds *bnds,
                                                    ixs_node *n) {
  ixs_node *x = n->u.unary.arg;
  ixs_node *r = floor_drop_small_bounded_term(ctx, bnds, x);
  if (!r)
    return NULL;
  if (r == x)
    return n;
  return simp_floor_bnds(ctx, bnds, r);
}

/* needs_bounds = false: this rule fires on structure alone (symbolic
 * denominator shared across addends) but uses bnds opportunistically
 * to tighten the remainder when available. */
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

/* For non-negative integers, floor division by a power of two is a logical
 * right shift, which distributes over xor.  Keep this as an ordinary
 * simplification rule so every generic facts query sees the same canonical
 * form. */
static ixs_node *rule_floor_shift_xor(ixs_ctx *ctx, ixs_bounds *bnds,
                                      ixs_node *n) {
  ixs_node *x = n->u.unary.arg;
  ixs_node *xor_node;
  ixs_node *divisor;
  ixs_node **shifted;
  ixs_node *result;
  ixs_arena_mark mark;
  int64_t p;
  int64_t q;
  uint32_t i;

  if (!bnds || x->tag != IXS_MUL || x->u.mul.nfactors != 1u ||
      x->u.mul.factors[0].exp != 1 || x->u.mul.factors[0].base->tag != IXS_XOR)
    return n;
  ixs_node_get_rat(x->u.mul.coeff, &p, &q);
  xor_node = x->u.mul.factors[0].base;
  if (p != 1 || q <= 1 || !uint64_pow2((uint64_t)q) ||
      xor_node->u.assoc.nargs == 0 || !xor_node->u.assoc.args)
    return n;
  for (i = 0; i < xor_node->u.assoc.nargs; i++) {
    if (!node_is_integer(bnds, xor_node->u.assoc.args[i]) ||
        !bounds_int_nonnegative_finite(bnds, xor_node->u.assoc.args[i]))
      return n;
  }

  mark = ixs_arena_save(&ctx->scratch);
  shifted =
      ixs_arena_alloc(&ctx->scratch, xor_node->u.assoc.nargs * sizeof(*shifted),
                      sizeof(void *));
  divisor = ixs_node_int(ctx, q);
  if (!shifted || !divisor) {
    ixs_arena_restore(&ctx->scratch, mark);
    return NULL;
  }
  for (i = 0; i < xor_node->u.assoc.nargs; i++) {
    ixs_node *quotient = simp_div(ctx, xor_node->u.assoc.args[i], divisor);
    shifted[i] = quotient ? simp_floor_bnds(ctx, bnds, quotient) : NULL;
    if (!shifted[i]) {
      ixs_arena_restore(&ctx->scratch, mark);
      return NULL;
    }
  }
  result = simp_xor_many_bnds(ctx, bnds, xor_node->u.assoc.nargs, shifted);
  ixs_arena_restore(&ctx->scratch, mark);
  return result;
}

/*
 * round(round(A) / D) -> round(A / D)  for round in {floor, ceiling}
 * when D is a positive integer.
 *
 * Proof (floor): let A = D*q + r + f where q = floor(A/D),
 * 0 <= r < D integer, 0 <= f < 1.  Then floor(A) = D*q + r,
 * floor(floor(A)/D) = q, and floor(A/D) = q  since r+f < D.
 * The ceiling proof is symmetric.
 *
 * Detects MUL nodes where one factor is FLOOR/CEIL^1 and the
 * remaining product is 1/D with D a positive integer.
 * Returns simplified result, n unchanged if the rule doesn't apply,
 * or NULL on OOM.
 */
static ixs_node *round_unwrap_inner(ixs_ctx *ctx, ixs_node *n,
                                    ixs_tag inner_tag, round_fn rnd) {
  ixs_node *x = n->u.unary.arg;
  if (x->tag != IXS_MUL)
    return n;

  int32_t fl_idx = -1;
  uint32_t i;
  for (i = 0; i < x->u.mul.nfactors; i++) {
    if (x->u.mul.factors[i].base->tag == inner_tag &&
        x->u.mul.factors[i].exp == 1) {
      fl_idx = (int32_t)i;
      break;
    }
  }
  if (fl_idx < 0)
    return n;

  /* Build denom D = (1/coeff) * prod(fi^(-ei)) for all non-round factors.
   * D must be a positive integer for the identity to hold. */
  int64_t cp, cq;
  ixs_node_get_rat(x->u.mul.coeff, &cp, &cq);
  if (cp <= 0)
    return n;
  ixs_node *denom = make_const(ctx, cq, cp);
  if (!denom)
    return NULL;
  for (i = 0; i < x->u.mul.nfactors && denom; i++) {
    bool unsupported = false;
    if ((int32_t)i == fl_idx)
      continue;
    denom = apply_inverse_power(ctx, denom, x->u.mul.factors[i].base,
                                x->u.mul.factors[i].exp, &unsupported);
    if (unsupported)
      return n;
  }
  if (!denom)
    return NULL;
  if (!ixs_node_is_integer_valued(denom))
    return n;

  ixs_node *inner_arg = x->u.mul.factors[fl_idx].base->u.unary.arg;
  ixs_node *replaced = simp_div(ctx, inner_arg, denom);
  if (!replaced)
    return NULL;
  return rnd(ctx, replaced);
}

static ixs_node *rule_floor_unwrap_inner(ixs_ctx *ctx, ixs_bounds *bnds,
                                         ixs_node *n) {
  (void)bnds;
  return round_unwrap_inner(ctx, n, IXS_FLOOR, simp_floor);
}

static ixs_node *rule_ceil_unwrap_inner(ixs_ctx *ctx, ixs_bounds *bnds,
                                        ixs_node *n) {
  (void)bnds;
  return round_unwrap_inner(ctx, n, IXS_CEIL, simp_ceil);
}

/* ---- Floor/ceil rule tables -------------------------------------- */
/* Order matters: bounds-dependent collapse first (cheapest), then
 * structural rewrites from most specific to most general.
 * round_extract_add/mul_add peel integer addends before pull_in_denom
 * redistributes; drop_const/drop_const_sym handle the remainder. */

static const ixs_rule floor_rules[] = {
    {rule_floor_collapse, "floor_collapse", true},
    {rule_round_integer_divinfo, "round_integer_divinfo", true},
    {rule_round_extract_add, "round_extract_add", false},
    {rule_round_extract_mul_add, "round_extract_mul_add", false},
    {rule_round_pull_in_denom, "round_pull_in_denom", false},
    {rule_floor_unwrap_inner, "floor_unwrap_inner", false},
    {rule_floor_drop_const, "floor_drop_const", false},
    {rule_floor_drop_small_bounded_term, "floor_drop_small_bounded_term", true},
    {rule_floor_drop_const_sym, "floor_drop_const_sym", false},
    {rule_floor_mod_div_zero, "floor_mod_div_zero", false},
    {rule_floor_shift_xor, "floor_shift_xor", true},
    {NULL, NULL, false},
};

static const ixs_rule ceil_rules[] = {
    {rule_ceil_collapse, "ceil_collapse", true},
    {rule_round_integer_divinfo, "round_integer_divinfo", true},
    {rule_round_extract_add, "round_extract_add", false},
    {rule_round_extract_mul_add, "round_extract_mul_add", false},
    {rule_round_pull_in_denom, "round_pull_in_denom", false},
    {rule_ceil_unwrap_inner, "ceil_unwrap_inner", false},
    {NULL, NULL, false},
};

/* ---- simp_floor / simp_ceil -------------------------------------- */

static ixs_node *simp_floor_bnds(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *x) {
  ixs_node *prop;
  if (!x)
    return NULL;
  prop = ixs_propagate1(x);
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

IXS_STATIC ixs_node *simp_floor(ixs_ctx *ctx, ixs_node *x) {
  return simp_floor_bnds(ctx, NULL, x);
}

static ixs_node *simp_ceil_bnds(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *x) {
  ixs_node *prop;
  if (!x)
    return NULL;
  prop = ixs_propagate1(x);
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

IXS_STATIC ixs_node *simp_ceil(ixs_ctx *ctx, ixs_node *x) {
  return simp_ceil_bnds(ctx, NULL, x);
}

static ixs_node *simp_trunc_bnds(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *x) {
  ixs_node *prop;
  ixs_node *pred;
  if (!x)
    return NULL;
  prop = ixs_propagate1(x);
  if (prop)
    return prop;
  if (x->tag == IXS_INT)
    return x;
  if (x->tag == IXS_RAT)
    return ixs_node_int(ctx, x->u.rat.p / x->u.rat.q);
  if (ixs_node_is_integer_valued(x))
    return x;
  if (bnds) {
    pred = simp_cmp(ctx, x, IXS_CMP_GE, ctx->node_zero);
    if (!pred)
      return NULL;
    if (ixs_bounds_check(bnds, pred) == IXS_CHECK_TRUE)
      return simp_floor_bnds(ctx, bnds, x);
    pred = simp_cmp(ctx, x, IXS_CMP_LE, ctx->node_zero);
    if (!pred)
      return NULL;
    if (ixs_bounds_check(bnds, pred) == IXS_CHECK_TRUE)
      return simp_ceil_bnds(ctx, bnds, x);
  }
  return ixs_node_trunc(ctx, x);
}

IXS_STATIC ixs_node *simp_trunc(ixs_ctx *ctx, ixs_node *x) {
  return simp_trunc_bnds(ctx, NULL, x);
}

/* ------------------------------------------------------------------ */
/*  simp_mod                                                          */
/* ------------------------------------------------------------------ */

/* Mod(c*t, m) -> 0 when all factors are integer-valued and m | c. */
static ixs_node *mod_mul_zero(ixs_ctx *ctx, ixs_node *n) {
  ixs_node *a = n->u.binary.lhs, *b = n->u.binary.rhs;
  if (a->tag != IXS_MUL || b->tag != IXS_INT || b->u.ival <= 0)
    return n;

  int64_t cp, cq;
  uint32_t i;
  ixs_node_get_rat(a->u.mul.coeff, &cp, &cq);
  if (cq != 1 || cp == 0 || cp % b->u.ival != 0)
    return n;

  for (i = 0; i < a->u.mul.nfactors; i++) {
    if (a->u.mul.factors[i].exp < 0 ||
        !ixs_node_is_integer_valued(a->u.mul.factors[i].base))
      return n;
  }
  return ixs_node_int(ctx, 0);
}

static ixs_node *mod_build_integer_reduced(ixs_ctx *ctx, ixs_addterm *reduced,
                                           uint32_t nr, int64_t new_const_p,
                                           int64_t new_const_q) {
  if (nr == 0)
    return make_const(ctx, new_const_p, new_const_q);
  {
    ixs_node *c = make_const(ctx, new_const_p, new_const_q);
    if (!c)
      return NULL;
    if (nr == 1 && ixs_rat_is_zero(new_const_p)) {
      int64_t rcp, rcq;
      ixs_node_get_rat(reduced[0].coeff, &rcp, &rcq);
      if (ixs_rat_is_one(rcp, rcq))
        return reduced[0].term;
      return simp_mul(ctx, make_const(ctx, rcp, rcq), reduced[0].term);
    }
    return ixs_node_add(ctx, c, nr, reduced);
  }
}

static ixs_node *mod_strip_integer_multiples(ixs_ctx *ctx, ixs_node *n,
                                             ixs_node *a, ixs_node *b) {
  int64_t m = b->u.ival;
  int64_t const_p, const_q;
  int64_t new_const_p, new_const_q;
  uint32_t nr = 0;
  uint32_t i;
  bool changed;
  ixs_node *new_a;
  ixs_arena_mark sm = ixs_arena_save(&ctx->scratch);
  ixs_addterm *reduced = ixs_arena_alloc(
      &ctx->scratch, a->u.add.nterms * sizeof(*reduced), sizeof(void *));
  if (!reduced) {
    ixs_arena_restore(&ctx->scratch, sm);
    return NULL;
  }

  ixs_node_get_rat(a->u.add.coeff, &const_p, &const_q);
  new_const_p = const_p;
  new_const_q = const_q;
  if (const_q == 1) {
    new_const_p = const_p % m;
    if (new_const_p < 0)
      new_const_p += m;
  }
  changed = (new_const_p != const_p || new_const_q != const_q);

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
    return n;
  }
  new_a = mod_build_integer_reduced(ctx, reduced, nr, new_const_p, new_const_q);
  ixs_arena_restore(&ctx->scratch, sm);
  return new_a ? simp_mod(ctx, new_a, b) : NULL;
}

static ixs_node *mod_build_symbolic_reduced(ixs_ctx *ctx, ixs_node *a,
                                            ixs_addterm *reduced, uint32_t nr) {
  if (nr == 0)
    return a->u.add.coeff;
  {
    int64_t cp, cq;
    ixs_node_get_rat(a->u.add.coeff, &cp, &cq);
    if (nr == 1 && cq == 1 && cp == 0) {
      int64_t rcp, rcq;
      ixs_node_get_rat(reduced[0].coeff, &rcp, &rcq);
      if (ixs_rat_is_one(rcp, rcq))
        return reduced[0].term;
      return simp_mul(ctx, reduced[0].coeff, reduced[0].term);
    }
    return ixs_node_add(ctx, a->u.add.coeff, nr, reduced);
  }
}

static bool mod_addend_divides(ixs_ctx *ctx, ixs_node *b,
                               const ixs_addterm *term) {
  ixs_node *addend = simp_mul(ctx, term->coeff, term->term);
  ixs_node *quotient = addend ? simp_div(ctx, addend, b) : NULL;
  return quotient && !ixs_node_is_sentinel(quotient) &&
         ixs_node_is_integer_valued(quotient);
}

static ixs_node *mod_strip_symbolic_multiples(ixs_ctx *ctx, ixs_node *n,
                                              ixs_node *a, ixs_node *b) {
  uint32_t nr = 0;
  uint32_t i;
  bool changed = false;
  ixs_node *new_a;
  ixs_arena_mark sm = ixs_arena_save(&ctx->scratch);
  ixs_addterm *reduced = ixs_arena_alloc(
      &ctx->scratch, a->u.add.nterms * sizeof(*reduced), sizeof(void *));
  if (!reduced) {
    ixs_arena_restore(&ctx->scratch, sm);
    return NULL;
  }

  for (i = 0; i < a->u.add.nterms; i++) {
    if (mod_addend_divides(ctx, b, &a->u.add.terms[i])) {
      changed = true;
      continue;
    }
    reduced[nr++] = a->u.add.terms[i];
  }

  if (!changed) {
    ixs_arena_restore(&ctx->scratch, sm);
    return n;
  }
  new_a = mod_build_symbolic_reduced(ctx, a, reduced, nr);
  ixs_arena_restore(&ctx->scratch, sm);
  return new_a ? simp_mod(ctx, new_a, b) : NULL;
}

/* Mod(x + k*m, m) -> Mod(x, m): strip additive multiples of m. */
static ixs_node *mod_strip_multiples(ixs_ctx *ctx, ixs_node *n) {
  ixs_node *a = n->u.binary.lhs, *b = n->u.binary.rhs;
  if (a->tag != IXS_ADD)
    return n;
  if (b->tag == IXS_INT && b->u.ival > 0)
    return mod_strip_integer_multiples(ctx, n, a, b);
  return mod_strip_symbolic_multiples(ctx, n, a, b);
}

static int scale_add_coeff_integer(ixs_ctx *ctx, ixs_node *coeff, int64_t sp,
                                   int64_t sq, ixs_node **scaled) {
  int64_t cp, cq, rp, rq;
  ixs_node_get_rat(coeff, &cp, &cq);
  if (!ixs_rat_mul(cp, cq, sp, sq, &rp, &rq))
    return 0;
  if (rq != 1)
    return 0;
  *scaled = make_const(ctx, rp, rq);
  return *scaled ? 1 : -1;
}

static ixs_node *mod_clear_rational_add_scale_impl(ixs_ctx *ctx, ixs_node *n) {
  ixs_node *a = n->u.binary.lhs;
  ixs_node *add;
  ixs_node *scaled_const;
  ixs_node *scaled_add;
  int64_t sp, sq;
  uint32_t i;
  ixs_addterm *terms;

  if (a->tag != IXS_MUL || a->u.mul.nfactors != 1 ||
      a->u.mul.factors[0].exp != 1 || a->u.mul.factors[0].base->tag != IXS_ADD)
    return n;

  ixs_node_get_rat(a->u.mul.coeff, &sp, &sq);
  if (sq == 1)
    return n;

  add = a->u.mul.factors[0].base;
  terms = ixs_arena_alloc(&ctx->scratch, add->u.add.nterms * sizeof(*terms),
                          sizeof(void *));
  if (!terms && add->u.add.nterms != 0)
    return NULL;

  {
    int rc =
        scale_add_coeff_integer(ctx, add->u.add.coeff, sp, sq, &scaled_const);
    if (rc < 0)
      return NULL;
    if (rc == 0)
      return n;
  }

  for (i = 0; i < add->u.add.nterms; i++) {
    int rc;
    terms[i].term = add->u.add.terms[i].term;
    rc = scale_add_coeff_integer(ctx, add->u.add.terms[i].coeff, sp, sq,
                                 &terms[i].coeff);
    if (rc < 0)
      return NULL;
    if (rc == 0)
      return n;
  }

  scaled_add = ixs_node_add(ctx, scaled_const, add->u.add.nterms, terms);
  return scaled_add ? simp_mod(ctx, scaled_add, n->u.binary.rhs) : NULL;
}

/* Mod((p/q)*(c + sum(ci*ti)), m) -> Mod(c' + sum(ci'*ti), m)
 * when every scaled coefficient is integral. */
static ixs_node *mod_clear_rational_add_scale(ixs_ctx *ctx, ixs_node *n) {
  ixs_arena_mark m = ixs_arena_save(&ctx->scratch);
  ixs_node *result = mod_clear_rational_add_scale_impl(ctx, n);
  ixs_arena_restore(&ctx->scratch, m);
  return result;
}

/* Extract the Euclidean residue of an ADD constant from Mod when every
 * non-constant addend is a multiple of the same grid.  The grid is the gcd
 * of the modulus and all integer term coefficients.
 *
 *   Mod(16 + 4*floor(a) + 3, 16)
 *       -> Mod(16 + 4*floor(a), 16) + 3
 *
 * Proof: write the dividend as B + r, where g divides B and the modulus,
 * and 0 < r < g.  Mod(B, m) is one of 0, g, ..., m-g, so adding r cannot
 * wrap across m. */
static ixs_node *mod_extract_small_const(ixs_ctx *ctx, ixs_node *n) {
  ixs_node *a = n->u.binary.lhs, *b = n->u.binary.rhs;
  if (a->tag != IXS_ADD || b->tag != IXS_INT || b->u.ival <= 0)
    return n;

  int64_t m = b->u.ival;
  int64_t const_p, const_q;
  ixs_node_get_rat(a->u.add.coeff, &const_p, &const_q);

  if (const_q != 1 || a->u.add.nterms == 0)
    return n;

  int64_t g = m;
  int64_t aligned_const;
  int64_t residue;
  bool ok = true;
  uint32_t i;

  for (i = 0; i < a->u.add.nterms; i++) {
    int64_t cp, cq;
    ixs_node_get_rat(a->u.add.terms[i].coeff, &cp, &cq);
    int64_t acp = (cp > 0) ? cp : (cp >= -INT64_MAX) ? -cp : 0;
    if (cq != 1 || acp == 0 ||
        !ixs_node_is_integer_valued(a->u.add.terms[i].term)) {
      ok = false;
      break;
    }
    g = ixs_gcd(g, acp);
  }

  if (!ok || g <= 1)
    return n;
  residue = const_p % g;
  if (residue < 0)
    residue += g;
  if (residue == 0 || !ixs_safe_sub(const_p, residue, &aligned_const))
    return n;

  ixs_node *inner_constant = ixs_node_int(ctx, aligned_const);
  if (!inner_constant)
    return NULL;
  ixs_node *inner =
      ixs_node_add(ctx, inner_constant, a->u.add.nterms, a->u.add.terms);
  if (!inner)
    return NULL;
  ixs_node *moded = simp_mod(ctx, inner, b);
  if (!moded)
    return NULL;
  return simp_add(ctx, moded, ixs_node_int(ctx, residue));
}

/* Leading positive integer coefficient of a MUL node, or 0 if the
 * coefficient is fractional, negative, or the node is not MUL. */
static int64_t mul_int_factor(ixs_node *b) {
  int64_t bp, bq;
  if (b->tag != IXS_MUL)
    return 0;
  ixs_node_get_rat(b->u.mul.coeff, &bp, &bq);
  return (bq == 1 && bp > 0) ? bp : 0;
}

static ixs_node *mod_scale_extract_mul(ixs_ctx *ctx, ixs_node *n, ixs_node *a,
                                       ixs_node *b) {
  int64_t ap, aq;
  int64_t aap;
  int64_t bfactor;
  int64_t g;
  ixs_node *gc;
  ixs_node *new_mod;
  ixs_node *inner;
  ixs_node *moded;

  ixs_node_get_rat(a->u.mul.coeff, &ap, &aq);
  aap = (ap > 0) ? ap : (ap >= -INT64_MAX) ? -ap : 0;
  if (aq != 1 || aap <= 1)
    return n;
  bfactor = mul_int_factor(b);
  if (bfactor == 0)
    return n;
  g = ixs_gcd(aap, bfactor);
  if (g <= 1)
    return n;
  gc = ixs_node_int(ctx, g);
  if (!gc)
    return NULL;
  new_mod = simp_div(ctx, b, gc);
  if (!new_mod || ixs_node_is_sentinel(new_mod))
    return n;
  inner = simp_div(ctx, a, gc);
  if (!inner || ixs_node_is_sentinel(inner))
    return n;
  moded = simp_mod(ctx, inner, new_mod);
  return moded ? simp_mul(ctx, gc, moded) : NULL;
}

static bool mod_scale_add_gcd(ixs_node *a, int64_t bfactor, int64_t *g) {
  uint32_t i;
  *g = bfactor;
  for (i = 0; i < a->u.add.nterms; i++) {
    int64_t cp, cq;
    int64_t acp;
    ixs_node_get_rat(a->u.add.terms[i].coeff, &cp, &cq);
    acp = (cp > 0) ? cp : (cp >= -INT64_MAX) ? -cp : 0;
    if (cq != 1 || acp == 0 ||
        !ixs_node_is_integer_valued(a->u.add.terms[i].term))
      return false;
    *g = ixs_gcd(*g, acp);
    if (*g <= 1)
      return false;
  }
  return true;
}

static ixs_node *mod_scale_add_inner(ixs_ctx *ctx, ixs_node *a, int64_t g) {
  uint32_t i;
  ixs_node *inner;
  if (a->u.add.nterms == 1) {
    int64_t cp, cq;
    int64_t nc;
    ixs_node_get_rat(a->u.add.terms[0].coeff, &cp, &cq);
    nc = cp / g;
    if (nc == 1)
      return a->u.add.terms[0].term;
    return simp_mul(ctx, make_const(ctx, nc, 1), a->u.add.terms[0].term);
  }
  {
    ixs_arena_mark sm = ixs_arena_save(&ctx->scratch);
    ixs_addterm *nt = ixs_arena_alloc(
        &ctx->scratch, a->u.add.nterms * sizeof(*nt), sizeof(void *));
    if (!nt) {
      ixs_arena_restore(&ctx->scratch, sm);
      return NULL;
    }
    for (i = 0; i < a->u.add.nterms; i++) {
      int64_t cp, cq;
      ixs_node_get_rat(a->u.add.terms[i].coeff, &cp, &cq);
      nt[i].coeff = make_const(ctx, cp / g, 1);
      nt[i].term = a->u.add.terms[i].term;
      if (!nt[i].coeff) {
        ixs_arena_restore(&ctx->scratch, sm);
        return NULL;
      }
    }
    {
      ixs_node *zero = ixs_node_int(ctx, 0);
      inner = zero ? ixs_node_add(ctx, zero, a->u.add.nterms, nt) : NULL;
    }
    ixs_arena_restore(&ctx->scratch, sm);
  }
  return inner;
}

static ixs_node *mod_scale_finish(ixs_ctx *ctx, ixs_node *gc, ixs_node *inner,
                                  ixs_node *new_mod, int64_t kp) {
  ixs_node *moded = simp_mod(ctx, inner, new_mod);
  ixs_node *scaled = moded ? simp_mul(ctx, gc, moded) : NULL;
  if (!scaled)
    return NULL;
  if (kp > 0)
    return simp_add(ctx, scaled, ixs_node_int(ctx, kp));
  return scaled;
}

static ixs_node *mod_scale_extract_add(ixs_ctx *ctx, ixs_bounds *bnds,
                                       ixs_node *n, ixs_node *a, ixs_node *b) {
  int64_t bfactor;
  int64_t g;
  int64_t kp, kq;
  ixs_node *gc;
  ixs_node *new_mod;
  ixs_node *inner;

  if (a->tag != IXS_ADD || a->u.add.nterms == 0)
    return n;
  bfactor = mul_int_factor(b);
  if (!mod_scale_add_gcd(a, bfactor, &g))
    return n;
  /* Congruence facts can establish the missing structural factor. */
  if (bfactor == 0 && (!bnds || !ixs_bounds_is_known_divisible(bnds, b, g)))
    return n;

  ixs_node_get_rat(a->u.add.coeff, &kp, &kq);
  if (kq != 1 || kp < 0 || kp >= g)
    return n;

  gc = ixs_node_int(ctx, g);
  if (!gc)
    return NULL;
  new_mod = simp_div(ctx, b, gc);
  if (!new_mod || ixs_node_is_sentinel(new_mod))
    return n;

  if (kp > 0 && !ixs_bounds_is_integer_with_divinfo(bnds, new_mod))
    return n;

  inner = mod_scale_add_inner(ctx, a, g);
  if (!inner)
    return NULL;
  return mod_scale_finish(ctx, gc, inner, new_mod, kp);
}

/* Mod(g*x + r, g*m) -> g*Mod(x, m) + r
 *
 * Factor out gcd(addend coefficients, modulus integer factor).
 * Valid when g > 1, 0 <= r < g, all terms integer-valued.
 * Also handles MUL LHS: Mod(c*x, c*m) -> c*Mod(x, m).
 *
 * Skips integer moduli -- extract_small_const et al. already cover
 * them, and extracting here changes canonical forms that downstream
 * difference-cancellation depends on. */
static ixs_node *mod_scale_extract(ixs_ctx *ctx, ixs_bounds *bnds,
                                   ixs_node *n) {
  ixs_node *a = n->u.binary.lhs, *b = n->u.binary.rhs;

  if (b->tag == IXS_INT)
    return n;
  if (a->tag == IXS_MUL)
    return mod_scale_extract_mul(ctx, n, a, b);
  return mod_scale_extract_add(ctx, bnds, n, a, b);
}

/* ---- Mod rule wrappers ------------------------------------------- */

typedef enum {
  MOD_DOMAIN_VALID_OR_UNKNOWN,
  MOD_DOMAIN_ZERO,
  MOD_DOMAIN_NEGATIVE,
  MOD_DOMAIN_NONPOSITIVE
} mod_domain_status;

static mod_domain_status mod_divisor_domain(ixs_bounds *bnds, ixs_node *b) {
  ixs_mod_divisor_class constant = ixs_node_classify_mod_divisor(b);

  if (constant == IXS_MOD_DIVISOR_ZERO)
    return MOD_DOMAIN_ZERO;
  if (constant == IXS_MOD_DIVISOR_NEGATIVE)
    return MOD_DOMAIN_NEGATIVE;
  if (!bnds || ixs_bounds_has_empty(bnds))
    return MOD_DOMAIN_VALID_OR_UNKNOWN;

  {
    ixs_interval iv = ixs_bounds_get(bnds, b);
    int upper_cmp;

    if (!iv.valid || ixs_interval_is_empty(iv) || iv.hi_inf)
      return MOD_DOMAIN_VALID_OR_UNKNOWN;
    upper_cmp = ixs_rat_cmp(iv.hi_p, iv.hi_q, 0, 1);
    if (upper_cmp < 0)
      return MOD_DOMAIN_NEGATIVE;
    if (upper_cmp > 0)
      return MOD_DOMAIN_VALID_OR_UNKNOWN;
    if (!iv.lo_inf && ixs_rat_cmp(iv.lo_p, iv.lo_q, 0, 1) == 0)
      return MOD_DOMAIN_ZERO;
    return MOD_DOMAIN_NONPOSITIVE;
  }
}

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
    return simp_undefined(ctx, "Mod: divisor is negative");
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
  (void)bnds;
  return mod_mul_zero(ctx, n);
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

/* Mod(c + k*Mod(x, m), m) -> Mod(c + k*x, m) for integer k. */
static ixs_node *rule_mod_flatten_nested(ixs_ctx *ctx, ixs_bounds *bnds,
                                         ixs_node *n) {
  ixs_node *dividend = n->u.binary.lhs;
  ixs_node *denominator = n->u.binary.rhs;
  ixs_arena_mark mark;
  ixs_addterm *terms;
  ixs_node *flattened;
  ixs_node *result;
  uint32_t i;
  bool changed = false;
  (void)bnds;

  if (dividend->tag != IXS_ADD)
    return n;
  mark = ixs_arena_save(&ctx->scratch);
  terms = ixs_arena_alloc(
      &ctx->scratch, dividend->u.add.nterms * sizeof(*terms), sizeof(void *));
  if (!terms && dividend->u.add.nterms != 0) {
    ixs_arena_restore(&ctx->scratch, mark);
    return NULL;
  }
  for (i = 0; i < dividend->u.add.nterms; i++) {
    ixs_node *term = dividend->u.add.terms[i].term;
    int64_t coefficient_p;
    int64_t coefficient_q;
    terms[i] = dividend->u.add.terms[i];
    ixs_node_get_rat(terms[i].coeff, &coefficient_p, &coefficient_q);
    if (coefficient_q == 1 && term->tag == IXS_MOD &&
        term->u.binary.rhs == denominator) {
      terms[i].term = term->u.binary.lhs;
      changed = true;
    }
  }
  if (!changed) {
    ixs_arena_restore(&ctx->scratch, mark);
    return n;
  }
  flattened =
      ixs_node_add(ctx, dividend->u.add.coeff, dividend->u.add.nterms, terms);
  result = flattened ? simp_mod(ctx, flattened, denominator) : NULL;
  ixs_arena_restore(&ctx->scratch, mark);
  return result;
}

static ixs_node *rule_mod_strip_multiples(ixs_ctx *ctx, ixs_bounds *bnds,
                                          ixs_node *n) {
  (void)bnds;
  return mod_strip_multiples(ctx, n);
}

static ixs_node *
rule_mod_clear_rational_add_scale(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *n) {
  (void)bnds;
  return mod_clear_rational_add_scale(ctx, n);
}

static ixs_node *rule_mod_extract_small_const(ixs_ctx *ctx, ixs_bounds *bnds,
                                              ixs_node *n) {
  (void)bnds;
  return mod_extract_small_const(ctx, n);
}

static ixs_node *rule_mod_scale_extract(ixs_ctx *ctx, ixs_bounds *bnds,
                                        ixs_node *n) {
  return mod_scale_extract(ctx, bnds, n);
}

static ixs_node *rule_mod_bounds_elim(ixs_ctx *ctx, ixs_bounds *bnds,
                                      ixs_node *n) {
  return mod_bounds_elim(ctx, bnds, n);
}

/* Constant folds and identity first, then structural, bounds last.
 * scale_extract skips IXS_INT moduli to preserve canonical forms that
 * strip_multiples and difference-cancellation in simp_add depend on. */
static const ixs_rule mod_rules[] = {
    {rule_mod_const_fold, "mod_const_fold", false},
    {rule_mod_one, "mod_one", false},
    {rule_mod_mul_zero, "mod_mul_zero", false},
    {rule_mod_idempotent, "mod_idempotent", false},
    {rule_mod_flatten_nested, "mod_flatten_nested", false},
    {rule_mod_clear_rational_add_scale, "mod_clear_rational_add_scale", false},
    {rule_mod_strip_multiples, "mod_strip_multiples", false},
    {rule_mod_extract_small_const, "mod_extract_small_const", false},
    {rule_mod_scale_extract, "mod_scale_extract", true},
    {rule_mod_bounds_elim, "mod_bounds_elim", true},
    {NULL, NULL, false},
};

static ixs_node *simp_mod_bnds(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *a,
                               ixs_node *b) {
  mod_domain_status domain;
  ixs_node *node;
  if (!a || !b)
    return NULL;
  {
    ixs_node *prop = ixs_propagate2(a, b);
    if (prop)
      return prop;
  }
  domain = mod_divisor_domain(bnds, b);
  if (domain == MOD_DOMAIN_ZERO)
    return simp_undefined(ctx, "Mod: divisor is zero");
  if (domain == MOD_DOMAIN_NEGATIVE)
    return simp_undefined(ctx, "Mod: divisor is negative");
  if (domain == MOD_DOMAIN_NONPOSITIVE)
    return simp_undefined(ctx,
                          "Mod: divisor is not positive under assumptions");
  node = ixs_node_binary(ctx, IXS_MOD, a, b, (ixs_cmp_op)0);
  if (!node)
    return NULL;
  return try_rules(ctx, bnds, node, mod_rules);
}

IXS_STATIC ixs_node *simp_mod(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  return simp_mod_bnds(ctx, NULL, a, b);
}

/* ------------------------------------------------------------------ */
/*  simp_max / simp_min                                               */
/* ------------------------------------------------------------------ */

typedef struct {
  ixs_node **items;
  size_t count;
  size_t cap;
} assoc_vec;

static bool assoc_vec_push(ixs_ctx *ctx, assoc_vec *vec, ixs_node *node) {
  if (vec->count == vec->cap) {
    vec->items =
        scratch_grow(&ctx->scratch, vec->items, &vec->cap, sizeof(*vec->items));
    if (!vec->items)
      return false;
  }
  vec->items[vec->count++] = node;
  return true;
}

/* Check the entire public input before reducing so propagation is independent
 * of operand order. */
static bool assoc_inputs_clean(uint32_t n, ixs_node *const *args,
                               ixs_node **propagated) {
  uint32_t i;
  ixs_node *domain_error = NULL;
  ixs_node *parse_error = NULL;

  *propagated = NULL;
  if (n != 0 && !args)
    return false;
  for (i = 0; i < n; i++) {
    if (!args[i])
      return false;
    if (args[i]->tag == IXS_PARSE_ERROR)
      parse_error = args[i];
    else if (args[i]->tag == IXS_ERROR)
      domain_error = args[i];
  }
  if (parse_error || domain_error) {
    *propagated = parse_error ? parse_error : domain_error;
    return false;
  }
  return true;
}

/* Same-tag children are already flat, but the explicit stack also handles
 * unpublished raw probes without adding recursive depth. */
static bool assoc_collect(ixs_ctx *ctx, ixs_tag tag, uint32_t n,
                          ixs_node *const *args, assoc_vec *out) {
  assoc_vec stack;
  uint32_t i;

  stack.cap = n > 4u ? n : 4u;
  if (stack.cap > (size_t)-1 / sizeof(*stack.items))
    return false;
  stack.count = 0;
  stack.items = ixs_arena_alloc(&ctx->scratch, stack.cap * sizeof(*stack.items),
                                sizeof(void *));
  out->cap = stack.cap;
  out->count = 0;
  out->items = ixs_arena_alloc(&ctx->scratch, out->cap * sizeof(*out->items),
                               sizeof(void *));
  if (!stack.items || !out->items)
    return false;
  for (i = n; i != 0; i--) {
    if (!assoc_vec_push(ctx, &stack, args[i - 1u]))
      return false;
  }
  while (stack.count != 0) {
    ixs_node *node = stack.items[--stack.count];
    if (node->tag == tag) {
      for (i = node->u.assoc.nargs; i != 0; i--) {
        if (!assoc_vec_push(ctx, &stack, node->u.assoc.args[i - 1u]))
          return false;
      }
    } else if (!assoc_vec_push(ctx, out, node)) {
      return false;
    }
  }
  return out->count <= UINT32_MAX;
}

static bool node_is_known_total_integer(const ixs_node *node) {
  return ixs_node_is_integer_valued(node) && ixs_node_is_known_total(node);
}

static bool node_is_proven_defined(ixs_bounds *bnds, const ixs_node *node) {
  return ixs_node_is_known_total(node) ||
         (bnds && ixs_bounds_check_defined(bnds, node) == IXS_CHECK_TRUE);
}

static int64_t bit_pattern_to_i64(uint64_t bits) {
  uint64_t magnitude;
  if (bits <= (uint64_t)INT64_MAX)
    return (int64_t)bits;
  magnitude = (~bits) + UINT64_C(1);
  if (magnitude == (UINT64_C(1) << 63))
    return INT64_MIN;
  return -(int64_t)magnitude;
}

static int64_t bit_fold(ixs_tag tag, int64_t lhs, int64_t rhs) {
  uint64_t a = (uint64_t)lhs;
  uint64_t b = (uint64_t)rhs;
  uint64_t result;
  if (tag == IXS_AND)
    result = a & b;
  else if (tag == IXS_OR)
    result = a | b;
  else
    result = a ^ b;
  return bit_pattern_to_i64(result);
}

static int interval_upper_cmp(const ixs_interval *a, const ixs_interval *b) {
  if (a->hi_inf)
    return b->hi_inf ? 0 : 1;
  if (b->hi_inf)
    return -1;
  return ixs_rat_cmp(a->hi_p, a->hi_q, b->hi_p, b->hi_q);
}

static int interval_lower_cmp(const ixs_interval *a, const ixs_interval *b) {
  if (a->lo_inf)
    return b->lo_inf ? 0 : -1;
  if (b->lo_inf)
    return 1;
  return ixs_rat_cmp(a->lo_p, a->lo_q, b->lo_p, b->lo_q);
}

typedef struct {
  ixs_interval first_iv;
  ixs_interval second_iv;
  uint32_t first;
  uint32_t second;
} extrema_rank;

static bool extrema_endpoint_better(ixs_tag tag, const ixs_interval *candidate,
                                    const ixs_interval *current) {
  int cmp = tag == IXS_MAX ? interval_upper_cmp(candidate, current)
                           : interval_lower_cmp(candidate, current);
  return tag == IXS_MAX ? cmp > 0 : cmp < 0;
}

static void extrema_rank_add(extrema_rank *rank, ixs_tag tag, uint32_t index,
                             ixs_interval iv, uint32_t end) {
  if (rank->first == end) {
    rank->first = index;
    rank->first_iv = iv;
    return;
  }
  if (extrema_endpoint_better(tag, &iv, &rank->first_iv)) {
    rank->second = rank->first;
    rank->second_iv = rank->first_iv;
    rank->first = index;
    rank->first_iv = iv;
    return;
  }
  if (rank->second == end ||
      extrema_endpoint_better(tag, &iv, &rank->second_iv)) {
    rank->second = index;
    rank->second_iv = iv;
  }
}

static bool extrema_candidate_wins(ixs_tag tag, const ixs_interval *candidate,
                                   const ixs_interval *other) {
  if (tag == IXS_MAX)
    return !candidate->lo_inf && !other->hi_inf &&
           ixs_rat_cmp(candidate->lo_p, candidate->lo_q, other->hi_p,
                       other->hi_q) >= 0;
  return !candidate->hi_inf && !other->lo_inf &&
         ixs_rat_cmp(candidate->hi_p, candidate->hi_q, other->lo_p,
                     other->lo_q) <= 0;
}

static ixs_node *assoc_extrema_bounds_winner(ixs_bounds *bnds, ixs_tag tag,
                                             ixs_node **args, uint32_t n) {
  extrema_rank rank;
  uint32_t i;

  if (!bnds)
    return NULL;
  rank.first_iv = ixs_interval_unknown();
  rank.second_iv = ixs_interval_unknown();
  rank.first = n;
  rank.second = n;
  for (i = 0; i < n; i++) {
    ixs_interval iv = ixs_bounds_get(bnds, args[i]);
    if (!iv.valid || ixs_interval_is_empty(iv) ||
        !node_is_proven_defined(bnds, args[i]))
      return NULL;
    extrema_rank_add(&rank, tag, i, iv, n);
  }
  if (rank.second == n)
    return args[0];
  for (i = 0; i < n; i++) {
    ixs_interval candidate = ixs_bounds_get(bnds, args[i]);
    const ixs_interval *other =
        i == rank.first ? &rank.second_iv : &rank.first_iv;
    if (extrema_candidate_wins(tag, &candidate, other))
      return args[i];
  }
  return NULL;
}

static ixs_node *simp_extrema_many_bnds(ixs_ctx *ctx, ixs_bounds *bnds,
                                        ixs_tag tag, uint32_t n,
                                        ixs_node *const *args) {
  ixs_arena_mark mark;
  ixs_node *propagated;
  ixs_node *best = NULL;
  ixs_node *result;
  assoc_vec flat;
  size_t read;
  uint32_t write;

  if (!assoc_inputs_clean(n, args, &propagated))
    return propagated;
  if (n == 0)
    return simp_err(ctx, tag == IXS_MAX ? "Max: expected an operand"
                                        : "Min: expected an operand");
  mark = ixs_arena_save(&ctx->scratch);
  if (!assoc_collect(ctx, tag, n, args, &flat)) {
    ixs_arena_restore(&ctx->scratch, mark);
    return NULL;
  }
  write = 0;
  for (read = 0; read < flat.count; read++) {
    ixs_node *arg = flat.items[read];
    if (ixs_node_is_const(arg)) {
      if (!best) {
        best = arg;
      } else {
        int64_t ap, aq, bp, bq;
        int cmp;
        ixs_node_get_rat(best, &ap, &aq);
        ixs_node_get_rat(arg, &bp, &bq);
        cmp = ixs_rat_cmp(ap, aq, bp, bq);
        if ((tag == IXS_MAX && cmp < 0) || (tag == IXS_MIN && cmp > 0))
          best = arg;
      }
    } else {
      flat.items[write++] = arg;
    }
  }
  if (best)
    flat.items[write++] = best;
  if (write == 0) {
    ixs_arena_restore(&ctx->scratch, mark);
    return simp_err(ctx, tag == IXS_MAX ? "Max: expected an operand"
                                        : "Min: expected an operand");
  }
  if (!node_key_sort(ctx, flat.items, write, sizeof(*flat.items),
                     node_ptr_sort_key)) {
    ixs_arena_restore(&ctx->scratch, mark);
    return NULL;
  }
  {
    uint32_t unique = 0;
    uint32_t i;
    for (i = 0; i < write; i++) {
      if (unique == 0 || flat.items[i] != flat.items[unique - 1u])
        flat.items[unique++] = flat.items[i];
    }
    write = unique;
  }
  result = write == 1u
               ? flat.items[0]
               : assoc_extrema_bounds_winner(bnds, tag, flat.items, write);
  if (!result)
    result = ixs_node_assoc(ctx, tag, write, flat.items);
  ixs_arena_restore(&ctx->scratch, mark);
  return result;
}

IXS_STATIC ixs_node *simp_max_many(ixs_ctx *ctx, uint32_t n,
                                   ixs_node *const *args) {
  return simp_extrema_many_bnds(ctx, NULL, IXS_MAX, n, args);
}

IXS_STATIC ixs_node *simp_min_many(ixs_ctx *ctx, uint32_t n,
                                   ixs_node *const *args) {
  return simp_extrema_many_bnds(ctx, NULL, IXS_MIN, n, args);
}

IXS_STATIC ixs_node *simp_max(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  ixs_node *args[2] = {a, b};
  return simp_max_many(ctx, 2, args);
}

IXS_STATIC ixs_node *simp_min(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  ixs_node *args[2] = {a, b};
  return simp_min_many(ctx, 2, args);
}

/* ------------------------------------------------------------------ */
/*  simp_xor                                                          */
/* ------------------------------------------------------------------ */

static bool xor_partition_constants(ixs_ctx *ctx, assoc_vec *flat,
                                    int64_t *constant, uint32_t *write,
                                    ixs_node **failure) {
  size_t read;

  *constant = 0;
  *write = 0;
  *failure = NULL;
  for (read = 0; read < flat->count; read++) {
    ixs_node *arg = flat->items[read];
    if (arg->tag == IXS_RAT && arg->u.rat.q != 1) {
      *failure = simp_undefined(ctx, "xor: operand is not integer-valued");
      return false;
    }
    if (arg->tag == IXS_INT)
      *constant = bit_fold(IXS_XOR, *constant, arg->u.ival);
    else
      flat->items[(*write)++] = arg;
  }
  return true;
}

static uint32_t xor_cancel_pairs(ixs_node **items, uint32_t count) {
  uint32_t out = 0;
  uint32_t begin = 0;

  while (begin < count) {
    uint32_t end = begin + 1u;
    while (end < count && items[end] == items[begin])
      end++;
    if (((end - begin) & 1u) != 0) {
      items[out++] = items[begin];
    } else if (!node_is_known_total_integer(items[begin])) {
      items[out++] = items[begin];
      items[out++] = items[begin];
    }
    begin = end;
  }
  return out;
}

static ixs_node *xor_build_result(ixs_ctx *ctx, ixs_node **items,
                                  uint32_t count, int64_t constant) {
  if (constant != 0) {
    ixs_node *constant_node = ixs_node_int(ctx, constant);
    if (!constant_node)
      return NULL;
    items[count++] = constant_node;
  }
  if (count == 0)
    return ctx->node_zero;
  if (count == 1u && ixs_node_is_integer_valued(items[0]))
    return items[0];
  if (count == 1u)
    items[count++] = ctx->node_zero;
  if (!node_key_sort(ctx, items, count, sizeof(*items), node_ptr_sort_key))
    return NULL;
  return ixs_node_assoc(ctx, IXS_XOR, count, items);
}

static ixs_node *xor_disjoint_bits_sum(ixs_ctx *ctx, ixs_bounds *bnds,
                                       ixs_node *result) {
  ixs_node *xor_node = result;
  uint64_t possible_bits = 0;
  uint32_t i;

  if (!bnds || result->tag != IXS_XOR)
    return result;
  for (i = 0; i < xor_node->u.assoc.nargs; i++) {
    ixs_bitfacts facts;
    ixs_node *arg = xor_node->u.assoc.args[i];
    uint64_t possible;
    if (!bounds_int_nonnegative_finite(bnds, arg) ||
        !node_is_proven_defined(bnds, arg) ||
        !ixs_bounds_get_bitfacts(bnds, arg, &facts))
      return result;
    possible = ~facts.known_zero;
    if ((possible_bits & possible) != 0)
      return result;
    possible_bits |= possible;
  }
  result = ctx->node_zero;
  for (i = 0; result && i < xor_node->u.assoc.nargs; i++)
    result = simp_add(ctx, result, xor_node->u.assoc.args[i]);
  return result;
}

static ixs_node *simp_xor_many_bnds(ixs_ctx *ctx, ixs_bounds *bnds, uint32_t n,
                                    ixs_node *const *args) {
  ixs_arena_mark mark;
  ixs_node *failure;
  ixs_node *propagated;
  ixs_node *result;
  assoc_vec flat;
  int64_t constant;
  uint32_t write;

  if (!assoc_inputs_clean(n, args, &propagated))
    return propagated;
  if (n == 0)
    return ctx->node_zero;
  mark = ixs_arena_save(&ctx->scratch);
  if (!assoc_collect(ctx, IXS_XOR, n, args, &flat)) {
    ixs_arena_restore(&ctx->scratch, mark);
    return NULL;
  }
  if (!xor_partition_constants(ctx, &flat, &constant, &write, &failure)) {
    ixs_arena_restore(&ctx->scratch, mark);
    return failure;
  }
  if (!node_key_sort(ctx, flat.items, write, sizeof(*flat.items),
                     node_ptr_sort_key)) {
    ixs_arena_restore(&ctx->scratch, mark);
    return NULL;
  }
  write = xor_cancel_pairs(flat.items, write);
  result = xor_build_result(ctx, flat.items, write, constant);
  if (result)
    result = xor_disjoint_bits_sum(ctx, bnds, result);
  ixs_arena_restore(&ctx->scratch, mark);
  return result;
}

IXS_STATIC ixs_node *simp_xor_many(ixs_ctx *ctx, uint32_t n,
                                   ixs_node *const *args) {
  return simp_xor_many_bnds(ctx, NULL, n, args);
}

IXS_STATIC ixs_node *simp_xor(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  ixs_node *args[2] = {a, b};
  return simp_xor_many(ctx, 2, args);
}

static bool bounds_int_nonnegative_finite(ixs_bounds *bnds, ixs_node *expr) {
  ixs_interval iv;
  if (!bnds || !expr || !ixs_node_is_integer_valued(expr))
    return false;
  iv = ixs_bounds_get(bnds, expr);
  if (!iv.valid || iv.lo_inf || iv.hi_inf || iv.hi_q != 1 || iv.hi_p < 0)
    return false;
  return ixs_rat_cmp(iv.lo_p, iv.lo_q, 0, 1) >= 0;
}

/* ------------------------------------------------------------------ */
/*  simp_cmp                                                          */
/* ------------------------------------------------------------------ */

/* Normalize: (a op b) -> ((a - b) op 0) so all comparisons have zero RHS.
 * simp_cmp_bnds has already propagated sentinel operands.  A sentinel created
 * here therefore means only that the exact rational difference is not
 * representable; retain the valid input comparison and its prior diagnostics.
 * Allocation failure remains NULL. */
static ixs_node *cmp_normalize_to_zero(ixs_ctx *ctx, ixs_node *n) {
  ixs_node *a = n->u.binary.lhs, *b = n->u.binary.rhs;
  ixs_arena_mark diag_mark;
  const char **saved_errors;
  size_t saved_nerrors;
  size_t saved_errors_cap;
  ixs_node *diff;
  if (ixs_node_is_zero(b))
    return n;
  diag_mark = ixs_arena_save(&ctx->diag);
  saved_errors = ctx->errors;
  saved_nerrors = ctx->nerrors;
  saved_errors_cap = ctx->errors_cap;
  diff = simp_sub(ctx, a, b);
  if (!diff)
    return diff;
  if (ixs_node_is_sentinel(diff)) {
    ixs_arena_restore(&ctx->diag, diag_mark);
    ctx->errors = saved_errors;
    ctx->nerrors = saved_nerrors;
    ctx->errors_cap = saved_errors_cap;
    return n;
  }
  return simp_cmp(ctx, diff, n->u.binary.cmp_op, ixs_node_int(ctx, 0));
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

/* A total scalar two-arm carrier with one zero arm represents the truth value
 * of its first-match predicate.  Keep this distinct from boolean Piecewise
 * canonicalization: the Piecewise remains scalar until it is explicitly
 * compared with zero. */
static ixs_node *rule_cmp_piecewise_zero_carrier(ixs_ctx *ctx, ixs_bounds *bnds,
                                                 ixs_node *n) {
  ixs_node *piecewise;
  ixs_node *condition;
  ixs_node *first;
  ixs_node *fallback;
  ixs_node *truth;
  int64_t p;
  int64_t q;
  bool first_nonzero;
  (void)bnds;
  if ((n->u.binary.cmp_op != IXS_CMP_EQ && n->u.binary.cmp_op != IXS_CMP_NE))
    return n;
  if (ixs_node_is_zero(n->u.binary.rhs))
    piecewise = n->u.binary.lhs;
  else if (ixs_node_is_zero(n->u.binary.lhs))
    piecewise = n->u.binary.rhs;
  else
    return n;
  if (piecewise->tag != IXS_PIECEWISE || piecewise->u.pw.ncases != 2u ||
      !piecewise->u.pw.cases ||
      !ixs_node_is_known_true(piecewise->u.pw.cases[1].cond))
    return n;
  condition = piecewise->u.pw.cases[0].cond;
  first = piecewise->u.pw.cases[0].value;
  fallback = piecewise->u.pw.cases[1].value;
  if (!condition || !ixs_node_is_bool_valued(condition) || !first || !fallback)
    return n;
  if (ixs_node_is_zero(first) && ixs_node_is_const(fallback)) {
    ixs_node_get_rat(fallback, &p, &q);
    if (p == 0 || q <= 0)
      return n;
    first_nonzero = false;
  } else if (ixs_node_is_zero(fallback) && ixs_node_is_const(first)) {
    ixs_node_get_rat(first, &p, &q);
    if (p == 0 || q <= 0)
      return n;
    first_nonzero = true;
  } else {
    return n;
  }
  truth = first_nonzero ? condition : simp_not(ctx, condition);
  if (!truth)
    return NULL;
  return n->u.binary.cmp_op == IXS_CMP_NE ? truth : simp_not(ctx, truth);
}

static ixs_node *rule_cmp_bool_zero(ixs_ctx *ctx, ixs_bounds *bnds,
                                    ixs_node *n) {
  ixs_node *lhs = n->u.binary.lhs;
  (void)bnds;
  if (!ixs_node_is_zero(n->u.binary.rhs) || !ixs_node_is_bool_valued(lhs))
    return n;
  if (n->u.binary.cmp_op == IXS_CMP_NE)
    return lhs;
  if (n->u.binary.cmp_op == IXS_CMP_EQ)
    return simp_not(ctx, lhs);
  return n;
}

static ixs_node *rule_cmp_identity(ixs_ctx *ctx, ixs_bounds *bnds,
                                   ixs_node *n) {
  if (n->u.binary.lhs != n->u.binary.rhs)
    return n;
  if (!node_is_proven_defined(bnds, n)) {
    return n;
  }
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
  if (ixs_node_is_zero(n->u.binary.rhs))
    return n;
  if (!node_is_proven_defined(bnds, n)) {
    return n;
  }
  return cmp_normalize_to_zero(ctx, n);
}

static ixs_node *rule_cmp_bounds_resolve(ixs_ctx *ctx, ixs_bounds *bnds,
                                         ixs_node *n) {
  return cmp_bounds_resolve(ctx, bnds, n);
}

/* Normalize before bounds: canonicalize to `expr CMP 0` so bounds
 * resolution sees a consistent form. */
static const ixs_rule cmp_rules[] = {
    {rule_cmp_const_fold, "cmp_const_fold", false},
    {rule_cmp_piecewise_zero_carrier, "cmp_piecewise_zero_carrier", false},
    {rule_cmp_bool_zero, "cmp_bool_zero", false},
    {rule_cmp_identity, "cmp_identity", false},
    {rule_cmp_normalize, "cmp_normalize", false},
    {rule_cmp_bounds_resolve, "cmp_bounds_resolve", true},
    {NULL, NULL, false},
};

/* Ad-hoc transforms tracked via IXS_STAT_HIT (not in rule tables). */
static const char *extra_transforms[] = {
    "recognize_mod",
    "cancel_floor_mod_pairs",
    "cancel_congruent_mod_difference",
    "cancel_equal_floor_difference",
    "cancel_scaled_mod_quotient",
    "simp_normalize_rational_carrier",
    "not_cmp_flip",
};

static const ixs_rule *const all_rule_tables[] = {
    floor_rules,
    ceil_rules,
    mod_rules,
    cmp_rules,
};

#define RULE_NAME_CAP 128 /* must be >= IXS_STATS_CAP */

static size_t collect_unique_names(const char **out, size_t cap) {
  size_t n = 0, t, i, j;
  for (t = 0; t < sizeof(all_rule_tables) / sizeof(all_rule_tables[0]); t++) {
    for (i = 0; all_rule_tables[t][i].fn; i++) {
      const char *name = all_rule_tables[t][i].name;
      bool dup = false;
      for (j = 0; j < n; j++) {
        if (strcmp(out[j], name) == 0) {
          dup = true;
          break;
        }
      }
      if (!dup && n < cap)
        out[n++] = name;
    }
  }
  for (i = 0; i < sizeof(extra_transforms) / sizeof(extra_transforms[0]); i++) {
    const char *name = extra_transforms[i];
    bool dup = false;
    for (j = 0; j < n; j++) {
      if (strcmp(out[j], name) == 0) {
        dup = true;
        break;
      }
    }
    if (!dup && n < cap)
      out[n++] = name;
  }
  return n;
}

size_t ixs_nrules(void) {
  const char *names[RULE_NAME_CAP];
  return collect_unique_names(names, RULE_NAME_CAP);
}

const char *ixs_rule_name(size_t index) {
  const char *names[RULE_NAME_CAP];
  size_t n = collect_unique_names(names, RULE_NAME_CAP);
  return index < n ? names[index] : NULL;
}

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

IXS_STATIC ixs_node *simp_cmp(ixs_ctx *ctx, ixs_node *a, ixs_cmp_op op,
                              ixs_node *b) {
  return simp_cmp_bnds(ctx, NULL, a, op, b);
}

/* ------------------------------------------------------------------ */
/*  simp_and / simp_or / simp_not                                     */
/* ------------------------------------------------------------------ */

static ixs_cmp_op cmp_flip_op(ixs_cmp_op op) {
  switch (op) {
  case IXS_CMP_GT:
    return IXS_CMP_LE;
  case IXS_CMP_GE:
    return IXS_CMP_LT;
  case IXS_CMP_LT:
    return IXS_CMP_GE;
  case IXS_CMP_LE:
    return IXS_CMP_GT;
  case IXS_CMP_EQ:
    return IXS_CMP_NE;
  case IXS_CMP_NE:
    return IXS_CMP_EQ;
  default:
    return op;
  }
}

/* ~(a > b) -> a <= b, etc.  Returns NULL if a is not a CMP node. */
static ixs_node *not_cmp_flip(ixs_ctx *ctx, ixs_node *a) {
  if (a->tag != IXS_CMP)
    return NULL;
  IXS_STAT_HIT(ctx);
  return ixs_node_binary(ctx, IXS_CMP, a->u.binary.lhs, a->u.binary.rhs,
                         cmp_flip_op(a->u.binary.cmp_op));
}

IXS_STATIC ixs_node *simp_not(ixs_ctx *ctx, ixs_node *a) {
  ixs_node *r;
  ixs_node *prop;
  if (!a)
    return NULL;
  prop = ixs_propagate1(a);
  if (prop)
    return prop;

  if (ixs_node_is_known_false(a))
    return ctx->node_true;
  if (ixs_node_is_known_true(a))
    return ctx->node_false;

  if (a->tag == IXS_NOT) {
    ixs_node *child = a->u.unary_bool.arg;
    if (ixs_node_is_bool_valued(child))
      return child;
    return simp_cmp(ctx, child, IXS_CMP_NE, ctx->node_zero);
  }

  r = not_cmp_flip(ctx, a);
  if (r)
    return r;

  return ixs_node_not(ctx, a);
}

static int assoc_contains(ixs_ctx *ctx, ixs_node *const *args, uint32_t n,
                          const ixs_node *target) {
  uint32_t lo = 0;
  uint32_t hi = n;
  while (lo < hi) {
    uint32_t mid = lo + (hi - lo) / 2u;
    int cmp = ixs_node_cmp(ctx, args[mid], target);
    if (cmp == IXS_NODE_CMP_OOM)
      return -1;
    if (cmp < 0)
      lo = mid + 1u;
    else
      hi = mid;
  }
  if (lo < n) {
    int cmp = ixs_node_cmp(ctx, args[lo], target);
    if (cmp == IXS_NODE_CMP_OOM)
      return -1;
    return cmp == 0;
  }
  return 0;
}

static int assoc_has_bool_complement(ixs_ctx *ctx, ixs_node *const *args,
                                     uint32_t n, ixs_node *arg) {
  if (arg->tag == IXS_NOT && ixs_node_is_bool_valued(arg->u.unary_bool.arg))
    return assoc_contains(ctx, args, n, arg->u.unary_bool.arg);
  if (arg->tag == IXS_CMP) {
    struct ixs_node_impl probe;
    memset(&probe, 0, sizeof(probe));
    probe.tag = IXS_CMP;
    probe.u.binary.lhs = arg->u.binary.lhs;
    probe.u.binary.rhs = arg->u.binary.rhs;
    probe.u.binary.cmp_op = cmp_flip_op(arg->u.binary.cmp_op);
    return assoc_contains(ctx, args, n, &probe);
  }
  if (ixs_node_is_bool_valued(arg)) {
    struct ixs_node_impl probe;
    memset(&probe, 0, sizeof(probe));
    probe.tag = IXS_NOT;
    probe.u.unary_bool.arg = arg;
    return assoc_contains(ctx, args, n, &probe);
  }
  return false;
}

static bool logic_sorted_prefix(ixs_tag tag, uint32_t n,
                                ixs_node *const *args) {
  return n == 2u && args && args[0] && args[1] && args[0]->tag == tag &&
         args[1]->tag != tag;
}

static bool logic_partition_constants(ixs_ctx *ctx, ixs_tag tag,
                                      assoc_vec *flat, uint32_t *write,
                                      int64_t *constant, bool *have_constant,
                                      ixs_node **failure) {
  size_t read;

  *write = 0;
  *constant = tag == IXS_AND ? -1 : 0;
  *have_constant = false;
  *failure = NULL;
  for (read = 0; read < flat->count; read++) {
    ixs_node *arg = flat->items[read];
    int64_t value;
    if (arg->tag == IXS_RAT && arg->u.rat.q != 1) {
      *failure = simp_undefined(ctx, tag == IXS_AND
                                         ? "and: operand is not integer-valued"
                                         : "or: operand is not integer-valued");
      return false;
    }
    if (arg->tag != IXS_INT && arg->tag != IXS_RAT) {
      flat->items[(*write)++] = arg;
      continue;
    }
    value = arg->tag == IXS_INT ? arg->u.ival : arg->u.rat.p;
    *constant = bit_fold(tag, *constant, value);
    *have_constant = true;
  }
  return true;
}

static bool logic_sort_unique(ixs_ctx *ctx, ixs_node **items, uint32_t *count,
                              bool sorted_prefix) {
  uint32_t read;
  uint32_t unique = 0;
  bool sorted = sorted_prefix
                    ? node_ptr_insert_last(ctx, items, *count)
                    : node_key_sort(ctx, items, *count, sizeof(*items),
                                    node_ptr_sort_key);

  if (!sorted)
    return false;
  for (read = 0; read < *count; read++) {
    if (unique == 0 || items[read] != items[unique - 1u])
      items[unique++] = items[read];
  }
  *count = unique;
  return true;
}

static int logic_has_reducible_complement(ixs_ctx *ctx, ixs_node **items,
                                          uint32_t count, bool sorted_prefix,
                                          ixs_node *appended) {
  uint32_t i;

  if (sorted_prefix) {
    int complement;
    if (appended->tag == IXS_INT || appended->tag == IXS_RAT)
      return 0;
    complement = assoc_has_bool_complement(ctx, items, count, appended);
    if (complement <= 0)
      return complement;
    return node_is_known_total_integer(appended) ? 1 : 0;
  }
  for (i = 0; i < count; i++) {
    int complement = assoc_has_bool_complement(ctx, items, count, items[i]);
    if (complement < 0)
      return -1;
    if (complement && node_is_known_total_integer(items[i]))
      return 1;
  }
  return 0;
}

static void logic_drop_odd_and_constant(ixs_tag tag, ixs_node **items,
                                        uint32_t count, int64_t constant,
                                        bool *have_constant) {
  uint32_t i;

  if (!*have_constant || tag != IXS_AND ||
      ((uint64_t)constant & UINT64_C(1)) == 0)
    return;
  for (i = 0; i < count; i++) {
    if (ixs_node_is_bool_valued(items[i])) {
      *have_constant = false;
      return;
    }
  }
}

static void logic_filter_absorbed_terms(ixs_tag tag, ixs_node **items,
                                        uint32_t *count, int64_t constant,
                                        bool have_constant) {
  bool drop_total_integers;
  bool drop_total_bools;
  uint32_t kept = 0;
  uint32_t i;

  if (!have_constant)
    return;
  drop_total_integers =
      (tag == IXS_AND && constant == 0) || (tag == IXS_OR && constant == -1);
  drop_total_bools = tag == IXS_OR && ((uint64_t)constant & UINT64_C(1)) != 0;
  if (!drop_total_integers && !drop_total_bools)
    return;
  for (i = 0; i < *count; i++) {
    bool drop = node_is_known_total_integer(items[i]) &&
                (drop_total_integers ||
                 (drop_total_bools && ixs_node_is_bool_valued(items[i])));
    if (!drop)
      items[kept++] = items[i];
  }
  *count = kept;
}

static ixs_node *logic_build_result(ixs_ctx *ctx, ixs_tag tag, ixs_node **items,
                                    uint32_t count, int64_t constant,
                                    bool have_constant) {
  int64_t identity_value = tag == IXS_AND ? -1 : 0;
  bool identity = !have_constant || constant == identity_value;

  if (count == 0)
    return ixs_node_int(ctx, have_constant ? constant : identity_value);
  if (identity && count == 1u && ixs_node_is_integer_valued(items[0]))
    return items[0];
  if (!identity || count == 1u) {
    ixs_node *constant_node =
        ixs_node_int(ctx, have_constant ? constant : identity_value);
    if (!constant_node)
      return NULL;
    items[count++] = constant_node;
  }
  if (!node_ptr_insert_last(ctx, items, count))
    return NULL;
  return ixs_node_assoc(ctx, tag, count, items);
}

static ixs_node *simp_logic_many(ixs_ctx *ctx, ixs_tag tag, uint32_t n,
                                 ixs_node *const *args) {
  ixs_arena_mark mark;
  ixs_node *failure;
  ixs_node *propagated;
  ixs_node *result;
  assoc_vec flat;
  int64_t constant;
  bool have_constant;
  uint32_t write;
  bool sorted_prefix = logic_sorted_prefix(tag, n, args);
  int complement;

  if (!assoc_inputs_clean(n, args, &propagated))
    return propagated;
  if (n == 0)
    return ixs_node_int(ctx, tag == IXS_AND ? -1 : 0);
  mark = ixs_arena_save(&ctx->scratch);
  if (!assoc_collect(ctx, tag, n, args, &flat)) {
    ixs_arena_restore(&ctx->scratch, mark);
    return NULL;
  }
  if (!logic_partition_constants(ctx, tag, &flat, &write, &constant,
                                 &have_constant, &failure)) {
    ixs_arena_restore(&ctx->scratch, mark);
    return failure;
  }
  if (!logic_sort_unique(ctx, flat.items, &write, sorted_prefix)) {
    ixs_arena_restore(&ctx->scratch, mark);
    return NULL;
  }
  complement = logic_has_reducible_complement(
      ctx, flat.items, write, sorted_prefix, sorted_prefix ? args[1] : NULL);
  if (complement < 0) {
    ixs_arena_restore(&ctx->scratch, mark);
    return NULL;
  }
  if (complement) {
    constant = tag == IXS_AND ? 0 : 1;
    have_constant = true;
  }
  logic_drop_odd_and_constant(tag, flat.items, write, constant, &have_constant);
  logic_filter_absorbed_terms(tag, flat.items, &write, constant, have_constant);
  result =
      logic_build_result(ctx, tag, flat.items, write, constant, have_constant);
  ixs_arena_restore(&ctx->scratch, mark);
  return result;
}

IXS_STATIC ixs_node *simp_and_many(ixs_ctx *ctx, uint32_t n,
                                   ixs_node *const *args) {
  return simp_logic_many(ctx, IXS_AND, n, args);
}

IXS_STATIC ixs_node *simp_or_many(ixs_ctx *ctx, uint32_t n,
                                  ixs_node *const *args) {
  return simp_logic_many(ctx, IXS_OR, n, args);
}

IXS_STATIC ixs_node *simp_and(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  ixs_node *args[2] = {a, b};
  return simp_and_many(ctx, 2, args);
}

IXS_STATIC ixs_node *simp_or(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  ixs_node *args[2] = {a, b};
  return simp_or_many(ctx, 2, args);
}

static ixs_node *truthy_predicate(ixs_ctx *ctx, ixs_node *c) {
  if (ixs_node_is_known_false(c))
    return ctx->node_false;
  if (ixs_node_is_known_true(c))
    return ctx->node_true;
  if (ixs_node_is_bool_valued(c))
    return c;
  return simp_cmp(ctx, c, IXS_CMP_NE, ctx->node_zero);
}

/* ------------------------------------------------------------------ */
/*  simp_pw (Piecewise)                                               */
/* ------------------------------------------------------------------ */

static int pw_merge_previous(ixs_ctx *ctx, ixs_pwcase *cases, uint32_t ncases,
                             ixs_node *value, ixs_node *cond) {
  ixs_node *lhs;
  ixs_node *rhs;
  if (ncases == 0 || cases[ncases - 1].value != value)
    return 0;
  lhs = truthy_predicate(ctx, cases[ncases - 1].cond);
  rhs = truthy_predicate(ctx, cond);
  if (!lhs || !rhs)
    return -1;
  cases[ncases - 1].cond = simp_or(ctx, lhs, rhs);
  if (!cases[ncases - 1].cond)
    return -1;
  return ixs_node_is_known_true(cases[ncases - 1].cond) ? 2 : 1;
}

static ixs_node *pw_finish(ixs_ctx *ctx, uint32_t ncases, ixs_pwcase *cases) {
  ixs_node *predicate;
  bool direct;
  bool inverted;

  if (ncases != 2 || !ixs_node_is_known_true(cases[1].cond))
    return ixs_node_pw(ctx, ncases, cases);
  direct = ixs_node_is_one(cases[0].value) && ixs_node_is_zero(cases[1].value);
  inverted =
      ixs_node_is_zero(cases[0].value) && ixs_node_is_one(cases[1].value);
  if (!direct && !inverted)
    return ixs_node_pw(ctx, ncases, cases);
  predicate = truthy_predicate(ctx, cases[0].cond);
  if (!predicate)
    return NULL;
  return direct ? predicate : simp_not(ctx, predicate);
}

static ixs_node *simp_pw_impl(ixs_ctx *ctx, uint32_t n, ixs_node *const *values,
                              ixs_node *const *conds) {
  size_t cap;
  ixs_pwcase *cases;
  uint32_t ncases = 0;
  uint32_t i;

  if (n == 0)
    return simp_err(ctx, "Piecewise: zero cases");
  if (n > UINT32_MAX / 2u)
    return simp_err(ctx, "Piecewise: too many cases");

  cap = n > 16 ? n : 16;
  if (cap > (size_t)-1 / sizeof(*cases))
    return simp_err(ctx, "Piecewise: too many cases");
  cases = ixs_arena_alloc(&ctx->scratch, cap * sizeof(*cases), sizeof(void *));
  if (!cases)
    return NULL;

  for (i = 0; i < n; i++) {
    ixs_node *v = values[i];
    ixs_node *c = conds[i];
    int merge_rc;

    if (!v || !c)
      return NULL;

    if (ixs_node_is_known_false(c))
      continue;

    if (ixs_node_is_sentinel(c)) {
      if (ncases > 0 && ixs_node_is_known_true(cases[ncases - 1].cond))
        continue;
      return c;
    }

    merge_rc = pw_merge_previous(ctx, cases, ncases, v, c);
    if (merge_rc < 0)
      return NULL;
    if (merge_rc == 2)
      break;
    if (merge_rc == 1)
      continue;

    if (ixs_node_is_known_true(c)) {
      if (ixs_node_is_sentinel(v)) {
        if (ncases > 0 && ixs_node_is_known_true(cases[ncases - 1].cond))
          break;
        return v;
      }
      cases[ncases].value = v;
      cases[ncases].cond = c;
      ncases++;
      break;
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
    return simp_undefined(ctx, "Piecewise: all conditions are False");

  if (ncases == 1 && ixs_node_is_known_true(cases[0].cond))
    return cases[0].value;

  return pw_finish(ctx, ncases, cases);
}

IXS_STATIC ixs_node *simp_pw(ixs_ctx *ctx, uint32_t n, ixs_node *const *values,
                             ixs_node *const *conds) {
  ixs_arena_mark m;
  ixs_node *result;
  uint32_t i;
  if (n > UINT32_MAX / 2u ||
      (n != 0 && sizeof(ixs_pwcase) > (size_t)-1 / (size_t)n))
    return simp_err(ctx, "Piecewise: too many cases");
  if (n > 0 && (!values || !conds))
    return NULL;
  for (i = 0; i < n; i++) {
    if (!values[i] || !conds[i])
      return NULL;
  }
  m = ixs_arena_save(&ctx->scratch);
  result = simp_pw_impl(ctx, n, values, conds);
  ixs_arena_restore(&ctx->scratch, m);
  return result;
}

/* ------------------------------------------------------------------ */
/*  Substitution (single and multi-target, with memoization)          */
/* ------------------------------------------------------------------ */

#define SUBS_MEMO_INITIAL_CAP 64u
#define SUBS_STACK_INITIAL_CAP 64u
#define SUBS_CHILD_INITIAL_CAP 16u

typedef struct {
  ixs_node *key;
  /* NULL means that key is active. Every completed substitution is non-NULL. */
  ixs_node *value;
} subs_memo_slot;

typedef struct {
  subs_memo_slot *slots;
  size_t capacity;
  size_t count;
  ixs_arena *arena;
} subs_memo;

typedef struct {
  ixs_node *expr;
  uint64_t next_child;
  bool entered;
} subs_frame;

typedef struct {
  ixs_ctx *ctx;
  uint32_t nsubs;
  ixs_node *const *targets;
  ixs_node *const *replacements;
  subs_memo memo;
  subs_frame *frames;
  size_t depth;
  size_t frame_capacity;
  ixs_node **children;
  size_t child_capacity;
} subs_query;

static size_t subs_memo_hash(const ixs_node *node) {
  uint32_t hash = node->hash;
  hash ^= hash >> 16;
  hash *= UINT32_C(0x7feb352d);
  hash ^= hash >> 15;
  return (size_t)hash;
}

static subs_memo_slot *subs_memo_find(subs_memo *memo, ixs_node *key,
                                      bool *found) {
  size_t slot = subs_memo_hash(key) & (memo->capacity - 1u);
  while (memo->slots[slot].key) {
    if (memo->slots[slot].key == key) {
      *found = true;
      return &memo->slots[slot];
    }
    slot = (slot + 1u) & (memo->capacity - 1u);
  }
  *found = false;
  return &memo->slots[slot];
}

static bool subs_memo_grow(subs_memo *memo) {
  subs_memo_slot *grown;
  size_t capacity;
  size_t bytes;
  size_t i;

  if (memo->capacity > SIZE_MAX / 2u)
    return false;
  capacity = memo->capacity * 2u;
  if (capacity > SIZE_MAX / sizeof(*grown))
    return false;
  bytes = capacity * sizeof(*grown);
  grown = ixs_arena_alloc(memo->arena, bytes, sizeof(void *));
  if (!grown)
    return false;
  memset(grown, 0, bytes);
  for (i = 0; i < memo->capacity; i++) {
    subs_memo_slot entry = memo->slots[i];
    size_t slot;
    if (!entry.key)
      continue;
    slot = subs_memo_hash(entry.key) & (capacity - 1u);
    while (grown[slot].key)
      slot = (slot + 1u) & (capacity - 1u);
    grown[slot] = entry;
  }
  memo->slots = grown;
  memo->capacity = capacity;
  return true;
}

static bool subs_memo_insert(subs_memo *memo, ixs_node *key, ixs_node *value) {
  subs_memo_slot *slot;
  bool found;

  slot = subs_memo_find(memo, key, &found);
  if (found) {
    assert(slot->value == NULL && value != NULL);
    if (slot->value != NULL || value == NULL)
      return false;
    slot->value = value;
    return true;
  }
  if (memo->count >= memo->capacity - memo->capacity / 4u) {
    if (!subs_memo_grow(memo))
      return false;
    slot = subs_memo_find(memo, key, &found);
    assert(!found);
    if (found)
      return false;
  }
  slot->key = key;
  slot->value = value;
  memo->count++;
  return true;
}

static ixs_node *subs_memo_value(subs_memo *memo, ixs_node *key) {
  subs_memo_slot *slot;
  bool found;
  slot = subs_memo_find(memo, key, &found);
  assert(found && slot->value != NULL);
  return found ? slot->value : NULL;
}

static bool subs_stack_push(subs_query *query, ixs_node *expr) {
  subs_frame *grown;
  size_t capacity;
  size_t bytes;

  if (query->depth == query->frame_capacity) {
    if (query->frame_capacity > SIZE_MAX / 2u)
      return false;
    capacity = query->frame_capacity * 2u;
    if (capacity > SIZE_MAX / sizeof(*grown))
      return false;
    bytes = capacity * sizeof(*grown);
    grown = ixs_arena_alloc(&query->ctx->scratch, bytes, sizeof(void *));
    if (!grown)
      return false;
    memcpy(grown, query->frames, query->depth * sizeof(*grown));
    query->frames = grown;
    query->frame_capacity = capacity;
  }
  query->frames[query->depth].expr = expr;
  query->frames[query->depth].next_child = 0;
  query->frames[query->depth].entered = false;
  query->depth++;
  return true;
}

static bool subs_ensure_children(subs_query *query, size_t count) {
  ixs_node **grown;
  size_t capacity = query->child_capacity;
  size_t bytes;

  if (count <= capacity)
    return true;
  while (capacity < count) {
    if (capacity > SIZE_MAX / 2u)
      return false;
    capacity *= 2u;
  }
  if (capacity > SIZE_MAX / sizeof(*grown))
    return false;
  bytes = capacity * sizeof(*grown);
  grown = ixs_arena_alloc(&query->ctx->scratch, bytes, sizeof(void *));
  if (!grown)
    return false;
  query->children = grown;
  query->child_capacity = capacity;
  return true;
}

static ixs_node *subs_direct_match(ixs_node *expr, uint32_t nsubs,
                                   ixs_node *const *targets,
                                   ixs_node *const *replacements) {
  uint32_t i;
  for (i = 0; i < nsubs; i++) {
    if (expr == targets[i])
      return replacements[i];
  }
  return NULL;
}

static bool subs_leaf_tag(ixs_tag tag) {
  switch (tag) {
  case IXS_INT:
  case IXS_RAT:
  case IXS_SYM:
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    return true;
  default:
    return false;
  }
}

static bool subs_node_rebuildable(ixs_node *expr) {
  switch (expr->tag) {
  case IXS_ADD:
  case IXS_MUL:
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
  case IXS_MOD:
  case IXS_CMP:
  case IXS_PIECEWISE:
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
  case IXS_NOT:
    return true;
  default:
    return false;
  }
}

static bool subs_add_child_at(ixs_node *expr, uint64_t ordinal,
                              ixs_node **child) {
  uint64_t index;
  if (ordinal == 0) {
    *child = expr->u.add.coeff;
    return true;
  }
  ordinal--;
  index = ordinal / 2u;
  if (index >= expr->u.add.nterms)
    return false;
  *child = (ordinal & 1u) == 0 ? expr->u.add.terms[index].term
                               : expr->u.add.terms[index].coeff;
  return true;
}

static bool subs_mul_child_at(ixs_node *expr, uint64_t ordinal,
                              ixs_node **child) {
  uint64_t index;
  if (ordinal == 0) {
    *child = expr->u.mul.coeff;
    return true;
  }
  index = ordinal - 1u;
  if (index >= expr->u.mul.nfactors)
    return false;
  *child = expr->u.mul.factors[index].base;
  return true;
}

static bool subs_unary_child_at(ixs_node *expr, uint64_t ordinal,
                                ixs_node **child) {
  if (ordinal != 0)
    return false;
  *child = expr->u.unary.arg;
  return true;
}

static bool subs_binary_child_at(ixs_node *expr, uint64_t ordinal,
                                 ixs_node **child) {
  if (ordinal > 1u)
    return false;
  *child = ordinal == 0 ? expr->u.binary.lhs : expr->u.binary.rhs;
  return true;
}

static bool subs_piecewise_child_at(ixs_node *expr, uint64_t ordinal,
                                    ixs_node **child) {
  uint64_t index = ordinal / 2u;
  if (index >= expr->u.pw.ncases)
    return false;
  *child = (ordinal & 1u) == 0 ? expr->u.pw.cases[index].value
                               : expr->u.pw.cases[index].cond;
  return true;
}

static bool subs_assoc_child_at(ixs_node *expr, uint64_t ordinal,
                                ixs_node **child) {
  if (ordinal >= expr->u.assoc.nargs)
    return false;
  *child = expr->u.assoc.args[ordinal];
  return true;
}

static bool subs_child_at(ixs_node *expr, uint64_t ordinal, ixs_node **child) {
  switch (expr->tag) {
  case IXS_ADD:
    return subs_add_child_at(expr, ordinal, child);
  case IXS_MUL:
    return subs_mul_child_at(expr, ordinal, child);
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
    return subs_unary_child_at(expr, ordinal, child);
  case IXS_MOD:
  case IXS_CMP:
    return subs_binary_child_at(expr, ordinal, child);
  case IXS_PIECEWISE:
    return subs_piecewise_child_at(expr, ordinal, child);
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
    return subs_assoc_child_at(expr, ordinal, child);
  case IXS_NOT:
    if (ordinal != 0)
      return false;
    *child = expr->u.unary_bool.arg;
    return true;
  default:
    return false;
  }
}

static ixs_node *subs_rebuild_add(subs_query *query, ixs_node *expr) {
  ixs_node *result = subs_memo_value(&query->memo, expr->u.add.coeff);
  uint32_t i;
  if (!result)
    return NULL;
  for (i = 0; i < expr->u.add.nterms; i++) {
    ixs_node *term = subs_memo_value(&query->memo, expr->u.add.terms[i].term);
    ixs_node *coefficient =
        subs_memo_value(&query->memo, expr->u.add.terms[i].coeff);
    if (!term || !coefficient)
      return NULL;
    term = simp_mul(query->ctx, coefficient, term);
    if (!term)
      return NULL;
    result = simp_add(query->ctx, result, term);
    if (!result)
      return NULL;
  }
  return result;
}

static ixs_node *subs_rebuild_mul(subs_query *query, ixs_node *expr) {
  ixs_node *result = subs_memo_value(&query->memo, expr->u.mul.coeff);
  uint32_t i;
  if (!result)
    return NULL;
  for (i = 0; i < expr->u.mul.nfactors; i++) {
    ixs_node *base = subs_memo_value(&query->memo, expr->u.mul.factors[i].base);
    int32_t exponent = expr->u.mul.factors[i].exp;
    ixs_node *power;
    if (!base)
      return NULL;
    if (exponent == 1) {
      power = base;
    } else if ((base->tag == IXS_INT || base->tag == IXS_RAT) && exponent > 0) {
      power =
          apply_pow(query->ctx, ixs_node_int(query->ctx, 1), base, exponent);
      if (power && ixs_node_is_sentinel(power)) {
        ixs_mulfactor factor;
        factor.base = base;
        factor.exp = exponent;
        power =
            ixs_node_mul(query->ctx, ixs_node_int(query->ctx, 1), 1, &factor);
      }
    } else {
      ixs_mulfactor factor;
      factor.base = base;
      factor.exp = exponent;
      power = ixs_node_mul(query->ctx, ixs_node_int(query->ctx, 1), 1, &factor);
    }
    if (!power)
      return NULL;
    result = simp_mul(query->ctx, result, power);
    if (!result)
      return NULL;
  }
  return result;
}

static ixs_node *subs_rebuild_assoc(subs_query *query, ixs_node *expr) {
  uint32_t count = expr->u.assoc.nargs;
  uint32_t i;
  if (!subs_ensure_children(query, count))
    return NULL;
  for (i = 0; i < count; i++) {
    query->children[i] = subs_memo_value(&query->memo, expr->u.assoc.args[i]);
    if (!query->children[i])
      return NULL;
  }
  if (expr->tag == IXS_MAX)
    return simp_max_many(query->ctx, count, query->children);
  if (expr->tag == IXS_MIN)
    return simp_min_many(query->ctx, count, query->children);
  if (expr->tag == IXS_XOR)
    return simp_xor_many(query->ctx, count, query->children);
  if (expr->tag == IXS_AND)
    return simp_and_many(query->ctx, count, query->children);
  return simp_or_many(query->ctx, count, query->children);
}

static ixs_node *subs_rebuild_piecewise(subs_query *query, ixs_node *expr) {
  uint32_t count = expr->u.pw.ncases;
  ixs_node **values;
  ixs_node **conditions;
  size_t needed;
  uint32_t i;

  if (count > UINT32_MAX / 2u)
    return NULL;
  needed = (size_t)count * 2u;
  if (!subs_ensure_children(query, needed))
    return NULL;
  values = query->children;
  conditions = query->children + count;
  for (i = 0; i < count; i++) {
    values[i] = subs_memo_value(&query->memo, expr->u.pw.cases[i].value);
    conditions[i] = subs_memo_value(&query->memo, expr->u.pw.cases[i].cond);
    if (!values[i] || !conditions[i])
      return NULL;
  }
  return simp_pw(query->ctx, count, values, conditions);
}

static ixs_node *subs_rebuild(subs_query *query, ixs_node *expr) {
  ixs_node *lhs;
  ixs_node *rhs;
  ixs_node *arg;
  switch (expr->tag) {
  case IXS_ADD:
    return subs_rebuild_add(query, expr);
  case IXS_MUL:
    return subs_rebuild_mul(query, expr);
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
    arg = subs_memo_value(&query->memo, expr->u.unary.arg);
    if (!arg)
      return NULL;
    if (expr->tag == IXS_FLOOR)
      return simp_floor(query->ctx, arg);
    if (expr->tag == IXS_CEIL)
      return simp_ceil(query->ctx, arg);
    return simp_trunc(query->ctx, arg);
  case IXS_MOD:
  case IXS_CMP:
    lhs = subs_memo_value(&query->memo, expr->u.binary.lhs);
    rhs = subs_memo_value(&query->memo, expr->u.binary.rhs);
    if (!lhs || !rhs)
      return NULL;
    if (expr->tag == IXS_MOD)
      return simp_mod(query->ctx, lhs, rhs);
    return simp_cmp(query->ctx, lhs, expr->u.binary.cmp_op, rhs);
  case IXS_PIECEWISE:
    return subs_rebuild_piecewise(query, expr);
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
    return subs_rebuild_assoc(query, expr);
  case IXS_NOT:
    arg = subs_memo_value(&query->memo, expr->u.unary_bool.arg);
    return arg ? simp_not(query->ctx, arg) : NULL;
  default:
    return expr;
  }
}

static bool subs_terminal_result(subs_query *query, ixs_node *expr,
                                 ixs_node **result) {
  if (ixs_node_is_sentinel(expr)) {
    *result = expr;
    return true;
  }
  *result = subs_direct_match(expr, query->nsubs, query->targets,
                              query->replacements);
  if (*result)
    return true;
  if (subs_leaf_tag(expr->tag) || !subs_node_rebuildable(expr)) {
    *result = expr;
    return true;
  }
  return false;
}

static ixs_node *subs_iterative(subs_query *query, ixs_node *root) {
  if (!subs_stack_push(query, root))
    return NULL;

  while (query->depth != 0) {
    subs_frame *frame = &query->frames[query->depth - 1u];
    ixs_node *expr = frame->expr;

    if (!frame->entered) {
      subs_memo_slot *slot;
      ixs_node *terminal;
      bool found;
      slot = subs_memo_find(&query->memo, expr, &found);
      if (found) {
        /* Interned nodes form a DAG; an active child would be a producer bug.
         */
        assert(slot->value != NULL);
        if (!slot->value)
          return NULL;
        query->depth--;
        continue;
      }
      if (subs_terminal_result(query, expr, &terminal)) {
        if (!subs_memo_insert(&query->memo, expr, terminal))
          return NULL;
        query->depth--;
        continue;
      }
      if (!subs_memo_insert(&query->memo, expr, NULL))
        return NULL;
      frame->entered = true;
      continue;
    }

    {
      ixs_node *child;
      if (subs_child_at(expr, frame->next_child, &child)) {
        subs_memo_slot *slot;
        bool found;
        slot = subs_memo_find(&query->memo, child, &found);
        if (found) {
          assert(slot->value != NULL);
          if (!slot->value)
            return NULL;
          frame->next_child++;
          continue;
        }
        if (!subs_stack_push(query, child))
          return NULL;
        continue;
      }
    }

    {
      ixs_node *result = subs_rebuild(query, expr);
      if (!result || !subs_memo_insert(&query->memo, expr, result))
        return NULL;
      query->depth--;
    }
  }
  return subs_memo_value(&query->memo, root);
}

static ixs_node *subs_common(ixs_ctx *ctx, ixs_node *expr, uint32_t nsubs,
                             ixs_node *const *targets,
                             ixs_node *const *replacements) {
  uint32_t i;
  ixs_node *parse_error = NULL;
  ixs_node *domain_error = NULL;
  ixs_node *result;
  ixs_arena_mark mark;
  subs_query query;
  subs_memo_slot initial_memo[SUBS_MEMO_INITIAL_CAP];
  subs_frame initial_frames[SUBS_STACK_INITIAL_CAP];
  ixs_node *initial_children[SUBS_CHILD_INITIAL_CAP];

  if (!expr)
    return NULL;
  if (nsubs > 0 && (!targets || !replacements))
    return NULL;
  if (expr->tag == IXS_PARSE_ERROR)
    parse_error = expr;
  else if (expr->tag == IXS_ERROR)
    domain_error = expr;
  for (i = 0; i < nsubs; i++) {
    if (!targets[i] || !replacements[i])
      return NULL;
    if (targets[i]->tag == IXS_PARSE_ERROR)
      parse_error = targets[i];
    else if (targets[i]->tag == IXS_ERROR)
      domain_error = targets[i];
    if (replacements[i]->tag == IXS_PARSE_ERROR)
      parse_error = replacements[i];
    else if (replacements[i]->tag == IXS_ERROR)
      domain_error = replacements[i];
  }
  if (parse_error)
    return parse_error;
  if (domain_error)
    return domain_error;
  if (nsubs == 0)
    return expr;
  for (i = 0; i < nsubs; i++) {
    if (expr == targets[i])
      return replacements[i];
  }

  mark = ixs_arena_save(&ctx->scratch);
  memset(&query, 0, sizeof(query));
  memset(initial_memo, 0, sizeof(initial_memo));
  query.ctx = ctx;
  query.nsubs = nsubs;
  query.targets = targets;
  query.replacements = replacements;
  query.memo.slots = initial_memo;
  query.memo.capacity = SUBS_MEMO_INITIAL_CAP;
  query.memo.arena = &ctx->scratch;
  query.frames = initial_frames;
  query.frame_capacity = SUBS_STACK_INITIAL_CAP;
  query.children = initial_children;
  query.child_capacity = SUBS_CHILD_INITIAL_CAP;
  result = subs_iterative(&query, expr);
  ixs_arena_restore(&ctx->scratch, mark);
  return result;
}

IXS_STATIC ixs_node *simp_subs(ixs_ctx *ctx, ixs_node *expr, ixs_node *target,
                               ixs_node *replacement) {
  return subs_common(ctx, expr, 1, &target, &replacement);
}

IXS_STATIC ixs_node *simp_subs_multi(ixs_ctx *ctx, ixs_node *expr,
                                     uint32_t nsubs, ixs_node *const *targets,
                                     ixs_node *const *replacements) {
  return subs_common(ctx, expr, nsubs, targets, replacements);
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

typedef struct {
  rewrite_memo_slot *slots;
  size_t cap;
  size_t used;
  ixs_arena *arena;
  bool grow_pending;
} rewrite_shared_cache;

/* Rehash is O(nodes seen in this cache lifetime); operations are amortized
 * O(1). */
static bool rewrite_shared_cache_grow(rewrite_shared_cache *cache) {
  size_t new_cap = cache->cap ? cache->cap * 2u : REWRITE_MEMO_SIZE;
  rewrite_memo_slot *slots;
  size_t i;
  if (new_cap < cache->cap || new_cap > (size_t)-1 / sizeof(*slots))
    return false;
  slots =
      ixs_arena_alloc(cache->arena, new_cap * sizeof(*slots), sizeof(void *));
  if (!slots)
    return false;
  memset(slots, 0, new_cap * sizeof(*slots));
  for (i = 0; i < cache->cap; i++) {
    if (cache->slots[i].key) {
      size_t slot = cache->slots[i].key->hash & (new_cap - 1u);
      while (slots[slot].key)
        slot = (slot + 1u) & (new_cap - 1u);
      slots[slot] = cache->slots[i];
    }
  }
  cache->slots = slots;
  cache->cap = new_cap;
  return true;
}

static ixs_node *rewrite_shared_cache_lookup(rewrite_shared_cache *cache,
                                             ixs_node *key) {
  size_t slot, probes;
  if (!cache || !cache->cap)
    return NULL;
  slot = key->hash & (cache->cap - 1u);
  for (probes = 0; probes < cache->cap; probes++) {
    if (!cache->slots[slot].key)
      return NULL;
    if (cache->slots[slot].key == key)
      return cache->slots[slot].val;
    slot = (slot + 1u) & (cache->cap - 1u);
  }
  return NULL;
}

static bool rewrite_shared_cache_store(rewrite_shared_cache *cache,
                                       ixs_node *key, ixs_node *value) {
  size_t slot;
  if (!cache)
    return true;
  if (!cache->cap && !rewrite_shared_cache_grow(cache))
    return false;
  /*
   * A Piecewise rewrite may hold scratch marks newer than this table.
   * Defer growth until the root iteration returns outside those marks.
   */
  if (cache->used >= cache->cap - cache->cap / 4u) {
    cache->grow_pending = true;
    return true;
  }
  slot = key->hash & (cache->cap - 1u);
  while (cache->slots[slot].key)
    slot = (slot + 1u) & (cache->cap - 1u);
  cache->slots[slot].key = key;
  cache->slots[slot].val = value;
  cache->used++;
  return true;
}

/*
 * If a MUL expression is pinned to zero (LE bound intersects propagated
 * GE to give [0,0]) and all but one factor are strictly nonzero, store
 * [0,0] for the remaining factor.
 * E.g. floor(C/32)*ceil(M/256) <= 0 with ceil(M/256)>=1 => floor(C/32)==0.
 */
static void decompose_product_zero(ixs_bounds *bnds, ixs_node *mul) {
  uint32_t i, j, nf;
  ixs_interval prod_iv;
  int64_t cp, cq;

  if (mul->tag != IXS_MUL)
    return;
  prod_iv = ixs_bounds_get(bnds, mul);
  if (!ixs_interval_is_point_int(prod_iv, NULL) || prod_iv.lo_p != 0)
    return;

  ixs_node_get_rat(mul->u.mul.coeff, &cp, &cq);
  (void)cq;
  if (cp == 0)
    return;

  nf = mul->u.mul.nfactors;
  for (i = 0; i < nf; i++) {
    ixs_interval fi;
    bool others_nonzero;
    if (mul->u.mul.factors[i].exp != 1)
      continue;
    fi = ixs_bounds_get(bnds, mul->u.mul.factors[i].base);
    if (fi.valid && ixs_rat_cmp(fi.lo_p, fi.lo_q, 0, 1) > 0)
      continue;

    others_nonzero = true;
    for (j = 0; j < nf; j++) {
      ixs_interval fj;
      if (j == i)
        continue;
      fj = ixs_bounds_get(bnds, mul->u.mul.factors[j].base);
      if (!fj.valid || !(ixs_rat_cmp(fj.lo_p, fj.lo_q, 0, 1) > 0 ||
                         ixs_rat_cmp(fj.hi_p, fj.hi_q, 0, 1) < 0)) {
        others_nonzero = false;
        break;
      }
    }
    if (others_nonzero)
      ixs_bounds_add_expr(bnds, mul->u.mul.factors[i].base,
                          ixs_interval_exact(0, 1));
  }
}

/*
 * Store a CMP as a branch-local bound.  For LT/LE, also store the negated
 * expression as a GT/GE bound so Max(neg_expr, c) can collapse when the
 * condition proves neg_expr >= c.  Finally, attempt product-zero
 * decomposition on the LHS when compared against zero.
 */
static void add_cmp_to_bounds(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *cmp) {
  ixs_bounds_add_assumption(bnds, cmp);
  if (ixs_node_is_zero(cmp->u.binary.rhs)) {
    ixs_cmp_op op = cmp->u.binary.cmp_op;
    if (op == IXS_CMP_LT || op == IXS_CMP_LE) {
      ixs_cmp_op flipped = (op == IXS_CMP_LT) ? IXS_CMP_GT : IXS_CMP_GE;
      ixs_node *zero = ixs_node_int(ctx, 0);
      ixs_node *neg = zero ? simp_sub(ctx, zero, cmp->u.binary.lhs) : NULL;
      if (neg) {
        ixs_node *neg_cmp = simp_cmp(ctx, neg, flipped, zero);
        if (neg_cmp && neg_cmp->tag == IXS_CMP)
          ixs_bounds_add_assumption(bnds, neg_cmp);
      }
    }
    decompose_product_zero(bnds, cmp->u.binary.lhs);
  }
}

static void add_cond_to_bounds(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *cond) {
  size_t cap = 16;
  size_t nstack = 0;
  ixs_node **stack =
      ixs_arena_alloc(&ctx->scratch, cap * sizeof(*stack), sizeof(void *));
  if (!stack)
    return;

  stack[nstack++] = cond;
  while (nstack > 0) {
    ixs_node *cur = stack[--nstack];
    if (cur->tag == IXS_CMP) {
      add_cmp_to_bounds(ctx, bnds, cur);
    } else if (cur->tag == IXS_AND && ixs_node_is_bool_valued(cur)) {
      uint32_t j;
      for (j = 0; j < cur->u.assoc.nargs; j++) {
        if (nstack == cap) {
          ixs_node **grown =
              scratch_grow(&ctx->scratch, stack, &cap, sizeof(*stack));
          if (!grown)
            return;
          stack = grown;
        }
        stack[nstack++] = cur->u.assoc.args[j];
      }
    }
  }
}

static ixs_node *rewrite_impl(ixs_ctx *ctx, ixs_node *n, ixs_bounds *bnds,
                              rewrite_memo_slot *memo,
                              rewrite_shared_cache *shared);

static ixs_node *rewrite(ixs_ctx *ctx, ixs_node *n, ixs_bounds *bnds,
                         rewrite_memo_slot *memo,
                         rewrite_shared_cache *shared) {
  ixs_node *result;
  uint32_t slot;
  if (!n || ixs_node_is_sentinel(n))
    return n;
  slot = n->hash & REWRITE_MEMO_MASK;
  if (memo[slot].key == n)
    return memo[slot].val;
  result = rewrite_shared_cache_lookup(shared, n);
  if (result) {
    memo[slot].key = n;
    memo[slot].val = result;
    return result;
  }
  result = rewrite_impl(ctx, n, bnds, memo, shared);
  if (result && !rewrite_shared_cache_store(shared, n, result))
    return NULL;
  memo[slot].key = n;
  memo[slot].val = result;
  return result;
}

/* Collapse floor or ceil to a constant when bounds pin it to one value. */
static ixs_node *try_floor_ceil_collapse(ixs_ctx *ctx, ixs_bounds *bnds,
                                         ixs_node *n, bool is_ceil) {
  ixs_node *arg = n->u.unary.arg;
  ixs_interval iv;
  int64_t lo_val, hi_val;
  if (!bnds)
    return n;
  iv = ixs_bounds_get(bnds, arg);
  if (!iv.valid)
    return n;
  lo_val = is_ceil ? ixs_rat_ceil(iv.lo_p, iv.lo_q)
                   : ixs_rat_floor(iv.lo_p, iv.lo_q);
  hi_val = is_ceil ? ixs_rat_ceil(iv.hi_p, iv.hi_q)
                   : ixs_rat_floor(iv.hi_p, iv.hi_q);
  if (lo_val == hi_val)
    return ixs_node_int(ctx, lo_val);
  return n;
}

static bool bounds_proves_zero_cmp(ixs_bounds *bnds, ixs_node *lhs,
                                   ixs_cmp_op op) {
  ixs_interval iv;
  if (!bnds || !lhs)
    return false;
  iv = ixs_bounds_get(bnds, lhs);
  if (!iv.valid)
    return false;
  switch (op) {
  case IXS_CMP_GT:
    return !iv.lo_inf && ixs_rat_cmp(iv.lo_p, iv.lo_q, 0, 1) > 0;
  case IXS_CMP_GE:
    return !iv.lo_inf && ixs_rat_cmp(iv.lo_p, iv.lo_q, 0, 1) >= 0;
  case IXS_CMP_LT:
    return !iv.hi_inf && ixs_rat_cmp(iv.hi_p, iv.hi_q, 0, 1) < 0;
  case IXS_CMP_LE:
    return !iv.hi_inf && ixs_rat_cmp(iv.hi_p, iv.hi_q, 0, 1) <= 0;
  case IXS_CMP_EQ:
  case IXS_CMP_NE:
    return false;
  }
  return false;
}

typedef enum {
  FLOOR_SHIFT_UNPROVEN,
  FLOOR_SHIFT_PROVEN,
  FLOOR_SHIFT_ERROR
} floor_shift_status;

static ixs_node *quotient_build_product(ixs_ctx *ctx, ixs_node *coefficient,
                                        uint32_t nfactors,
                                        const ixs_mulfactor *factors) {
  if (nfactors == 0)
    return coefficient;
  if (nfactors == 1 && factors[0].exp == 1 && ixs_node_is_one(coefficient))
    return factors[0].base;
  return ixs_node_mul(ctx, coefficient, nfactors, factors);
}

/* Partition one canonical product in two linear passes.  Reusing the sorted
 * factor array avoids repeated multiplication and supports every representable
 * exponent magnitude. */
static ixs_quotient_parts_status
quotient_product_parts(ixs_ctx *ctx, ixs_node *expr, ixs_node **numerator,
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
      return IXS_QUOTIENT_PARTS_NO_MATCH;
    num = ixs_node_int(ctx, p);
    denom = ixs_node_int(ctx, q);
    if (!num || !denom)
      return IXS_QUOTIENT_PARTS_OOM;
    *numerator = num;
    *denominator = denom;
    return IXS_QUOTIENT_PARTS_MATCH;
  }
  if (expr->tag != IXS_MUL)
    return IXS_QUOTIENT_PARTS_NO_MATCH;
  ixs_node_get_rat(expr->u.mul.coeff, &p, &q);
  for (i = 0; i < expr->u.mul.nfactors; i++) {
    int32_t exponent = expr->u.mul.factors[i].exp;
    if (exponent == INT32_MIN)
      return IXS_QUOTIENT_PARTS_NO_MATCH;
    if (exponent > 0)
      npositive++;
    else
      nnegative++;
  }
  if (q == 1 && nnegative == 0)
    return IXS_QUOTIENT_PARTS_NO_MATCH;

  mark = ixs_arena_save(&ctx->scratch);
  factors = ixs_arena_alloc(
      &ctx->scratch, expr->u.mul.nfactors * sizeof(*factors), sizeof(void *));
  if (!factors) {
    ixs_arena_restore(&ctx->scratch, mark);
    return IXS_QUOTIENT_PARTS_OOM;
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
    return IXS_QUOTIENT_PARTS_OOM;
  }
  num = quotient_build_product(ctx, num_coefficient, npositive, positive);
  denom = quotient_build_product(ctx, denom_coefficient, nnegative, negative);
  ixs_arena_restore(&ctx->scratch, mark);
  if (!num || !denom)
    return IXS_QUOTIENT_PARTS_OOM;
  *numerator = num;
  *denominator = denom;
  return IXS_QUOTIENT_PARTS_MATCH;
}

static ixs_quotient_parts_status exact_quotient_parts(ixs_ctx *ctx,
                                                      ixs_node *expr,
                                                      ixs_node **numerator,
                                                      ixs_node **denominator) {
  ixs_node *num;
  ixs_node *denom = NULL;
  ixs_node *constant_numerator;
  uint32_t i;

  if (expr->tag != IXS_ADD)
    return quotient_product_parts(ctx, expr, numerator, denominator);
  if (expr->u.add.nterms == 0)
    return IXS_QUOTIENT_PARTS_NO_MATCH;
  num = ixs_node_int(ctx, 0);
  if (!num)
    return IXS_QUOTIENT_PARTS_OOM;
  for (i = 0; i < expr->u.add.nterms; i++) {
    ixs_quotient_parts_status status;
    bool unrepresentable = false;
    ixs_node *scaled =
        simp_try_mul(ctx, expr->u.add.terms[i].coeff, expr->u.add.terms[i].term,
                     &unrepresentable);
    ixs_node *term_numerator;
    ixs_node *term_denominator;
    if (unrepresentable)
      return IXS_QUOTIENT_PARTS_NO_MATCH;
    if (!scaled)
      return IXS_QUOTIENT_PARTS_OOM;
    if (ixs_node_is_sentinel(scaled))
      return IXS_QUOTIENT_PARTS_NO_MATCH;
    status =
        quotient_product_parts(ctx, scaled, &term_numerator, &term_denominator);
    if (status != IXS_QUOTIENT_PARTS_MATCH)
      return status;
    if (denom && term_denominator != denom)
      return IXS_QUOTIENT_PARTS_NO_MATCH;
    denom = term_denominator;
    num = simp_try_add(ctx, num, term_numerator, &unrepresentable);
    if (unrepresentable)
      return IXS_QUOTIENT_PARTS_NO_MATCH;
    if (!num)
      return IXS_QUOTIENT_PARTS_OOM;
    if (ixs_node_is_sentinel(num))
      return IXS_QUOTIENT_PARTS_NO_MATCH;
  }
  if (!denom)
    return IXS_QUOTIENT_PARTS_NO_MATCH;
  {
    bool unrepresentable = false;
    constant_numerator =
        simp_try_mul(ctx, expr->u.add.coeff, denom, &unrepresentable);
    if (unrepresentable)
      return IXS_QUOTIENT_PARTS_NO_MATCH;
  }
  if (!constant_numerator)
    return IXS_QUOTIENT_PARTS_OOM;
  if (ixs_node_is_sentinel(constant_numerator))
    return IXS_QUOTIENT_PARTS_NO_MATCH;
  {
    bool unrepresentable = false;
    num = simp_try_add(ctx, num, constant_numerator, &unrepresentable);
    if (unrepresentable)
      return IXS_QUOTIENT_PARTS_NO_MATCH;
  }
  if (!num)
    return IXS_QUOTIENT_PARTS_OOM;
  if (ixs_node_is_sentinel(num))
    return IXS_QUOTIENT_PARTS_NO_MATCH;
  *numerator = num;
  *denominator = denom;
  return IXS_QUOTIENT_PARTS_MATCH;
}

IXS_STATIC ixs_quotient_parts_status
simp_exact_quotient_parts(ixs_ctx *ctx, ixs_node *expr, ixs_node **numerator,
                          ixs_node **denominator) {
  ixs_arena_mark mark = ixs_arena_save(&ctx->scratch);
  ixs_node *result_numerator = NULL;
  ixs_node *result_denominator = NULL;
  ixs_quotient_parts_status status;
  *numerator = NULL;
  *denominator = NULL;
  status =
      exact_quotient_parts(ctx, expr, &result_numerator, &result_denominator);
  ixs_arena_restore(&ctx->scratch, mark);
  if (status == IXS_QUOTIENT_PARTS_MATCH) {
    *numerator = result_numerator;
    *denominator = result_denominator;
  }
  return status;
}

static ixs_quotient_parts_status floor_quotient_parts(ixs_ctx *ctx,
                                                      ixs_node *floor,
                                                      ixs_node **numerator,
                                                      ixs_node **denominator) {
  ixs_node *arg;
  if (floor->tag != IXS_FLOOR)
    return IXS_QUOTIENT_PARTS_NO_MATCH;
  arg = floor->u.unary.arg;
  if (arg->tag == IXS_ADD && !ixs_node_is_zero(arg->u.add.coeff))
    return IXS_QUOTIENT_PARTS_NO_MATCH;
  return exact_quotient_parts(ctx, arg, numerator, denominator);
}

static floor_shift_status floor_shift_stays_in_residue(ixs_ctx *ctx,
                                                       ixs_bounds *bnds,
                                                       ixs_node *numerator,
                                                       ixs_node *shift,
                                                       ixs_node *denominator) {
  ixs_node *remainder;
  ixs_node *shifted;
  ixs_node *upper_difference;
  bool lower_safe;
  bool upper_safe;
  if (!bounds_proves_zero_cmp(bnds, denominator, IXS_CMP_GT) ||
      ixs_bounds_check_integer_valued(bnds, numerator) != IXS_CHECK_TRUE ||
      ixs_bounds_check_integer_valued(bnds, shift) != IXS_CHECK_TRUE ||
      ixs_bounds_check_integer_valued(bnds, denominator) != IXS_CHECK_TRUE)
    return bnds->oom ? FLOOR_SHIFT_ERROR : FLOOR_SHIFT_UNPROVEN;
  remainder = simp_mod_bnds(ctx, bnds, numerator, denominator);
  if (!remainder)
    return FLOOR_SHIFT_ERROR;
  if (ixs_node_is_sentinel(remainder))
    return FLOOR_SHIFT_UNPROVEN;
  shifted = simp_add(ctx, remainder, shift);
  if (!shifted)
    return FLOOR_SHIFT_ERROR;
  if (ixs_node_is_sentinel(shifted))
    return FLOOR_SHIFT_UNPROVEN;
  upper_difference = simp_sub(ctx, shifted, denominator);
  if (!upper_difference)
    return FLOOR_SHIFT_ERROR;
  if (ixs_node_is_sentinel(upper_difference))
    return FLOOR_SHIFT_UNPROVEN;
  lower_safe = bounds_proves_zero_cmp(bnds, shift, IXS_CMP_GE) ||
               bounds_proves_zero_cmp(bnds, shifted, IXS_CMP_GE);
  upper_safe = bounds_proves_zero_cmp(bnds, shift, IXS_CMP_LE) ||
               bounds_proves_zero_cmp(bnds, upper_difference, IXS_CMP_LT);
  if (bnds->oom)
    return FLOOR_SHIFT_ERROR;
  return lower_safe && upper_safe ? FLOOR_SHIFT_PROVEN : FLOOR_SHIFT_UNPROVEN;
}

/* One linear scan plus a fixed number of candidate-pair proofs. Quotient
 * decomposition is linear in the normalized top-level child counts. */
static ixs_node *cancel_equal_floor_difference(ixs_ctx *ctx, ixs_bounds *bnds,
                                               ixs_node *add) {
  uint32_t i, j;
  size_t inspected = 0;
  if (!bnds || add->tag != IXS_ADD || ixs_bounds_has_empty(bnds))
    return add;
  for (i = 0; i < add->u.add.nterms; i++) {
    ixs_quotient_parts_status left_status;
    ixs_node *left = add->u.add.terms[i].term;
    ixs_node *left_numerator;
    ixs_node *left_denominator;
    left_status =
        floor_quotient_parts(ctx, left, &left_numerator, &left_denominator);
    if (left_status == IXS_QUOTIENT_PARTS_OOM)
      return NULL;
    if (left_status != IXS_QUOTIENT_PARTS_MATCH)
      continue;
    for (j = i + 1; j < add->u.add.nterms; j++) {
      ixs_quotient_parts_status right_status;
      floor_shift_status proof;
      ixs_node *right = add->u.add.terms[j].term;
      ixs_node *right_numerator;
      ixs_node *right_denominator;
      ixs_node *shift;
      int64_t cp, cq;
      if (inspected++ == EQUAL_FLOOR_PAIR_LIMIT)
        return add;
      if (!addterm_coeffs_cancel(add->u.add.terms, i, j, &cp, &cq))
        continue;
      right_status = floor_quotient_parts(ctx, right, &right_numerator,
                                          &right_denominator);
      if (right_status == IXS_QUOTIENT_PARTS_OOM)
        return NULL;
      if (right_status != IXS_QUOTIENT_PARTS_MATCH ||
          right_denominator != left_denominator)
        continue;
      shift = simp_sub(ctx, right_numerator, left_numerator);
      if (!shift)
        return NULL;
      proof = ixs_node_is_sentinel(shift)
                  ? FLOOR_SHIFT_UNPROVEN
                  : floor_shift_stays_in_residue(ctx, bnds, left_numerator,
                                                 shift, left_denominator);
      if (proof == FLOOR_SHIFT_ERROR)
        return NULL;
      if (proof != FLOOR_SHIFT_PROVEN) {
        shift = simp_sub(ctx, left_numerator, right_numerator);
        if (!shift)
          return NULL;
        proof = ixs_node_is_sentinel(shift)
                    ? FLOOR_SHIFT_UNPROVEN
                    : floor_shift_stays_in_residue(ctx, bnds, right_numerator,
                                                   shift, right_denominator);
      }
      if (proof == FLOOR_SHIFT_ERROR)
        return NULL;
      if (proof != FLOOR_SHIFT_PROVEN)
        continue;
      IXS_STAT_HIT(ctx);
      return rebuild_add_without_pair(ctx, add, i, j);
    }
  }
  return add;
}

/* Mod(x, M) -> x when 0 <= x < M; -> r when x == r (mod m) and m % M == 0;
 * -> 0 when M | x. */
static ixs_node *mod_bounds_elim(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *n) {
  ixs_node *l = n->u.binary.lhs, *r = n->u.binary.rhs;
  ixs_node *diff;
  if (!bnds || ixs_bounds_has_empty(bnds))
    return n;

  if (r->tag == IXS_INT && r->u.ival > 0) {
    ixs_interval iv = ixs_bounds_get(bnds, l);
    if (iv.valid && iv.lo_q == 1 && iv.hi_q == 1 && iv.lo_p >= 0 &&
        iv.hi_p < r->u.ival)
      return l;

    /* x == rem (mod m) with m % M == 0  =>  Mod(x, M) == rem % M */
    if (l->tag == IXS_SYM) {
      int64_t sym_mod, sym_rem;
      if (ixs_bounds_get_modrem(bnds, l->u.name, &sym_mod, &sym_rem) &&
          sym_mod % r->u.ival == 0)
        return ixs_node_int(ctx, sym_rem % r->u.ival);
    }

    if (ixs_node_is_integer_valued(l) &&
        ixs_bounds_is_known_divisible(bnds, l, r->u.ival))
      return ixs_node_int(ctx, 0);
    return n;
  }

  /* Literal moduli use interval and congruence facts above. Only symbolic
   * moduli need the more expensive normalized comparison probes. */
  if (!bounds_proves_zero_cmp(bnds, r, IXS_CMP_GT) ||
      !bounds_proves_zero_cmp(bnds, l, IXS_CMP_GE))
    return n;
  diff = simp_sub(ctx, l, r);
  if (!diff || ixs_node_is_sentinel(diff))
    return diff;
  if (bounds_proves_zero_cmp(bnds, diff, IXS_CMP_LT))
    return l;
  return n;
}

/* Resolve (expr cmp 0) to 1/0 when bounds determine the outcome. */
static ixs_node *cmp_bounds_resolve(ixs_ctx *ctx, ixs_bounds *bnds,
                                    ixs_node *n) {
  ixs_check_result r;
  if (!bnds)
    return n;
  r = ixs_bounds_check(bnds, n);
  if (r == IXS_CHECK_TRUE)
    return ctx->node_true;
  if (r == IXS_CHECK_FALSE)
    return ctx->node_false;
  return n;
}

static ixs_node *rewrite_binary(ixs_ctx *ctx, ixs_node *n, ixs_bounds *bnds,
                                rewrite_memo_slot *memo,
                                rewrite_shared_cache *shared) {
  ixs_node *l = rewrite(ctx, n->u.binary.lhs, bnds, memo, shared);
  ixs_node *r = rewrite(ctx, n->u.binary.rhs, bnds, memo, shared);
  if (!l || !r)
    return NULL;
  switch (n->tag) {
  case IXS_MOD:
    return simp_mod_bnds(ctx, bnds, l, r);
  case IXS_CMP:
    return simp_cmp_bnds(ctx, bnds, l, n->u.binary.cmp_op, r);
  default: /* unreachable: only called from rewrite_impl's binary-op labels */
    return NULL;
  }
}

static ixs_node *rewrite_piecewise(ixs_ctx *ctx, ixs_node *n, ixs_bounds *bnds,
                                   rewrite_memo_slot *memo,
                                   rewrite_shared_cache *shared) {
  uint32_t i, nc = n->u.pw.ncases;
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
    cds[i] = rewrite(ctx, n->u.pw.cases[i].cond, bnds, memo, shared);
    if (!cds[i]) {
      ixs_arena_restore(&ctx->scratch, sm);
      return NULL;
    }
    /* For guarded branches, fork bounds with condition assumptions so
     * that e.g. Max(1, E) collapses when the condition proves E >= 1.
     * Fork and per-branch memo allocation are optimization-only: on scratch
     * OOM we rewrite under parent bounds, which is less precise but sound. */
    if (bnds && !ixs_node_is_known_true(cds[i]) &&
        !ixs_node_is_known_false(cds[i])) {
      ixs_arena_mark bm = ixs_arena_save(&ctx->scratch);
      ixs_bounds bbnds;
      bool bbnds_ready = ixs_bounds_fork(&bbnds, bnds);
      if (bbnds_ready) {
        rewrite_memo_slot *bmemo = ixs_arena_alloc(
            &ctx->scratch, REWRITE_MEMO_SIZE * sizeof(*bmemo), sizeof(void *));
        if (bmemo) {
          add_cond_to_bounds(ctx, &bbnds, cds[i]);
          memset(bmemo, 0, REWRITE_MEMO_SIZE * sizeof(*bmemo));
          /* Forked facts are branch-local and cannot populate the parent-fact
           * cache. */
          vals[i] = rewrite(ctx, n->u.pw.cases[i].value, &bbnds, bmemo, NULL);
        } else {
          vals[i] = rewrite(ctx, n->u.pw.cases[i].value, bnds, memo, shared);
        }
      } else {
        vals[i] = rewrite(ctx, n->u.pw.cases[i].value, bnds, memo, shared);
      }
      if (bbnds_ready)
        ixs_bounds_destroy(&bbnds);
      ixs_arena_restore(&ctx->scratch, bm);
    } else {
      vals[i] = rewrite(ctx, n->u.pw.cases[i].value, bnds, memo, shared);
    }
    if (!vals[i]) {
      ixs_arena_restore(&ctx->scratch, sm);
      return NULL;
    }
  }
  {
    ixs_node *pw;
    /* A two-arm scalar selector has the same partiality as its predicate and
     * a total constant multiplier.  Canonicalizing it to arithmetic lets the
     * ordinary multiplication rules cancel surrounding rational scales. */
    if (nc == 2u && ixs_node_is_known_true(cds[1]) &&
        ixs_node_is_zero(vals[1]) && ixs_node_is_const(vals[0]))
      pw = simp_mul(ctx, vals[0], cds[0]);
    else
      pw = simp_pw(ctx, nc, vals, cds);
    ixs_arena_restore(&ctx->scratch, sm);
    return pw;
  }
}

static ixs_node *rewrite_symbol(ixs_ctx *ctx, ixs_node *n, ixs_bounds *bnds) {
  int64_t val;
  if (bnds && ixs_interval_is_point_int(ixs_bounds_get(bnds, n), &val))
    return ixs_node_int(ctx, val);
  return n;
}

/* Recognize the Euclidean-remainder identity
 *
 *   N + D*ceiling(-N/D) == Mod(N, D),  D > 0,
 *
 * after child rewriting has exposed the complete affine numerator N.  The
 * fact-free ADD combiner recognizes the corresponding two-term shape, but an
 * affine N can occupy the ADD constant and several terms (for example N=x-3).
 * Integer-valuedness is essential: the identity is not valid for rational N.
 */
static ixs_node *cancel_ceil_remainder_node(ixs_ctx *ctx, ixs_bounds *bnds,
                                            ixs_node *add) {
  uint32_t i;
  if (!bnds || add->tag != IXS_ADD || ixs_bounds_has_empty(bnds))
    return add;
  for (i = 0; i < add->u.add.nterms; i++) {
    ixs_node *round = add->u.add.terms[i].term;
    ixs_node *numerator;
    ixs_node *scale;
    ixs_node *expected;
    ixs_node *modulus;
    ixs_node *result;
    int64_t p;
    int64_t q;
    uint32_t j;

    if (round->tag != IXS_CEIL)
      continue;
    ixs_node_get_rat(add->u.add.terms[i].coeff, &p, &q);
    if (q != 1 || p <= 0)
      continue;

    numerator = add->u.add.coeff;
    for (j = 0; j < add->u.add.nterms && numerator; j++) {
      ixs_node *term;
      if (j == i)
        continue;
      term = simp_mul(ctx, add->u.add.terms[j].coeff, add->u.add.terms[j].term);
      numerator = term ? simp_add(ctx, numerator, term) : NULL;
    }
    if (!numerator)
      return NULL;
    if (ixs_node_is_sentinel(numerator))
      continue;

    scale = make_const(ctx, -1, p);
    expected = scale ? distribute_mul_decompose(ctx, scale, numerator) : NULL;
    if (!expected)
      return NULL;
    if (ixs_node_is_sentinel(expected) || expected != round->u.unary.arg)
      continue;
    if (!node_is_integer(bnds, numerator)) {
      if (bnds->oom)
        return NULL;
      continue;
    }

    modulus = ixs_node_int(ctx, p);
    result = modulus ? simp_mod_bnds(ctx, bnds, numerator, modulus) : NULL;
    if (!result)
      return NULL;
    IXS_STAT_HIT(ctx);
    return result;
  }
  return add;
}

typedef struct {
  int64_t constant_p;
  int64_t constant_q;
  int64_t factor_p;
  int64_t factor_q;
  int64_t gcd;
  int64_t lcm;
} rational_carrier_plan;

typedef enum {
  RATIONAL_CARRIER_READY,
  RATIONAL_CARRIER_UNCHANGED,
  RATIONAL_CARRIER_OOM
} rational_carrier_status;

static rational_carrier_status
rational_carrier_scan(ixs_bounds *bnds, ixs_node *add,
                      rational_carrier_plan *plan) {
  uint32_t i;
  bool fractional = false;

  plan->lcm = 1;
  ixs_node_get_rat(add->u.add.coeff, &plan->constant_p, &plan->constant_q);
  if (plan->constant_q > 1)
    fractional = true;
  {
    int64_t scale = ixs_gcd(plan->lcm, plan->constant_q);
    if (!ixs_safe_mul(plan->lcm / scale, plan->constant_q, &plan->lcm))
      return RATIONAL_CARRIER_UNCHANGED;
  }
  for (i = 0; i < add->u.add.nterms; i++) {
    int64_t coefficient_p;
    int64_t coefficient_q;
    ixs_node_get_rat(add->u.add.terms[i].coeff, &coefficient_p, &coefficient_q);
    if (!node_is_integer(bnds, add->u.add.terms[i].term))
      return bnds && bnds->oom ? RATIONAL_CARRIER_OOM
                               : RATIONAL_CARRIER_UNCHANGED;
    if (coefficient_q > 1)
      fractional = true;
    {
      int64_t scale = ixs_gcd(plan->lcm, coefficient_q);
      if (!ixs_safe_mul(plan->lcm / scale, coefficient_q, &plan->lcm))
        return RATIONAL_CARRIER_UNCHANGED;
    }
  }
  return fractional ? RATIONAL_CARRIER_READY : RATIONAL_CARRIER_UNCHANGED;
}

static bool rational_carrier_find_factor(ixs_node *add,
                                         rational_carrier_plan *plan) {
  int64_t scaled;
  uint32_t i;

  plan->gcd = 0;
  if (plan->constant_p != 0) {
    if (!ixs_safe_mul(plan->constant_p, plan->lcm / plan->constant_q,
                      &scaled) ||
        scaled == INT64_MIN)
      return false;
    plan->gcd = ixs_gcd(plan->gcd, scaled);
  }
  for (i = 0; i < add->u.add.nterms; i++) {
    int64_t coefficient_p;
    int64_t coefficient_q;
    ixs_node_get_rat(add->u.add.terms[i].coeff, &coefficient_p, &coefficient_q);
    if (!ixs_safe_mul(coefficient_p, plan->lcm / coefficient_q, &scaled) ||
        scaled == INT64_MIN)
      return false;
    plan->gcd = ixs_gcd(plan->gcd, scaled);
  }
  return plan->gcd > 0 &&
         ixs_rat_normalize(plan->gcd, plan->lcm, &plan->factor_p,
                           &plan->factor_q) &&
         plan->factor_q != 1;
}

static ixs_node *rational_carrier_build(ixs_ctx *ctx, ixs_node *add,
                                        const rational_carrier_plan *plan) {
  ixs_arena_mark mark = ixs_arena_save(&ctx->scratch);
  ixs_addterm *terms;
  ixs_node *constant;
  ixs_node *factor;
  ixs_node *residual;
  ixs_node *result;
  int64_t scaled;
  uint32_t i;

  terms = ixs_arena_alloc(&ctx->scratch, add->u.add.nterms * sizeof(*terms),
                          sizeof(void *));
  if (!terms && add->u.add.nterms != 0) {
    ixs_arena_restore(&ctx->scratch, mark);
    return NULL;
  }
  if (!ixs_safe_mul(plan->constant_p, plan->lcm / plan->constant_q, &scaled)) {
    ixs_arena_restore(&ctx->scratch, mark);
    return add;
  }
  constant = ixs_node_int(ctx, scaled / plan->gcd);
  for (i = 0; i < add->u.add.nterms && constant; i++) {
    int64_t coefficient_p;
    int64_t coefficient_q;
    ixs_node_get_rat(add->u.add.terms[i].coeff, &coefficient_p, &coefficient_q);
    if (!ixs_safe_mul(coefficient_p, plan->lcm / coefficient_q, &scaled)) {
      constant = NULL;
      break;
    }
    terms[i].coeff = ixs_node_int(ctx, scaled / plan->gcd);
    terms[i].term = add->u.add.terms[i].term;
    if (!terms[i].coeff)
      constant = NULL;
  }
  residual =
      constant ? ixs_node_add(ctx, constant, add->u.add.nterms, terms) : NULL;
  factor = residual ? make_const(ctx, plan->factor_p, plan->factor_q) : NULL;
  result = factor ? simp_mul(ctx, factor, residual) : NULL;
  ixs_arena_restore(&ctx->scratch, mark);
  return result;
}

/* Factor the exact rational gcd of an additive carrier when every residual
 * term is provably integer-valued.  This leaves integer ADDs canonical while
 * exposing one literal denominator for downstream materialization. */
IXS_STATIC ixs_node *
simp_normalize_rational_carrier(ixs_ctx *ctx, ixs_bounds *bnds, ixs_node *add) {
  rational_carrier_plan plan;
  rational_carrier_status status;
  ixs_node *result;

  if (add->tag != IXS_ADD || node_is_integer(bnds, add))
    return add;
  status = rational_carrier_scan(bnds, add, &plan);
  if (status != RATIONAL_CARRIER_READY)
    return status == RATIONAL_CARRIER_OOM ? NULL : add;
  if (!rational_carrier_find_factor(add, &plan))
    return add;
  result = rational_carrier_build(ctx, add, &plan);
  if (result && result != add)
    IXS_STAT_HIT(ctx);
  return result;
}

static ixs_node *rewrite_add_node(ixs_ctx *ctx, ixs_node *n, ixs_bounds *bnds,
                                  rewrite_memo_slot *memo,
                                  rewrite_shared_cache *shared) {
  uint32_t i;
  unsigned floor_candidates = 0;
  ixs_node *result = rewrite(ctx, n->u.add.coeff, bnds, memo, shared);
  if (!result)
    return NULL;
  for (i = 0; i < n->u.add.nterms; i++) {
    ixs_node *t = rewrite(ctx, n->u.add.terms[i].term, bnds, memo, shared);
    ixs_node *rewritten_term;
    ixs_node *c = n->u.add.terms[i].coeff;
    if (!t)
      return NULL;
    if (t->tag == IXS_FLOOR && floor_candidates < 2u)
      floor_candidates++;
    rewritten_term = t;
    t = simp_mul(ctx, c, t);
    if (!t)
      return NULL;
    /* An ADD stores each term's rational coefficient outside the child node.
     * Re-run the generic rewrite on the reconstructed scalar term so rules
     * that consume the complete product also apply below an additive root. */
    if (t != rewritten_term) {
      t = rewrite(ctx, t, bnds, memo, shared);
      if (!t)
        return NULL;
    }
    result = simp_add(ctx, result, t);
    if (!result)
      return NULL;
  }
  result = cancel_ceil_remainder_node(ctx, bnds, result);
  if (!result)
    return NULL;
  result = cancel_congruent_mod_difference(ctx, bnds, result);
  result = cancel_wide_floor_mod_node(ctx, result);
  if (!result || floor_candidates < 2u)
    return result;
  return cancel_equal_floor_difference(ctx, bnds, result);
}

static ixs_node *rewrite_mul_factor(ixs_ctx *ctx, ixs_node *result,
                                    ixs_node *base, int32_t exp) {
  return mul_power_or_raw(ctx, result, base, exp,
                          ixs_node_is_const(base) && exp != 0);
}

static ixs_node *cancel_scaled_mod_quotient(ixs_ctx *ctx, ixs_bounds *bnds,
                                            ixs_node *mul) {
  ixs_node *mod, *inner, *modulus, *reduced;
  int64_t p, q;
  if (mul->tag != IXS_MUL || mul->u.mul.nfactors != 1 ||
      mul->u.mul.factors[0].exp != 1 ||
      mul->u.mul.factors[0].base->tag != IXS_MOD)
    return mul;
  ixs_node_get_rat(mul->u.mul.coeff, &p, &q);
  mod = mul->u.mul.factors[0].base;
  if (q <= 1 || mod->u.binary.rhs->tag != IXS_INT ||
      mod->u.binary.rhs->u.ival <= 0 || mod->u.binary.rhs->u.ival % q != 0)
    return mul;
  inner = simp_div(ctx, mod->u.binary.lhs, ixs_node_int(ctx, q));
  modulus = ixs_node_int(ctx, mod->u.binary.rhs->u.ival / q);
  if (!inner || !modulus)
    return NULL;
  if (ixs_node_is_sentinel(inner))
    return inner;
  if (!node_is_integer(bnds, inner))
    return mul;
  reduced = simp_mod_bnds(ctx, bnds, inner, modulus);
  if (!reduced)
    return NULL;
  IXS_STAT_HIT(ctx);
  return p == 1 ? reduced : simp_mul(ctx, ixs_node_int(ctx, p), reduced);
}

static ixs_node *cancel_scaled_xor_quotient(ixs_ctx *ctx, ixs_bounds *bnds,
                                            ixs_node *mul) {
  ixs_arena_mark mark;
  ixs_node *xor_node;
  ixs_node *divisor;
  ixs_node *reduced;
  ixs_node **args;
  int64_t p;
  int64_t q;
  size_t nargs;
  uint32_t i;

  if (mul->tag != IXS_MUL || mul->u.mul.nfactors != 1 ||
      mul->u.mul.factors[0].exp != 1 ||
      mul->u.mul.factors[0].base->tag != IXS_XOR)
    return mul;
  ixs_node_get_rat(mul->u.mul.coeff, &p, &q);
  xor_node = mul->u.mul.factors[0].base;
  nargs = (size_t)xor_node->u.assoc.nargs;
  /* Multiplication by a positive power of two is an exact bit shift, hence
   * xor(q*a_i) == q*xor(a_i).  No analogous rewrite is valid for an arbitrary
   * common integer factor. */
  if (q <= 1 || !uint64_pow2((uint64_t)q) || nargs == 0 ||
      !xor_node->u.assoc.args || nargs > SIZE_MAX / sizeof(*args))
    return mul;

  mark = ixs_arena_save(&ctx->scratch);
  args = ixs_arena_alloc(&ctx->scratch, nargs * sizeof(*args), sizeof(void *));
  divisor = ixs_node_int(ctx, q);
  if (!args || !divisor) {
    ixs_arena_restore(&ctx->scratch, mark);
    return NULL;
  }
  for (i = 0; i < xor_node->u.assoc.nargs; i++) {
    args[i] = simp_div(ctx, xor_node->u.assoc.args[i], divisor);
    if (!args[i]) {
      ixs_arena_restore(&ctx->scratch, mark);
      return NULL;
    }
    if (ixs_node_is_sentinel(args[i]) ||
        (!ixs_node_is_integer_valued(args[i]) &&
         !node_is_integer(bnds, args[i]))) {
      ixs_arena_restore(&ctx->scratch, mark);
      return mul;
    }
  }
  reduced = simp_xor_many_bnds(ctx, bnds, xor_node->u.assoc.nargs, args);
  if (reduced && p != 1)
    reduced = simp_mul(ctx, ixs_node_int(ctx, p), reduced);
  ixs_arena_restore(&ctx->scratch, mark);
  if (reduced)
    IXS_STAT_HIT(ctx);
  return reduced;
}

static ixs_node *rewrite_mul_node(ixs_ctx *ctx, ixs_node *n, ixs_bounds *bnds,
                                  rewrite_memo_slot *memo,
                                  rewrite_shared_cache *shared) {
  uint32_t i;
  ixs_node *result = rewrite(ctx, n->u.mul.coeff, bnds, memo, shared);
  if (!result)
    return NULL;
  for (i = 0; i < n->u.mul.nfactors; i++) {
    ixs_node *base = rewrite(ctx, n->u.mul.factors[i].base, bnds, memo, shared);
    if (!base)
      return NULL;
    result = rewrite_mul_factor(ctx, result, base, n->u.mul.factors[i].exp);
    if (!result)
      return NULL;
  }
  result = cancel_scaled_mod_quotient(ctx, bnds, result);
  return result ? cancel_scaled_xor_quotient(ctx, bnds, result) : NULL;
}

static ixs_node *rewrite_round_node(ixs_ctx *ctx, ixs_node *n, ixs_bounds *bnds,
                                    rewrite_memo_slot *memo,
                                    rewrite_shared_cache *shared, ixs_tag tag) {
  ixs_node *arg = rewrite(ctx, n->u.unary.arg, bnds, memo, shared);
  if (!arg)
    return NULL;
  if (tag == IXS_FLOOR)
    return simp_floor_bnds(ctx, bnds, arg);
  if (tag == IXS_CEIL)
    return simp_ceil_bnds(ctx, bnds, arg);
  return simp_trunc_bnds(ctx, bnds, arg);
}

static ixs_node *rewrite_assoc_node(ixs_ctx *ctx, ixs_node *n, ixs_bounds *bnds,
                                    rewrite_memo_slot *memo,
                                    rewrite_shared_cache *shared) {
  ixs_arena_mark mark = ixs_arena_save(&ctx->scratch);
  uint32_t nargs = n->u.assoc.nargs;
  uint32_t i;
  ixs_node *result;
  ixs_node **args =
      ixs_arena_alloc(&ctx->scratch, nargs * sizeof(*args), sizeof(void *));
  if (!args && nargs != 0) {
    ixs_arena_restore(&ctx->scratch, mark);
    return NULL;
  }
  for (i = 0; i < nargs; i++) {
    args[i] = rewrite(ctx, n->u.assoc.args[i], bnds, memo, shared);
    if (!args[i]) {
      ixs_arena_restore(&ctx->scratch, mark);
      return NULL;
    }
  }
  if (n->tag == IXS_MAX)
    result = simp_extrema_many_bnds(ctx, bnds, IXS_MAX, nargs, args);
  else if (n->tag == IXS_MIN)
    result = simp_extrema_many_bnds(ctx, bnds, IXS_MIN, nargs, args);
  else if (n->tag == IXS_XOR)
    result = simp_xor_many_bnds(ctx, bnds, nargs, args);
  else if (n->tag == IXS_AND)
    result = simp_and_many(ctx, nargs, args);
  else
    result = simp_or_many(ctx, nargs, args);
  ixs_arena_restore(&ctx->scratch, mark);
  return result;
}

static ixs_node *rewrite_not_node(ixs_ctx *ctx, ixs_node *n, ixs_bounds *bnds,
                                  rewrite_memo_slot *memo,
                                  rewrite_shared_cache *shared) {
  ixs_node *arg = rewrite(ctx, n->u.unary_bool.arg, bnds, memo, shared);
  return arg ? simp_not(ctx, arg) : NULL;
}

static ixs_node *rewrite_impl(ixs_ctx *ctx, ixs_node *n, ixs_bounds *bnds,
                              rewrite_memo_slot *memo,
                              rewrite_shared_cache *shared) {
  switch (n->tag) {
  case IXS_INT:
  case IXS_RAT:
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    return n;

  case IXS_SYM:
    return rewrite_symbol(ctx, n, bnds);
  case IXS_ADD:
    return rewrite_add_node(ctx, n, bnds, memo, shared);
  case IXS_MUL:
    return rewrite_mul_node(ctx, n, bnds, memo, shared);
  case IXS_FLOOR:
    return rewrite_round_node(ctx, n, bnds, memo, shared, IXS_FLOOR);
  case IXS_CEIL:
    return rewrite_round_node(ctx, n, bnds, memo, shared, IXS_CEIL);
  case IXS_TRUNC:
    return rewrite_round_node(ctx, n, bnds, memo, shared, IXS_TRUNC);
  case IXS_MOD:
  case IXS_CMP:
    return rewrite_binary(ctx, n, bnds, memo, shared);
  case IXS_PIECEWISE:
    return rewrite_piecewise(ctx, n, bnds, memo, shared);
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
    return rewrite_assoc_node(ctx, n, bnds, memo, shared);
  case IXS_NOT:
    return rewrite_not_node(ctx, n, bnds, memo, shared);
  }
  return n;
}

static ixs_node *simp_simplify_bounds_cached(ixs_ctx *ctx, ixs_node *expr,
                                             ixs_bounds *bnds,
                                             rewrite_shared_cache *shared,
                                             bool *limited) {
  ixs_node **seen = NULL;
  size_t seen_count = 0;
  size_t seen_capacity = 0;
  rewrite_memo_slot memo[REWRITE_MEMO_SIZE];

  (void)limited;
  if (!expr)
    return NULL;
  if (ixs_node_is_sentinel(expr))
    return expr;

  for (;;) {
    size_t i;
    ixs_node *prev = expr;
    memset(memo, 0, sizeof(memo));
    expr = rewrite(ctx, expr, bnds, memo, shared);
    if (!expr)
      return NULL;
    if (shared && shared->grow_pending) {
      shared->grow_pending = false;
      if (!rewrite_shared_cache_grow(shared))
        return NULL;
    }
    if (expr == prev)
      break;
    for (i = 0; i < seen_count; i++) {
      if (seen[i] == expr) {
        ixs_ctx_push_error(ctx, "simplify: rewrite cycle detected");
        return ctx->sentinel_error;
      }
    }
    if (seen_count == seen_capacity) {
      size_t next_capacity = seen_capacity ? seen_capacity * 2u : 8u;
      ixs_node **grown;
      if (next_capacity < seen_capacity ||
          next_capacity > SIZE_MAX / sizeof(*grown))
        return NULL;
      grown = ixs_arena_alloc(&ctx->scratch, next_capacity * sizeof(*grown),
                              sizeof(void *));
      if (!grown)
        return NULL;
      if (seen_count)
        memcpy(grown, seen, seen_count * sizeof(*grown));
      seen = grown;
      seen_capacity = next_capacity;
    }
    seen[seen_count++] = expr;
  }

  return expr;
}

IXS_STATIC ixs_node *simp_simplify_bounds_status(ixs_ctx *ctx, ixs_node *expr,
                                                 ixs_bounds *bnds,
                                                 bool *limited) {
  ixs_arena_mark mark;
  rewrite_shared_cache shared;
  ixs_node *result;
  bool query_held = false;
  assert(limited != NULL);
  *limited = false;
  if (!expr || ixs_node_is_sentinel(expr))
    return expr;
  if (!ixs_bounds_query_hold_begin(bnds, expr, &query_held)) {
    if (bnds && bnds->oom)
      return NULL;
    *limited = true;
    return expr;
  }
  mark = ixs_arena_save(&ctx->scratch);
  shared.slots = NULL;
  shared.cap = 0;
  shared.used = 0;
  shared.arena = &ctx->scratch;
  shared.grow_pending = false;
  if (!rewrite_shared_cache_grow(&shared)) {
    ixs_arena_restore(&ctx->scratch, mark);
    if (query_held)
      ixs_bounds_query_hold_end(bnds);
    return NULL;
  }
  result = simp_simplify_bounds_cached(ctx, expr, bnds, &shared, limited);
  ixs_arena_restore(&ctx->scratch, mark);
  if (query_held)
    ixs_bounds_query_hold_end(bnds);
  return result;
}

IXS_STATIC ixs_node *simp_simplify_bounds(ixs_ctx *ctx, ixs_node *expr,
                                          ixs_bounds *bnds) {
  bool limited;
  return simp_simplify_bounds_status(ctx, expr, bnds, &limited);
}

IXS_STATIC bool simp_simplify_batch_bounds(ixs_ctx *ctx, ixs_node **exprs,
                                           size_t n, ixs_bounds *bnds) {
  rewrite_shared_cache shared;
  size_t i;
  shared.slots = NULL;
  shared.cap = 0;
  shared.used = 0;
  shared.arena = &ctx->scratch;
  shared.grow_pending = false;
  if (n > 0 && !rewrite_shared_cache_grow(&shared))
    goto failed;
  for (i = 0; i < n; i++) {
    bool query_held = false;
    bool limited = false;
    if (!exprs[i] || ixs_node_is_sentinel(exprs[i]))
      continue;
    if (!ixs_bounds_query_hold_begin(bnds, exprs[i], &query_held)) {
      if (bnds && bnds->oom)
        goto failed;
      continue;
    }
    exprs[i] =
        simp_simplify_bounds_cached(ctx, exprs[i], bnds, &shared, &limited);
    if (query_held)
      ixs_bounds_query_hold_end(bnds);
    if (!exprs[i] || limited)
      goto failed;
  }
  return true;

failed:
  for (i = 0; i < n; i++)
    exprs[i] = NULL;
  return false;
}

IXS_STATIC ixs_node *simp_simplify(ixs_ctx *ctx, ixs_node *expr,
                                   ixs_node *const *assumptions,
                                   size_t n_assumptions) {
  ixs_arena_mark m = ixs_arena_save(&ctx->scratch);
  ixs_bounds bnds;
  ixs_bounds_build_status status = ixs_bounds_build_ctx(
      &bnds, ctx, &ctx->scratch, assumptions, n_assumptions);
  if (status != IXS_BOUNDS_BUILD_OK) {
    ixs_arena_restore(&ctx->scratch, m);
    return status == IXS_BOUNDS_BUILD_INVALID ? ctx->sentinel_error : NULL;
  }
  expr = simp_simplify_bounds(ctx, expr, &bnds);
  if (expr && !ixs_node_is_sentinel(expr))
    expr = simp_normalize_rational_carrier(ctx, &bnds, expr);
  ixs_bounds_destroy(&bnds);
  ixs_arena_restore(&ctx->scratch, m);
  return expr;
}

IXS_STATIC void simp_simplify_batch(ixs_ctx *ctx, ixs_node **exprs, size_t n,
                                    ixs_node *const *assumptions,
                                    size_t n_assumptions) {
  ixs_arena_mark m = ixs_arena_save(&ctx->scratch);
  ixs_bounds bnds;
  ixs_bounds_build_status status;
  size_t i;
  status = ixs_bounds_build_ctx(&bnds, ctx, &ctx->scratch, assumptions,
                                n_assumptions);
  if (status != IXS_BOUNDS_BUILD_OK) {
    for (i = 0; i < n; i++)
      exprs[i] =
          status == IXS_BOUNDS_BUILD_INVALID ? ctx->sentinel_error : NULL;
    ixs_arena_restore(&ctx->scratch, m);
    return;
  }
  (void)simp_simplify_batch_bounds(ctx, exprs, n, &bnds);
  for (i = 0; i < n; i++) {
    if (exprs[i] && !ixs_node_is_sentinel(exprs[i]))
      exprs[i] = simp_normalize_rational_carrier(ctx, &bnds, exprs[i]);
  }
  ixs_bounds_destroy(&bnds);
  ixs_arena_restore(&ctx->scratch, m);
}

IXS_STATIC ixs_check_result simp_check(ixs_ctx *ctx, ixs_node *expr,
                                       ixs_node *const *assumptions,
                                       size_t n_assumptions) {
  ixs_arena_mark m = ixs_arena_save(&ctx->scratch);
  ixs_bounds bnds;
  ixs_check_result r;
  if (ixs_bounds_build_ctx(&bnds, ctx, &ctx->scratch, assumptions,
                           n_assumptions) != IXS_BOUNDS_BUILD_OK) {
    ixs_arena_restore(&ctx->scratch, m);
    return IXS_CHECK_UNKNOWN;
  }
  r = ixs_bounds_check_query(&bnds, expr);
  ixs_bounds_destroy(&bnds);
  ixs_arena_restore(&ctx->scratch, m);
  return r;
}

typedef struct {
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds bounds;
  bool active;
  bool built;
  bool query_held;
} simp_bounds_scope;

static bool simp_bounds_scope_init(simp_bounds_scope *scope, ixs_ctx *ctx,
                                   ixs_node *const *assumptions,
                                   size_t n_assumptions) {
  scope->ctx = ctx;
  scope->mark = ixs_arena_save(&ctx->scratch);
  scope->active = true;
  scope->built = false;
  scope->query_held = false;
  if (ixs_bounds_build_ctx(&scope->bounds, ctx, &ctx->scratch, assumptions,
                           n_assumptions) != IXS_BOUNDS_BUILD_OK) {
    ixs_arena_restore(&ctx->scratch, scope->mark);
    scope->active = false;
    return false;
  }
  scope->built = true;
  return true;
}

static bool simp_bounds_scope_hold(simp_bounds_scope *scope, ixs_node *root) {
  assert(scope && scope->active && scope->built && !scope->query_held);
  return ixs_bounds_query_hold_begin(&scope->bounds, root, &scope->query_held);
}

static void simp_bounds_scope_end_query(simp_bounds_scope *scope) {
  if (!scope->query_held)
    return;
  ixs_bounds_query_hold_end(&scope->bounds);
  scope->query_held = false;
}

static void simp_bounds_scope_destroy(simp_bounds_scope *scope) {
  if (!scope->active)
    return;
  assert(!scope->query_held);
  if (scope->built)
    ixs_bounds_destroy(&scope->bounds);
  ixs_arena_restore(&scope->ctx->scratch, scope->mark);
  scope->active = false;
  scope->built = false;
}

IXS_STATIC ixs_check_result
simp_check_integer_valued(ixs_ctx *ctx, ixs_node *expr,
                          ixs_node *const *assumptions, size_t n_assumptions) {
  simp_bounds_scope scope;
  ixs_check_result result = IXS_CHECK_UNKNOWN;

  if (!ctx || !expr || ixs_node_is_sentinel(expr) ||
      !ixs_ctx_owns_node(ctx, expr))
    return IXS_CHECK_UNKNOWN;
  if (!simp_bounds_scope_init(&scope, ctx, assumptions, n_assumptions))
    return IXS_CHECK_UNKNOWN;
  if (!simp_bounds_scope_hold(&scope, expr)) {
    simp_bounds_scope_destroy(&scope);
    return IXS_CHECK_UNKNOWN;
  }
  result = ixs_bounds_check_integer_valued(&scope.bounds, expr);
  simp_bounds_scope_end_query(&scope);
  simp_bounds_scope_destroy(&scope);
  return result;
}

IXS_STATIC ixs_check_result simp_check_defined(ixs_ctx *ctx, ixs_node *expr,
                                               ixs_node *const *assumptions,
                                               size_t n_assumptions) {
  simp_bounds_scope scope;
  ixs_check_result result = IXS_CHECK_UNKNOWN;

  if (!ctx || !expr || ixs_node_is_sentinel(expr) ||
      !ixs_ctx_owns_node(ctx, expr))
    return IXS_CHECK_UNKNOWN;
  if (!simp_bounds_scope_init(&scope, ctx, assumptions, n_assumptions))
    return IXS_CHECK_UNKNOWN;
  if (!simp_bounds_scope_hold(&scope, expr)) {
    simp_bounds_scope_destroy(&scope);
    return IXS_CHECK_UNKNOWN;
  }
  result = ixs_bounds_check_defined(&scope.bounds, expr);
  simp_bounds_scope_end_query(&scope);
  simp_bounds_scope_destroy(&scope);
  return result;
}

static ixs_pow2_fact pow2_fact_from_int64(int64_t value) {
  uint64_t u;
  if (value == 0)
    return IXS_POW2_OR_ZERO;
  if (value < 0)
    return IXS_POW2_UNKNOWN;
  u = (uint64_t)value;
  return (u & (u - 1u)) == 0 ? IXS_POW2_POSITIVE : IXS_POW2_UNKNOWN;
}

IXS_STATIC ixs_pow2_fact simp_get_pow2_fact(ixs_ctx *ctx, ixs_node *expr,
                                            ixs_node *const *assumptions,
                                            size_t n_assumptions) {
  simp_bounds_scope scope;
  ixs_bitfacts bits;
  ixs_interval iv;
  int64_t exact;
  ixs_pow2_fact result = IXS_POW2_UNKNOWN;

  if (!expr || ixs_node_is_sentinel(expr))
    return IXS_POW2_UNKNOWN;

  if (!simp_bounds_scope_init(&scope, ctx, assumptions, n_assumptions))
    return IXS_POW2_UNKNOWN;
  if (!simp_bounds_scope_hold(&scope, expr))
    goto cleanup;

  if (ixs_bounds_has_empty(&scope.bounds))
    goto cleanup;

  if (ixs_bounds_get_bitfacts(&scope.bounds, expr, &bits))
    result = bits.pow2;
  if (result == IXS_POW2_UNKNOWN) {
    iv = ixs_bounds_get(&scope.bounds, expr);
    if (ixs_interval_is_point_int(iv, &exact))
      result = pow2_fact_from_int64(exact);
  }

cleanup:
  simp_bounds_scope_end_query(&scope);
  simp_bounds_scope_destroy(&scope);
  return result;
}

IXS_STATIC bool simp_range(ixs_ctx *ctx, ixs_node *expr,
                           ixs_node *const *assumptions, size_t n_assumptions,
                           ixs_range_result *out) {
  simp_bounds_scope scope;
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

  if (!expr || ixs_node_is_sentinel(expr))
    return false;

  if (!simp_bounds_scope_init(&scope, ctx, assumptions, n_assumptions))
    return false;
  if (!simp_bounds_scope_hold(&scope, expr))
    goto cleanup;

  if (ixs_bounds_has_empty(&scope.bounds))
    goto cleanup;

  iv = ixs_bounds_get(&scope.bounds, expr);
  if (!iv.valid || ixs_interval_is_empty(iv))
    goto cleanup;

  if (!iv.lo_inf) {
    out->has_lower = true;
    out->lower_p = iv.lo_p;
    out->lower_q = iv.lo_q;
  }
  if (!iv.hi_inf) {
    out->has_upper = true;
    out->upper_p = iv.hi_p;
    out->upper_q = iv.hi_q;
  }
  ok = true;

cleanup:
  simp_bounds_scope_end_query(&scope);
  simp_bounds_scope_destroy(&scope);
  return ok;
}
