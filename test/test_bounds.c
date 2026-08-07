/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
/*
 * Unit tests for interval arithmetic (interval.h/c) and the bounds
 * module (bounds.h/c).  Exercises overflow widening, reciprocal edge
 * cases, intersection, assumption parsing, fork/restore, and
 * propagation through expression trees.
 */

#include "bounds.h"
#include "interval.h"
#include "node.h"
#include "simplify.h"

#include "test_check.h"
#include <ixsimpl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifndef INT64_MIN
#define INT64_MIN (-9223372036854775807LL - 1)
#endif
#ifndef INT64_MAX
#define INT64_MAX 9223372036854775807LL
#endif

static ixs_finite_domain_result
finite_domain_equivalent(ixs_facts *facts, ixs_node *lhs, ixs_node *rhs,
                         size_t *remaining_work);

/* ------------------------------------------------------------------ */
/*  Interval arithmetic                                               */
/* ------------------------------------------------------------------ */

static void test_iv_add_basic(void) {
  ixs_interval a = ixs_interval_range(1, 1, 5, 1);
  ixs_interval b = ixs_interval_range(10, 1, 20, 1);
  ixs_interval r = iv_add(a, b);
  CHECK(r.valid);
  CHECK(r.lo_p == 11 && r.lo_q == 1);
  CHECK(r.hi_p == 25 && r.hi_q == 1);
}

static void test_iv_add_overflow_widens(void) {
  /* (-inf, -70] + [0, 63]: lo overflows, should widen to -inf. */
  ixs_interval a = ixs_interval_range(INT64_MIN, 1, -70, 1);
  ixs_interval b = ixs_interval_range(0, 1, 63, 1);
  ixs_interval_set_lo_neg_inf(&a);
  ixs_interval r = iv_add(a, b);
  CHECK(r.valid);
  CHECK(r.lo_inf);
  CHECK(r.hi_p == -7 && r.hi_q == 1);
}

static void test_iv_add_pos_overflow_widens(void) {
  /* [70, +inf) + [0, 63]: hi overflows, should widen to +inf. */
  ixs_interval a = ixs_interval_range(70, 1, INT64_MAX, 1);
  ixs_interval b = ixs_interval_range(0, 1, 63, 1);
  ixs_interval_set_hi_pos_inf(&a);
  ixs_interval r = iv_add(a, b);
  CHECK(r.valid);
  CHECK(r.lo_p == 70 && r.lo_q == 1);
  CHECK(r.hi_inf);
}

static void test_iv_add_invalid(void) {
  ixs_interval a = ixs_interval_range(1, 1, 5, 1);
  ixs_interval b = ixs_interval_unknown();
  ixs_interval r = iv_add(a, b);
  CHECK(!r.valid);
  r = iv_add(b, a);
  CHECK(!r.valid);
}

static void test_iv_mul_const_basic(void) {
  ixs_interval a = ixs_interval_range(2, 1, 10, 1);
  ixs_interval r = iv_mul_const(a, 3, 1);
  CHECK(r.valid);
  CHECK(r.lo_p == 6 && r.lo_q == 1);
  CHECK(r.hi_p == 30 && r.hi_q == 1);
}

static void test_iv_mul_const_negative(void) {
  ixs_interval a = ixs_interval_range(2, 1, 10, 1);
  ixs_interval r = iv_mul_const(a, -1, 1);
  CHECK(r.valid);
  CHECK(r.lo_p == -10 && r.lo_q == 1);
  CHECK(r.hi_p == -2 && r.hi_q == 1);
}

static void test_iv_mul_const_zero(void) {
  ixs_interval a = ixs_interval_range(-100, 1, 100, 1);
  ixs_interval r = iv_mul_const(a, 0, 1);
  CHECK(r.valid);
  CHECK(r.lo_p == 0 && r.lo_q == 1);
  CHECK(r.hi_p == 0 && r.hi_q == 1);
}

static void test_iv_mul_const_overflow_widens(void) {
  /* [1, INT64_MAX] * 2 should overflow and widen to +inf. */
  ixs_interval a = ixs_interval_range(1, 1, INT64_MAX, 1);
  ixs_interval_set_hi_pos_inf(&a);
  ixs_interval r = iv_mul_const(a, 2, 1);
  CHECK(r.valid);
  CHECK(r.lo_p == 2 && r.lo_q == 1);
  CHECK(r.hi_inf);
}

static void test_iv_mul_const_neg_overflow_widens(void) {
  /* [INT64_MIN, -1] * 2: lo overflows negative. */
  ixs_interval a = ixs_interval_range(INT64_MIN, 1, -1, 1);
  ixs_interval_set_lo_neg_inf(&a);
  ixs_interval r = iv_mul_const(a, 2, 1);
  CHECK(r.valid);
  CHECK(r.lo_inf);
  CHECK(r.hi_p == -2 && r.hi_q == 1);
}

static void test_iv_mul_basic(void) {
  ixs_interval a = ixs_interval_range(2, 1, 4, 1);
  ixs_interval b = ixs_interval_range(3, 1, 5, 1);
  ixs_interval r = iv_mul(a, b);
  CHECK(r.valid);
  CHECK(r.lo_p == 6 && r.lo_q == 1);
  CHECK(r.hi_p == 20 && r.hi_q == 1);
}

static void test_iv_mul_mixed_sign(void) {
  ixs_interval a = ixs_interval_range(-3, 1, 4, 1);
  ixs_interval b = ixs_interval_range(-2, 1, 5, 1);
  ixs_interval r = iv_mul(a, b);
  CHECK(r.valid);
  /* min of {6, -15, -8, 20} = -15 */
  CHECK(ixs_rat_cmp(r.lo_p, r.lo_q, -15, 1) == 0);
  /* max of {6, -15, -8, 20} = 20 */
  CHECK(ixs_rat_cmp(r.hi_p, r.hi_q, 20, 1) == 0);
}

static void test_iv_mul_overflow_widens(void) {
  ixs_interval a = ixs_interval_range(1, 1, INT64_MAX, 1);
  ixs_interval b = ixs_interval_range(2, 1, 3, 1);
  ixs_interval_set_hi_pos_inf(&a);
  ixs_interval r = iv_mul(a, b);
  CHECK(r.valid);
  CHECK(r.hi_inf);
}

static void test_iv_mul_invalid(void) {
  ixs_interval a = ixs_interval_range(1, 1, 5, 1);
  ixs_interval b = ixs_interval_unknown();
  CHECK(!iv_mul(a, b).valid);
  CHECK(!iv_mul(b, a).valid);
}

static void test_iv_recip_basic(void) {
  /* 1/[2, 4] = [1/4, 1/2] */
  ixs_interval a = ixs_interval_range(2, 1, 4, 1);
  ixs_interval r = iv_recip(a);
  CHECK(r.valid);
  CHECK(ixs_rat_cmp(r.lo_p, r.lo_q, 1, 4) == 0);
  CHECK(ixs_rat_cmp(r.hi_p, r.hi_q, 1, 2) == 0);
}

static void test_iv_recip_unbounded(void) {
  /* 1/[3, +inf] = [0, 1/3] */
  ixs_interval a = ixs_interval_range(3, 1, INT64_MAX, 1);
  ixs_interval_set_hi_pos_inf(&a);
  ixs_interval r = iv_recip(a);
  CHECK(r.valid);
  CHECK(r.lo_p == 0 && r.lo_q == 1);
  CHECK(ixs_rat_cmp(r.hi_p, r.hi_q, 1, 3) == 0);
}

static void test_iv_recip_negative(void) {
  ixs_interval a = ixs_interval_range(-4, 1, -2, 1);
  ixs_interval r = iv_recip(a);
  CHECK(r.valid);
  CHECK(ixs_rat_cmp(r.lo_p, r.lo_q, -1, 2) == 0);
  CHECK(ixs_rat_cmp(r.hi_p, r.hi_q, -1, 4) == 0);

  a = ixs_interval_range(INT64_MIN, 1, -3, 1);
  ixs_interval_set_lo_neg_inf(&a);
  r = iv_recip(a);
  CHECK(r.valid);
  CHECK(ixs_rat_cmp(r.lo_p, r.lo_q, -1, 3) == 0);
  CHECK(r.hi_p == 0 && r.hi_q == 1);
}

static void test_iv_recip_contains_zero(void) {
  ixs_interval a = ixs_interval_range(-1, 1, 5, 1);
  CHECK(!iv_recip(a).valid);
  a = ixs_interval_range(-1, 1, 0, 1);
  CHECK(!iv_recip(a).valid);
  a = ixs_interval_range(0, 1, 1, 1);
  CHECK(!iv_recip(a).valid);
}

static void test_iv_recip_invalid(void) {
  CHECK(!iv_recip(ixs_interval_unknown()).valid);
}

static void test_iv_pow_sign_and_parity(void) {
  ixs_interval r = iv_pow(ixs_interval_range(0, 1, 15, 1), 2);
  CHECK(r.valid && r.lo_p == 0 && r.lo_q == 1);
  CHECK(r.hi_p == 225 && r.hi_q == 1);

  r = iv_pow(ixs_interval_range(-3, 1, 5, 1), 2);
  CHECK(r.valid && r.lo_p == 0 && r.lo_q == 1);
  CHECK(r.hi_p == 25 && r.hi_q == 1);

  r = iv_pow(ixs_interval_range(-5, 1, -3, 1), 3);
  CHECK(r.valid && r.lo_p == -125 && r.lo_q == 1);
  CHECK(r.hi_p == -27 && r.hi_q == 1);

  r = iv_pow(ixs_interval_range(-5, 1, -3, 1), 2);
  CHECK(r.valid && r.lo_p == 9 && r.lo_q == 1);
  CHECK(r.hi_p == 25 && r.hi_q == 1);

  r = iv_pow(ixs_interval_range(-3, 2, 5, 2), 2);
  CHECK(r.valid && r.lo_p == 0 && r.lo_q == 1);
  CHECK(r.hi_p == 25 && r.hi_q == 4);
}

static void test_iv_pow_limits_and_overflow(void) {
  ixs_interval a = ixs_interval_range(INT64_MIN, 1, -2, 1);
  ixs_interval r;
  ixs_interval_set_lo_neg_inf(&a);
  r = iv_pow(a, 2);
  CHECK(r.valid && r.lo_p == 4 && r.lo_q == 1);
  CHECK(r.hi_inf);

  r = iv_pow(ixs_interval_range(INT64_MAX - 1, 1, INT64_MAX, 1), 2);
  CHECK(r.valid && r.lo_p == 0 && r.lo_q == 1);
  CHECK(r.hi_inf);

  r = iv_pow(ixs_interval_range(-2, 1, 3, 1), 0);
  CHECK(r.valid && r.lo_p == 1 && r.hi_p == 1);
  CHECK(!iv_pow(ixs_interval_unknown(), 2).valid);
}

static void test_iv_intersect_basic(void) {
  ixs_interval a = ixs_interval_range(0, 1, 10, 1);
  ixs_interval b = ixs_interval_range(5, 1, 20, 1);
  ixs_interval r = iv_intersect(a, b);
  CHECK(r.valid);
  CHECK(r.lo_p == 5 && r.lo_q == 1);
  CHECK(r.hi_p == 10 && r.hi_q == 1);
}

static void test_iv_intersect_empty(void) {
  ixs_interval a = ixs_interval_range(0, 1, 3, 1);
  ixs_interval b = ixs_interval_range(5, 1, 10, 1);
  ixs_interval r = iv_intersect(a, b);
  CHECK(!r.valid);
}

static void test_iv_intersect_one_invalid(void) {
  ixs_interval a = ixs_interval_range(0, 1, 10, 1);
  ixs_interval b = ixs_interval_unknown();
  ixs_interval r = iv_intersect(a, b);
  CHECK(r.valid);
  CHECK(r.lo_p == 0 && r.lo_q == 1);
  CHECK(r.hi_p == 10 && r.hi_q == 1);

  r = iv_intersect(b, a);
  CHECK(r.valid);
  CHECK(r.lo_p == 0 && r.lo_q == 1);
  CHECK(r.hi_p == 10 && r.hi_q == 1);
}

static void test_iv_hull(void) {
  ixs_interval a = ixs_interval_range(-3, 1, 4, 1);
  ixs_interval b = ixs_interval_range(2, 1, 10, 1);
  ixs_interval r = iv_hull(a, b);
  CHECK(r.valid && r.lo_p == -3 && r.lo_q == 1);
  CHECK(r.hi_p == 10 && r.hi_q == 1);
  CHECK(!iv_hull(a, ixs_interval_unknown()).valid);
}

/* ------------------------------------------------------------------ */
/*  Bounds: assumption parsing                                        */
/* ------------------------------------------------------------------ */

static void test_bounds_sym_ge(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));

  ixs_node *x = ixs_sym(ctx, "x");
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)));
  ixs_interval iv = ixs_bounds_get(&b, x);
  CHECK(iv.valid);
  CHECK(ixs_rat_cmp(iv.lo_p, iv.lo_q, 0, 1) == 0);
  CHECK(iv.hi_inf);

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_sym_lt(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));

  ixs_node *x = ixs_sym(ctx, "x");
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 32)));
  ixs_interval iv = ixs_bounds_get(&b, x);
  CHECK(iv.valid);
  /* x < 32 for integer x -> x <= 31 */
  CHECK(ixs_rat_cmp(iv.hi_p, iv.hi_q, 31, 1) == 0);

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_sym_eq(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));

  ixs_node *x = ixs_sym(ctx, "x");
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, 7)));
  ixs_interval iv = ixs_bounds_get(&b, x);
  CHECK(iv.valid);
  CHECK(ixs_rat_cmp(iv.lo_p, iv.lo_q, 7, 1) == 0);
  CHECK(ixs_rat_cmp(iv.hi_p, iv.hi_q, 7, 1) == 0);

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_assumption_invalidates_cache(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));

  ixs_node *x = ixs_sym(ctx, "x");
  ixs_interval iv = ixs_bounds_get(&b, x);
  CHECK(!iv.valid);

  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, 5)));
  iv = ixs_bounds_get(&b, x);
  CHECK(iv.valid);
  CHECK(iv.lo_p == 5 && iv.lo_q == 1);
  CHECK(iv.hi_p == 5 && iv.hi_q == 1);

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_empty_cache_invalidation(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds parent;
  ixs_bounds child;
  ixs_bounds expressions;
  ixs_interval zero = ixs_interval_exact(0, 1);
  ixs_interval one = ixs_interval_exact(1, 1);
  ixs_node *x = ixs_sym(ctx, "empty_cache_x");

  CHECK(ixs_bounds_init(&parent, ixs_test_scratch(ctx)));
  ixs_bounds_add_assumption(&parent,
                            ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)));
  CHECK(!parent.empty_cache_valid);
  CHECK(!ixs_bounds_has_empty(&parent));
  CHECK(parent.empty_cache_valid && !parent.empty_cache_value);
  CHECK(!ixs_bounds_has_empty(&parent));

  CHECK(ixs_bounds_fork(&child, &parent));
  CHECK(!child.empty_cache_valid);
  CHECK(!ixs_bounds_has_empty(&child));
  ixs_bounds_add_assumption(&child,
                            ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 0)));
  CHECK(!child.empty_cache_valid);
  CHECK(ixs_bounds_has_empty(&child));
  CHECK(child.empty_cache_valid && child.empty_cache_value);
  CHECK(parent.empty_cache_valid && !ixs_bounds_has_empty(&parent));

  ixs_bounds_destroy(&child);
  ixs_bounds_destroy(&parent);

  CHECK(ixs_bounds_init(&expressions, ixs_test_scratch(ctx)));
  ixs_bounds_add_expr(&expressions, x, zero);
  CHECK(!ixs_bounds_has_empty(&expressions));
  CHECK(expressions.empty_cache_valid);
  ixs_bounds_add_expr(&expressions, x, one);
  CHECK(!expressions.empty_cache_valid);
  CHECK(ixs_bounds_has_empty(&expressions));
  ixs_bounds_destroy(&expressions);

  ixs_ctx_destroy(ctx);
}

static void test_bounds_two_sided(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));

  ixs_node *x = ixs_sym(ctx, "x");
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)));
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 16)));
  ixs_interval iv = ixs_bounds_get(&b, x);
  CHECK(iv.valid);
  CHECK(ixs_rat_cmp(iv.lo_p, iv.lo_q, 0, 1) == 0);
  CHECK(ixs_rat_cmp(iv.hi_p, iv.hi_q, 15, 1) == 0);

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_sym_gt(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));

  ixs_node *x = ixs_sym(ctx, "x");
  /* x > 5  =>  x >= 6 for integer x */
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, x, IXS_CMP_GT, ixs_int(ctx, 5)));
  ixs_interval iv = ixs_bounds_get(&b, x);
  CHECK(iv.valid);
  CHECK(ixs_rat_cmp(iv.lo_p, iv.lo_q, 6, 1) == 0);

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

/* ------------------------------------------------------------------ */
/*  Bounds: propagation through expressions                           */
/* ------------------------------------------------------------------ */

static void test_bounds_propagate_add(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));

  ixs_node *x = ixs_sym(ctx, "x");
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)));
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 10)));

  ixs_node *expr = ixs_add(ctx, x, ixs_int(ctx, 5));
  ixs_interval iv = ixs_bounds_get(&b, expr);
  CHECK(iv.valid);
  CHECK(ixs_rat_cmp(iv.lo_p, iv.lo_q, 5, 1) == 0);
  CHECK(ixs_rat_cmp(iv.hi_p, iv.hi_q, 15, 1) == 0);

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_propagate_mul(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));

  ixs_node *x = ixs_sym(ctx, "x");
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 2)));
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 8)));

  ixs_node *expr = ixs_mul(ctx, ixs_int(ctx, 3), x);
  ixs_interval iv = ixs_bounds_get(&b, expr);
  CHECK(iv.valid);
  CHECK(ixs_rat_cmp(iv.lo_p, iv.lo_q, 6, 1) == 0);
  CHECK(ixs_rat_cmp(iv.hi_p, iv.hi_q, 24, 1) == 0);

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_propagate_mod(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));

  ixs_node *x = ixs_sym(ctx, "x");
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)));

  /* Mod(x, 16) in [0, 15] */
  ixs_node *expr = ixs_mod(ctx, x, ixs_int(ctx, 16));
  ixs_interval iv = ixs_bounds_get(&b, expr);
  CHECK(iv.valid);
  CHECK(ixs_rat_cmp(iv.lo_p, iv.lo_q, 0, 1) == 0);
  CHECK(ixs_rat_cmp(iv.hi_p, iv.hi_q, 15, 1) == 0);

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_propagate_mod_tight(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));

  ixs_node *x = ixs_sym(ctx, "x");
  /* x in [3, 7], Mod(x, 16) should tighten to [3, 7] since 7 < 16. */
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 3)));
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 7)));

  ixs_node *expr = ixs_mod(ctx, x, ixs_int(ctx, 16));
  ixs_interval iv = ixs_bounds_get(&b, expr);
  CHECK(iv.valid);
  CHECK(ixs_rat_cmp(iv.lo_p, iv.lo_q, 3, 1) == 0);
  CHECK(ixs_rat_cmp(iv.hi_p, iv.hi_q, 7, 1) == 0);

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_propagate_floor(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));

  ixs_node *x = ixs_sym(ctx, "x");
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)));
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 15)));

  /* floor(x/4) in [0, 3] */
  ixs_node *expr = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 4)));
  ixs_interval iv = ixs_bounds_get(&b, expr);
  CHECK(iv.valid);
  CHECK(ixs_rat_cmp(iv.lo_p, iv.lo_q, 0, 1) == 0);
  CHECK(ixs_rat_cmp(iv.hi_p, iv.hi_q, 3, 1) == 0);

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

/* ------------------------------------------------------------------ */
/*  Bounds: unknown symbol                                            */
/* ------------------------------------------------------------------ */

static void test_bounds_unknown_sym(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));

  ixs_node *y = ixs_sym(ctx, "y");
  ixs_interval iv = ixs_bounds_get(&b, y);
  CHECK(!iv.valid);

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

/* ------------------------------------------------------------------ */
/*  Bounds: fork preserves state                                      */
/* ------------------------------------------------------------------ */

static void test_bounds_fork(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));

  ixs_node *x = ixs_sym(ctx, "x");
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)));
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 100)));
  CHECK(b.difference_vars == NULL);
  CHECK(b.difference_var_cap == 0);

  ixs_bounds child;
  CHECK(ixs_bounds_fork(&child, &b));
  CHECK(child.var_index != b.var_index);
  CHECK(child.var_index_cap == b.var_index_cap);

  /* Child inherits parent bounds. */
  ixs_interval iv = ixs_bounds_get(&child, x);
  CHECK(iv.valid);
  CHECK(ixs_rat_cmp(iv.lo_p, iv.lo_q, 0, 1) == 0);
  CHECK(ixs_rat_cmp(iv.hi_p, iv.hi_q, 100, 1) == 0);

  /* Tighten in child doesn't affect parent. */
  ixs_bounds_add_assumption(&child,
                            ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 50)));
  ixs_interval child_iv = ixs_bounds_get(&child, x);
  CHECK(ixs_rat_cmp(child_iv.hi_p, child_iv.hi_q, 50, 1) == 0);

  ixs_interval parent_iv = ixs_bounds_get(&b, x);
  CHECK(ixs_rat_cmp(parent_iv.hi_p, parent_iv.hi_q, 100, 1) == 0);

  ixs_bounds_destroy(&child);
  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_expr_index_fork(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds parent;
  ixs_bounds child;
  ixs_interval parent_iv;
  ixs_interval child_iv;
  ixs_node *expr = ixs_sym(ctx, "expr_index_fork");
  ixs_node *extra = ixs_sym(ctx, "expr_index_fork_extra");
  size_t parent_count;

  CHECK(ixs_bounds_init(&parent, ixs_test_scratch(ctx)));
  ixs_bounds_add_expr(&parent, expr, ixs_interval_range(0, 1, 100, 1));
  CHECK(!parent.oom);
  CHECK(parent.expr_index != NULL);
  parent_count = parent.nexprs;

  CHECK(ixs_bounds_fork(&child, &parent));
  CHECK(child.expr_index != parent.expr_index);
  CHECK(child.expr_index_cap == parent.expr_index_cap);

  ixs_bounds_add_expr(&child, expr, ixs_interval_range(10, 1, 20, 1));
  ixs_bounds_add_expr(&child, extra, ixs_interval_exact(7, 1));
  CHECK(!child.oom);
  CHECK(child.nexprs == parent_count + 1u);

  child_iv = ixs_bounds_get(&child, expr);
  CHECK(child_iv.valid);
  CHECK(child_iv.lo_p == 10 && child_iv.lo_q == 1);
  CHECK(child_iv.hi_p == 20 && child_iv.hi_q == 1);
  parent_iv = ixs_bounds_get(&parent, expr);
  CHECK(parent_iv.valid);
  CHECK(parent_iv.lo_p == 0 && parent_iv.lo_q == 1);
  CHECK(parent_iv.hi_p == 100 && parent_iv.hi_q == 1);
  CHECK(!ixs_bounds_get(&parent, extra).valid);
  CHECK(parent.nexprs == parent_count);

  ixs_bounds_destroy(&child);
  ixs_bounds_destroy(&parent);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_difference_fork(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds parent;
  ixs_bounds child;
  ixs_node *x = ixs_sym(ctx, "difference_fork_x");
  ixs_node *y = ixs_sym(ctx, "difference_fork_y");
  ixs_node *z = ixs_sym(ctx, "difference_fork_z");
  ixs_interval parent_x;
  ixs_interval child_x;
  size_t parent_edges;

  CHECK(ixs_bounds_init(&parent, ixs_test_scratch(ctx)));
  CHECK(ixs_bounds_add_assumption(
      &parent, ixs_cmp(ctx, ixs_sub(ctx, x, y), IXS_CMP_LE, ixs_int(ctx, 2))));
  CHECK(ixs_bounds_add_assumption(
      &parent, ixs_cmp(ctx, y, IXS_CMP_LE, ixs_int(ctx, 10))));
  CHECK(!parent.oom);
  CHECK(parent.ndifferences == 1);
  CHECK(parent.ndifference_vars == 2);
  parent_edges = parent.ndifferences;
  parent_x = ixs_bounds_get(&parent, x);
  CHECK(parent_x.valid && !parent_x.hi_inf && parent_x.hi_p == 12 &&
        parent_x.hi_q == 1);

  CHECK(ixs_bounds_fork(&child, &parent));
  CHECK(child.difference_index != parent.difference_index);
  CHECK(child.difference_vars != parent.difference_vars);
  CHECK(child.ndifferences == parent.ndifferences);
  CHECK(child.ndifference_vars == parent.ndifference_vars);
  CHECK(child.difference_var_cap == parent.difference_var_cap);
  CHECK(child.difference_epoch == parent.difference_epoch);
  CHECK(child.difference_vars[0].incoming ==
        parent.difference_vars[0].incoming);
  CHECK(child.difference_vars[0].outgoing ==
        parent.difference_vars[0].outgoing);

  CHECK(ixs_bounds_add_assumption(
      &child, ixs_cmp(ctx, y, IXS_CMP_LE, ixs_int(ctx, 5))));
  child_x = ixs_bounds_get(&child, x);
  CHECK(child_x.valid && !child_x.hi_inf && child_x.hi_p == 7 &&
        child_x.hi_q == 1);
  parent_x = ixs_bounds_get(&parent, x);
  CHECK(parent_x.valid && !parent_x.hi_inf && parent_x.hi_p == 12 &&
        parent_x.hi_q == 1);

  CHECK(ixs_bounds_add_assumption(
      &child, ixs_cmp(ctx, ixs_sub(ctx, z, x), IXS_CMP_LE, ixs_int(ctx, 1))));
  CHECK(child.ndifferences == parent_edges + 1u);
  CHECK(child.ndifference_vars == 3);
  CHECK(parent.ndifferences == parent_edges);
  CHECK(parent.ndifference_vars == 2);
  CHECK(parent.difference_epoch != child.difference_epoch);
  CHECK(!ixs_bounds_get(&parent, z).valid);

  ixs_bounds_destroy(&child);
  ixs_bounds_destroy(&parent);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_exact_fork(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_session_binding binding;
  ixs_bounds parent;
  ixs_bounds child;
  ixs_node *x = ixs_sym(ctx, "exact_fork_x");
  ixs_node *y = ixs_sym(ctx, "exact_fork_y");
  ixs_node *z = ixs_sym(ctx, "exact_fork_z");
  ixs_interval range;

  CHECK(ixs_session_bind(&binding, IXS_TEST_SESSION(ctx)) == ctx);
  CHECK(ixs_bounds_init_ctx(&parent, ctx, &ctx->scratch));
  CHECK(ixs_bounds_add_assumption(
      &parent, ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_add(ctx, y, ixs_int(ctx, 3)))));
  CHECK(!parent.oom && !parent.contradiction);
  CHECK(parent.nexact_vars == 2);
  CHECK(parent.exact_vars != NULL && parent.exact_index != NULL);

  CHECK(ixs_bounds_fork(&child, &parent));
  CHECK(child.exact_vars != parent.exact_vars);
  CHECK(child.exact_index != parent.exact_index);
  CHECK(child.nexact_vars == parent.nexact_vars);
  CHECK(child.exact_var_cap == parent.exact_var_cap);
  CHECK(child.exact_index_cap == parent.exact_index_cap);

  CHECK(ixs_bounds_add_assumption(
      &child, ixs_cmp(ctx, y, IXS_CMP_EQ, ixs_add(ctx, z, ixs_int(ctx, 4)))));
  range = ixs_bounds_get(&child, ixs_sub(ctx, x, z));
  CHECK(range.valid && !range.lo_inf && !range.hi_inf);
  CHECK(range.lo_p == 7 && range.lo_q == 1);
  CHECK(range.hi_p == 7 && range.hi_q == 1);
  CHECK(parent.nexact_vars == 2);
  CHECK(!ixs_bounds_get(&parent, z).valid);

  ixs_bounds_destroy(&child);
  ixs_bounds_destroy(&parent);
  ixs_session_unbind(&binding);
  ixs_ctx_destroy(ctx);
}

/* ------------------------------------------------------------------ */
/*  Bounds: modular congruence                                        */
/* ------------------------------------------------------------------ */

static void test_bounds_modrem(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));

  ixs_node *x = ixs_sym(ctx, "x");
  /* Mod(x, 8) == 3 */
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 8)),
                                        IXS_CMP_EQ, ixs_int(ctx, 3)));

  int64_t mod, rem;
  CHECK(ixs_bounds_get_modrem(&b, x->u.name, &mod, &rem));
  CHECK(mod == 8);
  CHECK(rem == 3);

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_modrem_zero(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));

  ixs_node *x = ixs_sym(ctx, "x");
  /* Mod(x, 4) == 0 */
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 4)),
                                        IXS_CMP_EQ, ixs_int(ctx, 0)));

  int64_t mod, rem;
  CHECK(ixs_bounds_get_modrem(&b, x->u.name, &mod, &rem));
  CHECK(mod == 4);
  CHECK(rem == 0);

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_no_modrem(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));

  int64_t mod, rem;
  ixs_node *x = ixs_sym(ctx, "x");
  CHECK(!ixs_bounds_get_modrem(&b, x->u.name, &mod, &rem));

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

/* ------------------------------------------------------------------ */
/*  Bounds: bitwise facts                                             */
/* ------------------------------------------------------------------ */

static void test_bounds_bitfacts_pow2(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  ixs_bitfacts bits;
  ixs_interval iv;
  ixs_node *d = ixs_sym(ctx, "d");
  ixs_node *dm1 = ixs_sub(ctx, d, ixs_int(ctx, 1));
  ixs_node *pow2 =
      ixs_cmp(ctx, ixs_and(ctx, d, dm1), IXS_CMP_EQ, ixs_int(ctx, 0));

  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));
  ixs_bounds_add_assumption(&b, pow2);

  CHECK(ixs_bounds_get_bitfacts(&b, d, &bits));
  CHECK(bits.pow2 == IXS_POW2_OR_ZERO);
  CHECK(ixs_bounds_is_pow2_or_zero(&b, d));
  CHECK(!ixs_bounds_is_pow2_positive(&b, d));
  iv = ixs_bounds_get(&b, d);
  CHECK(iv.valid);
  CHECK(!iv.lo_inf);
  CHECK(iv.lo_p == 0 && iv.lo_q == 1);

  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, d, IXS_CMP_GT, ixs_int(ctx, 0)));
  CHECK(ixs_bounds_get_bitfacts(&b, d, &bits));
  CHECK(bits.pow2 == IXS_POW2_POSITIVE);
  CHECK(ixs_bounds_is_pow2_positive(&b, d));

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_bitfacts_masks(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  ixs_bitfacts bits;
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");

  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));

  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, ixs_and(ctx, x, ixs_int(ctx, 15)),
                                        IXS_CMP_EQ, ixs_int(ctx, 5)));
  CHECK(ixs_bounds_get_bitfacts(&b, x, &bits));
  CHECK((bits.known_one & 15u) == 5u);
  CHECK((bits.known_zero & 15u) == 10u);

  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, ixs_or(ctx, y, ixs_int(ctx, 3)),
                                        IXS_CMP_EQ, ixs_int(ctx, 7)));
  CHECK(ixs_bounds_get_bitfacts(&b, y, &bits));
  CHECK((bits.known_one & 7u) == 4u);
  CHECK((bits.known_zero & ~(uint64_t)7) == ~(uint64_t)7);

  ixs_bounds_add_assumption(
      &b, ixs_cmp(ctx, ixs_or(ctx, x, ixs_int(ctx, 8)), IXS_CMP_EQ, x));
  CHECK(ixs_bounds_get_bitfacts(&b, x, &bits));
  CHECK((bits.known_one & 8u) == 8u);

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_bitfacts_arithmetic(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  ixs_bitfacts bits;
  ixs_node *x = ixs_sym(ctx, "x");

  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));

  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, ixs_and(ctx, x, ixs_int(ctx, 15)),
                                        IXS_CMP_EQ, ixs_int(ctx, 5)));

  CHECK(ixs_bounds_get_bitfacts(&b, ixs_mod(ctx, x, ixs_int(ctx, 8)), &bits));
  CHECK((bits.known_one & 7u) == 5u);
  CHECK((bits.known_zero & 7u) == 2u);
  CHECK((bits.known_zero & ~(uint64_t)7) == ~(uint64_t)7);

  CHECK(ixs_bounds_get_bitfacts(&b, ixs_add(ctx, x, ixs_int(ctx, 3)), &bits));
  CHECK((bits.known_zero & 7u) == 7u);

  CHECK(ixs_bounds_get_bitfacts(
      &b, ixs_mul(ctx, ixs_int(ctx, 8), ixs_add(ctx, x, ixs_int(ctx, 1))),
      &bits));
  CHECK((bits.known_zero & 7u) == 7u);

  CHECK(ixs_bounds_get_bitfacts(
      &b,
      ixs_floor(ctx, ixs_div(ctx, ixs_mod(ctx, x, ixs_int(ctx, 64)),
                             ixs_int(ctx, 16))),
      &bits));
  CHECK((bits.known_zero & ~(uint64_t)3) == ~(uint64_t)3);

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_bitfacts_mod_requires_integer_dividend(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *mod =
      ixs_mod(ctx, ixs_div(ctx, x, ixs_int(ctx, 2)), ixs_int(ctx, 1));

  CHECK(ixs_node_tag(mod) == IXS_MOD);
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));
  CHECK(!ixs_bounds_is_known_divisible(&b, mod, 2));

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_bitfacts_mul_requires_integer_product(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *frac = ixs_add(ctx, y, ixs_div(ctx, x, ixs_int(ctx, 4)));
  ixs_node *prod = ixs_mul(ctx, ixs_int(ctx, 2), frac);
  ixs_node *query = ixs_cmp(ctx, ixs_mod(ctx, prod, ixs_int(ctx, 2)),
                            IXS_CMP_EQ, ixs_int(ctx, 0));

  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));
  CHECK(!ixs_bounds_is_known_divisible(&b, prod, 2));
  CHECK(ixs_check(ctx, query, NULL, 0) == IXS_CHECK_UNKNOWN);

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_extrema_divisibility(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *six_x = ixs_mul(ctx, ixs_int(ctx, 6), x);
  ixs_node *nine_y = ixs_mul(ctx, ixs_int(ctx, 9), y);
  ixs_node *ten_y = ixs_mul(ctx, ixs_int(ctx, 10), y);
  ixs_node *twelve = ixs_int(ctx, 12);
  ixs_node *divisible[3] = {six_x, nine_y, twelve};
  ixs_node *mixed[3] = {six_x, ten_y, twelve};

  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));
  CHECK(ixs_bounds_is_known_divisible(&b, ixs_max(ctx, six_x, nine_y), 3));
  CHECK(ixs_bounds_is_known_divisible(&b, ixs_min(ctx, six_x, nine_y), 3));
  CHECK(!ixs_bounds_is_known_divisible(&b, ixs_max(ctx, six_x, ten_y), 3));
  CHECK(!ixs_bounds_is_known_divisible(&b, ixs_min(ctx, six_x, ten_y), 3));
  CHECK(ixs_bounds_is_known_divisible(&b, ixs_max_many(ctx, 3, divisible), 3));
  CHECK(ixs_bounds_is_known_divisible(&b, ixs_min_many(ctx, 3, divisible), 3));
  CHECK(!ixs_bounds_is_known_divisible(&b, ixs_max_many(ctx, 3, mixed), 3));
  CHECK(!ixs_bounds_is_known_divisible(&b, ixs_min_many(ctx, 3, mixed), 3));

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_bitfacts_contradiction(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  ixs_node *x = ixs_sym(ctx, "x");

  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, ixs_and(ctx, x, ixs_int(ctx, 1)),
                                        IXS_CMP_EQ, ixs_int(ctx, 1)));
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, ixs_and(ctx, x, ixs_int(ctx, 1)),
                                        IXS_CMP_EQ, ixs_int(ctx, 0)));
  CHECK(ixs_bounds_has_empty(&b));

  ixs_bounds_destroy(&b);
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, 5)));
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, ixs_and(ctx, x, ixs_int(ctx, 1)),
                                        IXS_CMP_EQ, ixs_int(ctx, 0)));
  CHECK(ixs_bounds_has_empty(&b));

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void check_bounds_mutual_query_budget_and_cache(const char *prefix,
                                                       unsigned noise) {
  ixs_ctx *ctx = ixs_ctx_create();
  char name[96];
  ixs_node *x;
  ixs_node *value;
  ixs_node *modulus = ixs_int(ctx, INT64_C(4294967296));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_range_result range;
  size_t visits;
  size_t stride_visits;
  size_t range_pw_case_visits;
  size_t range_pw_limit_blocks;
  size_t cache_hits;
  size_t cycle_blocks;
  size_t limit_blocks;
  size_t active_count;
  size_t nesting;
  unsigned i;

  for (i = 0; i < noise; i++) {
    snprintf(name, sizeof(name), "%s_allocation_noise_%u", prefix, i);
    CHECK(ixs_sym(ctx, name) != NULL);
  }
  snprintf(name, sizeof(name), "%s_bounded_query_x", prefix);
  x = ixs_sym(ctx, name);
  value = x;
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 256)),
                                      IXS_CMP_EQ, ixs_int(ctx, 0))));
  for (i = 0; i < 12; i++) {
    ixs_node *values[2] = {ixs_mod(ctx, value, modulus), value};
    ixs_node *conditions[2];
    snprintf(name, sizeof(name), "%s_bounded_query_cond_%u", prefix, i);
    conditions[0] =
        ixs_cmp(ctx, ixs_sym(ctx, name), IXS_CMP_GT, ixs_int(ctx, 0));
    conditions[1] = ixs_true(ctx);
    value = ixs_pw(ctx, 2, values, conditions);
  }

  CHECK(test_ixs_range_facts(facts, ixs_mod(ctx, value, modulus), &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == INT64_C(4294967040) &&
        range.upper_q == 1);
  ixs_bounds_query_stats(&facts->bounds, &visits, &stride_visits,
                         &range_pw_case_visits, &range_pw_limit_blocks,
                         &cache_hits, &cycle_blocks, &limit_blocks,
                         &active_count, &nesting);
  CHECK(visits > 0 && visits < 256u);
  /* Stride queries share this counter and cache.  Without memoization, the
   * shared Piecewise DAG above doubles the stride work at every level. */
  CHECK(stride_visits > 0 && stride_visits < 256u);
  CHECK(range_pw_case_visits == 0);
  CHECK(range_pw_limit_blocks == 0);
  CHECK(cache_hits > 0);
  CHECK(cycle_blocks == 0);
  CHECK(limit_blocks == 0);
  CHECK(active_count == 0 && nesting == 0);

  /* Fact simplification is Wave's primary entry.  Its outer hold must cover
   * direct interval calls made by simplifier rules, not just public range
   * queries. */
  value = test_ixs_simplify_facts(facts, ixs_mod(ctx, value, modulus));
  CHECK(value != NULL);
  ixs_bounds_query_stats(&facts->bounds, &visits, &stride_visits,
                         &range_pw_case_visits, &range_pw_limit_blocks,
                         &cache_hits, &cycle_blocks, &limit_blocks,
                         &active_count, &nesting);
  CHECK(visits > 0);
  CHECK(active_count == 0 && nesting == 0);

  CHECK(ixs_bounds_query_cycle_probe(&facts->bounds, x));
  ixs_bounds_query_stats(&facts->bounds, &visits, &stride_visits,
                         &range_pw_case_visits, &range_pw_limit_blocks,
                         &cache_hits, &cycle_blocks, &limit_blocks,
                         &active_count, &nesting);
  /* Visits count work entries/cache misses.  The re-entry finds the
   * incomplete memo slot in O(1) and is therefore not a second visit. */
  CHECK(visits == 1);
  CHECK(cycle_blocks == 1);
  CHECK(range_pw_case_visits == 0);
  CHECK(range_pw_limit_blocks == 0);
  CHECK(limit_blocks == 0);
  CHECK(active_count == 0 && nesting == 0);

  ixs_ctx_destroy(ctx);
}

static void test_bounds_mutual_query_budget_and_cache(void) {
  check_bounds_mutual_query_budget_and_cache("short", 0);
  check_bounds_mutual_query_budget_and_cache(
      "pointer_layout_shifted_by_a_long_symbol_prefix", 1);
  check_bounds_mutual_query_budget_and_cache("many_allocations", 17);
}

static void check_bounds_piecewise_congruence_depth_envelope(unsigned depth) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "piecewise_depth_x");
  ixs_node *value = x;
  ixs_node *modulus = ixs_int(ctx, INT64_C(4294967296));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_range_result range;
  ixs_range_query_result query_result;
  size_t visits;
  size_t stride_visits;
  size_t range_pw_case_visits;
  size_t range_pw_limit_blocks;
  size_t cache_hits;
  size_t cycle_blocks;
  size_t limit_blocks;
  size_t active_count;
  size_t nesting;
  unsigned i;

  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 256)),
                                      IXS_CMP_EQ, ixs_int(ctx, 0))));
  for (i = 0; i < depth; i++) {
    char name[64];
    ixs_node *values[2] = {ixs_mod(ctx, value, modulus), value};
    ixs_node *conditions[2];
    snprintf(name, sizeof(name), "piecewise_depth_cond_%u", i);
    conditions[0] =
        ixs_cmp(ctx, ixs_sym(ctx, name), IXS_CMP_GT, ixs_int(ctx, 0));
    conditions[1] = ixs_true(ctx);
    value = ixs_pw(ctx, 2, values, conditions);
  }

  query_result = ixs_range_facts(facts, ixs_mod(ctx, value, modulus));
  CHECK(query_result.status == IXS_FACT_QUERY_COMPLETE &&
        query_result.available);
  range = query_result.range;
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == INT64_C(4294967040) &&
        range.upper_q == 1);
  ixs_bounds_query_stats(&facts->bounds, &visits, &stride_visits,
                         &range_pw_case_visits, &range_pw_limit_blocks,
                         &cache_hits, &cycle_blocks, &limit_blocks,
                         &active_count, &nesting);
  CHECK(visits > 0 && stride_visits > 0 && cache_hits > 0);
  CHECK(cycle_blocks == 0);
  CHECK(limit_blocks == 0);
  CHECK(range_pw_case_visits == 0);
  CHECK(range_pw_limit_blocks == 0);
  CHECK(active_count == 0 && nesting == 0);

  ixs_ctx_destroy(ctx);
}

static void test_bounds_piecewise_congruence_depth_envelope(void) {
  check_bounds_piecewise_congruence_depth_envelope(16);
  check_bounds_piecewise_congruence_depth_envelope(31);
  check_bounds_piecewise_congruence_depth_envelope(32);
  check_bounds_piecewise_congruence_depth_envelope(48);
}

static void test_bounds_piecewise_range_with_unrelated_congruence(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *y = ixs_sym(ctx, "piecewise_range_y");
  ixs_node *inner_values[2] = {ixs_int(ctx, 0), ixs_int(ctx, 3)};
  ixs_node *inner_conditions[2] = {ixs_cmp(ctx,
                                           ixs_sym(ctx, "piecewise_range_c0"),
                                           IXS_CMP_GT, ixs_int(ctx, 0)),
                                   ixs_true(ctx)};
  ixs_node *inner = ixs_pw(ctx, 2, inner_values, inner_conditions);
  ixs_node *outer_values[2] = {ixs_mod(ctx, inner, ixs_int(ctx, 1000)), inner};
  ixs_node *outer_conditions[2] = {ixs_cmp(ctx,
                                           ixs_sym(ctx, "piecewise_range_c1"),
                                           IXS_CMP_GT, ixs_int(ctx, 0)),
                                   ixs_true(ctx)};
  ixs_node *outer = ixs_pw(ctx, 2, outer_values, outer_conditions);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_range_result range;

  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, ixs_mod(ctx, y, ixs_int(ctx, 2)),
                                      IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(test_ixs_range_facts(facts, ixs_mod(ctx, outer, ixs_int(ctx, 1000)),
                             &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 3 && range.upper_q == 1);

  ixs_ctx_destroy(ctx);
}

static void test_bounds_flat_piecewise_keeps_case_limit(void) {
  enum { FLAT_CASES = 1024 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "flat_piecewise_x");
  ixs_node *y = ixs_sym(ctx, "flat_piecewise_y");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *flat;
  ixs_pwcase cases[FLAT_CASES];
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_range_result range;
  size_t visits;
  size_t stride_visits;
  size_t range_pw_case_visits;
  size_t range_pw_limit_blocks;
  size_t cache_hits;
  size_t cycle_blocks;
  size_t limit_blocks;
  size_t active_count;
  size_t nesting;
  uint32_t i;

  for (i = 0; i < FLAT_CASES; i++) {
    cases[i].value = i + 1u == FLAT_CASES ? ixs_int(ctx, 7) : zero;
    cases[i].cond = i + 1u == FLAT_CASES ? ixs_true(ctx) : ixs_false(ctx);
  }
  flat = ixs_node_pw(ctx, FLAT_CASES, cases);
  CHECK(flat && !ixs_node_contains_nested_piecewise(flat));
  CHECK(ixs_facts_assume_pred(facts, ixs_cmp(ctx, x, IXS_CMP_EQ, flat)));
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, ixs_mod(ctx, y, ixs_int(ctx, 2)), IXS_CMP_EQ, zero)));
  CHECK(test_ixs_range_facts(facts, x, &range));
  CHECK(range.has_lower && range.lower_p == 7 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 7 && range.upper_q == 1);
  ixs_bounds_query_stats(&facts->bounds, &visits, &stride_visits,
                         &range_pw_case_visits, &range_pw_limit_blocks,
                         &cache_hits, &cycle_blocks, &limit_blocks,
                         &active_count, &nesting);
  CHECK(range_pw_case_visits == 0 && range_pw_limit_blocks == 0);
  CHECK(active_count == 0 && nesting == 0);

  ixs_ctx_destroy(ctx);
}

static void test_bounds_query_state_lazy_oom_and_lifecycle(void) {
  ixs_ctx *unused = ixs_ctx_create();
  ixs_ctx *ctx;
  ixs_facts *facts;
  ixs_node *x;
  ixs_node *value;
  ixs_node *modulus;
  ixs_node *query;
  ixs_range_result range;
  unsigned i;

  CHECK(unused != NULL && unused->bounds_query_state == NULL);
  ixs_ctx_destroy(unused);

  ctx = ixs_ctx_create();
  x = ixs_sym(ctx, "lazy_query_state_x");
  value = x;
  modulus = ixs_int(ctx, 1024);
  facts = ixs_facts_create(ctx);
  for (i = 0; i < 2; i++) {
    char name[32];
    ixs_node *values[2] = {ixs_mod(ctx, value, modulus), value};
    ixs_node *conditions[2];
    snprintf(name, sizeof(name), "lazy_query_cond_%u", i);
    conditions[0] =
        ixs_cmp(ctx, ixs_sym(ctx, name), IXS_CMP_GT, ixs_int(ctx, 0));
    conditions[1] = ixs_true(ctx);
    value = ixs_pw(ctx, 2, values, conditions);
  }

  query = ixs_mod(ctx, value, modulus);
  CHECK(query != NULL);
  CHECK(ctx->bounds_query_state == NULL && facts->bounds.query_state == NULL);
  ixs_arena_set_fail_after(&ctx->arena, 0);
  CHECK(!test_ixs_range_facts(facts, query, &range));
  ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
  CHECK(ctx->bounds_query_state == NULL && facts->bounds.query_state == NULL);
  CHECK(!facts->bounds.oom);

  facts->bounds.oom = false;
  CHECK(test_ixs_range_facts(facts, query, &range));
  CHECK(ctx->bounds_query_state != NULL && facts->bounds.query_state != NULL);
  CHECK(facts->bounds.query_tracking_depth == 0);

  ixs_ctx_destroy(ctx);
}

static ixs_node *make_nested_query_root(ixs_ctx *ctx, const char *prefix) {
  char first_name[96];
  char second_name[96];
  ixs_pwcase inner_cases[2];
  ixs_pwcase outer_cases[2];
  ixs_node *inner;

  snprintf(first_name, sizeof(first_name), "%s_first", prefix);
  snprintf(second_name, sizeof(second_name), "%s_second", prefix);
  inner_cases[0].value = ixs_int(ctx, 1);
  inner_cases[0].cond =
      ixs_cmp(ctx, ixs_sym(ctx, first_name), IXS_CMP_GT, ixs_int(ctx, 0));
  inner_cases[1].value = ixs_int(ctx, 2);
  inner_cases[1].cond = ixs_true(ctx);
  inner = ixs_node_pw(ctx, 2, inner_cases);
  outer_cases[0].value = inner;
  outer_cases[0].cond =
      ixs_cmp(ctx, ixs_sym(ctx, second_name), IXS_CMP_GT, ixs_int(ctx, 0));
  outer_cases[1].value = ixs_int(ctx, 3);
  outer_cases[1].cond = ixs_true(ctx);
  return inner ? ixs_node_pw(ctx, 2, outer_cases) : NULL;
}

static ixs_node *make_nested_boolean_query_root(ixs_ctx *ctx) {
  ixs_pwcase inner_cases[2];
  ixs_pwcase outer_cases[2];
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *inner;

  inner_cases[0].value =
      ixs_cmp(ctx, ixs_sym(ctx, "predicate_nested_x"), IXS_CMP_GE, zero);
  inner_cases[0].cond =
      ixs_cmp(ctx, ixs_sym(ctx, "predicate_nested_c"), IXS_CMP_GT, zero);
  inner_cases[1].value =
      ixs_cmp(ctx, ixs_sym(ctx, "predicate_nested_y"), IXS_CMP_GE, zero);
  inner_cases[1].cond = ixs_true(ctx);
  inner = ixs_node_pw(ctx, 2, inner_cases);
  outer_cases[0].value = inner;
  outer_cases[0].cond =
      ixs_cmp(ctx, ixs_sym(ctx, "predicate_nested_d"), IXS_CMP_GT, zero);
  outer_cases[1].value =
      ixs_cmp(ctx, ixs_sym(ctx, "predicate_nested_z"), IXS_CMP_GE, zero);
  outer_cases[1].cond = ixs_true(ctx);
  return inner ? ixs_node_pw(ctx, 2, outer_cases) : NULL;
}

static void test_bounds_contextless_query_arena_lifecycle_and_fork(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds bounds;
  ixs_bounds forked;
  ixs_bounds grandchild;
  ixs_bounds_query_state *state;
  ixs_node *root = make_nested_query_root(ctx, "contextless_query");
  size_t range_pw_case_visits;
  size_t visits;
  size_t cycle_blocks;
  size_t active_count;
  size_t nesting;
  bool held = false;
  bool fork_held = false;

  CHECK(ctx && root && ixs_node_contains_nested_piecewise(root));
  CHECK(ixs_bounds_init(&bounds, ixs_test_scratch(ctx)));
  CHECK(bounds.query_arena.current == NULL && bounds.query_state == NULL);

  ixs_arena_set_fail_after(&bounds.query_arena, 0);
  CHECK(!ixs_bounds_query_hold_begin(&bounds, root, &held));
  CHECK(!held && bounds.oom && bounds.query_state == NULL);
  ixs_arena_set_fail_after(&bounds.query_arena, IXS_ARENA_FAILURE_DISABLED);

  bounds.oom = false;
  CHECK(ixs_bounds_query_hold_begin(&bounds, root, &held) && held);
  CHECK(bounds.query_state != NULL && bounds.query_state_owner &&
        !bounds.query_state_borrowed && bounds.query_arena.current != NULL);
  state = bounds.query_state;
  ixs_bounds_query_hold_end(&bounds);
  held = false;
  CHECK(bounds.query_state == state && bounds.query_tracking_depth == 0);

  ixs_arena_set_fail_after(&bounds.query_arena, 0);
  CHECK(!ixs_bounds_query_cycle_probe(&bounds, root));
  CHECK(bounds.oom && bounds.query_tracking_depth == 0);
  ixs_bounds_query_stats(&bounds, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
                         &active_count, &nesting);
  CHECK(active_count == 0 && nesting == 0);
  ixs_arena_set_fail_after(&bounds.query_arena, IXS_ARENA_FAILURE_DISABLED);
  bounds.oom = false;
  CHECK(ixs_bounds_query_cycle_probe(&bounds, root));
  CHECK(bounds.query_tracking_depth == 0);

  CHECK(ixs_bounds_query_hold_begin(&bounds, root, &held) && held);
  CHECK(bounds.query_state == state);
  CHECK(ixs_bounds_fork(&forked, &bounds));
  CHECK(forked.query_state == state && !forked.query_state_owner &&
        forked.query_state_borrowed && forked.query_tracking_depth == 0 &&
        forked.query_arena.current == NULL);
  CHECK(bounds.query_owner != forked.query_owner);
  CHECK(ixs_bounds_fork(&grandchild, &forked));
  CHECK(grandchild.query_state == state && !grandchild.query_state_owner &&
        grandchild.query_state_borrowed &&
        grandchild.query_tracking_depth == 0 &&
        grandchild.query_arena.current == NULL);
  CHECK(grandchild.query_owner != bounds.query_owner &&
        grandchild.query_owner != forked.query_owner);
  ixs_bounds_query_stats(&bounds, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
                         &active_count, &nesting);
  CHECK(active_count == 0 && nesting == 1u);
  CHECK(ixs_bounds_query_cycle_probe(&grandchild, root));
  CHECK(grandchild.query_tracking_depth == 0 &&
        forked.query_tracking_depth == 0 && bounds.query_tracking_depth == 1);
  ixs_bounds_query_stats(&bounds, &visits, NULL, &range_pw_case_visits, NULL,
                         NULL, &cycle_blocks, NULL, &active_count, &nesting);
  CHECK(visits == 1u && cycle_blocks == 1u && range_pw_case_visits == 0 &&
        active_count == 0 && nesting == 1u);
  ixs_bounds_destroy(&grandchild);
  CHECK(ixs_bounds_query_hold_begin(&forked, root, &fork_held) && fork_held);
  ixs_bounds_query_hold_end(&forked);
  fork_held = false;
  ixs_bounds_destroy(&forked);
  CHECK(bounds.query_state == state && bounds.query_tracking_depth == 1);
  ixs_bounds_query_hold_end(&bounds);
  held = false;
  ixs_bounds_destroy(&bounds);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_query_hold_grows_and_unwinds(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds bounds;
  ixs_node *root = make_nested_query_root(ctx, "query_hold_limit");
  size_t held_count = 0;
  size_t limit_blocks;
  size_t active_count;
  size_t nesting;
  bool entered = false;

  CHECK(ctx && root && ixs_bounds_init(&bounds, ixs_test_scratch(ctx)));
  while (held_count < 1024u &&
         ixs_bounds_query_hold_begin(&bounds, root, &entered)) {
    CHECK(entered);
    held_count++;
    entered = false;
  }
  CHECK(!entered && held_count == 1024u && !bounds.oom);
  ixs_bounds_query_stats(&bounds, NULL, NULL, NULL, NULL, NULL, NULL,
                         &limit_blocks, &active_count, &nesting);
  CHECK(limit_blocks == 0 && active_count == 0 && nesting == held_count);
  while (held_count > 0) {
    ixs_bounds_query_hold_end(&bounds);
    held_count--;
  }
  CHECK(bounds.query_tracking_depth == 0);
  ixs_bounds_query_stats(&bounds, NULL, NULL, NULL, NULL, NULL, NULL,
                         &limit_blocks, &active_count, &nesting);
  CHECK(active_count == 0 && nesting == 0);

  CHECK(ixs_bounds_query_hold_begin(&bounds, root, &entered) && entered);
  ixs_bounds_query_stats(&bounds, NULL, NULL, NULL, NULL, NULL, NULL,
                         &limit_blocks, NULL, &nesting);
  CHECK(limit_blocks == 0 && nesting == 1u);
  ixs_bounds_query_hold_end(&bounds);
  ixs_bounds_destroy(&bounds);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_query_transport_poison_and_residue_retry(void) {
  enum { DEPTH = 4096 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds bounds;
  struct ixs_node_impl *chain = calloc(DEPTH, sizeof(*chain));
  ixs_addterm *terms = calloc(DEPTH, sizeof(*terms));
  ixs_node *x = ixs_sym(ctx, "query_transport_x");
  ixs_node *y = ixs_sym(ctx, "query_transport_y");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *eight = ixs_int(ctx, 8);
  ixs_node *expr = x;
  ixs_node *congruence =
      ixs_cmp(ctx, ixs_mod(ctx, x, eight), IXS_CMP_EQ, ixs_int(ctx, 3));
  ixs_bounds_test_transport observed;
  uint64_t residue = 0;
  size_t active_count;
  size_t nesting;
  bool held = false;
  size_t i;

  CHECK(ctx && chain && terms && x && y && zero && one && eight && congruence);
  if (!ctx || !chain || !terms || !x || !y || !zero || !one || !eight ||
      !congruence) {
    free(terms);
    free(chain);
    ixs_ctx_destroy(ctx);
    return;
  }
  CHECK(ixs_bounds_init(&bounds, ixs_test_scratch(ctx)));
  CHECK(ixs_bounds_add_assumption(&bounds, congruence));
  CHECK(ixs_bounds_add_assumption(&bounds, ixs_cmp(ctx, x, IXS_CMP_EQ, y)));
  CHECK(bounds.nequalities != 0);
  /* Contextless ownership keeps the query cache in query_arena.  The
   * expression context is needed only by structural congruence queries and
   * is installed after assumption ingestion so their scratch storage stays
   * independent. */
  bounds.ctx = ctx;

  for (i = 0; i < DEPTH; i++) {
    chain[i].tag = IXS_ADD;
    chain[i].properties = IXS_NODE_PROPERTY_VALID | IXS_NODE_PROPERTY_INTEGER |
                          IXS_NODE_PROPERTY_TOTAL;
    chain[i].u.add.coeff = zero;
    chain[i].u.add.nterms = 1;
    chain[i].u.add.terms = &terms[i];
    terms[i].coeff = one;
    terms[i].term = expr;
    expr = &chain[i];
  }

  /* Allocate the owner-local query state, then fail its first active/cache
   * growth.  No semantic miss may survive that generation. */
  CHECK(ixs_bounds_query_hold_begin(&bounds, expr, &held) && held);
  ixs_bounds_query_hold_end(&bounds);
  held = false;
  ixs_arena_set_fail_after(&bounds.query_arena, 0);
  CHECK(ixs_bounds_query_hold_begin(&bounds, expr, &held) && held);
  CHECK(!ixs_bounds_known_residue_probe(&bounds, expr, 8, &residue));
  CHECK(bounds.oom);
  ixs_bounds_query_hold_end(&bounds);
  held = false;
  ixs_arena_set_fail_after(&bounds.query_arena, IXS_ARENA_FAILURE_DISABLED);
  bounds.oom = false;
  CHECK(ixs_bounds_query_hold_begin(&bounds, expr, &held) && held);
  CHECK(ixs_bounds_known_residue_probe(&bounds, expr, 8, &residue) &&
        residue == 3);
  ixs_bounds_query_hold_end(&bounds);
  held = false;

  /* The first scratch allocation creates the explicit residue stack; fail
   * the first ADD-group allocation after the tracked root has started. */
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 1);
  CHECK(ixs_bounds_query_hold_begin(&bounds, expr, &held) && held);
  CHECK(!ixs_bounds_known_residue_probe(&bounds, expr, 8, &residue));
  CHECK(bounds.oom);
  ixs_bounds_query_hold_end(&bounds);
  held = false;
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  bounds.oom = false;
  CHECK(ixs_bounds_query_hold_begin(&bounds, expr, &held) && held);
  CHECK(ixs_bounds_known_residue_probe(&bounds, expr, 8, &residue) &&
        residue == 3);
  ixs_bounds_query_hold_end(&bounds);
  held = false;

  CHECK(ixs_bounds_query_transport_probe(
      &bounds, expr, IXS_BOUNDS_TEST_TRANSPORT_INVALID, &observed));
  CHECK(observed == IXS_BOUNDS_TEST_TRANSPORT_INVALID);
  CHECK(ixs_bounds_query_transport_probe(
      &bounds, expr, IXS_BOUNDS_TEST_TRANSPORT_LIMITED, &observed));
  CHECK(observed == IXS_BOUNDS_TEST_TRANSPORT_LIMITED);
  CHECK(ixs_bounds_query_transport_probe(
      &bounds, expr, IXS_BOUNDS_TEST_TRANSPORT_VALUE, &observed));
  CHECK(observed == IXS_BOUNDS_TEST_TRANSPORT_VALUE);
  ixs_bounds_query_stats(&bounds, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
                         &active_count, &nesting);
  CHECK(bounds.query_tracking_depth == 0 && active_count == 0 && nesting == 0);

  ixs_bounds_destroy(&bounds);
  free(terms);
  free(chain);
  ixs_ctx_destroy(ctx);
}

static void check_nested_query_tracking_clean(ixs_ctx *ctx, ixs_facts *facts) {
  size_t active_count;
  size_t nesting;
  CHECK(ctx->bounds_query_state != NULL && facts->bounds.query_state != NULL);
  CHECK(facts->bounds.query_tracking_depth == 0);
  ixs_bounds_query_stats(&facts->bounds, NULL, NULL, NULL, NULL, NULL, NULL,
                         NULL, &active_count, &nesting);
  CHECK(active_count == 0 && nesting == 0);
}

static void test_nested_piecewise_public_query_tracking(void) {
  ixs_ctx *ctx;
  ixs_facts *facts;
  ixs_node *flat;
  ixs_node *nested;
  ixs_node *derived;
  ixs_range_result range;
  ixs_integer_range_result integer_range;
  size_t budget;
  int64_t delta;
  unsigned query;

  ctx = ixs_ctx_create();
  facts = ixs_facts_create(ctx);
  flat = ixs_int(ctx, 1);
  nested = make_nested_query_root(ctx, "equivalence_tracking");
  CHECK(ctx->bounds_query_state == NULL);
  (void)test_ixs_equivalent_facts(facts, flat, nested);
  check_nested_query_tracking_clean(ctx, facts);
  ixs_ctx_destroy(ctx);

  ctx = ixs_ctx_create();
  facts = ixs_facts_create(ctx);
  flat = ixs_int(ctx, 1);
  nested = make_nested_query_root(ctx, "modulo_tracking");
  CHECK(ctx->bounds_query_state == NULL);
  (void)test_ixs_equivalent_modulo_pow2_facts(facts, flat, nested, 4);
  check_nested_query_tracking_clean(ctx, facts);
  ixs_ctx_destroy(ctx);

  ctx = ixs_ctx_create();
  facts = ixs_facts_create(ctx);
  flat = ixs_int(ctx, 1);
  nested = make_nested_query_root(ctx, "finite_tracking");
  budget = 4;
  CHECK(ctx->bounds_query_state == NULL);
  (void)finite_domain_equivalent(facts, flat, nested, &budget);
  check_nested_query_tracking_clean(ctx, facts);
  ixs_ctx_destroy(ctx);

  ctx = ixs_ctx_create();
  facts = ixs_facts_create(ctx);
  flat = ixs_int(ctx, 1);
  nested = make_nested_query_root(ctx, "algebra_tracking");
  CHECK(ctx->bounds_query_state == NULL);
  (void)test_ixs_constant_difference_facts(facts, flat, nested, &delta);
  check_nested_query_tracking_clean(ctx, facts);
  ixs_ctx_destroy(ctx);

  ctx = ixs_ctx_create();
  facts = ixs_facts_create(ctx);
  nested = make_nested_boolean_query_root(ctx);
  CHECK(nested && ixs_node_contains_nested_piecewise(nested));
  CHECK(ctx->bounds_query_state == NULL);
  (void)test_ixs_check_predicate_facts(facts, nested);
  check_nested_query_tracking_clean(ctx, facts);
  ixs_ctx_destroy(ctx);

  ctx = ixs_ctx_create();
  facts = ixs_facts_create(ctx);
  nested = make_nested_query_root(ctx, "ingestion_tracking");
  CHECK(ctx->bounds_query_state == NULL);
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, nested, IXS_CMP_LE, ixs_int(ctx, 3))));
  check_nested_query_tracking_clean(ctx, facts);
  ixs_ctx_destroy(ctx);

  ctx = ixs_ctx_create();
  facts = ixs_facts_create(ctx);
  nested = make_nested_query_root(ctx, "derive_tracking");
  derived = ixs_sym(ctx, "derive_tracking_result");
  CHECK(ctx->bounds_query_state == NULL);
  CHECK(ixs_facts_derive_affine(facts, nested, 2, 1, derived));
  check_nested_query_tracking_clean(ctx, facts);
  CHECK(test_ixs_range_facts(facts, derived, &range));
  CHECK(range.has_lower && range.lower_p == 3 && range.lower_q == 1 &&
        range.has_upper && range.upper_p == 7 && range.upper_q == 1);
  ixs_ctx_destroy(ctx);

  for (query = 0; query < 5u; query++) {
    ctx = ixs_ctx_create();
    nested = make_nested_query_root(ctx, "direct_query_tracking");
    CHECK(ctx->bounds_query_state == NULL);
    switch (query) {
    case 0:
      (void)ixs_check_integer_valued(ctx, nested, NULL, 0);
      break;
    case 1:
      (void)ixs_check_defined(ctx, nested, NULL, 0);
      break;
    case 2:
      (void)ixs_get_pow2_fact(ctx, nested, NULL, 0);
      break;
    case 3:
      (void)ixs_range(ctx, nested, NULL, 0, &range);
      break;
    case 4:
      (void)ixs_integer_range(ctx, nested, NULL, 0, &integer_range);
      break;
    }
    CHECK(ctx->bounds_query_state != NULL);
    ixs_ctx_destroy(ctx);
  }
}

static void test_bounds_query_cache_rejects_stack_probes(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *a = ixs_sym(ctx, "stack_probe_a");
  ixs_node *b = ixs_sym(ctx, "stack_probe_b");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *one = ixs_int(ctx, 1);
  ixs_pwcase dead_case = {zero, ixs_false(ctx)};
  ixs_node *dead = ixs_node_pw(ctx, 1, &dead_case);
  ixs_pwcase cases[3];
  ixs_node *root;
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_range_result range;
  size_t active_count;
  size_t nesting;

  cases[0].value = dead;
  cases[0].cond = ixs_cmp(ctx, ixs_and(ctx, a, one), IXS_CMP_EQ, one);
  cases[1].value = ixs_int(ctx, 5);
  cases[1].cond = ixs_cmp(ctx, ixs_and(ctx, b, one), IXS_CMP_EQ, one);
  cases[2].value = ixs_int(ctx, 7);
  cases[2].cond = ixs_true(ctx);
  root = ixs_node_pw(ctx, 3, cases);

  CHECK(dead && root && ixs_node_contains_nested_piecewise(root));
  CHECK(ixs_facts_assume_pred(facts, ixs_cmp(ctx, a, IXS_CMP_EQ, zero)));
  CHECK(ixs_facts_assume_pred(facts, ixs_cmp(ctx, b, IXS_CMP_EQ, one)));
  CHECK(test_ixs_range_facts(facts, root, &range));
  CHECK(range.has_lower && range.lower_p == 5 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 5 && range.upper_q == 1);
  ixs_bounds_query_stats(&facts->bounds, NULL, NULL, NULL, NULL, NULL, NULL,
                         NULL, &active_count, &nesting);
  CHECK(active_count == 0 && nesting == 0);

  ixs_ctx_destroy(ctx);
}

static void test_piecewise_residue_domain_guards(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "piecewise_residue_domain_x");
  ixs_node *c = ixs_sym(ctx, "piecewise_residue_domain_c");
  ixs_node *d = ixs_sym(ctx, "piecewise_residue_domain_d");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *two = ixs_int(ctx, 2);
  ixs_node *fallback = ixs_true(ctx);
  ixs_node *condition = ixs_cmp(ctx, c, IXS_CMP_GT, zero);
  ixs_node *reciprocal = ixs_div(ctx, one, x);
  ixs_node *undefined_condition = ixs_cmp(ctx, reciprocal, IXS_CMP_GT, zero);
  ixs_node *undefined_value = ixs_floor(ctx, reciprocal);
  ixs_node *conditions[2] = {condition, fallback};
  ixs_node *undefined_conditions[2] = {undefined_condition, fallback};
  ixs_node *differing_values[2] = {zero, one};
  ixs_node *same_residue_values[2] = {zero, two};
  ixs_node *undefined_values[2] = {undefined_value, zero};
  ixs_node *differing = ixs_pw(ctx, 2, differing_values, conditions);
  ixs_node *bad_condition =
      ixs_pw(ctx, 2, same_residue_values, undefined_conditions);
  ixs_node *bad_value = ixs_pw(ctx, 2, undefined_values, conditions);
  ixs_node *negative_modulus = ixs_mod(ctx, x, ixs_int(ctx, -8));
  ixs_node *zero_dynamic_modulus = ixs_mod(ctx, x, d);
  ixs_facts *facts = ixs_facts_create(ctx);

  CHECK(differing && bad_condition && bad_value && negative_modulus &&
        zero_dynamic_modulus && facts);
  CHECK(ixs_facts_assume_pred(facts, ixs_cmp(ctx, d, IXS_CMP_EQ, zero)));
  CHECK(test_ixs_check_congruent_facts(facts, differing, 2, 0) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_congruent_facts(facts, bad_condition, 2, 0) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_congruent_facts(facts, bad_value, 1, 0) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_congruent_facts(facts, negative_modulus, 2, 0) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_congruent_facts(facts, zero_dynamic_modulus, 2, 0) ==
        IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

/* ------------------------------------------------------------------ */
/*  Bounds: expression-level overrides (expr >= 0 pattern)            */
/* ------------------------------------------------------------------ */

static void test_bounds_expr_override(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));

  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *expr = ixs_add(ctx, x, y);

  /* x+y >= 0 as an expression-level assumption */
  ixs_bounds_add_assumption(&b,
                            ixs_cmp(ctx, expr, IXS_CMP_GE, ixs_int(ctx, 0)));
  ixs_interval iv = ixs_bounds_get(&b, expr);
  CHECK(iv.valid);
  CHECK(ixs_rat_cmp(iv.lo_p, iv.lo_q, 0, 1) == 0);

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_expr_override_invalidates_cache(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));

  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *expr = ixs_add(ctx, x, y);

  ixs_interval iv = ixs_bounds_get(&b, expr);
  CHECK(!iv.valid);

  ixs_bounds_add_expr(&b, expr, ixs_interval_exact(7, 1));
  iv = ixs_bounds_get(&b, expr);
  CHECK(iv.valid);
  CHECK(iv.lo_p == 7 && iv.lo_q == 1);
  CHECK(iv.hi_p == 7 && iv.hi_q == 1);

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static size_t test_expr_index_bucket(const ixs_node *expr, size_t capacity) {
  uint64_t x = (uint64_t)(uintptr_t)expr;
  x ^= x >> 33;
  x *= UINT64_C(0xff51afd7ed558ccd);
  x ^= x >> 33;
  return (size_t)x & (capacity - 1u);
}

static void test_bounds_expr_index_collision(void) {
  enum { INDEX_CAPACITY = 8, CANDIDATE_COUNT = INDEX_CAPACITY + 1 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  ixs_node *buckets[INDEX_CAPACITY] = {0};
  ixs_node *first = NULL;
  ixs_node *second = NULL;
  size_t bucket = 0;
  size_t i;

  for (i = 0; i < CANDIDATE_COUNT; i++) {
    char name[32];
    ixs_node *candidate;
    size_t candidate_bucket;
    snprintf(name, sizeof(name), "expr_collision_%zu", i);
    candidate = ixs_sym(ctx, name);
    candidate_bucket = test_expr_index_bucket(candidate, INDEX_CAPACITY);
    if (buckets[candidate_bucket]) {
      first = buckets[candidate_bucket];
      second = candidate;
      bucket = candidate_bucket;
      break;
    }
    buckets[candidate_bucket] = candidate;
  }

  CHECK(first != NULL);
  CHECK(second != NULL);
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));
  ixs_bounds_add_expr(&b, first, ixs_interval_exact(11, 1));
  ixs_bounds_add_expr(&b, second, ixs_interval_exact(22, 1));
  CHECK(!b.oom);
  CHECK(b.nexprs == 2);
  CHECK(b.exprs[0].expr == first);
  CHECK(b.exprs[1].expr == second);
  CHECK(b.expr_index_cap == INDEX_CAPACITY);
  CHECK(b.expr_index[bucket] == 1u);
  CHECK(b.expr_index[(bucket + 1u) & (INDEX_CAPACITY - 1u)] == 2u);
  CHECK(ixs_bounds_get(&b, first).lo_p == 11);
  CHECK(ixs_bounds_get(&b, second).lo_p == 22);

  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_expr_index_growth_and_merge(void) {
  enum { EXPR_COUNT = 64 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  ixs_bounds conflicting;
  ixs_node *exprs[EXPR_COUNT];
  ixs_node *conflict = ixs_sym(ctx, "expr_index_conflict");
  ixs_interval iv;
  size_t count;
  size_t i;

  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));
  for (i = 0; i < EXPR_COUNT; i++) {
    char name[32];
    snprintf(name, sizeof(name), "expr_index_%zu", i);
    exprs[i] = ixs_sym(ctx, name);
    ixs_bounds_add_expr(&b, exprs[i],
                        ixs_interval_range((int64_t)i, 1, (int64_t)i + 100, 1));
  }
  CHECK(!b.oom);
  CHECK(b.nexprs == EXPR_COUNT);
  CHECK(b.expr_index_cap != 0);
  CHECK((b.expr_index_cap & (b.expr_index_cap - 1u)) == 0);
  CHECK(b.nexprs <= b.expr_index_cap - b.expr_index_cap / 4u);

  for (i = EXPR_COUNT; i > 0; i--) {
    size_t index = i - 1u;
    iv = ixs_bounds_get(&b, exprs[index]);
    CHECK(iv.valid);
    CHECK(iv.lo_p == (int64_t)index && iv.lo_q == 1);
    CHECK(iv.hi_p == (int64_t)index + 100 && iv.hi_q == 1);
  }

  count = b.nexprs;
  ixs_bounds_add_expr(&b, exprs[0], ixs_interval_range(20, 1, 80, 1));
  CHECK(b.nexprs == count);
  iv = ixs_bounds_get(&b, exprs[0]);
  CHECK(iv.valid);
  CHECK(iv.lo_p == 20 && iv.lo_q == 1);
  CHECK(iv.hi_p == 80 && iv.hi_q == 1);

  CHECK(ixs_bounds_init(&conflicting, ixs_test_scratch(ctx)));
  ixs_bounds_add_expr(&conflicting, conflict, ixs_interval_exact(0, 1));
  ixs_bounds_add_expr(&conflicting, conflict, ixs_interval_exact(1, 1));
  CHECK(conflicting.nexprs == 1);
  CHECK(!conflicting.exprs[0].iv.valid);
  CHECK(ixs_bounds_has_empty(&conflicting));
  ixs_bounds_add_expr(&conflicting, conflict, ixs_interval_exact(0, 1));
  CHECK(!conflicting.empty_cache_valid);
  CHECK(conflicting.nexprs == 1);
  CHECK(!conflicting.exprs[0].iv.valid);
  CHECK(ixs_bounds_has_empty(&conflicting));

  ixs_bounds_destroy(&conflicting);
  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_var_index_oom(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_arena *scratch = ixs_test_scratch(ctx);
  ixs_arena_mark mark;
  ixs_bounds lazy;
  ixs_bounds growth;
  ixs_bounds parent;
  ixs_bounds child;
  ixs_node *vars[7];
  size_t *saved_index;
  ixs_var_bound *saved_vars;
  size_t saved_index_cap;
  size_t i;

  CHECK(ixs_bounds_init(&lazy, scratch));
  vars[0] = ixs_sym(ctx, "var_index_oom_lazy");
  ixs_arena_set_fail_after(scratch, 0);
  CHECK(!ixs_bounds_add_assumption(
      &lazy, ixs_cmp(ctx, vars[0], IXS_CMP_GE, ixs_int(ctx, 0))));
  ixs_arena_set_fail_after(scratch, IXS_ARENA_FAILURE_DISABLED);
  CHECK(lazy.oom);
  CHECK(lazy.nvars == 0);
  CHECK(lazy.var_index == NULL);
  CHECK(lazy.var_index_cap == 0);

  CHECK(ixs_bounds_init(&growth, scratch));
  for (i = 0; i < 7; i++) {
    char name[32];
    snprintf(name, sizeof(name), "var_index_grow_oom_%zu", i);
    vars[i] = ixs_sym(ctx, name);
  }
  for (i = 0; i < 6; i++)
    CHECK(ixs_bounds_add_assumption(
        &growth, ixs_cmp(ctx, vars[i], IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(!growth.oom);
  CHECK(growth.nvars == 6);
  saved_index = growth.var_index;
  saved_vars = growth.vars;
  saved_index_cap = growth.var_index_cap;
  ixs_arena_set_fail_after(scratch, 0);
  CHECK(!ixs_bounds_add_assumption(
      &growth, ixs_cmp(ctx, vars[6], IXS_CMP_GE, ixs_int(ctx, 0))));
  ixs_arena_set_fail_after(scratch, IXS_ARENA_FAILURE_DISABLED);
  CHECK(growth.oom);
  CHECK(growth.nvars == 6);
  CHECK(growth.var_index == saved_index);
  CHECK(growth.var_index_cap == saved_index_cap);
  CHECK(growth.vars == saved_vars);

  CHECK(ixs_bounds_init(&parent, scratch));
  CHECK(ixs_bounds_add_assumption(
      &parent, ixs_cmp(ctx, vars[0], IXS_CMP_GE, ixs_int(ctx, 0))));
  saved_index = parent.var_index;
  mark = ixs_arena_save(scratch);
  ixs_arena_set_fail_after(scratch, 1);
  CHECK(!ixs_bounds_fork(&child, &parent));
  ixs_arena_set_fail_after(scratch, IXS_ARENA_FAILURE_DISABLED);
  ixs_arena_restore(scratch, mark);
  CHECK(parent.var_index == saved_index);
  CHECK(parent.nvars == 1);
  CHECK(ixs_bounds_get(&parent, vars[0]).valid);

  ixs_bounds_destroy(&parent);
  ixs_bounds_destroy(&growth);
  ixs_bounds_destroy(&lazy);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_expr_index_oom(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_arena *scratch = ixs_test_scratch(ctx);
  ixs_arena_mark mark;
  ixs_bounds lazy;
  ixs_bounds atomic;
  ixs_bounds growth;
  ixs_bounds parent;
  ixs_bounds child;
  ixs_node *expr = ixs_sym(ctx, "expr_index_oom");
  ixs_node *growth_exprs[7];
  size_t *saved_index;
  ixs_expr_bound *saved_exprs;
  size_t saved_index_cap;
  size_t i;

  CHECK(ixs_bounds_init(&lazy, scratch));
  ixs_arena_set_fail_after(scratch, 0);
  ixs_bounds_add_expr(&lazy, expr, ixs_interval_exact(0, 1));
  ixs_arena_set_fail_after(scratch, IXS_ARENA_FAILURE_DISABLED);
  CHECK(lazy.oom);
  CHECK(lazy.nexprs == 0);
  CHECK(lazy.exprs == NULL);
  CHECK(lazy.expr_index == NULL);

  CHECK(ixs_bounds_init(&atomic, scratch));
  ixs_arena_set_fail_after(scratch, 1);
  ixs_bounds_add_expr(&atomic, expr, ixs_interval_exact(0, 1));
  ixs_arena_set_fail_after(scratch, IXS_ARENA_FAILURE_DISABLED);
  CHECK(atomic.oom);
  CHECK(atomic.nexprs == 0);
  CHECK(atomic.exprs == NULL);
  CHECK(atomic.expr_index == NULL);

  CHECK(ixs_bounds_init(&growth, scratch));
  for (i = 0; i < 7; i++) {
    char name[32];
    snprintf(name, sizeof(name), "expr_index_grow_oom_%zu", i);
    growth_exprs[i] = ixs_sym(ctx, name);
  }
  for (i = 0; i < 6; i++)
    ixs_bounds_add_expr(&growth, growth_exprs[i],
                        ixs_interval_exact((int64_t)i, 1));
  CHECK(!growth.oom);
  CHECK(growth.nexprs == 6);
  saved_index = growth.expr_index;
  saved_exprs = growth.exprs;
  saved_index_cap = growth.expr_index_cap;
  ixs_arena_set_fail_after(scratch, 0);
  ixs_bounds_add_expr(&growth, growth_exprs[6], ixs_interval_exact(6, 1));
  ixs_arena_set_fail_after(scratch, IXS_ARENA_FAILURE_DISABLED);
  CHECK(growth.oom);
  CHECK(growth.nexprs == 6);
  CHECK(growth.expr_index == saved_index);
  CHECK(growth.expr_index_cap == saved_index_cap);
  CHECK(growth.exprs == saved_exprs);

  CHECK(ixs_bounds_init(&parent, scratch));
  ixs_bounds_add_expr(&parent, expr, ixs_interval_exact(0, 1));
  CHECK(!parent.oom);
  saved_index = parent.expr_index;
  mark = ixs_arena_save(scratch);
  ixs_arena_set_fail_after(scratch, 2);
  CHECK(!ixs_bounds_fork(&child, &parent));
  ixs_arena_set_fail_after(scratch, IXS_ARENA_FAILURE_DISABLED);
  ixs_arena_restore(scratch, mark);
  CHECK(parent.expr_index == saved_index);
  CHECK(parent.nexprs == 1);
  CHECK(ixs_bounds_get(&parent, expr).valid);

  ixs_bounds_destroy(&parent);
  ixs_bounds_destroy(&growth);
  ixs_bounds_destroy(&atomic);
  ixs_bounds_destroy(&lazy);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_expr_le(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));

  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *expr = ixs_add(ctx, x, y);

  /* x+y <= 0 as an expression-level assumption */
  ixs_bounds_add_assumption(&b,
                            ixs_cmp(ctx, expr, IXS_CMP_LE, ixs_int(ctx, 0)));
  ixs_interval iv = ixs_bounds_get(&b, expr);
  CHECK(iv.valid);
  CHECK(ixs_rat_cmp(iv.hi_p, iv.hi_q, 0, 1) == 0);
  CHECK(iv.lo_inf);

  /* x+y < 0 tightens upper bound to -1 */
  ixs_bounds b2;
  CHECK(ixs_bounds_init(&b2, ixs_test_scratch(ctx)));
  ixs_bounds_add_assumption(&b2,
                            ixs_cmp(ctx, expr, IXS_CMP_LT, ixs_int(ctx, 0)));
  iv = ixs_bounds_get(&b2, expr);
  CHECK(iv.valid);
  CHECK(iv.hi_p == -1 && iv.hi_q == 1);

  ixs_bounds_destroy(&b2);
  ixs_bounds_destroy(&b);
  ixs_ctx_destroy(ctx);
}

/* ------------------------------------------------------------------ */
/*  Endpoint widening                                                 */
/* ------------------------------------------------------------------ */

static void test_iv_endpoint_widen_positive(void) {
  int64_t rp, rq;
  iv_endpoint_widen(5, 3, &rp, &rq);
  CHECK(ixs_interval_is_pos_inf(rp, rq));
}

static void test_iv_endpoint_widen_negative(void) {
  int64_t rp, rq;
  iv_endpoint_widen(-5, 3, &rp, &rq);
  CHECK(ixs_interval_is_neg_inf(rp, rq));
}

static void test_iv_endpoint_widen_neg_neg(void) {
  int64_t rp, rq;
  /* negative * negative -> positive -> +inf */
  iv_endpoint_widen(-5, -3, &rp, &rq);
  CHECK(ixs_interval_is_pos_inf(rp, rq));
}

/* ------------------------------------------------------------------ */
/*  Bounds: entailment check (ixs_bounds_check)                       */
/* ------------------------------------------------------------------ */

/* M in (-inf, 63]: M < 70 is always true. */
static void test_bounds_check_true(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *M = ixs_sym(ctx, "M");
  ixs_node *assume = ixs_cmp(ctx, M, IXS_CMP_LT, ixs_int(ctx, 64));
  ixs_node *query = ixs_cmp(ctx, M, IXS_CMP_LT, ixs_int(ctx, 70));
  CHECK(ixs_check(ctx, query, &assume, 1) == IXS_CHECK_TRUE);
  ixs_ctx_destroy(ctx);
}

/* M in (-inf, 63]: M > 70 is always false. */
static void test_bounds_check_false(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *M = ixs_sym(ctx, "M");
  ixs_node *assume = ixs_cmp(ctx, M, IXS_CMP_LT, ixs_int(ctx, 64));
  ixs_node *query = ixs_cmp(ctx, M, IXS_CMP_GT, ixs_int(ctx, 70));
  CHECK(ixs_check(ctx, query, &assume, 1) == IXS_CHECK_FALSE);
  ixs_ctx_destroy(ctx);
}

/* M in (-inf, 63]: M < 32 is unknown (could be 10 or 50). */
static void test_bounds_check_unknown(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *M = ixs_sym(ctx, "M");
  ixs_node *assume = ixs_cmp(ctx, M, IXS_CMP_LT, ixs_int(ctx, 64));
  ixs_node *query = ixs_cmp(ctx, M, IXS_CMP_LT, ixs_int(ctx, 32));
  CHECK(ixs_check(ctx, query, &assume, 1) == IXS_CHECK_UNKNOWN);
  ixs_ctx_destroy(ctx);
}

/* M == 5: (M - 5) == 0 is true; (M - 3) == 0 is false. */
static void test_bounds_check_eq(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *M = ixs_sym(ctx, "M");
  ixs_node *assume = ixs_cmp(ctx, M, IXS_CMP_EQ, ixs_int(ctx, 5));
  ixs_node *q_true = ixs_cmp(ctx, M, IXS_CMP_EQ, ixs_int(ctx, 5));
  ixs_node *q_false = ixs_cmp(ctx, M, IXS_CMP_EQ, ixs_int(ctx, 3));
  CHECK(ixs_check(ctx, q_true, &assume, 1) == IXS_CHECK_TRUE);
  CHECK(ixs_check(ctx, q_false, &assume, 1) == IXS_CHECK_FALSE);
  ixs_ctx_destroy(ctx);
}

/* M in [0, 10]: M != 20 is true. */
static void test_bounds_check_ne(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *M = ixs_sym(ctx, "M");
  ixs_node *assumes[2];
  assumes[0] = ixs_cmp(ctx, M, IXS_CMP_GE, ixs_int(ctx, 0));
  assumes[1] = ixs_cmp(ctx, M, IXS_CMP_LE, ixs_int(ctx, 10));
  ixs_node *query = ixs_cmp(ctx, M, IXS_CMP_NE, ixs_int(ctx, 20));
  CHECK(ixs_check(ctx, query, assumes, 2) == IXS_CHECK_TRUE);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_check_mod_congruence(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *K = ixs_sym(ctx, "K");
  ixs_node *assume = ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 256)),
                             IXS_CMP_EQ, ixs_int(ctx, 0));

  CHECK(ixs_check(ctx,
                  ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 32)), IXS_CMP_EQ,
                          ixs_int(ctx, 0)),
                  &assume, 1) == IXS_CHECK_TRUE);
  CHECK(ixs_check(ctx,
                  ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 32)), IXS_CMP_NE,
                          ixs_int(ctx, 0)),
                  &assume, 1) == IXS_CHECK_FALSE);
  CHECK(ixs_check(ctx,
                  ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 32)), IXS_CMP_EQ,
                          ixs_int(ctx, 1)),
                  &assume, 1) == IXS_CHECK_FALSE);
  CHECK(ixs_check(ctx,
                  ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 32)), IXS_CMP_NE,
                          ixs_int(ctx, 1)),
                  &assume, 1) == IXS_CHECK_TRUE);
  CHECK(ixs_check(ctx,
                  ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 512)), IXS_CMP_EQ,
                          ixs_int(ctx, 0)),
                  &assume, 1) == IXS_CHECK_UNKNOWN);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_check_mod_remainder(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *K = ixs_sym(ctx, "K");
  ixs_node *assume = ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 8)), IXS_CMP_EQ,
                             ixs_int(ctx, 3));

  CHECK(ixs_check(ctx,
                  ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 4)), IXS_CMP_EQ,
                          ixs_int(ctx, 3)),
                  &assume, 1) == IXS_CHECK_TRUE);
  CHECK(ixs_check(ctx,
                  ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 4)), IXS_CMP_EQ,
                          ixs_int(ctx, 1)),
                  &assume, 1) == IXS_CHECK_FALSE);
  CHECK(ixs_check(ctx,
                  ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 4)), IXS_CMP_EQ,
                          ixs_int(ctx, 7)),
                  &assume, 1) == IXS_CHECK_FALSE);
  CHECK(ixs_check(ctx,
                  ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 4)), IXS_CMP_NE,
                          ixs_int(ctx, 7)),
                  &assume, 1) == IXS_CHECK_TRUE);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_check_composite_divisibility(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *K = ixs_sym(ctx, "K");
  ixs_node *N = ixs_sym(ctx, "N");
  ixs_node *assumes[2];

  assumes[0] = ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 32)), IXS_CMP_EQ,
                       ixs_int(ctx, 0));
  assumes[1] = ixs_cmp(ctx, ixs_mod(ctx, N, ixs_int(ctx, 16)), IXS_CMP_EQ,
                       ixs_int(ctx, 0));

  CHECK(ixs_check(ctx,
                  ixs_cmp(ctx,
                          ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, 3), K),
                                  ixs_int(ctx, 32)),
                          IXS_CMP_EQ, ixs_int(ctx, 0)),
                  assumes, 2) == IXS_CHECK_TRUE);
  CHECK(
      ixs_check(ctx,
                ixs_cmp(ctx, ixs_mod(ctx, ixs_add(ctx, K, N), ixs_int(ctx, 16)),
                        IXS_CMP_EQ, ixs_int(ctx, 0)),
                assumes, 2) == IXS_CHECK_TRUE);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_check_pow2_fact(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *d = ixs_sym(ctx, "d");
  ixs_node *dm1 = ixs_sub(ctx, d, ixs_int(ctx, 1));
  ixs_node *pow2_expr = ixs_and(ctx, d, dm1);
  ixs_node *assume = ixs_cmp(ctx, pow2_expr, IXS_CMP_EQ, ixs_int(ctx, 0));

  CHECK(ixs_check(ctx, ixs_cmp(ctx, pow2_expr, IXS_CMP_EQ, ixs_int(ctx, 0)),
                  &assume, 1) == IXS_CHECK_TRUE);
  CHECK(ixs_check(ctx, ixs_cmp(ctx, pow2_expr, IXS_CMP_NE, ixs_int(ctx, 0)),
                  &assume, 1) == IXS_CHECK_FALSE);
  CHECK(ixs_check(ctx, ixs_cmp(ctx, pow2_expr, IXS_CMP_EQ, ixs_int(ctx, 4)),
                  &assume, 1) == IXS_CHECK_FALSE);
  CHECK(ixs_check(ctx, ixs_cmp(ctx, d, IXS_CMP_GE, ixs_int(ctx, 0)), &assume,
                  1) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_bounds_check_mask_fact(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *assume = ixs_cmp(ctx, ixs_and(ctx, x, ixs_int(ctx, 15)), IXS_CMP_EQ,
                             ixs_int(ctx, 5));

  CHECK(ixs_check(ctx,
                  ixs_cmp(ctx, ixs_and(ctx, x, ixs_int(ctx, 7)), IXS_CMP_EQ,
                          ixs_int(ctx, 5)),
                  &assume, 1) == IXS_CHECK_TRUE);
  CHECK(ixs_check(ctx,
                  ixs_cmp(ctx, ixs_and(ctx, x, ixs_int(ctx, 7)), IXS_CMP_EQ,
                          ixs_int(ctx, 1)),
                  &assume, 1) == IXS_CHECK_FALSE);
  CHECK(ixs_check(ctx,
                  ixs_cmp(ctx, ixs_and(ctx, x, ixs_int(ctx, 16)), IXS_CMP_EQ,
                          ixs_int(ctx, 0)),
                  &assume, 1) == IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_bounds_check_contradiction_unknown(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *lo = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 10));
  ixs_node *hi = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 5));
  ixs_node *both = ixs_and(ctx, lo, hi);
  ixs_node *query = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_range_result r;

  CHECK(ixs_check(ctx, query, &both, 1) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_get_pow2_fact(ctx, x, &both, 1) == IXS_POW2_UNKNOWN);
  CHECK(!ixs_range(ctx, x, &both, 1, &r));
  CHECK(ixs_facts_assume_pred(facts, both));
  CHECK(test_ixs_check_facts(facts, query) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_get_pow2_fact_facts(facts, x) == IXS_POW2_UNKNOWN);
  CHECK(!test_ixs_range_facts(facts, x, &r));

  ixs_ctx_destroy(ctx);
}

static void test_public_pow2_fact(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *d = ixs_sym(ctx, "d");
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *dm1 = ixs_sub(ctx, d, ixs_int(ctx, 1));
  ixs_node *pow2_expr = ixs_and(ctx, d, dm1);
  ixs_node *assumes[2];

  assumes[0] = ixs_cmp(ctx, pow2_expr, IXS_CMP_EQ, ixs_int(ctx, 0));
  assumes[1] = ixs_cmp(ctx, d, IXS_CMP_GT, ixs_int(ctx, 0));

  CHECK(ixs_get_pow2_fact(ctx, ixs_int(ctx, 0), NULL, 0) == IXS_POW2_OR_ZERO);
  CHECK(ixs_get_pow2_fact(ctx, ixs_int(ctx, 8), NULL, 0) == IXS_POW2_POSITIVE);
  CHECK(ixs_get_pow2_fact(ctx, ixs_int(ctx, 6), NULL, 0) == IXS_POW2_UNKNOWN);

  CHECK(ixs_get_pow2_fact(ctx, d, assumes, 1) == IXS_POW2_OR_ZERO);
  CHECK(ixs_get_pow2_fact(ctx, d, assumes, 2) == IXS_POW2_POSITIVE);

  assumes[0] = ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, 7));
  CHECK(ixs_get_pow2_fact(ctx, ixs_add(ctx, x, ixs_int(ctx, 1)), assumes, 1) ==
        IXS_POW2_POSITIVE);
  assumes[0] = ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, -1));
  CHECK(ixs_get_pow2_fact(ctx, ixs_add(ctx, x, ixs_int(ctx, 1)), assumes, 1) ==
        IXS_POW2_OR_ZERO);

  assumes[0] = ixs_cmp(ctx, d, IXS_CMP_GE, ixs_int(ctx, 10));
  assumes[1] = ixs_cmp(ctx, d, IXS_CMP_LE, ixs_int(ctx, 5));
  CHECK(ixs_get_pow2_fact(ctx, d, assumes, 2) == IXS_POW2_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

/* Canonical predicates survive smart-constructor folding; other non-CMP
 * inputs return UNKNOWN. */
static void test_bounds_check_non_cmp(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *falsehood = ixs_false(ctx);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);
  CHECK(ixs_check(ctx, ixs_true(ctx), NULL, 0) == IXS_CHECK_TRUE);
  CHECK(ixs_check(ctx, ixs_false(ctx), NULL, 0) == IXS_CHECK_FALSE);
  CHECK(ixs_check(ctx, ixs_int(ctx, 2), NULL, 0) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check(ctx, x, NULL, 0) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_facts(facts, ixs_true(ctx)) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(facts, ixs_false(ctx)) == IXS_CHECK_FALSE);
  CHECK(test_ixs_check_facts(facts, ixs_int(ctx, 2)) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_facts(facts, x) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check(ctx, ixs_true(ctx), &falsehood, 1) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_facts_assume_pred(contradictory, falsehood));
  CHECK(test_ixs_check_facts(contradictory, ixs_true(ctx)) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_facts(contradictory, ixs_false(ctx)) ==
        IXS_CHECK_UNKNOWN);
  ixs_ctx_destroy(ctx);
}

static void test_bounds_partial_predicate_is_semantic_unknown(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "partial_predicate_x");
  ixs_node *partial = ixs_floor(
      ctx, ixs_div(ctx, ixs_int(ctx, 1), ixs_sub(ctx, x, ixs_int(ctx, 1))));
  ixs_node *query = ixs_cmp(ctx, partial, IXS_CMP_GE, ixs_int(ctx, -1));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_fact_check_result result;

  CHECK(ctx && x && partial && query && facts);
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 31))));
  result = ixs_check_predicate_facts(facts, query);
  CHECK(result.status == IXS_FACT_QUERY_COMPLETE &&
        result.check == IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_public_fact_consistency(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *raw = ixs_sym(ctx, "raw");
  ixs_node *shifted = ixs_add(ctx, ixs_int(ctx, 63), raw);
  ixs_node *fraction = ixs_div(ctx, shifted, ixs_int(ctx, 64));
  ixs_node *values[2] = {ixs_floor(ctx, fraction), ixs_ceil(ctx, fraction)};
  ixs_node *conditions[2] = {ixs_cmp(ctx, shifted, IXS_CMP_GE, ixs_int(ctx, 0)),
                             ixs_true(ctx)};
  ixs_node *quotient = ixs_pw(ctx, 2, values, conditions);
  ixs_node *contradiction[2] = {
      ixs_cmp(ctx, quotient, IXS_CMP_GE, ixs_int(ctx, 2)),
      ixs_cmp(ctx, shifted, IXS_CMP_LT, ixs_int(ctx, 0))};
  ixs_facts *facts = ixs_facts_create(ctx);

  CHECK(test_ixs_check_consistent_facts(NULL) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_consistent_facts(facts) == IXS_CHECK_TRUE);
  CHECK(ixs_facts_assume_preds(facts, contradiction, 2));
  CHECK(test_ixs_check_consistent_facts(facts) == IXS_CHECK_FALSE);

  ixs_ctx_destroy(ctx);
}

/* ------------------------------------------------------------------ */
/*  Bounds: public range API                                          */
/* ------------------------------------------------------------------ */

static void test_public_range_basic(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *assumes[2];
  ixs_node *expr;
  ixs_range_result r;

  assumes[0] = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  assumes[1] = ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 16));
  expr = ixs_add(ctx, x, ixs_int(ctx, 5));

  CHECK(ixs_range(ctx, expr, assumes, 2, &r));
  CHECK(r.has_lower);
  CHECK(r.has_upper);
  CHECK(r.lower_p == 5 && r.lower_q == 1);
  CHECK(r.upper_p == 20 && r.upper_q == 1);

  ixs_ctx_destroy(ctx);
}

static void test_public_range_unbounded(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *assume = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_range_result r;

  CHECK(ixs_range(ctx, x, &assume, 1, &r));
  CHECK(r.has_lower);
  CHECK(!r.has_upper);
  CHECK(r.lower_p == 0 && r.lower_q == 1);

  ixs_ctx_destroy(ctx);
}

static void test_public_range_rational(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *assumes[2];
  ixs_node *expr;
  ixs_range_result r;

  assumes[0] = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 1));
  assumes[1] = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 3));
  expr = ixs_div(ctx, x, ixs_int(ctx, 2));

  CHECK(ixs_range(ctx, expr, assumes, 2, &r));
  CHECK(r.has_lower);
  CHECK(r.has_upper);
  CHECK(r.lower_p == 1 && r.lower_q == 2);
  CHECK(r.upper_p == 3 && r.upper_q == 2);

  ixs_ctx_destroy(ctx);
}

static void test_public_integer_range(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "integer_range_x");
  ixs_node *y = ixs_sym(ctx, "integer_range_y");
  ixs_node *other_x = ixs_sym(other, "integer_range_x");
  ixs_node *bounded[2];
  ixs_node *even_bounded[3];
  ixs_node *foreign_assumption;
  ixs_node *half = ixs_div(ctx, x, ixs_int(ctx, 2));
  ixs_node *reciprocal = ixs_div(ctx, ixs_int(ctx, 1), y);
  ixs_node *composite = ixs_add(
      ctx, ixs_mul(ctx, ixs_int(ctx, 2), ixs_mul(ctx, x, y)), ixs_int(ctx, 1));
  ixs_node *shifted = ixs_add(ctx, x, ixs_int(ctx, 1));
  ixs_node *x_mod_four = ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 4)),
                                 IXS_CMP_EQ, ixs_int(ctx, 0));
  ixs_range_result input = {true, true, 1, 2, 19, 2};
  ixs_integer_range_result result;
  ixs_facts *rounded = ixs_facts_create(ctx);
  ixs_facts *lower_only = ixs_facts_create(ctx);
  ixs_facts *upper_only = ixs_facts_create(ctx);
  ixs_facts *aligned = ixs_facts_create(ctx);
  ixs_facts *empty = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);
  ixs_facts *overflow_one_sided = ixs_facts_create(ctx);
  ixs_facts *overflow_bounded = ixs_facts_create(ctx);
  ixs_facts *oom = ixs_facts_create(ctx);

  bounded[0] = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_rat(ctx, 1, 2));
  bounded[1] = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_rat(ctx, 19, 2));
  CHECK(ixs_integer_range(ctx, x, bounded, 2, &result));
  CHECK(result.has_lower && result.lower == 1);
  CHECK(result.has_upper && result.upper == 9);

  CHECK(!ixs_integer_range(ctx, half, bounded, 2, &result));
  CHECK(!result.has_lower && !result.has_upper && result.lower == 0 &&
        result.upper == 0);
  even_bounded[0] = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 1));
  even_bounded[1] = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 10));
  even_bounded[2] = ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 2)), IXS_CMP_EQ,
                            ixs_int(ctx, 0));
  CHECK(ixs_integer_range(ctx, half, even_bounded, 3, &result));
  CHECK(result.has_lower && result.lower == 1);
  CHECK(result.has_upper && result.upper == 5);

  CHECK(!ixs_integer_range(ctx, reciprocal, NULL, 0, &result));
  CHECK(!result.has_lower && !result.has_upper && result.lower == 0 &&
        result.upper == 0);
  CHECK(!ixs_integer_range(ctx, x, NULL, 0, NULL));

  CHECK(ixs_facts_assume_range(rounded, x, &input));
  CHECK(test_ixs_integer_range_facts(rounded, x, &result));
  CHECK(result.has_lower && result.lower == 1);
  CHECK(result.has_upper && result.upper == 9);

  input.has_upper = false;
  CHECK(ixs_facts_assume_range(lower_only, x, &input));
  CHECK(test_ixs_integer_range_facts(lower_only, x, &result));
  CHECK(result.has_lower && result.lower == 1);
  CHECK(!result.has_upper);

  input.has_lower = false;
  input.has_upper = true;
  CHECK(ixs_facts_assume_range(upper_only, x, &input));
  CHECK(test_ixs_integer_range_facts(upper_only, x, &result));
  CHECK(!result.has_lower);
  CHECK(result.has_upper && result.upper == 9);

  input.has_lower = true;
  input.lower_p = 0;
  input.lower_q = 1;
  input.upper_p = 10;
  input.upper_q = 1;
  CHECK(ixs_facts_assume_range(aligned, composite, &input));
  CHECK(test_ixs_integer_range_facts(aligned, composite, &result));
  CHECK(result.has_lower && result.lower == 1);
  CHECK(result.has_upper && result.upper == 9);

  input.lower_p = 1;
  input.lower_q = 4;
  input.upper_p = 3;
  input.upper_q = 4;
  CHECK(ixs_facts_assume_range(empty, x, &input));
  CHECK(!test_ixs_integer_range_facts(empty, x, &result));
  CHECK(!result.has_lower && !result.has_upper && result.lower == 0 &&
        result.upper == 0);

  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 2))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 1))));
  CHECK(!test_ixs_integer_range_facts(contradictory, x, &result));
  CHECK(!result.has_lower && !result.has_upper && result.lower == 0 &&
        result.upper == 0);

  input.has_upper = false;
  input.lower_p = INT64_MAX;
  input.lower_q = 1;
  CHECK(ixs_facts_assume_range(overflow_one_sided, x, &input));
  CHECK(ixs_facts_assume_pred(overflow_one_sided, x_mod_four));
  CHECK(test_ixs_integer_range_facts(overflow_one_sided, x, &result));
  CHECK(result.has_lower && result.lower == INT64_MAX);
  CHECK(!result.has_upper);

  input.has_upper = true;
  input.upper_p = INT64_MAX;
  input.upper_q = 1;
  CHECK(ixs_facts_assume_range(overflow_bounded, x, &input));
  CHECK(ixs_facts_assume_pred(overflow_bounded, x_mod_four));
  CHECK(!test_ixs_integer_range_facts(overflow_bounded, x, &result));
  CHECK(!result.has_lower && !result.has_upper && result.lower == 0 &&
        result.upper == 0);

  CHECK(!ixs_integer_range(ctx, other_x, NULL, 0, &result));
  CHECK(!result.has_lower && !result.has_upper && result.lower == 0 &&
        result.upper == 0);
  foreign_assumption = ixs_cmp(other, other_x, IXS_CMP_GE, ixs_int(other, 0));
  CHECK(!ixs_integer_range(ctx, x, &foreign_assumption, 1, &result));
  CHECK(!result.has_lower && !result.has_upper && result.lower == 0 &&
        result.upper == 0);
  CHECK(!test_ixs_integer_range_facts(rounded, other_x, &result));
  CHECK(!result.has_lower && !result.has_upper && result.lower == 0 &&
        result.upper == 0);
  CHECK(!test_ixs_integer_range_facts(NULL, x, &result));
  CHECK(!result.has_lower && !result.has_upper && result.lower == 0 &&
        result.upper == 0);

  input.has_lower = true;
  input.lower_p = 0;
  input.lower_q = 1;
  input.upper_p = 10;
  input.upper_q = 1;
  CHECK(ixs_facts_assume_range(oom, x, &input));
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(!test_ixs_integer_range_facts(oom, shifted, &result));
  CHECK(!result.has_lower && !result.has_upper && result.lower == 0 &&
        result.upper == 0);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_public_range_unknown(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *contradictory[2];
  ixs_range_result r;

  CHECK(!ixs_range(ctx, x, NULL, 0, &r));
  CHECK(!ixs_range(ctx, x, NULL, 0, NULL));

  contradictory[0] = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 10));
  contradictory[1] = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 5));
  CHECK(!ixs_range(ctx, x, contradictory, 2, &r));
  CHECK(!ixs_range(ctx, ixs_neg(ctx, x), contradictory, 2, &r));

  ixs_ctx_destroy(ctx);
}

static void test_public_range_int64_extrema(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_range_result r;

  CHECK(ixs_range(ctx, ixs_int(ctx, INT64_MIN), NULL, 0, &r));
  CHECK(r.has_lower);
  CHECK(r.has_upper);
  CHECK(r.lower_p == INT64_MIN && r.lower_q == 1);
  CHECK(r.upper_p == INT64_MIN && r.upper_q == 1);

  CHECK(ixs_range(ctx, ixs_int(ctx, INT64_MAX), NULL, 0, &r));
  CHECK(r.has_lower);
  CHECK(r.has_upper);
  CHECK(r.lower_p == INT64_MAX && r.lower_q == 1);
  CHECK(r.upper_p == INT64_MAX && r.upper_q == 1);

  ixs_ctx_destroy(ctx);
}

static void test_public_range_mod_int64_min_step(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *m = ixs_sym(ctx, "m");
  ixs_node *scaled = ixs_mul(ctx, ixs_int(ctx, INT64_MIN), x);
  ixs_node *add = ixs_add(ctx, scaled, ixs_mul(ctx, ixs_int(ctx, 7), y));
  ixs_node *literal_mod = ixs_mod(ctx, scaled, ixs_int(ctx, 7));
  ixs_node *literal_add_mod = ixs_mod(ctx, add, ixs_int(ctx, 7));
  ixs_node *symbolic_mod = ixs_mod(ctx, scaled, m);
  ixs_node *exact_m = ixs_cmp(ctx, m, IXS_CMP_EQ, ixs_int(ctx, 7));
  ixs_node *is_zero = ixs_cmp(ctx, symbolic_mod, IXS_CMP_EQ, ixs_int(ctx, 0));
  ixs_range_result r;

  CHECK(ixs_range(ctx, literal_mod, NULL, 0, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 6 && r.upper_q == 1);

  CHECK(ixs_range(ctx, literal_add_mod, NULL, 0, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 6 && r.upper_q == 1);

  CHECK(ixs_range(ctx, symbolic_mod, &exact_m, 1, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 6 && r.upper_q == 1);
  CHECK(ixs_check(ctx, is_zero, &exact_m, 1) == IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_public_range_mod_requires_positive_divisor(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *m = ixs_sym(ctx, "m");
  ixs_node *expr = ixs_mod(ctx, x, m);
  ixs_node *positive[2];
  ixs_node *negative;
  ixs_node *mixed[2];
  ixs_range_result r;

  positive[0] = ixs_cmp(ctx, m, IXS_CMP_GE, ixs_int(ctx, 1));
  positive[1] = ixs_cmp(ctx, m, IXS_CMP_LE, ixs_int(ctx, 8));
  CHECK(ixs_range(ctx, expr, positive, 2, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 7 && r.upper_q == 1);

  negative = ixs_cmp(ctx, m, IXS_CMP_LT, ixs_int(ctx, 0));
  CHECK(!ixs_range(ctx, expr, &negative, 1, &r));
  CHECK(!ixs_range(ctx, expr, NULL, 0, &r));

  mixed[0] = ixs_cmp(ctx, m, IXS_CMP_GE, ixs_int(ctx, -1));
  mixed[1] = ixs_cmp(ctx, m, IXS_CMP_LE, ixs_int(ctx, 8));
  CHECK(!ixs_range(ctx, expr, mixed, 2, &r));

  ixs_ctx_destroy(ctx);
}

static void test_public_range_mod_nonnegative_dividend_cap(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "mod_dividend_cap_x");
  ixs_node *d = ixs_sym(ctx, "mod_dividend_cap_d");
  ixs_node *remainder = ixs_mod(ctx, x, d);
  ixs_facts *nonnegative = ixs_facts_create(ctx);
  ixs_facts *crossing = ixs_facts_create(ctx);
  ixs_range_result input = {true, true, 0, 1, 100, 1};
  ixs_integer_range_result result;

  CHECK(ctx && x && d && remainder && nonnegative && crossing);
  CHECK(ixs_facts_assume_range(nonnegative, x, &input));
  input.lower_p = 4;
  input.upper_p = 1000;
  CHECK(ixs_facts_assume_range(nonnegative, d, &input));
  CHECK(test_ixs_integer_range_facts(nonnegative, remainder, &result));
  CHECK(result.has_lower && result.lower == 0);
  CHECK(result.has_upper && result.upper == 100);

  input.lower_p = -100;
  input.upper_p = 100;
  CHECK(ixs_facts_assume_range(crossing, x, &input));
  input.lower_p = 4;
  input.upper_p = 1000;
  CHECK(ixs_facts_assume_range(crossing, d, &input));
  CHECK(test_ixs_integer_range_facts(crossing, remainder, &result));
  CHECK(result.has_lower && result.lower == 0);
  CHECK(result.has_upper && result.upper == 999);

  ixs_ctx_destroy(ctx);
}

static void test_public_range_mod_congruence_intersection(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "mod_intersection_x");
  ixs_range_result input;
  ixs_range_result result;
  ixs_facts *cycle = ixs_facts_create(ctx);
  ixs_facts *partial = ixs_facts_create(ctx);
  ixs_facts *negative = ixs_facts_create(ctx);
  ixs_facts *exact = ixs_facts_create(ctx);
  ixs_facts *extreme = ixs_facts_create(ctx);
  ixs_facts *fallback = ixs_facts_create(ctx);
  ixs_facts *insufficient = ixs_facts_create(ctx);
  ixs_facts *incompatible = ixs_facts_create(ctx);
  ixs_node *mod8 = ixs_mod(ctx, x, ixs_int(ctx, 8));

  input.has_lower = true;
  input.has_upper = true;
  input.lower_q = 1;
  input.upper_q = 1;

  input.lower_p = -100;
  input.upper_p = 100;
  CHECK(ixs_facts_assume_range(cycle, x, &input));
  CHECK(ixs_facts_assume_pred(cycle,
                              ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 6)),
                                      IXS_CMP_EQ, ixs_int(ctx, 1))));
  CHECK(test_ixs_range_facts(cycle, mod8, &result));
  CHECK(result.has_lower && result.lower_p == 1 && result.lower_q == 1);
  CHECK(result.has_upper && result.upper_p == 7 && result.upper_q == 1);

  input.lower_p = 0;
  input.upper_p = 1;
  CHECK(ixs_facts_assume_range(partial, x, &input));
  CHECK(ixs_facts_assume_pred(partial,
                              ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 2)),
                                      IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(
      test_ixs_range_facts(partial, ixs_mod(ctx, x, ixs_int(ctx, 3)), &result));
  CHECK(result.has_lower && result.lower_p == 0);
  CHECK(result.has_upper && result.upper_p == 0);

  input.lower_p = -10;
  input.upper_p = 0;
  CHECK(ixs_facts_assume_range(negative, x, &input));
  CHECK(ixs_facts_assume_pred(negative,
                              ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 6)),
                                      IXS_CMP_EQ, ixs_int(ctx, 1))));
  CHECK(test_ixs_range_facts(negative, mod8, &result));
  CHECK(result.has_lower && result.lower_p == 3);
  CHECK(result.has_upper && result.upper_p == 3);

  CHECK(ixs_facts_assume_pred(exact,
                              ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 32)),
                                      IXS_CMP_EQ, ixs_int(ctx, 5))));
  CHECK(test_ixs_range_facts(exact, mod8, &result));
  CHECK(result.has_lower && result.lower_p == 5);
  CHECK(result.has_upper && result.upper_p == 5);

  input.lower_p = INT64_MAX - 1;
  input.upper_p = INT64_MAX;
  CHECK(ixs_facts_assume_range(extreme, x, &input));
  CHECK(ixs_facts_assume_pred(
      extreme, ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, INT64_MAX)),
                       IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(test_ixs_range_facts(extreme, mod8, &result));
  CHECK(result.has_lower && result.lower_p == 7);
  CHECK(result.has_upper && result.upper_p == 7);

  input.lower_p = -10000;
  input.upper_p = 0;
  CHECK(ixs_facts_assume_range(fallback, x, &input));
  CHECK(ixs_facts_assume_pred(fallback,
                              ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 2)),
                                      IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(test_ixs_range_facts(fallback, ixs_mod(ctx, x, ixs_int(ctx, 10007)),
                             &result));
  CHECK(result.has_lower && result.lower_p == 0);
  CHECK(result.has_upper && result.upper_p == 10005);

  input.lower_p = -100;
  input.upper_p = 100;
  CHECK(ixs_facts_assume_range(insufficient, x, &input));
  CHECK(test_ixs_range_facts(insufficient, mod8, &result));
  CHECK(result.has_lower && result.lower_p == 0);
  CHECK(result.has_upper && result.upper_p == 7);

  input.lower_p = 0;
  input.upper_p = 2;
  CHECK(ixs_facts_assume_range(incompatible, x, &input));
  CHECK(ixs_facts_assume_pred(incompatible,
                              ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 4)),
                                      IXS_CMP_EQ, ixs_int(ctx, 3))));
  CHECK(!test_ixs_range_facts(incompatible, mod8, &result));

  ixs_ctx_destroy(ctx);
}

static void assume_signed_i32_grid(ixs_ctx *ctx, ixs_facts *facts,
                                   ixs_node *symbol) {
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, symbol, IXS_CMP_GE, ixs_int(ctx, INT32_MIN))));
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, symbol, IXS_CMP_LE, ixs_int(ctx, INT32_MAX))));
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, ixs_mod(ctx, symbol, ixs_int(ctx, 16)), IXS_CMP_EQ,
                     ixs_int(ctx, 0))));
}

static void test_public_range_congruence_tightens_endpoints(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "congruent_endpoint_x");
  ixs_node *negated = ixs_mul(ctx, ixs_int(ctx, -1), x);
  ixs_node *plus_seven = ixs_add(ctx, x, ixs_int(ctx, 7));
  ixs_node *plus_sixteen = ixs_add(ctx, x, ixs_int(ctx, 16));
  ixs_facts *aligned = ixs_facts_create(ctx);
  ixs_facts *residue_seven = ixs_facts_create(ctx);
  ixs_facts *unaligned = ixs_facts_create(ctx);
  ixs_range_result range;

  assume_signed_i32_grid(ctx, aligned, x);
  CHECK(test_ixs_range_facts(aligned, x, &range));
  CHECK(range.has_lower && range.lower_p == INT32_MIN && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == INT64_C(2147483632) &&
        range.upper_q == 1);
  CHECK(test_ixs_range_facts(aligned, negated, &range));
  CHECK(range.has_lower && range.lower_p == INT64_C(-2147483632) &&
        range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == INT64_C(2147483648) &&
        range.upper_q == 1);
  CHECK(test_ixs_check_facts(aligned, ixs_cmp(ctx, plus_seven, IXS_CMP_LE,
                                              ixs_int(ctx, INT32_MAX))) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(aligned, ixs_cmp(ctx, plus_sixteen, IXS_CMP_LE,
                                              ixs_int(ctx, INT32_MAX))) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(
      residue_seven, ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, INT32_MIN))));
  CHECK(ixs_facts_assume_pred(
      residue_seven, ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, INT32_MAX))));
  CHECK(ixs_facts_assume_pred(residue_seven,
                              ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 16)),
                                      IXS_CMP_EQ, ixs_int(ctx, 7))));
  CHECK(test_ixs_range_facts(residue_seven, x, &range));
  CHECK(range.has_lower && range.lower_p == INT64_C(-2147483641) &&
        range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == INT64_C(2147483639) &&
        range.upper_q == 1);

  CHECK(ixs_facts_assume_pred(
      unaligned, ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, INT32_MIN))));
  CHECK(ixs_facts_assume_pred(
      unaligned, ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, INT32_MAX))));
  CHECK(test_ixs_check_facts(unaligned, ixs_cmp(ctx, plus_seven, IXS_CMP_LE,
                                                ixs_int(ctx, INT32_MAX))) ==
        IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_public_range_congruence_alignment_overflow(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "congruence_overflow_x");
  ixs_node *even = ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 2)), IXS_CMP_EQ,
                           ixs_int(ctx, 0));
  ixs_node *odd = ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 2)), IXS_CMP_EQ,
                          ixs_int(ctx, 1));
  ixs_facts *lower_overflow = ixs_facts_create(ctx);
  ixs_facts *upper_underflow = ixs_facts_create(ctx);
  ixs_facts *incompatible = ixs_facts_create(ctx);
  ixs_range_result input;
  ixs_range_result range;

  input.has_lower = true;
  input.has_upper = false;
  input.lower_p = INT64_MAX;
  input.lower_q = 1;
  input.upper_p = 0;
  input.upper_q = 1;
  CHECK(ixs_facts_assume_range(lower_overflow, x, &input));
  CHECK(ixs_facts_assume_pred(lower_overflow, even));
  CHECK(test_ixs_range_facts(lower_overflow, x, &range));
  CHECK(range.has_lower && range.lower_p == INT64_MAX && range.lower_q == 1);
  CHECK(!range.has_upper);

  input.has_lower = false;
  input.has_upper = true;
  input.lower_p = 0;
  input.upper_p = INT64_MIN;
  CHECK(ixs_facts_assume_range(upper_underflow, x, &input));
  CHECK(ixs_facts_assume_pred(upper_underflow, odd));
  CHECK(test_ixs_range_facts(upper_underflow, x, &range));
  CHECK(!range.has_lower);
  CHECK(range.has_upper && range.upper_p == INT64_MIN && range.upper_q == 1);

  input.has_lower = true;
  input.lower_p = INT64_MAX;
  input.upper_p = INT64_MAX;
  CHECK(ixs_facts_assume_range(incompatible, x, &input));
  CHECK(ixs_facts_assume_pred(incompatible, even));
  CHECK(!test_ixs_range_facts(incompatible, x, &range));

  ixs_ctx_destroy(ctx);
}

static bool assume_unit_difference_upper(ixs_ctx *ctx, ixs_facts *facts,
                                         ixs_node *lhs, ixs_node *rhs,
                                         ixs_cmp_op op, int64_t upper) {
  return ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, ixs_sub(ctx, lhs, rhs), op, ixs_int(ctx, upper)));
}

static void test_public_range_difference_constraint_propagation(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *iv = ixs_sym(ctx, "difference_loop_iv");
  ixs_node *trip = ixs_sym(ctx, "difference_loop_trip");
  ixs_node *upper_x = ixs_sym(ctx, "difference_upper_x");
  ixs_node *upper_y = ixs_sym(ctx, "difference_upper_y");
  ixs_node *upper_z = ixs_sym(ctx, "difference_upper_z");
  ixs_node *lower_x = ixs_sym(ctx, "difference_lower_x");
  ixs_node *lower_y = ixs_sym(ctx, "difference_lower_y");
  ixs_node *lower_z = ixs_sym(ctx, "difference_lower_z");
  ixs_node *aligned_x = ixs_sym(ctx, "difference_aligned_x");
  ixs_node *aligned_y = ixs_sym(ctx, "difference_aligned_y");
  ixs_node *unknown_x = ixs_sym(ctx, "difference_unknown_x");
  ixs_node *unknown_y = ixs_sym(ctx, "difference_unknown_y");
  ixs_node *scaled_x = ixs_sym(ctx, "difference_scaled_x");
  ixs_node *scaled_y = ixs_sym(ctx, "difference_scaled_y");
  ixs_node *overflow_x = ixs_sym(ctx, "difference_overflow_x");
  ixs_node *overflow_y = ixs_sym(ctx, "difference_overflow_y");
  ixs_facts *loop = ixs_facts_create(ctx);
  ixs_facts *upper = ixs_facts_create(ctx);
  ixs_facts *lower = ixs_facts_create(ctx);
  ixs_facts *aligned = ixs_facts_create(ctx);
  ixs_facts *aligned_lower = ixs_facts_create(ctx);
  ixs_facts *unknown = ixs_facts_create(ctx);
  ixs_facts *scaled = ixs_facts_create(ctx);
  ixs_facts *overflow = ixs_facts_create(ctx);
  ixs_range_result input = {0};
  ixs_range_result range;

  CHECK(assume_unit_difference_upper(ctx, loop, iv, trip, IXS_CMP_LT, 0));
  CHECK(ixs_facts_assume_pred(loop,
                              ixs_cmp(ctx, iv, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      loop, ixs_cmp(ctx, trip, IXS_CMP_GE, ixs_int(ctx, INT32_MIN))));
  CHECK(ixs_facts_assume_pred(
      loop, ixs_cmp(ctx, trip, IXS_CMP_LE, ixs_int(ctx, INT32_MAX))));
  CHECK(test_ixs_range_facts(loop, iv, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == INT64_C(2147483646) &&
        range.upper_q == 1);

  CHECK(assume_unit_difference_upper(ctx, upper, upper_x, upper_y, IXS_CMP_LT,
                                     0));
  CHECK(assume_unit_difference_upper(ctx, upper, upper_y, upper_z, IXS_CMP_LE,
                                     3));
  input.has_upper = true;
  input.upper_p = 100;
  input.upper_q = 1;
  CHECK(ixs_facts_assume_range(upper, upper_z, &input));
  CHECK(test_ixs_range_facts(upper, upper_x, &range));
  CHECK(range.has_upper && range.upper_p == 102 && range.upper_q == 1);

  CHECK(assume_unit_difference_upper(ctx, lower, lower_x, lower_y, IXS_CMP_GT,
                                     0));
  CHECK(assume_unit_difference_upper(ctx, lower, lower_y, lower_z, IXS_CMP_GE,
                                     3));
  input.has_upper = false;
  input.has_lower = true;
  input.lower_p = -100;
  input.lower_q = 1;
  CHECK(ixs_facts_assume_range(lower, lower_z, &input));
  CHECK(test_ixs_range_facts(lower, lower_x, &range));
  CHECK(range.has_lower && range.lower_p == -96 && range.lower_q == 1);

  CHECK(assume_unit_difference_upper(ctx, aligned, aligned_x, aligned_y,
                                     IXS_CMP_LE, 0));
  CHECK(ixs_facts_assume_pred(
      aligned, ixs_cmp(ctx, aligned_y, IXS_CMP_LE, ixs_int(ctx, 10))));
  CHECK(ixs_facts_assume_pred(
      aligned, ixs_cmp(ctx, ixs_mod(ctx, aligned_y, ixs_int(ctx, 4)),
                       IXS_CMP_EQ, ixs_int(ctx, 3))));
  CHECK(test_ixs_range_facts(aligned, aligned_x, &range));
  CHECK(range.has_upper && range.upper_p == 7 && range.upper_q == 1);

  CHECK(assume_unit_difference_upper(ctx, aligned_lower, aligned_x, aligned_y,
                                     IXS_CMP_GE, 0));
  CHECK(ixs_facts_assume_pred(
      aligned_lower, ixs_cmp(ctx, aligned_y, IXS_CMP_GE, ixs_int(ctx, -10))));
  CHECK(ixs_facts_assume_pred(
      aligned_lower, ixs_cmp(ctx, ixs_mod(ctx, aligned_y, ixs_int(ctx, 4)),
                             IXS_CMP_EQ, ixs_int(ctx, 3))));
  CHECK(test_ixs_range_facts(aligned_lower, aligned_x, &range));
  CHECK(range.has_lower && range.lower_p == -9 && range.lower_q == 1);

  CHECK(assume_unit_difference_upper(ctx, unknown, unknown_x, unknown_y,
                                     IXS_CMP_LT, 0));
  CHECK(ixs_facts_assume_pred(
      unknown, ixs_cmp(ctx, unknown_y, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(!test_ixs_range_facts(unknown, unknown_x, &range) || !range.has_upper);

  CHECK(ixs_facts_assume_pred(
      scaled,
      ixs_cmp(ctx,
              ixs_sub(ctx, ixs_mul(ctx, ixs_int(ctx, 2), scaled_x), scaled_y),
              IXS_CMP_LT, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      scaled, ixs_cmp(ctx, scaled_y, IXS_CMP_LE, ixs_int(ctx, 100))));
  CHECK(!test_ixs_range_facts(scaled, scaled_x, &range) || !range.has_upper);

  CHECK(assume_unit_difference_upper(ctx, overflow, overflow_x, overflow_y,
                                     IXS_CMP_LE, 1));
  CHECK(ixs_facts_assume_pred(
      overflow, ixs_cmp(ctx, overflow_y, IXS_CMP_LE, ixs_int(ctx, INT64_MAX))));
  CHECK(!test_ixs_range_facts(overflow, overflow_x, &range) ||
        !range.has_upper);

  ixs_ctx_destroy(ctx);
}

static void check_public_exact_integer_range(ixs_facts *facts, ixs_node *expr,
                                             int64_t expected) {
  ixs_range_result range;
  CHECK(test_ixs_range_facts(facts, expr, &range));
  CHECK(range.has_lower && range.lower_p == expected && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == expected && range.upper_q == 1);
}

static void check_public_integer_range(ixs_facts *facts, ixs_node *expr,
                                       int64_t lower, int64_t upper) {
  ixs_range_result range;
  CHECK(test_ixs_range_facts(facts, expr, &range));
  CHECK(range.has_lower && range.lower_p == lower && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == upper && range.upper_q == 1);
}

static void test_public_exact_residual_relation_chain_and_boundaries(void) {
  enum { CHAIN_LENGTH = 320 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *two = ixs_int(ctx, 2);
  ixs_node *two32 = ixs_int(ctx, INT64_C(4294967296));
  ixs_node *nodes[CHAIN_LENGTH + 1];
  ixs_node *predicates[CHAIN_LENGTH];
  ixs_facts *chain;
  ixs_node *appended;
  ixs_node *uncached_appended;
  ixs_node *base;
  ixs_node *middle;
  ixs_node *tail;
  ixs_node *boundary_predicates[2];
  ixs_facts *boundary;
  ixs_node *wide_negative;
  ixs_node *wide_positive;
  ixs_node *wide_tail;
  ixs_node *wide_predicates[2];
  ixs_facts *wide;
  int64_t delta;
  unsigned i;

  for (i = 0; i <= CHAIN_LENGTH; i++) {
    char name[48];
    snprintf(name, sizeof(name), "exact_residual_chain_%u", i);
    nodes[i] = ixs_mod(ctx, ixs_sym(ctx, name), two32);
    if (i != 0)
      predicates[i - 1u] =
          ixs_cmp(ctx, nodes[i], IXS_CMP_EQ, ixs_add(ctx, nodes[i - 1u], one));
  }
  chain = ixs_facts_create(ctx);
  CHECK(ixs_facts_assume_preds(chain, predicates, CHAIN_LENGTH));
  CHECK(test_ixs_constant_difference_facts(chain, nodes[CHAIN_LENGTH], nodes[0],
                                           &delta));
  CHECK(delta == CHAIN_LENGTH);

  appended = ixs_mod(ctx, ixs_sym(ctx, "exact_residual_chain_appended"), two32);
  CHECK(!test_ixs_constant_difference_facts(chain, appended, nodes[0], &delta));
  CHECK(ixs_facts_assume_pred(chain,
                              ixs_cmp(ctx, appended, IXS_CMP_EQ,
                                      ixs_add(ctx, nodes[CHAIN_LENGTH], one))));
  CHECK(test_ixs_constant_difference_facts(chain, appended, nodes[0], &delta));
  CHECK(delta == CHAIN_LENGTH + 1);
  uncached_appended =
      ixs_mod(ctx, ixs_sym(ctx, "exact_residual_chain_uncached"), two32);
  CHECK(ixs_facts_assume_pred(chain, ixs_cmp(ctx, uncached_appended, IXS_CMP_EQ,
                                             ixs_add(ctx, appended, one))));
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  {
    ixs_constant_difference_result query_result =
        ixs_constant_difference_facts(chain, uncached_appended, nodes[0]);
    CHECK(query_result.status == IXS_FACT_QUERY_OOM);
    CHECK(!query_result.available && query_result.difference == 0);
  }
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(test_ixs_constant_difference_facts(chain, uncached_appended, nodes[0],
                                           &delta));
  CHECK(delta == CHAIN_LENGTH + 2);

  base = ixs_floor(ctx, ixs_div(ctx, ixs_sym(ctx, "exact_boundary_base"), two));
  middle =
      ixs_floor(ctx, ixs_div(ctx, ixs_sym(ctx, "exact_boundary_middle"), two));
  tail = ixs_floor(ctx, ixs_div(ctx, ixs_sym(ctx, "exact_boundary_tail"), two));
  boundary_predicates[0] =
      ixs_cmp(ctx, middle, IXS_CMP_EQ,
              ixs_add(ctx, base, ixs_int(ctx, INT64_MIN + INT64_C(1))));
  boundary_predicates[1] =
      ixs_cmp(ctx, tail, IXS_CMP_EQ, ixs_add(ctx, middle, ixs_int(ctx, -1)));
  boundary = ixs_facts_create(ctx);
  CHECK(ixs_facts_assume_preds(boundary, boundary_predicates, 2));
  CHECK(!test_ixs_constant_difference_facts(boundary, base, tail, &delta));
  CHECK(test_ixs_constant_difference_facts(boundary, tail, base, &delta));
  CHECK(delta == INT64_MIN);

  wide_negative =
      ixs_floor(ctx, ixs_div(ctx, ixs_sym(ctx, "exact_wide_negative"), two));
  wide_positive =
      ixs_floor(ctx, ixs_div(ctx, ixs_sym(ctx, "exact_wide_positive"), two));
  wide_tail =
      ixs_floor(ctx, ixs_div(ctx, ixs_sym(ctx, "exact_wide_tail"), two));
  wide_predicates[0] =
      ixs_cmp(ctx,
              ixs_add(ctx, ixs_sub(ctx, wide_positive, wide_negative),
                      ixs_int(ctx, INT64_MIN)),
              IXS_CMP_EQ, ixs_int(ctx, 0));
  wide_predicates[1] = ixs_cmp(ctx, wide_tail, IXS_CMP_EQ,
                               ixs_add(ctx, wide_positive, ixs_int(ctx, -1)));
  wide = ixs_facts_create(ctx);
  CHECK(ixs_facts_assume_preds(wide, wide_predicates, 2));
  CHECK(test_ixs_constant_difference_facts(wide, wide_tail, wide_negative,
                                           &delta));
  CHECK(delta == INT64_MAX);

  ixs_ctx_destroy(ctx);
}

static void test_public_exact_residual_wide_term_partition(void) {
  enum { SIDE_TERMS = 192 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *lhs = ixs_int(ctx, 0);
  ixs_node *rhs = ixs_int(ctx, 0);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_range_result zero = {.has_lower = true,
                           .has_upper = true,
                           .lower_p = 0,
                           .lower_q = 1,
                           .upper_p = 0,
                           .upper_q = 1};
  int64_t delta;
  unsigned i;

  for (i = 0; i < SIDE_TERMS; i++) {
    char lhs_name[48];
    char rhs_name[48];
    snprintf(lhs_name, sizeof(lhs_name), "wide_relation_lhs_%u", i);
    snprintf(rhs_name, sizeof(rhs_name), "wide_relation_rhs_%u", i);
    lhs = ixs_add(ctx, lhs, ixs_sym(ctx, lhs_name));
    rhs = ixs_add(ctx, rhs, ixs_sym(ctx, rhs_name));
  }
  CHECK(ixs_facts_assume_pred(
      facts,
      ixs_cmp(ctx, lhs, IXS_CMP_EQ, ixs_add(ctx, rhs, ixs_int(ctx, 7)))));
  CHECK(test_ixs_constant_difference_facts(facts, lhs, rhs, &delta));
  CHECK(delta == 7);
  CHECK(ixs_facts_assume_range(facts, rhs, &zero));
  check_public_exact_integer_range(facts, lhs, 7);

  ixs_ctx_destroy(ctx);
}

static void test_public_exact_relation_disconnected_fanout(void) {
  enum { DISCONNECTED_EDGES = 512, PREDICATE_COUNT = DISCONNECTED_EDGES + 1 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *modulus = ixs_int(ctx, INT64_C(4294967296));
  ixs_node *predicates[PREDICATE_COUNT];
  ixs_node *target_lhs =
      ixs_mod(ctx, ixs_sym(ctx, "disconnected_target_lhs"), modulus);
  ixs_node *target_rhs =
      ixs_mod(ctx, ixs_sym(ctx, "disconnected_target_rhs"), modulus);
  ixs_facts *facts = ixs_facts_create(ctx);
  int64_t delta = 0;
  unsigned i;

  predicates[0] = ixs_cmp(ctx, target_lhs, IXS_CMP_EQ,
                          ixs_add(ctx, target_rhs, ixs_int(ctx, 7)));
  for (i = 0; i < DISCONNECTED_EDGES; i++) {
    char lhs_name[48];
    char rhs_name[48];
    ixs_node *lhs;
    ixs_node *rhs;
    (void)snprintf(lhs_name, sizeof(lhs_name), "disconnected_lhs_%u", i);
    (void)snprintf(rhs_name, sizeof(rhs_name), "disconnected_rhs_%u", i);
    lhs = ixs_mod(ctx, ixs_sym(ctx, lhs_name), modulus);
    rhs = ixs_mod(ctx, ixs_sym(ctx, rhs_name), modulus);
    predicates[i + 1u] =
        ixs_cmp(ctx, lhs, IXS_CMP_EQ,
                ixs_add(ctx, rhs, ixs_int(ctx, (int64_t)(i & 7u))));
  }
  CHECK(ixs_facts_assume_preds(facts, predicates, PREDICATE_COUNT));
  CHECK(test_ixs_constant_difference_facts(facts, target_lhs, target_rhs,
                                           &delta));
  CHECK(delta == 7);
  ixs_ctx_destroy(ctx);
}

static void test_public_exact_equality_range_projection(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *s = ixs_sym(ctx, "equality_projection_s");
  ixs_node *d = ixs_sym(ctx, "equality_projection_d");
  ixs_node *x = ixs_sym(ctx, "equality_projection_x");
  ixs_node *y = ixs_sym(ctx, "equality_projection_y");
  ixs_node *z = ixs_sym(ctx, "equality_projection_z");
  ixs_node *two32 = ixs_int(ctx, INT64_C(4294967296));
  ixs_node *eight = ixs_int(ctx, 8);
  ixs_node *sixteen = ixs_int(ctx, 16);
  ixs_node *wrap32_equality =
      ixs_cmp(ctx, s, IXS_CMP_EQ, ixs_mod(ctx, s, two32));
  ixs_node *dynamic = ixs_cmp(ctx, s, IXS_CMP_EQ, ixs_mod(ctx, s, d));
  ixs_node *d_is_eight = ixs_cmp(ctx, d, IXS_CMP_EQ, eight);
  ixs_node *forward[2] = {dynamic, d_is_eight};
  ixs_node *reverse[2] = {d_is_eight, dynamic};
  ixs_node *floored = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 4)));
  ixs_node *floored_wrap = ixs_mod(ctx, floored, sixteen);
  ixs_node *first = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 2)));
  ixs_node *second = ixs_ceil(ctx, ixs_div(ctx, y, ixs_int(ctx, 3)));
  ixs_node *transitive[2] = {
      ixs_cmp(ctx, first, IXS_CMP_EQ, second),
      ixs_cmp(ctx, second, IXS_CMP_EQ, ixs_mod(ctx, second, sixteen))};
  ixs_node *reverse_transitive[2] = {transitive[1], transitive[0]};
  ixs_node *partial = ixs_floor(ctx, ixs_div(ctx, x, d));
  ixs_node *partial_predicates[2] = {
      ixs_cmp(ctx, s, IXS_CMP_EQ, partial),
      ixs_cmp(ctx, partial, IXS_CMP_EQ, ixs_mod(ctx, y, eight))};
  ixs_node *d_nonzero = ixs_cmp(ctx, d, IXS_CMP_NE, ixs_int(ctx, 0));
  ixs_node *ratio = ixs_div(ctx, x, d);
  ixs_node *ratio_equality = ixs_cmp(ctx, ratio, IXS_CMP_EQ, z);
  ixs_range_result half = {.has_lower = true,
                           .has_upper = true,
                           .lower_p = 1,
                           .lower_q = 2,
                           .upper_p = 1,
                           .upper_q = 2};
  ixs_facts *wrap32 = ixs_facts_create(ctx);
  ixs_facts *forward_facts = ixs_facts_create(ctx);
  ixs_facts *reverse_facts = ixs_facts_create(ctx);
  ixs_facts *equality_first = ixs_facts_create(ctx);
  ixs_facts *divisor_first = ixs_facts_create(ctx);
  ixs_facts *arbitrary = ixs_facts_create(ctx);
  ixs_facts *transitive_facts = ixs_facts_create(ctx);
  ixs_facts *reverse_transitive_facts = ixs_facts_create(ctx);
  ixs_facts *partial_facts = ixs_facts_create(ctx);
  ixs_facts *integer_facts = ixs_facts_create(ctx);
  ixs_facts *integer_conflict = ixs_facts_create(ctx);
  ixs_facts *range_conflict = ixs_facts_create(ctx);
  ixs_facts *substitution_source = ixs_facts_create(ctx);
  ixs_facts *substitution_result = ixs_facts_create(ctx);
  ixs_range_result range;

  CHECK(ixs_facts_assume_pred(wrap32, wrap32_equality));
  check_public_integer_range(wrap32, s, 0, INT64_C(4294967295));

  CHECK(ixs_facts_assume_preds(forward_facts, forward, 2));
  CHECK(ixs_facts_assume_preds(reverse_facts, reverse, 2));
  check_public_integer_range(forward_facts, s, 0, 7);
  check_public_integer_range(reverse_facts, s, 0, 7);

  CHECK(ixs_facts_assume_pred(equality_first, dynamic));
  CHECK(!test_ixs_range_facts(equality_first, s, &range));
  CHECK(ixs_facts_assume_pred(equality_first, d_is_eight));
  check_public_integer_range(equality_first, s, 0, 7);
  CHECK(ixs_facts_assume_pred(divisor_first, d_is_eight));
  CHECK(ixs_facts_assume_pred(divisor_first, dynamic));
  check_public_integer_range(divisor_first, s, 0, 7);

  CHECK(ixs_facts_assume_pred(arbitrary,
                              ixs_cmp(ctx, floored, IXS_CMP_EQ, floored_wrap)));
  check_public_integer_range(arbitrary, floored, 0, 15);

  CHECK(ixs_facts_assume_pred(substitution_source,
                              ixs_cmp(ctx, floored, IXS_CMP_EQ, floored_wrap)));
  CHECK(ixs_facts_substitute(substitution_result, substitution_source, x, z));
  check_public_integer_range(substitution_result,
                             ixs_floor(ctx, ixs_div(ctx, z, ixs_int(ctx, 4))),
                             0, 15);

  CHECK(ixs_facts_assume_preds(transitive_facts, transitive, 2));
  CHECK(
      ixs_facts_assume_preds(reverse_transitive_facts, reverse_transitive, 2));
  check_public_integer_range(transitive_facts, first, 0, 15);
  check_public_integer_range(reverse_transitive_facts, first, 0, 15);

  CHECK(ixs_facts_assume_pred(partial_facts, partial_predicates[0]));
  CHECK(ixs_facts_assume_pred(partial_facts, partial_predicates[1]));
  CHECK(test_ixs_check_defined_facts(partial_facts, partial) ==
        IXS_CHECK_UNKNOWN);
  CHECK(!test_ixs_range_facts(partial_facts, s, &range));
  CHECK(ixs_facts_assume_pred(partial_facts, d_nonzero));
  CHECK(test_ixs_check_defined_facts(partial_facts, partial) == IXS_CHECK_TRUE);
  check_public_integer_range(partial_facts, s, 0, 7);

  CHECK(ixs_facts_assume_pred(integer_facts, ratio_equality));
  CHECK(test_ixs_check_integer_valued_facts(integer_facts, ratio) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_facts_assume_pred(integer_facts, d_is_eight));
  CHECK(test_ixs_check_integer_valued_facts(integer_facts, ratio) ==
        IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(integer_conflict, ratio_equality));
  CHECK(ixs_facts_assume_pred(integer_conflict, d_is_eight));
  CHECK(ixs_facts_assume_range(integer_conflict, ratio, &half));
  CHECK(test_ixs_check_integer_valued_facts(integer_conflict, ratio) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(
      range_conflict, ixs_cmp(ctx, s, IXS_CMP_EQ, ixs_mod(ctx, s, eight))));
  CHECK(ixs_facts_assume_pred(range_conflict,
                              ixs_cmp(ctx, s, IXS_CMP_EQ, sixteen)));
  CHECK(!test_ixs_range_facts(range_conflict, s, &range));

  ixs_ctx_destroy(ctx);
}

static void test_public_exact_scaled_residual_range_projection(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *workitem = ixs_sym(ctx, "exact_scaled_workitem");
  ixs_node *body = ixs_sym(ctx, "exact_scaled_body");
  ixs_node *scaled =
      ixs_mul(ctx, ixs_int(ctx, 128), ixs_mod(ctx, workitem, ixs_int(ctx, 16)));
  ixs_node *predicates[3] = {
      ixs_cmp(ctx, workitem, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, ixs_add(ctx, ixs_int(ctx, -INT64_C(2147483647)), workitem),
              IXS_CMP_LE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, ixs_sub(ctx, body, scaled), IXS_CMP_EQ, ixs_int(ctx, 0))};
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_range_result range;

  CHECK(ixs_facts_assume_preds(facts, predicates, 3));
  CHECK(test_ixs_range_facts(facts, body, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 1920 && range.upper_q == 1);
  CHECK(test_ixs_check_facts(facts,
                             ixs_cmp(ctx, body, IXS_CMP_GE, ixs_int(ctx, 0))) ==
        IXS_CHECK_TRUE);
  CHECK(
      test_ixs_check_facts(facts, ixs_cmp(ctx, body, IXS_CMP_LE,
                                          ixs_int(ctx, INT64_C(4294967295)))) ==
      IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_bounds_exact_relation_fork_owns_graph(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_session_binding binding;
  ixs_bounds source;
  ixs_bounds forked;
  ixs_node *modulus = ixs_int(ctx, 16);
  ixs_node *lhs = ixs_mod(ctx, ixs_sym(ctx, "fork_relation_lhs"), modulus);
  ixs_node *rhs = ixs_mod(ctx, ixs_sym(ctx, "fork_relation_rhs"), modulus);
  ixs_interval rhs_range = ixs_interval_range(4, 1, 6, 1);
  ixs_interval lhs_range;
  size_t i;
  bool saw_edge = false;

  CHECK(ctx && lhs && rhs);
  CHECK(ixs_session_bind(&binding, IXS_TEST_SESSION(ctx)) == ctx);
  CHECK(ixs_bounds_init_ctx(&source, ctx, &ctx->scratch));
  CHECK(ixs_bounds_add_assumption(
      &source,
      ixs_cmp(ctx, lhs, IXS_CMP_EQ, ixs_add(ctx, rhs, ixs_int(ctx, 3)))));
  ixs_bounds_add_expr(&source, rhs, rhs_range);
  CHECK(!source.oom && source.nequalities == 1);
  CHECK(ixs_bounds_fork(&forked, &source));
  CHECK(forked.nequalities == source.nequalities);
  CHECK(forked.equality_endpoints != source.equality_endpoints);
  CHECK(forked.equality_endpoint_index != source.equality_endpoint_index);
  CHECK(forked.equality_index != source.equality_index);
  for (i = 0; i < source.equality_index_cap; i++) {
    if (!source.equality_index[i])
      continue;
    saw_edge = true;
    CHECK(forked.equality_index[i] != NULL);
    CHECK(forked.equality_index[i] != source.equality_index[i]);
  }
  CHECK(saw_edge);

  ixs_bounds_destroy(&source);
  lhs_range = ixs_bounds_get(&forked, lhs);
  CHECK(lhs_range.valid && !lhs_range.lo_inf && !lhs_range.hi_inf);
  CHECK(lhs_range.lo_p == 7 && lhs_range.lo_q == 1);
  CHECK(lhs_range.hi_p == 9 && lhs_range.hi_q == 1);
  ixs_bounds_destroy(&forked);
  ixs_session_unbind(&binding);
  ixs_ctx_destroy(ctx);
}

static ixs_node *test_signed_wrap(ixs_ctx *ctx, ixs_node *value, int64_t bias,
                                  int64_t modulus) {
  return ixs_sub(ctx,
                 ixs_mod(ctx, ixs_add(ctx, ixs_int(ctx, bias), value),
                         ixs_int(ctx, modulus)),
                 ixs_int(ctx, bias));
}

static void test_public_modular_projection_difference(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *tile = ixs_sym(ctx, "modular_projection_tile");
  ixs_node *lane = ixs_sym(ctx, "modular_projection_lane");
  ixs_node *limit = ixs_sym(ctx, "modular_projection_limit");
  ixs_node *inner = ixs_mod(ctx,
                            ixs_add(ctx, ixs_int(ctx, INT64_C(2147483648)),
                                    ixs_mul(ctx, ixs_int(ctx, 256), tile)),
                            ixs_int(ctx, INT64_C(4294967296)));
  ixs_node *lane_high = ixs_mul(ctx, ixs_int(ctx, 128), lane);
  ixs_node *value0 = ixs_sub(
      ctx,
      ixs_mod(ctx,
              ixs_add(ctx, inner, ixs_xor(ctx, ixs_int(ctx, 64), lane_high)),
              ixs_int(ctx, INT64_C(4294967296))),
      ixs_int(ctx, INT64_C(2147483648)));
  ixs_node *value1 = ixs_sub(
      ctx,
      ixs_mod(ctx,
              ixs_add(ctx, inner, ixs_xor(ctx, ixs_int(ctx, 65), lane_high)),
              ixs_int(ctx, INT64_C(4294967296))),
      ixs_int(ctx, INT64_C(2147483648)));
  ixs_node *predicate0 =
      ixs_cmp(ctx, ixs_sub(ctx, value0, limit), IXS_CMP_LT, ixs_int(ctx, 0));
  ixs_node *predicate1 =
      ixs_cmp(ctx, ixs_sub(ctx, value1, limit), IXS_CMP_LT, ixs_int(ctx, 0));
  ixs_range_result int32_range = {.has_lower = true,
                                  .has_upper = true,
                                  .lower_p = INT32_MIN,
                                  .lower_q = 1,
                                  .upper_p = INT32_MAX,
                                  .upper_q = 1};
  ixs_range_result lane_range = {.has_lower = true,
                                 .has_upper = true,
                                 .lower_p = 0,
                                 .lower_q = 1,
                                 .upper_p = 31,
                                 .upper_q = 1};
  ixs_facts *wave = ixs_facts_create(ctx);
  ixs_node *x = ixs_sym(ctx, "modular_projection_x");
  ixs_node *wrapped0 = test_signed_wrap(ctx, x, 8, 16);
  ixs_node *wrapped1 =
      test_signed_wrap(ctx, ixs_add(ctx, x, ixs_int(ctx, 1)), 8, 16);
  ixs_node *wrapped2 =
      test_signed_wrap(ctx, ixs_add(ctx, x, ixs_int(ctx, 2)), 8, 16);
  ixs_node *scaled16_lhs = ixs_mul(ctx, ixs_int(ctx, 16), wrapped1);
  ixs_node *scaled16_rhs = ixs_mul(ctx, ixs_int(ctx, 16), wrapped0);
  ixs_node *scaled_overflow_lhs =
      ixs_mul(ctx, ixs_int(ctx, INT64_MAX), wrapped2);
  ixs_node *scaled_overflow_rhs =
      ixs_mul(ctx, ixs_int(ctx, INT64_MAX), wrapped0);
  ixs_facts *negative = ixs_facts_create(ctx);
  ixs_facts *ambiguous = ixs_facts_create(ctx);
  ixs_facts *boundary = ixs_facts_create(ctx);
  ixs_facts *partial = ixs_facts_create(ctx);
  ixs_range_result boundary_range = {.has_lower = true,
                                     .has_upper = true,
                                     .lower_p = 7,
                                     .lower_q = 1,
                                     .upper_p = 8,
                                     .upper_q = 1};
  ixs_range_result partial_range = {.has_lower = true,
                                    .has_upper = true,
                                    .lower_p = 8,
                                    .lower_q = 1,
                                    .upper_p = 15,
                                    .upper_q = 1};
  ixs_node *raw0 = ixs_add(ctx, wrapped0, ixs_int(ctx, 8));
  ixs_node *raw1 = ixs_add(ctx, wrapped1, ixs_int(ctx, 8));
  ixs_node *extreme_low = ixs_add(ctx, raw1, ixs_int(ctx, INT64_MIN));
  ixs_node *overflow_high = ixs_add(ctx, raw1, ixs_int(ctx, INT64_MAX));
  ixs_node *overflow_rhs = ixs_sub(ctx, raw0, ixs_int(ctx, 1));
  int64_t delta = 0;

  CHECK(ixs_facts_assume_range(wave, tile, &int32_range));
  CHECK(ixs_facts_assume_range(wave, lane, &lane_range));
  CHECK(ixs_facts_assume_range(wave, limit, &int32_range));
  CHECK(ixs_facts_assume_pred(wave,
                              ixs_cmp(ctx, ixs_mod(ctx, limit, ixs_int(ctx, 4)),
                                      IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(test_ixs_constant_difference_facts(wave, value1, value0, &delta));
  CHECK(delta == 1);
  CHECK(test_ixs_equivalent_facts(wave, predicate0, predicate1) ==
        IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(negative,
                              ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 4)),
                                      IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(
      test_ixs_constant_difference_facts(negative, wrapped1, wrapped0, &delta));
  CHECK(delta == 1);
  CHECK(test_ixs_constant_difference_facts(negative, scaled16_lhs, scaled16_rhs,
                                           &delta));
  CHECK(delta == 16);
  CHECK(!test_ixs_constant_difference_facts(negative, scaled_overflow_lhs,
                                            scaled_overflow_rhs, &delta));
  CHECK(
      test_ixs_constant_difference_facts(negative, extreme_low, raw0, &delta));
  CHECK(delta == INT64_MIN + 1);
  CHECK(!test_ixs_constant_difference_facts(negative, overflow_high,
                                            overflow_rhs, &delta));

  CHECK(!test_ixs_constant_difference_facts(ambiguous, wrapped1, wrapped0,
                                            &delta));
  CHECK(test_ixs_equivalent_facts(
            ambiguous, ixs_cmp(ctx, wrapped0, IXS_CMP_LT, ixs_int(ctx, 0)),
            ixs_cmp(ctx, wrapped1, IXS_CMP_LT, ixs_int(ctx, 0))) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_range(boundary, x, &boundary_range));
  CHECK(!test_ixs_constant_difference_facts(boundary, wrapped1, wrapped0,
                                            &delta));

  CHECK(ixs_facts_assume_range(partial, raw0, &partial_range));
  CHECK(
      !test_ixs_constant_difference_facts(partial, wrapped1, wrapped0, &delta));

  ixs_ctx_destroy(ctx);
}

static ixs_node *test_unsigned_remainder_wrap(ixs_ctx *ctx, ixs_node *value,
                                              ixs_node *divisor,
                                              int64_t offset) {
  ixs_node *modulus = ixs_int(ctx, INT64_C(4294967296));
  ixs_node *biased =
      offset == 0 ? value : ixs_add(ctx, value, ixs_int(ctx, offset));
  ixs_node *unsigned_value = ixs_mod(ctx, biased, modulus);
  ixs_node *unsigned_divisor = ixs_mod(ctx, divisor, modulus);
  ixs_node *remainder = ixs_mod(ctx, unsigned_value, unsigned_divisor);
  return test_signed_wrap(ctx, remainder, INT64_C(2147483648),
                          INT64_C(4294967296));
}

static ixs_node *test_fixed_width_scaled_signed_remainder(ixs_ctx *ctx,
                                                          ixs_node *value,
                                                          ixs_node *divisor) {
  ixs_node *two = ixs_int(ctx, 2);
  ixs_node *bias = ixs_int(ctx, INT64_C(2147483648));
  ixs_node *modulus = ixs_int(ctx, INT64_C(4294967296));
  ixs_node *remainder = test_unsigned_remainder_wrap(ctx, value, divisor, 0);
  ixs_node *biased = ixs_add(ctx, bias, remainder);
  ixs_node *low = ixs_mod(ctx, ixs_mul(ctx, two, remainder), modulus);
  ixs_node *sign = ixs_mod(ctx,
                           ixs_add(ctx, ixs_int(ctx, INT64_C(4294967295)),
                                   ixs_floor(ctx, ixs_div(ctx, biased, bias))),
                           modulus);
  ixs_node *values[2] = {ixs_sub(ctx, sign, modulus), sign};
  ixs_node *conditions[2] = {ixs_cmp(ctx, sign, IXS_CMP_GE, bias),
                             ixs_true(ctx)};
  ixs_node *extension = ixs_pw(ctx, 2, values, conditions);
  return ixs_add(ctx, low, ixs_mul(ctx, modulus, extension));
}

static void test_public_range_nonnegative_signed_remainder_packet(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "signed_remainder_packet_x");
  ixs_node *d = ixs_sym(ctx, "signed_remainder_packet_d");
  ixs_node *packet = test_fixed_width_scaled_signed_remainder(ctx, x, d);
  ixs_node *simplified;
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_range_result input = {true, true, 0, 1, 1073741822, 1};
  ixs_integer_range_result result;

  CHECK(ctx && x && d && packet && facts);
  CHECK(ixs_facts_assume_range(facts, x, &input));
  input.lower_p = 4;
  input.upper_p = INT32_MAX;
  CHECK(ixs_facts_assume_range(facts, d, &input));
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 2)),
                                      IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, ixs_mod(ctx, d, ixs_int(ctx, 4)),
                                      IXS_CMP_EQ, ixs_int(ctx, 0))));

  CHECK(test_ixs_integer_range_facts(facts, packet, &result));
  CHECK(result.has_lower && result.lower == 0);
  CHECK(result.has_upper && result.upper == INT64_C(2147483644));

  simplified = test_ixs_simplify_facts(facts, packet);
  CHECK(simplified && !ixs_is_error(simplified));
  CHECK(test_ixs_integer_range_facts(facts, simplified, &result));
  CHECK(result.has_lower && result.lower == 0);
  CHECK(result.has_upper && result.upper == INT64_C(2147483644));

  ixs_ctx_destroy(ctx);
}

static void test_public_dynamic_modular_projection_difference(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "dynamic_modular_projection_x");
  ixs_node *d = ixs_sym(ctx, "dynamic_modular_projection_d");
  ixs_node *value0 = test_unsigned_remainder_wrap(ctx, x, d, 0);
  ixs_node *value1 = test_unsigned_remainder_wrap(ctx, x, d, 1);
  ixs_node *value8 = test_unsigned_remainder_wrap(ctx, x, d, 8);
  ixs_node *direct0 = ixs_mod(ctx, x, d);
  ixs_node *direct1 = ixs_mod(ctx, ixs_add(ctx, x, ixs_int(ctx, 1)), d);
  ixs_facts *pair = ixs_facts_create(ctx);
  ixs_facts *vector = ixs_facts_create(ctx);
  ixs_facts *zero_denominator = ixs_facts_create(ctx);
  ixs_facts *negative_denominator = ixs_facts_create(ctx);
  ixs_range_result pair_x_range = {.has_lower = true,
                                   .has_upper = true,
                                   .lower_p = 0,
                                   .lower_q = 1,
                                   .upper_p = 1073741822,
                                   .upper_q = 1};
  ixs_range_result vector_x_range = {.has_lower = true,
                                     .has_upper = true,
                                     .lower_p = 0,
                                     .lower_q = 1,
                                     .upper_p = 1073741816,
                                     .upper_q = 1};
  ixs_range_result pair_d_range = {.has_lower = true,
                                   .has_upper = true,
                                   .lower_p = 4,
                                   .lower_q = 1,
                                   .upper_p = 1073741824,
                                   .upper_q = 1};
  ixs_range_result vector_d_range = {.has_lower = true,
                                     .has_upper = true,
                                     .lower_p = 16,
                                     .lower_q = 1,
                                     .upper_p = 1073741824,
                                     .upper_q = 1};
  ixs_range_result zero_range = {.has_lower = true,
                                 .has_upper = true,
                                 .lower_p = 0,
                                 .lower_q = 1,
                                 .upper_p = 0,
                                 .upper_q = 1};
  ixs_range_result negative_range = {.has_lower = true,
                                     .has_upper = true,
                                     .lower_p = -16,
                                     .lower_q = 1,
                                     .upper_p = -4,
                                     .upper_q = 1};
  int64_t delta;
  int64_t offset;

  CHECK(ixs_facts_assume_range(pair, x, &pair_x_range));
  CHECK(ixs_facts_assume_range(pair, d, &pair_d_range));
  CHECK(
      ixs_facts_assume_pred(pair, ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 2)),
                                          IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(
      ixs_facts_assume_pred(pair, ixs_cmp(ctx, ixs_mod(ctx, d, ixs_int(ctx, 4)),
                                          IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(test_ixs_constant_difference_facts(pair, value1, value0, &delta));
  CHECK(delta == 1);
  CHECK(test_ixs_equivalent_facts(pair, value1,
                                  ixs_add(ctx, value0, ixs_int(ctx, 1))) ==
        IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_range(vector, x, &vector_x_range));
  CHECK(ixs_facts_assume_range(vector, d, &vector_d_range));
  CHECK(ixs_facts_assume_pred(vector,
                              ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 8)),
                                      IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(vector,
                              ixs_cmp(ctx, ixs_mod(ctx, d, ixs_int(ctx, 16)),
                                      IXS_CMP_EQ, ixs_int(ctx, 0))));
  for (offset = 1; offset <= 7; offset++) {
    ixs_node *value = test_unsigned_remainder_wrap(ctx, x, d, offset);
    CHECK(test_ixs_constant_difference_facts(vector, value, value0, &delta));
    CHECK(delta == offset);
    CHECK(test_ixs_equivalent_facts(
              vector, value, ixs_add(ctx, value0, ixs_int(ctx, offset))) ==
          IXS_CHECK_TRUE);
    CHECK(test_ixs_constant_difference_facts(vector, value0, value, &delta));
    CHECK(delta == -offset);
    CHECK(test_ixs_equivalent_facts(
              vector, value0, ixs_sub(ctx, value, ixs_int(ctx, offset))) ==
          IXS_CHECK_TRUE);
  }
  CHECK(!test_ixs_constant_difference_facts(vector, value8, value0, &delta));
  CHECK(!test_ixs_constant_difference_facts(vector, value0, value8, &delta));

  CHECK(ixs_facts_assume_range(zero_denominator, x, &pair_x_range));
  CHECK(ixs_facts_assume_range(zero_denominator, d, &zero_range));
  CHECK(!test_ixs_constant_difference_facts(zero_denominator, direct1, direct0,
                                            &delta));

  CHECK(ixs_facts_assume_range(negative_denominator, x, &pair_x_range));
  CHECK(ixs_facts_assume_range(negative_denominator, d, &negative_range));
  CHECK(!test_ixs_constant_difference_facts(negative_denominator, direct1,
                                            direct0, &delta));

  ixs_ctx_destroy(ctx);
}

static void test_public_modular_projection_unbounded_query_stack(void) {
  enum { PAIRS = 48 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *lhs = ixs_int(ctx, 0);
  ixs_node *rhs = ixs_int(ctx, 0);
  ixs_node *predicates[PAIRS];
  ixs_facts *facts = ixs_facts_create(ctx);
  int64_t delta = 0;
  unsigned i;

  for (i = 0; i < PAIRS; i++) {
    char name[48];
    ixs_node *x;
    ixs_node *modulus = ixs_int(ctx, (int64_t)(16u + 4u * i));
    (void)snprintf(name, sizeof(name), "modular_stack_x_%u", i);
    x = ixs_sym(ctx, name);
    lhs = ixs_add(ctx, lhs,
                  ixs_mod(ctx, ixs_add(ctx, x, ixs_int(ctx, 1)), modulus));
    rhs = ixs_add(ctx, rhs, ixs_mod(ctx, x, modulus));
    predicates[i] = ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 4)), IXS_CMP_EQ,
                            ixs_int(ctx, 0));
  }
  CHECK(ixs_facts_assume_preds(facts, predicates, PAIRS));
  CHECK(test_ixs_constant_difference_facts(facts, lhs, rhs, &delta));
  CHECK(delta == PAIRS);
  CHECK(test_ixs_equivalent_facts(facts, lhs,
                                  ixs_add(ctx, rhs, ixs_int(ctx, PAIRS))) ==
        IXS_CHECK_TRUE);

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(!test_ixs_constant_difference_facts(facts, lhs, rhs, &delta));
  CHECK(delta == 0);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(test_ixs_constant_difference_facts(facts, lhs, rhs, &delta));
  CHECK(delta == PAIRS);

  ixs_ctx_destroy(ctx);
}

static void test_public_modular_projection_exact_residual(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "modular_projection_residual_x");
  ixs_node *y = ixs_sym(ctx, "modular_projection_residual_y");
  ixs_node *z = ixs_sym(ctx, "modular_projection_residual_z");
  ixs_node *wrapped0 = test_signed_wrap(ctx, x, 8, 16);
  ixs_node *wrapped1 =
      test_signed_wrap(ctx, ixs_add(ctx, x, ixs_int(ctx, 1)), 8, 16);
  ixs_node *lhs = ixs_add(ctx, wrapped1, y);
  ixs_node *rhs = ixs_add(ctx, wrapped0, z);
  ixs_facts *facts = ixs_facts_create(ctx);
  int64_t delta = 0;

  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 4)),
                                      IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, y, IXS_CMP_EQ, ixs_add(ctx, z, ixs_int(ctx, 3)))));
  CHECK(test_ixs_constant_difference_facts(facts, lhs, rhs, &delta));
  CHECK(delta == 4);

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(!test_ixs_constant_difference_facts(facts, lhs, rhs, &delta));
  CHECK(delta == 0);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(test_ixs_constant_difference_facts(facts, lhs, rhs, &delta));
  CHECK(delta == 4);

  ixs_ctx_destroy(ctx);
}

static void test_public_constant_difference_no_round_piecewise_fast_path(void) {
  enum { TERM_COUNT = 256 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_node *x = ixs_sym(ctx, "no_round_piecewise_x");
  ixs_node *y = ixs_sym(ctx, "no_round_piecewise_y");
  ixs_node *values[2] = {x, y};
  ixs_node *conditions[2] = {ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 0)),
                             ixs_true(ctx)};
  ixs_node *piecewise = ixs_pw(ctx, 2, values, conditions);
  ixs_node *lhs = piecewise;
  ixs_node *rhs = ixs_int(ctx, 0);
  int64_t delta;
  unsigned i;

  CHECK(piecewise->tag == IXS_PIECEWISE);
  CHECK(!ixs_node_contains_rounding(piecewise));
  for (i = 0; i < TERM_COUNT; i++) {
    char lhs_name[48];
    char rhs_name[48];
    snprintf(lhs_name, sizeof(lhs_name), "no_round_piecewise_lhs_%u", i);
    snprintf(rhs_name, sizeof(rhs_name), "no_round_piecewise_rhs_%u", i);
    lhs = ixs_add(ctx, lhs, ixs_sym(ctx, lhs_name));
    rhs = ixs_add(ctx, rhs, ixs_sym(ctx, rhs_name));
  }
  CHECK(!ixs_node_contains_rounding(lhs));
  CHECK(!test_ixs_constant_difference_facts(facts, lhs, rhs, &delta));

  values[0] = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 2)));
  piecewise = ixs_pw(ctx, 2, values, conditions);
  CHECK(ixs_node_contains_rounding(piecewise));
  values[0] = x;
  conditions[0] = ixs_cmp(ctx, values[0], IXS_CMP_LT,
                          ixs_floor(ctx, ixs_div(ctx, y, ixs_int(ctx, 2))));
  piecewise = ixs_pw(ctx, 2, values, conditions);
  CHECK(ixs_node_contains_rounding(piecewise));

  ixs_ctx_destroy(ctx);
}

static void test_public_exact_equality_direct(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "exact_direct_x");
  ixs_node *y = ixs_sym(ctx, "exact_direct_y");
  ixs_node *affine =
      ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), x), ixs_int(ctx, 3));
  ixs_node *mod_x = ixs_mod(ctx, x, ixs_int(ctx, 7));
  ixs_node *mod_y = ixs_mod(ctx, y, ixs_int(ctx, 5));
  ixs_facts *affine_range = ixs_facts_create(ctx);
  ixs_facts *direct = ixs_facts_create(ctx);
  ixs_facts *complementary = ixs_facts_create(ctx);
  ixs_facts *nonaffine = ixs_facts_create(ctx);
  ixs_range_result exact = {.has_lower = true,
                            .has_upper = true,
                            .lower_p = 11,
                            .lower_q = 1,
                            .upper_p = 11,
                            .upper_q = 1};
  int64_t delta = 0;

  CHECK(ixs_facts_assume_range(affine_range, affine, &exact));
  check_public_exact_integer_range(affine_range, affine, 11);
  check_public_exact_integer_range(affine_range,
                                   ixs_sub(ctx, affine, ixs_int(ctx, 11)), 0);
  CHECK(test_ixs_equivalent_facts(affine_range, affine, ixs_int(ctx, 11)) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_constant_difference_facts(affine_range, affine,
                                           ixs_int(ctx, 11), &delta));
  CHECK(delta == 0);

  CHECK(ixs_facts_assume_pred(
      direct, ixs_cmp(ctx, y, IXS_CMP_EQ, ixs_add(ctx, x, ixs_int(ctx, 4)))));
  check_public_exact_integer_range(
      direct, ixs_sub(ctx, y, ixs_add(ctx, x, ixs_int(ctx, 4))), 0);
  CHECK(test_ixs_equivalent_facts(
            direct, y, ixs_add(ctx, x, ixs_int(ctx, 4))) == IXS_CHECK_TRUE);
  CHECK(test_ixs_constant_difference_facts(direct, y, x, &delta));
  CHECK(delta == 4);

  CHECK(assume_unit_difference_upper(ctx, complementary, x, y, IXS_CMP_LE, 4));
  CHECK(assume_unit_difference_upper(ctx, complementary, y, x, IXS_CMP_LE, -4));
  check_public_exact_integer_range(complementary, ixs_sub(ctx, x, y), 4);
  CHECK(test_ixs_equivalent_facts(complementary, x,
                                  ixs_add(ctx, y, ixs_int(ctx, 4))) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_constant_difference_facts(complementary, x, y, &delta));
  CHECK(delta == 4);

  CHECK(ixs_facts_assume_pred(
      nonaffine,
      ixs_cmp(ctx, mod_x, IXS_CMP_EQ, ixs_add(ctx, mod_y, ixs_int(ctx, 4)))));
  check_public_exact_integer_range(nonaffine, ixs_sub(ctx, mod_x, mod_y), 4);
  CHECK(test_ixs_equivalent_facts(nonaffine, mod_x,
                                  ixs_add(ctx, mod_y, ixs_int(ctx, 4))) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_constant_difference_facts(nonaffine, mod_x, mod_y, &delta));
  CHECK(delta == 4);

  ixs_ctx_destroy(ctx);
}

static void test_public_exact_equality_transitive(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "exact_transitive_x");
  ixs_node *y = ixs_sym(ctx, "exact_transitive_y");
  ixs_node *z = ixs_sym(ctx, "exact_transitive_z");
  ixs_facts *forward = ixs_facts_create(ctx);
  ixs_facts *reverse = ixs_facts_create(ctx);
  ixs_facts *offset = ixs_facts_create(ctx);
  int64_t delta = 0;

  CHECK(ixs_facts_assume_pred(forward, ixs_cmp(ctx, x, IXS_CMP_EQ, y)));
  CHECK(ixs_facts_assume_pred(forward, ixs_cmp(ctx, y, IXS_CMP_EQ, z)));
  check_public_exact_integer_range(forward, ixs_sub(ctx, x, z), 0);
  CHECK(test_ixs_equivalent_facts(forward, x, z) == IXS_CHECK_TRUE);
  CHECK(test_ixs_constant_difference_facts(forward, x, z, &delta));
  CHECK(delta == 0);
  CHECK(test_ixs_equivalent_facts(
            forward, ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 9)),
            ixs_cmp(ctx, z, IXS_CMP_LT, ixs_int(ctx, 9))) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(reverse, ixs_cmp(ctx, y, IXS_CMP_EQ, z)));
  CHECK(ixs_facts_assume_pred(reverse, ixs_cmp(ctx, x, IXS_CMP_EQ, y)));
  check_public_exact_integer_range(reverse, ixs_sub(ctx, x, z), 0);
  CHECK(test_ixs_equivalent_facts(reverse, x, z) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(
      offset, ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_add(ctx, y, ixs_int(ctx, 3)))));
  CHECK(ixs_facts_assume_pred(
      offset, ixs_cmp(ctx, y, IXS_CMP_EQ, ixs_add(ctx, z, ixs_int(ctx, 4)))));
  check_public_exact_integer_range(offset, ixs_sub(ctx, x, z), 7);
  CHECK(test_ixs_equivalent_facts(
            offset, x, ixs_add(ctx, z, ixs_int(ctx, 7))) == IXS_CHECK_TRUE);
  CHECK(test_ixs_constant_difference_facts(offset, x, z, &delta));
  CHECK(delta == 7);
  CHECK(test_ixs_equivalent_facts(
            offset, ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 9)),
            ixs_cmp(ctx, z, IXS_CMP_LT, ixs_int(ctx, 2))) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_public_exact_equality_substitution_and_negatives(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "exact_substitution_x");
  ixs_node *y = ixs_sym(ctx, "exact_substitution_y");
  ixs_node *z = ixs_sym(ctx, "exact_substitution_z");
  ixs_facts *source = ixs_facts_create(ctx);
  ixs_facts *substituted = ixs_facts_create(ctx);
  ixs_facts *one_sided = ixs_facts_create(ctx);
  ixs_facts *scaled = ixs_facts_create(ctx);
  int64_t delta = 0;

  CHECK(ixs_facts_assume_pred(
      source, ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_add(ctx, y, ixs_int(ctx, 4)))));
  CHECK(ixs_facts_substitute(substituted, source, y, z));
  check_public_exact_integer_range(
      substituted, ixs_sub(ctx, x, ixs_add(ctx, z, ixs_int(ctx, 4))), 0);
  CHECK(test_ixs_equivalent_facts(substituted, x,
                                  ixs_add(ctx, z, ixs_int(ctx, 4))) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_constant_difference_facts(substituted, x, z, &delta));
  CHECK(delta == 4);

  CHECK(ixs_facts_assume_pred(
      one_sided,
      ixs_cmp(ctx, x, IXS_CMP_LE, ixs_add(ctx, y, ixs_int(ctx, 4)))));
  CHECK(!test_ixs_constant_difference_facts(one_sided, x, y, &delta));
  CHECK(test_ixs_equivalent_facts(one_sided, x,
                                  ixs_add(ctx, y, ixs_int(ctx, 4))) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(
      scaled, ixs_cmp(ctx, ixs_mul(ctx, ixs_int(ctx, 2), x), IXS_CMP_EQ, y)));
  CHECK(test_ixs_equivalent_facts(scaled, ixs_mul(ctx, ixs_int(ctx, 2), x),
                                  y) == IXS_CHECK_TRUE);
  CHECK(!test_ixs_constant_difference_facts(scaled, x, y, &delta));

  ixs_ctx_destroy(ctx);
}

static void test_public_exact_equality_ignores_inequality_fanout(void) {
  enum { FANOUT = 320 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "exact_fanout_x");
  ixs_node *y = ixs_sym(ctx, "exact_fanout_y");
  ixs_node *z = ixs_sym(ctx, "exact_fanout_z");
  ixs_node *neighbors[FANOUT];
  ixs_node *predicates[FANOUT];
  ixs_facts *facts = ixs_facts_create(ctx);
  int64_t delta = 1;
  size_t i;

  CHECK(ixs_facts_assume_pred(facts, ixs_cmp(ctx, x, IXS_CMP_EQ, y)));
  CHECK(ixs_facts_assume_pred(facts, ixs_cmp(ctx, y, IXS_CMP_EQ, z)));
  for (i = 0; i < FANOUT; i++) {
    char name[40];
    (void)snprintf(name, sizeof(name), "exact_fanout_neighbor_%lu",
                   (unsigned long)i);
    neighbors[i] = ixs_sym(ctx, name);
    predicates[i] =
        ixs_cmp(ctx, y, IXS_CMP_LE,
                ixs_add(ctx, neighbors[i], ixs_int(ctx, (int64_t)i + 1)));
  }
  CHECK(ixs_facts_assume_preds(facts, predicates, FANOUT));
  CHECK(facts->bounds.nexact_vars == 3);
  check_public_exact_integer_range(facts, ixs_sub(ctx, x, z), 0);
  CHECK(test_ixs_equivalent_facts(facts, x, z) == IXS_CHECK_TRUE);
  CHECK(test_ixs_constant_difference_facts(facts, x, z, &delta));
  CHECK(delta == 0);

  ixs_ctx_destroy(ctx);
}

static void test_public_exact_equality_long_chain(void) {
  enum { LINKS = 300, NODES = LINKS + 1 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *nodes[NODES];
  ixs_node *predicates[LINKS];
  ixs_facts *facts = ixs_facts_create(ctx);
  int64_t delta = 0;
  size_t i;

  for (i = 0; i < NODES; i++) {
    char name[40];
    (void)snprintf(name, sizeof(name), "exact_chain_%lu", (unsigned long)i);
    nodes[i] = ixs_sym(ctx, name);
  }
  for (i = 0; i < LINKS; i++)
    predicates[i] = ixs_cmp(ctx, nodes[i], IXS_CMP_EQ,
                            ixs_add(ctx, nodes[i + 1u], ixs_int(ctx, 1)));

  CHECK(ixs_facts_assume_preds(facts, predicates, LINKS));
  check_public_exact_integer_range(facts, ixs_sub(ctx, nodes[0], nodes[LINKS]),
                                   LINKS);
  CHECK(test_ixs_constant_difference_facts(facts, nodes[0], nodes[LINKS],
                                           &delta));
  CHECK(delta == LINKS);
  CHECK(test_ixs_equivalent_facts(
            facts, nodes[0], ixs_add(ctx, nodes[LINKS], ixs_int(ctx, LINKS))) ==
        IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_public_exact_equality_cycles_and_overflow(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "exact_cycle_x");
  ixs_node *y = ixs_sym(ctx, "exact_cycle_y");
  ixs_node *z = ixs_sym(ctx, "exact_cycle_z");
  ixs_node *w = ixs_sym(ctx, "exact_cycle_w");
  ixs_facts *inconsistent = ixs_facts_create(ctx);
  ixs_facts *overflow = ixs_facts_create(ctx);
  int64_t delta = 0;

  CHECK(ixs_facts_assume_pred(inconsistent, ixs_cmp(ctx, x, IXS_CMP_EQ, y)));
  CHECK(ixs_facts_assume_pred(inconsistent, ixs_cmp(ctx, y, IXS_CMP_EQ, z)));
  CHECK(ixs_facts_assume_pred(inconsistent, ixs_cmp(ctx, x, IXS_CMP_EQ, w)));
  CHECK(ixs_facts_assume_pred(
      inconsistent,
      ixs_cmp(ctx, w, IXS_CMP_EQ, ixs_add(ctx, z, ixs_int(ctx, 1)))));
  CHECK(inconsistent->bounds.contradiction);
  CHECK(!test_ixs_constant_difference_facts(inconsistent, x, z, &delta));
  CHECK(test_ixs_equivalent_facts(inconsistent, x, z) == IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(
      overflow,
      ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_add(ctx, y, ixs_int(ctx, INT64_MAX)))));
  CHECK(ixs_facts_assume_pred(
      overflow, ixs_cmp(ctx, y, IXS_CMP_EQ, ixs_add(ctx, z, ixs_int(ctx, 1)))));
  CHECK(!overflow->bounds.contradiction);
  CHECK(!test_ixs_constant_difference_facts(overflow, x, z, &delta));
  CHECK(test_ixs_equivalent_facts(overflow, x, z) == IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_public_range_composite_predicate_fact(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *a = ixs_sym(ctx, "A");
  ixs_node *b = ixs_sym(ctx, "B");
  ixs_node *expr = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), a),
                           ixs_mul(ctx, ixs_int(ctx, 16), b));
  ixs_node *factored = ixs_mul(
      ctx, ixs_int(ctx, 2), ixs_add(ctx, a, ixs_mul(ctx, ixs_int(ctx, 8), b)));
  ixs_node *u = ixs_sym(ctx, "affine_u");
  ixs_node *w = ixs_sym(ctx, "affine_w");
  ixs_node *delta = ixs_add(ctx, ixs_int(ctx, 128),
                            ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 64), u), w));
  ixs_node *delta_lower = ixs_cmp(ctx, delta, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *delta_upper =
      ixs_cmp(ctx, ixs_add(ctx, ixs_int(ctx, -2147483647), delta), IXS_CMP_LE,
              ixs_int(ctx, 0));
  ixs_node *delta_facts = ixs_and(ctx, delta_lower, delta_upper);
  ixs_node *fits_u32 =
      ixs_cmp(ctx, delta, IXS_CMP_LE, ixs_int(ctx, INT64_C(4294967295)));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *lower_only = ixs_facts_create(ctx);
  ixs_node *assumes[2];
  ixs_range_result r;

  assumes[0] = ixs_cmp(ctx, expr, IXS_CMP_GE, ixs_int(ctx, 0));
  assumes[1] = ixs_cmp(ctx, ixs_add(ctx, ixs_int(ctx, -2147483630), expr),
                       IXS_CMP_LE, ixs_int(ctx, 0));

  CHECK(ixs_range(ctx, expr, assumes, 2, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 2147483630 && r.upper_q == 1);

  CHECK(ixs_range(ctx, factored, assumes, 2, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 2147483630 && r.upper_q == 1);

  CHECK(ixs_facts_assume_pred(facts, delta_facts));
  CHECK(test_ixs_range_facts(facts, delta, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 2147483647 && r.upper_q == 1);
  CHECK(test_ixs_check_facts(facts, fits_u32) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(lower_only, delta_lower));
  CHECK(test_ixs_range_facts(lower_only, delta, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(!r.has_upper);
  CHECK(test_ixs_check_facts(lower_only, fits_u32) == IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_batch_preserves_affine_range(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "batch_affine_x");
  ixs_node *y = ixs_sym(ctx, "batch_affine_y");
  ixs_node *values[2] = {x, ixs_int(ctx, 1)};
  ixs_node *conditions[2] = {ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 1)),
                             ixs_true(ctx)};
  ixs_node *piecewise = ixs_pw(ctx, 2, values, conditions);
  ixs_node *e = ixs_add(ctx, y, piecewise);
  ixs_node *twice_e = ixs_mul(ctx, ixs_int(ctx, 2), e);
  ixs_node *r = ixs_add(ctx, ixs_int(ctx, 128), twice_e);
  ixs_node *predicates[8] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, e, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, e, IXS_CMP_LE, ixs_int(ctx, 131064)),
      ixs_cmp(ctx, y, IXS_CMP_GE, ixs_int(ctx, -1)),
      ixs_cmp(ctx, ixs_add(ctx, ixs_int(ctx, 768), e), IXS_CMP_GE,
              ixs_int(ctx, 0)),
      ixs_cmp(ctx, ixs_add(ctx, ixs_int(ctx, -74232), e), IXS_CMP_LE,
              ixs_int(ctx, 0)),
      ixs_cmp(ctx, ixs_add(ctx, ixs_int(ctx, 1536), twice_e), IXS_CMP_GE,
              ixs_int(ctx, 0)),
      ixs_cmp(ctx, ixs_add(ctx, ixs_int(ctx, -148464), twice_e), IXS_CMP_LE,
              ixs_int(ctx, 0))};
  ixs_node *reversed[8];
  ixs_facts *forward = ixs_facts_create(ctx);
  ixs_facts *backward = ixs_facts_create(ctx);
  ixs_range_result range;
  size_t i;

  for (i = 0; i < 8; i++)
    reversed[i] = predicates[7 - i];

  CHECK(r->tag == IXS_ADD);
  CHECK(ixs_facts_assume_preds(forward, predicates, 8));
  CHECK(ixs_facts_assume_preds(backward, reversed, 8));
  CHECK(test_ixs_range_facts(forward, e, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 74232 && range.upper_q == 1);
  CHECK(test_ixs_range_facts(backward, e, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 74232 && range.upper_q == 1);
  CHECK(test_ixs_range_facts(forward, r, &range));
  CHECK(range.has_lower && range.lower_p == 128 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 148592 && range.upper_q == 1);
  CHECK(test_ixs_range_facts(backward, r, &range));
  CHECK(range.has_lower && range.lower_p == 128 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 148592 && range.upper_q == 1);

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_batch_a4w4_order_independent(void) {
  static const char target_text[] =
      "raw0*floor(1/64*wi) + 64*raw0*Mod(floor(1/32*wi), 2) + "
      "32*raw0*Mod(floor(1/16*wi), 2) + "
      "16*raw0*Mod(floor(1/8*wi), 2) + 16*Mod(wi, 2) + "
      "64*Mod(floor(1/4*wi), 2) + 32*Mod(floor(1/2*wi), 2)";
  static const char original_one_text[] =
      "raw0*xor(64*Mod(floor(1/32*wi), 2), "
      "32*Mod(floor(1/16*wi), 2), 16*Mod(floor(1/8*wi), 2), "
      "2*Mod(floor(1/128*wi), 2), 4*Mod(floor(1/256*wi), 2), "
      "8*Mod(floor(1/512*wi), 2), 128*Mod(floor(1/1024*wi), 2), "
      "Mod(floor(1/64*wi), 2)) + 16*Mod(wi, 2) + "
      "64*Mod(floor(1/4*wi), 2) + 32*Mod(floor(1/2*wi), 2)";
  static const char original_two_text[] =
      "raw0*xor(2*Mod(floor(1/128*wi), 2), "
      "4*Mod(floor(1/256*wi), 2), 8*Mod(floor(1/512*wi), 2), "
      "16*Mod(floor(1/8*wi), 2), 32*Mod(floor(1/16*wi), 2), "
      "64*Mod(floor(1/32*wi), 2), 128*Mod(floor(1/1024*wi), 2), "
      "Mod(floor(1/64*wi), 2)) + "
      "xor(16*Mod(wi, 2), 32*Mod(floor(1/2*wi), 2), "
      "64*Mod(floor(1/4*wi), 2))";
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *target = ixs_parse_expr(ctx, target_text, sizeof(target_text) - 1u);
  ixs_node *original_one =
      ixs_parse_expr(ctx, original_one_text, sizeof(original_one_text) - 1u);
  ixs_node *original_two =
      ixs_parse_expr(ctx, original_two_text, sizeof(original_two_text) - 1u);
  ixs_node *raw0 = ixs_sym(ctx, "raw0");
  ixs_node *wi = ixs_sym(ctx, "wi");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *predicates[10];
  ixs_node *reversed[10];
  ixs_facts *forward = ixs_facts_create(ctx);
  ixs_facts *backward = ixs_facts_create(ctx);
  ixs_range_result range;
  size_t i;

  predicates[0] = ixs_cmp(ctx, original_one, IXS_CMP_GE, zero);
  predicates[1] =
      ixs_cmp(ctx, ixs_add(ctx, ixs_int(ctx, -2147483632), original_one),
              IXS_CMP_LE, zero);
  predicates[2] = ixs_cmp(ctx, ixs_add(ctx, ixs_int(ctx, 2147483648), raw0),
                          IXS_CMP_GE, zero);
  predicates[3] = ixs_cmp(ctx, ixs_add(ctx, ixs_int(ctx, -2147483647), raw0),
                          IXS_CMP_LE, zero);
  predicates[4] =
      ixs_cmp(ctx, ixs_mod(ctx, raw0, ixs_int(ctx, 16)), IXS_CMP_EQ, zero);
  predicates[5] = ixs_cmp(ctx, ixs_add(ctx, ixs_int(ctx, -2147483632), raw0),
                          IXS_CMP_LE, zero);
  predicates[6] = ixs_cmp(ctx, original_two, IXS_CMP_GE, zero);
  predicates[7] =
      ixs_cmp(ctx, ixs_add(ctx, ixs_int(ctx, -2147483632), original_two),
              IXS_CMP_LE, zero);
  predicates[8] = ixs_cmp(ctx, wi, IXS_CMP_GE, zero);
  predicates[9] =
      ixs_cmp(ctx, ixs_add(ctx, ixs_int(ctx, -255), wi), IXS_CMP_LE, zero);
  for (i = 0; i < 10; i++)
    reversed[i] = predicates[9 - i];

  CHECK(ixs_facts_assume_preds(forward, predicates, 10));
  CHECK(ixs_facts_assume_preds(backward, reversed, 10));
  CHECK(test_ixs_range_facts(forward, target, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 2147483632 && range.upper_q == 1);
  CHECK(test_ixs_range_facts(backward, target, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 2147483632 && range.upper_q == 1);

  ixs_ctx_destroy(ctx);
}

static void test_public_range_proportional_add_edges(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "proportional_x");
  ixs_node *y = ixs_sym(ctx, "proportional_y");
  ixs_node *positive = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), x),
                               ixs_mul(ctx, ixs_int(ctx, 3), y));
  ixs_node *positive_scaled =
      ixs_add(ctx, ixs_int(ctx, 128),
              ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 6), y),
                      ixs_mul(ctx, ixs_int(ctx, 4), x)));
  ixs_node *negative = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, -2), x),
                               ixs_mul(ctx, ixs_int(ctx, 3), y));
  ixs_node *negative_scaled =
      ixs_add(ctx, ixs_int(ctx, 5),
              ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, -9), y),
                      ixs_mul(ctx, ixs_int(ctx, 6), x)));
  ixs_node *rational = ixs_add(ctx, ixs_mul(ctx, ixs_rat(ctx, 1, 2), x),
                               ixs_mul(ctx, ixs_rat(ctx, 3, 4), y));
  ixs_node *rational_scaled =
      ixs_add(ctx, ixs_int(ctx, 1),
              ixs_add(ctx, x, ixs_mul(ctx, ixs_rat(ctx, 3, 2), y)));
  ixs_node *extreme = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, INT64_MIN), x),
                              ixs_mul(ctx, ixs_int(ctx, INT64_MIN), y));
  ixs_node *extreme_half =
      ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, INT64_MIN / 2), x),
              ixs_mul(ctx, ixs_int(ctx, INT64_MIN / 2), y));
  ixs_facts *positive_facts = ixs_facts_create(ctx);
  ixs_facts *negative_facts = ixs_facts_create(ctx);
  ixs_facts *rational_facts = ixs_facts_create(ctx);
  ixs_facts *extreme_facts = ixs_facts_create(ctx);
  ixs_range_result input;
  ixs_range_result range;

  input.has_lower = true;
  input.has_upper = true;
  input.lower_q = 1;
  input.upper_q = 1;

  CHECK(!test_ixs_range_facts(positive_facts, positive_scaled, &range));
  input.lower_p = 0;
  input.upper_p = 100;
  CHECK(ixs_facts_assume_range(positive_facts, positive, &input));
  CHECK(test_ixs_range_facts(positive_facts, positive_scaled, &range));
  CHECK(range.has_lower && range.lower_p == 128 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 328 && range.upper_q == 1);

  input.lower_p = -4;
  input.upper_p = 7;
  CHECK(ixs_facts_assume_range(negative_facts, negative, &input));
  CHECK(test_ixs_range_facts(negative_facts, negative_scaled, &range));
  CHECK(range.has_lower && range.lower_p == -16 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 17 && range.upper_q == 1);

  input.lower_p = -2;
  input.upper_p = 5;
  CHECK(ixs_facts_assume_range(rational_facts, rational, &input));
  CHECK(test_ixs_range_facts(rational_facts, rational_scaled, &range));
  CHECK(range.has_lower && range.lower_p == -3 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 11 && range.upper_q == 1);

  input.lower_p = 0;
  input.upper_p = 10;
  CHECK(ixs_facts_assume_range(extreme_facts, extreme, &input));
  CHECK(!test_ixs_range_facts(extreme_facts, extreme_half, &range));
  CHECK(!test_ixs_range_facts(extreme_facts, extreme_half, &range));
  CHECK(test_ixs_range_facts(extreme_facts, extreme, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 10 && range.upper_q == 1);

  CHECK(ixs_facts_assume_pred(
      negative_facts, ixs_cmp(ctx, negative, IXS_CMP_LE, ixs_int(ctx, -5))));
  CHECK(!test_ixs_range_facts(negative_facts, negative_scaled, &range));

  ixs_ctx_destroy(ctx);
}

static void test_shifted_add_range_oom_and_contradiction(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *u = ixs_sym(ctx, "shifted_oom_u");
  ixs_node *w = ixs_sym(ctx, "shifted_oom_w");
  ixs_node *base = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 64), u), w);
  ixs_node *shifted = ixs_add(ctx, ixs_int(ctx, 128), base);
  ixs_facts *oom = ixs_facts_create(ctx);
  ixs_facts *control = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);
  ixs_range_result input;
  ixs_range_result result;

  input.has_lower = true;
  input.lower_p = -128;
  input.lower_q = 1;
  input.has_upper = true;
  input.upper_p = 2147483519;
  input.upper_q = 1;
  CHECK(ixs_facts_assume_range(oom, base, &input));
  CHECK(ixs_facts_assume_range(control, base, &input));

  ixs_node_transform_cache_clear(ctx);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  {
    ixs_range_query_result query_result = ixs_range_facts(oom, shifted);
    CHECK(query_result.status == IXS_FACT_QUERY_OOM);
    CHECK(!query_result.available && !query_result.range.has_lower &&
          !query_result.range.has_upper);
  }
  CHECK(!oom->bounds.oom);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);

  CHECK(test_ixs_range_facts(control, shifted, &result));
  CHECK(result.has_lower && result.lower_p == 0 && result.lower_q == 1);
  CHECK(result.has_upper && result.upper_p == 2147483647 &&
        result.upper_q == 1);

  CHECK(ixs_facts_assume_pred(
      contradictory, ixs_cmp(ctx, shifted, IXS_CMP_GE, ixs_int(ctx, 10))));
  CHECK(ixs_facts_assume_pred(
      contradictory, ixs_cmp(ctx, shifted, IXS_CMP_LE, ixs_int(ctx, 5))));
  CHECK(!test_ixs_range_facts(contradictory, shifted, &result));
  CHECK(!result.has_lower && !result.has_upper);

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_range_and_transfer(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *orig = ixs_sym(ctx, "orig");
  ixs_node *a = ixs_sym(ctx, "A");
  ixs_node *b = ixs_sym(ctx, "B");
  ixs_node *replacement = ixs_add(ctx, a, ixs_mul(ctx, ixs_int(ctx, 8), b));
  ixs_node *scaled = ixs_mul(ctx, ixs_int(ctx, 2), orig);
  ixs_node *subst_scaled = ixs_mul(ctx, ixs_int(ctx, 2), replacement);
  ixs_node *expanded_scaled = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), a),
                                      ixs_mul(ctx, ixs_int(ctx, 16), b));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *subst = ixs_facts_create(ctx);
  ixs_range_result input;
  ixs_range_result r;

  input.has_lower = true;
  input.lower_p = 0;
  input.lower_q = 1;
  input.has_upper = true;
  input.upper_p = 1073741815;
  input.upper_q = 1;

  CHECK(facts != NULL);
  CHECK(subst != NULL);
  CHECK(ixs_facts_assume_range(facts, orig, &input));
  CHECK(ixs_facts_derive_affine(facts, orig, 2, 0, scaled));

  CHECK(test_ixs_range_facts(facts, scaled, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 2147483630 && r.upper_q == 1);

  CHECK(ixs_facts_substitute(subst, facts, orig, replacement));
  CHECK(test_ixs_range_facts(subst, replacement, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 1073741815 && r.upper_q == 1);

  CHECK(test_ixs_range_facts(subst, subst_scaled, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 2147483630 && r.upper_q == 1);

  CHECK(test_ixs_range_facts(subst, expanded_scaled, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 2147483630 && r.upper_q == 1);

  ixs_ctx_destroy(ctx);
}

static ixs_node *raw_power(ixs_ctx *ctx, ixs_node *base, int32_t exp) {
  ixs_mulfactor factor;
  factor.base = base;
  factor.exp = exp;
  return ixs_node_mul(ctx, ctx->node_one, 1, &factor);
}

static ixs_node *raw_two_term_add(ixs_ctx *ctx, ixs_node *left_coeff,
                                  ixs_node *left, ixs_node *right_coeff,
                                  ixs_node *right) {
  ixs_addterm terms[2];
  terms[0].coeff = left_coeff;
  terms[0].term = left;
  terms[1].coeff = right_coeff;
  terms[1].term = right;
  if (ixs_node_cmp(ctx, terms[0].term, terms[1].term) > 0) {
    ixs_addterm swap = terms[0];
    terms[0] = terms[1];
    terms[1] = swap;
  }
  return ixs_node_add(ctx, ctx->node_zero, 2, terms);
}

static void test_public_range_powers(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "power_x");
  ixs_node *assumes[2];
  ixs_range_result r;

  assumes[0] = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  assumes[1] = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 15));
  CHECK(ixs_range(ctx, raw_power(ctx, x, 2), assumes, 2, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 225 && r.upper_q == 1);

  assumes[0] = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, -3));
  assumes[1] = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 5));
  CHECK(ixs_range(ctx, raw_power(ctx, x, 2), assumes, 2, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 25 && r.upper_q == 1);

  assumes[0] = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, -5));
  assumes[1] = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, -3));
  CHECK(ixs_range(ctx, raw_power(ctx, x, 3), assumes, 2, &r));
  CHECK(r.has_lower && r.lower_p == -125 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == -27 && r.upper_q == 1);

  assumes[0] = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 2));
  assumes[1] = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 4));
  CHECK(ixs_range(ctx, raw_power(ctx, x, -2), assumes, 2, &r));
  CHECK(r.has_lower && r.lower_p == 1 && r.lower_q == 16);
  CHECK(r.has_upper && r.upper_p == 1 && r.upper_q == 4);

  assumes[0] = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, -4));
  assumes[1] = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, -2));
  CHECK(ixs_range(ctx, raw_power(ctx, x, -3), assumes, 2, &r));
  CHECK(r.has_lower && r.lower_p == -1 && r.lower_q == 8);
  CHECK(r.has_upper && r.upper_p == -1 && r.upper_q == 64);

  assumes[0] = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, -1));
  assumes[1] = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 1));
  CHECK(!ixs_range(ctx, raw_power(ctx, x, -2), assumes, 2, &r));
  CHECK(ixs_range(ctx, raw_power(ctx, x, 65), assumes, 2, &r));
  CHECK(r.has_lower && r.lower_p == -1 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 1 && r.upper_q == 1);
  CHECK(!ixs_range(ctx, raw_power(ctx, x, INT32_MIN), assumes, 2, &r));

  assumes[0] = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, INT64_MAX - 1));
  assumes[1] = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, INT64_MAX));
  CHECK(ixs_range(ctx, raw_power(ctx, x, 2), assumes, 2, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(!r.has_upper);

  ixs_ctx_destroy(ctx);
}

static void test_public_range_xor(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "xor_x");
  ixs_node *y = ixs_sym(ctx, "xor_y");
  ixs_node *expr = ixs_xor(ctx, x, y);
  ixs_node *assumes[4];
  ixs_range_result r;

  assumes[0] = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  assumes[1] = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 15));
  assumes[2] = ixs_cmp(ctx, y, IXS_CMP_GE, ixs_int(ctx, 0));
  assumes[3] = ixs_cmp(ctx, y, IXS_CMP_LE, ixs_int(ctx, 15));
  CHECK(ixs_range(ctx, expr, assumes, 4, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 15 && r.upper_q == 1);

  assumes[0] = ixs_cmp(ctx, ixs_and(ctx, x, ixs_int(ctx, 15)), IXS_CMP_EQ,
                       ixs_int(ctx, 5));
  assumes[1] = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  assumes[2] = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 15));
  assumes[3] = ixs_cmp(ctx, y, IXS_CMP_EQ, ixs_int(ctx, 3));
  CHECK(ixs_range(ctx, expr, assumes, 4, &r));
  CHECK(r.has_lower && r.lower_p == 6 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 6 && r.upper_q == 1);

  assumes[0] = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  assumes[1] = ixs_cmp(ctx, y, IXS_CMP_GE, ixs_int(ctx, 0));
  assumes[2] = ixs_cmp(ctx, y, IXS_CMP_LE, ixs_int(ctx, 15));
  CHECK(ixs_range(ctx, expr, assumes, 3, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(!r.has_upper);

  assumes[0] = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, -1));
  assumes[1] = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 15));
  assumes[2] = ixs_cmp(ctx, y, IXS_CMP_GE, ixs_int(ctx, 0));
  assumes[3] = ixs_cmp(ctx, y, IXS_CMP_LE, ixs_int(ctx, 15));
  CHECK(!ixs_range(ctx, expr, assumes, 4, &r));

  expr = ixs_xor(ctx, ixs_div(ctx, x, ixs_int(ctx, 2)), y);
  assumes[0] = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  assumes[1] = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 15));
  CHECK(!ixs_range(ctx, expr, assumes, 4, &r));

  ixs_ctx_destroy(ctx);
}

static void test_public_range_associative_many(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "assoc_range_x");
  ixs_node *y = ixs_sym(ctx, "assoc_range_y");
  ixs_node *z = ixs_sym(ctx, "assoc_range_z");
  ixs_node *args[3] = {x, y, z};
  ixs_node *bounds[6];
  ixs_node *masked[3] = {x, y, ixs_int(ctx, 3)};
  ixs_node *scaled[3];
  ixs_node *overlap[3];
  ixs_node *congruent[3];
  ixs_node *mixed[3];
  ixs_node *extreme[2];
  ixs_node *expr;
  ixs_node *sum;
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_range_result r;

  bounds[0] = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 1));
  bounds[1] = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 3));
  bounds[2] = ixs_cmp(ctx, y, IXS_CMP_GE, ixs_int(ctx, 5));
  bounds[3] = ixs_cmp(ctx, y, IXS_CMP_LE, ixs_int(ctx, 7));
  bounds[4] = ixs_cmp(ctx, z, IXS_CMP_GE, ixs_int(ctx, -2));
  bounds[5] = ixs_cmp(ctx, z, IXS_CMP_LE, ixs_int(ctx, 2));
  CHECK(ixs_range(ctx, ixs_max_many(ctx, 3, args), bounds, 6, &r));
  CHECK(r.has_lower && r.lower_p == 5 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 7 && r.upper_q == 1);
  CHECK(ixs_range(ctx, ixs_min_many(ctx, 3, args), bounds, 6, &r));
  CHECK(r.has_lower && r.lower_p == -2 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 2 && r.upper_q == 1);
  CHECK(ixs_range(ctx, ixs_and_many(ctx, 3, masked), NULL, 0, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 3 && r.upper_q == 1);

  bounds[0] = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  bounds[1] = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 15));
  bounds[2] = ixs_cmp(ctx, y, IXS_CMP_GE, ixs_int(ctx, 0));
  bounds[3] = ixs_cmp(ctx, y, IXS_CMP_LE, ixs_int(ctx, 15));
  bounds[4] = ixs_cmp(ctx, z, IXS_CMP_GE, ixs_int(ctx, 0));
  bounds[5] = ixs_cmp(ctx, z, IXS_CMP_LE, ixs_int(ctx, 15));
  CHECK(ixs_range(ctx, ixs_xor_many(ctx, 3, args), bounds, 6, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 15 && r.upper_q == 1);

  scaled[0] = x;
  scaled[1] = ixs_mul(ctx, ixs_int(ctx, 16), y);
  scaled[2] = ixs_mul(ctx, ixs_int(ctx, 256), z);
  overlap[0] = x;
  overlap[1] = ixs_mul(ctx, ixs_int(ctx, 8), y);
  overlap[2] = scaled[2];
  sum = ixs_add(ctx, scaled[0], ixs_add(ctx, scaled[1], scaled[2]));
  CHECK(ixs_simplify(ctx, ixs_xor_many(ctx, 3, scaled), bounds, 6) == sum);
  CHECK(ixs_node_tag(ixs_simplify(ctx, ixs_xor_many(ctx, 3, overlap), bounds,
                                  6)) == IXS_XOR);

  congruent[0] =
      ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 4), x), ixs_int(ctx, 1));
  congruent[1] =
      ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 4), y), ixs_int(ctx, 1));
  congruent[2] =
      ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 4), z), ixs_int(ctx, 1));
  mixed[0] = congruent[0];
  mixed[1] = congruent[1];
  mixed[2] = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 4), z), ixs_int(ctx, 2));
  CHECK(test_ixs_check_congruent_facts(facts, ixs_max_many(ctx, 3, congruent),
                                       4, 1) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_congruent_facts(facts, ixs_min_many(ctx, 3, mixed), 4,
                                       1) == IXS_CHECK_UNKNOWN);

  extreme[0] = ixs_int(ctx, INT64_MAX);
  extreme[1] = x;
  CHECK(ixs_node_tag(ixs_simplify(ctx, ixs_max_many(ctx, 2, extreme), bounds,
                                  1)) == IXS_MAX);
  extreme[0] = ixs_int(ctx, INT64_MIN);
  bounds[0] = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 0));
  CHECK(ixs_node_tag(ixs_simplify(ctx, ixs_min_many(ctx, 2, extreme), bounds,
                                  1)) == IXS_MIN);

  args[0] = ixs_int(ctx, 8);
  args[1] = x;
  args[2] = y;
  bounds[0] = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 7));
  bounds[1] = ixs_cmp(ctx, y, IXS_CMP_LE, ixs_int(ctx, 6));
  expr = ixs_max_many(ctx, 3, args);
  CHECK(ixs_simplify(ctx, expr, bounds, 2) == ixs_int(ctx, 8));

  ixs_ctx_destroy(ctx);
}

static void test_public_range_piecewise(void) {
  enum { MANY_CASES = 1025 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "range_pw_x");
  ixs_node *y = ixs_sym(ctx, "range_pw_y");
  ixs_node *assumes[2];
  ixs_node *values[3];
  ixs_node *conds[3];
  ixs_node *expr;
  ixs_range_result r;
  ixs_pwcase raw_case;
  ixs_pwcase many_cases[MANY_CASES];
  unsigned i;

  assumes[0] = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  assumes[1] = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 31));
  values[0] = x;
  values[1] = ixs_sub(ctx, ixs_int(ctx, 31), x);
  conds[0] = ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 16));
  conds[1] = ixs_true(ctx);
  expr = ixs_pw(ctx, 2, values, conds);
  CHECK(ixs_range(ctx, expr, assumes, 2, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 15 && r.upper_q == 1);

  values[0] = ixs_div(ctx, ixs_int(ctx, 1), x);
  values[1] = x;
  conds[0] = ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 0));
  conds[1] = ixs_true(ctx);
  expr = ixs_pw(ctx, 2, values, conds);
  CHECK(ixs_range(ctx, expr, assumes, 2, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 31 && r.upper_q == 1);

  values[0] = x;
  values[1] = ixs_int(ctx, 1000);
  values[2] = ixs_sub(ctx, ixs_int(ctx, 31), x);
  conds[0] = ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 16));
  conds[1] = ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 8));
  conds[2] = ixs_true(ctx);
  expr = ixs_pw(ctx, 3, values, conds);
  CHECK(ixs_range(ctx, expr, assumes, 2, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 15 && r.upper_q == 1);

  values[0] = x;
  conds[0] = ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 16));
  expr = ixs_pw(ctx, 1, values, conds);
  CHECK(!ixs_range(ctx, expr, assumes, 2, &r));

  values[0] = y;
  values[1] = ixs_int(ctx, 0);
  conds[0] = ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 16));
  conds[1] = ixs_true(ctx);
  expr = ixs_pw(ctx, 2, values, conds);
  CHECK(!ixs_range(ctx, expr, assumes, 2, &r));

  expr = ixs_int(ctx, 1);
  raw_case.cond = ixs_true(ctx);
  for (i = 0; i <= 32u; i++) {
    raw_case.value = expr;
    expr = ixs_node_pw(ctx, 1, &raw_case);
  }
  CHECK(ixs_range(ctx, expr, NULL, 0, &r));
  CHECK(r.has_lower && r.lower_p == 1 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 1 && r.upper_q == 1);

  for (i = 0; i < MANY_CASES; i++) {
    many_cases[i].value = ixs_int(ctx, 1);
    many_cases[i].cond = ixs_true(ctx);
  }
  expr = ixs_node_pw(ctx, MANY_CASES, many_cases);
  CHECK(ixs_range(ctx, expr, NULL, 0, &r));
  CHECK(r.has_lower && r.lower_p == 1 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 1 && r.upper_q == 1);

  ixs_ctx_destroy(ctx);
}

static void test_failed_expand_is_not_expression_fact_alias(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *x65 = raw_power(ctx, x, 65);
  ixs_node *y65 = raw_power(ctx, y, 65);
  ixs_node *assume = ixs_cmp(ctx, x65, IXS_CMP_GE, ixs_int(ctx, 5));
  ixs_node *query = ixs_cmp(ctx, y65, IXS_CMP_GE, ixs_int(ctx, 5));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_range_result input;
  ixs_range_result r;

  input.has_lower = true;
  input.lower_p = 5;
  input.lower_q = 1;
  input.has_upper = false;
  input.upper_p = 0;
  input.upper_q = 1;

  CHECK(ixs_ctx_nerrors(ctx) == 0);
  CHECK(ixs_check(ctx, query, &assume, 1) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 0);
  CHECK(ixs_range(ctx, x65, &assume, 1, &r));
  CHECK(r.has_lower && r.lower_p == 5 && r.lower_q == 1);
  CHECK(!r.has_upper);
  CHECK(ixs_ctx_nerrors(ctx) == 0);
  CHECK(ixs_facts_assume_range(facts, x65, &input));
  CHECK(ixs_ctx_nerrors(ctx) == 0);
  CHECK(test_ixs_range_facts(facts, x65, &r));
  CHECK(ixs_ctx_nerrors(ctx) == 0);
  CHECK(!test_ixs_range_facts(facts, y65, &r));
  CHECK(ixs_ctx_nerrors(ctx) == 0);

  ixs_ctx_destroy(ctx);
}

static void test_bounds_canonical_alias_cache(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "canonical_x");
  ixs_node *s = ixs_sym(ctx, "canonical_s");
  ixs_node *x128 = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 128)));
  ixs_node *x256 = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 256)));
  ixs_node *digit = ixs_mod(ctx, x128, ixs_int(ctx, 2));
  ixs_node *a = raw_two_term_add(
      ctx, ixs_int(ctx, 1),
      ixs_mul(ctx, ixs_int(ctx, 64), ixs_mul(ctx, s, x256)), ixs_int(ctx, 1),
      ixs_mul(ctx, ixs_int(ctx, 32), ixs_mul(ctx, s, digit)));
  ixs_node *b = ixs_mul(ctx, ixs_int(ctx, 32), ixs_mul(ctx, s, x128));
  ixs_facts *left_facts = ixs_facts_create(ctx);
  ixs_facts *right_facts = ixs_facts_create(ctx);
  ixs_facts *empty = ixs_facts_create(ctx);
  ixs_range_result input;
  ixs_range_result range;

  input.has_lower = true;
  input.lower_p = 0;
  input.lower_q = 1;
  input.has_upper = true;
  input.upper_p = 2147483632;
  input.upper_q = 1;

  CHECK(a != b);
  CHECK(test_ixs_equivalent_facts(empty, a, b) == IXS_CHECK_TRUE);
  CHECK(ixs_facts_assume_range(left_facts, a, &input));
  CHECK(test_ixs_range_facts(left_facts, b, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 2147483632 && range.upper_q == 1);
  CHECK(ixs_facts_assume_range(right_facts, b, &input));
  CHECK(test_ixs_range_facts(right_facts, a, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 2147483632 && range.upper_q == 1);
  CHECK(ixs_node_transform_cache_lookup(
            ctx, a, IXS_NODE_TRANSFORM_BOUNDS_CANONICAL) == b);

  ixs_ctx_destroy(ctx);
}

static void test_bounds_canonical_alias_failure_semantics(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "canonical_fail_x");
  ixs_node *s = ixs_sym(ctx, "canonical_fail_s");
  ixs_node *lhs = ixs_node_cmp(ctx, x, s) < 0 ? x : s;
  ixs_node *rhs = lhs == x ? s : x;
  ixs_node *xor_args[2] = {lhs, rhs};
  ixs_node *uncached = ixs_node_assoc(ctx, IXS_XOR, 2, xor_args);
  ixs_node *too_large = raw_power(ctx, x, 65);
  ixs_node *expand_oom =
      ixs_mul(ctx, ixs_add(ctx, x, s), ixs_sym(ctx, "canonical_fail_z"));
  ixs_facts *failed = ixs_facts_create(ctx);
  ixs_facts *populated = ixs_facts_create(ctx);
  ixs_facts *oom = ixs_facts_create(ctx);
  ixs_facts *sentinel = ixs_facts_create(ctx);
  ixs_range_result input;
  ixs_range_result result;

  input.has_lower = true;
  input.lower_p = 0;
  input.lower_q = 1;
  input.has_upper = true;
  input.upper_p = 2147483632;
  input.upper_q = 1;

  ixs_arena_set_fail_after(&ctx->arena, 0);
  CHECK(ixs_facts_assume_range(failed, uncached, &input));
  CHECK(ixs_node_transform_cache_lookup(
            ctx, uncached, IXS_NODE_TRANSFORM_BOUNDS_CANONICAL) == NULL);
  CHECK(ixs_ctx_nerrors(ctx) == 0);
  ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);

  CHECK(ixs_facts_assume_range(populated, uncached, &input));
  CHECK(ixs_node_transform_cache_lookup(
            ctx, uncached, IXS_NODE_TRANSFORM_BOUNDS_CANONICAL) == uncached);

  ixs_arena_set_fail_after(&ctx->arena, 0);
  CHECK(!ixs_facts_assume_range(oom, expand_oom, &input));
  CHECK(ixs_node_transform_cache_lookup(
            ctx, expand_oom, IXS_NODE_TRANSFORM_BOUNDS_CANONICAL) == NULL);
  CHECK(ixs_ctx_nerrors(ctx) == 0);
  ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
  CHECK(!test_ixs_range_facts(oom, expand_oom, &result));
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  ixs_ctx_clear_errors(ctx);

  CHECK(ixs_facts_assume_range(sentinel, too_large, &input));
  CHECK(ixs_node_transform_cache_lookup(
            ctx, too_large, IXS_NODE_TRANSFORM_BOUNDS_CANONICAL) == too_large);
  CHECK(ixs_ctx_nerrors(ctx) == 0);
  CHECK(test_ixs_range_facts(sentinel, too_large, &result));
  CHECK(result.has_lower && result.lower_p == 0 && result.lower_q == 1);
  CHECK(result.has_upper && result.upper_p == 2147483632 &&
        result.upper_q == 1);
  CHECK(ixs_ctx_nerrors(ctx) == 0);

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_assume_conjunction(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *ge0 = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *le10 = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 10));
  ixs_node *both = ixs_and(ctx, ge0, le10);
  ixs_node *either = ixs_or(ctx, ge0, le10);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *unsupported = ixs_facts_create(ctx);
  ixs_range_result r;

  CHECK(ixs_facts_assume_pred(facts, both));
  CHECK(test_ixs_range_facts(facts, x, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 10 && r.upper_q == 1);
  CHECK(!ixs_facts_assume_pred(unsupported, either));

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_assume_batch(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "batch_x");
  ixs_node *y = ixs_sym(ctx, "batch_y");
  ixs_node *other_x = ixs_sym(other, "batch_x");
  ixs_node *predicates[3];
  ixs_node *invalid[2];
  ixs_node *wrong_context_predicates[2];
  ixs_node *oom_predicates[2];
  ixs_node *contradictory_predicates[2];
  ixs_facts *batch = ixs_facts_create(ctx);
  ixs_facts *sequential = ixs_facts_create(ctx);
  ixs_facts *noop = ixs_facts_create(ctx);
  ixs_facts *failed = ixs_facts_create(ctx);
  ixs_facts *null_array = ixs_facts_create(ctx);
  ixs_facts *wrong_context = ixs_facts_create(ctx);
  ixs_facts *oom = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);
  ixs_range_result batch_range;
  ixs_range_result sequential_range;
  size_t before_vars;
  size_t i;
  bool before_hi_inf;

  predicates[0] = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  predicates[1] = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 10));
  predicates[2] = ixs_cmp(ctx, y, IXS_CMP_EQ, ixs_int(ctx, 3));

  CHECK(ixs_facts_assume_preds(batch, predicates, 3));
  for (i = 0; i < 3; i++)
    CHECK(ixs_facts_assume_pred(sequential, predicates[i]));
  CHECK(test_ixs_range_facts(batch, x, &batch_range));
  CHECK(test_ixs_range_facts(sequential, x, &sequential_range));
  CHECK(batch_range.has_lower == sequential_range.has_lower);
  CHECK(batch_range.has_upper == sequential_range.has_upper);
  CHECK(batch_range.lower_p == sequential_range.lower_p);
  CHECK(batch_range.lower_q == sequential_range.lower_q);
  CHECK(batch_range.upper_p == sequential_range.upper_p);
  CHECK(batch_range.upper_q == sequential_range.upper_q);
  CHECK(test_ixs_check_facts(batch, predicates[2]) == IXS_CHECK_TRUE);

  contradictory_predicates[0] = ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, 0));
  contradictory_predicates[1] = ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, 1));
  CHECK(ixs_facts_assume_preds(contradictory, contradictory_predicates, 2));
  CHECK(test_ixs_check_facts(contradictory, ixs_true(ctx)) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(noop, predicates[0]));
  CHECK(ixs_facts_assume_preds(noop, NULL, 0));
  CHECK(test_ixs_check_facts(noop, predicates[0]) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(failed, predicates[0]));
  before_vars = failed->bounds.nvars;
  invalid[0] = ixs_cmp(ctx, y, IXS_CMP_GE, ixs_int(ctx, 5));
  invalid[1] = ixs_or(ctx, predicates[0], predicates[1]);
  CHECK(!ixs_facts_assume_preds(failed, invalid, 2));
  CHECK(failed->bounds.nvars == before_vars);
  CHECK(!failed->usable);

  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_facts_assume_preds(null_array, NULL, 1));
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "NULL array") != NULL);
  CHECK(!null_array->usable);

  CHECK(ixs_facts_assume_pred(wrong_context, predicates[0]));
  before_vars = wrong_context->bounds.nvars;
  before_hi_inf = wrong_context->bounds.vars[0].iv.hi_inf;
  wrong_context_predicates[0] = predicates[1];
  wrong_context_predicates[1] =
      ixs_cmp(other, other_x, IXS_CMP_GE, ixs_int(other, 0));
  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_facts_assume_preds(wrong_context, wrong_context_predicates, 2));
  CHECK(wrong_context->bounds.nvars == before_vars);
  CHECK(wrong_context->bounds.vars[0].iv.hi_inf == before_hi_inf);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  CHECK(!wrong_context->usable);

  CHECK(ixs_facts_assume_pred(oom, predicates[0]));
  before_vars = oom->bounds.nvars;
  before_hi_inf = oom->bounds.vars[0].iv.hi_inf;
  oom_predicates[0] = predicates[1];
  oom_predicates[1] = invalid[0];
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 1);
  CHECK(!ixs_facts_assume_preds(oom, oom_predicates, 2));
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(oom->bounds.nvars == before_vars);
  CHECK(oom->bounds.vars[0].iv.hi_inf == before_hi_inf);
  CHECK(!oom->usable);

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_public_facts_assume_batch_closure(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *base = ixs_sym(ctx, "batch_closure_base");
  ixs_node *lane = ixs_sym(ctx, "batch_closure_lane");
  ixs_node *divisor = ixs_sym(ctx, "batch_closure_divisor");
  ixs_node *scale = ixs_sym(ctx, "batch_closure_scale");
  ixs_node *remainder = ixs_mod(ctx, lane, ixs_int(ctx, 8));
  ixs_node *divisor_minus_eight = ixs_sub(ctx, divisor, ixs_int(ctx, 8));
  ixs_node *scale_minus_one = ixs_sub(ctx, scale, ixs_int(ctx, 1));
  ixs_node *base_range =
      ixs_and(ctx,
              ixs_cmp(ctx, ixs_add(ctx, ixs_int(ctx, 2147483648), base),
                      IXS_CMP_GE, ixs_int(ctx, 0)),
              ixs_cmp(ctx, ixs_sub(ctx, base, ixs_int(ctx, 2147483647)),
                      IXS_CMP_LE, ixs_int(ctx, 0)));
  ixs_node *lane_range =
      ixs_and(ctx, ixs_cmp(ctx, remainder, IXS_CMP_GE, ixs_int(ctx, 0)),
              ixs_cmp(ctx, ixs_sub(ctx, remainder, ixs_int(ctx, 31)),
                      IXS_CMP_LE, ixs_int(ctx, 0)));
  ixs_node *divisor_eight = ixs_and(
      ctx, ixs_cmp(ctx, divisor_minus_eight, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, divisor_minus_eight, IXS_CMP_LE, ixs_int(ctx, 0)));
  ixs_node *scale_positive =
      ixs_cmp(ctx, scale_minus_one, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *scale_range =
      ixs_and(ctx, scale_positive,
              ixs_cmp(ctx, ixs_sub(ctx, scale, ixs_int(ctx, 2147483647)),
                      IXS_CMP_LE, ixs_int(ctx, 0)));
  ixs_node *quotient = ixs_floor(ctx, ixs_div(ctx, remainder, divisor));
  ixs_node *projected_nonnegative =
      ixs_cmp(ctx, ixs_add(ctx, base, ixs_mul(ctx, scale, quotient)),
              IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *query = ixs_cmp(ctx, base, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *predicates[7] = {
      lane_range, divisor_eight, scale_positive,       scale_range,
      base_range, ixs_true(ctx), projected_nonnegative};
  ixs_node *insufficient[4] = {
      lane_range,
      ixs_cmp(ctx, divisor, IXS_CMP_GE, ixs_int(ctx, 1)),
      scale_positive,
      projected_nonnegative,
  };
  ixs_facts *closed = ixs_facts_create(ctx);
  ixs_facts *open = ixs_facts_create(ctx);

  CHECK(ixs_facts_assume_pred(closed, base_range));
  CHECK(ixs_facts_assume_preds(closed, predicates, 7));
  CHECK(test_ixs_check_facts(closed, query) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(open, base_range));
  CHECK(ixs_facts_assume_preds(open, insufficient, 4));
  CHECK(test_ixs_check_facts(open, query) == IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_assume_batch_saturates_until_stable(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "batch_replay_x");
  ixs_node *y = ixs_sym(ctx, "batch_replay_y");
  ixs_node *z = ixs_sym(ctx, "batch_replay_z");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *predicates[3] = {ixs_cmp(ctx, ixs_add(ctx, x, y), IXS_CMP_GE, zero),
                             ixs_cmp(ctx, ixs_add(ctx, y, z), IXS_CMP_EQ, zero),
                             ixs_cmp(ctx, z, IXS_CMP_EQ, zero)};
  ixs_facts *facts = ixs_facts_create(ctx);

  CHECK(ixs_facts_assume_preds(facts, predicates, 3));
  CHECK(test_ixs_check_facts(facts, ixs_cmp(ctx, x, IXS_CMP_GE, zero)) ==
        IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_assume_batch_has_no_round_limit(void) {
  enum { CHAIN_LINKS = 1024, PREDICATE_COUNT = CHAIN_LINKS + 1 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *symbols[PREDICATE_COUNT];
  ixs_node *predicates[PREDICATE_COUNT];
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_facts *facts = ixs_facts_create(ctx);
  char name[32];
  size_t i;

  for (i = 0; i < PREDICATE_COUNT; i++) {
    (void)snprintf(name, sizeof(name), "batch_chain_%lu", (unsigned long)i);
    symbols[i] = ixs_sym(ctx, name);
  }
  predicates[0] =
      ixs_cmp(ctx, ixs_add(ctx, symbols[0], symbols[1]), IXS_CMP_GE, zero);
  for (i = 1; i < CHAIN_LINKS; i++)
    predicates[i] = ixs_cmp(ctx, ixs_add(ctx, symbols[i], symbols[i + 1]),
                            IXS_CMP_EQ, zero);
  predicates[CHAIN_LINKS] =
      ixs_cmp(ctx, symbols[CHAIN_LINKS], IXS_CMP_EQ, zero);

  CHECK(ixs_facts_assume_preds(facts, predicates, PREDICATE_COUNT));
  CHECK(test_ixs_check_facts(facts, ixs_cmp(ctx, symbols[0], IXS_CMP_GE,
                                            zero)) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_assume_batch_mid_simplify_oom(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "batch_oom_x");
  ixs_node *lower = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *upper = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 8));
  ixs_node *values[2] = {ixs_sub(ctx, x, ixs_int(ctx, 10)),
                         ixs_add(ctx, x, ixs_int(ctx, 2))};
  ixs_node *conditions[2] = {ixs_cmp(ctx, x, IXS_CMP_GT, ixs_int(ctx, 3)),
                             ixs_true(ctx)};
  ixs_node *piecewise = ixs_pw(ctx, 2, values, conditions);
  ixs_node *second = ixs_cmp(ctx, piecewise, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *predicates[2] = {upper, second};
  ixs_facts *prefix = ixs_facts_create(ctx);
  ixs_facts *failed = ixs_facts_create(ctx);
  ixs_bounds before;
  ixs_var_bound before_var;
  size_t prefix_allocations;
  const size_t budget = 1024;

  CHECK(ixs_facts_assume_pred(prefix, lower));
  CHECK(ixs_facts_assume_pred(failed, lower));
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), budget);
  CHECK(ixs_facts_assume_pred(prefix, upper));
  prefix_allocations = budget - ixs_test_scratch(ctx)->fail_after;
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);

  /* Same prefix exhausts the budget inside the second simplifier. */
  before = failed->bounds;
  CHECK(before.nvars == 1);
  before_var = before.vars[0];
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), prefix_allocations);
  CHECK(!ixs_facts_assume_preds(failed, predicates, 2));
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(!failed->usable);
  CHECK(failed->bounds.vars == before.vars);
  CHECK(failed->bounds.nvars == before.nvars);
  CHECK(failed->bounds.cap == before.cap);
  CHECK(failed->bounds.var_index == before.var_index);
  CHECK(failed->bounds.var_index_cap == before.var_index_cap);
  CHECK(failed->bounds.exprs == before.exprs);
  CHECK(failed->bounds.nexprs == before.nexprs);
  CHECK(failed->bounds.expr_cap == before.expr_cap);
  CHECK(failed->bounds.expr_index == before.expr_index);
  CHECK(failed->bounds.expr_index_cap == before.expr_index_cap);
  CHECK(failed->bounds.difference_index == before.difference_index);
  CHECK(failed->bounds.difference_vars == before.difference_vars);
  CHECK(failed->bounds.ndifferences == before.ndifferences);
  CHECK(failed->bounds.ndifference_vars == before.ndifference_vars);
  CHECK(failed->bounds.difference_index_cap == before.difference_index_cap);
  CHECK(failed->bounds.difference_var_cap == before.difference_var_cap);
  CHECK(failed->bounds.difference_epoch == before.difference_epoch);
  CHECK(failed->bounds.exact_vars == before.exact_vars);
  CHECK(failed->bounds.exact_index == before.exact_index);
  CHECK(failed->bounds.nexact_vars == before.nexact_vars);
  CHECK(failed->bounds.exact_var_cap == before.exact_var_cap);
  CHECK(failed->bounds.exact_index_cap == before.exact_index_cap);
  CHECK(failed->bounds.nonzero == before.nonzero);
  CHECK(failed->bounds.nnonzero == before.nnonzero);
  CHECK(failed->bounds.nonzero_cap == before.nonzero_cap);
  CHECK(failed->bounds.cache == before.cache);
  CHECK(failed->bounds.cache_cap == before.cache_cap);
  CHECK(failed->bounds.contradiction == before.contradiction);
  CHECK(failed->bounds.vars[0].name == before_var.name);
  CHECK(failed->bounds.vars[0].iv.lo_p == before_var.iv.lo_p);
  CHECK(failed->bounds.vars[0].iv.lo_q == before_var.iv.lo_q);
  CHECK(failed->bounds.vars[0].iv.hi_p == before_var.iv.hi_p);
  CHECK(failed->bounds.vars[0].iv.hi_q == before_var.iv.hi_q);
  CHECK(failed->bounds.vars[0].iv.lo_inf == before_var.iv.lo_inf);
  CHECK(failed->bounds.vars[0].iv.hi_inf == before_var.iv.hi_inf);
  CHECK(failed->bounds.vars[0].iv.valid == before_var.iv.valid);
  CHECK(failed->bounds.vars[0].modulus == before_var.modulus);
  CHECK(failed->bounds.vars[0].remainder == before_var.remainder);
  CHECK(failed->bounds.vars[0].bits.known_zero == before_var.bits.known_zero);
  CHECK(failed->bounds.vars[0].bits.known_one == before_var.bits.known_one);
  CHECK(failed->bounds.vars[0].bits.pow2 == before_var.bits.pow2);

  ixs_ctx_destroy(ctx);
}

static void test_public_difference_constraint_oom_is_atomic(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "difference_oom_x");
  ixs_node *y = ixs_sym(ctx, "difference_oom_y");
  ixs_node *z = ixs_sym(ctx, "difference_oom_z");
  ixs_node *first =
      ixs_cmp(ctx, ixs_sub(ctx, x, y), IXS_CMP_LE, ixs_int(ctx, 0));
  ixs_node *second =
      ixs_cmp(ctx, ixs_sub(ctx, y, z), IXS_CMP_LE, ixs_int(ctx, 0));
  ixs_facts *warm = ixs_facts_create(ctx);
  ixs_facts *probe = ixs_facts_create(ctx);
  const size_t allowance = 1024u;
  size_t allocations;
  size_t budget;
  size_t failures = 0;

  CHECK(ixs_facts_assume_pred(warm, first));
  CHECK(ixs_facts_assume_pred(warm, second));
  CHECK(ixs_facts_assume_pred(probe, first));
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), allowance);
  CHECK(ixs_facts_assume_pred(probe, second));
  allocations = allowance - ixs_test_scratch(ctx)->fail_after;
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(allocations > 0 && allocations < allowance);

  for (budget = 0; budget < allocations; budget++) {
    ixs_facts *facts = ixs_facts_create(ctx);
    ixs_bounds before;
    ixs_difference_var before_difference_vars[2];
    bool ok;

    CHECK(ixs_facts_assume_pred(facts, first));
    CHECK(facts->bounds.nvars == 2);
    before = facts->bounds;
    before_difference_vars[0] = facts->bounds.difference_vars[0];
    before_difference_vars[1] = facts->bounds.difference_vars[1];

    ixs_arena_set_fail_after(ixs_test_scratch(ctx), budget);
    ok = ixs_facts_assume_pred(facts, second);
    ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
    if (ok) {
      CHECK(facts->bounds.ndifferences == before.ndifferences + 1u);
      CHECK(facts->bounds.ndifference_vars == before.ndifference_vars + 1u);
      continue;
    }
    failures++;
    CHECK(!facts->usable);
    CHECK(facts->bounds.vars == before.vars);
    CHECK(facts->bounds.nvars == before.nvars);
    CHECK(facts->bounds.cap == before.cap);
    CHECK(facts->bounds.var_index == before.var_index);
    CHECK(facts->bounds.var_index_cap == before.var_index_cap);
    CHECK(facts->bounds.exprs == before.exprs);
    CHECK(facts->bounds.nexprs == before.nexprs);
    CHECK(facts->bounds.expr_index == before.expr_index);
    CHECK(facts->bounds.expr_index_cap == before.expr_index_cap);
    CHECK(facts->bounds.difference_index == before.difference_index);
    CHECK(facts->bounds.difference_vars == before.difference_vars);
    CHECK(facts->bounds.ndifferences == before.ndifferences);
    CHECK(facts->bounds.ndifference_vars == before.ndifference_vars);
    CHECK(facts->bounds.difference_index_cap == before.difference_index_cap);
    CHECK(facts->bounds.difference_var_cap == before.difference_var_cap);
    CHECK(facts->bounds.difference_epoch == before.difference_epoch);
    CHECK(facts->bounds.exact_vars == before.exact_vars);
    CHECK(facts->bounds.exact_index == before.exact_index);
    CHECK(facts->bounds.nexact_vars == before.nexact_vars);
    CHECK(facts->bounds.exact_var_cap == before.exact_var_cap);
    CHECK(facts->bounds.exact_index_cap == before.exact_index_cap);
    CHECK(facts->bounds.contradiction == before.contradiction);
    CHECK(facts->bounds.difference_vars[0].incoming ==
          before_difference_vars[0].incoming);
    CHECK(facts->bounds.difference_vars[0].outgoing ==
          before_difference_vars[0].outgoing);
    CHECK(facts->bounds.difference_vars[0].potential ==
          before_difference_vars[0].potential);
    CHECK(facts->bounds.difference_vars[0].queue_epoch ==
          before_difference_vars[0].queue_epoch);
    CHECK(facts->bounds.difference_vars[0].hops ==
          before_difference_vars[0].hops);
    CHECK(facts->bounds.difference_vars[1].incoming ==
          before_difference_vars[1].incoming);
    CHECK(facts->bounds.difference_vars[1].outgoing ==
          before_difference_vars[1].outgoing);
    CHECK(facts->bounds.difference_vars[1].potential ==
          before_difference_vars[1].potential);
    CHECK(facts->bounds.difference_vars[1].queue_epoch ==
          before_difference_vars[1].queue_epoch);
    CHECK(facts->bounds.difference_vars[1].hops ==
          before_difference_vars[1].hops);
  }
  CHECK(failures > 0);

  ixs_ctx_destroy(ctx);
}

static void test_public_exact_equality_oom_is_atomic(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "exact_oom_x");
  ixs_node *y = ixs_sym(ctx, "exact_oom_y");
  ixs_node *first =
      ixs_cmp(ctx, ixs_sub(ctx, x, y), IXS_CMP_LE, ixs_int(ctx, 0));
  ixs_node *second =
      ixs_cmp(ctx, ixs_sub(ctx, y, x), IXS_CMP_LE, ixs_int(ctx, 0));
  ixs_facts *probe = ixs_facts_create(ctx);
  const size_t allowance = 1024u;
  size_t allocations;
  size_t budget;
  size_t failures = 0;

  CHECK(ixs_facts_assume_pred(probe, first));
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), allowance);
  CHECK(ixs_facts_assume_pred(probe, second));
  allocations = allowance - ixs_test_scratch(ctx)->fail_after;
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(allocations > 0 && allocations < allowance);
  CHECK(probe->bounds.nexact_vars == 2);
  CHECK(probe->bounds.nequalities == 1);

  for (budget = 0; budget < allocations; budget++) {
    ixs_facts *facts = ixs_facts_create(ctx);
    ixs_bounds before;
    bool ok;

    CHECK(ixs_facts_assume_pred(facts, first));
    CHECK(facts->bounds.nexact_vars == 0);
    before = facts->bounds;
    ixs_arena_set_fail_after(ixs_test_scratch(ctx), budget);
    ok = ixs_facts_assume_pred(facts, second);
    ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
    if (ok) {
      CHECK(facts->bounds.nexact_vars == 2);
      CHECK(facts->bounds.nequalities == 1);
      continue;
    }
    failures++;
    CHECK(!facts->usable);
    CHECK(facts->bounds.vars == before.vars);
    CHECK(facts->bounds.var_index == before.var_index);
    CHECK(facts->bounds.exprs == before.exprs);
    CHECK(facts->bounds.expr_index == before.expr_index);
    CHECK(facts->bounds.difference_index == before.difference_index);
    CHECK(facts->bounds.difference_vars == before.difference_vars);
    CHECK(facts->bounds.ndifferences == before.ndifferences);
    CHECK(facts->bounds.exact_vars == before.exact_vars);
    CHECK(facts->bounds.exact_index == before.exact_index);
    CHECK(facts->bounds.nexact_vars == before.nexact_vars);
    CHECK(facts->bounds.exact_var_cap == before.exact_var_cap);
    CHECK(facts->bounds.exact_index_cap == before.exact_index_cap);
    CHECK(facts->bounds.equality_endpoints == before.equality_endpoints);
    CHECK(facts->bounds.equality_endpoint_index ==
          before.equality_endpoint_index);
    CHECK(facts->bounds.nequality_endpoints == before.nequality_endpoints);
    CHECK(facts->bounds.equality_endpoint_cap == before.equality_endpoint_cap);
    CHECK(facts->bounds.equality_endpoint_index_cap ==
          before.equality_endpoint_index_cap);
    CHECK(facts->bounds.equality_index == before.equality_index);
    CHECK(facts->bounds.nequalities == before.nequalities);
    CHECK(facts->bounds.equality_index_cap == before.equality_index_cap);
    CHECK(facts->bounds.contradiction == before.contradiction);
  }
  CHECK(failures > 0);

  ixs_ctx_destroy(ctx);
}

static void test_public_difference_potential_overflow_is_atomic(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "difference_potential_x");
  ixs_node *y = ixs_sym(ctx, "difference_potential_y");
  ixs_node *z = ixs_sym(ctx, "difference_potential_z");
  ixs_node *x_minus_y = ixs_sub(ctx, x, y);
  ixs_node *z_minus_x = ixs_sub(ctx, z, x);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_range_result input = {0};
  ixs_bounds before;
  ixs_difference_var before_x;

  input.has_upper = true;
  input.upper_p = INT64_MIN;
  input.upper_q = 1;
  CHECK(ixs_facts_assume_range(facts, x_minus_y, &input));
  CHECK(facts->bounds.ndifferences == 1);
  before = facts->bounds;
  before_x = facts->bounds.difference_vars[0];

  input.upper_p = -1;
  CHECK(!ixs_facts_assume_range(facts, z_minus_x, &input));
  CHECK(!facts->usable);
  CHECK(facts->bounds.vars == before.vars);
  CHECK(facts->bounds.nvars == before.nvars);
  CHECK(facts->bounds.var_index == before.var_index);
  CHECK(facts->bounds.var_index_cap == before.var_index_cap);
  CHECK(facts->bounds.exprs == before.exprs);
  CHECK(facts->bounds.nexprs == before.nexprs);
  CHECK(facts->bounds.difference_index == before.difference_index);
  CHECK(facts->bounds.difference_vars == before.difference_vars);
  CHECK(facts->bounds.ndifferences == before.ndifferences);
  CHECK(facts->bounds.ndifference_vars == before.ndifference_vars);
  CHECK(facts->bounds.difference_index_cap == before.difference_index_cap);
  CHECK(facts->bounds.difference_var_cap == before.difference_var_cap);
  CHECK(facts->bounds.difference_epoch == before.difference_epoch);
  CHECK(facts->bounds.exact_vars == before.exact_vars);
  CHECK(facts->bounds.exact_index == before.exact_index);
  CHECK(facts->bounds.nexact_vars == before.nexact_vars);
  CHECK(facts->bounds.exact_var_cap == before.exact_var_cap);
  CHECK(facts->bounds.exact_index_cap == before.exact_index_cap);
  CHECK(facts->bounds.difference_vars[0].potential == before_x.potential);
  CHECK(facts->bounds.difference_vars[0].queue_epoch == before_x.queue_epoch);
  CHECK(facts->bounds.difference_vars[0].hops == before_x.hops);

  ixs_ctx_destroy(ctx);
}

static ixs_node *raw_logic_node(ixs_ctx *ctx, ixs_tag tag, uint32_t nargs,
                                ixs_node **args) {
  ixs_node *node = ixs_node_assoc(ctx, tag, nargs, args);
  CHECK(node != NULL);
  return node;
}

static void test_ctx_node_ownership_uses_intern_table(void) {
  enum { NNODES = 2500 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "owned_x");
  ixs_node *foreign = ixs_sym(other, "owned_x");
  ixs_node *middle = NULL;
  ixs_node *post_rehash = NULL;
  ixs_node *last = NULL;
  struct ixs_node_impl *raw =
      ixs_arena_alloc(&ctx->arena, sizeof(*raw), sizeof(void *));
  unsigned char *storage =
      ixs_arena_alloc(&ctx->arena, 2 * sizeof(*raw), sizeof(void *));
  struct ixs_node_impl *interior =
      storage ? (struct ixs_node_impl *)(void *)(storage + sizeof(*raw)) : NULL;
  size_t initial_cap = ctx->htab_cap;
  int i;

  CHECK(raw != NULL);
  if (raw)
    memcpy(raw, x, sizeof(*raw));
  CHECK(storage != NULL);
  if (interior)
    memcpy(interior, x, sizeof(*interior));
  for (i = 0; i < NNODES; i++) {
    char name[32];
    snprintf(name, sizeof(name), "owned_rehash_%d", i);
    last = ixs_sym(ctx, name);
    CHECK(last != NULL);
    if (i == NNODES / 2)
      middle = last;
    if (!post_rehash && ctx->htab_cap > initial_cap)
      post_rehash = last;
  }

  CHECK(ctx->htab_cap > initial_cap);
  CHECK(ixs_ctx_owns_node(ctx, x));
  CHECK(ixs_ctx_owns_node(ctx, middle));
  CHECK(ixs_ctx_owns_node(ctx, post_rehash));
  CHECK(ixs_ctx_owns_node(ctx, last));
  CHECK(!ixs_ctx_owns_node(ctx, foreign));
  if (raw)
    CHECK(!ixs_ctx_owns_node(ctx, raw));
  if (interior)
    CHECK(!ixs_ctx_owns_node(ctx, interior));

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_compound_assumption_legacy_fact_parity(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *d = ixs_sym(ctx, "d");
  ixs_node *range_pred =
      ixs_and(ctx, ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 31)));
  ixs_node *dm1 = ixs_sub(ctx, d, ixs_int(ctx, 1));
  ixs_node *pow2_pred = ixs_and(
      ctx, ixs_cmp(ctx, ixs_and(ctx, d, dm1), IXS_CMP_EQ, ixs_int(ctx, 0)),
      ixs_cmp(ctx, d, IXS_CMP_GT, ixs_int(ctx, 0)));
  ixs_node *all = ixs_and(ctx, range_pred, pow2_pred);
  ixs_node *query = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 31));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_range_result legacy_range;
  ixs_range_result fact_range;

  CHECK(ixs_range(ctx, x, &all, 1, &legacy_range));
  CHECK(legacy_range.has_lower && legacy_range.lower_p == 0 &&
        legacy_range.lower_q == 1);
  CHECK(legacy_range.has_upper && legacy_range.upper_p == 31 &&
        legacy_range.upper_q == 1);
  CHECK(ixs_check(ctx, query, &all, 1) == IXS_CHECK_TRUE);
  CHECK(ixs_get_pow2_fact(ctx, d, &all, 1) == IXS_POW2_POSITIVE);

  CHECK(ixs_facts_assume_pred(facts, all));
  CHECK(test_ixs_range_facts(facts, x, &fact_range));
  CHECK(fact_range.has_lower == legacy_range.has_lower);
  CHECK(fact_range.has_upper == legacy_range.has_upper);
  CHECK(fact_range.lower_p == legacy_range.lower_p);
  CHECK(fact_range.lower_q == legacy_range.lower_q);
  CHECK(fact_range.upper_p == legacy_range.upper_p);
  CHECK(fact_range.upper_q == legacy_range.upper_q);
  CHECK(test_ixs_check_facts(facts, query) == IXS_CHECK_TRUE);
  CHECK(test_ixs_get_pow2_fact_facts(facts, d) == IXS_POW2_POSITIVE);

  ixs_ctx_destroy(ctx);
}

static void test_fact_check_xor_cancellation_parity(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "xor_check_x");
  ixs_node *lo = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *hi = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 31));
  ixs_node *range = ixs_and(ctx, lo, hi);
  ixs_node *nested =
      ixs_xor(ctx, ixs_int(ctx, 1), ixs_xor(ctx, ixs_int(ctx, 1), x));
  ixs_node *equal = ixs_cmp(ctx, nested, IXS_CMP_EQ, x);
  ixs_node *different =
      ixs_xor(ctx, ixs_int(ctx, 1), ixs_xor(ctx, ixs_int(ctx, 2), x));
  ixs_node *not_equal = ixs_cmp(ctx, different, IXS_CMP_EQ, x);
  ixs_facts *facts = ixs_facts_create(ctx);

  CHECK(nested == x);
  CHECK(ixs_check(ctx, equal, &range, 1) == IXS_CHECK_TRUE);
  CHECK(ixs_facts_assume_pred(facts, range));
  CHECK(test_ixs_check_facts(facts, equal) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_predicate_facts(facts, equal) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, nested, x) == IXS_CHECK_TRUE);

  CHECK(different != x);
  CHECK(ixs_check(ctx, not_equal, &range, 1) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_facts(facts, not_equal) == IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_compound_assumption_rejection_is_atomic(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *ge0 = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *le10 = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 10));
  ixs_node *or_pred = ixs_or(ctx, ge0, le10);
  ixs_node *not_pred = ixs_not(ctx, ixs_and(ctx, ge0, le10));
  ixs_node *query = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *non_boolean = ixs_int(ctx, 2);
  ixs_node *legacy[2];
  ixs_node *raw_children[2];
  ixs_node *malformed_child[1];
  ixs_node *sentinel_tree;
  ixs_node *malformed_tree;
  ixs_node *atomic_tree;
  ixs_node *other_pred =
      ixs_cmp(other, ixs_sym(other, "x"), IXS_CMP_GE, ixs_int(other, 0));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_range_result r;

  legacy[0] = ge0;
  legacy[1] = or_pred;
  ixs_ctx_clear_errors(ctx);
  CHECK(ixs_check(ctx, query, legacy, 2) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "OR") != NULL);

  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_range(ctx, x, &not_pred, 1, &r));
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "NOT") != NULL);

  raw_children[0] = ge0;
  raw_children[1] = ctx->sentinel_error;
  sentinel_tree = raw_logic_node(ctx, IXS_AND, 2, raw_children);
  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_range(ctx, x, &sentinel_tree, 1, &r));
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "sentinel") != NULL);

  malformed_child[0] = ge0;
  malformed_tree = raw_logic_node(ctx, IXS_AND, 1, malformed_child);
  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_range(ctx, x, &malformed_tree, 1, &r));
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "malformed") != NULL);

  ixs_ctx_clear_errors(ctx);
  CHECK(ixs_check(ctx, query, NULL, 1) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "NULL array") != NULL);

  ixs_ctx_clear_errors(ctx);
  CHECK(ixs_check(ctx, query, &other_pred, 1) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);

  ixs_ctx_clear_errors(ctx);
  CHECK(ixs_check(ctx, query, &non_boolean, 1) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "boolean constant") != NULL);

  CHECK(ixs_facts_assume_pred(facts, ge0));
  raw_children[0] = ixs_cmp(ctx, y, IXS_CMP_GE, ixs_int(ctx, 5));
  raw_children[1] = or_pred;
  atomic_tree = raw_logic_node(ctx, IXS_AND, 2, raw_children);
  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_facts_assume_pred(facts, atomic_tree));
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "OR") != NULL);
  CHECK(!test_ixs_range_facts(facts, x, &r));
  CHECK(!test_ixs_range_facts(facts, y, &r));
  CHECK(test_ixs_check_facts(facts, query) == IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_compound_assumption_boolean_constants(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *value = ixs_int(ctx, 7);
  ixs_node *truth = ixs_true(ctx);
  ixs_node *falsehood = ixs_false(ctx);
  ixs_facts *true_facts = ixs_facts_create(ctx);
  ixs_facts *false_facts = ixs_facts_create(ctx);
  ixs_range_result r;

  CHECK(ixs_range(ctx, value, &truth, 1, &r));
  CHECK(r.has_lower && r.lower_p == 7 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 7 && r.upper_q == 1);
  CHECK(!ixs_range(ctx, value, &falsehood, 1, &r));

  CHECK(ixs_facts_assume_pred(true_facts, truth));
  CHECK(test_ixs_range_facts(true_facts, value, &r));
  CHECK(ixs_facts_assume_pred(false_facts, falsehood));
  CHECK(!test_ixs_range_facts(false_facts, value, &r));

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_assume_deep_conjunction(void) {
  enum { N = 300 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_node *pred = NULL;
  ixs_node *first = NULL;
  ixs_node *last = NULL;
  ixs_range_result r;
  int i;

  for (i = 0; i < N; i++) {
    char name[32];
    ixs_node *sym, *cmp;
    snprintf(name, sizeof(name), "d%d", i);
    sym = ixs_sym(ctx, name);
    cmp = ixs_cmp(ctx, sym, IXS_CMP_GE, ixs_int(ctx, i));
    if (i == 0)
      first = sym;
    if (i == N - 1)
      last = sym;
    pred = pred ? ixs_and(ctx, pred, cmp) : cmp;
  }

  CHECK(ixs_facts_assume_pred(facts, pred));
  CHECK(ixs_range(ctx, last, &pred, 1, &r));
  CHECK(r.has_lower && r.lower_p == N - 1 && r.lower_q == 1);
  CHECK(test_ixs_range_facts(facts, first, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(test_ixs_range_facts(facts, last, &r));
  CHECK(r.has_lower && r.lower_p == N - 1 && r.lower_q == 1);

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_substitute_preserves_symbol_facts(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *d = ixs_sym(ctx, "d");
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *seed = ixs_sym(ctx, "seed");
  ixs_node *pow2_expr = ixs_and(ctx, d, ixs_sub(ctx, d, ixs_int(ctx, 1)));
  ixs_node *pow2_assume = ixs_cmp(ctx, pow2_expr, IXS_CMP_EQ, ixs_int(ctx, 0));
  ixs_facts *src = ixs_facts_create(ctx);
  ixs_facts *dst = ixs_facts_create(ctx);
  ixs_range_result seed_range;

  seed_range.has_lower = true;
  seed_range.lower_p = 0;
  seed_range.lower_q = 1;
  seed_range.has_upper = true;
  seed_range.upper_p = 1;
  seed_range.upper_q = 1;

  CHECK(ixs_facts_assume_pred(src, pow2_assume));
  CHECK(test_ixs_get_pow2_fact_facts(src, d) == IXS_POW2_OR_ZERO);
  CHECK(ixs_facts_assume_range(dst, seed, &seed_range));

  CHECK(ixs_facts_substitute(dst, src, x, y));
  CHECK(test_ixs_get_pow2_fact_facts(dst, d) == IXS_POW2_OR_ZERO);

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_substitute_preserves_difference_graph(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "substitute_difference_x");
  ixs_node *y = ixs_sym(ctx, "substitute_difference_y");
  ixs_node *z = ixs_sym(ctx, "substitute_difference_z");
  ixs_facts *src = ixs_facts_create(ctx);
  ixs_facts *dst = ixs_facts_create(ctx);
  ixs_range_result range;

  CHECK(assume_unit_difference_upper(ctx, src, x, y, IXS_CMP_LE, 2));
  CHECK(ixs_facts_assume_pred(src,
                              ixs_cmp(ctx, y, IXS_CMP_LE, ixs_int(ctx, 10))));
  CHECK(ixs_facts_substitute(dst, src, x, z));

  CHECK(test_ixs_range_facts(dst, z, &range));
  CHECK(range.has_upper && range.upper_p == 12 && range.upper_q == 1);
  CHECK(test_ixs_check_facts(dst, ixs_cmp(ctx, ixs_sub(ctx, z, y), IXS_CMP_LE,
                                          ixs_int(ctx, 2))) == IXS_CHECK_TRUE);
  CHECK(test_ixs_range_facts(src, x, &range));
  CHECK(range.has_upper && range.upper_p == 12 && range.upper_q == 1);
  CHECK(!test_ixs_range_facts(src, z, &range));

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_substitute_multi_semantics(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "multi_x");
  ixs_node *y = ixs_sym(ctx, "multi_y");
  ixs_node *z = ixs_sym(ctx, "multi_z");
  ixs_node *a = ixs_sym(ctx, "multi_a");
  ixs_node *b = ixs_sym(ctx, "multi_b");
  ixs_node *d = ixs_sym(ctx, "multi_d");
  ixs_node *seed = ixs_sym(ctx, "multi_seed");
  ixs_node *pow2_expr = ixs_and(ctx, d, ixs_sub(ctx, d, ixs_int(ctx, 1)));
  ixs_node *pow2_pred = ixs_cmp(ctx, pow2_expr, IXS_CMP_EQ, ixs_int(ctx, 0));
  ixs_node *targets[2] = {x, y};
  ixs_node *replacements[2] = {y, z};
  ixs_node *duplicate_targets[2] = {x, x};
  ixs_node *duplicate_replacements[2] = {a, b};
  ixs_facts *src = ixs_facts_create(ctx);
  ixs_facts *dst = ixs_facts_create(ctx);
  ixs_facts *duplicates = ixs_facts_create(ctx);
  ixs_facts *empty_copy = ixs_facts_create(ctx);
  ixs_range_result input;
  ixs_range_result range;

  input.has_lower = true;
  input.has_upper = true;
  input.lower_q = 1;
  input.upper_q = 1;
  input.lower_p = 0;
  input.upper_p = 15;
  CHECK(ixs_facts_assume_range(src, x, &input));
  input.lower_p = 20;
  input.upper_p = 30;
  CHECK(ixs_facts_assume_range(src, y, &input));
  CHECK(ixs_facts_assume_pred(src, pow2_pred));
  input.lower_p = 100;
  input.upper_p = 200;
  CHECK(ixs_facts_assume_range(dst, seed, &input));

  CHECK(ixs_facts_substitute_multi(dst, src, 2, targets, replacements));
  CHECK(test_ixs_range_facts(dst, y, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 15 && range.upper_q == 1);
  CHECK(test_ixs_range_facts(dst, z, &range));
  CHECK(range.has_lower && range.lower_p == 20 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 30 && range.upper_q == 1);
  CHECK(test_ixs_range_facts(dst, seed, &range));
  CHECK(range.has_lower && range.lower_p == 100);
  CHECK(range.has_upper && range.upper_p == 200);
  CHECK(test_ixs_get_pow2_fact_facts(dst, d) == IXS_POW2_OR_ZERO);

  CHECK(ixs_facts_substitute_multi(duplicates, src, 2, duplicate_targets,
                                   duplicate_replacements));
  CHECK(test_ixs_range_facts(duplicates, a, &range));
  CHECK(range.has_lower && range.lower_p == 0);
  CHECK(range.has_upper && range.upper_p == 15);
  CHECK(!test_ixs_range_facts(duplicates, b, &range));

  CHECK(ixs_facts_substitute_multi(empty_copy, src, 0, NULL, NULL));
  CHECK(test_ixs_range_facts(empty_copy, x, &range));
  CHECK(range.has_lower && range.lower_p == 0);
  CHECK(range.has_upper && range.upper_p == 15);

  CHECK(ixs_facts_substitute_multi(src, src, 1, &x, &a));
  CHECK(test_ixs_range_facts(src, x, &range));
  CHECK(range.has_lower && range.lower_p == 0);
  CHECK(range.has_upper && range.upper_p == 15);
  CHECK(test_ixs_range_facts(src, a, &range));
  CHECK(range.has_lower && range.lower_p == 0);
  CHECK(range.has_upper && range.upper_p == 15);

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_substitute_inverse_facts(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *y = ixs_sym(ctx, "inverse_y");
  ixs_node *k = ixs_sym(ctx, "inverse_k");
  ixs_node *l = ixs_sym(ctx, "inverse_l");
  ixs_node *two_k = ixs_mul(ctx, ixs_int(ctx, 2), k);
  ixs_node *four_k_plus_two =
      ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 4), k), ixs_int(ctx, 2));
  ixs_node *nonlinear = ixs_mul(ctx, k, l);
  ixs_node *mod8 = ixs_cmp(ctx, ixs_mod(ctx, y, ixs_int(ctx, 8)), IXS_CMP_EQ,
                           ixs_int(ctx, 0));
  ixs_node *pow2_expr = ixs_and(ctx, y, ixs_sub(ctx, y, ixs_int(ctx, 1)));
  ixs_node *pow2_pred = ixs_cmp(ctx, pow2_expr, IXS_CMP_EQ, ixs_int(ctx, 0));
  ixs_facts *src = ixs_facts_create(ctx);
  ixs_facts *dst = ixs_facts_create(ctx);
  ixs_facts *offset_src = ixs_facts_create(ctx);
  ixs_facts *offset_dst = ixs_facts_create(ctx);
  ixs_facts *nonlinear_dst = ixs_facts_create(ctx);
  ixs_known_bits bits;

  CHECK(ixs_facts_assume_pred(src, mod8));
  CHECK(ixs_facts_assume_pred(src, pow2_pred));
  CHECK(
      ixs_facts_assume_pred(src, ixs_cmp(ctx, y, IXS_CMP_GT, ixs_int(ctx, 0))));
  CHECK(ixs_facts_substitute(dst, src, y, two_k));
  CHECK(test_ixs_check_congruent_facts(dst, k, 4, 0) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_congruent_facts(dst, k, 8, 0) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_get_known_bits_facts(dst, k, &bits));
  CHECK((bits.known_zero & 3u) == 3u);
  CHECK((bits.known_one & 3u) == 0);
  CHECK(test_ixs_get_pow2_fact_facts(dst, k) == IXS_POW2_POSITIVE);

  CHECK(ixs_facts_assume_pred(offset_src,
                              ixs_cmp(ctx, ixs_mod(ctx, y, ixs_int(ctx, 6)),
                                      IXS_CMP_EQ, ixs_int(ctx, 2))));
  CHECK(ixs_facts_substitute(offset_dst, offset_src, y, four_k_plus_two));
  CHECK(test_ixs_check_congruent_facts(offset_dst, k, 3, 0) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_substitute(nonlinear_dst, src, y, nonlinear));
  CHECK(test_ixs_check_congruent_facts(nonlinear_dst, k, 4, 0) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_get_pow2_fact_facts(nonlinear_dst, k) == IXS_POW2_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_substitute_contradiction_and_extrema(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "inverse_extreme_x");
  ixs_node *y = ixs_sym(ctx, "inverse_extreme_y");
  ixs_node *k = ixs_sym(ctx, "inverse_extreme_k");
  ixs_node *two_k = ixs_mul(ctx, ixs_int(ctx, 2), k);
  ixs_node *min_k = ixs_mul(ctx, ixs_int(ctx, INT64_MIN), k);
  ixs_node *min_offset = ixs_add(ctx, k, ixs_int(ctx, INT64_MIN));
  ixs_facts *incompatible = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);
  ixs_facts *extreme_src = ixs_facts_create(ctx);
  ixs_facts *extreme_dst = ixs_facts_create(ctx);
  ixs_facts *residue_src = ixs_facts_create(ctx);
  ixs_facts *residue_dst = ixs_facts_create(ctx);
  ixs_facts *merge_src = ixs_facts_create(ctx);
  ixs_facts *merge_dst = ixs_facts_create(ctx);
  ixs_facts *range_src = ixs_facts_create(ctx);
  ixs_facts *range_dst = ixs_facts_create(ctx);
  ixs_range_result input;
  ixs_range_result range;
  int64_t modulus;
  int64_t residue;

  CHECK(ixs_facts_assume_pred(incompatible,
                              ixs_cmp(ctx, ixs_mod(ctx, y, ixs_int(ctx, 2)),
                                      IXS_CMP_EQ, ixs_int(ctx, 1))));
  CHECK(ixs_facts_substitute(contradictory, incompatible, y, two_k));
  CHECK(test_ixs_check_congruent_facts(contradictory, k, 2, 0) ==
        IXS_CHECK_UNKNOWN);
  CHECK(!test_ixs_range_facts(contradictory, k, &range));

  CHECK(ixs_facts_assume_pred(
      extreme_src, ixs_cmp(ctx, ixs_mod(ctx, y, ixs_int(ctx, INT64_MAX)),
                           IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(ixs_facts_substitute(extreme_dst, extreme_src, y, min_k));
  CHECK(test_ixs_check_congruent_facts(extreme_dst, k, INT64_MAX, 0) ==
        IXS_CHECK_TRUE);
  CHECK(ixs_facts_assume_pred(
      residue_src, ixs_cmp(ctx, ixs_mod(ctx, y, ixs_int(ctx, INT64_MAX)),
                           IXS_CMP_EQ, ixs_int(ctx, INT64_MAX - 2))));
  CHECK(
      test_ixs_get_symbol_congruence_facts(residue_src, y, &modulus, &residue));
  CHECK(modulus == INT64_MAX);
  CHECK(residue == INT64_MAX - 2);
  CHECK(ixs_facts_substitute(residue_dst, residue_src, y, ixs_neg(ctx, k)));
  CHECK(
      test_ixs_get_symbol_congruence_facts(residue_dst, k, &modulus, &residue));
  CHECK(modulus == INT64_MAX);
  CHECK(residue == 2);
  CHECK(test_ixs_check_congruent_facts(residue_dst, k, INT64_MAX, 2) ==
        IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(
      merge_src, ixs_cmp(ctx, ixs_mod(ctx, y, ixs_int(ctx, 2147483629)),
                         IXS_CMP_EQ, ixs_int(ctx, 456))));
  CHECK(ixs_facts_assume_pred(
      merge_dst, ixs_cmp(ctx, ixs_mod(ctx, k, ixs_int(ctx, 2147483647)),
                         IXS_CMP_EQ, ixs_int(ctx, 123))));
  CHECK(ixs_facts_substitute(merge_dst, merge_src, y, k));
  CHECK(test_ixs_check_congruent_facts(merge_dst, k, 2147483629, 456) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_congruent_facts(merge_dst, k, 2147483647, 123) ==
        IXS_CHECK_TRUE);

  input.has_lower = true;
  input.has_upper = true;
  input.lower_p = 0;
  input.lower_q = 1;
  input.upper_p = 1;
  input.upper_q = 1;
  CHECK(ixs_facts_assume_range(range_src, x, &input));
  CHECK(ixs_facts_substitute(range_dst, range_src, x, min_offset));
  CHECK(test_ixs_range_facts(range_dst, min_offset, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 1 && range.upper_q == 1);

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_substitute_failures_are_atomic(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "substitute_failure_x");
  ixs_node *y = ixs_sym(ctx, "substitute_failure_y");
  ixs_node *other_y = ixs_sym(other, "substitute_failure_y");
  ixs_node *targets[1] = {x};
  ixs_node *replacements[1] = {y};
  ixs_node *wrong_replacements[1] = {other_y};
  ixs_node *sentinel_targets[1] = {ctx->sentinel_error};
  ixs_facts *src = ixs_facts_create(ctx);
  ixs_facts *other_src = ixs_facts_create(other);
  ixs_facts *wrong_node_dst = ixs_facts_create(ctx);
  ixs_facts *wrong_src_dst = ixs_facts_create(ctx);
  ixs_facts *sentinel_dst = ixs_facts_create(ctx);
  ixs_facts *null_array_dst = ixs_facts_create(ctx);
  ixs_facts *oom_dst = ixs_facts_create(ctx);
  ixs_range_result input;
  ixs_range_result range;

  input.has_lower = true;
  input.has_upper = true;
  input.lower_p = 1;
  input.lower_q = 1;
  input.upper_p = 9;
  input.upper_q = 1;
  CHECK(ixs_facts_assume_range(src, x, &input));
  CHECK(ixs_facts_assume_range(wrong_node_dst, y, &input));
  CHECK(ixs_facts_assume_range(wrong_src_dst, y, &input));
  CHECK(ixs_facts_assume_range(sentinel_dst, y, &input));
  CHECK(ixs_facts_assume_range(null_array_dst, y, &input));
  CHECK(ixs_facts_assume_range(oom_dst, y, &input));

  CHECK(!ixs_facts_substitute_multi(wrong_node_dst, src, 1, targets,
                                    wrong_replacements));
  CHECK(!test_ixs_range_facts(wrong_node_dst, y, &range));
  CHECK(!ixs_facts_substitute_multi(wrong_src_dst, other_src, 1, targets,
                                    replacements));
  CHECK(!test_ixs_range_facts(wrong_src_dst, y, &range));
  CHECK(!ixs_facts_substitute_multi(sentinel_dst, src, 1, sentinel_targets,
                                    replacements));
  CHECK(!test_ixs_range_facts(sentinel_dst, y, &range));
  CHECK(
      !ixs_facts_substitute_multi(null_array_dst, src, 1, NULL, replacements));
  CHECK(!test_ixs_range_facts(null_array_dst, y, &range));

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(!ixs_facts_substitute_multi(oom_dst, src, 1, targets, replacements));
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(!test_ixs_range_facts(oom_dst, y, &range));
  CHECK(test_ixs_range_facts(src, x, &range));
  CHECK(range.has_lower && range.lower_p == 1);
  CHECK(range.has_upper && range.upper_p == 9);

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

/* ------------------------------------------------------------------ */
/*  Public integrality and divisibility                               */
/* ------------------------------------------------------------------ */

static void test_public_structural_and_assumption_integrality(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *k = ixs_sym(ctx, "K");
  ixs_node *reciprocal = ixs_div(ctx, ixs_int(ctx, 1), x);
  ixs_node *scaled = ixs_div(ctx, k, ixs_int(ctx, 32));
  ixs_node *sum = ixs_add(ctx, x, scaled);
  ixs_node *half = ixs_rat(ctx, 1, 2);
  ixs_node *congruence = ixs_cmp(ctx, ixs_mod(ctx, k, ixs_int(ctx, 32)),
                                 IXS_CMP_EQ, ixs_int(ctx, 0));

  CHECK(ixs_node_is_integer_valued(x));
  CHECK(!ixs_node_is_integer_valued(reciprocal));
  CHECK(!ixs_node_is_integer_valued(scaled));
  CHECK(!ixs_node_is_integer_valued(sum));
  CHECK(!ixs_node_is_integer_valued(half));

  CHECK(ixs_check_integer_valued(ctx, reciprocal, NULL, 0) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_integer_valued(ctx, scaled, NULL, 0) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_integer_valued(ctx, sum, NULL, 0) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_integer_valued(ctx, half, NULL, 0) == IXS_CHECK_FALSE);
  CHECK(ixs_check_integer_valued(ctx, scaled, &congruence, 1) ==
        IXS_CHECK_TRUE);
  CHECK(ixs_check_integer_valued(ctx, sum, &congruence, 1) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_public_fact_integrality_associative_many(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "assoc_integral_x");
  ixs_node *y = ixs_sym(ctx, "assoc_integral_y");
  ixs_node *k = ixs_sym(ctx, "assoc_integral_k");
  ixs_node *scaled = ixs_div(ctx, k, ixs_int(ctx, 2));
  ixs_node *args[3] = {x, y, scaled};
  ixs_node *exprs[5];
  ixs_node *even = ixs_cmp(ctx, ixs_mod(ctx, k, ixs_int(ctx, 2)), IXS_CMP_EQ,
                           ixs_int(ctx, 0));
  ixs_facts *facts = ixs_facts_create(ctx);
  size_t i;

  exprs[0] = ixs_max_many(ctx, 3, args);
  exprs[1] = ixs_min_many(ctx, 3, args);
  exprs[2] = ixs_xor_many(ctx, 3, args);
  exprs[3] = ixs_and_many(ctx, 3, args);
  exprs[4] = ixs_or_many(ctx, 3, args);
  CHECK(ixs_facts_assume_pred(facts, even));
  for (i = 0; i < sizeof(exprs) / sizeof(exprs[0]); i++) {
    CHECK(ixs_node_assoc_nargs(exprs[i]) == 3);
    CHECK(ixs_node_assoc_arg(exprs[i], 2) == scaled);
    CHECK(!ixs_node_is_integer_valued(exprs[i]));
    CHECK(test_ixs_check_integer_valued_facts(facts, exprs[i]) ==
          IXS_CHECK_TRUE);
  }

  ixs_ctx_destroy(ctx);
}

static void test_public_fact_integrality_deep_mixed_dag(void) {
  enum { DEPTH = 8192 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *k = ixs_sym(ctx, "deep_integrality_k");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *two = ixs_int(ctx, 2);
  ixs_node *truth = ixs_true(ctx);
  ixs_node *expr = ixs_div(ctx, k, two);
  ixs_node *even = ixs_cmp(ctx, ixs_mod(ctx, k, two), IXS_CMP_EQ, zero);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_fact_check_result result;
  unsigned i;

  CHECK(ctx && k && zero && one && two && truth && expr && even && facts);
  if (!ctx || !k || !zero || !one || !two || !truth || !expr || !even ||
      !facts) {
    ixs_ctx_destroy(ctx);
    return;
  }
  CHECK(ixs_facts_assume_pred(facts, even));
  for (i = 0; i < DEPTH && expr; i++) {
    if (i % 3u == 0u) {
      ixs_addterm term = {expr, one};
      expr = ixs_node_add(ctx, zero, 1, &term);
    } else if (i % 3u == 1u) {
      ixs_node *args[2] = {expr, expr};
      expr = ixs_node_assoc(ctx, IXS_MAX, 2, args);
    } else {
      ixs_pwcase pwcase = {expr, truth};
      expr = ixs_node_pw(ctx, 1, &pwcase);
    }
  }
  CHECK(i == DEPTH && expr && !ixs_node_is_integer_valued(expr) &&
        ixs_node_contains_nested_piecewise(expr));
  if (i != DEPTH || !expr) {
    ixs_ctx_destroy(ctx);
    return;
  }

  /* The first growth beyond the inline exact-proof buffers is transport OOM,
   * and the same persistent fact set must remain retryable. */
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  result = ixs_check_integer_valued_facts(facts, expr);
  CHECK(result.status == IXS_FACT_QUERY_OOM &&
        result.check == IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  result = ixs_check_integer_valued_facts(facts, expr);
  CHECK(result.status == IXS_FACT_QUERY_COMPLETE &&
        result.check == IXS_CHECK_TRUE);
  result = ixs_check_divisible_facts(facts, expr, 1);
  CHECK(result.status == IXS_FACT_QUERY_COMPLETE &&
        result.check == IXS_CHECK_TRUE);

  /* An owned malformed node reaches the internal proof boundary.  The active
   * nested-Piecewise hold transports that producer violation as INVALID. */
  {
    ixs_node *arg[1] = {expr};
    ixs_node *malformed = ixs_node_assoc(ctx, IXS_MAX, 1, arg);
    result = ixs_check_integer_valued_facts(facts, malformed);
    CHECK(result.status == IXS_FACT_QUERY_INVALID &&
          result.check == IXS_CHECK_UNKNOWN);
  }

  ixs_ctx_destroy(ctx);
}

static void test_public_fact_integrality_piecewise(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *k = ixs_sym(ctx, "K");
  ixs_node *scaled = ixs_div(ctx, k, ixs_int(ctx, 32));
  ixs_node *values[2];
  ixs_node *conds[2];
  ixs_node *piecewise;
  ixs_node *unreachable_values[2];
  ixs_node *unreachable_conds[2];
  ixs_node *unreachable;
  ixs_node *congruence = ixs_cmp(ctx, ixs_mod(ctx, k, ixs_int(ctx, 32)),
                                 IXS_CMP_EQ, ixs_int(ctx, 0));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *range_facts = ixs_facts_create(ctx);

  values[0] = scaled;
  values[1] = x;
  conds[0] = ixs_cmp(ctx, x, IXS_CMP_GT, ixs_int(ctx, 0));
  conds[1] = ixs_true(ctx);
  piecewise = ixs_pw(ctx, 2, values, conds);
  CHECK(!ixs_node_is_integer_valued(piecewise));
  CHECK(test_ixs_check_integer_valued_facts(facts, piecewise) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_facts_assume_pred(facts, congruence));
  CHECK(test_ixs_check_integer_valued_facts(facts, scaled) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_integer_valued_facts(facts, piecewise) ==
        IXS_CHECK_TRUE);

  unreachable_values[0] = ixs_div(ctx, ixs_int(ctx, 1), x);
  unreachable_values[1] = x;
  unreachable_conds[0] = ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 0));
  unreachable_conds[1] = ixs_true(ctx);
  unreachable = ixs_pw(ctx, 2, unreachable_values, unreachable_conds);
  CHECK(ixs_facts_assume_pred(range_facts,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(test_ixs_check_integer_valued_facts(range_facts, unreachable) ==
        IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_public_fact_integrality_nested_mod(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "nested_mod_x");
  ixs_node *k = ixs_sym(ctx, "nested_mod_k");
  ixs_node *d = ixs_sym(ctx, "nested_mod_d");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *two = ixs_int(ctx, 2);
  ixs_node *eight = ixs_int(ctx, 8);
  ixs_node *inner = ixs_mod(ctx, k, ixs_int(ctx, 1024));
  ixs_node *scaled = ixs_div(ctx, inner, eight);
  ixs_node *nested = ixs_mod(ctx, scaled, two);
  ixs_node *wave_inner =
      ixs_mod(ctx, ixs_mul(ctx, eight, x), ixs_int(ctx, 1024));
  ixs_node *wave_scaled = ixs_div(ctx, wave_inner, eight);
  ixs_node *wave_nested = ixs_mod(ctx, wave_scaled, two);
  ixs_node *dynamic_divisor = ixs_div(ctx, d, two);
  ixs_node *dynamic = ixs_mod(ctx, scaled, dynamic_divisor);
  ixs_node *k_multiple = ixs_cmp(ctx, ixs_mod(ctx, k, eight), IXS_CMP_EQ, zero);
  ixs_node *d_even = ixs_cmp(ctx, ixs_mod(ctx, d, two), IXS_CMP_EQ, zero);
  ixs_node *dynamic_assumptions[2] = {k_multiple, d_even};
  ixs_node *k_multiple_four =
      ixs_cmp(ctx, ixs_mod(ctx, k, ixs_int(ctx, 4)), IXS_CMP_EQ, zero);
  ixs_facts *empty = ixs_facts_create(ctx);
  ixs_facts *weak = ixs_facts_create(ctx);
  ixs_facts *dividend_only = ixs_facts_create(ctx);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *range_only = ixs_facts_create(ctx);
  ixs_facts *closed = ixs_facts_create(ctx);
  ixs_range_result asserted_range;

  CHECK(!ixs_node_is_integer_valued(scaled));
  CHECK(!ixs_node_is_integer_valued(nested));
  CHECK(!ixs_node_is_integer_valued(wave_scaled));
  CHECK(!ixs_node_is_integer_valued(wave_nested));
  CHECK(!ixs_node_is_integer_valued(dynamic));
  CHECK(test_ixs_check_integer_valued_facts(empty, nested) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_integer_valued_facts(empty, wave_scaled) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_integer_valued_facts(empty, wave_nested) ==
        IXS_CHECK_TRUE);
  CHECK(ixs_facts_assume_pred(weak, k_multiple_four));
  CHECK(test_ixs_check_integer_valued_facts(weak, nested) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_facts_assume_pred(dividend_only, k_multiple));
  CHECK(test_ixs_check_integer_valued_facts(dividend_only, nested) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_integer_valued_facts(dividend_only, dynamic) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_integer_valued(ctx, dynamic, dynamic_assumptions, 2) ==
        IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(facts, k_multiple));
  CHECK(ixs_facts_assume_pred(facts, d_even));
  CHECK(test_ixs_check_integer_valued_facts(facts, scaled) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_integer_valued_facts(facts, nested) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_integer_valued_facts(facts, dynamic) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_defined_facts(facts, dynamic) == IXS_CHECK_UNKNOWN);

  asserted_range.has_lower = true;
  asserted_range.has_upper = true;
  asserted_range.lower_p = 0;
  asserted_range.lower_q = 1;
  asserted_range.upper_p = 7;
  asserted_range.upper_q = 1;
  CHECK(ixs_facts_assume_pred(range_only, k_multiple));
  CHECK(ixs_facts_assume_pred(range_only, d_even));
  CHECK(ixs_facts_assume_range(range_only, dynamic, &asserted_range));
  CHECK(test_ixs_check_integer_valued_facts(range_only, dynamic) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_defined_facts(range_only, dynamic) == IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(closed, k_multiple));
  CHECK(ixs_facts_assume_pred(closed, d_even));
  CHECK(ixs_facts_assume_pred(closed,
                              ixs_cmp(ctx, d, IXS_CMP_GE, ixs_int(ctx, 2))));
  CHECK(test_ixs_check_defined_facts(closed, dynamic) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_public_fact_integrality_nested_mod_cancellation(void) {
  static const char exact_text[] = "1/4*(32 + 1/8*Mod(item, 64) - "
                                   "1/8*Mod(Mod(item, 64), 32))";
  static const char base_text[] =
      "32 + 1/8*Mod(item, 64) - 1/8*Mod(Mod(item, 64), 32)";
  static const char noncancelling_text[] = "1/4*(32 + 1/8*Mod(item, 64) - "
                                           "1/8*Mod(Mod(item, 64), 24))";
  static const char negative_modulus_text[] = "1/4*(32 + 1/8*Mod(item, 64) - "
                                              "1/8*Mod(Mod(item, 64), -32))";
  static const char noninteger_dividend_text[] =
      "1/4*(32 + 1/8*Mod(item/2, 64) - "
      "1/8*Mod(Mod(item/2, 64), 32))";
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *exact = ixs_parse_expr(ctx, exact_text, strlen(exact_text));
  ixs_node *base = ixs_parse_expr(ctx, base_text, strlen(base_text));
  ixs_node *noncancelling =
      ixs_parse_expr(ctx, noncancelling_text, strlen(noncancelling_text));
  ixs_node *negative_modulus =
      ixs_parse_expr(ctx, negative_modulus_text, strlen(negative_modulus_text));
  ixs_node *noninteger_dividend = ixs_parse_expr(
      ctx, noninteger_dividend_text, strlen(noninteger_dividend_text));
  ixs_node *domain = ixs_parse_pred(ctx, "item >= 0 & item <= 255",
                                    strlen("item >= 0 & item <= 255"));
  ixs_facts *facts = ixs_facts_create(ctx);

  CHECK(exact && base && noncancelling && negative_modulus &&
        noninteger_dividend && domain && facts);
  CHECK(ixs_facts_assume_pred(facts, domain));
  CHECK(test_ixs_check_integer_valued_facts(facts, exact) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_defined_facts(facts, exact) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_divisible_facts(facts, base, 4) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_integer_valued_facts(facts, noncancelling) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_integer_valued_facts(facts, negative_modulus) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_integer_valued_facts(facts, noninteger_dividend) ==
        IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_public_fact_integrality_scaled_xor(void) {
  static const char expression_text[] =
      "1/2*xor(2*Mod(item, 2), 6*Mod(floor(item/2), 2), "
      "12*Mod(floor(item/4), 2), 24*Mod(floor(item/8), 2), "
      "48*Mod(floor(item/16), 2), 96*floor(item/32))";
  static const char domain_text[] = "item >= 0 & item <= 63";
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *expression =
      ixs_parse_expr(ctx, expression_text, strlen(expression_text));
  ixs_node *domain = ixs_parse_pred(ctx, domain_text, strlen(domain_text));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_node *simplified;

  CHECK(expression && domain && facts);
  CHECK(ixs_facts_assume_pred(facts, domain));
  CHECK(ixs_node_tag(expression) == IXS_MUL);
  CHECK(ixs_node_mul_nfactors(expression) == 1);
  CHECK(ixs_node_tag(ixs_node_mul_coeff(expression)) == IXS_RAT);
  CHECK(ixs_node_rat_num(ixs_node_mul_coeff(expression)) == 1);
  CHECK(ixs_node_rat_den(ixs_node_mul_coeff(expression)) == 2);
  CHECK(ixs_node_mul_factor_exp(expression, 0) == 1);
  CHECK(ixs_node_tag(ixs_node_mul_factor_base(expression, 0)) == IXS_XOR);
  CHECK(test_ixs_check_divisible_facts(
            facts, (ixs_node *)ixs_node_mul_factor_base(expression, 0), 2) ==
        IXS_CHECK_TRUE);
  CHECK(!ixs_node_is_integer_valued(expression));
  CHECK(test_ixs_check_integer_valued_facts(facts, expression) ==
        IXS_CHECK_TRUE);
  simplified = test_ixs_simplify_facts(facts, expression);
  CHECK(simplified != NULL);
  CHECK(ixs_node_tag(simplified) == IXS_XOR);
  CHECK(ixs_node_is_integer_valued(simplified));
  CHECK(test_ixs_equivalent_facts(facts, expression, simplified) ==
        IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_public_fact_divisibility(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *k = ixs_sym(ctx, "K");
  ixs_node *congruence = ixs_cmp(ctx, ixs_mod(ctx, k, ixs_int(ctx, 32)),
                                 IXS_CMP_EQ, ixs_int(ctx, 0));
  ixs_facts *facts = ixs_facts_create(ctx);

  CHECK(ixs_facts_assume_pred(facts, congruence));
  CHECK(test_ixs_check_divisible_facts(facts, k, 32) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_divisible_facts(facts, k, -32) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_divisible_facts(facts, k, 64) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_divisible_facts(facts, ixs_int(ctx, 64), 32) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_divisible_facts(facts, ixs_int(ctx, 65), 32) ==
        IXS_CHECK_FALSE);
  CHECK(test_ixs_check_divisible_facts(facts, ixs_rat(ctx, 1, 2), 1) ==
        IXS_CHECK_FALSE);
  CHECK(test_ixs_check_divisible_facts(facts, ixs_div(ctx, ixs_int(ctx, 1), k),
                                       1) == IXS_CHECK_UNKNOWN);

  CHECK(test_ixs_check_divisible_facts(facts, ixs_int(ctx, INT64_MIN),
                                       INT64_MIN) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_divisible_facts(facts, ixs_int(ctx, INT64_MAX),
                                       INT64_MIN) == IXS_CHECK_FALSE);
  CHECK(test_ixs_check_divisible_facts(facts, ixs_int(ctx, 0), INT64_MIN) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_divisible_facts(facts, ixs_int(ctx, INT64_MIN), -1) ==
        IXS_CHECK_TRUE);

  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_check_divisible_facts(facts, k, 0) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "modulus must be nonzero") != NULL);

  ixs_ctx_destroy(ctx);
}

static void test_public_fact_divisibility_rejects_reciprocal_factor(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *k = ixs_sym(ctx, "reciprocal_k");
  ixs_node *z = ixs_sym(ctx, "reciprocal_z");
  ixs_node *two = ixs_int(ctx, 2);
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *base_args[2] = {z, ixs_div(ctx, k, two)};
  ixs_node *base = ixs_max_many(ctx, 2, base_args);
  ixs_node *product = ixs_mul(ctx, two, base);
  ixs_node *reciprocal = ixs_div(ctx, two, base);
  ixs_node *product_query =
      ixs_cmp(ctx, ixs_mod(ctx, product, two), IXS_CMP_EQ, zero);
  ixs_node *reciprocal_query =
      ixs_cmp(ctx, ixs_mod(ctx, reciprocal, two), IXS_CMP_EQ, zero);
  ixs_facts *facts = ixs_facts_create(ctx);

  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, ixs_mod(ctx, k, two), IXS_CMP_EQ, zero)));
  CHECK(ixs_facts_assume_pred(facts, ixs_cmp(ctx, k, IXS_CMP_GE, two)));
  CHECK(ixs_facts_assume_pred(facts, ixs_cmp(ctx, z, IXS_CMP_GE, one)));
  CHECK(test_ixs_check_integer_valued_facts(facts, base) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(facts, product_query) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_integer_valued_facts(facts, reciprocal) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_defined_facts(facts, reciprocal) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(facts, reciprocal_query) == IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_public_known_bits_propagation(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *item = ixs_sym(ctx, "item");
  ixs_node *slot = ixs_sym(ctx, "slot");
  ixs_node *x = ixs_sym(ctx, "known_x");
  ixs_node *y = ixs_sym(ctx, "known_y");
  ixs_node *z = ixs_sym(ctx, "known_z");
  ixs_node *bit_args[3] = {x, y, z};
  ixs_node *wide = ixs_floor(
      ctx, ixs_div(ctx, item, ixs_int(ctx, INT64_C(4611686018427387904))));
  ixs_node *scaled16 = ixs_mul(ctx, ixs_int(ctx, 16), item);
  ixs_node *scaled8 = ixs_mul(ctx, ixs_int(ctx, 8), item);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *src = ixs_facts_create(ctx);
  ixs_facts *subst = ixs_facts_create(ctx);
  ixs_known_bits bits;
  ixs_known_bits a_bits;
  ixs_known_bits b_bits;

  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, slot, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, slot, IXS_CMP_LE, ixs_int(ctx, 15))));
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, ixs_and(ctx, x, ixs_int(ctx, 15)),
                                      IXS_CMP_EQ, ixs_int(ctx, 5))));
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, ixs_and(ctx, y, ixs_int(ctx, 15)),
                                      IXS_CMP_EQ, ixs_int(ctx, 10))));
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, ixs_and(ctx, z, ixs_int(ctx, 15)),
                                      IXS_CMP_EQ, ixs_int(ctx, 3))));
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 0))));

  CHECK(test_ixs_get_known_bits_facts(facts, ixs_int(ctx, 5), &bits));
  CHECK(bits.known_zero == ~(uint64_t)5);
  CHECK(bits.known_one == 5u);
  CHECK(bits.pow2 == IXS_POW2_UNKNOWN);

  CHECK(test_ixs_get_known_bits_facts(facts, slot, &bits));
  CHECK((bits.known_zero & ~(uint64_t)15) == ~(uint64_t)15);
  CHECK((bits.known_one & 15u) == 0);

  CHECK(test_ixs_get_known_bits_facts(facts, ixs_add(ctx, x, ixs_int(ctx, 3)),
                                      &bits));
  CHECK(((bits.known_zero | bits.known_one) & 15u) == 15u);
  CHECK((bits.known_one & 15u) == 8u);

  CHECK(test_ixs_get_known_bits_facts(facts, ixs_mul(ctx, ixs_int(ctx, 16), x),
                                      &bits));
  CHECK(((bits.known_zero | bits.known_one) & 255u) == 255u);
  CHECK((bits.known_one & 255u) == 80u);

  CHECK(test_ixs_get_known_bits_facts(facts, ixs_xor(ctx, x, y), &bits));
  CHECK(((bits.known_zero | bits.known_one) & 15u) == 15u);
  CHECK((bits.known_one & 15u) == 15u);

  CHECK(test_ixs_get_known_bits_facts(facts, ixs_xor_many(ctx, 3, bit_args),
                                      &bits));
  CHECK(((bits.known_zero | bits.known_one) & 15u) == 15u);
  CHECK((bits.known_one & 15u) == 12u);
  CHECK(test_ixs_get_known_bits_facts(facts, ixs_and_many(ctx, 3, bit_args),
                                      &bits));
  CHECK(((bits.known_zero | bits.known_one) & 15u) == 15u);
  CHECK((bits.known_one & 15u) == 0u);
  CHECK(test_ixs_get_known_bits_facts(facts, ixs_or_many(ctx, 3, bit_args),
                                      &bits));
  CHECK(((bits.known_zero | bits.known_one) & 15u) == 15u);
  CHECK((bits.known_one & 15u) == 15u);

  CHECK(test_ixs_get_known_bits_facts(facts, scaled16, &a_bits));
  CHECK(test_ixs_get_known_bits_facts(facts, slot, &b_bits));
  CHECK(((~a_bits.known_zero) & (~b_bits.known_zero)) == 0);
  CHECK(test_ixs_get_known_bits_facts(facts, scaled8, &a_bits));
  CHECK((((~a_bits.known_zero) & (~b_bits.known_zero)) & 8u) != 0);

  /* Dividing by 2^62 can expose source bits 62 and 63 only.  Source bits
   * beyond the low-64 abstraction stay unknown. */
  CHECK(test_ixs_get_known_bits_facts(facts, wide, &bits));
  CHECK(((bits.known_zero | bits.known_one) & ~(uint64_t)3) == 0);

  CHECK(
      ixs_facts_assume_pred(src, ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, 7))));
  CHECK(ixs_facts_substitute(subst, src, x, y));
  CHECK(test_ixs_get_known_bits_facts(subst, y, &bits));
  CHECK(bits.known_zero == ~(uint64_t)7);
  CHECK(bits.known_one == 7u);

  ixs_ctx_destroy(ctx);
}

static void test_public_known_bits_failures(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "known_invalid_x");
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);
  ixs_known_bits bits;
  ixs_known_bits_query_result query;

  CHECK(test_ixs_get_known_bits_facts(facts, x, &bits));
  CHECK(bits.known_zero == 0 && bits.known_one == 0);
  CHECK(test_ixs_get_known_bits_facts(facts, ixs_rat(ctx, 1, 2), &bits));
  CHECK(bits.known_zero == 0 && bits.known_one == 0);

  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 10))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 5))));
  bits.known_zero = ~(uint64_t)0;
  bits.known_one = ~(uint64_t)0;
  bits.pow2 = IXS_POW2_POSITIVE;
  CHECK(test_ixs_get_known_bits_facts(contradictory, x, &bits));
  CHECK(bits.known_zero == 0 && bits.known_one == 0);
  CHECK(bits.pow2 == IXS_POW2_UNKNOWN);

  ixs_ctx_clear_errors(ctx);
  query = ixs_get_known_bits_facts(facts, ixs_sym(other, "x"));
  CHECK(query.status == IXS_FACT_QUERY_INVALID);
  CHECK(query.bits.known_zero == 0 && query.bits.known_one == 0 &&
        query.bits.pow2 == IXS_POW2_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  query = ixs_get_known_bits_facts(facts, ctx->sentinel_error);
  CHECK(query.status == IXS_FACT_QUERY_INVALID);
  CHECK(query.bits.known_zero == 0 && query.bits.known_one == 0 &&
        query.bits.pow2 == IXS_POW2_UNKNOWN);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "sentinel") != NULL);
  ixs_ctx_clear_errors(ctx);
  query = ixs_get_known_bits_facts(facts, NULL);
  CHECK(query.status == IXS_FACT_QUERY_INVALID);
  CHECK(query.bits.known_zero == 0 && query.bits.known_one == 0 &&
        query.bits.pow2 == IXS_POW2_UNKNOWN);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "NULL expression") != NULL);

  query = ixs_get_known_bits_facts(NULL, x);
  CHECK(query.status == IXS_FACT_QUERY_INVALID);
  CHECK(query.bits.known_zero == 0 && query.bits.known_one == 0 &&
        query.bits.pow2 == IXS_POW2_UNKNOWN);

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_public_symbol_congruence(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *k = ixs_sym(ctx, "congruence_k");
  ixs_node *x = ixs_sym(ctx, "congruence_x");
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);
  int64_t modulus = -1;
  int64_t residue = -1;

  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, ixs_mod(ctx, k, ixs_int(ctx, 32)),
                                      IXS_CMP_EQ, ixs_int(ctx, 5))));
  CHECK(test_ixs_get_symbol_congruence_facts(facts, k, &modulus, &residue));
  CHECK(modulus == 32 && residue == 5);

  CHECK(!test_ixs_get_symbol_congruence_facts(facts, x, &modulus, &residue));
  CHECK(modulus == 0 && residue == 0);
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, ixs_mod(ctx, k, ixs_int(ctx, 8)),
                                      IXS_CMP_EQ, ixs_int(ctx, 1))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, ixs_mod(ctx, k, ixs_int(ctx, 8)),
                                      IXS_CMP_EQ, ixs_int(ctx, 2))));
  CHECK(!test_ixs_get_symbol_congruence_facts(contradictory, k, &modulus,
                                              &residue));

  ixs_ctx_clear_errors(ctx);
  CHECK(!test_ixs_get_symbol_congruence_facts(facts, ixs_add(ctx, k, x),
                                              &modulus, &residue));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "must be a symbol") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!test_ixs_get_symbol_congruence_facts(facts, ixs_sym(other, "k"),
                                              &modulus, &residue));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!test_ixs_get_symbol_congruence_facts(facts, ctx->sentinel_error,
                                              &modulus, &residue));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "sentinel") != NULL);
  {
    ixs_symbol_congruence_result query =
        ixs_get_symbol_congruence_facts(facts, k);
    CHECK(query.status == IXS_FACT_QUERY_COMPLETE && query.available);
    CHECK(query.modulus == 32 && query.residue == 5);
  }

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_public_congruence_query(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *k = ixs_sym(ctx, "query_k");
  ixs_node *n = ixs_sym(ctx, "query_n");
  ixs_node *x = ixs_sym(ctx, "query_x");
  ixs_node *int64_scaled =
      ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, INT64_MIN), x), ixs_int(ctx, 7));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *nonpow = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);

  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, ixs_mod(ctx, k, ixs_int(ctx, 32)),
                                      IXS_CMP_EQ, ixs_int(ctx, 5))));
  CHECK(test_ixs_check_congruent_facts(facts, k, 32, 5) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_congruent_facts(facts, k, 32, 6) == IXS_CHECK_FALSE);
  CHECK(test_ixs_check_congruent_facts(facts, k, -32, -27) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_congruent_facts(facts, k, 16, 5) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_congruent_facts(facts, k, 64, 5) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_congruent_facts(
            facts,
            ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 3), k), ixs_int(ctx, 2)), 32,
            17) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(nonpow,
                              ixs_cmp(ctx, ixs_mod(ctx, n, ixs_int(ctx, 15)),
                                      IXS_CMP_EQ, ixs_int(ctx, 4))));
  CHECK(test_ixs_check_congruent_facts(
            nonpow,
            ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 3), n), ixs_int(ctx, 2)), 15,
            14) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_congruent_facts(nonpow, ixs_mul(ctx, ixs_int(ctx, 5), n),
                                       15, 5) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_congruent_facts(
            nonpow,
            ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 6), x), ixs_int(ctx, 2)), 3,
            2) == IXS_CHECK_TRUE);

  CHECK(test_ixs_check_congruent_facts(facts, ixs_int(ctx, INT64_MIN),
                                       INT64_MIN, 0) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_congruent_facts(facts, ixs_int(ctx, INT64_MAX),
                                       INT64_MIN, -1) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_congruent_facts(facts, int64_scaled, INT64_MIN, 7) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_congruent_facts(facts, ixs_int(ctx, 65), 32, 1) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_congruent_facts(facts, ixs_int(ctx, 65), 32, 2) ==
        IXS_CHECK_FALSE);
  CHECK(test_ixs_check_congruent_facts(facts, ixs_rat(ctx, 1, 2), 3, 1) ==
        IXS_CHECK_FALSE);

  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 10))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 5))));
  CHECK(test_ixs_check_congruent_facts(contradictory, ixs_int(ctx, 1), 2, 1) ==
        IXS_CHECK_UNKNOWN);

  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_check_congruent_facts(facts, x, 0, 0) == IXS_CHECK_UNKNOWN);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "modulus must be nonzero") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_check_congruent_facts(facts, ixs_sym(other, "x"), 8, 0) ==
        IXS_CHECK_UNKNOWN);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_check_congruent_facts(facts, ctx->sentinel_error, 8, 0) ==
        IXS_CHECK_UNKNOWN);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "sentinel") != NULL);

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_public_predicate_tree_query(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "predicate_x");
  ixs_node *y = ixs_sym(ctx, "predicate_y");
  ixs_node *x_nonnegative = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *y_small = ixs_cmp(ctx, y, IXS_CMP_LT, ixs_int(ctx, 4));
  ixs_node *both = ixs_and(ctx, x_nonnegative, y_small);
  ixs_node *either = ixs_or(ctx, x_nonnegative, y_small);
  ixs_node *not_x = ixs_not(ctx, x);
  ixs_node *reciprocal = ixs_div(ctx, ixs_int(ctx, 1), x);
  ixs_node *partial_pred =
      ixs_cmp(ctx, reciprocal, IXS_CMP_GT, ixs_int(ctx, 0));
  ixs_node *guarded_false = ixs_and(ctx, ixs_false(ctx), partial_pred);
  ixs_node *guarded_true = ixs_or(ctx, ixs_true(ctx), partial_pred);
  ixs_facts *all_true = ixs_facts_create(ctx);
  ixs_facts *one_false = ixs_facts_create(ctx);
  ixs_facts *all_false = ixs_facts_create(ctx);
  ixs_facts *partial = ixs_facts_create(ctx);
  ixs_facts *no_domain = ixs_facts_create(ctx);
  ixs_facts *defined = ixs_facts_create(ctx);

  CHECK(ixs_facts_assume_pred(all_true, x_nonnegative));
  CHECK(ixs_facts_assume_pred(all_true, y_small));
  CHECK(ixs_facts_assume_pred(all_true,
                              ixs_cmp(ctx, y, IXS_CMP_NE, ixs_int(ctx, 2))));
  CHECK(test_ixs_check_predicate_facts(all_true, both) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_predicate_facts(
            all_true, ixs_cmp(ctx, y, IXS_CMP_NE, ixs_int(ctx, 2))) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_predicate_facts(all_true, either) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_predicate_facts(all_true, ixs_not(ctx, both)) ==
        IXS_CHECK_FALSE);

  CHECK(ixs_facts_assume_pred(one_false,
                              ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 0))));
  CHECK(test_ixs_check_predicate_facts(one_false, both) == IXS_CHECK_FALSE);
  CHECK(test_ixs_check_predicate_facts(one_false, either) == IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(all_false,
                              ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(all_false,
                              ixs_cmp(ctx, y, IXS_CMP_GE, ixs_int(ctx, 4))));
  CHECK(test_ixs_check_predicate_facts(all_false, either) == IXS_CHECK_FALSE);
  CHECK(test_ixs_check_predicate_facts(all_false, ixs_not(ctx, either)) ==
        IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(partial,
                              ixs_cmp(ctx, x, IXS_CMP_GT, ixs_int(ctx, 0))));
  CHECK(test_ixs_check_predicate_facts(partial, not_x) == IXS_CHECK_FALSE);
  CHECK(test_ixs_check_predicate_facts(partial, ixs_not(ctx, y)) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_predicate_facts(partial, both) == IXS_CHECK_UNKNOWN);

  CHECK(ixs_node_tag(guarded_false) == IXS_AND);
  CHECK(ixs_node_tag(guarded_true) == IXS_OR);
  CHECK(test_ixs_check_predicate_facts(no_domain, guarded_false) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_predicate_facts(no_domain, guarded_true) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_facts_assume_pred(defined,
                              ixs_cmp(ctx, x, IXS_CMP_NE, ixs_int(ctx, 0))));
  CHECK(test_ixs_check_predicate_facts(defined, guarded_false) ==
        IXS_CHECK_FALSE);
  CHECK(test_ixs_check_predicate_facts(defined, guarded_true) ==
        IXS_CHECK_TRUE);

  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_check_predicate_facts(
            partial, ixs_and(ctx, x, ixs_int(ctx, 7))) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "not a predicate tree") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_check_predicate_facts(partial, ixs_or(ctx, x, y)) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "not a predicate tree") != NULL);

  ixs_ctx_destroy(ctx);
}

static ixs_node *signed_i32_offset_cmp(ixs_ctx *ctx, ixs_node *value,
                                       ixs_node *limit, int64_t offset,
                                       ixs_cmp_op op) {
  ixs_node *biased =
      ixs_add(ctx, value, ixs_int(ctx, INT64_C(2147483648) + offset));
  ixs_node *wrapped =
      ixs_add(ctx, ixs_mod(ctx, biased, ixs_int(ctx, INT64_C(4294967296))),
              ixs_int(ctx, INT64_C(-2147483648)));
  return ixs_cmp(ctx, ixs_sub(ctx, wrapped, limit), op, ixs_int(ctx, 0));
}

static void test_public_equivalence_congruent_signed_no_wrap(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *base = ixs_sym(ctx, "equiv_signed_base");
  ixs_node *limit = ixs_sym(ctx, "equiv_signed_limit");
  ixs_node *toggle = ixs_sym(ctx, "equiv_signed_toggle");
  ixs_node *lt_one = signed_i32_offset_cmp(ctx, base, limit, 1, IXS_CMP_LT);
  ixs_node *lt_seven = signed_i32_offset_cmp(ctx, base, limit, 7, IXS_CMP_LT);
  ixs_node *lt_sixteen =
      signed_i32_offset_cmp(ctx, base, limit, 16, IXS_CMP_LT);
  ixs_node *le_one = signed_i32_offset_cmp(ctx, base, limit, 1, IXS_CMP_LE);
  ixs_node *le_seven = signed_i32_offset_cmp(ctx, base, limit, 7, IXS_CMP_LE);
  ixs_node *gt_one = signed_i32_offset_cmp(ctx, base, limit, 1, IXS_CMP_GT);
  ixs_node *gt_seven = signed_i32_offset_cmp(ctx, base, limit, 7, IXS_CMP_GT);
  ixs_node *bucket_base =
      ixs_add(ctx, base, ixs_mul(ctx, ixs_int(ctx, 4), toggle));
  ixs_node *bucket_plus_eight = ixs_add(ctx, bucket_base, ixs_int(ctx, 8));
  ixs_node *bucket_plus_twelve = ixs_add(ctx, bucket_base, ixs_int(ctx, 12));
  ixs_facts *aligned = ixs_facts_create(ctx);
  ixs_facts *signed_only = ixs_facts_create(ctx);
  ixs_facts *bucket = ixs_facts_create(ctx);

  assume_signed_i32_grid(ctx, aligned, base);
  assume_signed_i32_grid(ctx, aligned, limit);
  CHECK(test_ixs_equivalent_facts(aligned, lt_one, lt_seven) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(aligned, lt_one, lt_sixteen) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_facts(aligned, le_one, le_seven) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(aligned, gt_one, gt_seven) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(
      signed_only, ixs_cmp(ctx, base, IXS_CMP_GE, ixs_int(ctx, INT32_MIN))));
  CHECK(ixs_facts_assume_pred(
      signed_only, ixs_cmp(ctx, base, IXS_CMP_LE, ixs_int(ctx, INT32_MAX))));
  CHECK(ixs_facts_assume_pred(
      signed_only, ixs_cmp(ctx, limit, IXS_CMP_GE, ixs_int(ctx, INT32_MIN))));
  CHECK(ixs_facts_assume_pred(
      signed_only, ixs_cmp(ctx, limit, IXS_CMP_LE, ixs_int(ctx, INT32_MAX))));
  CHECK(test_ixs_equivalent_facts(signed_only, lt_one, lt_seven) ==
        IXS_CHECK_UNKNOWN);

  assume_signed_i32_grid(ctx, bucket, base);
  assume_signed_i32_grid(ctx, bucket, limit);
  CHECK(ixs_facts_assume_pred(
      bucket, ixs_cmp(ctx, toggle, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      bucket, ixs_cmp(ctx, toggle, IXS_CMP_LE, ixs_int(ctx, 1))));
  CHECK(test_ixs_check_facts(bucket, ixs_cmp(ctx, bucket_plus_eight, IXS_CMP_LE,
                                             ixs_int(ctx, INT32_MAX))) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(
            bucket, ixs_cmp(ctx, bucket_plus_twelve, IXS_CMP_LE,
                            ixs_int(ctx, INT32_MAX))) == IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static ixs_node *wrapped_xor_ordered_cmp(ixs_ctx *ctx, ixs_node *lane,
                                         ixs_node *tile, ixs_node *limit,
                                         int64_t offset) {
  ixs_node *lane_bits = ixs_mul(ctx, ixs_int(ctx, 128), lane);
  ixs_node *tile_bits = ixs_mul(ctx, ixs_int(ctx, 256), tile);
  ixs_node *xor_bits = ixs_xor(ctx, ixs_int(ctx, 64 + offset), lane_bits);
  ixs_node *biased = ixs_add(ctx, ixs_int(ctx, INT64_C(2147483648)),
                             ixs_add(ctx, tile_bits, xor_bits));
  ixs_node *wrapped =
      ixs_add(ctx, ixs_mod(ctx, biased, ixs_int(ctx, INT64_C(4294967296))),
              ixs_int(ctx, INT64_C(-2147483648)));
  return ixs_cmp(ctx, ixs_sub(ctx, wrapped, limit), IXS_CMP_LT,
                 ixs_int(ctx, 0));
}

static void test_public_equivalence_ordered_congruence_forms(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *base = ixs_sym(ctx, "ordered_grid_base");
  ixs_node *limit = ixs_sym(ctx, "ordered_grid_limit");
  ixs_node *toggle = ixs_sym(ctx, "ordered_grid_toggle");
  ixs_node *residual = ixs_sub(
      ctx, ixs_add(ctx, base, ixs_mul(ctx, ixs_int(ctx, 4), toggle)), limit);
  ixs_node *plus_four = ixs_add(ctx, residual, ixs_int(ctx, 4));
  ixs_node *plus_eight = ixs_add(ctx, residual, ixs_int(ctx, 8));
  ixs_node *plus_twelve = ixs_add(ctx, residual, ixs_int(ctx, 12));
  ixs_node *plus_sixteen = ixs_add(ctx, residual, ixs_int(ctx, 16));
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_facts *grid = ixs_facts_create(ctx);
  ixs_facts *coarse = ixs_facts_create(ctx);
  ixs_facts *wide_toggle = ixs_facts_create(ctx);
  ixs_node *lane = ixs_sym(ctx, "ordered_wrap_lane");
  ixs_node *tile = ixs_sym(ctx, "ordered_wrap_tile");
  ixs_node *wrap_limit = ixs_sym(ctx, "ordered_wrap_limit");
  ixs_facts *wrapped = ixs_facts_create(ctx);
  ixs_facts *wrapped_no_lane = ixs_facts_create(ctx);
  ixs_facts *wrapped_no_limit_grid = ixs_facts_create(ctx);
  ixs_node *wrapped_base =
      wrapped_xor_ordered_cmp(ctx, lane, tile, wrap_limit, 0);
  int64_t offset;

  CHECK(ixs_facts_assume_pred(
      grid,
      ixs_cmp(ctx, ixs_mod(ctx, base, ixs_int(ctx, 16)), IXS_CMP_EQ, zero)));
  CHECK(ixs_facts_assume_pred(
      grid,
      ixs_cmp(ctx, ixs_mod(ctx, limit, ixs_int(ctx, 16)), IXS_CMP_EQ, zero)));
  CHECK(ixs_facts_assume_pred(grid, ixs_cmp(ctx, toggle, IXS_CMP_GE, zero)));
  CHECK(ixs_facts_assume_pred(
      grid, ixs_cmp(ctx, toggle, IXS_CMP_LE, ixs_int(ctx, 1))));

  CHECK(test_ixs_equivalent_facts(
            grid, ixs_cmp(ctx, residual, IXS_CMP_LT, zero),
            ixs_cmp(ctx, plus_eight, IXS_CMP_LT, zero)) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(
            grid, ixs_cmp(ctx, residual, IXS_CMP_GE, zero),
            ixs_cmp(ctx, plus_eight, IXS_CMP_GE, zero)) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(
            grid, ixs_cmp(ctx, plus_four, IXS_CMP_LE, zero),
            ixs_cmp(ctx, plus_twelve, IXS_CMP_LE, zero)) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(
            grid, ixs_cmp(ctx, plus_four, IXS_CMP_GT, zero),
            ixs_cmp(ctx, plus_twelve, IXS_CMP_GT, zero)) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(
      coarse,
      ixs_cmp(ctx, ixs_mod(ctx, base, ixs_int(ctx, 8)), IXS_CMP_EQ, zero)));
  CHECK(ixs_facts_assume_pred(
      coarse,
      ixs_cmp(ctx, ixs_mod(ctx, limit, ixs_int(ctx, 8)), IXS_CMP_EQ, zero)));
  CHECK(ixs_facts_assume_pred(coarse, ixs_cmp(ctx, toggle, IXS_CMP_GE, zero)));
  CHECK(ixs_facts_assume_pred(
      coarse, ixs_cmp(ctx, toggle, IXS_CMP_LE, ixs_int(ctx, 1))));
  CHECK(test_ixs_equivalent_facts(
            coarse, ixs_cmp(ctx, residual, IXS_CMP_LT, zero),
            ixs_cmp(ctx, plus_eight, IXS_CMP_LT, zero)) == IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(
      wide_toggle,
      ixs_cmp(ctx, ixs_mod(ctx, base, ixs_int(ctx, 16)), IXS_CMP_EQ, zero)));
  CHECK(ixs_facts_assume_pred(
      wide_toggle,
      ixs_cmp(ctx, ixs_mod(ctx, limit, ixs_int(ctx, 16)), IXS_CMP_EQ, zero)));
  CHECK(ixs_facts_assume_pred(wide_toggle,
                              ixs_cmp(ctx, toggle, IXS_CMP_GE, zero)));
  CHECK(ixs_facts_assume_pred(
      wide_toggle, ixs_cmp(ctx, toggle, IXS_CMP_LE, ixs_int(ctx, 2))));
  CHECK(test_ixs_equivalent_facts(
            wide_toggle, ixs_cmp(ctx, residual, IXS_CMP_LT, zero),
            ixs_cmp(ctx, plus_eight, IXS_CMP_LT, zero)) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_facts(
            grid, ixs_cmp(ctx, residual, IXS_CMP_LT, zero),
            ixs_cmp(ctx, plus_sixteen, IXS_CMP_LT, zero)) == IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(wrapped, ixs_cmp(ctx, lane, IXS_CMP_GE, zero)));
  CHECK(ixs_facts_assume_pred(
      wrapped, ixs_cmp(ctx, lane, IXS_CMP_LE, ixs_int(ctx, 31))));
  CHECK(ixs_facts_assume_pred(
      wrapped, ixs_cmp(ctx, ixs_mod(ctx, wrap_limit, ixs_int(ctx, 4)),
                       IXS_CMP_EQ, zero)));
  for (offset = 1; offset <= 3; offset++)
    CHECK(test_ixs_equivalent_facts(
              wrapped, wrapped_base,
              wrapped_xor_ordered_cmp(ctx, lane, tile, wrap_limit, offset)) ==
          IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(
            wrapped, wrapped_base,
            wrapped_xor_ordered_cmp(ctx, lane, tile, wrap_limit, 4)) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(
      wrapped_no_lane, ixs_cmp(ctx, ixs_mod(ctx, wrap_limit, ixs_int(ctx, 4)),
                               IXS_CMP_EQ, zero)));
  CHECK(test_ixs_equivalent_facts(
            wrapped_no_lane, wrapped_base,
            wrapped_xor_ordered_cmp(ctx, lane, tile, wrap_limit, 1)) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_facts_assume_pred(wrapped_no_limit_grid,
                              ixs_cmp(ctx, lane, IXS_CMP_GE, zero)));
  CHECK(ixs_facts_assume_pred(
      wrapped_no_limit_grid, ixs_cmp(ctx, lane, IXS_CMP_LE, ixs_int(ctx, 31))));
  CHECK(test_ixs_equivalent_facts(
            wrapped_no_limit_grid, wrapped_base,
            wrapped_xor_ordered_cmp(ctx, lane, tile, wrap_limit, 1)) ==
        IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_public_equivalence_ordered_candidate_growth(void) {
  enum { DISTRACTOR_COUNT = 40 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *base = ixs_sym(ctx, "ordered_growth_base");
  ixs_node *limit = ixs_sym(ctx, "ordered_growth_limit");
  ixs_node *toggle = ixs_sym(ctx, "ordered_growth_toggle");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *residual = ixs_sub(
      ctx, ixs_add(ctx, base, ixs_mul(ctx, ixs_int(ctx, 16), toggle)), limit);
  ixs_facts *facts = ixs_facts_create(ctx);
  int i;

  CHECK(ixs_facts_assume_pred(
      facts,
      ixs_cmp(ctx, ixs_mod(ctx, base, ixs_int(ctx, 64)), IXS_CMP_EQ, zero)));
  CHECK(ixs_facts_assume_pred(
      facts,
      ixs_cmp(ctx, ixs_mod(ctx, limit, ixs_int(ctx, 64)), IXS_CMP_EQ, zero)));
  CHECK(ixs_facts_assume_pred(facts, ixs_cmp(ctx, toggle, IXS_CMP_GE, zero)));
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, toggle, IXS_CMP_LE, ixs_int(ctx, 1))));

  for (i = 0; i < DISTRACTOR_COUNT; i++) {
    char name[64];
    ixs_node *symbol;
    int64_t modulus = (int64_t)i + 2;
    CHECK(snprintf(name, sizeof(name), "ordered_growth_noise_%d", i) > 0);
    symbol = ixs_sym(ctx, name);
    residual = ixs_add(ctx, residual, ixs_mul(ctx, ixs_int(ctx, 64), symbol));
    CHECK(ixs_facts_assume_pred(
        facts, ixs_cmp(ctx, ixs_mod(ctx, symbol, ixs_int(ctx, modulus)),
                       IXS_CMP_EQ, zero)));
  }

  /* The useful modulus 64 follows more than 32 smaller distinct candidates.
   * Candidate discovery must grow instead of silently truncating the proof. */
  CHECK(test_ixs_equivalent_facts(
            facts, ixs_cmp(ctx, residual, IXS_CMP_LT, zero),
            ixs_cmp(ctx, ixs_add(ctx, residual, ixs_int(ctx, 32)), IXS_CMP_LT,
                    zero)) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_public_total_equivalence(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "equiv_x");
  ixs_node *y = ixs_sym(ctx, "equiv_y");
  ixs_node *z = ixs_sym(ctx, "equiv_z");
  ixs_node *k = ixs_sym(ctx, "equiv_k");
  ixs_node *slot = ixs_sym(ctx, "equiv_slot");
  ixs_node *p = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *q = ixs_cmp(ctx, y, IXS_CMP_LT, ixs_int(ctx, 4));
  ixs_node *r = ixs_cmp(ctx, z, IXS_CMP_NE, ixs_int(ctx, 0));
  ixs_node *and_lhs = ixs_and(ctx, ixs_and(ctx, p, q), r);
  ixs_node *and_rhs = ixs_and(ctx, p, ixs_and(ctx, r, q));
  ixs_node *or_lhs = ixs_or(ctx, ixs_or(ctx, p, q), r);
  ixs_node *or_rhs = ixs_or(ctx, r, ixs_or(ctx, q, p));
  ixs_node *reciprocal = ixs_div(ctx, ixs_int(ctx, 1), x);
  ixs_node *reciprocal_algebraic_lhs =
      ixs_div(ctx, ixs_add(ctx, x, ixs_int(ctx, 1)), x);
  ixs_node *reciprocal_algebraic_rhs =
      ixs_add(ctx, ixs_int(ctx, 1), reciprocal);
  ixs_node *polynomial = ixs_mul(ctx, ixs_add(ctx, x, ixs_int(ctx, 1)),
                                 ixs_add(ctx, x, ixs_int(ctx, 1)));
  ixs_node *expanded = ixs_add(
      ctx, ixs_add(ctx, ixs_mul(ctx, x, x), ixs_mul(ctx, ixs_int(ctx, 2), x)),
      ixs_int(ctx, 1));
  ixs_node *scaled = ixs_mul(ctx, ixs_int(ctx, 16), x);
  ixs_node *disjoint_xor = ixs_xor(ctx, scaled, slot);
  ixs_node *disjoint_add = ixs_add(ctx, scaled, slot);
  ixs_node *overlap_xor = ixs_xor(ctx, ixs_mul(ctx, ixs_int(ctx, 8), x), slot);
  ixs_node *overlap_add = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 8), x), slot);
  ixs_node *mod_lhs = ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 16)),
                              IXS_CMP_LT, ixs_int(ctx, 8));
  ixs_node *mod_rhs =
      ixs_cmp(ctx, ixs_mod(ctx, ixs_add(ctx, x, k), ixs_int(ctx, 16)),
              IXS_CMP_LT, ixs_int(ctx, 8));
  ixs_node *ordinary_lhs = ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 8));
  ixs_node *ordinary_rhs =
      ixs_cmp(ctx, ixs_add(ctx, x, k), IXS_CMP_LT, ixs_int(ctx, 8));
  ixs_node *x_zero = ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, 0));
  ixs_node *x_grid = ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 16)), IXS_CMP_EQ,
                             ixs_int(ctx, 0));
  ixs_facts *empty = ixs_facts_create(ctx);
  ixs_facts *nonzero = ixs_facts_create(ctx);
  ixs_facts *xor_facts = ixs_facts_create(ctx);
  ixs_facts *mod_facts = ixs_facts_create(ctx);
  ixs_facts *grid_facts = ixs_facts_create(ctx);
  ixs_facts *opposite = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);

  CHECK(test_ixs_equivalent_facts(empty, x, x) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(empty, polynomial, expanded) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(empty, and_lhs, and_rhs) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(empty, or_lhs, or_rhs) == IXS_CHECK_TRUE);

  CHECK(test_ixs_equivalent_facts(empty, reciprocal, reciprocal) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_facts(empty, reciprocal_algebraic_lhs,
                                  reciprocal_algebraic_rhs) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_facts_assume_pred(nonzero,
                              ixs_cmp(ctx, x, IXS_CMP_NE, ixs_int(ctx, 0))));
  CHECK(test_ixs_equivalent_facts(nonzero, reciprocal, reciprocal) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(nonzero, reciprocal_algebraic_lhs,
                                  reciprocal_algebraic_rhs) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(xor_facts,
                              ixs_cmp(ctx, slot, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      xor_facts, ixs_cmp(ctx, slot, IXS_CMP_LE, ixs_int(ctx, 15))));
  CHECK(ixs_facts_assume_pred(xor_facts,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(xor_facts,
                              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 100))));
  CHECK(test_ixs_equivalent_facts(xor_facts, disjoint_xor, disjoint_add) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(xor_facts, overlap_xor, overlap_add) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(mod_facts,
                              ixs_cmp(ctx, ixs_mod(ctx, k, ixs_int(ctx, 16)),
                                      IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(test_ixs_equivalent_facts(mod_facts, mod_lhs, mod_rhs) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(mod_facts, ordinary_lhs, ordinary_rhs) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_facts_assume_pred(grid_facts, x_grid));
  CHECK(test_ixs_equivalent_facts(grid_facts, x_zero, x_grid) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(opposite,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 10))));
  CHECK(test_ixs_equivalent_facts(
            opposite, ordinary_lhs,
            ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 8))) == IXS_CHECK_FALSE);
  CHECK(test_ixs_equivalent_facts(
            empty, ordinary_lhs,
            ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 9))) == IXS_CHECK_UNKNOWN);

  {
    ixs_facts *aligned = ixs_facts_create(ctx);
    ixs_facts *reachable = ixs_facts_create(ctx);
    ixs_node *lt_eight = ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 8));
    ixs_node *lt_nine = ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 9));
    CHECK(test_ixs_equivalent_facts(
              empty, lt_eight, ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 7))) ==
          IXS_CHECK_TRUE);
    CHECK(test_ixs_equivalent_facts(
              empty, ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 8)),
              ixs_cmp(ctx, x, IXS_CMP_GT, ixs_int(ctx, 7))) == IXS_CHECK_TRUE);
    CHECK(test_ixs_equivalent_facts(
              empty, ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, INT64_MAX)),
              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, INT64_MAX - 1))) ==
          IXS_CHECK_TRUE);
    CHECK(test_ixs_equivalent_facts(
              empty,
              ixs_cmp(ctx, ixs_add(ctx, x, ixs_int(ctx, INT64_MAX)), IXS_CMP_GT,
                      ixs_int(ctx, 0)),
              ixs_cmp(ctx, x, IXS_CMP_GT, ixs_int(ctx, 0))) ==
          IXS_CHECK_UNKNOWN);
    CHECK(ixs_facts_assume_pred(aligned,
                                ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 16)),
                                        IXS_CMP_EQ, ixs_int(ctx, 0))));
    CHECK(test_ixs_equivalent_facts(aligned, lt_eight, lt_nine) ==
          IXS_CHECK_TRUE);
    CHECK(ixs_facts_assume_pred(reachable,
                                ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 8)),
                                        IXS_CMP_EQ, ixs_int(ctx, 0))));
    CHECK(test_ixs_equivalent_facts(reachable, lt_eight, lt_nine) ==
          IXS_CHECK_UNKNOWN);
    CHECK(test_ixs_equivalent_facts(
              empty, lt_eight, ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 9))) ==
          IXS_CHECK_UNKNOWN);
    CHECK(test_ixs_equivalent_facts(
              empty,
              ixs_cmp(ctx, ixs_div(ctx, x, ixs_int(ctx, 2)), IXS_CMP_LT,
                      ixs_int(ctx, 8)),
              ixs_cmp(ctx, ixs_div(ctx, x, ixs_int(ctx, 2)), IXS_CMP_LE,
                      ixs_int(ctx, 7))) == IXS_CHECK_UNKNOWN);
  }

  {
    ixs_node *a = ixs_sym(ctx, "equiv_mod_shift_a");
    ixs_node *d = ixs_sym(ctx, "equiv_mod_shift_d");
    ixs_node *next = ixs_mod(ctx, ixs_add(ctx, a, ixs_int(ctx, 1)), d);
    ixs_node *next_sum = ixs_add(ctx, ixs_mod(ctx, a, d), ixs_int(ctx, 1));
    ixs_node *previous = ixs_mod(ctx, ixs_sub(ctx, a, ixs_int(ctx, 2)), d);
    ixs_node *previous_sum = ixs_sub(ctx, ixs_mod(ctx, a, d), ixs_int(ctx, 2));
    ixs_node *lower_cross = ixs_mod(ctx, ixs_sub(ctx, a, ixs_int(ctx, 4)), d);
    ixs_node *lower_cross_sum =
        ixs_sub(ctx, ixs_mod(ctx, a, d), ixs_int(ctx, 4));
    ixs_node *half = ixs_div(ctx, a, ixs_int(ctx, 2));
    ixs_node *half_next = ixs_mod(ctx, ixs_add(ctx, half, ixs_int(ctx, 1)), d);
    ixs_node *half_next_sum =
        ixs_add(ctx, ixs_mod(ctx, half, d), ixs_int(ctx, 1));
    ixs_facts *safe = ixs_facts_create(ctx);
    ixs_facts *boundary = ixs_facts_create(ctx);
    ixs_facts *no_positive = ixs_facts_create(ctx);
    ixs_facts *negative_divisor = ixs_facts_create(ctx);
    ixs_facts *no_divisibility = ixs_facts_create(ctx);
    ixs_facts *noninteger = ixs_facts_create(ctx);
    ixs_node *d_divisible = ixs_cmp(ctx, ixs_mod(ctx, d, ixs_int(ctx, 16)),
                                    IXS_CMP_EQ, ixs_int(ctx, 0));
    ixs_node *d_positive = ixs_cmp(ctx, d, IXS_CMP_GT, ixs_int(ctx, 0));
    ixs_node *a_three = ixs_cmp(ctx, ixs_mod(ctx, a, ixs_int(ctx, 16)),
                                IXS_CMP_EQ, ixs_int(ctx, 3));
    ixs_node *a_fifteen = ixs_cmp(ctx, ixs_mod(ctx, a, ixs_int(ctx, 16)),
                                  IXS_CMP_EQ, ixs_int(ctx, 15));
    CHECK(ixs_facts_assume_pred(safe, a_three));
    CHECK(ixs_facts_assume_pred(safe, d_divisible));
    CHECK(ixs_facts_assume_pred(safe, d_positive));
    CHECK(test_ixs_equivalent_facts(safe, next, next_sum) == IXS_CHECK_TRUE);
    CHECK(test_ixs_equivalent_facts(safe, previous, previous_sum) ==
          IXS_CHECK_TRUE);
    CHECK(test_ixs_equivalent_facts(safe, next_sum, next) == IXS_CHECK_TRUE);
    CHECK(test_ixs_equivalent_facts(safe, lower_cross, lower_cross_sum) ==
          IXS_CHECK_UNKNOWN);

    CHECK(ixs_facts_assume_pred(boundary, a_fifteen));
    CHECK(ixs_facts_assume_pred(boundary, d_divisible));
    CHECK(ixs_facts_assume_pred(boundary, d_positive));
    CHECK(test_ixs_equivalent_facts(boundary, next, next_sum) ==
          IXS_CHECK_UNKNOWN);

    CHECK(ixs_facts_assume_pred(no_positive, a_three));
    CHECK(ixs_facts_assume_pred(no_positive, d_divisible));
    CHECK(test_ixs_equivalent_facts(no_positive, next, next_sum) ==
          IXS_CHECK_UNKNOWN);

    CHECK(ixs_facts_assume_pred(negative_divisor, a_three));
    CHECK(ixs_facts_assume_pred(negative_divisor, d_divisible));
    CHECK(ixs_facts_assume_pred(negative_divisor,
                                ixs_cmp(ctx, d, IXS_CMP_LT, ixs_int(ctx, 0))));
    CHECK(test_ixs_equivalent_facts(negative_divisor, next, next_sum) ==
          IXS_CHECK_UNKNOWN);

    CHECK(ixs_facts_assume_pred(no_divisibility, a_three));
    CHECK(ixs_facts_assume_pred(no_divisibility, d_positive));
    CHECK(test_ixs_equivalent_facts(no_divisibility, next, next_sum) ==
          IXS_CHECK_UNKNOWN);

    CHECK(ixs_facts_assume_pred(noninteger, d_divisible));
    CHECK(ixs_facts_assume_pred(noninteger, d_positive));
    CHECK(test_ixs_equivalent_facts(noninteger, half_next, half_next_sum) ==
          IXS_CHECK_UNKNOWN);
  }

  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 10))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 5))));
  CHECK(test_ixs_equivalent_facts(contradictory, ixs_int(ctx, 1),
                                  ixs_int(ctx, 2)) == IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static ixs_node *parse_bounds_expr(ixs_ctx *ctx, const char *text) {
  return ixs_parse_expr(ctx, text, strlen(text));
}

static ixs_node *parse_bounds_pred(ixs_ctx *ctx, const char *text) {
  return ixs_parse_pred(ctx, text, strlen(text));
}

static void test_public_trunc_primitive_constant_difference(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "trunc_primitive_x");
  ixs_node *d = ixs_sym(ctx, "trunc_primitive_d");
  ixs_node *sixteen = ixs_int(ctx, 16);
  ixs_node *base =
      ixs_sub(ctx, x, ixs_mul(ctx, d, ixs_trunc(ctx, ixs_div(ctx, x, d))));
  ixs_node *scaled_base = ixs_mul(ctx, sixteen, base);
  ixs_facts *facts = ixs_facts_create(ctx);
  int64_t offset;
  int64_t delta = 0;

  CHECK(ctx && x && d && sixteen && scaled_base && facts);
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, d, IXS_CMP_NE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 8)),
                                      IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(facts, ixs_cmp(ctx, ixs_mod(ctx, d, sixteen),
                                             IXS_CMP_EQ, ixs_int(ctx, 0))));

  for (offset = 1; offset <= 7; offset++) {
    ixs_node *numerator = ixs_add(ctx, x, ixs_int(ctx, offset));
    ixs_node *remainder =
        ixs_sub(ctx, numerator,
                ixs_mul(ctx, d, ixs_trunc(ctx, ixs_div(ctx, numerator, d))));
    ixs_node *scaled = ixs_mul(ctx, sixteen, remainder);
    CHECK(
        test_ixs_constant_difference_facts(facts, scaled, scaled_base, &delta));
    CHECK(delta == 16 * offset);
  }

  ixs_ctx_destroy(ctx);
}

static void test_public_truncating_remainder_equivalence(void) {
  static const char scaled_zero[] = "16*x - 16*d*Piecewise((floor(x/d), "
                                    "(x >= 0 & d > 0) | (x <= 0 & d < 0)), "
                                    "(ceiling(x/d), True))";
  static const char scaled_next[] =
      "16 + 16*x - 16*d*Piecewise((floor((1 + x)/d), "
      "((1 + x) >= 0 & d > 0) | ((1 + x) <= 0 & d < 0)), "
      "(ceiling((1 + x)/d), True))";
  static const char wave_negative_zero[] =
      "16*x - 16*d*Piecewise((floor(x/d), x <= 0 & d < 0), "
      "(ceiling(x/d), True))";
  static const char wave_negative_next[] =
      "16 + 16*x - 16*d*Piecewise((floor((1 + x)/d), "
      "(1 + x) <= 0 & d < 0), (ceiling((1 + x)/d), True))";
  static const char floor_quotient[] = "floor(x/d)";
  static const char ceiling_quotient[] = "ceiling(x/d)";
  static const char positive_remainder_quotient[] = "(x - Mod(x, 4))/d";
  static const char negative_remainder_quotient[] = "(x + Mod(-x, 4))/d";
  static const char wrong_zero[] =
      "16*x - 16*d*Piecewise((floor(x/d), x < 0 & d < 0), "
      "(ceiling(x/d), True))";
  static const char wrong_next[] =
      "16 + 16*x - 16*d*Piecewise((floor((1 + x)/d), "
      "(1 + x) < 0 & d < 0), (ceiling((1 + x)/d), True))";
  static const char overlap_zero[] =
      "16*x - 16*d*Piecewise((floor(x/d), "
      "(x <= 0 & d < 0) | x == 1), (ceiling(x/d), True))";
  static const char overlap_next[] =
      "16 + 16*x - 16*d*Piecewise((floor((1 + x)/d), "
      "((1 + x) <= 0 & d < 0) | (1 + x) == 1), "
      "(ceiling((1 + x)/d), True))";
  static const char uncovered_zero[] =
      "16*x - 16*d*Piecewise((floor(x/d), x <= 0 & d < 0), "
      "(ceiling(x/d), x >= 0))";
  static const char uncovered_next[] =
      "16 + 16*x - 16*d*Piecewise((floor((1 + x)/d), "
      "(1 + x) <= 0 & d < 0), (ceiling((1 + x)/d), (1 + x) >= 0))";
  static const char nonintegral_zero[] =
      "16*Max(x/2, 0) - 16*d*Piecewise((floor(Max(x/2, 0)/d), "
      "(Max(x/2, 0) >= 0 & d > 0) | "
      "(Max(x/2, 0) <= 0 & d < 0)), "
      "(ceiling(Max(x/2, 0)/d), True))";
  static const char nonintegral_next[] =
      "16 + 16*Max(x/2, 0) - 16*d*Piecewise("
      "(floor((1 + Max(x/2, 0))/d), "
      "((1 + Max(x/2, 0)) >= 0 & d > 0) | "
      "((1 + Max(x/2, 0)) <= 0 & d < 0)), "
      "(ceiling((1 + Max(x/2, 0))/d), True))";
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *zero = parse_bounds_expr(ctx, scaled_zero);
  ixs_node *next = parse_bounds_expr(ctx, scaled_next);
  ixs_node *negative_zero = parse_bounds_expr(ctx, wave_negative_zero);
  ixs_node *negative_next = parse_bounds_expr(ctx, wave_negative_next);
  ixs_node *floor = parse_bounds_expr(ctx, floor_quotient);
  ixs_node *ceiling = parse_bounds_expr(ctx, ceiling_quotient);
  ixs_node *positive_quotient =
      parse_bounds_expr(ctx, positive_remainder_quotient);
  ixs_node *negative_quotient =
      parse_bounds_expr(ctx, negative_remainder_quotient);
  ixs_node *wrong0 = parse_bounds_expr(ctx, wrong_zero);
  ixs_node *wrong1 = parse_bounds_expr(ctx, wrong_next);
  ixs_node *overlap0 = parse_bounds_expr(ctx, overlap_zero);
  ixs_node *overlap1 = parse_bounds_expr(ctx, overlap_next);
  ixs_node *uncovered0 = parse_bounds_expr(ctx, uncovered_zero);
  ixs_node *uncovered1 = parse_bounds_expr(ctx, uncovered_next);
  ixs_node *nonintegral0 = parse_bounds_expr(ctx, nonintegral_zero);
  ixs_node *nonintegral1 = parse_bounds_expr(ctx, nonintegral_next);
  ixs_node *sixteen = ixs_int(ctx, 16);
  ixs_facts *positive = ixs_facts_create(ctx);
  ixs_facts *dynamic_positive = ixs_facts_create(ctx);
  ixs_facts *negative_divisor = ixs_facts_create(ctx);
  ixs_facts *at_zero = ixs_facts_create(ctx);
  ixs_facts *negative_positive_divisor = ixs_facts_create(ctx);
  ixs_facts *negative_negative_divisor = ixs_facts_create(ctx);
  ixs_facts *positive_boundary = ixs_facts_create(ctx);
  ixs_facts *negative_boundary = ixs_facts_create(ctx);
  ixs_facts *zero_divisor = ixs_facts_create(ctx);
  ixs_facts *unknown_divisor = ixs_facts_create(ctx);
  ixs_facts *nonintegral = ixs_facts_create(ctx);
  int64_t delta;

  CHECK(ctx && zero && next && negative_zero && negative_next && floor &&
        ceiling && positive_quotient && negative_quotient && wrong0 && wrong1 &&
        overlap0 && overlap1 && uncovered0 && uncovered1 && nonintegral0 &&
        nonintegral1 && sixteen);

  CHECK(ixs_facts_assume_pred(positive, parse_bounds_pred(ctx, "x >= 0")));
  CHECK(ixs_facts_assume_pred(positive,
                              parse_bounds_pred(ctx, "x <= 1073741822")));
  CHECK(ixs_facts_assume_pred(positive, parse_bounds_pred(ctx, "d == 4")));
  CHECK(ixs_facts_assume_pred(positive,
                              parse_bounds_pred(ctx, "Mod(x, 2) == 0")));
  CHECK(test_ixs_equivalent_facts(
            positive, next, ixs_add(ctx, zero, sixteen)) == IXS_CHECK_TRUE);
  delta = 0;
  CHECK(test_ixs_constant_difference_facts(positive, next, zero, &delta));
  CHECK(delta == 16);
  CHECK(test_ixs_equivalent_facts(positive, floor, positive_quotient) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(positive, ceiling, positive_quotient) !=
        IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(dynamic_positive,
                              parse_bounds_pred(ctx, "x >= 0")));
  CHECK(ixs_facts_assume_pred(dynamic_positive,
                              parse_bounds_pred(ctx, "x <= 1073741822")));
  CHECK(ixs_facts_assume_pred(dynamic_positive,
                              parse_bounds_pred(ctx, "Mod(x, 2) == 0")));
  CHECK(ixs_facts_assume_pred(dynamic_positive,
                              parse_bounds_pred(ctx, "d >= 4")));
  CHECK(ixs_facts_assume_pred(dynamic_positive,
                              parse_bounds_pred(ctx, "d <= 1073741824")));
  CHECK(ixs_facts_assume_pred(dynamic_positive,
                              parse_bounds_pred(ctx, "Mod(d, 4) == 0")));
  CHECK(test_ixs_equivalent_facts(dynamic_positive, next,
                                  ixs_add(ctx, zero, sixteen)) ==
        IXS_CHECK_TRUE);
  CHECK(
      test_ixs_constant_difference_facts(dynamic_positive, next, zero, &delta));
  CHECK(delta == 16);

  CHECK(ixs_facts_assume_pred(negative_divisor,
                              parse_bounds_pred(ctx, "x >= 0")));
  CHECK(ixs_facts_assume_pred(negative_divisor,
                              parse_bounds_pred(ctx, "x <= 1073741822")));
  CHECK(ixs_facts_assume_pred(negative_divisor,
                              parse_bounds_pred(ctx, "d == -4")));
  CHECK(ixs_facts_assume_pred(negative_divisor,
                              parse_bounds_pred(ctx, "Mod(x, 2) == 0")));
  CHECK(test_ixs_equivalent_facts(negative_divisor, negative_next,
                                  ixs_add(ctx, negative_zero, sixteen)) ==
        IXS_CHECK_TRUE);
  delta = 0;
  CHECK(test_ixs_constant_difference_facts(negative_divisor, negative_next,
                                           negative_zero, &delta));
  CHECK(delta == 16);
  CHECK(test_ixs_equivalent_facts(negative_divisor, ceiling,
                                  positive_quotient) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(negative_divisor, floor, positive_quotient) !=
        IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(at_zero, parse_bounds_pred(ctx, "x == 0")));
  CHECK(ixs_facts_assume_pred(at_zero, parse_bounds_pred(ctx, "d == -4")));
  CHECK(test_ixs_equivalent_facts(at_zero, negative_next,
                                  ixs_add(ctx, negative_zero, sixteen)) ==
        IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(negative_positive_divisor,
                              parse_bounds_pred(ctx, "x >= -100")));
  CHECK(ixs_facts_assume_pred(negative_positive_divisor,
                              parse_bounds_pred(ctx, "x <= -2")));
  CHECK(ixs_facts_assume_pred(negative_positive_divisor,
                              parse_bounds_pred(ctx, "d == 4")));
  CHECK(ixs_facts_assume_pred(negative_positive_divisor,
                              parse_bounds_pred(ctx, "Mod(x, 4) == 2")));
  CHECK(test_ixs_equivalent_facts(negative_positive_divisor, next,
                                  ixs_add(ctx, zero, sixteen)) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(negative_positive_divisor, ceiling,
                                  negative_quotient) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(negative_positive_divisor, floor,
                                  negative_quotient) != IXS_CHECK_TRUE);
  CHECK(ixs_facts_assume_pred(negative_negative_divisor,
                              parse_bounds_pred(ctx, "x >= -100")));
  CHECK(ixs_facts_assume_pred(negative_negative_divisor,
                              parse_bounds_pred(ctx, "x <= -2")));
  CHECK(ixs_facts_assume_pred(negative_negative_divisor,
                              parse_bounds_pred(ctx, "d == -4")));
  CHECK(ixs_facts_assume_pred(negative_negative_divisor,
                              parse_bounds_pred(ctx, "Mod(x, 4) == 2")));
  CHECK(test_ixs_equivalent_facts(negative_negative_divisor, next,
                                  ixs_add(ctx, zero, sixteen)) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(negative_negative_divisor, floor,
                                  negative_quotient) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(negative_negative_divisor, ceiling,
                                  negative_quotient) != IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(positive_boundary,
                              parse_bounds_pred(ctx, "x == 3")));
  CHECK(ixs_facts_assume_pred(positive_boundary,
                              parse_bounds_pred(ctx, "d == 4")));
  CHECK(test_ixs_equivalent_facts(positive_boundary, next,
                                  ixs_add(ctx, zero, sixteen)) !=
        IXS_CHECK_TRUE);
  CHECK(ixs_facts_assume_pred(negative_boundary,
                              parse_bounds_pred(ctx, "x == -4")));
  CHECK(ixs_facts_assume_pred(negative_boundary,
                              parse_bounds_pred(ctx, "d == -4")));
  CHECK(test_ixs_equivalent_facts(negative_boundary, next,
                                  ixs_add(ctx, zero, sixteen)) !=
        IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(zero_divisor, parse_bounds_pred(ctx, "x >= 0")));
  CHECK(ixs_facts_assume_pred(zero_divisor, parse_bounds_pred(ctx, "d == 0")));
  CHECK(test_ixs_equivalent_facts(zero_divisor, next,
                                  ixs_add(ctx, zero, sixteen)) ==
        IXS_CHECK_UNKNOWN);
  CHECK(!test_ixs_constant_difference_facts(zero_divisor, next, zero, &delta));
  CHECK(
      ixs_facts_assume_pred(unknown_divisor, parse_bounds_pred(ctx, "x >= 0")));
  CHECK(
      ixs_facts_assume_pred(unknown_divisor, parse_bounds_pred(ctx, "d != 0")));
  CHECK(ixs_facts_assume_pred(unknown_divisor,
                              parse_bounds_pred(ctx, "Mod(x, 2) == 0")));
  CHECK(test_ixs_equivalent_facts(unknown_divisor, next,
                                  ixs_add(ctx, zero, sixteen)) ==
        IXS_CHECK_UNKNOWN);

  CHECK(test_ixs_equivalent_facts(negative_divisor, wrong1,
                                  ixs_add(ctx, wrong0, sixteen)) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_facts(negative_divisor, overlap1,
                                  ixs_add(ctx, overlap0, sixteen)) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_facts(negative_divisor, uncovered1,
                                  ixs_add(ctx, uncovered0, sixteen)) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_facts_assume_pred(nonintegral, parse_bounds_pred(ctx, "x >= 0")));
  CHECK(ixs_facts_assume_pred(nonintegral, parse_bounds_pred(ctx, "x <= 100")));
  CHECK(ixs_facts_assume_pred(nonintegral, parse_bounds_pred(ctx, "d == -4")));
  CHECK(test_ixs_equivalent_facts(nonintegral, nonintegral1,
                                  ixs_add(ctx, nonintegral0, sixteen)) ==
        IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_public_truncating_remainder_oom(void) {
  static const char scaled_zero[] = "16*x - 16*d*Piecewise((floor(x/d), "
                                    "(x >= 0 & d > 0) | (x <= 0 & d < 0)), "
                                    "(ceiling(x/d), True))";
  static const char scaled_next[] =
      "16 + 16*x - 16*d*Piecewise((floor((1 + x)/d), "
      "((1 + x) >= 0 & d > 0) | ((1 + x) <= 0 & d < 0)), "
      "(ceiling((1 + x)/d), True))";
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *zero = parse_bounds_expr(ctx, scaled_zero);
  ixs_node *next = parse_bounds_expr(ctx, scaled_next);
  ixs_node *expected = ixs_add(ctx, zero, ixs_int(ctx, 16));
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *d = ixs_sym(ctx, "d");
  ixs_node *direct =
      ixs_sub(ctx, x, ixs_mul(ctx, d, ixs_trunc(ctx, ixs_div(ctx, x, d))));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_range_query_result range;

  CHECK(ctx && zero && next && expected && direct && facts);
  CHECK(ixs_facts_assume_pred(facts, parse_bounds_pred(ctx, "x >= 0")));
  CHECK(
      ixs_facts_assume_pred(facts, parse_bounds_pred(ctx, "x <= 1073741822")));
  CHECK(ixs_facts_assume_pred(facts, parse_bounds_pred(ctx, "d == 4")));
  CHECK(ixs_facts_assume_pred(facts, parse_bounds_pred(ctx, "Mod(x, 2) == 0")));

  ixs_arena_set_fail_after(&ctx->arena, 0);
  CHECK(test_ixs_equivalent_facts(facts, next, expected) == IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
  CHECK(test_ixs_equivalent_facts(facts, next, expected) == IXS_CHECK_TRUE);

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(test_ixs_equivalent_facts(facts, next, expected) == IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(test_ixs_equivalent_facts(facts, next, expected) == IXS_CHECK_TRUE);

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  range = ixs_range_facts(facts, direct);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(range.status == IXS_FACT_QUERY_OOM && !range.available &&
        !range.range.has_lower && !range.range.has_upper);
  range = ixs_range_facts(facts, direct);
  CHECK(range.status == IXS_FACT_QUERY_COMPLETE && range.available);

  ixs_ctx_destroy(ctx);
}

static void test_public_remainder_projection_candidate_growth(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_node *wide = ixs_int(ctx, 0);
  ixs_node *projected = ixs_int(ctx, 0);
  ixs_node *no_remainder = ixs_int(ctx, 0);
  ixs_node *other = ixs_sym(ctx, "remainder_limit_other");
  ixs_node *divisor = ixs_sym(ctx, "remainder_limit_divisor");
  char name[32];
  unsigned i;

  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, divisor, IXS_CMP_EQ, ixs_int(ctx, -4))));
  for (i = 0; i < 33u; i++) {
    ixs_node *symbol;
    ixs_node *quotient;
    ixs_node *values[2];
    ixs_node *conditions[2];
    ixs_node *round;
    ixs_node *modulo;
    snprintf(name, sizeof(name), "remainder_limit_%u", i);
    symbol = ixs_sym(ctx, name);
    CHECK(ixs_facts_assume_pred(
        facts, ixs_cmp(ctx, symbol, IXS_CMP_GE, ixs_int(ctx, 0))));
    CHECK(ixs_facts_assume_pred(
        facts, ixs_cmp(ctx, ixs_mod(ctx, symbol, ixs_int(ctx, 2)), IXS_CMP_EQ,
                       ixs_int(ctx, 0))));
    quotient = ixs_div(ctx, symbol, divisor);
    values[0] = ixs_floor(ctx, quotient);
    values[1] = ixs_ceil(ctx, quotient);
    conditions[0] =
        ixs_and(ctx, ixs_cmp(ctx, symbol, IXS_CMP_LE, ixs_int(ctx, 0)),
                ixs_cmp(ctx, divisor, IXS_CMP_LT, ixs_int(ctx, 0)));
    conditions[1] = ixs_true(ctx);
    round = ixs_sub(ctx, symbol,
                    ixs_mul(ctx, divisor, ixs_pw(ctx, 2, values, conditions)));
    modulo = ixs_mod(ctx, symbol, ixs_int(ctx, 4));
    wide = ixs_add(ctx, wide, round);
    projected = ixs_add(ctx, projected, modulo);
  }
  CHECK(test_ixs_equivalent_facts(facts, wide, projected) == IXS_CHECK_TRUE);

  for (i = 0; i < 400u; i++) {
    snprintf(name, sizeof(name), "remainder_plain_%u", i);
    no_remainder = ixs_add(ctx, no_remainder, ixs_sym(ctx, name));
  }
  CHECK(test_ixs_equivalent_facts(facts, no_remainder, other) ==
        IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_public_remainder_projection_large_candidate_set(void) {
  enum { CANDIDATE_COUNT = 1050 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "remainder_many_x");
  ixs_node *four = ixs_int(ctx, 4);
  ixs_node *lhs = ixs_int(ctx, 0);
  ixs_node *rhs = ixs_int(ctx, 0);
  ixs_facts *facts = ixs_facts_create(ctx);
  unsigned i;

  CHECK(ctx && x && four && lhs && rhs && facts);
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 100000))));
  for (i = 0; i < CANDIDATE_COUNT; i++) {
    ixs_node *numerator = ixs_add(ctx, x, ixs_int(ctx, (int64_t)i));
    ixs_node *remainder = ixs_mod(ctx, numerator, four);
    ixs_node *replacement =
        ixs_div(ctx, ixs_sub(ctx, numerator, remainder), four);
    lhs = ixs_add(ctx, lhs, ixs_floor(ctx, ixs_div(ctx, numerator, four)));
    rhs = ixs_add(ctx, rhs, replacement);
    CHECK(numerator && remainder && replacement && lhs && rhs);
  }

  CHECK(test_ixs_equivalent_facts(facts, lhs, rhs) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, rhs, lhs) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_public_remainder_projection_shared_diamond(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *raw = ixs_sym(ctx, "remainder_diamond_raw");
  ixs_node *inner_argument =
      ixs_add(ctx, ixs_div(ctx, raw, ixs_int(ctx, 64)), ixs_rat(ctx, 63, 64));
  ixs_node *inner_values[2] = {ixs_floor(ctx, inner_argument),
                               ixs_ceil(ctx, inner_argument)};
  ixs_node *inner_conditions[2] = {ixs_cmp(ctx,
                                           ixs_add(ctx, raw, ixs_int(ctx, 63)),
                                           IXS_CMP_GE, ixs_int(ctx, 0)),
                                   ixs_true(ctx)};
  ixs_node *inner = ixs_pw(ctx, 2, inner_values, inner_conditions);
  ixs_node *outer_numerator = ixs_sub(ctx, inner, ixs_int(ctx, 2));
  ixs_node *outer_argument =
      ixs_add(ctx, ixs_div(ctx, inner, ixs_int(ctx, 3)), ixs_rat(ctx, 1, 3));
  ixs_node *outer_values[2] = {
      ixs_add(ctx, ixs_int(ctx, -1), ixs_floor(ctx, outer_argument)),
      ixs_add(ctx, ixs_int(ctx, -1), ixs_ceil(ctx, outer_argument))};
  ixs_node *outer_conditions[2] = {
      ixs_cmp(ctx, outer_numerator, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_true(ctx)};
  ixs_node *outer = ixs_pw(ctx, 2, outer_values, outer_conditions);
  ixs_node *source =
      ixs_sub(ctx, outer_numerator, ixs_mul(ctx, ixs_int(ctx, 3), outer));
  ixs_node *positive_mod = ixs_mod(ctx, outer_numerator, ixs_int(ctx, 3));
  ixs_node *negative_mod = ixs_neg(
      ctx, ixs_mod(ctx, ixs_neg(ctx, outer_numerator), ixs_int(ctx, 3)));
  ixs_node *expected_values[2] = {positive_mod, negative_mod};
  ixs_node *expected_conditions[2] = {
      ixs_cmp(ctx, outer_numerator, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_true(ctx)};
  ixs_node *expected = ixs_pw(ctx, 2, expected_values, expected_conditions);
  ixs_facts *facts = ixs_facts_create(ctx);

  CHECK(ctx && raw && inner_argument && inner && outer_numerator &&
        outer_argument && outer && source && positive_mod && negative_mod &&
        expected && facts);
  expected = test_ixs_simplify_facts(facts, expected);
  CHECK(expected);

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(test_ixs_equivalent_facts(facts, source, expected) ==
        IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(test_ixs_simplify_facts(facts, source) == expected);
  CHECK(test_ixs_equivalent_facts(facts, source, expected) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, expected, source) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_public_modulo_pow2_equivalence(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "modulo_pow2_x");
  ixs_node *y = ixs_sym(ctx, "modulo_pow2_y");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *wrap_modulus = ixs_int(ctx, INT64_C(4294967296));
  ixs_node *wrapped_x = ixs_mod(ctx, x, wrap_modulus);
  ixs_node *wrapped_y = ixs_mod(ctx, y, wrap_modulus);
  ixs_node *targets[] = {x, y};
  ixs_node *replacements[] = {wrapped_x, wrapped_y};
  ixs_node *add = ixs_add(
      ctx, ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 3), x), ixs_int(ctx, 7)),
      ixs_mul(ctx, ixs_int(ctx, -5), y));
  ixs_node *product = ixs_mul(ctx, ixs_add(ctx, x, ixs_int(ctx, 3)),
                              ixs_add(ctx, y, ixs_int(ctx, 5)));
  ixs_node *bitwise = ixs_and(ctx, ixs_xor(ctx, x, ixs_int(ctx, 85)),
                              ixs_or(ctx, y, ixs_int(ctx, 256)));
  ixs_node *add_wrapped = ixs_subs_multi(ctx, add, 2, targets, replacements);
  ixs_node *product_wrapped =
      ixs_subs_multi(ctx, product, 2, targets, replacements);
  ixs_node *bitwise_wrapped =
      ixs_subs_multi(ctx, bitwise, 2, targets, replacements);
  ixs_node *mod16 = ixs_mod(ctx, add, ixs_int(ctx, 16));
  ixs_node *mod16_wrapped =
      ixs_subs_multi(ctx, mod16, 2, targets, replacements);
  ixs_node *mod12 = ixs_mod(ctx, add, ixs_int(ctx, 12));
  ixs_node *mod12_wrapped =
      ixs_subs_multi(ctx, mod12, 2, targets, replacements);
  ixs_node *floor_x = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)));
  ixs_node *floor_wrapped =
      ixs_floor(ctx, ixs_div(ctx, wrapped_x, ixs_int(ctx, 3)));
  ixs_node *ceil_x = ixs_ceil(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)));
  ixs_node *ceil_wrapped =
      ixs_ceil(ctx, ixs_div(ctx, wrapped_x, ixs_int(ctx, 3)));
  ixs_node *shared_opaque_lhs = ixs_add(
      ctx, wrapped_x, ixs_floor(ctx, ixs_div(ctx, wrapped_x, ixs_int(ctx, 3))));
  ixs_node *shared_opaque_rhs = ixs_add(ctx, x, floor_x);
  ixs_node *piecewise_values[] = {x, zero};
  ixs_node *piecewise_conditions[] = {ixs_cmp(ctx, x, IXS_CMP_GE, zero),
                                      ixs_true(ctx)};
  ixs_node *piecewise = ixs_pw(ctx, 2, piecewise_values, piecewise_conditions);
  ixs_node *piecewise_wrapped = ixs_subs(ctx, piecewise, x, wrapped_x);
  ixs_node *mod6 = ixs_mod(ctx, x, ixs_int(ctx, 6));
  ixs_node *wrapped4 = ixs_mod(ctx, x, ixs_int(ctx, 4));
  ixs_node *mod6_wrapped = ixs_mod(ctx, wrapped4, ixs_int(ctx, 6));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *x_is_six = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);
  ixs_facts *deep_facts = ixs_facts_create(ctx);
  ixs_node *deep = x;
  unsigned i;

  CHECK(ctx && other && x && y && zero && wrap_modulus && wrapped_x &&
        wrapped_y && add && product && bitwise && add_wrapped &&
        product_wrapped && bitwise_wrapped && mod16 && mod16_wrapped && mod12 &&
        mod12_wrapped && floor_x && floor_wrapped && ceil_x && ceil_wrapped &&
        shared_opaque_lhs && shared_opaque_rhs && piecewise &&
        piecewise_wrapped && mod6 && wrapped4 && mod6_wrapped && facts &&
        x_is_six && contradictory && deep_facts);

  CHECK(test_ixs_equivalent_modulo_pow2_facts(facts, x, wrapped_x, 32) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_modulo_pow2_facts(facts, add, add_wrapped, 32) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_modulo_pow2_facts(facts, product, product_wrapped,
                                              32) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_modulo_pow2_facts(facts, bitwise, bitwise_wrapped,
                                              32) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_modulo_pow2_facts(facts, mod16, mod16_wrapped, 4) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_modulo_pow2_facts(facts, mod12, mod12_wrapped, 2) ==
        IXS_CHECK_TRUE);

  CHECK(test_ixs_equivalent_modulo_pow2_facts(facts, x, y, 0) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_modulo_pow2_facts(facts, zero,
                                              ixs_int(ctx, INT64_C(4294967296)),
                                              32) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_modulo_pow2_facts(facts, zero,
                                              ixs_int(ctx, INT64_C(4294967297)),
                                              32) == IXS_CHECK_FALSE);
  CHECK(test_ixs_equivalent_modulo_pow2_facts(
            facts, zero, ixs_int(ctx, INT64_MIN), 63) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_modulo_pow2_facts(
            facts, zero, ixs_int(ctx, INT64_MAX), 63) == IXS_CHECK_FALSE);

  CHECK(test_ixs_equivalent_modulo_pow2_facts(facts, floor_x, floor_x, 4) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_modulo_pow2_facts(facts, floor_x, floor_wrapped,
                                              4) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_modulo_pow2_facts(facts, ceil_x, ceil_wrapped, 4) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_modulo_pow2_facts(facts, shared_opaque_lhs,
                                              shared_opaque_rhs,
                                              32) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_modulo_pow2_facts(
            facts, piecewise, piecewise_wrapped, 4) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_modulo_pow2_facts(facts, mod6, mod6_wrapped, 2) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_facts_assume_pred(x_is_six,
                              ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, 6))));
  CHECK(test_ixs_equivalent_modulo_pow2_facts(x_is_six, mod6, mod6_wrapped,
                                              2) == IXS_CHECK_FALSE);

  CHECK(test_ixs_equivalent_modulo_pow2_facts(facts, ixs_rat(ctx, 1, 2),
                                              ixs_rat(ctx, 1, 2),
                                              1) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 2))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 1))));
  CHECK(test_ixs_equivalent_modulo_pow2_facts(contradictory, x, x, 1) ==
        IXS_CHECK_UNKNOWN);

  for (i = 0; i < 70u; i++)
    deep = ixs_mod(ctx, deep, ixs_int(ctx, 1000 - (int64_t)(2u * i)));
  CHECK(deep != NULL);
  CHECK(test_ixs_equivalent_modulo_pow2_facts(deep_facts, deep, x, 1) ==
        IXS_CHECK_TRUE);

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(test_ixs_equivalent_modulo_pow2_facts(facts, x, wrapped_x, 32) ==
        IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(test_ixs_equivalent_modulo_pow2_facts(facts, x, wrapped_x, 32) ==
        IXS_CHECK_TRUE);

  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_equivalent_modulo_pow2_facts(facts, x, wrapped_x, 64) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "bits") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_equivalent_modulo_pow2_facts(facts, x,
                                              ixs_sym(other, "modulo_pow2_x"),
                                              32) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_equivalent_modulo_pow2_facts(facts, ctx->sentinel_error,
                                              ctx->sentinel_error,
                                              32) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "sentinel") != NULL);

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static ixs_finite_domain_result
finite_domain_equivalent(ixs_facts *facts, ixs_node *lhs, ixs_node *rhs,
                         size_t *remaining_work) {
  ixs_finite_domain_query query;
  query.kind = IXS_FINITE_DOMAIN_EQUIVALENCE;
  query.as.equivalence.lhs = lhs;
  query.as.equivalence.rhs = rhs;
  return ixs_finite_domain_facts(facts, &query, remaining_work);
}

static void test_public_finite_domain_equivalence(void) {
  static const char finite_text[] =
      "Piecewise((1, x*(x - 1)*(x - 2)*(x - 3) == 0), (2, True))";
  static const char unbounded_text[] =
      "y*Piecewise((0, x*(x - 1)*(x - 2)*(x - 3) == 0), (1, True))";
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "finite_equivalence_x");
  ixs_node *finite_x = ixs_sym(ctx, "x");
  ixs_node *finite = ixs_parse_expr(ctx, finite_text, sizeof(finite_text) - 1u);
  ixs_node *unbounded =
      ixs_parse_expr(ctx, unbounded_text, sizeof(unbounded_text) - 1u);
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *one = ixs_int(ctx, 1);
  ixs_facts *range_four = ixs_facts_create(ctx);
  ixs_facts *range_five = ixs_facts_create(ctx);
  ixs_facts *x_range = ixs_facts_create(ctx);
  ixs_facts *empty = ixs_facts_create(ctx);
  ixs_finite_domain_result result;
  size_t budget;

  CHECK(ctx && other && x && finite_x && finite && unbounded && range_four &&
        range_five && x_range && empty);
  CHECK(ixs_facts_assume_pred(range_four,
                              ixs_cmp(ctx, finite_x, IXS_CMP_GE, zero)));
  CHECK(ixs_facts_assume_pred(
      range_four, ixs_cmp(ctx, finite_x, IXS_CMP_LE, ixs_int(ctx, 3))));
  CHECK(ixs_facts_assume_pred(range_five,
                              ixs_cmp(ctx, finite_x, IXS_CMP_GE, zero)));
  CHECK(ixs_facts_assume_pred(
      range_five, ixs_cmp(ctx, finite_x, IXS_CMP_LE, ixs_int(ctx, 4))));
  CHECK(ixs_facts_assume_pred(x_range, ixs_cmp(ctx, x, IXS_CMP_GE, zero)));
  CHECK(ixs_facts_assume_pred(x_range,
                              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 1))));

  CHECK(test_ixs_equivalent_facts(range_four, finite, one) ==
        IXS_CHECK_UNKNOWN);
  budget = 4;
  result = finite_domain_equivalent(range_four, finite, one, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value == NULL);
  CHECK(budget == 0);

  budget = 4;
  result = finite_domain_equivalent(range_four, unbounded, zero, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value == NULL);
  CHECK(budget == 0);

  budget = 4;
  result = finite_domain_equivalent(range_five, finite, one, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_EXHAUSTED &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
  CHECK(budget == 4);
  budget = 5;
  result = finite_domain_equivalent(range_five, finite, one, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
  CHECK(budget == 0);
  budget = 5;
  result =
      finite_domain_equivalent(range_five, finite, ixs_int(ctx, 2), &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
  CHECK(budget == 0);

  budget = 7;
  result = finite_domain_equivalent(x_range, x, x, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value == NULL);
  CHECK(budget == 7);
  result = finite_domain_equivalent(x_range, zero, one, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_FALSE && result.value == NULL);
  CHECK(budget == 7);

  budget = 3;
  result = finite_domain_equivalent(
      empty, ixs_mul(ctx, x, ixs_sub(ctx, x, one)), zero, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
  CHECK(budget == 3);

  {
    enum { SYMBOLS = 65 };
    ixs_node *wide = zero;
    size_t symbol;
    for (symbol = 0; symbol < SYMBOLS; symbol++) {
      char name[48];
      snprintf(name, sizeof(name), "finite_equivalence_wide_%zu", symbol);
      wide = ixs_add(ctx, wide, ixs_sym(ctx, name));
    }
    budget = 1000;
    result = finite_domain_equivalent(x_range, wide, zero, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
    CHECK(budget == 1000);
  }

  {
    ixs_node *a = ixs_sym(ctx, "finite_equivalence_a");
    ixs_node *b = ixs_sym(ctx, "finite_equivalence_b");
    ixs_node *a_term = ixs_mul(ctx, a, ixs_sub(ctx, a, one));
    ixs_node *b_term = ixs_mul(ctx, ixs_mul(ctx, b, ixs_sub(ctx, b, one)),
                               ixs_sub(ctx, b, ixs_int(ctx, 2)));
    ixs_node *product_identity = ixs_add(ctx, a_term, b_term);
    ixs_facts *product_facts = ixs_facts_create(ctx);
    CHECK(ixs_facts_assume_pred(product_facts,
                                ixs_cmp(ctx, a, IXS_CMP_GE, zero)));
    CHECK(
        ixs_facts_assume_pred(product_facts, ixs_cmp(ctx, a, IXS_CMP_LE, one)));
    CHECK(ixs_facts_assume_pred(product_facts,
                                ixs_cmp(ctx, b, IXS_CMP_GE, zero)));
    CHECK(ixs_facts_assume_pred(product_facts,
                                ixs_cmp(ctx, b, IXS_CMP_LE, ixs_int(ctx, 2))));
    budget = 5;
    result = finite_domain_equivalent(product_facts, product_identity, zero,
                                      &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_EXHAUSTED &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
    CHECK(budget == 5);
    budget = 6;
    result = finite_domain_equivalent(product_facts, product_identity, zero,
                                      &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && result.value == NULL);
    CHECK(budget == 0);
  }

  ixs_ctx_clear_errors(ctx);
  result = finite_domain_equivalent(x_range, x, x, NULL);
  CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "remaining_work") != NULL);
  ixs_ctx_clear_errors(ctx);
  budget = 3;
  result = finite_domain_equivalent(
      x_range, x, ixs_sym(other, "finite_equivalence_x"), &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
  CHECK(budget == 3);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);

  budget = 4;
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  result = finite_domain_equivalent(range_four, finite, one, &budget);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(result.status == IXS_FINITE_DOMAIN_OOM &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
  CHECK(budget == 4);
  result = finite_domain_equivalent(range_four, finite, one, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value == NULL);
  CHECK(budget == 0);

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_finite_domain_equivalence_growable_discovery(void) {
  enum { FINITE_SYMBOLS = 80, QUERY_SYMBOLS = 4100 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *finite[FINITE_SYMBOLS];
  ixs_node **query_symbols = calloc(QUERY_SYMBOLS, sizeof(*query_symbols));
  ixs_node *wide;
  ixs_node *difference;
  ixs_range_result singleton_integer = {true, true, -1, 4, 1, 4};
  ixs_finite_domain_result result;
  char name[64];
  size_t budget = 1;
  size_t i;

  CHECK(ctx && facts && zero && one && query_symbols);
  if (!ctx || !facts || !zero || !one || !query_symbols) {
    free(query_symbols);
    ixs_ctx_destroy(ctx);
    return;
  }
  for (i = 0; i < FINITE_SYMBOLS; i++) {
    snprintf(name, sizeof(name), "finite_discovery_%03zu", i);
    finite[i] = ixs_sym(ctx, name);
    CHECK(finite[i] &&
          ixs_facts_assume_range(facts, finite[i], &singleton_integer));
  }
  for (i = 0; i < QUERY_SYMBOLS; i++) {
    snprintf(name, sizeof(name), "query_discovery_%04zu", i);
    query_symbols[i] = ixs_sym(ctx, name);
    CHECK(query_symbols[i]);
  }
  wide = ixs_max_many(ctx, QUERY_SYMBOLS, query_symbols);
  free(query_symbols);
  difference = ixs_mul(ctx, finite[0], wide);
  for (i = 1; i < FINITE_SYMBOLS; i++)
    difference = ixs_add(ctx, difference, finite[i]);

  CHECK(wide && difference);
  CHECK(test_ixs_equivalent_facts(facts, difference, zero) ==
        IXS_CHECK_UNKNOWN);
  result = finite_domain_equivalent(facts, difference, zero, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value == NULL);
  CHECK(budget == 0);

  ixs_ctx_destroy(ctx);
}

static ixs_finite_domain_result
finite_domain_synthesize(ixs_facts *facts, ixs_finite_domain_query_kind kind,
                         ixs_node *symbol, const int64_t *points,
                         ixs_node *const *values, size_t npoints,
                         size_t *remaining_work) {
  ixs_finite_domain_query query;
  query.kind = kind;
  query.as.synthesis.symbol = symbol;
  query.as.synthesis.points = points;
  query.as.synthesis.values = values;
  query.as.synthesis.npoints = npoints;
  return ixs_finite_domain_facts(facts, &query, remaining_work);
}

static void test_public_finite_domain_synthesis(void) {
  const int64_t points[4] = {4, 5, 6, 7};
  const int64_t noncontiguous[4] = {4, 5, 7, 8};
  const int64_t unordered[4] = {4, 5, 5, 8};
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *item = ixs_sym(ctx, "finite_synthesis_item");
  ixs_node *base = ixs_sym(ctx, "finite_synthesis_base");
  ixs_node *limit = ixs_sym(ctx, "finite_synthesis_limit");
  ixs_node *additive[4];
  ixs_node *gf2[4];
  ixs_node *unsupported[4];
  ixs_node *comparisons[4];
  ixs_node *nested[4];
  ixs_node *invariant_predicates[4];
  ixs_node *predicate_piecewise;
  ixs_node *predicate_piecewise_values[4];
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);
  ixs_finite_domain_result result;
  ixs_node *additive_candidate;
  ixs_node *predicate_candidate;
  size_t budget;
  size_t i;

  CHECK(ctx && other && item && base && limit && facts && contradictory);
  for (i = 0; i < 4u; i++) {
    static const int64_t additive_delta[4] = {0, 4, 8, 12};
    static const int64_t gf2_delta[4] = {0, 1, 1, 0};
    static const int64_t unsupported_delta[4] = {0, 1, 2, 4};
    ixs_node *greater;
    ixs_node *different;
    additive[i] = ixs_add(ctx, base, ixs_int(ctx, additive_delta[i]));
    gf2[i] = ixs_add(ctx, base, ixs_int(ctx, gf2_delta[i]));
    unsupported[i] = ixs_add(ctx, base, ixs_int(ctx, unsupported_delta[i]));
    greater = ixs_cmp(ctx, additive[i], IXS_CMP_GE, limit);
    different = ixs_not(ctx, ixs_cmp(ctx, gf2[i], IXS_CMP_EQ, limit));
    comparisons[i] = greater;
    nested[i] = ixs_and(ctx, greater, different);
    invariant_predicates[i] = comparisons[0];
    CHECK(additive[i] && gf2[i] && unsupported[i] && comparisons[i] &&
          nested[i]);
  }
  {
    const ixs_node *values[2] = {comparisons[0], nested[1]};
    const ixs_node *conditions[2] = {ixs_cmp(ctx, item, IXS_CMP_LT, base),
                                     ixs_true(ctx)};
    predicate_piecewise = (ixs_node *)ixs_pw(ctx, 2, values, conditions);
    CHECK(predicate_piecewise && predicate_piecewise->tag == IXS_PIECEWISE &&
          ixs_node_is_pred_kind(predicate_piecewise));
    for (i = 0; i < 4u; i++)
      predicate_piecewise_values[i] = predicate_piecewise;
  }

  budget = 8;
  result = finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_EXPR_SYNTHESIS,
                                    item, points, additive, 4, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value != NULL);
  CHECK(budget == 0);
  additive_candidate = (ixs_node *)result.value;

  {
    ixs_finite_domain_query relation;
    relation.kind = IXS_FINITE_DOMAIN_EXPR_RELATION;
    relation.as.relation.symbol = item;
    relation.as.relation.points = points;
    relation.as.relation.values = additive;
    relation.as.relation.npoints = 4;
    relation.as.relation.candidate = additive_candidate;
    budget = 4;
    result = ixs_finite_domain_facts(facts, &relation, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && result.value == NULL);
    CHECK(budget == 0);
    relation.as.relation.candidate = base;
    budget = 4;
    result = ixs_finite_domain_facts(facts, &relation, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
    CHECK(budget == 0);
    {
      ixs_node *reciprocal_values[4] = {ixs_rat(ctx, 1, 4), ixs_rat(ctx, 1, 5),
                                        ixs_rat(ctx, 1, 6), ixs_rat(ctx, 1, 7)};
      ixs_node *reciprocal = ixs_div(ctx, ixs_int(ctx, 1), item);
      CHECK(reciprocal_values[0] && reciprocal_values[1] &&
            reciprocal_values[2] && reciprocal_values[3] && reciprocal);
      relation.as.relation.values = reciprocal_values;
      relation.as.relation.candidate = reciprocal;
      budget = 4;
      result = ixs_finite_domain_facts(facts, &relation, &budget);
      CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
            result.check == IXS_CHECK_TRUE && result.value == NULL);
      CHECK(budget == 0);
      relation.as.relation.values = additive;
    }
    relation.as.relation.candidate = additive_candidate;
    budget = 4;
    ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
    result = ixs_finite_domain_facts(facts, &relation, &budget);
    ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
    CHECK(result.status == IXS_FINITE_DOMAIN_OOM &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
    CHECK(budget == 0);
    ixs_ctx_clear_errors(ctx);
    relation.as.relation.candidate = predicate_piecewise;
    budget = 4;
    result = ixs_finite_domain_facts(facts, &relation, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
    CHECK(budget == 0 && ixs_ctx_nerrors(ctx) == 0);
  }

  budget = 8;
  result = finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_EXPR_SYNTHESIS,
                                    item, points, gf2, 4, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value != NULL);
  CHECK(budget == 0);

  budget = 8;
  result = finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_EXPR_SYNTHESIS,
                                    item, points, unsupported, 4, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
  CHECK(budget == 0);

  budget = 7;
  result = finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_EXPR_SYNTHESIS,
                                    item, points, additive, 4, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_EXHAUSTED &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
  CHECK(budget == 7);

  budget = 8;
  result = finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_EXPR_SYNTHESIS,
                                    item, noncontiguous, additive, 4, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
  CHECK(budget == 0);
  budget = 6;
  result = finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_EXPR_SYNTHESIS,
                                    item, points, additive, 3, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value != NULL);
  CHECK(budget == 0);
  budget = 8;
  result = finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_EXPR_SYNTHESIS,
                                    item, unordered, additive, 4, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
  CHECK(budget == 8);

  budget = 24;
  result = finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_PRED_SYNTHESIS,
                                    item, points, comparisons, 4, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value != NULL);
  CHECK(budget == 0);
  predicate_candidate = (ixs_node *)result.value;
  {
    ixs_finite_domain_query relation;
    relation.kind = IXS_FINITE_DOMAIN_PRED_RELATION;
    relation.as.relation.symbol = item;
    relation.as.relation.points = points;
    relation.as.relation.values = comparisons;
    relation.as.relation.npoints = 4;
    relation.as.relation.candidate = predicate_candidate;
    budget = 4;
    result = ixs_finite_domain_facts(facts, &relation, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && result.value == NULL);
    CHECK(budget == 0);
  }

  /* Expression modes treat structured predicates as their canonical numeric
   * 0/1 values.  An invariant predicate table therefore synthesizes that
   * predicate and the expression relation proves the returned scalar. */
  budget = 8;
  result =
      finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_EXPR_SYNTHESIS, item,
                               points, invariant_predicates, 4, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value != NULL &&
        ixs_node_is_pred_kind(result.value));
  CHECK(budget == 0);
  {
    ixs_finite_domain_query relation;
    relation.kind = IXS_FINITE_DOMAIN_EXPR_RELATION;
    relation.as.relation.symbol = item;
    relation.as.relation.points = points;
    relation.as.relation.values = invariant_predicates;
    relation.as.relation.npoints = 4;
    relation.as.relation.candidate = result.value;
    budget = 4;
    result = ixs_finite_domain_facts(facts, &relation, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && result.value == NULL);
    CHECK(budget == 0);
  }

  ixs_ctx_clear_errors(ctx);
  budget = 8;
  result = finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_EXPR_SYNTHESIS,
                                    item, points, comparisons, 4, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
  CHECK(budget == 0 && ixs_ctx_nerrors(ctx) == 0);

  ixs_ctx_clear_errors(ctx);
  budget = 8;
  result =
      finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_EXPR_SYNTHESIS, item,
                               points, predicate_piecewise_values, 4, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
  CHECK(budget == 0 && ixs_ctx_nerrors(ctx) == 0);

  budget = 64;
  result = finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_PRED_SYNTHESIS,
                                    item, points, nested, 4, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value != NULL);
  CHECK(budget == 8);

  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, base, IXS_CMP_GE, ixs_int(ctx, 1))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, base, IXS_CMP_LE, ixs_int(ctx, 0))));
  budget = 8;
  result =
      finite_domain_synthesize(contradictory, IXS_FINITE_DOMAIN_EXPR_SYNTHESIS,
                               item, points, additive, 4, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
  CHECK(budget == 8);

  {
    ixs_finite_domain_query malformed;
    malformed.kind = IXS_FINITE_DOMAIN_EXPR_RELATION;
    malformed.as.relation = (ixs_finite_domain_relation_query){
        item, NULL, additive, 4, additive_candidate};
    budget = 0;
    result = ixs_finite_domain_facts(facts, &malformed, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 0);
    result = ixs_finite_domain_facts(contradictory, &malformed, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 0);

    malformed.kind = IXS_FINITE_DOMAIN_EXPR_SYNTHESIS;
    malformed.as.synthesis =
        (ixs_finite_domain_synthesis_query){item, NULL, additive, 4};
    result = ixs_finite_domain_facts(facts, &malformed, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 0);
    result = ixs_finite_domain_facts(contradictory, &malformed, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 0);
  }

  ixs_ctx_clear_errors(ctx);
  budget = 8;
  result = ixs_finite_domain_facts(facts, NULL, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
  CHECK(budget == 8 && ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "query is NULL") != NULL);

  {
    ixs_finite_domain_query invalid;
    memset(&invalid, 0, sizeof(invalid));
    invalid.kind = (ixs_finite_domain_query_kind)99;
    ixs_ctx_clear_errors(ctx);
    budget = 8;
    result = ixs_finite_domain_facts(facts, &invalid, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
    CHECK(budget == 8 && ixs_ctx_nerrors(ctx) == 1);
    CHECK(strstr(ixs_ctx_error(ctx, 0), "invalid query kind") != NULL);
  }

  {
    ixs_finite_domain_query hostile;
    size_t hostile_npoints = SIZE_MAX / sizeof(uint64_t) + 1u;
    const int64_t *hostile_points = (const int64_t *)(uintptr_t)1;
    const ixs_node *const *hostile_values =
        (const ixs_node *const *)(uintptr_t)1;
    memset(&hostile, 0, sizeof(hostile));
    hostile.kind = IXS_FINITE_DOMAIN_EXPR_RELATION;
    hostile.as.relation.symbol = item;
    hostile.as.relation.points = hostile_points;
    hostile.as.relation.values = hostile_values;
    hostile.as.relation.npoints = hostile_npoints;
    hostile.as.relation.candidate = additive_candidate;
    budget = SIZE_MAX;
    result = ixs_finite_domain_facts(facts, &hostile, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
    CHECK(budget == SIZE_MAX);

    hostile.kind = IXS_FINITE_DOMAIN_EXPR_SYNTHESIS;
    hostile.as.synthesis.symbol = item;
    hostile.as.synthesis.points = hostile_points;
    hostile.as.synthesis.values = hostile_values;
    hostile.as.synthesis.npoints = hostile_npoints;
    budget = SIZE_MAX;
    result = ixs_finite_domain_facts(facts, &hostile, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
    CHECK(budget == SIZE_MAX);

    hostile.kind = IXS_FINITE_DOMAIN_EXPR_RELATION;
    hostile.as.relation.symbol = item;
    hostile.as.relation.points = hostile_points;
    hostile.as.relation.values = hostile_values;
    hostile.as.relation.npoints = 2;
    hostile.as.relation.candidate = additive_candidate;
    budget = 0;
    result = ixs_finite_domain_facts(facts, &hostile, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_EXHAUSTED &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
    CHECK(budget == 0);

    hostile.kind = IXS_FINITE_DOMAIN_EXPR_SYNTHESIS;
    hostile.as.synthesis.symbol = item;
    hostile.as.synthesis.points = hostile_points;
    hostile.as.synthesis.values = hostile_values;
    hostile.as.synthesis.npoints = 4;
    budget = 1;
    result = ixs_finite_domain_facts(facts, &hostile, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_EXHAUSTED &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
    CHECK(budget == 1);
  }

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  budget = 8;
  result = finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_EXPR_SYNTHESIS,
                                    item, points, additive, 4, &budget);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(result.status == IXS_FINITE_DOMAIN_OOM &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
  CHECK(budget == 0);
  budget = 8;
  result = finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_EXPR_SYNTHESIS,
                                    item, points, additive, 4, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value != NULL);
  CHECK(budget == 0);

  ixs_ctx_clear_errors(ctx);
  additive[1] = ixs_sym(other, "finite_synthesis_foreign");
  budget = 8;
  result = finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_EXPR_SYNTHESIS,
                                    item, points, additive, 4, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL);
  CHECK(budget == 8 && ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_public_mapped_expression_facts(void) {
  const int64_t points[4] = {0, 1, 2, 3};
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *item = ixs_sym(ctx, "mapped_expression_item");
  ixs_node *base = ixs_sym(ctx, "mapped_expression_base");
  ixs_node *guard = ixs_sym(ctx, "mapped_expression_guard");
  ixs_node *scaled = ixs_mul(ctx, ixs_int(ctx, 4), item);
  const ixs_node *expressions[2] = {
      ixs_add(ctx, ixs_add(ctx, base, scaled), ixs_int(ctx, 7)),
      ixs_add(ctx, ixs_add(ctx, base, scaled), ixs_int(ctx, -3))};
  ixs_mapped_expression_row rows[7] = {
      {1, 2, 2, -3}, {0, 0, 0, 7},  {1, 3, 3, -3}, {0, 1, 1, 7},
      {0, 2, 2, 7},  {1, 0, 0, -3}, {1, 2, 2, -3}};
  ixs_mapped_expression_row mismatched[7];
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *strong = ixs_facts_create(ctx);
  ixs_facts *weak = ixs_facts_create(ctx);
  ixs_finite_domain_result result;
  const ixs_node *candidate;
  size_t budget;
  size_t i;

  CHECK(ctx && item && base && guard && scaled && expressions[0] &&
        expressions[1] && facts && strong && weak);
  budget = 10;
  result = ixs_synthesize_mapped_expression_facts(facts, item, expressions, 2,
                                                  points, 4, rows, 7, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_EXHAUSTED &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
        budget == 10);

  budget = 11;
  result = ixs_synthesize_mapped_expression_facts(facts, item, expressions, 2,
                                                  points, 4, rows, 7, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value != NULL && budget == 0);
  candidate = result.value;
  CHECK(test_ixs_equivalent_facts(
            facts, (ixs_node *)candidate,
            ixs_add(ctx, base, ixs_mul(ctx, ixs_int(ctx, 4), item))) ==
        IXS_CHECK_TRUE);

  budget = 7;
  result = ixs_verify_mapped_expression_facts(facts, item, expressions, 2, rows,
                                              7, candidate, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value == NULL && budget == 0);

  memcpy(mismatched, rows, sizeof(rows));
  mismatched[5].additive_offset = -2;
  budget = 11;
  result = ixs_synthesize_mapped_expression_facts(
      facts, item, expressions, 2, points, 4, mismatched, 7, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value == candidate &&
        budget == 0);
  budget = 7;
  result = ixs_verify_mapped_expression_facts(
      facts, item, expressions, 2, mismatched, 7, candidate, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
        budget == 0);

  {
    const ixs_node *gf2_expressions[1] = {ixs_xor(
        ctx, ixs_mod(ctx, item, ixs_int(ctx, 2)),
        ixs_mod(ctx, ixs_floor(ctx, ixs_div(ctx, item, ixs_int(ctx, 2))),
                ixs_int(ctx, 2)))};
    const ixs_mapped_expression_row gf2_rows[4] = {
        {0, 0, 0, 0}, {0, 1, 1, 0}, {0, 2, 2, 0}, {0, 3, 3, 0}};
    budget = 8;
    result = ixs_synthesize_mapped_expression_facts(
        facts, item, gf2_expressions, 1, points, 4, gf2_rows, 4, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && result.value != NULL &&
          budget == 0);
    budget = 4;
    result = ixs_verify_mapped_expression_facts(
        facts, item, gf2_expressions, 1, gf2_rows, 4, result.value, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && budget == 0);
  }

  {
    const int64_t shifted_points[2] = {0, 2};
    const ixs_node *shifted_expressions[2] = {
        ixs_add(ctx, ixs_int(ctx, 1), ixs_mul(ctx, ixs_int(ctx, 2), item)),
        ixs_add(ctx, ixs_int(ctx, 5), ixs_mul(ctx, ixs_int(ctx, 2), item))};
    const ixs_mapped_expression_row shifted_rows[4] = {
        {1, 0, 2, 0}, {0, 0, 0, 0}, {1, 2, 2, 4}, {0, 2, 0, 4}};
    budget = 6;
    result = ixs_synthesize_mapped_expression_facts(
        facts, item, shifted_expressions, 2, shifted_points, 2, shifted_rows, 4,
        &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && result.value != NULL &&
          budget == 0);
    CHECK(test_ixs_equivalent_facts(facts, (ixs_node *)result.value,
                                    (ixs_node *)shifted_expressions[0]) ==
          IXS_CHECK_TRUE);
  }

  {
    enum { SPARSE_POINTS = 64 };
    int64_t sparse_points[SPARSE_POINTS];
    ixs_mapped_expression_row sparse_rows[SPARSE_POINTS];
    const ixs_node *sparse_expressions[1] = {ixs_add(ctx, base, item)};
    for (i = 0; i < SPARSE_POINTS; i++) {
      sparse_points[i] = (int64_t)(2u * i);
      sparse_rows[i] =
          (ixs_mapped_expression_row){0, sparse_points[i], sparse_points[i], 0};
    }
    budget = 2u * SPARSE_POINTS;
    result = ixs_synthesize_mapped_expression_facts(
        facts, item, sparse_expressions, 1, sparse_points, SPARSE_POINTS,
        sparse_rows, SPARSE_POINTS, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && result.value != NULL &&
          budget == 0);
    budget = SPARSE_POINTS;
    result = ixs_verify_mapped_expression_facts(facts, item, sparse_expressions,
                                                1, sparse_rows, SPARSE_POINTS,
                                                result.value, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && budget == 0);
  }

  {
    const int64_t irregular_points[3] = {0, 1, 3};
    const ixs_node *irregular_expressions[1] = {ixs_add(ctx, base, item)};
    const ixs_mapped_expression_row irregular_rows[3] = {
        {0, 3, 3, 0}, {0, 0, 0, 0}, {0, 1, 1, 0}};
    budget = 6;
    result = ixs_synthesize_mapped_expression_facts(
        facts, item, irregular_expressions, 1, irregular_points, 3,
        irregular_rows, 3, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && result.value != NULL &&
          budget == 0);
  }

  {
    const int64_t predicate_points[2] = {0, 1};
    const ixs_node *predicate_expressions[1] = {
        ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 1))};
    const ixs_mapped_expression_row predicate_rows[2] = {{0, 1, 1, 0},
                                                         {0, 0, 0, 0}};
    budget = 4;
    result = ixs_synthesize_mapped_expression_facts(
        facts, item, predicate_expressions, 1, predicate_points, 2,
        predicate_rows, 2, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && result.value != NULL &&
          ixs_node_is_pred(result.value) && budget == 0);
    budget = 2;
    result = ixs_verify_mapped_expression_facts(
        facts, item, predicate_expressions, 1, predicate_rows, 2, result.value,
        &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && budget == 0);
  }

  {
    const ixs_node *limit = ixs_sym(ctx, "mapped_expression_limit");
    const ixs_node *predicate_expressions[1] = {
        ixs_cmp(ctx, item, IXS_CMP_LT, limit)};
    const ixs_mapped_expression_row predicate_rows[4] = {
        {0, 0, 0, 0}, {0, 2, 1, 0}, {0, 4, 2, 0}, {0, 6, 3, 0}};

    CHECK(limit && predicate_expressions[0]);
    budget = 23;
    result = ixs_synthesize_mapped_expression_facts(
        facts, item, predicate_expressions, 1, points, 4, predicate_rows, 4,
        &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_EXHAUSTED &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 7);
    budget = 24;
    result = ixs_synthesize_mapped_expression_facts(
        facts, item, predicate_expressions, 1, points, 4, predicate_rows, 4,
        &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && result.value != NULL &&
          ixs_node_is_pred(result.value) && budget == 0);
    budget = 4;
    result = ixs_verify_mapped_expression_facts(
        facts, item, predicate_expressions, 1, predicate_rows, 4, result.value,
        &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && budget == 0);
  }

  {
    const ixs_node *literal_expressions[1] = {item};
    const ixs_mapped_expression_row literal_rows[4] = {
        {0, 0, 0, 0}, {0, 1, 1, 0}, {0, 0, 2, 0}, {0, 1, 3, 0}};

    budget = 8;
    result = ixs_synthesize_mapped_expression_facts(
        facts, item, literal_expressions, 1, points, 4, literal_rows, 4,
        &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && result.value != NULL &&
          budget == 0);
    budget = 4;
    result = ixs_verify_mapped_expression_facts(
        facts, item, literal_expressions, 1, literal_rows, 4, result.value,
        &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && budget == 0);
  }

  {
    const int64_t single_point[1] = {0};
    const ixs_node *partial_values[1] = {base};
    const ixs_node *partial_conditions[1] = {
        ixs_cmp(ctx, guard, IXS_CMP_GE, ixs_int(ctx, 0))};
    const ixs_node *partial_expressions[1] = {
        ixs_pw(ctx, 1, partial_values, partial_conditions)};
    const ixs_mapped_expression_row partial_rows[1] = {{0, 0, 0, 0}};
    ixs_facts *inactive = ixs_facts_create(ctx);
    const ixs_node *partial_candidate;
    CHECK(inactive);
    CHECK(ixs_facts_assume_pred(strong, partial_conditions[0]));
    budget = 2;
    result = ixs_synthesize_mapped_expression_facts(
        weak, item, partial_expressions, 1, single_point, 1, partial_rows, 1,
        &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 0);
    budget = 2;
    result = ixs_synthesize_mapped_expression_facts(
        strong, item, partial_expressions, 1, single_point, 1, partial_rows, 1,
        &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && result.value != NULL &&
          budget == 0);
    partial_candidate = result.value;
    budget = 1;
    result = ixs_verify_mapped_expression_facts(weak, item, partial_expressions,
                                                1, partial_rows, 1,
                                                partial_candidate, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_UNKNOWN && budget == 0);
    budget = 1;
    result = ixs_verify_mapped_expression_facts(
        strong, item, partial_expressions, 1, partial_rows, 1,
        partial_candidate, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && budget == 0);
    CHECK(ixs_facts_assume_pred(inactive, ixs_not(ctx, partial_conditions[0])));
    budget = 2;
    result = ixs_synthesize_mapped_expression_facts(
        inactive, item, partial_expressions, 1, single_point, 1, partial_rows,
        1, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 0);
  }

  ixs_ctx_destroy(ctx);
}

static void test_public_mapped_bundle_facts(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *item = ixs_sym(ctx, "mapped_bundle_item");
  ixs_node *base = ixs_sym(ctx, "mapped_bundle_base");
  ixs_node *guard_value = ixs_sym(ctx, "mapped_bundle_guard");
  ixs_node *guard = ixs_cmp(ctx, guard_value, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *not_guard = ixs_not(ctx, guard);
  ixs_node *address = ixs_add(ctx, base, item);
  const ixs_node *partial_values[1] = {address};
  const ixs_node *partial_conditions[1] = {guard};
  const ixs_node *partial_expressions[1] = {
      ixs_pw(ctx, 1, partial_values, partial_conditions)};
  const ixs_node *address_expressions[1] = {address};
  const ixs_node *predicate_expressions[1] = {
      ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 1))};
  ixs_facts *common = ixs_facts_create(ctx);
  ixs_session exact_session;
  ixs_facts *strong;
  ixs_facts *opposite;
  ixs_mapped_bundle_row exact_rows[2];
  ixs_mapped_bundle_component component;
  ixs_mapped_bundle_result result;
  const ixs_node *candidates[2];
  size_t budget;

  CHECK(ctx && item && base && guard_value && guard && not_guard && address &&
        partial_expressions[0] && predicate_expressions[0] && common);
  ixs_session_init(&exact_session, ctx);
  strong = (ixs_facts_create)(&exact_session);
  opposite = (ixs_facts_create)(&exact_session);
  CHECK(strong && opposite && ixs_facts_assume_pred(strong, guard) &&
        ixs_facts_assume_pred(opposite, not_guard));

  exact_rows[0] = (ixs_mapped_bundle_row){strong, {0, 1, 1, 0}};
  exact_rows[1] = (ixs_mapped_bundle_row){strong, {0, 0, 0, 0}};
  component = (ixs_mapped_bundle_component){IXS_MAPPED_BUNDLE_SCALAR,
                                            common,
                                            item,
                                            partial_expressions,
                                            1,
                                            exact_rows,
                                            2,
                                            false,
                                            0,
                                            0};
  candidates[0] = base;
  budget = 9;
  result =
      ixs_synthesize_mapped_bundle_facts(&component, 1, candidates, 1, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_EXHAUSTED &&
        result.check == IXS_CHECK_UNKNOWN && candidates[0] == NULL &&
        budget == 1);
  budget = 10;
  result =
      ixs_synthesize_mapped_bundle_facts(&component, 1, candidates, 1, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && candidates[0] != NULL &&
        test_ixs_equivalent_facts(strong, (ixs_node *)candidates[0], address) ==
            IXS_CHECK_TRUE &&
        budget == 0);

  {
    const ixs_node *left_values[1] = {base};
    const ixs_node *right_values[1] = {ixs_add(ctx, base, ixs_int(ctx, 1))};
    const ixs_node *left_conditions[1] = {guard};
    const ixs_node *right_conditions[1] = {not_guard};
    const ixs_node *incompatible_expressions[2] = {
        ixs_pw(ctx, 1, left_values, left_conditions),
        ixs_pw(ctx, 1, right_values, right_conditions)};
    ixs_mapped_bundle_row incompatible_rows[2] = {{strong, {0, 0, 0, 0}},
                                                  {opposite, {1, 0, 0, 0}}};
    ixs_mapped_bundle_component incompatible = {IXS_MAPPED_BUNDLE_SCALAR,
                                                common,
                                                item,
                                                incompatible_expressions,
                                                2,
                                                incompatible_rows,
                                                2,
                                                false,
                                                0,
                                                0};
    CHECK(incompatible_expressions[0] && incompatible_expressions[1]);
    candidates[0] = base;
    budget = 11;
    result = ixs_synthesize_mapped_bundle_facts(&incompatible, 1, candidates, 1,
                                                &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_UNKNOWN && candidates[0] == NULL &&
          budget == 0);
  }

  {
    ixs_mapped_bundle_row scalar_rows[2] = {{common, {0, 1, 1, 0}},
                                            {common, {0, 0, 0, 0}}};
    ixs_mapped_bundle_component components[2] = {
        {IXS_MAPPED_BUNDLE_SCALAR, common, item, address_expressions, 1,
         scalar_rows, 2, false, 0, 0},
        {IXS_MAPPED_BUNDLE_PREDICATE, common, item, predicate_expressions, 1,
         scalar_rows, 2, false, 0, 0}};

    candidates[0] = base;
    candidates[1] = base;
    budget = 11;
    result = ixs_synthesize_mapped_bundle_facts(components, 2, candidates, 2,
                                                &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_EXHAUSTED &&
          result.check == IXS_CHECK_UNKNOWN && candidates[0] == NULL &&
          candidates[1] == NULL && budget == 1);
    budget = 12;
    result = ixs_synthesize_mapped_bundle_facts(components, 2, candidates, 2,
                                                &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && candidates[0] != NULL &&
          candidates[1] != NULL && ixs_node_is_pred(candidates[1]) &&
          budget == 0);

    components[1].expressions = address_expressions;
    candidates[0] = base;
    candidates[1] = base;
    budget = 10;
    result = ixs_synthesize_mapped_bundle_facts(components, 2, candidates, 2,
                                                &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_UNKNOWN && candidates[0] == NULL &&
          candidates[1] == NULL && budget == 0);
  }

  {
    ixs_node *item_lower = ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 0));
    ixs_node *item_upper = ixs_cmp(ctx, item, IXS_CMP_LE, ixs_int(ctx, 1));
    ixs_node *guard_zero =
        ixs_cmp(ctx, guard_value, IXS_CMP_EQ, ixs_int(ctx, 0));
    ixs_node *guard_positive =
        ixs_cmp(ctx, guard_value, IXS_CMP_GT, ixs_int(ctx, 0));
    const ixs_node *ranged_values[2] = {item, ixs_int(ctx, -1)};
    const ixs_node *ranged_conditions[2] = {guard, ixs_true(ctx)};
    const ixs_node *ranged_expressions[1] = {
        ixs_pw(ctx, 2, ranged_values, ranged_conditions)};
    ixs_facts *range_common = ixs_facts_create(ctx);
    ixs_facts *zero_domain = ixs_facts_create(ctx);
    ixs_facts *positive_domain = ixs_facts_create(ctx);
    ixs_mapped_bundle_row ranged_rows[2] = {{zero_domain, {0, 0, 0, 0}},
                                            {positive_domain, {0, 1, 1, 0}}};
    ixs_mapped_bundle_component ranged = {IXS_MAPPED_BUNDLE_SCALAR,
                                          range_common,
                                          item,
                                          ranged_expressions,
                                          1,
                                          ranged_rows,
                                          2,
                                          true,
                                          0,
                                          1};

    CHECK(item_lower && item_upper && guard_zero && guard_positive &&
          ranged_values[1] && ranged_expressions[0] && range_common &&
          zero_domain && positive_domain &&
          ixs_facts_assume_pred(range_common, item_lower) &&
          ixs_facts_assume_pred(range_common, item_upper) &&
          ixs_facts_assume_pred(zero_domain, item_lower) &&
          ixs_facts_assume_pred(zero_domain, item_upper) &&
          ixs_facts_assume_pred(zero_domain, guard_zero) &&
          ixs_facts_assume_pred(positive_domain, item_lower) &&
          ixs_facts_assume_pred(positive_domain, item_upper) &&
          ixs_facts_assume_pred(positive_domain, guard_positive));

    candidates[0] = base;
    budget = 9;
    result =
        ixs_synthesize_mapped_bundle_facts(&ranged, 1, candidates, 1, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_EXHAUSTED &&
          result.check == IXS_CHECK_UNKNOWN && candidates[0] == NULL &&
          budget == 0);
    budget = 10;
    result =
        ixs_synthesize_mapped_bundle_facts(&ranged, 1, candidates, 1, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && candidates[0] != NULL &&
          test_ixs_equivalent_facts(range_common, (ixs_node *)candidates[0],
                                    item) == IXS_CHECK_TRUE &&
          budget == 0);
  }

  ixs_session_destroy(&exact_session);
  ixs_ctx_destroy(ctx);
}

static void test_public_mapped_bundle_failures(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *item = ixs_sym(ctx, "mapped_bundle_failure_item");
  ixs_node *base = ixs_sym(ctx, "mapped_bundle_failure_base");
  ixs_node *foreign = ixs_sym(other, "mapped_bundle_failure_foreign");
  const ixs_node *expressions[1] = {ixs_add(ctx, base, item)};
  const ixs_node *foreign_expressions[1] = {foreign};
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *foreign_facts = ixs_facts_create(other);
  ixs_session stale_session;
  ixs_facts *stale;
  ixs_mapped_bundle_row rows[1] = {{facts, {0, 0, 0, 0}}};
  ixs_mapped_bundle_component component = {IXS_MAPPED_BUNDLE_SCALAR,
                                           facts,
                                           item,
                                           expressions,
                                           1,
                                           rows,
                                           1,
                                           false,
                                           0,
                                           0};
  ixs_mapped_bundle_result result;
  const ixs_node *candidate = base;
  size_t budget;

  CHECK(ctx && other && item && base && foreign && expressions[0] && facts &&
        foreign_facts);
  ixs_session_init(&stale_session, ctx);
  stale = (ixs_facts_create)(&stale_session);
  CHECK(stale != NULL);
  ixs_session_reset(&stale_session);

  budget = 3;
  result =
      ixs_synthesize_mapped_bundle_facts(&component, 1, &candidate, 0, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
        result.check == IXS_CHECK_UNKNOWN && budget == 3);

  component.rows = (const ixs_mapped_bundle_row *)(uintptr_t)1;
  candidate = base;
  budget = 1;
  result =
      ixs_synthesize_mapped_bundle_facts(&component, 1, &candidate, 1, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_EXHAUSTED &&
        result.check == IXS_CHECK_UNKNOWN && candidate == NULL && budget == 1);
  component.rows = rows;
  budget = 3;

  rows[0].relation.expression_index = 1;
  candidate = base;
  result =
      ixs_synthesize_mapped_bundle_facts(&component, 1, &candidate, 1, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
        result.check == IXS_CHECK_UNKNOWN && candidate == NULL && budget == 3);
  rows[0].relation.expression_index = 0;

  component.kind = (ixs_mapped_bundle_component_kind)99;
  candidate = base;
  result =
      ixs_synthesize_mapped_bundle_facts(&component, 1, &candidate, 1, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
        result.check == IXS_CHECK_UNKNOWN && candidate == NULL && budget == 3);
  component.kind = IXS_MAPPED_BUNDLE_SCALAR;

  component.has_candidate_range = true;
  component.candidate_lower = 1;
  component.candidate_upper = 0;
  candidate = base;
  result =
      ixs_synthesize_mapped_bundle_facts(&component, 1, &candidate, 1, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
        result.check == IXS_CHECK_UNKNOWN && candidate == NULL && budget == 3);
  component.candidate_lower = 0;
  component.candidate_upper = 1;
  component.kind = IXS_MAPPED_BUNDLE_PREDICATE;
  candidate = base;
  result =
      ixs_synthesize_mapped_bundle_facts(&component, 1, &candidate, 1, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
        result.check == IXS_CHECK_UNKNOWN && candidate == NULL && budget == 3);
  component.kind = IXS_MAPPED_BUNDLE_SCALAR;
  component.has_candidate_range = false;

  component.expressions = foreign_expressions;
  candidate = base;
  result =
      ixs_synthesize_mapped_bundle_facts(&component, 1, &candidate, 1, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
        result.check == IXS_CHECK_UNKNOWN && candidate == NULL && budget == 3);
  component.expressions = expressions;

  candidate = base;
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  result =
      ixs_synthesize_mapped_bundle_facts(&component, 1, &candidate, 1, &budget);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(result.status == IXS_FINITE_DOMAIN_OOM &&
        result.check == IXS_CHECK_UNKNOWN && candidate == NULL && budget == 3);

  rows[0].facts = foreign_facts;
  candidate = base;
  result =
      ixs_synthesize_mapped_bundle_facts(&component, 1, &candidate, 1, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
        result.check == IXS_CHECK_UNKNOWN && candidate == NULL && budget == 3);
  rows[0].facts = stale;
  candidate = base;
  result =
      ixs_synthesize_mapped_bundle_facts(&component, 1, &candidate, 1, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
        result.check == IXS_CHECK_UNKNOWN && candidate == NULL && budget == 3);

  ixs_session_destroy(&stale_session);
  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_public_mapped_expression_failures(void) {
  const int64_t points[2] = {0, 1};
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *item = ixs_sym(ctx, "mapped_failure_item");
  ixs_node *base = ixs_sym(ctx, "mapped_failure_base");
  const ixs_node *expressions[1] = {ixs_add(ctx, base, item)};
  const ixs_mapped_expression_row rows[2] = {{0, 1, 1, 0}, {0, 0, 0, 0}};
  ixs_mapped_expression_row malformed_rows[2];
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_finite_domain_result result;
  const ixs_node *candidate;
  size_t budget;

  CHECK(ctx && other && item && base && expressions[0] && facts);
  budget = 4;
  result = ixs_synthesize_mapped_expression_facts(facts, item, expressions, 1,
                                                  points, 2, rows, 2, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value != NULL && budget == 0);
  candidate = result.value;

  memcpy(malformed_rows, rows, sizeof(rows));
  malformed_rows[0].expression_index = 1;
  budget = 4;
  result = ixs_synthesize_mapped_expression_facts(
      facts, item, expressions, 1, points, 2, malformed_rows, 2, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
        budget == 4);
  budget = 2;
  result = ixs_verify_mapped_expression_facts(
      facts, item, expressions, 1, malformed_rows, 2, candidate, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
        budget == 2);

  {
    const ixs_mapped_expression_row missing[1] = {{0, 0, 0, 0}};
    budget = 4;
    result = ixs_synthesize_mapped_expression_facts(
        facts, item, expressions, 1, points, 2, missing, 1, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 4);
  }

  {
    const ixs_mapped_expression_row duplicate_missing[2] = {{0, 0, 0, 0},
                                                            {0, 1, 0, 0}};
    budget = 4;
    result = ixs_synthesize_mapped_expression_facts(
        facts, item, expressions, 1, points, 2, duplicate_missing, 2, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 4);
  }

  {
    const int64_t duplicate_points[2] = {0, 0};
    budget = 4;
    result = ixs_synthesize_mapped_expression_facts(
        facts, item, expressions, 1, duplicate_points, 2, rows, 2, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 4);
  }

  {
    const ixs_node *foreign_expressions[1] = {
        ixs_sym(other, "mapped_failure_foreign")};
    budget = 4;
    result = ixs_synthesize_mapped_expression_facts(
        facts, item, foreign_expressions, 1, points, 2, rows, 2, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 4);
    budget = 2;
    result = ixs_verify_mapped_expression_facts(
        facts, item, expressions, 1, rows, 2, foreign_expressions[0], &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 2);
  }

  {
    const ixs_node *const *hostile_expressions =
        (const ixs_node *const *)(uintptr_t)1;
    const int64_t *hostile_points = (const int64_t *)(uintptr_t)1;
    const ixs_mapped_expression_row *hostile_rows =
        (const ixs_mapped_expression_row *)(uintptr_t)1;
    budget = 1;
    result = ixs_synthesize_mapped_expression_facts(
        facts, item, hostile_expressions, 1, hostile_points, 1, hostile_rows, 1,
        &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_EXHAUSTED &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 1);
    budget = 0;
    result =
        ixs_verify_mapped_expression_facts(facts, item, hostile_expressions, 1,
                                           hostile_rows, 1, candidate, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_EXHAUSTED &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 0);

    budget = SIZE_MAX;
    result = ixs_synthesize_mapped_expression_facts(
        facts, item, hostile_expressions, SIZE_MAX, hostile_points, 1,
        hostile_rows, 1, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == SIZE_MAX);
    budget = SIZE_MAX;
    result = ixs_synthesize_mapped_expression_facts(
        facts, item, hostile_expressions, 1, hostile_points, SIZE_MAX / 2u + 1u,
        hostile_rows, 1, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == SIZE_MAX);
  }

  budget = 4;
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  result = ixs_synthesize_mapped_expression_facts(facts, item, expressions, 1,
                                                  points, 2, rows, 2, &budget);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(result.status == IXS_FINITE_DOMAIN_OOM &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
        budget == 4);
  budget = 4;
  result = ixs_synthesize_mapped_expression_facts(facts, item, expressions, 1,
                                                  points, 2, rows, 2, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value != NULL && budget == 0);

  budget = 2;
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  result = ixs_verify_mapped_expression_facts(facts, item, expressions, 1, rows,
                                              2, candidate, &budget);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(result.status == IXS_FINITE_DOMAIN_OOM &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
        budget == 0);
  budget = 2;
  result = ixs_verify_mapped_expression_facts(facts, item, expressions, 1, rows,
                                              2, candidate, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value == NULL && budget == 0);

  budget = 4;
  result = ixs_synthesize_mapped_expression_facts(facts, item, expressions, 1,
                                                  points, 2, rows, 2, NULL);
  CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
        budget == 4);

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_public_mapped_constant_differences(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *item = ixs_sym(ctx, "mapped_difference_item");
  ixs_node *base = ixs_sym(ctx, "mapped_difference_base");
  ixs_node *other_base = ixs_sym(ctx, "mapped_difference_other_base");
  ixs_node *guard = ixs_sym(ctx, "mapped_difference_guard");
  ixs_node *scaled = ixs_mul(ctx, ixs_int(ctx, 4), item);
  const ixs_node *partial_values[1] = {base};
  const ixs_node *partial_conditions[1] = {
      ixs_cmp(ctx, guard, IXS_CMP_GE, ixs_int(ctx, 0))};
  const ixs_node *expressions[6] = {
      ixs_add(ctx, ixs_add(ctx, base, scaled), ixs_int(ctx, 7)),
      ixs_add(ctx, ixs_add(ctx, base, scaled), ixs_int(ctx, -3)),
      ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 1)),
      ixs_pw(ctx, 1, partial_values, partial_conditions),
      base,
      other_base};
  const ixs_mapped_difference_row rows[4] = {
      {0, 2, 1, 0}, {2, 0, 2, 1}, {0, 2, 1, 0}, {1, 1, 0, 3}};
  const int64_t expected[4] = {18, -1, 18, -18};
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *strong = ixs_facts_create(ctx);
  ixs_finite_domain_result result;
  int64_t differences[4] = {101, 102, 103, 104};
  size_t budget;

  CHECK(ctx && other && item && base && other_base && guard && scaled &&
        expressions[0] && expressions[1] && expressions[2] && expressions[3] &&
        facts && strong);
  budget = 3;
  result = ixs_mapped_constant_differences_facts(facts, item, expressions, 6,
                                                 rows, 4, differences, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_EXHAUSTED &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
        budget == 3 && differences[0] == 101 && differences[1] == 102 &&
        differences[2] == 103 && differences[3] == 104);

  budget = 4;
  result = ixs_mapped_constant_differences_facts(facts, item, expressions, 6,
                                                 rows, 4, differences, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value == NULL && budget == 0 &&
        memcmp(differences, expected, sizeof(expected)) == 0);

  {
    const ixs_mapped_difference_row atomic_rows[2] = {{0, 2, 1, 0},
                                                      {4, 0, 5, 0}};
    differences[0] = 201;
    differences[1] = 202;
    budget = 2;
    result = ixs_mapped_constant_differences_facts(
        facts, item, expressions, 6, atomic_rows, 2, differences, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 0 && differences[0] == 201 && differences[1] == 202);
  }

  {
    const ixs_mapped_difference_row partial_row[1] = {{3, 0, 4, 0}};
    differences[0] = 301;
    budget = 1;
    result = ixs_mapped_constant_differences_facts(
        facts, item, expressions, 6, partial_row, 1, differences, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 0 && differences[0] == 301);
    CHECK(ixs_facts_assume_pred(strong, partial_conditions[0]));
    budget = 1;
    result = ixs_mapped_constant_differences_facts(
        strong, item, expressions, 6, partial_row, 1, differences, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && result.value == NULL &&
          budget == 0 && differences[0] == 0);
  }

  {
    ixs_mapped_difference_row invalid_row = {6, 0, 0, 0};
    differences[0] = 401;
    budget = 1;
    result = ixs_mapped_constant_differences_facts(
        facts, item, expressions, 6, &invalid_row, 1, differences, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 1 && differences[0] == 401);
  }

  {
    const ixs_node *foreign_expressions[1] = {
        ixs_sym(other, "mapped_difference_foreign")};
    const ixs_mapped_difference_row single_row = {0, 0, 0, 0};
    differences[0] = 501;
    budget = 1;
    result = ixs_mapped_constant_differences_facts(
        facts, item, foreign_expressions, 1, &single_row, 1, differences,
        &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 1 && differences[0] == 501);
  }

  {
    const ixs_node *const *hostile_expressions =
        (const ixs_node *const *)(uintptr_t)1;
    const ixs_mapped_difference_row *hostile_rows =
        (const ixs_mapped_difference_row *)(uintptr_t)1;
    int64_t *hostile_output = (int64_t *)(uintptr_t)1;
    budget = 0;
    result = ixs_mapped_constant_differences_facts(
        facts, item, hostile_expressions, 1, hostile_rows, 1, hostile_output,
        &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_EXHAUSTED &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 0);
    budget = SIZE_MAX;
    result = ixs_mapped_constant_differences_facts(
        facts, item, hostile_expressions, SIZE_MAX, hostile_rows, 1,
        hostile_output, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == SIZE_MAX);
  }

  differences[0] = 601;
  budget = 1;
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  result = ixs_mapped_constant_differences_facts(facts, item, expressions, 6,
                                                 rows, 1, differences, &budget);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(result.status == IXS_FINITE_DOMAIN_OOM &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
        budget == 0 && differences[0] == 601);
  budget = 1;
  result = ixs_mapped_constant_differences_facts(facts, item, expressions, 6,
                                                 rows, 1, differences, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value == NULL && budget == 0 &&
        differences[0] == 18);

  budget = 1;
  result = ixs_mapped_constant_differences_facts(facts, item, expressions, 6,
                                                 rows, 1, NULL, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
        budget == 1);
  result = ixs_mapped_constant_differences_facts(facts, item, expressions, 6,
                                                 rows, 1, differences, NULL);
  CHECK(result.status == IXS_FINITE_DOMAIN_INVALID &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL);

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_public_finite_domain_batch(void) {
  const int64_t block_points[2] = {0, 1};
  const int64_t item_points[2] = {2, 4};
  const int64_t slot_points[2] = {5, 6};
  const int64_t unordered_points[2] = {1, 1};
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *block = ixs_sym(ctx, "finite_batch_block");
  ixs_node *item = ixs_sym(ctx, "finite_batch_item");
  ixs_node *slot = ixs_sym(ctx, "finite_batch_slot");
  ixs_node *unknown = ixs_sym(ctx, "finite_batch_unknown");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *five = ixs_int(ctx, 5);
  ixs_node *two = ixs_int(ctx, 2);
  ixs_node *partial = ixs_div(ctx, one, ixs_sub(ctx, slot, five));
  ixs_node *query_partial = ixs_div(ctx, one, unknown);
  ixs_node *fraction = ixs_div(ctx, block, two);
  ixs_node *true_pred = ixs_cmp(ctx, block, IXS_CMP_GE, zero);
  ixs_node *slot_is_five = ixs_cmp(ctx, slot, IXS_CMP_EQ, five);
  ixs_node *unknown_pred = ixs_cmp(ctx, unknown, IXS_CMP_EQ, zero);
  ixs_node *late_false =
      ixs_and(ctx, unknown_pred, ixs_cmp(ctx, block, IXS_CMP_EQ, zero));
  ixs_facts *facts = ixs_facts_create(ctx);
  const ixs_node *false_predicate[1] = {ixs_false(ctx)};
  ixs_facts *contradictory_facts =
      ixs_facts_create_preds(IXS_TEST_SESSION(ctx), false_predicate, 1);
  ixs_finite_integer_domain domains[3];
  ixs_finite_domain_batch_query queries[7];
  ixs_finite_domain_batch_result results[7];
  ixs_finite_domain_status status;
  size_t budget;

  CHECK(ctx && other && block && item && slot && unknown && zero && one &&
        five && two && partial && query_partial && fraction && true_pred &&
        slot_is_five && unknown_pred && late_false && facts &&
        contradictory_facts);
  domains[0] = (ixs_finite_integer_domain){block, block_points, 2};
  domains[1] = (ixs_finite_integer_domain){item, item_points, 2};
  domains[2] = (ixs_finite_integer_domain){slot, slot_points, 2};
  queries[0] = (ixs_finite_domain_batch_query){IXS_FINITE_DOMAIN_PREDICATE_TRUE,
                                               true_pred};
  queries[1] = (ixs_finite_domain_batch_query){IXS_FINITE_DOMAIN_PREDICATE_TRUE,
                                               slot_is_five};
  queries[2] = (ixs_finite_domain_batch_query){IXS_FINITE_DOMAIN_PREDICATE_TRUE,
                                               unknown_pred};
  queries[3] =
      (ixs_finite_domain_batch_query){IXS_FINITE_DOMAIN_DEFINED, partial};
  queries[4] = (ixs_finite_domain_batch_query){IXS_FINITE_DOMAIN_INTEGER_VALUED,
                                               fraction};
  queries[5] =
      (ixs_finite_domain_batch_query){IXS_FINITE_DOMAIN_DEFINED, fraction};
  queries[6] = (ixs_finite_domain_batch_query){IXS_FINITE_DOMAIN_PREDICATE_TRUE,
                                               late_false};

  budget = 55;
  status = ixs_finite_domain_batch_facts(facts, domains, 3, queries, 7, results,
                                         &budget);
  CHECK(status == IXS_FINITE_DOMAIN_EXHAUSTED && budget == 55);
  for (size_t query = 0; query < 7; query++)
    CHECK(results[query].check == IXS_CHECK_UNKNOWN &&
          results[query].witness == SIZE_MAX);

  results[0].check = IXS_CHECK_TRUE;
  results[0].witness = 0;
  budget = 1;
  status = ixs_finite_domain_batch_facts(facts, domains, 0, queries, 1, results,
                                         &budget);
  CHECK(status == IXS_FINITE_DOMAIN_INVALID && budget == 1);
  CHECK(results[0].check == IXS_CHECK_UNKNOWN &&
        results[0].witness == SIZE_MAX);
  results[0].check = IXS_CHECK_TRUE;
  results[0].witness = 0;
  budget = 0;
  status = ixs_finite_domain_batch_facts(contradictory_facts, domains, 0,
                                         queries, 1, results, &budget);
  CHECK(status == IXS_FINITE_DOMAIN_INVALID && budget == 0);
  CHECK(results[0].check == IXS_CHECK_UNKNOWN &&
        results[0].witness == SIZE_MAX);

  budget = 56;
  status = ixs_finite_domain_batch_facts(facts, domains, 3, queries, 7, results,
                                         &budget);
  CHECK(status == IXS_FINITE_DOMAIN_COMPLETE && budget == 0);
  CHECK(results[0].check == IXS_CHECK_TRUE && results[0].witness == SIZE_MAX);
  CHECK(results[1].check == IXS_CHECK_FALSE && results[1].witness == 1);
  CHECK(results[2].check == IXS_CHECK_UNKNOWN && results[2].witness == 0);
  CHECK(results[3].check != IXS_CHECK_TRUE && results[3].witness == 0);
  CHECK(results[4].check == IXS_CHECK_FALSE && results[4].witness == 4);
  CHECK(results[5].check == IXS_CHECK_TRUE && results[5].witness == SIZE_MAX);
  CHECK(results[6].check == IXS_CHECK_FALSE && results[6].witness == 0);

  {
    const int64_t partial_points[2] = {0, 1};
    ixs_node *partial_values[1] = {one};
    ixs_node *partial_conditions[1] = {ixs_cmp(ctx, slot, IXS_CMP_EQ, zero)};
    ixs_node *partial_piecewise =
        ixs_pw(ctx, 1, partial_values, partial_conditions);
    ixs_node *partial_mod = ixs_mod(ctx, slot, slot);
    ixs_node *partial_negative_mod = ixs_mod(ctx, slot, ixs_neg(ctx, slot));
    ixs_node *half = ixs_div(ctx, slot, two);
    ixs_node *partial_xor = ixs_xor(ctx, half, one);
    ixs_node *partial_and = ixs_and(ctx, half, one);
    ixs_node *partial_or = ixs_or(ctx, half, one);
    ixs_node *guarded_values[2] = {partial_mod, zero};
    ixs_node *guarded_conditions[2] = {ixs_cmp(ctx, slot, IXS_CMP_NE, zero),
                                       ixs_true(ctx)};
    ixs_node *guarded_mod = ixs_pw(ctx, 2, guarded_values, guarded_conditions);
    ixs_node *nested_predicate =
        ixs_cmp(ctx, ixs_add(ctx, partial_xor, one), IXS_CMP_EQ, two);
    ixs_finite_integer_domain partial_domain = {slot, partial_points, 2};
    ixs_finite_domain_batch_query partial_queries[9] = {
        {IXS_FINITE_DOMAIN_DEFINED, partial_piecewise},
        {IXS_FINITE_DOMAIN_INTEGER_VALUED, partial_piecewise},
        {IXS_FINITE_DOMAIN_PREDICATE_TRUE, nested_predicate},
        {IXS_FINITE_DOMAIN_DEFINED, partial_mod},
        {IXS_FINITE_DOMAIN_DEFINED, partial_negative_mod},
        {IXS_FINITE_DOMAIN_DEFINED, partial_xor},
        {IXS_FINITE_DOMAIN_DEFINED, partial_and},
        {IXS_FINITE_DOMAIN_DEFINED, partial_or},
        {IXS_FINITE_DOMAIN_DEFINED, guarded_mod}};
    ixs_finite_domain_batch_result partial_results[9];
    size_t errors = ixs_ctx_nerrors(ctx);

    CHECK(partial_piecewise && partial_mod && partial_negative_mod && half &&
          partial_xor && partial_and && partial_or && guarded_mod &&
          nested_predicate);
    budget = 18;
    status = ixs_finite_domain_batch_facts(facts, &partial_domain, 1,
                                           partial_queries, 9, partial_results,
                                           &budget);
    CHECK(status == IXS_FINITE_DOMAIN_COMPLETE && budget == 0);
    for (size_t query = 0; query < 8; query++)
      CHECK(partial_results[query].check == IXS_CHECK_FALSE);
    CHECK(partial_results[0].witness == 1 && partial_results[1].witness == 1 &&
          partial_results[2].witness == 1 && partial_results[3].witness == 0 &&
          partial_results[4].witness == 0 && partial_results[5].witness == 1 &&
          partial_results[6].witness == 1 && partial_results[7].witness == 1);
    CHECK(partial_results[8].check == IXS_CHECK_TRUE &&
          partial_results[8].witness == SIZE_MAX);
    CHECK(ixs_ctx_nerrors(ctx) == errors);
  }

  {
    const int64_t overflow_points[1] = {1};
    ixs_node *overflow = ixs_add(ctx, slot, ixs_int(ctx, INT64_MAX));
    ixs_finite_integer_domain overflow_domain = {slot, overflow_points, 1};
    ixs_finite_domain_batch_query overflow_query = {IXS_FINITE_DOMAIN_DEFINED,
                                                    overflow};
    ixs_finite_domain_batch_result overflow_result;

    CHECK(overflow);
    ixs_ctx_clear_errors(ctx);
    budget = 1;
    status = ixs_finite_domain_batch_facts(facts, &overflow_domain, 1,
                                           &overflow_query, 1, &overflow_result,
                                           &budget);
    CHECK(status == IXS_FINITE_DOMAIN_INVALID && budget == 0);
    CHECK(overflow_result.check == IXS_CHECK_UNKNOWN &&
          overflow_result.witness == SIZE_MAX);
    CHECK(ixs_ctx_nerrors(ctx) == 1 &&
          strstr(ixs_ctx_error(ctx, 0), "rational overflow in add") != NULL);
    ixs_ctx_clear_errors(ctx);
  }

  for (size_t query = 0; query < 7; query++) {
    results[query].check = IXS_CHECK_TRUE;
    results[query].witness = 0;
  }
  budget = 0;
  status = ixs_finite_domain_batch_facts(contradictory_facts, domains, 3,
                                         queries, 7, results, &budget);
  CHECK(status == IXS_FINITE_DOMAIN_COMPLETE && budget == 0);
  for (size_t query = 0; query < 7; query++)
    CHECK(results[query].check == IXS_CHECK_UNKNOWN &&
          results[query].witness == SIZE_MAX);

  {
    ixs_finite_integer_domain bad_domains[3] = {domains[0], domains[1],
                                                domains[2]};
    bad_domains[2].points = unordered_points;
    results[0].check = IXS_CHECK_TRUE;
    results[0].witness = 0;
    budget = 56;
    ixs_ctx_clear_errors(ctx);
    status = ixs_finite_domain_batch_facts(facts, bad_domains, 3, queries, 7,
                                           results, &budget);
    CHECK(status == IXS_FINITE_DOMAIN_INVALID && budget == 56);
    CHECK(results[0].check == IXS_CHECK_UNKNOWN &&
          results[0].witness == SIZE_MAX);
    CHECK(ixs_ctx_nerrors(ctx) == 1 &&
          strstr(ixs_ctx_error(ctx, 0), "points are not ordered") != NULL);

    bad_domains[1] = domains[0];
    bad_domains[2] = domains[2];
    budget = 56;
    ixs_ctx_clear_errors(ctx);
    status = ixs_finite_domain_batch_facts(facts, bad_domains, 3, queries, 7,
                                           results, &budget);
    CHECK(status == IXS_FINITE_DOMAIN_INVALID && budget == 56);
    CHECK(ixs_ctx_nerrors(ctx) == 1 &&
          strstr(ixs_ctx_error(ctx, 0), "not distinct") != NULL);
  }

  {
    ixs_finite_domain_batch_query bad = {IXS_FINITE_DOMAIN_PREDICATE_TRUE,
                                         block};
    budget = 8;
    ixs_ctx_clear_errors(ctx);
    status = ixs_finite_domain_batch_facts(facts, domains, 3, &bad, 1, results,
                                           &budget);
    CHECK(status == IXS_FINITE_DOMAIN_INVALID && budget == 8);
    CHECK(ixs_ctx_nerrors(ctx) == 1 &&
          strstr(ixs_ctx_error(ctx, 0), "kind mismatch") != NULL);

    bad.kind = (ixs_finite_domain_batch_query_kind)99;
    budget = 8;
    ixs_ctx_clear_errors(ctx);
    status = ixs_finite_domain_batch_facts(facts, domains, 3, &bad, 1, results,
                                           &budget);
    CHECK(status == IXS_FINITE_DOMAIN_INVALID && budget == 8);
    CHECK(ixs_ctx_nerrors(ctx) == 1 &&
          strstr(ixs_ctx_error(ctx, 0), "invalid query kind") != NULL);

    bad.kind = IXS_FINITE_DOMAIN_DEFINED;
    bad.value = ixs_sym(other, "finite_batch_foreign");
    budget = 8;
    ixs_ctx_clear_errors(ctx);
    status = ixs_finite_domain_batch_facts(facts, domains, 3, &bad, 1, results,
                                           &budget);
    CHECK(status == IXS_FINITE_DOMAIN_INVALID && budget == 8);
    CHECK(ixs_ctx_nerrors(ctx) == 1 &&
          strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  }

  {
    const int64_t points[2] = {0, 1};
    ixs_node *values[2] = {slot_is_five, unknown_pred};
    ixs_node *conditions[2] = {ixs_cmp(ctx, block, IXS_CMP_EQ, zero),
                               ixs_true(ctx)};
    ixs_node *predicate_piecewise = ixs_pw(ctx, 2, values, conditions);
    ixs_finite_integer_domain domain = {block, points, 2};
    ixs_finite_domain_batch_query predicate_queries[2] = {
        {IXS_FINITE_DOMAIN_DEFINED, predicate_piecewise},
        {IXS_FINITE_DOMAIN_INTEGER_VALUED, predicate_piecewise}};
    CHECK(predicate_piecewise &&
          ixs_node_tag(predicate_piecewise) == IXS_PIECEWISE &&
          ixs_node_is_pred_kind(predicate_piecewise));
    budget = 4;
    status = ixs_finite_domain_batch_facts(facts, &domain, 1, predicate_queries,
                                           2, results, &budget);
    CHECK(status == IXS_FINITE_DOMAIN_COMPLETE && budget == 0);
    CHECK(results[0].check == IXS_CHECK_TRUE && results[0].witness == SIZE_MAX);
    CHECK(results[1].check == IXS_CHECK_TRUE && results[1].witness == SIZE_MAX);
  }

  {
    const int64_t point[1] = {0};
    ixs_node *deep = ixs_rat(ctx, 1, 2);
    ixs_finite_integer_domain domain = {block, point, 1};
    ixs_finite_domain_batch_query query;
    unsigned depth;
    for (depth = 0; depth < 40u; depth++) {
      char name[64];
      ixs_pwcase cases[2];
      snprintf(name, sizeof(name), "finite_batch_limit_%u", depth);
      cases[0].value = deep;
      cases[0].cond = ixs_cmp(ctx, ixs_sym(ctx, name), IXS_CMP_GT, zero);
      cases[1].value = ixs_rat(ctx, (int64_t)(2u * depth + 3u), 2);
      cases[1].cond = ixs_true(ctx);
      deep = ixs_node_pw(ctx, 2, cases);
      CHECK(deep != NULL);
    }
    CHECK(ixs_node_contains_nested_piecewise(deep));
    query =
        (ixs_finite_domain_batch_query){IXS_FINITE_DOMAIN_INTEGER_VALUED, deep};
    results[0].check = IXS_CHECK_TRUE;
    results[0].witness = 0;
    budget = 1;
    status = ixs_finite_domain_batch_facts(facts, &domain, 1, &query, 1,
                                           results, &budget);
    CHECK(status == IXS_FINITE_DOMAIN_COMPLETE && budget == 0);
    CHECK(results[0].check == IXS_CHECK_UNKNOWN && results[0].witness == 0 &&
          !facts->bounds.oom);
  }

  {
    ixs_finite_integer_domain hostile[2];
    ixs_finite_domain_batch_query query = {IXS_FINITE_DOMAIN_PREDICATE_TRUE,
                                           true_pred};
    hostile[0] = (ixs_finite_integer_domain){
        block, (const int64_t *)(uintptr_t)1, SIZE_MAX};
    hostile[1] =
        (ixs_finite_integer_domain){item, (const int64_t *)(uintptr_t)1, 2};
    budget = SIZE_MAX;
    ixs_ctx_clear_errors(ctx);
    status = ixs_finite_domain_batch_facts(facts, hostile, 2, &query, 1,
                                           results, &budget);
    CHECK(status == IXS_FINITE_DOMAIN_INVALID && budget == SIZE_MAX);

    hostile[0].npoints = SIZE_MAX / 2 + 1;
    hostile[1].npoints = 2;
    budget = SIZE_MAX;
    ixs_ctx_clear_errors(ctx);
    status = ixs_finite_domain_batch_facts(facts, hostile, 2, &query, 1,
                                           results, &budget);
    CHECK(status == IXS_FINITE_DOMAIN_INVALID && budget == SIZE_MAX);
  }

  ixs_ctx_clear_errors(ctx);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  budget = 56;
  status = ixs_finite_domain_batch_facts(facts, domains, 3, queries, 7, results,
                                         &budget);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(status == IXS_FINITE_DOMAIN_OOM && budget == 0);
  for (size_t query = 0; query < 7; query++)
    CHECK(results[query].check == IXS_CHECK_UNKNOWN &&
          results[query].witness == SIZE_MAX);
  budget = 56;
  status = ixs_finite_domain_batch_facts(facts, domains, 3, queries, 7, results,
                                         &budget);
  CHECK(status == IXS_FINITE_DOMAIN_COMPLETE && budget == 0 &&
        results[0].check == IXS_CHECK_TRUE);

  {
    const int64_t point[1] = {0};
    ixs_finite_integer_domain domain = {block, point, 1};
    ixs_finite_domain_batch_query query = {IXS_FINITE_DOMAIN_DEFINED,
                                           query_partial};
    results[0].check = IXS_CHECK_TRUE;
    results[0].witness = 0;
    budget = 1;
    ixs_arena_set_fail_after(ixs_test_scratch(ctx), 2);
    status = ixs_finite_domain_batch_facts(facts, &domain, 1, &query, 1,
                                           results, &budget);
    ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
    CHECK(status == IXS_FINITE_DOMAIN_OOM && budget == 0);
    CHECK(results[0].check == IXS_CHECK_UNKNOWN &&
          results[0].witness == SIZE_MAX);
    budget = 1;
    status = ixs_finite_domain_batch_facts(facts, &domain, 1, &query, 1,
                                           results, &budget);
    CHECK(status == IXS_FINITE_DOMAIN_COMPLETE && budget == 0);
  }

  {
    const int64_t point[1] = {101};
    ixs_node *replacement_symbol = ixs_sym(ctx, "finite_batch_replacement_oom");
    ixs_node *replacement_predicate =
        ixs_cmp(ctx, replacement_symbol, IXS_CMP_GE, zero);
    ixs_finite_integer_domain domain = {replacement_symbol, point, 1};
    ixs_finite_domain_batch_query query = {IXS_FINITE_DOMAIN_PREDICATE_TRUE,
                                           replacement_predicate};
    CHECK(replacement_symbol && replacement_predicate);
    results[0].check = IXS_CHECK_TRUE;
    results[0].witness = 0;
    budget = 1;
    ixs_arena_set_fail_after(&ctx->arena, 0);
    status = ixs_finite_domain_batch_facts(facts, &domain, 1, &query, 1,
                                           results, &budget);
    ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
    CHECK(status == IXS_FINITE_DOMAIN_OOM && budget == 0);
    CHECK(results[0].check == IXS_CHECK_UNKNOWN &&
          results[0].witness == SIZE_MAX);
    budget = 1;
    status = ixs_finite_domain_batch_facts(facts, &domain, 1, &query, 1,
                                           results, &budget);
    CHECK(status == IXS_FINITE_DOMAIN_COMPLETE && budget == 0 &&
          results[0].check == IXS_CHECK_TRUE);
  }

  {
    const int64_t point[1] = {103};
    ixs_node *substitution_symbol =
        ixs_sym(ctx, "finite_batch_substitution_oom");
    ixs_node *replacement = ixs_int(ctx, point[0]);
    ixs_node *substitution_value = ixs_add(ctx, substitution_symbol, unknown);
    ixs_finite_integer_domain domain = {substitution_symbol, point, 1};
    ixs_finite_domain_batch_query query = {IXS_FINITE_DOMAIN_DEFINED,
                                           substitution_value};
    CHECK(substitution_symbol && replacement && substitution_value);
    results[0].check = IXS_CHECK_TRUE;
    results[0].witness = 0;
    budget = 1;
    ixs_arena_set_fail_after(&ctx->arena, 0);
    status = ixs_finite_domain_batch_facts(facts, &domain, 1, &query, 1,
                                           results, &budget);
    ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
    CHECK(status == IXS_FINITE_DOMAIN_OOM && budget == 0);
    CHECK(results[0].check == IXS_CHECK_UNKNOWN &&
          results[0].witness == SIZE_MAX);
    budget = 1;
    status = ixs_finite_domain_batch_facts(facts, &domain, 1, &query, 1,
                                           results, &budget);
    CHECK(status == IXS_FINITE_DOMAIN_COMPLETE && budget == 0 &&
          results[0].check == IXS_CHECK_TRUE);
  }

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_public_finite_domain_query_hold_oom_retry(void) {
  {
    ixs_ctx *ctx = ixs_ctx_create();
    ixs_facts *facts = ixs_facts_create(ctx);
    ixs_node *nested = make_nested_query_root(ctx, "finite_hold_equivalence");
    ixs_finite_domain_result result;
    size_t budget = 0;
    CHECK(ctx && facts && nested && ctx->bounds_query_state == NULL &&
          !facts->bounds.oom);
    ixs_arena_set_fail_after(&ctx->arena, 0);
    result = finite_domain_equivalent(facts, nested, nested, &budget);
    ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
    CHECK(result.status == IXS_FINITE_DOMAIN_OOM &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 0 && !facts->bounds.oom &&
          facts->bounds.query_tracking_depth == 0);
    result = finite_domain_equivalent(facts, nested, nested, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && result.value == NULL &&
          budget == 0);
    check_nested_query_tracking_clean(ctx, facts);
    ixs_ctx_destroy(ctx);
  }

  {
    const int64_t points[1] = {0};
    ixs_ctx *ctx = ixs_ctx_create();
    ixs_facts *facts = ixs_facts_create(ctx);
    ixs_node *item = ixs_sym(ctx, "finite_hold_relation_item");
    ixs_node *nested = make_nested_query_root(ctx, "finite_hold_relation");
    ixs_node *values[1] = {nested};
    ixs_finite_domain_query query;
    ixs_finite_domain_result result;
    size_t budget = 1;
    query.kind = IXS_FINITE_DOMAIN_EXPR_RELATION;
    query.as.relation =
        (ixs_finite_domain_relation_query){item, points, values, 1, nested};
    CHECK(ctx && facts && item && nested && ctx->bounds_query_state == NULL &&
          !facts->bounds.oom);
    ixs_arena_set_fail_after(&ctx->arena, 0);
    result = ixs_finite_domain_facts(facts, &query, &budget);
    ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
    CHECK(result.status == IXS_FINITE_DOMAIN_OOM &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 0 && !facts->bounds.oom &&
          facts->bounds.query_tracking_depth == 0);
    budget = 1;
    result = ixs_finite_domain_facts(facts, &query, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && result.value == NULL &&
          budget == 0);
    check_nested_query_tracking_clean(ctx, facts);
    ixs_ctx_destroy(ctx);
  }

  {
    const int64_t points[1] = {0};
    ixs_ctx *ctx = ixs_ctx_create();
    ixs_facts *facts = ixs_facts_create(ctx);
    ixs_node *item = ixs_sym(ctx, "finite_hold_synthesis_item");
    ixs_node *nested = make_nested_query_root(ctx, "finite_hold_synthesis");
    ixs_node *values[1] = {nested};
    ixs_finite_domain_result result;
    size_t budget = 2;
    CHECK(ctx && facts && item && nested && ctx->bounds_query_state == NULL &&
          !facts->bounds.oom);
    ixs_arena_set_fail_after(&ctx->arena, 0);
    result = finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_EXPR_SYNTHESIS,
                                      item, points, values, 1, &budget);
    ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
    CHECK(result.status == IXS_FINITE_DOMAIN_OOM &&
          result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
          budget == 0 && !facts->bounds.oom &&
          facts->bounds.query_tracking_depth == 0);
    budget = 2;
    result = finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_EXPR_SYNTHESIS,
                                      item, points, values, 1, &budget);
    CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
          result.check == IXS_CHECK_TRUE && result.value != NULL &&
          budget == 0);
    check_nested_query_tracking_clean(ctx, facts);
    ixs_ctx_destroy(ctx);
  }

  {
    const int64_t points[1] = {0};
    ixs_ctx *ctx = ixs_ctx_create();
    ixs_facts *facts = ixs_facts_create(ctx);
    ixs_node *item = ixs_sym(ctx, "finite_hold_batch_item");
    ixs_node *nested = make_nested_query_root(ctx, "finite_hold_batch");
    ixs_finite_integer_domain domain = {item, points, 1};
    ixs_finite_domain_batch_query query = {IXS_FINITE_DOMAIN_DEFINED, nested};
    ixs_finite_domain_batch_result result = {IXS_CHECK_TRUE, 0};
    ixs_finite_domain_status status;
    size_t budget = 1;
    CHECK(ctx && facts && item && nested && ctx->bounds_query_state == NULL &&
          !facts->bounds.oom);
    ixs_arena_set_fail_after(&ctx->arena, 0);
    status = ixs_finite_domain_batch_facts(facts, &domain, 1, &query, 1,
                                           &result, &budget);
    ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
    CHECK(status == IXS_FINITE_DOMAIN_OOM && budget == 0 &&
          result.check == IXS_CHECK_UNKNOWN && result.witness == SIZE_MAX &&
          !facts->bounds.oom && facts->bounds.query_tracking_depth == 0);
    budget = 1;
    status = ixs_finite_domain_batch_facts(facts, &domain, 1, &query, 1,
                                           &result, &budget);
    CHECK(status == IXS_FINITE_DOMAIN_COMPLETE && budget == 0 &&
          result.check == IXS_CHECK_TRUE && result.witness == SIZE_MAX);
    check_nested_query_tracking_clean(ctx, facts);
    ixs_ctx_destroy(ctx);
  }
}

static void test_public_finite_domain_composed_synthesis(void) {
  const int64_t dense_points[8] = {0, 1, 2, 3, 4, 5, 6, 7};
  const int64_t sparse_points[16] = {0,  1,  2,  3,  4,  5,  6,  7,
                                     16, 17, 18, 19, 20, 21, 22, 23};
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *item = ixs_sym(ctx, "finite_composed_item");
  ixs_node *base = ixs_sym(ctx, "finite_composed_base");
  ixs_node *add_xor[8];
  ixs_node *xor_add[8];
  ixs_node *xor_xor[8];
  ixs_node *sparse[16];
  int64_t nonpower_points[192];
  ixs_node *nonpower[192];
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_finite_domain_result result;
  size_t budget;
  size_t i;

  CHECK(ctx && item && base && facts);
  for (i = 0; i < 8u; i++) {
    int64_t xor_delta =
        ((i & 1u) ? 3 : 0) ^ ((i & 2u) ? 5 : 0) ^ ((i & 4u) ? 6 : 0);
    add_xor[i] = ixs_add(ctx, base, ixs_int(ctx, xor_delta));
    xor_add[i] = ixs_xor(ctx, base, ixs_int(ctx, (int64_t)i));
    xor_xor[i] = ixs_xor(ctx, base, ixs_int(ctx, xor_delta));
    CHECK(add_xor[i] && xor_add[i] && xor_xor[i]);
  }
  for (i = 0; i < 16u; i++) {
    sparse[i] = ixs_add(ctx, base, ixs_int(ctx, 8 * sparse_points[i]));
    CHECK(sparse[i]);
  }
  for (i = 0; i < 192u; i++) {
    nonpower_points[i] = (int64_t)i;
    nonpower[i] = ixs_add(ctx, base, ixs_int(ctx, 8 * (int64_t)i));
    CHECK(nonpower[i]);
  }

  budget = 16;
  result = finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_EXPR_SYNTHESIS,
                                    item, dense_points, add_xor, 8, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value != NULL);
  CHECK(budget == 0);

  budget = 16;
  result = finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_EXPR_SYNTHESIS,
                                    item, dense_points, xor_add, 8, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value != NULL);
  CHECK(budget == 0);

  budget = 16;
  result = finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_EXPR_SYNTHESIS,
                                    item, dense_points, xor_xor, 8, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value != NULL);
  CHECK(budget == 0);

  budget = 32;
  result = finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_EXPR_SYNTHESIS,
                                    item, sparse_points, sparse, 16, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value != NULL);
  CHECK(budget == 0);
  if (result.value) {
    ixs_node *at_missing_basis =
        ixs_subs(ctx, (ixs_node *)result.value, item, ixs_int(ctx, 8));
    ixs_node *expected = ixs_add(ctx, base, ixs_int(ctx, 64));
    CHECK(test_ixs_equivalent_facts(facts, at_missing_basis, expected) ==
          IXS_CHECK_TRUE);
  }

  budget = 384;
  result =
      finite_domain_synthesize(facts, IXS_FINITE_DOMAIN_EXPR_SYNTHESIS, item,
                               nonpower_points, nonpower, 192, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value != NULL);
  CHECK(budget == 0);

  ixs_ctx_destroy(ctx);
}

static void test_total_equivalence_new_proof_oom(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "equiv_new_oom_x");
  ixs_node *lhs = ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 8));
  ixs_node *rhs = ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 7));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_node *base = ixs_sym(ctx, "equiv_ordered_oom_base");
  ixs_node *limit = ixs_sym(ctx, "equiv_ordered_oom_limit");
  ixs_node *toggle = ixs_sym(ctx, "equiv_ordered_oom_toggle");
  ixs_node *residual = ixs_sub(
      ctx, ixs_add(ctx, base, ixs_mul(ctx, ixs_int(ctx, 4), toggle)), limit);
  ixs_node *ordered_lhs = ixs_cmp(ctx, residual, IXS_CMP_LT, ixs_int(ctx, 0));
  ixs_node *ordered_rhs = ixs_cmp(ctx, ixs_add(ctx, residual, ixs_int(ctx, 8)),
                                  IXS_CMP_LT, ixs_int(ctx, 0));
  ixs_facts *ordered = ixs_facts_create(ctx);

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(test_ixs_equivalent_facts(facts, lhs, rhs) == IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(test_ixs_equivalent_facts(facts, lhs, rhs) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(ordered,
                              ixs_cmp(ctx, ixs_mod(ctx, base, ixs_int(ctx, 16)),
                                      IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      ordered, ixs_cmp(ctx, ixs_mod(ctx, limit, ixs_int(ctx, 16)), IXS_CMP_EQ,
                       ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      ordered, ixs_cmp(ctx, toggle, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      ordered, ixs_cmp(ctx, toggle, IXS_CMP_LE, ixs_int(ctx, 1))));
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(test_ixs_equivalent_facts(ordered, ordered_lhs, ordered_rhs) ==
        IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(test_ixs_equivalent_facts(ordered, ordered_lhs, ordered_rhs) ==
        IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_public_equivalence_invalid_inputs(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "equiv_invalid_x");
  ixs_facts *facts = ixs_facts_create(ctx);

  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_equivalent_facts(facts, x, ixs_sym(other, "x")) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_equivalent_facts(facts, ctx->sentinel_error,
                                  ctx->sentinel_error) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "sentinel") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_check_predicate_facts(facts, ixs_sym(other, "p")) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_check_predicate_facts(facts, ctx->sentinel_parse_error) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "sentinel") != NULL);

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_public_affine_and_constant_difference(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "algebra_x");
  ixs_node *i = ixs_sym(ctx, "algebra_i");
  ixs_node *base = ixs_sym(ctx, "algebra_base");
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_node *coefficient = NULL;
  ixs_node *residual = NULL;
  int64_t delta = 0;

  CHECK(test_ixs_constant_difference_facts(
      facts, ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 4), x), ixs_int(ctx, 4)),
      ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 4), x), ixs_int(ctx, 1)), &delta));
  CHECK(delta == 3);
  CHECK(test_ixs_constant_difference_facts(
      facts, ixs_mul(ctx, ixs_int(ctx, 4), ixs_add(ctx, x, ixs_int(ctx, 1))),
      ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 4), x), ixs_int(ctx, 1)), &delta));
  CHECK(delta == 3);
  delta = 9;
  CHECK(!test_ixs_constant_difference_facts(facts, ixs_int(ctx, INT64_MAX),
                                            ixs_int(ctx, -1), &delta));
  CHECK(delta == 0);

  CHECK(test_ixs_affine_decompose_facts(
      facts, ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 8), i), base), i,
      &coefficient, &residual));
  CHECK(ixs_same_node(coefficient, ixs_int(ctx, 8)));
  CHECK(ixs_same_node(residual, base));
  CHECK(test_ixs_affine_decompose_facts(
      facts, ixs_mul(ctx, ixs_int(ctx, 8), ixs_add(ctx, i, base)), i,
      &coefficient, &residual));
  CHECK(ixs_same_node(coefficient, ixs_int(ctx, 8)));
  CHECK(ixs_same_node(residual, ixs_mul(ctx, ixs_int(ctx, 8), base)));
  CHECK(test_ixs_affine_decompose_facts(facts, ixs_div(ctx, i, ixs_int(ctx, 2)),
                                        i, &coefficient, &residual));
  CHECK(ixs_same_node(coefficient, ixs_rat(ctx, 1, 2)));
  CHECK(ixs_same_node(residual, ixs_int(ctx, 0)));

  CHECK(!test_ixs_affine_decompose_facts(facts, ixs_mul(ctx, i, i), i,
                                         &coefficient, &residual));
  CHECK(coefficient == NULL && residual == NULL);
  CHECK(!test_ixs_affine_decompose_facts(facts, ixs_mul(ctx, base, i), i,
                                         &coefficient, &residual));
  CHECK(coefficient == NULL && residual == NULL);
  CHECK(!test_ixs_affine_decompose_facts(
      facts, ixs_mod(ctx, i, ixs_int(ctx, 8)), i, &coefficient, &residual));
  CHECK(coefficient == NULL && residual == NULL);

  ixs_ctx_destroy(ctx);
}

static void test_public_exact_quotient_decomposition(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "quotient_x");
  ixs_node *y = ixs_sym(ctx, "quotient_y");
  ixs_node *z = ixs_sym(ctx, "quotient_z");
  ixs_node *w = ixs_sym(ctx, "quotient_w");
  ixs_node *i = ixs_sym(ctx, "quotient_i");
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *numerator = NULL;
  ixs_node *denominator = NULL;
  ixs_node *x_squared = ixs_mul(ctx, x, x);
  ixs_node *y_squared = ixs_mul(ctx, y, y);
  ixs_node *product =
      ixs_mul(ctx, ixs_rat(ctx, 3, 4), ixs_div(ctx, x_squared, y_squared));
  ixs_node *common_denominator = ixs_mul(ctx, ixs_int(ctx, 2), y);
  ixs_node *sum = ixs_add(ctx,
                          ixs_add(ctx, ixs_div(ctx, x, common_denominator),
                                  ixs_div(ctx, ixs_mul(ctx, ixs_int(ctx, 3), z),
                                          common_denominator)),
                          ixs_int(ctx, 5));
  ixs_node *expected_sum_numerator =
      ixs_add(ctx, ixs_add(ctx, x, ixs_mul(ctx, ixs_int(ctx, 3), z)),
              ixs_mul(ctx, ixs_int(ctx, 10), y));
  ixs_node *condition = ixs_cmp(ctx, i, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *values[2] = {sum, x};
  ixs_node *conditions[2] = {condition, ixs_true(ctx)};
  ixs_node *piecewise = ixs_pw(ctx, 2, values, conditions);
  ixs_node *different_denominators =
      ixs_add(ctx, ixs_div(ctx, x, y), ixs_div(ctx, z, w));
  ixs_node *different_rational_denominators = ixs_add(
      ctx, ixs_div(ctx, x, ixs_int(ctx, 2)), ixs_div(ctx, z, ixs_int(ctx, 4)));
  ixs_mulfactor large_factor = {y, 65};
  ixs_node *large_denominator = ixs_node_mul(ctx, one, 1, &large_factor);
  ixs_node *large_quotient = ixs_div(ctx, x, large_denominator);
  ixs_facts *empty = ixs_facts_create(ctx);
  ixs_facts *nonnegative = ixs_facts_create(ctx);

  CHECK(test_ixs_decompose_exact_quotient_facts(empty, product, &numerator,
                                                &denominator));
  CHECK(ixs_same_node(numerator, ixs_mul(ctx, ixs_int(ctx, 3), x_squared)));
  CHECK(ixs_same_node(denominator, ixs_mul(ctx, ixs_int(ctx, 4), y_squared)));
  CHECK(ixs_same_node(ixs_div(ctx, numerator, denominator), product));

  CHECK(test_ixs_decompose_exact_quotient_facts(empty, sum, &numerator,
                                                &denominator));
  CHECK(ixs_same_node(numerator, expected_sum_numerator));
  CHECK(ixs_same_node(denominator, common_denominator));
  CHECK(ixs_same_node(ixs_expand(ctx, ixs_div(ctx, numerator, denominator)),
                      sum));

  CHECK(test_ixs_decompose_exact_quotient_facts(empty, ixs_rat(ctx, -3, 4),
                                                &numerator, &denominator));
  CHECK(ixs_same_node(numerator, ixs_int(ctx, -3)));
  CHECK(ixs_same_node(denominator, ixs_int(ctx, 4)));
  CHECK(!test_ixs_decompose_exact_quotient_facts(empty, ixs_int(ctx, 3),
                                                 &numerator, &denominator));
  CHECK(numerator == NULL && denominator == NULL);

  CHECK(!test_ixs_decompose_exact_quotient_facts(empty, piecewise, &numerator,
                                                 &denominator));
  CHECK(numerator == NULL && denominator == NULL);
  CHECK(ixs_facts_assume_pred(nonnegative, condition));
  CHECK(test_ixs_decompose_exact_quotient_facts(nonnegative, piecewise,
                                                &numerator, &denominator));
  CHECK(ixs_same_node(numerator, expected_sum_numerator));
  CHECK(ixs_same_node(denominator, common_denominator));

  CHECK(!test_ixs_decompose_exact_quotient_facts(empty, different_denominators,
                                                 &numerator, &denominator));
  CHECK(numerator == NULL && denominator == NULL);
  CHECK(!test_ixs_decompose_exact_quotient_facts(
      empty, different_rational_denominators, &numerator, &denominator));
  CHECK(numerator == NULL && denominator == NULL);
  CHECK(!test_ixs_decompose_exact_quotient_facts(
      empty, ixs_mul(ctx, ixs_int(ctx, 2), x), &numerator, &denominator));
  CHECK(numerator == NULL && denominator == NULL);

  CHECK(test_ixs_decompose_exact_quotient_facts(empty, large_quotient,
                                                &numerator, &denominator));
  CHECK(ixs_same_node(numerator, x));
  CHECK(ixs_same_node(denominator, large_denominator));

  ixs_ctx_destroy(ctx);
}

static void test_public_exact_quotient_invalid_and_oom(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "quotient_invalid_x");
  ixs_node *y = ixs_sym(ctx, "quotient_invalid_y");
  ixs_node *expr = ixs_mul(ctx, ixs_rat(ctx, 3, 4), ixs_div(ctx, x, y));
  ixs_node *numerator = x;
  ixs_node *denominator = y;
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);
  ixs_exact_quotient_result result;

  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 10))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 5))));
  CHECK(!test_ixs_decompose_exact_quotient_facts(contradictory, expr,
                                                 &numerator, &denominator));
  CHECK(numerator == NULL && denominator == NULL);

  numerator = x;
  denominator = y;
  CHECK(!test_ixs_decompose_exact_quotient_facts(
      facts, ixs_sym(other, "quotient_other"), &numerator, &denominator));
  CHECK(numerator == NULL && denominator == NULL);
  numerator = x;
  denominator = y;
  CHECK(!test_ixs_decompose_exact_quotient_facts(facts, ctx->sentinel_error,
                                                 &numerator, &denominator));
  CHECK(numerator == NULL && denominator == NULL);
  numerator = x;
  denominator = y;
  CHECK(!test_ixs_decompose_exact_quotient_facts(facts, NULL, &numerator,
                                                 &denominator));
  CHECK(numerator == NULL && denominator == NULL);
  result = ixs_decompose_exact_quotient_facts(NULL, expr);
  CHECK(result.status == IXS_FACT_QUERY_INVALID && !result.available &&
        result.numerator == NULL && result.denominator == NULL);

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  result = ixs_decompose_exact_quotient_facts(facts, expr);
  CHECK(result.status == IXS_FACT_QUERY_OOM && !result.available &&
        result.numerator == NULL && result.denominator == NULL);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  result = ixs_decompose_exact_quotient_facts(facts, expr);
  CHECK(result.status == IXS_FACT_QUERY_COMPLETE && result.available &&
        result.numerator != NULL && result.denominator != NULL);

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_public_finite_difference_and_additive_split(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *i = ixs_sym(ctx, "difference_i");
  ixs_node *base = ixs_sym(ctx, "difference_base");
  ixs_node *one = ixs_int(ctx, 1);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *predicate_facts = ixs_facts_create(ctx);
  ixs_node *invariant_predicate =
      ixs_cmp(ctx, base, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *difference = NULL;
  ixs_node *residual = NULL;
  int64_t constant = 0;

  CHECK(predicate_facts && invariant_predicate);

  CHECK(test_ixs_finite_difference_facts(
      facts, ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 8), i), base), i, one,
      &difference));
  CHECK(ixs_same_node(difference, ixs_int(ctx, 8)));
  CHECK(test_ixs_finite_difference_facts(facts, ixs_mul(ctx, i, i), i, one,
                                         &difference));
  CHECK(ixs_same_node(difference, ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), i),
                                          ixs_int(ctx, 1))));
  CHECK(test_ixs_finite_difference_facts(
      facts, ixs_mul(ctx, ixs_int(ctx, 8), ixs_add(ctx, i, base)), i, one,
      &difference));
  CHECK(ixs_same_node(difference, ixs_int(ctx, 8)));
  CHECK(!test_ixs_finite_difference_facts(facts, i, i, i, &difference));
  CHECK(difference == NULL);
  CHECK(!test_ixs_finite_difference_facts(
      facts, ixs_add(ctx, i, ixs_int(ctx, 1)), i, ixs_int(ctx, INT64_MAX),
      &difference));
  CHECK(difference == NULL);

  /* Predicates are scalar 0/1 expressions on algebra-query surfaces.  This
   * models a Wave loop-invariant, all-equal predicate table. */
  CHECK(ixs_facts_assume_pred(predicate_facts, invariant_predicate));
  CHECK(test_ixs_equivalent_facts(predicate_facts, invariant_predicate, one) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_finite_difference_facts(predicate_facts, invariant_predicate,
                                         i, one, &difference));
  CHECK(ixs_same_node(difference, ixs_int(ctx, 0)));

  CHECK(test_ixs_split_additive_constant_facts(
      facts, ixs_add(ctx, base, ixs_int(ctx, 96)), &residual, &constant));
  CHECK(ixs_same_node(residual, base));
  CHECK(constant == 96);
  CHECK(test_ixs_split_additive_constant_facts(
      facts,
      ixs_mul(ctx, ixs_int(ctx, 8), ixs_add(ctx, base, ixs_int(ctx, 12))),
      &residual, &constant));
  CHECK(ixs_same_node(residual, ixs_mul(ctx, ixs_int(ctx, 8), base)));
  CHECK(constant == 96);
  CHECK(test_ixs_split_additive_constant_facts(
      facts, ixs_add(ctx, base, ixs_int(ctx, INT64_MAX)), &residual,
      &constant));
  CHECK(ixs_same_node(residual, base) && constant == INT64_MAX);
  CHECK(test_ixs_split_additive_constant_facts(
      facts, ixs_add(ctx, base, ixs_int(ctx, INT64_MIN)), &residual,
      &constant));
  CHECK(ixs_same_node(residual, base) && constant == INT64_MIN);
  CHECK(test_ixs_split_additive_constant_facts(facts, base, &residual,
                                               &constant));
  CHECK(ixs_same_node(residual, base) && constant == 0);
  CHECK(!test_ixs_split_additive_constant_facts(
      facts, ixs_add(ctx, base, ixs_rat(ctx, 1, 2)), &residual, &constant));
  CHECK(residual == NULL && constant == 0);

  ixs_ctx_destroy(ctx);
}

static void test_public_invariant_under_step(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *i = ixs_sym(ctx, "invariant_i");
  ixs_node *base = ixs_sym(ctx, "invariant_base");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *four = ixs_int(ctx, 4);
  ixs_node *mod = ixs_mod(ctx, i, four);
  ixs_node *linear = ixs_mul(ctx, ixs_int(ctx, 8), i);
  ixs_node *partial = ixs_div(ctx, one, ixs_sub(ctx, i, one));
  ixs_node *nested = make_nested_query_root(ctx, "invariant_limit");
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *zero_facts = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);
  ixs_fact_check_result result;

  CHECK(ctx && other && i && base && zero && one && four && mod && linear &&
        partial && nested && facts && zero_facts && contradictory);
  CHECK(test_ixs_check_invariant_under_step_facts(facts, base, i, one) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_invariant_under_step_facts(facts, mod, i, four) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_invariant_under_step_facts(facts, linear, i, one) ==
        IXS_CHECK_FALSE);
  CHECK(test_ixs_check_invariant_under_step_facts(facts, base, i, i) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(zero_facts, ixs_cmp(ctx, i, IXS_CMP_EQ, zero)));
  CHECK(test_ixs_check_invariant_under_step_facts(zero_facts, partial, i,
                                                  one) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, i, IXS_CMP_GE, ixs_int(ctx, 1))));
  CHECK(
      ixs_facts_assume_pred(contradictory, ixs_cmp(ctx, i, IXS_CMP_LE, zero)));
  result = ixs_check_invariant_under_step_facts(contradictory, base, i, one);
  CHECK(result.status == IXS_FACT_QUERY_COMPLETE &&
        result.check == IXS_CHECK_UNKNOWN);

  ixs_ctx_clear_errors(ctx);
  result = ixs_check_invariant_under_step_facts(facts, base,
                                                ixs_add(ctx, i, one), one);
  CHECK(result.status == IXS_FACT_QUERY_INVALID &&
        result.check == IXS_CHECK_UNKNOWN && ixs_ctx_nerrors(ctx) == 1u &&
        strstr(ixs_ctx_error(ctx, 0), "must be a symbol") != NULL);
  ixs_ctx_clear_errors(ctx);
  result = ixs_check_invariant_under_step_facts(
      facts, base, i, ixs_sym(other, "invariant_foreign"));
  CHECK(result.status == IXS_FACT_QUERY_INVALID &&
        result.check == IXS_CHECK_UNKNOWN && ixs_ctx_nerrors(ctx) == 1u &&
        strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  result =
      ixs_check_invariant_under_step_facts(facts, ctx->sentinel_error, i, one);
  CHECK(result.status == IXS_FACT_QUERY_INVALID &&
        result.check == IXS_CHECK_UNKNOWN && ixs_ctx_nerrors(ctx) == 1u &&
        strstr(ixs_ctx_error(ctx, 0), "sentinel") != NULL);
  result = ixs_check_invariant_under_step_facts(NULL, base, i, one);
  CHECK(result.status == IXS_FACT_QUERY_INVALID &&
        result.check == IXS_CHECK_UNKNOWN);

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  result = ixs_check_invariant_under_step_facts(facts, mod, i, four);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(result.status == IXS_FACT_QUERY_OOM &&
        result.check == IXS_CHECK_UNKNOWN);
  result = ixs_check_invariant_under_step_facts(facts, mod, i, four);
  CHECK(result.status == IXS_FACT_QUERY_COMPLETE &&
        result.check == IXS_CHECK_TRUE);

  {
    ixs_bounds_test_transport observed;
    bool held = false;
    CHECK(ixs_bounds_query_hold_begin(&facts->bounds, nested, &held) && held);
    CHECK(ixs_bounds_query_transport_probe(
        &facts->bounds, nested, IXS_BOUNDS_TEST_TRANSPORT_LIMITED, &observed));
    CHECK(observed == IXS_BOUNDS_TEST_TRANSPORT_LIMITED);
    result = ixs_check_invariant_under_step_facts(facts, nested, i, four);
    CHECK(result.status == IXS_FACT_QUERY_LIMITED &&
          result.check == IXS_CHECK_UNKNOWN);
    if (held)
      ixs_bounds_query_hold_end(&facts->bounds);
    result = ixs_check_invariant_under_step_facts(facts, nested, i, four);
    CHECK(result.status == IXS_FACT_QUERY_COMPLETE &&
          result.check == IXS_CHECK_TRUE);
  }

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_public_cyclic_decomposition_shapes_and_facts(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *i = ixs_sym(ctx, "cyclic_i");
  ixs_node *w = ixs_sym(ctx, "cyclic_w");
  ixs_node *four = ixs_int(ctx, 4);
  ixs_node *direct = ixs_mod(ctx, i, four);
  ixs_node *phased = ixs_mod(ctx, ixs_add(ctx, i, ixs_int(ctx, 2)), four);
  ixs_node *scaled = ixs_mul(ctx, ixs_int(ctx, 8192), phased);
  ixs_node *base = ixs_mul(ctx, ixs_int(ctx, 1024), w);
  ixs_node *added =
      ixs_add(ctx, base,
              ixs_mul(ctx, ixs_int(ctx, 32768),
                      ixs_mod(ctx, ixs_add(ctx, i, ixs_int(ctx, -2)), four)));
  ixs_facts *empty = ixs_facts_create(ctx);
  ixs_facts *bounded = ixs_facts_create(ctx);
  ixs_cyclic_decomposition result;

  CHECK(test_ixs_decompose_cyclic_facts(empty, direct, i, &result));
  CHECK(ixs_same_node(result.residual, ixs_int(ctx, 0)));
  CHECK(result.scale == 1 && result.modulus == 4 && result.phase == 0 &&
        result.ring == 4 && result.residual_bounded);

  CHECK(test_ixs_decompose_cyclic_facts(empty, scaled, i, &result));
  CHECK(ixs_same_node(result.residual, ixs_int(ctx, 0)));
  CHECK(result.scale == 8192 && result.modulus == 4 && result.phase == 2 &&
        result.ring == 32768 && result.residual_bounded);

  CHECK(ixs_facts_assume_pred(bounded,
                              ixs_cmp(ctx, w, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(bounded,
                              ixs_cmp(ctx, w, IXS_CMP_LE, ixs_int(ctx, 15))));
  CHECK(test_ixs_decompose_cyclic_facts(bounded, added, i, &result));
  CHECK(ixs_same_node(result.residual, base));
  CHECK(result.scale == 32768 && result.modulus == 4 && result.phase == 2 &&
        result.ring == 131072 && result.residual_bounded);

  CHECK(test_ixs_decompose_cyclic_facts(empty, added, i, &result));
  CHECK(ixs_same_node(result.residual, base));
  CHECK(!result.residual_bounded);

  CHECK(test_ixs_decompose_cyclic_facts(
      empty,
      ixs_add(ctx, ixs_int(ctx, 8), ixs_mul(ctx, ixs_int(ctx, 8), direct)), i,
      &result));
  CHECK(ixs_same_node(result.residual, ixs_int(ctx, 8)));
  CHECK(result.scale == 8 && result.ring == 32 && !result.residual_bounded);

  ixs_ctx_destroy(ctx);
}

static void test_public_cyclic_decomposition_bound_oom(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *i = ixs_sym(ctx, "cyclic_bound_oom_i");
  ixs_node *residual = ixs_sym(ctx, "cyclic_bound_oom_residual");
  ixs_node *mod = ixs_mod(ctx, i, ixs_int(ctx, 4));
  int64_t scale = 104729;
  ixs_node *cyclic = ixs_mul(ctx, ixs_int(ctx, scale), mod);
  ixs_node *expr = ixs_add(ctx, residual, cyclic);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_cyclic_decomposition result;

  CHECK(ctx && i && residual && mod && cyclic && expr && facts);
  /* Prewarm all earlier constructors; scale - 1 remains uninterned. */
  CHECK(ixs_add(ctx, i, ixs_int(ctx, 1)) != NULL);
  CHECK(ixs_same_node(ixs_sub(ctx, expr, cyclic), residual));
  memset(&result, 0xa5, sizeof(result));
  ixs_arena_set_fail_after(&ctx->arena, 0);
  CHECK(!test_ixs_decompose_cyclic_facts(facts, expr, i, &result));
  ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
  CHECK(result.residual == NULL && result.scale == 0 && result.modulus == 0 &&
        result.phase == 0 && result.ring == 0 && !result.residual_bounded);
  CHECK(test_ixs_decompose_cyclic_facts(facts, expr, i, &result));
  CHECK(ixs_same_node(result.residual, residual));
  CHECK(result.scale == scale && result.modulus == 4 && result.phase == 0 &&
        result.ring == scale * 4 && !result.residual_bounded);

  ixs_ctx_destroy(ctx);
}

static void test_public_cyclic_decomposition_rejections(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *i = ixs_sym(ctx, "cyclic_reject_i");
  ixs_node *w = ixs_sym(ctx, "cyclic_reject_w");
  ixs_node *d = ixs_sym(ctx, "cyclic_reject_d");
  ixs_node *mod = ixs_mod(ctx, i, ixs_int(ctx, 4));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *positive_divisor = ixs_facts_create(ctx);
  ixs_facts *point = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);
  ixs_cyclic_decomposition result;

  CHECK(!test_ixs_decompose_cyclic_facts(
      facts, ixs_mul(ctx, ixs_int(ctx, -8), mod), i, &result));
  CHECK(result.residual == NULL && result.scale == 0 && result.modulus == 0 &&
        result.phase == 0 && result.ring == 0 && !result.residual_bounded);
  CHECK(!test_ixs_decompose_cyclic_facts(
      facts, ixs_mul(ctx, ixs_rat(ctx, 1, 2), mod), i, &result));
  CHECK(!test_ixs_decompose_cyclic_facts(
      facts, ixs_mod(ctx, i, ixs_int(ctx, 1)), i, &result));

  CHECK(ixs_facts_assume_pred(positive_divisor,
                              ixs_cmp(ctx, d, IXS_CMP_GT, ixs_int(ctx, 1))));
  CHECK(!test_ixs_decompose_cyclic_facts(positive_divisor, ixs_mod(ctx, i, d),
                                         i, &result));
  CHECK(!test_ixs_decompose_cyclic_facts(
      facts, ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, 2), i), ixs_int(ctx, 4)), i,
      &result));
  CHECK(!test_ixs_decompose_cyclic_facts(
      facts, ixs_mod(ctx, ixs_add(ctx, i, w), ixs_int(ctx, 4)), i, &result));
  CHECK(!test_ixs_decompose_cyclic_facts(
      facts, ixs_add(ctx, i, ixs_mul(ctx, ixs_int(ctx, 8), mod)), i, &result));
  CHECK(ixs_facts_assume_pred(point,
                              ixs_cmp(ctx, i, IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(!test_ixs_decompose_cyclic_facts(
      point, ixs_add(ctx, i, ixs_mul(ctx, ixs_int(ctx, 8), mod)), i, &result));
  CHECK(!test_ixs_decompose_cyclic_facts(
      facts,
      ixs_mul(ctx, ixs_int(ctx, INT64_MAX), ixs_mod(ctx, i, ixs_int(ctx, 2))),
      i, &result));
  CHECK(
      !test_ixs_decompose_cyclic_facts(facts, ixs_add(ctx, i, w), i, &result));

  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, w, IXS_CMP_GE, ixs_int(ctx, 1))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, w, IXS_CMP_LE, ixs_int(ctx, 0))));
  CHECK(!test_ixs_decompose_cyclic_facts(contradictory, mod, i, &result));

  ixs_ctx_clear_errors(ctx);
  CHECK(!test_ixs_decompose_cyclic_facts(facts, mod, ixs_int(ctx, 1), &result));
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "must be a symbol") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!test_ixs_decompose_cyclic_facts(
      facts, mod, ixs_sym(other, "cyclic_reject_i"), &result));
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(
      !test_ixs_decompose_cyclic_facts(facts, ctx->sentinel_error, i, &result));
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "sentinel") != NULL);

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_public_algebra_helpers_use_facts(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *i = ixs_sym(ctx, "facts_algebra_i");
  ixs_node *base = ixs_sym(ctx, "facts_algebra_base");
  ixs_node *condition = ixs_cmp(ctx, i, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *values[2];
  ixs_node *conditions[2];
  ixs_node *piecewise;
  ixs_node *coefficient = NULL;
  ixs_node *residual = NULL;
  ixs_node *reciprocal = ixs_div(ctx, ixs_int(ctx, 1), i);
  ixs_facts *empty = ixs_facts_create(ctx);
  ixs_facts *nonnegative = ixs_facts_create(ctx);
  ixs_facts *nonzero = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);
  int64_t delta = 7;

  values[0] = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 8), i), base);
  values[1] = base;
  conditions[0] = condition;
  conditions[1] = ixs_true(ctx);
  piecewise = ixs_pw(ctx, 2, values, conditions);
  CHECK(!test_ixs_affine_decompose_facts(empty, piecewise, i, &coefficient,
                                         &residual));
  CHECK(ixs_facts_assume_pred(nonnegative, condition));
  CHECK(test_ixs_affine_decompose_facts(nonnegative, piecewise, i, &coefficient,
                                        &residual));
  CHECK(ixs_same_node(coefficient, ixs_int(ctx, 8)));
  CHECK(ixs_same_node(residual, base));

  CHECK(!test_ixs_constant_difference_facts(empty, reciprocal, reciprocal,
                                            &delta));
  CHECK(delta == 0);
  CHECK(ixs_facts_assume_pred(nonzero,
                              ixs_cmp(ctx, i, IXS_CMP_NE, ixs_int(ctx, 0))));
  CHECK(test_ixs_constant_difference_facts(nonzero, reciprocal, reciprocal,
                                           &delta));
  CHECK(delta == 0);

  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, i, IXS_CMP_GE, ixs_int(ctx, 10))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, i, IXS_CMP_LE, ixs_int(ctx, 5))));
  CHECK(!test_ixs_constant_difference_facts(contradictory, i, i, &delta));
  CHECK(!test_ixs_affine_decompose_facts(contradictory, i, i, &coefficient,
                                         &residual));

  ixs_ctx_destroy(ctx);
}

static void test_public_algebra_helper_invalid_inputs(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "invalid_algebra_x");
  ixs_node *other_x = ixs_sym(other, "invalid_algebra_x");
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_node *first = NULL;
  ixs_node *second = NULL;
  int64_t value = 0;

  ixs_ctx_clear_errors(ctx);
  CHECK(!test_ixs_constant_difference_facts(facts, x, other_x, &value));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!test_ixs_constant_difference_facts(facts, ctx->sentinel_error, x,
                                            &value));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "sentinel") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!test_ixs_affine_decompose_facts(facts, x, other_x, &first, &second));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!test_ixs_affine_decompose_facts(
      facts, x, ixs_add(ctx, x, ixs_int(ctx, 1)), &first, &second));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "must be a symbol") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!test_ixs_finite_difference_facts(facts, x, x, other_x, &first));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!test_ixs_finite_difference_facts(facts, ctx->sentinel_error, x,
                                          ixs_int(ctx, 1), &first));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "sentinel") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(
      !test_ixs_split_additive_constant_facts(facts, other_x, &first, &value));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!test_ixs_split_additive_constant_facts(facts, ctx->sentinel_error,
                                                &first, &value));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "sentinel") != NULL);

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_public_exact_divide_basic(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *item = ixs_sym(ctx, "item");
  ixs_node *slot = ixs_sym(ctx, "slot");
  ixs_node *k = ixs_sym(ctx, "K");
  ixs_node *expr = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 64), item),
                           ixs_mul(ctx, ixs_int(ctx, 32), slot));
  ixs_node *expected = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 8), item),
                               ixs_mul(ctx, ixs_int(ctx, 4), slot));
  ixs_node *negative_expected =
      ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, -8), item),
              ixs_mul(ctx, ixs_int(ctx, -4), slot));
  ixs_node *congruence = ixs_cmp(ctx, ixs_mod(ctx, k, ixs_int(ctx, 32)),
                                 IXS_CMP_EQ, ixs_int(ctx, 0));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_exact_divide_result result;

  result = ixs_try_exact_divide_facts(facts, expr, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  CHECK(ixs_same_node(result.quotient, expected));

  result = ixs_try_exact_divide_facts(facts, expr, -8);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  CHECK(ixs_same_node(result.quotient, negative_expected));

  result =
      ixs_try_exact_divide_facts(facts, ixs_add(ctx, item, ixs_int(ctx, 1)), 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_UNKNOWN);
  CHECK(result.quotient == NULL);
  result = ixs_try_exact_divide_facts(facts, ixs_int(ctx, 65), 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_NOT_EXACT);
  CHECK(result.quotient == NULL);
  result =
      ixs_try_exact_divide_facts(facts, ixs_div(ctx, ixs_int(ctx, 1), item), 1);
  CHECK(result.status == IXS_EXACT_DIVIDE_UNKNOWN);
  CHECK(result.quotient == NULL);

  CHECK(ixs_facts_assume_pred(facts, congruence));
  result = ixs_try_exact_divide_facts(facts, k, 32);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  CHECK(ixs_same_node(result.quotient, ixs_div(ctx, k, ixs_int(ctx, 32))));

  ixs_ctx_destroy(ctx);
}

static void test_public_exact_divide_fact_integer_bitwise_factor(void) {
  static const char integer_xor[] =
      "xor(1/8*(8*Mod(raw, 2) + 32*Mod(floor(1/4*raw), 2) + "
      "16*Mod(floor(1/2*raw), 2)), Mod(floor(1/16*raw), 8))";
  static const char noninteger_xor[] = "xor(1/8*raw, Mod(floor(1/16*raw), 8))";
  ixs_ctx *ctx = ixs_ctx_create();
  const ixs_node *integer =
      ixs_parse_expr(ctx, integer_xor, sizeof(integer_xor) - 1);
  const ixs_node *noninteger =
      ixs_parse_expr(ctx, noninteger_xor, sizeof(noninteger_xor) - 1);
  ixs_facts *facts = ixs_facts_create(ctx);
  const ixs_node *scaled_integer = ixs_mul(ctx, ixs_int(ctx, 16), integer);
  const ixs_node *scaled_noninteger =
      ixs_mul(ctx, ixs_int(ctx, 16), noninteger);
  ixs_exact_divide_result result;

  CHECK(!ixs_node_is_integer_valued(integer));
  CHECK(test_ixs_check_integer_valued_facts(facts, integer) == IXS_CHECK_TRUE);
  result = ixs_try_exact_divide_facts(facts, scaled_integer, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  CHECK(result.quotient != NULL);

  CHECK(test_ixs_check_integer_valued_facts(facts, noninteger) ==
        IXS_CHECK_UNKNOWN);
  result = ixs_try_exact_divide_facts(facts, scaled_noninteger, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_UNKNOWN);
  CHECK(result.quotient == NULL);

  ixs_ctx_destroy(ctx);
}

static void test_public_exact_divide_fact_scaled_xor_quotient(void) {
  const size_t allowance = 100000;
  const size_t fault_window = 16;
  static const char dividend_text[] =
      "xor(2*Mod(item, 2), 6*Mod(floor(item/2), 2), "
      "12*Mod(floor(item/4), 2), 24*Mod(floor(item/8), 2), "
      "48*Mod(floor(item/16), 2), 96*floor(item/32))";
  static const char expected_text[] =
      "xor(Mod(item, 2), 3*Mod(floor(item/2), 2), "
      "6*Mod(floor(item/4), 2), 12*Mod(floor(item/8), 2), "
      "24*Mod(floor(item/16), 2), 48*floor(item/32))";
  static const char domain_text[] = "item >= 0 & item <= 63";
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *dividend =
      ixs_parse_expr(ctx, dividend_text, sizeof(dividend_text) - 1);
  ixs_node *expected =
      ixs_parse_expr(ctx, expected_text, sizeof(expected_text) - 1);
  ixs_node *domain = ixs_parse_pred(ctx, domain_text, sizeof(domain_text) - 1);
  ixs_node *origin = ixs_sym(ctx, "origin");
  ixs_node *dividend_with_origin =
      ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), origin), dividend);
  ixs_node *expected_with_origin = ixs_add(ctx, origin, expected);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_exact_divide_result result;
  size_t allocations;
  size_t budget;
  size_t first_fault_budget;
  size_t first_success_budget;
  bool reached_success = false;

  CHECK(dividend && expected && domain && origin && dividend_with_origin &&
        expected_with_origin && facts);
  CHECK(ixs_facts_assume_pred(facts, domain));

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), allowance);
  result = ixs_try_exact_divide_facts(facts, dividend_with_origin, 2);
  allocations = allowance - ixs_test_scratch(ctx)->fail_after;
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  CHECK(result.quotient != NULL);
  CHECK(ixs_same_node(result.quotient, expected_with_origin));
  CHECK(allocations > 0 && allocations < allowance - fault_window);

  result = ixs_try_exact_divide_facts(facts, dividend, 2);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  CHECK(result.quotient != NULL);
  CHECK(ixs_same_node(result.quotient, expected));

  first_fault_budget =
      allocations > fault_window ? allocations - fault_window : 0;
  first_success_budget = allocations + fault_window;
  for (budget = first_fault_budget; budget <= first_success_budget; budget++) {
    ixs_ctx *oom_ctx = ixs_ctx_create();
    ixs_node *oom_dividend =
        ixs_parse_expr(oom_ctx, dividend_text, sizeof(dividend_text) - 1);
    ixs_node *oom_expected =
        ixs_parse_expr(oom_ctx, expected_text, sizeof(expected_text) - 1);
    ixs_node *oom_domain =
        ixs_parse_pred(oom_ctx, domain_text, sizeof(domain_text) - 1);
    ixs_node *oom_origin = ixs_sym(oom_ctx, "origin");
    ixs_node *oom_dividend_with_origin =
        ixs_add(oom_ctx, ixs_mul(oom_ctx, ixs_int(oom_ctx, 2), oom_origin),
                oom_dividend);
    ixs_node *oom_expected_with_origin =
        ixs_add(oom_ctx, oom_origin, oom_expected);
    ixs_facts *oom_facts = ixs_facts_create(oom_ctx);

    CHECK(oom_dividend && oom_expected && oom_domain && oom_origin &&
          oom_dividend_with_origin && oom_expected_with_origin && oom_facts);
    CHECK(ixs_facts_assume_pred(oom_facts, oom_domain));
    ixs_arena_set_fail_after(ixs_test_scratch(oom_ctx), budget);
    result = ixs_try_exact_divide_facts(oom_facts, oom_dividend_with_origin, 2);
    ixs_arena_set_fail_after(ixs_test_scratch(oom_ctx),
                             IXS_ARENA_FAILURE_DISABLED);
    if (result.status == IXS_EXACT_DIVIDE_PROVEN) {
      CHECK(ixs_same_node(result.quotient, oom_expected_with_origin));
      reached_success = true;
      ixs_ctx_destroy(oom_ctx);
      break;
    }
    CHECK(result.status == IXS_EXACT_DIVIDE_OOM);
    CHECK(result.quotient == NULL);
    CHECK(ixs_ctx_nerrors(oom_ctx) == 1);
    if (ixs_ctx_nerrors(oom_ctx) != 0)
      CHECK(strstr(ixs_ctx_error(oom_ctx, 0), "out of memory") != NULL);

    result = ixs_try_exact_divide_facts(oom_facts, oom_dividend_with_origin, 2);
    CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
    CHECK(ixs_same_node(result.quotient, oom_expected_with_origin));
    ixs_ctx_destroy(oom_ctx);
  }
  CHECK(reached_success);
  CHECK(budget > first_fault_budget);

  ixs_ctx_destroy(ctx);
}

static void test_public_exact_divide_requires_defined_product(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *k = ixs_sym(ctx, "partial_product_k");
  ixs_node *x = ixs_sym(ctx, "partial_product_x");
  ixs_node *two = ixs_int(ctx, 2);
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *condition = ixs_cmp(ctx, x, IXS_CMP_GT, zero);
  ixs_node *values[1] = {ixs_div(ctx, k, two)};
  ixs_node *conditions[1] = {condition};
  ixs_node *piecewise = ixs_pw(ctx, 1, values, conditions);
  ixs_node *product = ixs_mul(ctx, ixs_int(ctx, 16), piecewise);
  ixs_node *even = ixs_cmp(ctx, ixs_mod(ctx, k, two), IXS_CMP_EQ, zero);
  ixs_facts *partial = ixs_facts_create(ctx);
  ixs_facts *covered = ixs_facts_create(ctx);
  ixs_exact_divide_result result;

  CHECK(ixs_facts_assume_pred(partial, even));
  CHECK(test_ixs_check_integer_valued_facts(partial, piecewise) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_defined_facts(partial, piecewise) == IXS_CHECK_UNKNOWN);
  result = ixs_try_exact_divide_facts(partial, product, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_UNKNOWN);
  CHECK(result.quotient == NULL);

  CHECK(ixs_facts_assume_pred(covered, even));
  CHECK(ixs_facts_assume_pred(covered, condition));
  result = ixs_try_exact_divide_facts(covered, product, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  CHECK(ixs_same_node(result.quotient, k));

  ixs_ctx_destroy(ctx);
}

static void test_public_exact_divide_fact_simplification(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *item = ixs_sym(ctx, "exact_pw_item");
  ixs_node *slot = ixs_sym(ctx, "exact_pw_slot");
  ixs_node *inner = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), item), slot);
  ixs_node *value = ixs_mul(ctx, ixs_int(ctx, 32), inner);
  ixs_node *condition = ixs_cmp(ctx, item, IXS_CMP_LT, ixs_int(ctx, 64));
  ixs_node *values[1] = {value};
  ixs_node *conditions[1] = {condition};
  ixs_node *piecewise = ixs_pw(ctx, 1, values, conditions);
  ixs_node *scaled_predicate_values[2] = {ixs_int(ctx, 2), ixs_int(ctx, 0)};
  ixs_node *scaled_predicate_conditions[2] = {condition, ixs_true(ctx)};
  ixs_node *scaled_predicate =
      ixs_pw(ctx, 2, scaled_predicate_values, scaled_predicate_conditions);
  ixs_node *in_range =
      ixs_and(ctx, ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 0)),
              ixs_cmp(ctx, item, IXS_CMP_LE, ixs_int(ctx, 63)));
  ixs_node *outside = ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 64));
  ixs_node *expected = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 8), item),
                               ixs_mul(ctx, ixs_int(ctx, 4), slot));
  ixs_facts *unknown = ixs_facts_create(ctx);
  ixs_facts *active = ixs_facts_create(ctx);
  ixs_facts *inactive = ixs_facts_create(ctx);
  ixs_exact_divide_result result;

  CHECK(test_ixs_check_defined_facts(unknown, scaled_predicate) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_divisible_facts(unknown, scaled_predicate, 2) ==
        IXS_CHECK_TRUE);
  result = ixs_try_exact_divide_facts(unknown, scaled_predicate, 2);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  CHECK(ixs_same_node(result.quotient, condition));

  CHECK(ixs_facts_assume_pred(active, in_range));
  result = ixs_try_exact_divide_facts(active, piecewise, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  CHECK(ixs_same_node(result.quotient, expected));

  result = ixs_try_exact_divide_facts(unknown, piecewise, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_UNKNOWN);
  CHECK(result.quotient == NULL);

  CHECK(ixs_facts_assume_pred(inactive, outside));
  CHECK(test_ixs_check_defined_facts(inactive, piecewise) == IXS_CHECK_FALSE);
  result = ixs_try_exact_divide_facts(inactive, piecewise, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_UNKNOWN);
  CHECK(result.quotient == NULL);

  ixs_ctx_destroy(ctx);
}

static void test_public_exact_divide_canonical_nonzero_factor(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "canonical_nonzero_x");
  ixs_node *d = ixs_sym(ctx, "canonical_nonzero_d");
  ixs_node *other = ixs_sym(ctx, "canonical_nonzero_other");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *source_argument =
      ixs_mul(ctx, ixs_rat(ctx, 1, 256), ixs_add(ctx, ixs_int(ctx, 255), d));
  ixs_node *canonical_argument = ixs_add(ctx, ixs_rat(ctx, 255, 256),
                                         ixs_mul(ctx, ixs_rat(ctx, 1, 256), d));
  ixs_node *source_base = ixs_trunc(ctx, source_argument);
  ixs_node *canonical_base = ixs_trunc(ctx, canonical_argument);
  ixs_node *scaled_base = ixs_mul(ctx, ixs_int(ctx, 8), source_base);
  ixs_node *base_nonzero = ixs_cmp(ctx, scaled_base, IXS_CMP_NE, zero);
  ixs_node *quotient_source = ixs_trunc(ctx, ixs_div(ctx, x, source_base));
  ixs_node *dividend = ixs_mul(ctx, ixs_int(ctx, 8), quotient_source);
  ixs_node *canonical_quotient =
      ixs_trunc(ctx, ixs_div(ctx, x, canonical_base));
  ixs_node *sum = ixs_add(ctx, source_base, other);
  ixs_node *sum_nonzero = ixs_cmp(ctx, sum, IXS_CMP_NE, zero);
  ixs_node *canonical_reciprocal =
      ixs_div(ctx, ixs_int(ctx, 1), canonical_base);
  ixs_node *piecewise_values[2] = {source_base, ixs_int(ctx, 8)};
  ixs_node *piecewise_conditions[2] = {
      ixs_cmp(ctx, source_base, IXS_CMP_LT, ixs_int(ctx, 8)), ixs_true(ctx)};
  ixs_node *source_piecewise =
      ixs_pw(ctx, 2, piecewise_values, piecewise_conditions);
  ixs_node *canonical_piecewise = ixs_expand(ctx, source_piecewise);
  ixs_node *piecewise_nonzero =
      ixs_cmp(ctx, source_piecewise, IXS_CMP_NE, zero);
  ixs_node *piecewise_quotient_source =
      ixs_trunc(ctx, ixs_div(ctx, x, source_piecewise));
  ixs_node *piecewise_dividend =
      ixs_mul(ctx, ixs_int(ctx, 8), piecewise_quotient_source);
  ixs_node *canonical_piecewise_reciprocal =
      ixs_div(ctx, ixs_int(ctx, 1), canonical_piecewise);
  ixs_facts *product = ixs_facts_create(ctx);
  ixs_facts *piecewise = ixs_facts_create(ctx);
  ixs_facts *addition = ixs_facts_create(ctx);
  ixs_exact_divide_result result;

  CHECK(!ixs_same_node(source_base, canonical_base));
  CHECK(ixs_facts_assume_preds(product, &base_nonzero, 1));
  CHECK(test_ixs_check_defined_facts(product, dividend) == IXS_CHECK_TRUE);
  result = ixs_try_exact_divide_facts(product, dividend, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  CHECK(ixs_same_node(result.quotient, canonical_quotient));
  CHECK(test_ixs_check_defined_facts(product, result.quotient) ==
        IXS_CHECK_TRUE);

  CHECK(!ixs_same_node(source_piecewise, canonical_piecewise));
  CHECK(ixs_facts_assume_preds(piecewise, &piecewise_nonzero, 1));
  CHECK(test_ixs_check_defined_facts(
            piecewise, canonical_piecewise_reciprocal) == IXS_CHECK_TRUE);
  result = ixs_try_exact_divide_facts(piecewise, piecewise_dividend, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  CHECK(test_ixs_check_defined_facts(piecewise, result.quotient) ==
        IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_preds(addition, &sum_nonzero, 1));
  CHECK(test_ixs_check_defined_facts(addition, canonical_reciprocal) ==
        IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_public_exact_divide_scaled_mod_domain(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "scaled_mod_x");
  ixs_node *two31 = ixs_int(ctx, INT64_C(2147483648));
  ixs_node *two32 = ixs_int(ctx, INT64_C(4294967296));
  ixs_node *scaled = ixs_mul(ctx, ixs_int(ctx, 2), x);
  ixs_node *mod = ixs_mod(ctx, scaled, two32);
  ixs_node *expected_signed = ixs_mod(ctx, x, two31);
  ixs_facts *nonnegative = ixs_facts_create(ctx);
  ixs_facts *signed_range = ixs_facts_create(ctx);
  ixs_facts *negative_wrap = ixs_facts_create(ctx);
  ixs_facts *upper_wrap = ixs_facts_create(ctx);
  ixs_exact_divide_result result;
  ixs_node *quotient;

  CHECK(ixs_facts_assume_pred(nonnegative,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(nonnegative, ixs_cmp(ctx, x, IXS_CMP_LT, two31)));
  result = ixs_try_exact_divide_facts(nonnegative, mod, 2);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  quotient = test_ixs_simplify_facts(nonnegative, result.quotient);
  CHECK(ixs_same_node(quotient, x));
  CHECK(test_ixs_equivalent_facts(nonnegative, result.quotient, x) ==
        IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(
      signed_range, ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, INT32_MIN))));
  CHECK(ixs_facts_assume_pred(
      signed_range, ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, INT32_MAX))));
  result = ixs_try_exact_divide_facts(signed_range, mod, 2);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  quotient = test_ixs_simplify_facts(signed_range, result.quotient);
  CHECK(ixs_same_node(quotient, expected_signed));
  CHECK(test_ixs_equivalent_facts(signed_range, result.quotient, x) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(negative_wrap,
                              ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, -1))));
  result = ixs_try_exact_divide_facts(negative_wrap, mod, 2);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  quotient = test_ixs_simplify_facts(negative_wrap, result.quotient);
  CHECK(ixs_same_node(quotient, ixs_int(ctx, INT32_MAX)));

  CHECK(ixs_facts_assume_pred(upper_wrap, ixs_cmp(ctx, x, IXS_CMP_EQ, two31)));
  result = ixs_try_exact_divide_facts(upper_wrap, mod, 2);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  quotient = test_ixs_simplify_facts(upper_wrap, result.quotient);
  CHECK(ixs_same_node(quotient, ixs_int(ctx, 0)));

  ixs_ctx_destroy(ctx);
}

static void test_public_exact_divide_extrema_and_overflow(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *k = ixs_sym(ctx, "K");
  ixs_node *large = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, INT64_MAX), x),
                            ixs_mul(ctx, ixs_int(ctx, INT64_MAX), y));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *overflow_facts = ixs_facts_create(ctx);
  ixs_exact_divide_result result;

  result =
      ixs_try_exact_divide_facts(facts, ixs_int(ctx, INT64_MIN), INT64_MIN);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  CHECK(ixs_same_node(result.quotient, ixs_int(ctx, 1)));
  result =
      ixs_try_exact_divide_facts(facts, ixs_int(ctx, INT64_MAX), INT64_MIN);
  CHECK(result.status == IXS_EXACT_DIVIDE_NOT_EXACT);

  ixs_ctx_clear_errors(ctx);
  result = ixs_try_exact_divide_facts(facts, ixs_int(ctx, INT64_MIN), -1);
  CHECK(result.status == IXS_EXACT_DIVIDE_INVALID);
  CHECK(result.quotient == NULL);
  CHECK(ixs_ctx_nerrors(ctx) >= 1);
  CHECK(strstr(ixs_ctx_error(ctx, ixs_ctx_nerrors(ctx) - 1),
               "quotient is not representable") != NULL);

  result = ixs_try_exact_divide_facts(facts, large, INT64_MAX);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  CHECK(ixs_same_node(result.quotient, ixs_add(ctx, x, y)));

  CHECK(ixs_facts_assume_pred(
      overflow_facts, ixs_cmp(ctx, ixs_mod(ctx, k, ixs_int(ctx, INT64_MAX)),
                              IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(overflow_facts,
                              ixs_cmp(ctx, ixs_mod(ctx, k, ixs_int(ctx, 2)),
                                      IXS_CMP_EQ, ixs_int(ctx, 0))));
  result = ixs_try_exact_divide_facts(overflow_facts, k, INT64_MAX);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  result = ixs_try_exact_divide_facts(overflow_facts, k, 2);
  CHECK(result.status == IXS_EXACT_DIVIDE_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_public_exact_divide_invalid_and_oom(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *item = ixs_sym(ctx, "item");
  ixs_node *slot = ixs_sym(ctx, "slot");
  ixs_node *floor_reciprocal =
      ixs_floor(ctx, ixs_div(ctx, ixs_int(ctx, 1), item));
  ixs_node *expr = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 64), item),
                           ixs_mul(ctx, ixs_int(ctx, 32), slot));
  ixs_node *guarded = ixs_mul(ctx, ixs_int(ctx, 8), floor_reciprocal);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *positive = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);
  ixs_exact_divide_result result;

  CHECK(ixs_facts_assume_pred(positive,
                              ixs_cmp(ctx, item, IXS_CMP_GT, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      contradictory, ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 10))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, item, IXS_CMP_LE, ixs_int(ctx, 5))));
  result = ixs_try_exact_divide_facts(contradictory, expr, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_UNKNOWN);
  CHECK(result.quotient == NULL);

  ixs_ctx_clear_errors(ctx);
  result = ixs_try_exact_divide_facts(facts, expr, 0);
  CHECK(result.status == IXS_EXACT_DIVIDE_INVALID);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "divisor must be nonzero") != NULL);
  result = ixs_try_exact_divide_facts(facts, ixs_sym(other, "item"), 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_INVALID);
  CHECK(strstr(ixs_ctx_error(ctx, 1), "different context") != NULL);
  result = ixs_try_exact_divide_facts(facts, ctx->sentinel_error, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_INVALID);
  CHECK(strstr(ixs_ctx_error(ctx, 2), "sentinel expression") != NULL);
  result = ixs_try_exact_divide_facts(facts, NULL, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_INVALID);
  CHECK(strstr(ixs_ctx_error(ctx, 3), "NULL expression") != NULL);

  ixs_ctx_clear_errors(ctx);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  result = ixs_try_exact_divide_facts(facts, expr, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_OOM);
  CHECK(result.quotient == NULL);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "out of memory") != NULL);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  result = ixs_try_exact_divide_facts(facts, expr, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  CHECK(result.quotient != NULL);

  ixs_ctx_clear_errors(ctx);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  result = ixs_try_exact_divide_facts(positive, guarded, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_OOM);
  CHECK(result.quotient == NULL);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "out of memory") != NULL);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  result = ixs_try_exact_divide_facts(positive, guarded, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  CHECK(ixs_same_node(result.quotient, floor_reciprocal));

  result = ixs_try_exact_divide_facts(NULL, expr, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_INVALID);
  CHECK(result.quotient == NULL);

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_public_integrality_invalid_and_contradictory(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *other_x = ixs_sym(other, "x");
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);

  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 10))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 5))));
  CHECK(test_ixs_check_integer_valued_facts(contradictory, x) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_divisible_facts(contradictory, ixs_int(ctx, 64), 32) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_check_integer_valued(ctx, other_x, NULL, 0) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_integer_valued(ctx, ctx->sentinel_error, NULL, 0) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_integer_valued_facts(facts, other_x) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_integer_valued_facts(facts, ctx->sentinel_error) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_divisible_facts(facts, other_x, 8) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_divisible_facts(facts, ctx->sentinel_error, 8) ==
        IXS_CHECK_UNKNOWN);
  CHECK(!ixs_node_is_integer_valued(ctx->sentinel_error));

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_public_defined_reciprocal_and_children(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "defined_x");
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *reciprocal = ixs_div(ctx, one, x);
  ixs_node *positive = ixs_cmp(ctx, x, IXS_CMP_GT, zero);
  ixs_node *negative = ixs_cmp(ctx, x, IXS_CMP_LT, zero);
  ixs_node *is_zero = ixs_cmp(ctx, x, IXS_CMP_EQ, zero);
  ixs_node *nonzero = ixs_cmp(ctx, x, IXS_CMP_NE, zero);
  ixs_node *mixed[2] = {ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, -1)),
                        ixs_cmp(ctx, x, IXS_CMP_LE, one)};
  ixs_node *contradictory[2] = {nonzero, is_zero};
  ixs_node *strict_nodes[10];
  ixs_mulfactor strict_factor;
  size_t i;

  CHECK(ixs_check_defined(ctx, reciprocal, NULL, 0) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_defined(ctx, reciprocal, &positive, 1) == IXS_CHECK_TRUE);
  CHECK(ixs_check_defined(ctx, reciprocal, &negative, 1) == IXS_CHECK_TRUE);
  CHECK(ixs_check_defined(ctx, reciprocal, &nonzero, 1) == IXS_CHECK_TRUE);
  CHECK(ixs_check_defined(ctx, reciprocal, &is_zero, 1) == IXS_CHECK_FALSE);
  CHECK(ixs_check_defined(ctx, reciprocal, mixed, 2) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_defined(ctx, reciprocal, contradictory, 2) ==
        IXS_CHECK_UNKNOWN);

  strict_nodes[0] = ixs_add(ctx, reciprocal, one);
  strict_factor.base = reciprocal;
  strict_factor.exp = 1;
  strict_nodes[1] = ixs_node_mul(ctx, one, 1, &strict_factor);
  strict_nodes[2] = ixs_floor(ctx, reciprocal);
  strict_nodes[3] = ixs_ceil(ctx, reciprocal);
  strict_nodes[4] = ixs_max(ctx, reciprocal, one);
  strict_nodes[5] = ixs_min(ctx, reciprocal, one);
  strict_nodes[6] = ixs_xor(ctx, reciprocal, one);
  strict_nodes[7] = ixs_cmp(ctx, reciprocal, IXS_CMP_GT, zero);
  strict_nodes[8] = ixs_and(ctx, strict_nodes[7], ixs_true(ctx));
  strict_nodes[9] = ixs_not(ctx, strict_nodes[7]);
  for (i = 0; i < sizeof(strict_nodes) / sizeof(strict_nodes[0]); i++)
    CHECK(ixs_check_defined(ctx, strict_nodes[i], &is_zero, 1) ==
          IXS_CHECK_FALSE);

  ixs_ctx_destroy(ctx);
}

static void test_public_defined_mod_contract(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "defined_mod_x");
  ixs_node *m = ixs_sym(ctx, "defined_mod_m");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *positive_mod = ixs_mod(ctx, x, ixs_int(ctx, 4));
  ixs_node *rational_mod = ixs_mod(ctx, x, ixs_rat(ctx, 1, 2));
  ixs_node *symbolic_mod = ixs_mod(ctx, x, m);
  ixs_node *m_positive = ixs_cmp(ctx, m, IXS_CMP_GT, zero);
  ixs_node *m_negative = ixs_cmp(ctx, m, IXS_CMP_LT, zero);
  ixs_node *m_zero = ixs_cmp(ctx, m, IXS_CMP_EQ, zero);
  ixs_node *m_nonzero = ixs_cmp(ctx, m, IXS_CMP_NE, zero);
  ixs_node *raw_zero = ixs_node_binary(ctx, IXS_MOD, x, zero, IXS_CMP_EQ);
  ixs_node *raw_negative =
      ixs_node_binary(ctx, IXS_MOD, x, ixs_int(ctx, -4), IXS_CMP_EQ);
  ixs_node *bad_lhs =
      ixs_mod(ctx, ixs_div(ctx, ixs_int(ctx, 1), x), ixs_int(ctx, 4));
  ixs_node *reciprocal_mod = ixs_div(ctx, ixs_int(ctx, 1), positive_mod);
  ixs_node *x_zero = ixs_cmp(ctx, x, IXS_CMP_EQ, zero);
  ixs_node *x_nonzero = ixs_cmp(ctx, x, IXS_CMP_NE, zero);
  ixs_node *mod_zero = ixs_cmp(ctx, positive_mod, IXS_CMP_EQ, zero);
  ixs_node *mod_nonzero = ixs_cmp(ctx, positive_mod, IXS_CMP_NE, zero);
  ixs_node *literal_zero = ixs_mod(ctx, x, zero);
  ixs_node *literal_negative = ixs_mod(ctx, x, ixs_int(ctx, -1));

  CHECK(ixs_check_defined(ctx, positive_mod, NULL, 0) == IXS_CHECK_TRUE);
  CHECK(ixs_check_defined(ctx, rational_mod, NULL, 0) == IXS_CHECK_TRUE);
  CHECK(ixs_check_defined(ctx, symbolic_mod, NULL, 0) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_defined(ctx, symbolic_mod, &m_positive, 1) == IXS_CHECK_TRUE);
  CHECK(ixs_check_defined(ctx, symbolic_mod, &m_negative, 1) ==
        IXS_CHECK_FALSE);
  CHECK(ixs_check_defined(ctx, symbolic_mod, &m_zero, 1) == IXS_CHECK_FALSE);
  CHECK(ixs_check_defined(ctx, symbolic_mod, &m_nonzero, 1) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_defined(ctx, raw_zero, NULL, 0) == IXS_CHECK_FALSE);
  CHECK(ixs_check_defined(ctx, raw_negative, NULL, 0) == IXS_CHECK_FALSE);
  CHECK(ixs_check_defined(ctx, bad_lhs, &x_zero, 1) == IXS_CHECK_FALSE);
  CHECK(ixs_check_defined(ctx, bad_lhs, &x_nonzero, 1) == IXS_CHECK_TRUE);
  CHECK(ixs_check_defined(ctx, reciprocal_mod, &mod_nonzero, 1) ==
        IXS_CHECK_TRUE);
  CHECK(ixs_check_defined(ctx, reciprocal_mod, &mod_zero, 1) ==
        IXS_CHECK_FALSE);
  CHECK(ixs_check_defined(ctx, literal_zero, NULL, 0) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_defined(ctx, literal_negative, NULL, 0) == IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_public_defined_bitwise_integrality(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "defined_bit_x");
  ixs_node *y = ixs_sym(ctx, "defined_bit_y");
  ixs_node *k = ixs_sym(ctx, "defined_bit_k");
  ixs_node *scaled = ixs_div(ctx, k, ixs_int(ctx, 2));
  ixs_node *args[3] = {x, y, scaled};
  ixs_node *exprs[3];
  ixs_node *even = ixs_cmp(ctx, ixs_mod(ctx, k, ixs_int(ctx, 2)), IXS_CMP_EQ,
                           ixs_int(ctx, 0));
  ixs_node *one = ixs_cmp(ctx, k, IXS_CMP_EQ, ixs_int(ctx, 1));
  ixs_facts *unknown = ixs_facts_create(ctx);
  ixs_facts *integral = ixs_facts_create(ctx);
  ixs_facts *fractional = ixs_facts_create(ctx);
  size_t i;

  exprs[0] = ixs_xor_many(ctx, 3, args);
  exprs[1] = ixs_and_many(ctx, 3, args);
  exprs[2] = ixs_or_many(ctx, 3, args);
  CHECK(ixs_facts_assume_pred(integral, even));
  CHECK(ixs_facts_assume_pred(fractional, one));
  for (i = 0; i < sizeof(exprs) / sizeof(exprs[0]); i++) {
    CHECK(ixs_node_assoc_nargs(exprs[i]) == 3);
    CHECK(ixs_node_assoc_arg(exprs[i], 2) == scaled);
    CHECK(test_ixs_check_defined_facts(unknown, exprs[i]) == IXS_CHECK_UNKNOWN);
    CHECK(test_ixs_check_defined_facts(integral, exprs[i]) == IXS_CHECK_TRUE);
    CHECK(test_ixs_check_defined_facts(fractional, exprs[i]) ==
          IXS_CHECK_FALSE);
  }

  ixs_ctx_destroy(ctx);
}

static void test_public_defined_piecewise_first_match(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "defined_pw_x");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *two = ixs_int(ctx, 2);
  ixs_node *reciprocal = ixs_div(ctx, one, x);
  ixs_node *values[3];
  ixs_node *conds[3];
  ixs_node *piecewise;
  ixs_node *x_positive = ixs_cmp(ctx, x, IXS_CMP_GT, zero);
  ixs_node *x_negative = ixs_cmp(ctx, x, IXS_CMP_LT, zero);
  ixs_node *x_nonnegative = ixs_cmp(ctx, x, IXS_CMP_GE, zero);
  ixs_node *x_zero = ixs_cmp(ctx, x, IXS_CMP_EQ, zero);
  ixs_node *x_nonzero = ixs_cmp(ctx, x, IXS_CMP_NE, zero);
  ixs_node *x_lt_16 = ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 16));
  ixs_node *x_ge_16 = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 16));
  ixs_pwcase raw_cases[2];

  values[0] = reciprocal;
  values[1] = ixs_add(ctx, reciprocal, one);
  values[2] = one;
  conds[0] = x_positive;
  conds[1] = x_negative;
  conds[2] = ixs_true(ctx);
  piecewise = ixs_pw(ctx, 3, values, conds);
  CHECK(ixs_check_defined(ctx, piecewise, NULL, 0) == IXS_CHECK_TRUE);

  values[0] = reciprocal;
  values[1] = one;
  conds[0] = x_zero;
  conds[1] = ixs_true(ctx);
  piecewise = ixs_pw(ctx, 2, values, conds);
  CHECK(ixs_check_defined(ctx, piecewise, &x_positive, 1) == IXS_CHECK_TRUE);
  CHECK(ixs_check_defined(ctx, piecewise, &x_zero, 1) == IXS_CHECK_FALSE);

  values[0] = reciprocal;
  values[1] = one;
  conds[0] = x_nonzero;
  conds[1] = ixs_true(ctx);
  piecewise = ixs_pw(ctx, 2, values, conds);
  CHECK(ixs_check_defined(ctx, piecewise, NULL, 0) == IXS_CHECK_TRUE);

  values[0] = one;
  values[1] = reciprocal;
  values[2] = two;
  conds[0] = x_nonnegative;
  conds[1] = x_zero;
  conds[2] = ixs_true(ctx);
  piecewise = ixs_pw(ctx, 3, values, conds);
  CHECK(ixs_check_defined(ctx, piecewise, NULL, 0) == IXS_CHECK_TRUE);

  values[0] = one;
  conds[0] = x_lt_16;
  piecewise = ixs_pw(ctx, 1, values, conds);
  CHECK(ixs_check_defined(ctx, piecewise, &x_lt_16, 1) == IXS_CHECK_TRUE);
  CHECK(ixs_check_defined(ctx, piecewise, NULL, 0) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_defined(ctx, piecewise, &x_ge_16, 1) == IXS_CHECK_FALSE);

  raw_cases[0].value = ctx->sentinel_error;
  raw_cases[0].cond = ixs_false(ctx);
  raw_cases[1].value = one;
  raw_cases[1].cond = ixs_true(ctx);
  piecewise = ixs_node_pw(ctx, 2, raw_cases);
  CHECK(ixs_check_defined(ctx, piecewise, NULL, 0) == IXS_CHECK_TRUE);

  raw_cases[0].value = one;
  raw_cases[0].cond = ixs_true(ctx);
  raw_cases[1].value = ctx->sentinel_error;
  raw_cases[1].cond = x_zero;
  piecewise = ixs_node_pw(ctx, 2, raw_cases);
  CHECK(ixs_check_defined(ctx, piecewise, NULL, 0) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_public_defined_piecewise_condition(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "defined_cond_x");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *reciprocal = ixs_div(ctx, one, x);
  ixs_node *condition = ixs_cmp(ctx, reciprocal, IXS_CMP_GT, zero);
  ixs_node *values[2] = {one, zero};
  ixs_node *conds[2] = {condition, ixs_true(ctx)};
  ixs_node *piecewise = ixs_pw(ctx, 2, values, conds);
  ixs_node *x_zero = ixs_cmp(ctx, x, IXS_CMP_EQ, zero);
  ixs_node *x_positive = ixs_cmp(ctx, x, IXS_CMP_GT, zero);
  ixs_node *mixed[2] = {ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, -1)),
                        ixs_cmp(ctx, x, IXS_CMP_LE, one)};

  CHECK(ixs_check_defined(ctx, piecewise, &x_zero, 1) == IXS_CHECK_FALSE);
  CHECK(ixs_check_defined(ctx, piecewise, &x_positive, 1) == IXS_CHECK_TRUE);
  CHECK(ixs_check_defined(ctx, piecewise, mixed, 2) == IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_public_defined_shared_rounding_piecewise(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "defined_shared_round_x");
  ixs_node *d = ixs_sym(ctx, "defined_shared_round_d");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *quotient = ixs_div(ctx, x, d);
  ixs_node *values[2] = {ixs_floor(ctx, quotient), ixs_ceil(ctx, quotient)};
  ixs_node *conditions[2] = {ixs_cmp(ctx, x, IXS_CMP_GE, zero), ixs_true(ctx)};
  ixs_node *piecewise = ixs_pw(ctx, 2, values, conditions);
  ixs_node *d_nonzero = ixs_cmp(ctx, d, IXS_CMP_NE, zero);
  ixs_node *d_zero = ixs_cmp(ctx, d, IXS_CMP_EQ, zero);

  CHECK(ixs_check_defined(ctx, piecewise, NULL, 0) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_defined(ctx, piecewise, &d_nonzero, 1) == IXS_CHECK_TRUE);
  CHECK(ixs_check_defined(ctx, piecewise, &d_zero, 1) == IXS_CHECK_FALSE);

  ixs_ctx_destroy(ctx);
}

static void test_public_defined_facts_and_invalid(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "defined_fact_x");
  ixs_node *other_x = ixs_sym(other, "defined_fact_x");
  ixs_node *reciprocal = ixs_div(ctx, ixs_int(ctx, 1), x);
  ixs_node *invalid_cmp = ixs_node_binary(ctx, IXS_CMP, x, ixs_int(ctx, 0),
                                          (ixs_cmp_op)(IXS_CMP_NE + 1));
  ixs_facts *positive = ixs_facts_create(ctx);
  ixs_facts *zero = ixs_facts_create(ctx);
  ixs_facts *nonzero = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);
  ixs_range_result range;

  range.has_lower = true;
  range.has_upper = true;
  range.lower_p = 1;
  range.lower_q = 1;
  range.upper_p = 8;
  range.upper_q = 1;
  CHECK(ixs_facts_assume_range(positive, x, &range));
  CHECK(test_ixs_check_defined_facts(positive, reciprocal) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(zero,
                              ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(test_ixs_check_defined_facts(zero, reciprocal) == IXS_CHECK_FALSE);
  CHECK(ixs_facts_assume_pred(nonzero,
                              ixs_cmp(ctx, x, IXS_CMP_NE, ixs_int(ctx, 0))));
  CHECK(test_ixs_check_defined_facts(nonzero, reciprocal) == IXS_CHECK_TRUE);
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 2))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 1))));
  CHECK(test_ixs_check_defined_facts(contradictory, reciprocal) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_check_defined(ctx, NULL, NULL, 0) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_defined(ctx, ctx->sentinel_error, NULL, 0) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_defined(ctx, other_x, NULL, 0) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_defined_facts(positive, other_x) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_defined_facts(positive, ctx->sentinel_parse_error) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_defined_facts(NULL, x) == IXS_CHECK_UNKNOWN);
  CHECK(invalid_cmp != NULL && !ixs_node_is_known_total(invalid_cmp));
  CHECK((invalid_cmp->properties & IXS_NODE_PROPERTY_VALID) != 0);
  CHECK((invalid_cmp->properties &
         (IXS_NODE_PROPERTY_INTEGER | IXS_NODE_PROPERTY_BOOL |
          IXS_NODE_PROPERTY_TOTAL)) == 0);
  CHECK(!ixs_node_is_integer_valued(invalid_cmp));
  CHECK(!ixs_node_is_pred(invalid_cmp));
  CHECK(ixs_check_integer_valued(ctx, invalid_cmp, NULL, 0) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_defined(ctx, invalid_cmp, NULL, 0) == IXS_CHECK_UNKNOWN);

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(test_ixs_check_defined_facts(positive, reciprocal) ==
        IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(test_ixs_check_defined_facts(positive, reciprocal) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_public_defined_total_memo_rejects_malformed_nodes(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "defined_total_memo_x");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *ge_zero = ixs_cmp(ctx, x, IXS_CMP_GE, zero);
  ixs_node *le_one = ixs_cmp(ctx, x, IXS_CMP_LE, one);
  ixs_node *single_arg[1] = {ge_zero};
  ixs_mulfactor zero_factor = {x, 0};
  ixs_node *malformed_assoc = ixs_node_assoc(ctx, IXS_AND, 1, single_arg);
  ixs_node *malformed_mul = ixs_node_mul(ctx, one, 1, &zero_factor);
  ixs_node *canonical_assoc = ixs_and(ctx, ge_zero, le_one);
  ixs_node *canonical_mul = ixs_mul(ctx, x, ixs_int(ctx, 2));

  CHECK(malformed_assoc != NULL && malformed_mul != NULL);
  CHECK(!ixs_node_is_known_total(malformed_assoc));
  CHECK(!ixs_node_is_known_total(malformed_mul));
  CHECK((malformed_assoc->properties &
         (IXS_NODE_PROPERTY_INTEGER | IXS_NODE_PROPERTY_BOOL |
          IXS_NODE_PROPERTY_TOTAL)) == 0);
  CHECK((malformed_mul->properties &
         (IXS_NODE_PROPERTY_INTEGER | IXS_NODE_PROPERTY_TOTAL)) == 0);
  CHECK(!ixs_node_is_integer_valued(malformed_assoc));
  CHECK(!ixs_node_is_pred(malformed_assoc));
  CHECK(!ixs_node_is_integer_valued(malformed_mul));
  CHECK(ixs_check_defined(ctx, malformed_assoc, NULL, 0) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_defined(ctx, malformed_mul, NULL, 0) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_integer_valued(ctx, malformed_assoc, NULL, 0) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_integer_valued(ctx, malformed_mul, NULL, 0) ==
        IXS_CHECK_UNKNOWN);

  CHECK(canonical_assoc != NULL && canonical_mul != NULL);
  CHECK(ixs_node_tag(canonical_assoc) == IXS_AND);
  CHECK((canonical_assoc->properties &
         (IXS_NODE_PROPERTY_INTEGER | IXS_NODE_PROPERTY_BOOL |
          IXS_NODE_PROPERTY_TOTAL)) ==
        (IXS_NODE_PROPERTY_INTEGER | IXS_NODE_PROPERTY_BOOL |
         IXS_NODE_PROPERTY_TOTAL));
  CHECK(ixs_node_is_pred(canonical_assoc));
  CHECK(ixs_node_is_known_total(canonical_assoc));
  CHECK(ixs_node_is_known_total(canonical_mul));
  CHECK(ixs_check_defined(ctx, canonical_assoc, NULL, 0) == IXS_CHECK_TRUE);
  CHECK(ixs_check_defined(ctx, canonical_mul, NULL, 0) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_public_defined_expression_facts_do_not_close_domain(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "defined_range_x");
  ixs_node *d = ixs_sym(ctx, "defined_range_d");
  ixs_node *floored = ixs_floor(ctx, ixs_div(ctx, x, d));
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *self_equality = ixs_cmp(ctx, floored, IXS_CMP_EQ, zero);
  ixs_node *divisor_nonzero = ixs_cmp(ctx, d, IXS_CMP_NE, zero);
  ixs_node *closed_assumptions[2] = {self_equality, divisor_nonzero};
  ixs_facts *range_only = ixs_facts_create(ctx);
  ixs_facts *range_closed = ixs_facts_create(ctx);
  ixs_facts *equality_only = ixs_facts_create(ctx);
  ixs_facts *equality_closed = ixs_facts_create(ctx);
  ixs_facts *batch_unclosed = ixs_facts_create(ctx);
  ixs_facts *batch_closed = ixs_facts_create(ctx);
  ixs_range_result range;

  range.has_lower = true;
  range.has_upper = true;
  range.lower_p = 0;
  range.lower_q = 1;
  range.upper_p = 7;
  range.upper_q = 1;

  CHECK(ixs_facts_assume_range(range_only, floored, &range));
  CHECK(test_ixs_check_defined_facts(range_only, floored) == IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_range(range_closed, floored, &range));
  CHECK(ixs_facts_assume_pred(range_closed, divisor_nonzero));
  CHECK(test_ixs_check_defined_facts(range_closed, floored) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(equality_only, self_equality));
  CHECK(test_ixs_check_defined_facts(equality_only, floored) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(equality_closed, self_equality));
  CHECK(ixs_facts_assume_pred(equality_closed, divisor_nonzero));
  CHECK(test_ixs_check_defined_facts(equality_closed, floored) ==
        IXS_CHECK_TRUE);

  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_facts_assume_preds(batch_unclosed, &self_equality, 1));
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "closed domain") != NULL);
  ixs_ctx_clear_errors(ctx);

  CHECK(ixs_facts_assume_preds(batch_closed, closed_assumptions, 2));
  CHECK(test_ixs_check_defined_facts(batch_closed, floored) == IXS_CHECK_TRUE);

  CHECK(ixs_check_defined(ctx, floored, &self_equality, 1) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_defined(ctx, floored, closed_assumptions, 2) ==
        IXS_CHECK_TRUE);

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(test_ixs_check_defined_facts(range_closed, floored) ==
        IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(test_ixs_check_defined_facts(range_closed, floored) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void check_bounds_payload_unchanged(const ixs_bounds *actual,
                                           const ixs_bounds *before) {
  CHECK(actual->vars == before->vars && actual->nvars == before->nvars &&
        actual->cap == before->cap);
  CHECK(actual->exprs == before->exprs && actual->nexprs == before->nexprs &&
        actual->expr_cap == before->expr_cap);
  CHECK(actual->difference_vars == before->difference_vars &&
        actual->ndifference_vars == before->ndifference_vars &&
        actual->difference_index == before->difference_index &&
        actual->ndifferences == before->ndifferences);
  CHECK(actual->exact_vars == before->exact_vars &&
        actual->nexact_vars == before->nexact_vars &&
        actual->exact_index == before->exact_index);
  CHECK(actual->nonzero == before->nonzero &&
        actual->nnonzero == before->nnonzero);
  CHECK(actual->contradiction == before->contradiction &&
        actual->oom == before->oom);
}

static void test_public_facts_closed_batch_contract(void) {
  const size_t budget = 4096;
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "closed_batch_x");
  ixs_node *d = ixs_sym(ctx, "closed_batch_d");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *floored = ixs_floor(ctx, ixs_div(ctx, x, d));
  ixs_node *unclosed = ixs_cmp(ctx, floored, IXS_CMP_EQ, zero);
  ixs_node *x_nonnegative = ixs_cmp(ctx, x, IXS_CMP_GE, zero);
  ixs_node *nested = make_nested_query_root(ctx, "closed_batch_nested");
  ixs_node *nested_floor = ixs_floor(ctx, ixs_div(ctx, nested, d));
  ixs_node *nested_unclosed = ixs_cmp(ctx, nested_floor, IXS_CMP_EQ, zero);
  ixs_node *contradictory_predicates[2] = {unclosed, ixs_false(ctx)};
  ixs_facts *rejected = ixs_facts_create(ctx);
  ixs_facts *calibration = ixs_facts_create(ctx);
  ixs_facts *validation_oom = ixs_facts_create(ctx);
  ixs_facts *nested_rejected = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);
  ixs_facts *created;
  ixs_bounds before;
  ixs_bounds observed;
  size_t active_count;
  size_t nesting;
  size_t prefix_allocations;

  CHECK(ixs_facts_assume_pred(rejected, x_nonnegative));
  before = rejected->bounds;
  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_facts_assume_preds(rejected, &unclosed, 1));
  CHECK(!rejected->usable);
  check_bounds_payload_unchanged(&rejected->bounds, &before);
  CHECK(ixs_ctx_nerrors(ctx) == 1 &&
        strstr(ixs_ctx_error(ctx, 0), "closed domain") != NULL);
  CHECK(!ixs_facts_assume_pred(rejected,
                               ixs_cmp(ctx, d, IXS_CMP_NE, ixs_int(ctx, 0))));
  CHECK(test_ixs_check_defined_facts(rejected, floored) == IXS_CHECK_UNKNOWN);

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), budget);
  CHECK(ixs_facts_assume_pred(calibration, unclosed));
  prefix_allocations = budget - ixs_test_scratch(ctx)->fail_after;
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(prefix_allocations > 0 && prefix_allocations < budget);
  before = validation_oom->bounds;
  ixs_ctx_clear_errors(ctx);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), prefix_allocations);
  CHECK(!ixs_facts_assume_preds(validation_oom, &unclosed, 1));
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(!validation_oom->usable);
  check_bounds_payload_unchanged(&validation_oom->bounds, &before);
  CHECK(ixs_ctx_nerrors(ctx) == 0);

  CHECK(nested && ixs_node_contains_nested_piecewise(nested_unclosed));
  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_facts_assume_preds(nested_rejected, &nested_unclosed, 1));
  CHECK(ctx->bounds_query_state != NULL);
  observed = nested_rejected->bounds;
  observed.query_state = ctx->bounds_query_state;
  ixs_bounds_query_stats(&observed, NULL, NULL, NULL, NULL, NULL, NULL, NULL,
                         &active_count, &nesting);
  CHECK(observed.query_tracking_depth == 0 && active_count == 0 &&
        nesting == 0);

  CHECK(ixs_facts_assume_preds(contradictory, contradictory_predicates, 2));
  CHECK(contradictory->usable);
  CHECK(test_ixs_check_defined_facts(contradictory, floored) ==
        IXS_CHECK_UNKNOWN);

  created = ixs_facts_create_preds(IXS_TEST_SESSION(ctx), &unclosed, 1);
  CHECK(created != NULL && created->usable);
  CHECK(test_ixs_check_defined_facts(created, floored) == IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_public_defined_traversal_bounds_and_sharing(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *shallow = ixs_sym(ctx, "defined_depth");
  ixs_node *deep;
  ixs_node *shared_base = ixs_sym(ctx, "defined_shared");
  ixs_node *shared = shared_base;
  ixs_node *guarded;
  ixs_node *shared_pw;
  ixs_node *shared_values[2];
  ixs_node *shared_conds[2];
  ixs_node *nested = ixs_int(ctx, 1);
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *shared_positive =
      ixs_cmp(ctx, shared_base, IXS_CMP_GT, ixs_int(ctx, 0));
  ixs_facts *shared_facts = ixs_facts_create(ctx);
  ixs_mulfactor guarded_factor;
  ixs_pwcase one_case;
  unsigned i;

  for (i = 0; i < 300; i++)
    shallow = ixs_node_floor(ctx, shallow);
  CHECK(ixs_check_defined(ctx, shallow, NULL, 0) == IXS_CHECK_TRUE);

  deep = shallow;
  for (i = 300; i < 1100; i++)
    deep = ixs_node_floor(ctx, deep);
  /* Interning already proved this structurally total one node at a time. */
  CHECK(ixs_check_defined(ctx, deep, NULL, 0) == IXS_CHECK_TRUE);

  for (i = 0; i < 60; i++) {
    ixs_node *max_args[2] = {shared, shared};
    shared = ixs_node_assoc(ctx, IXS_MAX, 2, max_args);
  }
  CHECK(ixs_check_defined(ctx, shared, NULL, 0) == IXS_CHECK_TRUE);
  guarded_factor.base = shared;
  guarded_factor.exp = -1;
  guarded = ixs_node_mul(ctx, one, 1, &guarded_factor);
  CHECK(ixs_check_defined(ctx, guarded, &shared_positive, 1) == IXS_CHECK_TRUE);
  CHECK(ixs_facts_assume_pred(shared_facts, shared_positive));
  /* Eval memo, stack, depth memo succeed; interval cache fails. */
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 3);
  CHECK(test_ixs_check_defined_facts(shared_facts, guarded) ==
        IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(test_ixs_check_defined_facts(shared_facts, guarded) == IXS_CHECK_TRUE);
  shared_values[0] = guarded;
  shared_values[1] = one;
  shared_conds[0] = shared_positive;
  shared_conds[1] = ixs_true(ctx);
  shared_pw = ixs_pw(ctx, 2, shared_values, shared_conds);
  CHECK(ixs_check_defined(ctx, shared_pw, NULL, 0) == IXS_CHECK_TRUE);

  one_case.cond = ixs_true(ctx);
  for (i = 0; i < 33; i++) {
    one_case.value = nested;
    nested = ixs_node_pw(ctx, 1, &one_case);
  }
  CHECK(ixs_check_defined(ctx, nested, NULL, 0) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_fact_simplify_session_lifetime_and_oom(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "fact_lifetime_x");
  ixs_node *lo = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *hi = ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 8));
  ixs_node *mod = ixs_mod(ctx, x, ixs_int(ctx, 16));
  ixs_node *values[2] = {ixs_add(ctx, x, ixs_int(ctx, 1)),
                         ixs_add(ctx, x, ixs_int(ctx, 2))};
  ixs_node *conds[2] = {ixs_cmp(ctx, x, IXS_CMP_GT, ixs_int(ctx, 3)),
                        ixs_true(ctx)};
  ixs_node *piecewise = ixs_pw(ctx, 2, values, conds);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *poisoned;
  ixs_node *batch[2];
  ixs_simplify_result simplify_result;
  size_t errors;

  CHECK(ixs_facts_assume_pred(facts, lo));
  CHECK(ixs_facts_assume_pred(facts, hi));

  errors = ixs_ctx_nerrors(ctx);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  simplify_result = ixs_simplify_facts(facts, x);
  CHECK(simplify_result.status == IXS_FACT_QUERY_OOM &&
        simplify_result.value == NULL);
  CHECK(ixs_ctx_nerrors(ctx) == errors + 1);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  simplify_result = ixs_simplify_facts(facts, piecewise);
  CHECK(simplify_result.status == IXS_FACT_QUERY_OOM &&
        simplify_result.value == NULL);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(test_ixs_simplify_facts(facts, mod) == x);

  batch[0] = mod;
  batch[1] = piecewise;
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(ixs_simplify_batch_facts(facts, batch, 2) == IXS_FACT_QUERY_OOM);
  CHECK(batch[0] == mod);
  CHECK(batch[1] == piecewise);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(test_ixs_simplify_facts(facts, mod) == x);

  poisoned = ixs_facts_create(ctx);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(!ixs_facts_assume_pred(poisoned, lo));
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  simplify_result = ixs_simplify_facts(poisoned, mod);
  CHECK(simplify_result.status == IXS_FACT_QUERY_INVALID &&
        simplify_result.value == NULL);
  CHECK(test_ixs_check_facts(poisoned, lo) == IXS_CHECK_UNKNOWN);

  (ixs_session_reset)(IXS_TEST_SESSION(ctx));
  CHECK(test_ixs_simplify_facts(facts, mod) == NULL);
  facts = ixs_facts_create(ctx);
  CHECK(facts != NULL);
  CHECK(test_ixs_simplify_facts(facts, mod) == mod);
  ixs_ctx_destroy(ctx);

  {
    ixs_ctx *raw_ctx = (ixs_ctx_create)();
    ixs_session session;
    ixs_node *raw_x;
    ixs_node *raw_pred;
    ixs_facts *stale;
    ixs_facts *fresh;

    ixs_session_init(&session, raw_ctx);
    raw_x = (ixs_sym)(&session, "destroyed_fact_x");
    raw_pred = (ixs_cmp)(&session, raw_x, IXS_CMP_GE, (ixs_int)(&session, 0));
    stale = (ixs_facts_create)(&session);
    CHECK((ixs_facts_assume_pred)(stale, raw_pred));
    ixs_session_destroy(&session);
    CHECK(test_ixs_simplify_facts(stale, raw_x) == NULL);

    ixs_session_init(&session, raw_ctx);
    CHECK(test_ixs_simplify_facts(stale, raw_x) == NULL);
    fresh = (ixs_facts_create)(&session);
    CHECK(fresh != NULL);
    CHECK(test_ixs_simplify_facts(fresh, raw_x) == raw_x);
    ixs_session_destroy(&session);
    (ixs_ctx_destroy)(raw_ctx);
  }
}

static void test_fact_query_arena_session_teardown(void) {
  ixs_ctx *ctx = (ixs_ctx_create)();
  ixs_session session;
  ixs_node *x;
  ixs_node *zero;
  ixs_node *pred;
  ixs_facts *first;
  ixs_facts *second;
  ixs_facts *after_reset;
  ixs_fact_check_result result;

  ixs_session_init(&session, ctx);
  x = (ixs_sym)(&session, "fact_query_arena_teardown_x");
  zero = (ixs_int)(&session, 0);
  pred = (ixs_cmp)(&session, x, IXS_CMP_GE, zero);
  first = (ixs_facts_create)(&session);
  second = (ixs_facts_create)(&session);
  CHECK(first != NULL && second != NULL);

  result = (ixs_check_predicate_facts)(first, pred);
  CHECK(result.status == IXS_FACT_QUERY_COMPLETE);
  result = (ixs_check_predicate_facts)(second, pred);
  CHECK(result.status == IXS_FACT_QUERY_COMPLETE);
  CHECK(first->bounds.query_arena.current != NULL ||
        first->bounds.query_arena.spare != NULL);
  CHECK(second->bounds.query_arena.current != NULL ||
        second->bounds.query_arena.spare != NULL);

  ixs_session_reset(&session);
  CHECK(first->impl == NULL && first->epoch == 0 &&
        first->bounds.query_arena.current == NULL &&
        first->bounds.query_arena.spare == NULL);
  CHECK(second->impl == NULL && second->epoch == 0 &&
        second->bounds.query_arena.current == NULL &&
        second->bounds.query_arena.spare == NULL);
  result = (ixs_check_predicate_facts)(first, pred);
  CHECK(result.status == IXS_FACT_QUERY_INVALID);

  after_reset = (ixs_facts_create)(&session);
  CHECK(after_reset != NULL);
  result = (ixs_check_predicate_facts)(after_reset, pred);
  CHECK(result.status == IXS_FACT_QUERY_COMPLETE);
  CHECK(after_reset->bounds.query_arena.current != NULL ||
        after_reset->bounds.query_arena.spare != NULL);

  ixs_session_destroy(&session);
  CHECK(after_reset->impl == NULL && after_reset->epoch == 0 &&
        after_reset->bounds.query_arena.current == NULL &&
        after_reset->bounds.query_arena.spare == NULL);
  result = (ixs_check_predicate_facts)(after_reset, pred);
  CHECK(result.status == IXS_FACT_QUERY_INVALID);
  (ixs_ctx_destroy)(ctx);
}

static void test_batch_rewrite_cache_oom_is_atomic(void) {
  enum { NROOTS = 260 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *single = ixs_sym(ctx, "batch_cache_initial_oom");
  ixs_node *single_batch[1] = {single};
  ixs_node *growth_batch[NROOTS];
  ixs_session_binding binding;
  ixs_bounds bnds;
  ixs_arena_mark mark;
  size_t i;

  for (i = 0; i < NROOTS; i++) {
    char name[40];
    snprintf(name, sizeof(name), "batch_cache_growth_oom_%zu", i);
    growth_batch[i] = ixs_sym(ctx, name);
  }

  CHECK(ixs_session_bind(&binding, IXS_TEST_SESSION(ctx)) == ctx);

  mark = ixs_arena_save(&ctx->scratch);
  CHECK(ixs_bounds_init_ctx(&bnds, ctx, &ctx->scratch));
  ixs_arena_set_fail_after(&ctx->scratch, 0);
  CHECK(!simp_simplify_batch_bounds(ctx, single_batch, 1, &bnds));
  CHECK(single_batch[0] == NULL);
  ixs_arena_set_fail_after(&ctx->scratch, IXS_ARENA_FAILURE_DISABLED);
  ixs_arena_restore(&ctx->scratch, mark);

  mark = ixs_arena_save(&ctx->scratch);
  CHECK(ixs_bounds_init_ctx(&bnds, ctx, &ctx->scratch));
  /*
   * The first allocation creates the 256-slot table. Unique roots then fill
   * it to 75 percent; the second allocation is the deferred table growth.
   */
  ixs_arena_set_fail_after(&ctx->scratch, 1);
  CHECK(!simp_simplify_batch_bounds(ctx, growth_batch, NROOTS, &bnds));
  for (i = 0; i < NROOTS; i++)
    CHECK(growth_batch[i] == NULL);
  ixs_arena_set_fail_after(&ctx->scratch, IXS_ARENA_FAILURE_DISABLED);
  ixs_arena_restore(&ctx->scratch, mark);

  ixs_session_unbind(&binding);
  ixs_ctx_destroy(ctx);
}

static void test_mod_rewrite_oom_propagates(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "mod_rewrite_oom_x");
  ixs_node *y = ixs_sym(ctx, "mod_rewrite_oom_y");
  ixs_node *z = ixs_sym(ctx, "mod_rewrite_oom_z");
  ixs_node *m16 = ixs_int(ctx, 16);
  ixs_node *left_arg = ixs_add(ctx, x, z);
  ixs_node *right_arg = ixs_add(ctx, y, z);
  ixs_node *difference =
      ixs_sub(ctx, ixs_mod(ctx, left_arg, m16), ixs_mod(ctx, right_arg, m16));
  ixs_node *congruences[] = {
      ixs_cmp(ctx, ixs_mod(ctx, x, m16), IXS_CMP_EQ, ixs_int(ctx, 0)),
      ixs_cmp(ctx, ixs_mod(ctx, y, m16), IXS_CMP_EQ, ixs_int(ctx, 0)),
  };
  ixs_node *m32 = ixs_int(ctx, 32);
  ixs_node *scaled_arg = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), x),
                                 ixs_mul(ctx, ixs_int(ctx, 2), y));
  ixs_node *scaled_quotient =
      ixs_div(ctx, ixs_mod(ctx, scaled_arg, m32), ixs_int(ctx, 2));

  /* Prebuild the literal-Mod relational probes; leave each transform's
   * result as the first new permanent-arena node. */
  CHECK(ixs_sub(ctx, left_arg, m16) != NULL);
  CHECK(ixs_sub(ctx, right_arg, m16) != NULL);
  ixs_arena_set_fail_after(&ctx->arena, 0);
  CHECK(ixs_simplify(ctx, difference, congruences, 2) == NULL);
  ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
  CHECK(ixs_simplify(ctx, difference, congruences, 2) == ixs_int(ctx, 0));

  CHECK(ixs_sub(ctx, scaled_arg, m32) != NULL);
  ixs_arena_set_fail_after(&ctx->arena, 0);
  CHECK(ixs_simplify(ctx, scaled_quotient, NULL, 0) == NULL);
  ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
  CHECK(ixs_simplify(ctx, scaled_quotient, NULL, 0) != NULL);

  ixs_ctx_destroy(ctx);
}

static void test_same_bucket_floor_oom_is_conservative(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *a = ixs_sym(ctx, "floor_resource_a");
  ixs_node *d = ixs_sym(ctx, "floor_resource_d");
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *base = ixs_floor(ctx, ixs_div(ctx, a, d));
  ixs_node *next = ixs_floor(ctx, ixs_div(ctx, ixs_add(ctx, a, one), d));
  ixs_node *difference = ixs_sub(ctx, base, next);
  ixs_node *positive = ixs_cmp(ctx, d, IXS_CMP_GT, ixs_int(ctx, 0));
  ixs_node *no_cross =
      ixs_cmp(ctx, ixs_add(ctx, ixs_mod(ctx, a, d), one), IXS_CMP_LT, d);
  ixs_node *safe[] = {positive, no_cross};

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(ixs_simplify(ctx, difference, safe, 2) == NULL);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(ixs_simplify(ctx, difference, safe, 2) == ixs_int(ctx, 0));

  ixs_ctx_destroy(ctx);
}

static void test_associative_constructor_oom(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "assoc_oom_x");
  ixs_node *y = ixs_sym(ctx, "assoc_oom_y");
  ixs_node *z = ixs_sym(ctx, "assoc_oom_z");
  ixs_node *args[3] = {x, y, z};
  ixs_node *constants[2] = {ixs_int(ctx, 1), ixs_int(ctx, 2)};
  ixs_node *partial = ixs_div(ctx, x, ixs_int(ctx, 2));

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(ixs_xor_many(ctx, 3, args) == NULL);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(ixs_node_tag(ixs_xor_many(ctx, 3, args)) == IXS_XOR);

  ixs_arena_set_fail_after(&ctx->arena, 0);
  CHECK(ixs_xor_many(ctx, 2, constants) == NULL);
  ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
  CHECK(ixs_xor_many(ctx, 2, constants) == ixs_int(ctx, 3));

  ixs_arena_set_fail_after(&ctx->arena, 0);
  CHECK(ixs_and_many(ctx, 1, &partial) == NULL);
  ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
  CHECK(ixs_node_tag(ixs_and_many(ctx, 1, &partial)) == IXS_AND);

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(ixs_is_domain_error(ixs_pw(ctx, 0, NULL, NULL)));
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);

  ixs_ctx_destroy(ctx);
}

/* ------------------------------------------------------------------ */
/*  main                                                              */
/* ------------------------------------------------------------------ */

static void test_deep_node_order_is_iterative(void) {
  enum { DEPTH = 150000 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_session_binding binding;
  struct ixs_node_impl *chain_a = calloc(DEPTH, sizeof(*chain_a));
  struct ixs_node_impl *chain_b = calloc(DEPTH, sizeof(*chain_b));
  ixs_node *a = ixs_node_sym(ctx, "deep_a", 6);
  ixs_node *b = ixs_node_sym(ctx, "deep_b", 6);
  ixs_node *modulus = ixs_node_int(ctx, 7);
  ixs_node *args[2];
  uint32_t i;
  size_t errors;

  CHECK(ctx != NULL && chain_a != NULL && chain_b != NULL && a != NULL &&
        b != NULL && modulus != NULL);
  if (!ctx || !chain_a || !chain_b || !a || !b || !modulus) {
    free(chain_a);
    free(chain_b);
    ixs_ctx_destroy(ctx);
    return;
  }
  for (i = 0; i < DEPTH; i++) {
    chain_a[i].tag = IXS_MOD;
    chain_a[i].properties = IXS_NODE_PROPERTY_VALID |
                            IXS_NODE_PROPERTY_INTEGER | IXS_NODE_PROPERTY_TOTAL;
    chain_a[i].u.binary.lhs = a;
    chain_a[i].u.binary.rhs = modulus;
    chain_b[i].tag = IXS_MOD;
    chain_b[i].properties = chain_a[i].properties;
    chain_b[i].u.binary.lhs = b;
    chain_b[i].u.binary.rhs = modulus;
    a = &chain_a[i];
    b = &chain_b[i];
  }

  CHECK(ixs_session_bind(&binding, IXS_TEST_SESSION(ctx)) == ctx);
  CHECK(ixs_node_cmp(ctx, a, b) < 0);
  ixs_arena_set_fail_after(&ctx->scratch, 0);
  CHECK(ixs_node_cmp(ctx, a, b) == IXS_NODE_CMP_OOM);
  ixs_arena_set_fail_after(&ctx->scratch, IXS_ARENA_FAILURE_DISABLED);

  args[0] = b;
  args[1] = a;
  errors = ctx->nerrors;
  ixs_arena_set_fail_after(&ctx->scratch, 2);
  CHECK(simp_max_many(ctx, 2, args) == NULL);
  CHECK(ctx->nerrors == errors);
  ixs_arena_set_fail_after(&ctx->scratch, IXS_ARENA_FAILURE_DISABLED);
  CHECK(simp_max_many(ctx, 2, args) != NULL);

  errors = ctx->nerrors;
  ixs_arena_set_fail_after(&ctx->scratch, 1);
  CHECK(simp_add(ctx, a, b) == NULL);
  CHECK(ctx->nerrors == errors);
  ixs_arena_set_fail_after(&ctx->scratch, IXS_ARENA_FAILURE_DISABLED);
  CHECK(simp_add(ctx, a, b) != NULL);
  ixs_session_unbind(&binding);

  ixs_ctx_destroy(ctx);
  free(chain_a);
  free(chain_b);
}

static void rational_assume_integer_range(ixs_facts *facts, ixs_node *expr,
                                          int64_t lower, int64_t upper) {
  ixs_range_result range;
  range.has_lower = true;
  range.has_upper = true;
  range.lower_p = lower;
  range.lower_q = 1;
  range.upper_p = upper;
  range.upper_q = 1;
  CHECK(ixs_facts_assume_range(facts, expr, &range));
}

static void test_public_rational_intermediate_boundaries(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "rational_boundary_x");
  int64_t large_denominator = INT64_C(1099511627776);
  int64_t large_bias = large_denominator - 1;
  ixs_node *half = ixs_div(ctx, x, ixs_int(ctx, 2));
  ixs_node *floor_half = ixs_floor(ctx, half);
  ixs_node *ceil_half = ixs_ceil(ctx, half);
  ixs_node *trunc_half = ixs_trunc(ctx, half);
  ixs_node *ceil_third = ixs_ceil(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)));
  ixs_node *ceil_fifth = ixs_ceil(ctx, ixs_div(ctx, x, ixs_int(ctx, 5)));
  ixs_node *ceil_u32_max =
      ixs_ceil(ctx, ixs_div(ctx, x, ixs_int(ctx, INT64_C(4294967295))));
  ixs_node *ceil_above_u32 =
      ixs_ceil(ctx, ixs_div(ctx, x, ixs_int(ctx, INT64_C(4294967296))));
  ixs_node *large_quotient = ixs_div(ctx, x, ixs_int(ctx, large_denominator));
  ixs_node *large_ceil = ixs_ceil(ctx, large_quotient);
  ixs_node *large_trunc = ixs_trunc(ctx, large_quotient);
  ixs_facts *signed_boundary = ixs_facts_create(ctx);
  ixs_facts *word_boundary = ixs_facts_create(ctx);
  ixs_facts *word_overflow = ixs_facts_create(ctx);
  ixs_facts *partial_crossing = ixs_facts_create(ctx);
  ixs_facts *ceil_word_boundary = ixs_facts_create(ctx);
  ixs_facts *signed_i32_word = ixs_facts_create(ctx);
  ixs_facts *unsigned_i32_word = ixs_facts_create(ctx);
  ixs_facts *mixed_i32_word = ixs_facts_create(ctx);
  ixs_facts *overflow_i32_word = ixs_facts_create(ctx);
  ixs_facts *wide_word = ixs_facts_create(ctx);
  ixs_facts *widest_word = ixs_facts_create(ctx);
  ixs_facts *signed_i64_word = ixs_facts_create(ctx);
  ixs_facts *large_ceil_fit = ixs_facts_create(ctx);
  ixs_facts *large_ceil_bias_overflow = ixs_facts_create(ctx);
  ixs_facts *large_trunc_negative = ixs_facts_create(ctx);
  ixs_facts *dynamic_word = ixs_facts_create(ctx);
  ixs_facts *dynamic_overflow = ixs_facts_create(ctx);
  ixs_facts *dynamic_undefined = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);
  ixs_facts *empty = ixs_facts_create(ctx);
  ixs_node *rational_leaf = ixs_rat(ctx, 256, 3);
  ixs_node *divisor = ixs_sym(ctx, "rational_boundary_divisor");
  ixs_node *dynamic_quotient = ixs_div(ctx, x, divisor);
  ixs_node *dynamic_floor = ixs_floor(ctx, dynamic_quotient);
  ixs_node *dynamic_ceil = ixs_ceil(ctx, dynamic_quotient);
  ixs_node *dynamic_trunc = ixs_trunc(ctx, dynamic_quotient);
  ixs_rational_materialization_plan plan;
  size_t errors;

  rational_assume_integer_range(signed_boundary, x, -128, 127);
  rational_assume_integer_range(word_boundary, x, 0, 255);
  rational_assume_integer_range(word_overflow, x, 256, 256);
  rational_assume_integer_range(partial_crossing, x, 0, 256);
  rational_assume_integer_range(ceil_word_boundary, x, 255, 255);
  rational_assume_integer_range(signed_i32_word, x, -INT64_C(2147483647) - 1,
                                INT64_C(2147483647));
  rational_assume_integer_range(unsigned_i32_word, x, 0, INT64_C(4294967295));
  rational_assume_integer_range(mixed_i32_word, x, -1, INT64_C(4294967295));
  rational_assume_integer_range(overflow_i32_word, x, INT64_C(4294967296),
                                INT64_C(4294967296));
  rational_assume_integer_range(wide_word, x, 0, INT64_C(4611686018427387903));
  rational_assume_integer_range(widest_word, x, 0, INT64_MAX);
  rational_assume_integer_range(signed_i64_word, x, INT64_MIN, INT64_MAX);
  rational_assume_integer_range(large_ceil_fit, x, INT64_MAX - large_bias,
                                INT64_MAX - large_bias);
  rational_assume_integer_range(large_ceil_bias_overflow, x,
                                INT64_MAX - large_bias + 1,
                                INT64_MAX - large_bias + 1);
  rational_assume_integer_range(large_trunc_negative, x, INT64_MIN, -1);
  rational_assume_integer_range(dynamic_word, x, -128, 127);
  rational_assume_integer_range(dynamic_word, divisor, 1, 8);
  rational_assume_integer_range(dynamic_overflow, x, 128, 128);
  rational_assume_integer_range(dynamic_overflow, divisor, 2, 3);
  rational_assume_integer_range(dynamic_undefined, x, -128, 127);
  rational_assume_integer_range(dynamic_undefined, divisor, 0, 8);
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 10))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 5))));

  CHECK(test_ixs_check_rational_intermediates_facts(signed_boundary, floor_half,
                                                    8) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(signed_boundary, trunc_half,
                                                    8) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(signed_boundary, ceil_half,
                                                    8) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(signed_boundary, ceil_third,
                                                    8) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(signed_boundary, ceil_fifth,
                                                    8) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(word_boundary, floor_half,
                                                    8) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(word_boundary, ceil_half,
                                                    8) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(word_boundary, ceil_third,
                                                    8) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(word_overflow, floor_half,
                                                    8) == IXS_CHECK_FALSE);
  CHECK(test_ixs_check_rational_intermediates_facts(
            partial_crossing, floor_half, 8) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_rational_intermediates_facts(
            ceil_word_boundary, ceil_half, 8) == IXS_CHECK_TRUE);
  plan = ixs_plan_rational_materialization_facts(signed_boundary, half, 8);
  CHECK(plan.status == IXS_FACT_QUERY_COMPLETE && plan.check == IXS_CHECK_TRUE);
  CHECK(plan.denominator == 2 && !plan.numerator_nonnegative &&
        !plan.ceil_bias_safe);
  plan = ixs_plan_rational_materialization_facts(word_boundary, half, 8);
  CHECK(plan.status == IXS_FACT_QUERY_COMPLETE && plan.check == IXS_CHECK_TRUE);
  CHECK(plan.denominator == 2 && plan.numerator_nonnegative &&
        !plan.ceil_bias_safe);
  CHECK(test_ixs_check_rational_intermediates_facts(signed_i32_word, ceil_half,
                                                    32) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(signed_i32_word, ceil_third,
                                                    32) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(signed_i32_word, ceil_fifth,
                                                    32) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(
            unsigned_i32_word, ceil_half, 32) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(
            unsigned_i32_word, ceil_u32_max, 32) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(
            unsigned_i32_word, ceil_above_u32, 32) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(mixed_i32_word, ceil_half,
                                                    32) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_rational_intermediates_facts(
            overflow_i32_word, ceil_half, 32) == IXS_CHECK_FALSE);
  CHECK(test_ixs_check_rational_intermediates_facts(wide_word, floor_half,
                                                    62) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(widest_word, floor_half,
                                                    63) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(signed_i64_word, floor_half,
                                                    64) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(signed_i64_word, ceil_half,
                                                    64) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(signed_i64_word, trunc_half,
                                                    64) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(large_ceil_fit, large_ceil,
                                                    64) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(
            large_ceil_bias_overflow, large_ceil, 64) == IXS_CHECK_TRUE);
  plan = ixs_plan_rational_materialization_facts(large_ceil_fit, large_quotient,
                                                 64);
  CHECK(plan.status == IXS_FACT_QUERY_COMPLETE && plan.check == IXS_CHECK_TRUE);
  CHECK(plan.denominator == large_denominator && plan.numerator_nonnegative &&
        plan.ceil_bias_safe);
  plan = ixs_plan_rational_materialization_facts(large_ceil_bias_overflow,
                                                 large_quotient, 64);
  CHECK(plan.status == IXS_FACT_QUERY_COMPLETE && plan.check == IXS_CHECK_TRUE);
  CHECK(plan.denominator == large_denominator && plan.numerator_nonnegative &&
        !plan.ceil_bias_safe);
  CHECK(test_ixs_check_rational_intermediates_facts(
            large_trunc_negative, large_trunc, 64) == IXS_CHECK_TRUE);
  plan =
      ixs_plan_rational_materialization_facts(signed_i64_word, trunc_half, 64);
  CHECK(plan.status == IXS_FACT_QUERY_COMPLETE && plan.check == IXS_CHECK_TRUE);
  CHECK(plan.denominator == 1);
  CHECK(ixs_same_node(plan.numerator, trunc_half));
  CHECK(test_ixs_check_rational_intermediates_facts(dynamic_word, dynamic_floor,
                                                    8) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(dynamic_word, dynamic_ceil,
                                                    8) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(dynamic_word, dynamic_trunc,
                                                    8) == IXS_CHECK_TRUE);
  plan =
      ixs_plan_rational_materialization_facts(dynamic_word, dynamic_trunc, 8);
  CHECK(plan.status == IXS_FACT_QUERY_COMPLETE && plan.check == IXS_CHECK_TRUE);
  CHECK(plan.denominator == 1);
  CHECK(ixs_same_node(plan.numerator, dynamic_trunc));
  CHECK(test_ixs_check_rational_intermediates_facts(
            dynamic_overflow, dynamic_trunc, 8) == IXS_CHECK_FALSE);
  CHECK(test_ixs_check_rational_intermediates_facts(
            dynamic_undefined, dynamic_trunc, 8) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_rational_intermediates_facts(empty, x, 8) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(empty, rational_leaf, 8) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(contradictory, floor_half,
                                                    8) == IXS_CHECK_UNKNOWN);

  errors = ixs_ctx_nerrors(ctx);
  CHECK(test_ixs_check_rational_intermediates_facts(word_boundary, floor_half,
                                                    1) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == errors + 1u);
  ixs_ctx_clear_errors(ctx);
  errors = ixs_ctx_nerrors(ctx);
  CHECK(test_ixs_check_rational_intermediates_facts(word_boundary, floor_half,
                                                    65) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == errors + 1u);
  ixs_ctx_clear_errors(ctx);
  ixs_ctx_destroy(ctx);
}

static void test_public_rational_intermediate_compounds(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "rational_compound_x");
  ixs_node *y = ixs_sym(ctx, "rational_compound_y");
  ixs_node *guard = ixs_sym(ctx, "rational_compound_guard");
  ixs_node *half_x = ixs_div(ctx, x, ixs_int(ctx, 2));
  ixs_node *quarter_y = ixs_div(ctx, y, ixs_int(ctx, 4));
  ixs_node *condition =
      ixs_cmp(ctx, ixs_floor(ctx, ixs_div(ctx, guard, ixs_int(ctx, 2))),
              IXS_CMP_GT, ixs_int(ctx, 0));
  ixs_node *values[2] = {half_x, quarter_y};
  ixs_node *conditions[2] = {condition, ixs_true(ctx)};
  ixs_node *piecewise = ixs_pw(ctx, 2, values, conditions);
  ixs_node *sum = ixs_add(ctx, half_x, quarter_y);
  ixs_node *reciprocal_sum = ixs_mul(ctx, ixs_div(ctx, ixs_int(ctx, 1), y), x);
  ixs_node *product = ixs_mul(ctx, half_x, y);
  ixs_node *bitwise = ixs_and(ctx, half_x, ixs_int(ctx, 7));
  ixs_node *bitwise_island = ixs_add(ctx, bitwise, ixs_rat(ctx, 1, 2));
  ixs_facts *sum_boundary = ixs_facts_create(ctx);
  ixs_facts *sum_overflow = ixs_facts_create(ctx);
  ixs_facts *product_boundary = ixs_facts_create(ctx);
  ixs_facts *product_overflow = ixs_facts_create(ctx);
  ixs_facts *piecewise_fit = ixs_facts_create(ctx);
  ixs_facts *piecewise_overflow = ixs_facts_create(ctx);
  ixs_facts *bitwise_fit = ixs_facts_create(ctx);
  ixs_facts *bitwise_noninteger = ixs_facts_create(ctx);
  ixs_rational_materialization_plan plan;
  ixs_node *expected_sum_numerator =
      ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), x), y);

  rational_assume_integer_range(sum_boundary, x, 127, 127);
  rational_assume_integer_range(sum_boundary, y, 1, 1);
  rational_assume_integer_range(sum_overflow, x, 128, 128);
  rational_assume_integer_range(sum_overflow, y, 0, 0);
  rational_assume_integer_range(product_boundary, x, 255, 255);
  rational_assume_integer_range(product_boundary, y, 1, 1);
  rational_assume_integer_range(product_overflow, x, 128, 128);
  rational_assume_integer_range(product_overflow, y, 2, 2);
  rational_assume_integer_range(piecewise_fit, x, 0, 100);
  rational_assume_integer_range(piecewise_fit, y, 0, 200);
  rational_assume_integer_range(piecewise_fit, guard, 0, 255);
  rational_assume_integer_range(piecewise_overflow, x, 128, 128);
  rational_assume_integer_range(piecewise_overflow, y, 0, 200);
  rational_assume_integer_range(piecewise_overflow, guard, 0, 255);
  rational_assume_integer_range(bitwise_fit, x, 0, 62);
  CHECK(ixs_facts_assume_pred(bitwise_fit,
                              ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 2)),
                                      IXS_CMP_EQ, ixs_int(ctx, 0))));
  rational_assume_integer_range(bitwise_noninteger, x, 0, 63);

  /* Conditions are checked as separate materialization roots; they do not
   * participate in the common-denominator value numerator. */
  CHECK(test_ixs_check_rational_intermediates_facts(sum_boundary, sum, 8) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(sum_overflow, sum, 8) ==
        IXS_CHECK_FALSE);
  CHECK(test_ixs_check_rational_intermediates_facts(product_boundary, product,
                                                    8) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(product_overflow, product,
                                                    8) == IXS_CHECK_FALSE);
  CHECK(test_ixs_check_rational_intermediates_facts(
            product_boundary, reciprocal_sum, 8) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(piecewise_fit, piecewise,
                                                    8) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(
            piecewise_overflow, piecewise, 8) == IXS_CHECK_FALSE);
  CHECK(test_ixs_check_rational_intermediates_facts(bitwise_fit, bitwise_island,
                                                    8) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(
            bitwise_noninteger, bitwise_island, 8) == IXS_CHECK_UNKNOWN);
  plan = ixs_plan_rational_materialization_facts(sum_boundary, sum, 8);
  CHECK(plan.status == IXS_FACT_QUERY_COMPLETE && plan.check == IXS_CHECK_TRUE);
  CHECK(plan.denominator == 4);
  CHECK(ixs_same_node(plan.numerator, expected_sum_numerator));
  plan = ixs_plan_rational_materialization_facts(sum_overflow, sum, 8);
  CHECK(plan.status == IXS_FACT_QUERY_COMPLETE &&
        plan.check == IXS_CHECK_FALSE);
  CHECK(plan.numerator == NULL);
  CHECK(plan.denominator == 1);
  CHECK(!plan.numerator_nonnegative && !plan.ceil_bias_safe);
  ixs_ctx_destroy(ctx);
}

static void test_public_rational_intermediate_piecewise_conditions(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *guard = ixs_sym(ctx, "rational_condition_guard");
  ixs_node *selector = ixs_sym(ctx, "rational_condition_selector");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *half_guard = ixs_div(ctx, guard, ixs_int(ctx, 2));
  ixs_node *rational_condition =
      ixs_cmp(ctx, ixs_floor(ctx, half_guard), IXS_CMP_GT, zero);
  ixs_node *scalar_values[2] = {ixs_int(ctx, 3), ixs_int(ctx, 5)};
  ixs_node *direct_conditions[2] = {rational_condition, ixs_true(ctx)};
  ixs_node *direct = ixs_pw(ctx, 2, scalar_values, direct_conditions);
  ixs_node *predicate_values[2] = {rational_condition, ixs_true(ctx)};
  ixs_node *predicate_conditions[2] = {ixs_cmp(ctx, selector, IXS_CMP_GT, zero),
                                       ixs_true(ctx)};
  ixs_node *nested_condition =
      ixs_pw(ctx, 2, predicate_values, predicate_conditions);
  ixs_node *nested_conditions[2] = {nested_condition, ixs_true(ctx)};
  ixs_node *nested = ixs_pw(ctx, 2, scalar_values, nested_conditions);
  ixs_facts *fitting = ixs_facts_create(ctx);
  ixs_facts *overflow = ixs_facts_create(ctx);
  ixs_rational_materialization_plan plan;

  CHECK(ctx && guard && selector && half_guard && rational_condition &&
        direct && nested_condition && nested && fitting && overflow);
  CHECK(ixs_node_tag(direct) == IXS_PIECEWISE);
  CHECK(ixs_node_tag(nested_condition) == IXS_PIECEWISE);
  CHECK(ixs_node_tag(nested) == IXS_PIECEWISE);
  rational_assume_integer_range(fitting, guard, 255, 255);
  rational_assume_integer_range(fitting, selector, 0, 1);
  rational_assume_integer_range(overflow, guard, 256, 256);
  rational_assume_integer_range(overflow, selector, 0, 1);

  /* Branch values fit in one byte, but the condition is executable and its
   * rational numerator therefore participates in the materialization proof. */
  CHECK(test_ixs_check_rational_intermediates_facts(fitting, direct, 8) ==
        IXS_CHECK_TRUE);
  plan = ixs_plan_rational_materialization_facts(fitting, direct, 8);
  CHECK(plan.status == IXS_FACT_QUERY_COMPLETE &&
        plan.check == IXS_CHECK_TRUE && plan.numerator != NULL &&
        plan.denominator == 1);
  CHECK(test_ixs_check_rational_intermediates_facts(overflow, direct, 8) ==
        IXS_CHECK_FALSE);
  plan = ixs_plan_rational_materialization_facts(overflow, direct, 8);
  CHECK(plan.status == IXS_FACT_QUERY_COMPLETE &&
        plan.check == IXS_CHECK_FALSE && plan.numerator == NULL &&
        plan.denominator == 1);

  /* The same obligation is found recursively when a predicate-valued
   * Piecewise is itself used as the outer Piecewise condition. */
  CHECK(test_ixs_check_rational_intermediates_facts(fitting, nested, 8) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(overflow, nested, 8) ==
        IXS_CHECK_FALSE);

  ixs_ctx_destroy(ctx);
}

static void test_public_rational_intermediate_unsupported_extrema(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "rational_extrema_x");
  ixs_node *half_x = ixs_div(ctx, x, ixs_int(ctx, 2));
  ixs_node *constant = ixs_int(ctx, 7);
  ixs_node *rational_args[2] = {half_x, ixs_int(ctx, 1)};
  ixs_node *integral_args[2] = {x, ixs_int(ctx, 1)};
  ixs_node *maximum = ixs_max_many(ctx, 2, rational_args);
  ixs_node *minimum = ixs_min_many(ctx, 2, rational_args);
  ixs_node *maximum_predicate = ixs_cmp(ctx, maximum, IXS_CMP_EQ, constant);
  ixs_node *minimum_predicate = ixs_cmp(ctx, minimum, IXS_CMP_EQ, constant);
  ixs_node *integral_predicate =
      ixs_cmp(ctx, ixs_max_many(ctx, 2, integral_args), IXS_CMP_EQ, constant);
  ixs_facts *fitting = ixs_facts_create(ctx);
  ixs_facts *overflow = ixs_facts_create(ctx);
  ixs_rational_materialization_plan plan;

  rational_assume_integer_range(fitting, x, 0, 255);
  rational_assume_integer_range(overflow, x, 256, 256);

  CHECK(ixs_node_tag(maximum) == IXS_MAX);
  CHECK(ixs_node_tag(minimum) == IXS_MIN);
  CHECK(test_ixs_check_rational_intermediates_facts(fitting, maximum_predicate,
                                                    8) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_rational_intermediates_facts(fitting, minimum_predicate,
                                                    8) == IXS_CHECK_UNKNOWN);
  plan = ixs_plan_rational_materialization_facts(fitting, maximum_predicate, 8);
  CHECK(plan.status == IXS_FACT_QUERY_COMPLETE &&
        plan.check == IXS_CHECK_UNKNOWN && plan.numerator == NULL &&
        plan.denominator == 1);

  /* A conclusive child overflow remains conclusive across the unsupported
   * boundary. An integral extremum still has no executable materialization
   * plan, so it must not turn into a vacuous TRUE through the predicate. */
  CHECK(test_ixs_check_rational_intermediates_facts(overflow, maximum_predicate,
                                                    8) == IXS_CHECK_FALSE);
  CHECK(test_ixs_check_rational_intermediates_facts(fitting, integral_predicate,
                                                    8) == IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_public_rational_intermediate_piecewise_selector(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *work = ixs_sym(ctx, "rational_piecewise_work");
  ixs_node *lane = ixs_sym(ctx, "rational_piecewise_lane");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *condition = ixs_cmp(ctx, ixs_sub(ctx, work, one), IXS_CMP_LT, zero);
  ixs_node *values[] = {work, one};
  ixs_node *conditions[] = {condition, ixs_true(ctx)};
  ixs_node *selector = ixs_pw(ctx, 2, values, conditions);
  ixs_node *quarter_selector = ixs_mul(ctx, ixs_rat(ctx, 1, 4), selector);
  ixs_node *five_quarters_work = ixs_mul(ctx, ixs_rat(ctx, 5, 4), work);
  ixs_node *tile =
      ixs_floor(ctx, ixs_add(ctx, five_quarters_work, quarter_selector));
  ixs_node *stream = ixs_add(ctx, lane, tile);
  ixs_node *dma = ixs_add(ctx, lane, ixs_mul(ctx, ixs_int(ctx, 64), tile));
  ixs_node *assumptions[] = {
      ixs_cmp(ctx, work, IXS_CMP_GE, zero),
      ixs_cmp(ctx, ixs_sub(ctx, work, ixs_int(ctx, 2)), IXS_CMP_LE, zero),
      ixs_cmp(ctx, lane, IXS_CMP_GE, zero),
      ixs_cmp(ctx, ixs_sub(ctx, lane, ixs_int(ctx, 63)), IXS_CMP_LE, zero),
  };
  ixs_facts *facts =
      ixs_facts_create_preds(IXS_TEST_SESSION(ctx), assumptions, 4);
  ixs_node *simplified_stream;
  ixs_node *simplified_dma;

  CHECK(facts != NULL);
  simplified_stream = test_ixs_simplify_facts(facts, stream);
  simplified_dma = test_ixs_simplify_facts(facts, dma);
  CHECK(simplified_stream != NULL);
  CHECK(simplified_dma != NULL);
  CHECK(test_ixs_check_rational_intermediates_facts(facts, simplified_stream,
                                                    32) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(facts, simplified_dma,
                                                    32) == IXS_CHECK_TRUE);

  {
    ixs_node *predicate_source = ixs_sym(ctx, "rational_predicate_source");
    ixs_node *half = ixs_div(ctx, predicate_source, ixs_int(ctx, 2));
    ixs_node *predicate = ixs_cmp(ctx, half, IXS_CMP_GT, zero);
    ixs_node *nonnegative = ixs_cmp(ctx, predicate_source, IXS_CMP_GE, zero);
    ixs_node *conjunction = ixs_and(ctx, predicate, nonnegative);
    ixs_node *disjunction = ixs_or(ctx, predicate, nonnegative);
    ixs_facts *fitting = ixs_facts_create(ctx);
    ixs_facts *overflow = ixs_facts_create(ctx);
    rational_assume_integer_range(fitting, predicate_source, 0, 255);
    rational_assume_integer_range(overflow, predicate_source, 256, 256);

    CHECK(test_ixs_check_rational_intermediates_facts(fitting, predicate, 8) ==
          IXS_CHECK_TRUE);
    CHECK(test_ixs_check_rational_intermediates_facts(overflow, predicate, 8) ==
          IXS_CHECK_FALSE);
    CHECK(test_ixs_check_rational_intermediates_facts(
              overflow, ixs_not(ctx, predicate), 8) == IXS_CHECK_FALSE);
    CHECK(test_ixs_check_rational_intermediates_facts(fitting, conjunction,
                                                      8) == IXS_CHECK_TRUE);
    CHECK(test_ixs_check_rational_intermediates_facts(fitting, disjunction,
                                                      8) == IXS_CHECK_TRUE);
    CHECK(test_ixs_check_rational_intermediates_facts(overflow, conjunction,
                                                      8) == IXS_CHECK_FALSE);
    CHECK(test_ixs_check_rational_intermediates_facts(overflow, disjunction,
                                                      8) == IXS_CHECK_FALSE);
  }
  ixs_ctx_destroy(ctx);
}

static void test_public_rational_intermediate_growable_and_shared_dag(void) {
  enum { CASE_LIMIT = 1025, MEMO_CASES = 1024 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "rational_limit_x");
  ixs_node *guard = ixs_sym(ctx, "rational_limit_guard");
  ixs_node *zero_symbol = ixs_sym(ctx, "rational_limit_zero");
  ixs_node *half_x = ixs_div(ctx, x, ixs_int(ctx, 2));
  ixs_node *floor_half = ixs_floor(ctx, half_x);
  ixs_node *deep = half_x;
  ixs_node *power_base = x;
  ixs_node *power;
  ixs_node *case_values[CASE_LIMIT];
  ixs_node *case_conditions[CASE_LIMIT];
  ixs_node *memo_values[MEMO_CASES];
  ixs_node *memo_conditions[MEMO_CASES];
  ixs_node *too_many_cases;
  ixs_node *shared_piecewise;
  ixs_facts *facts = ixs_facts_create(ctx);
  uint32_t i;

  rational_assume_integer_range(facts, x, 0, 0);
  rational_assume_integer_range(facts, zero_symbol, 0, 0);
  for (i = 0; i < 70; i++)
    deep = ixs_floor(
        ctx, ixs_div(ctx, ixs_add(ctx, deep, zero_symbol), ixs_int(ctx, 2)));
  CHECK(test_ixs_check_rational_intermediates_facts(facts, deep, 16) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(facts, floor_half, 16) ==
        IXS_CHECK_TRUE);

  for (i = 1; i < 65; i++)
    power_base = ixs_mul(ctx, power_base, x);
  power = ixs_floor(ctx, ixs_div(ctx, power_base, ixs_int(ctx, 2)));
  CHECK(test_ixs_check_rational_intermediates_facts(facts, power, 16) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(facts, floor_half, 16) ==
        IXS_CHECK_TRUE);

  for (i = 0; i < CASE_LIMIT; i++) {
    case_values[i] = ixs_add(ctx, half_x, ixs_rat(ctx, 2 * (int64_t)i + 1, 2));
    case_conditions[i] =
        i + 1u == CASE_LIMIT
            ? ixs_true(ctx)
            : ixs_cmp(ctx, guard, IXS_CMP_GT, ixs_int(ctx, (int64_t)i));
  }
  too_many_cases = ixs_pw(ctx, CASE_LIMIT, case_values, case_conditions);
  CHECK(ixs_node_tag(too_many_cases) == IXS_PIECEWISE);
  CHECK(test_ixs_check_rational_intermediates_facts(facts, too_many_cases,
                                                    16) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(facts, floor_half, 16) ==
        IXS_CHECK_TRUE);

  deep = half_x;
  for (i = 0; i < 32; i++)
    deep = ixs_floor(
        ctx, ixs_div(ctx, ixs_add(ctx, deep, zero_symbol), ixs_int(ctx, 2)));
  for (i = 0; i < MEMO_CASES; i++) {
    memo_values[i] = ixs_add(ctx, deep, ixs_rat(ctx, 2 * (int64_t)i + 1, 2));
    memo_conditions[i] =
        i + 1u == MEMO_CASES
            ? ixs_true(ctx)
            : ixs_cmp(ctx, guard, IXS_CMP_GT, ixs_int(ctx, (int64_t)i));
  }
  shared_piecewise = ixs_pw(ctx, MEMO_CASES, memo_values, memo_conditions);
  CHECK(ixs_node_tag(shared_piecewise) == IXS_PIECEWISE);
  /* The shared value is analyzed once even though every arm references it. */
  CHECK(test_ixs_check_rational_intermediates_facts(facts, shared_piecewise,
                                                    16) == IXS_CHECK_TRUE);
  ixs_ctx_destroy(ctx);
}

static void test_public_rational_intermediate_mod_projection(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "rational_mod_x");
  ixs_node *half_x = ixs_div(ctx, x, ixs_int(ctx, 2));
  ixs_node *pow2_mod = ixs_mod(ctx, half_x, ixs_int(ctx, 4));
  ixs_node *other_mod = ixs_mod(ctx, half_x, ixs_int(ctx, 3));
  ixs_node *half = ixs_rat(ctx, 1, 2);
  ixs_node *pow2_island = ixs_add(ctx, pow2_mod, half);
  ixs_node *other_island = ixs_add(ctx, other_mod, half);
  ixs_node *reciprocal_island =
      ixs_div(ctx, half, ixs_mul(ctx, ixs_int(ctx, 2), x));
  ixs_facts *facts = ixs_facts_create(ctx);

  rational_assume_integer_range(facts, x, 600, 600);
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 2)),
                                      IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(test_ixs_check_rational_intermediates_facts(facts, pow2_island, 8) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_rational_intermediates_facts(facts, other_island, 8) ==
        IXS_CHECK_FALSE);
  CHECK(test_ixs_check_rational_intermediates_facts(facts, reciprocal_island,
                                                    8) == IXS_CHECK_TRUE);
  {
    ixs_rational_materialization_plan plan =
        ixs_plan_rational_materialization_facts(facts, reciprocal_island, 8);
    CHECK(plan.status == IXS_FACT_QUERY_COMPLETE &&
          plan.check == IXS_CHECK_TRUE);
    CHECK(plan.denominator == 2400);
    CHECK(ixs_same_node(plan.numerator, ixs_int(ctx, 1)));
  }
  ixs_ctx_destroy(ctx);
}

static void
test_public_rational_intermediate_order_independent_envelopes(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *u = ixs_sym(ctx, "rational_order_u");
  ixs_node *v = ixs_sym(ctx, "rational_order_v");
  ixs_node *huge = ixs_sym(ctx, "rational_mul_huge");
  ixs_node *zero = ixs_sym(ctx, "rational_mul_zero");
  ixs_node *trunc_input = ixs_sym(ctx, "rational_trunc_bias");
  ixs_node *deep_input = ixs_sym(ctx, "rational_deep_input");
  ixs_node *deep_zero = ixs_sym(ctx, "rational_deep_zero");
  ixs_node *two = ixs_int(ctx, 2);
  ixs_node *ordered = ixs_div(
      ctx, ixs_add(ctx, ixs_int(ctx, INT64_C(4000000000)), ixs_add(ctx, u, v)),
      two);
  ixs_node *zero_product = ixs_div(ctx, ixs_mul(ctx, huge, zero), two);
  ixs_node *selected_trunc =
      ixs_trunc(ctx, ixs_div(ctx, trunc_input, ixs_int(ctx, 256)));
  ixs_node *deep = ixs_div(ctx, deep_input, two);
  ixs_node *cycle = ixs_add(ctx, u, ixs_rat(ctx, 1, 2));
  ixs_facts *unsafe_add = ixs_facts_create(ctx);
  ixs_facts *safe_add = ixs_facts_create(ctx);
  ixs_facts *mul_facts = ixs_facts_create(ctx);
  ixs_facts *trunc_facts = ixs_facts_create(ctx);
  ixs_facts *deep_facts = ixs_facts_create(ctx);
  ixs_facts *cycle_facts = ixs_facts_create(ctx);
  unsigned i;

  rational_assume_integer_range(unsafe_add, u, -1000000000, -1000000000);
  rational_assume_integer_range(unsafe_add, v, 1000000000, 1000000000);
  CHECK(test_ixs_check_rational_intermediates_facts(unsafe_add, ordered, 32) ==
        IXS_CHECK_UNKNOWN);

  rational_assume_integer_range(safe_add, u, -200000000, -200000000);
  rational_assume_integer_range(safe_add, v, 200000000, 200000000);
  CHECK(test_ixs_check_rational_intermediates_facts(safe_add, ordered, 32) ==
        IXS_CHECK_TRUE);

  rational_assume_integer_range(mul_facts, huge, INT64_C(5000000000),
                                INT64_C(5000000000));
  rational_assume_integer_range(mul_facts, zero, 0, 0);
  CHECK(test_ixs_check_rational_intermediates_facts(mul_facts, zero_product,
                                                    32) == IXS_CHECK_FALSE);

  rational_assume_integer_range(trunc_facts, trunc_input, -128, 127);
  CHECK(test_ixs_check_rational_intermediates_facts(trunc_facts, selected_trunc,
                                                    8) == IXS_CHECK_TRUE);

  rational_assume_integer_range(deep_facts, deep_input, 0, 127);
  rational_assume_integer_range(deep_facts, deep_zero, 0, 0);
  for (i = 0; i < 80; i++)
    deep = ixs_floor(
        ctx, ixs_div(ctx, ixs_add(ctx, deep, deep_zero), ixs_int(ctx, 2)));
  CHECK(ixs_node_tag(deep) == IXS_FLOOR);
  CHECK(test_ixs_check_rational_intermediates_facts(deep_facts, deep, 16) ==
        IXS_CHECK_TRUE);

  rational_assume_integer_range(cycle_facts, u, 0, 127);
  {
    ixs_addterm *terms = (ixs_addterm *)(uintptr_t)cycle->u.add.terms;
    ixs_node *saved = terms[0].term;
    ixs_check_result cycle_result;
    terms[0].term = cycle;
    cycle_result =
        test_ixs_check_rational_intermediates_facts(cycle_facts, cycle, 16);
    terms[0].term = saved;
    CHECK(cycle_result == IXS_CHECK_UNKNOWN);
  }
  ixs_ctx_destroy(ctx);
}

static void test_public_rational_intermediate_oom_and_invalid(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "rational_oom_x");
  ixs_node *y = ixs_sym(ctx, "rational_oom_y");
  ixs_node *guard = ixs_sym(ctx, "rational_oom_guard");
  ixs_node *values[2] = {ixs_div(ctx, x, ixs_int(ctx, 2)),
                         ixs_div(ctx, y, ixs_int(ctx, 4))};
  ixs_node *conditions[2] = {ixs_cmp(ctx, guard, IXS_CMP_GT, ixs_int(ctx, 0)),
                             ixs_true(ctx)};
  ixs_node *piecewise = ixs_pw(ctx, 2, values, conditions);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_rational_materialization_plan plan;
  size_t errors;

  rational_assume_integer_range(facts, x, 0, 100);
  rational_assume_integer_range(facts, y, 0, 200);
  errors = ixs_ctx_nerrors(ctx);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  plan = ixs_plan_rational_materialization_facts(facts, piecewise, 8);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(plan.status == IXS_FACT_QUERY_OOM && plan.check == IXS_CHECK_UNKNOWN &&
        plan.numerator == NULL && plan.denominator == 1 &&
        !plan.numerator_nonnegative && !plan.ceil_bias_safe);
  CHECK(ixs_ctx_nerrors(ctx) == errors + 1u);
  plan = ixs_plan_rational_materialization_facts(facts, piecewise, 8);
  CHECK(plan.status == IXS_FACT_QUERY_COMPLETE &&
        plan.check == IXS_CHECK_TRUE && plan.numerator != NULL &&
        plan.denominator > 0);
  CHECK(test_ixs_check_rational_intermediates_facts(
            facts, ixs_sym(other, "rational_oom_foreign"), 8) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == errors + 2u);
  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static ixs_group_union_result
scalar_group_union_query(ixs_ctx *ctx, const ixs_predicate_group *groups,
                         const ixs_group_union_query *query) {
  ixs_node *predicates[16];
  size_t n_predicates = 0;
  size_t side;
  ixs_facts *facts;
  ixs_group_union_result result = {IXS_CHECK_UNKNOWN, 0};

  for (side = 0; side < 2; side++) {
    size_t group_index = side == 0 ? query->lhs_group : query->rhs_group;
    size_t predicate_index;
    for (predicate_index = 0;
         predicate_index < groups[group_index].n_predicates;
         predicate_index++) {
      ixs_node *predicate = groups[group_index].predicates[predicate_index];
      size_t existing;
      for (existing = 0; existing < n_predicates; existing++)
        if (predicates[existing] == predicate)
          break;
      if (existing == n_predicates) {
        CHECK(n_predicates < sizeof(predicates) / sizeof(predicates[0]));
        predicates[n_predicates++] = predicate;
      }
    }
  }
  facts = ixs_facts_create(ctx);
  CHECK(facts != NULL);
  CHECK(ixs_facts_assume_preds(facts, predicates, n_predicates));
  if (query->kind == IXS_GROUP_UNION_EQUIVALENT) {
    result.status = test_ixs_equivalent_facts(facts, query->lhs, query->rhs);
  } else if (query->kind == IXS_GROUP_UNION_FINITE_DOMAIN_EQUIVALENT) {
    ixs_finite_domain_query finite_query;
    ixs_finite_domain_result finite_result;
    size_t remaining_work = 1000000;
    finite_query.kind = IXS_FINITE_DOMAIN_EQUIVALENCE;
    finite_query.as.equivalence.lhs = query->lhs;
    finite_query.as.equivalence.rhs = query->rhs;
    finite_result =
        ixs_finite_domain_facts(facts, &finite_query, &remaining_work);
    CHECK(finite_result.status == IXS_FINITE_DOMAIN_COMPLETE);
    result.status = finite_result.check;
  } else if (test_ixs_constant_difference_facts(facts, query->lhs, query->rhs,
                                                &result.difference)) {
    result.status = IXS_CHECK_TRUE;
  }
  return result;
}

static void test_public_group_union_scalar_oracle_size(size_t n_groups) {
  enum { MAX_GROUPS = 17, MAX_QUERIES = MAX_GROUPS * (MAX_GROUPS - 1) };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *shared = ixs_sym(ctx, "group_union_shared");
  ixs_node *shared_lower = ixs_cmp(ctx, shared, IXS_CMP_GE, ixs_int(ctx, -100));
  ixs_node *shared_upper = ixs_cmp(ctx, shared, IXS_CMP_LE, ixs_int(ctx, 100));
  ixs_node *values[MAX_GROUPS];
  ixs_node *predicate_storage[MAX_GROUPS][3];
  ixs_predicate_group groups[MAX_GROUPS];
  ixs_group_union_query queries[MAX_QUERIES];
  ixs_group_union_result results[MAX_QUERIES];
  size_t n_queries = 0;
  size_t remaining_work = 1000000;
  size_t i;

  CHECK(n_groups <= MAX_GROUPS);
  for (i = 0; i < n_groups; i++) {
    char name[48];
    snprintf(name, sizeof(name), "group_union_value_%u_%u", (unsigned)n_groups,
             (unsigned)i);
    values[i] = ixs_sym(ctx, name);
    predicate_storage[i][0] = shared_lower;
    predicate_storage[i][1] = shared_upper;
    predicate_storage[i][2] =
        ixs_cmp(ctx, values[i], IXS_CMP_EQ, ixs_int(ctx, (int64_t)(4u * i)));
    groups[i].predicates = predicate_storage[i];
    groups[i].n_predicates = 3;
  }
  for (i = 0; i < n_groups; i++) {
    size_t j;
    for (j = i + 1u; j < n_groups; j++) {
      int64_t delta = (int64_t)(4u * (j - i));
      queries[n_queries++] =
          (ixs_group_union_query){i, j, IXS_GROUP_UNION_EQUIVALENT, values[j],
                                  ixs_add(ctx, values[i], ixs_int(ctx, delta))};
      queries[n_queries++] = (ixs_group_union_query){
          i, j, IXS_GROUP_UNION_CONSTANT_DIFFERENCE, values[j], values[i]};
    }
  }
  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), groups, n_groups,
                                 queries, n_queries, results,
                                 &remaining_work) == IXS_GROUP_UNION_COMPLETE);
  CHECK(remaining_work < 1000000);
  for (i = 0; i < n_queries; i++) {
    ixs_group_union_result scalar =
        scalar_group_union_query(ctx, groups, &queries[i]);
    CHECK(results[i].status == scalar.status);
    if (scalar.status == IXS_CHECK_TRUE &&
        queries[i].kind == IXS_GROUP_UNION_CONSTANT_DIFFERENCE)
      CHECK(results[i].difference == scalar.difference);
  }
  ixs_ctx_destroy(ctx);
}

static ixs_node *group_union_complex_repeated_operand(ixs_ctx *ctx) {
  ixs_node *x = ixs_sym(ctx, "group_union_admission_x");
  ixs_node *y = ixs_sym(ctx, "group_union_admission_y");
  ixs_node *guard = ixs_sym(ctx, "group_union_admission_guard");
  ixs_node *sum = ixs_int(ctx, 0);
  ixs_node *values[2];
  ixs_node *conditions[2];
  size_t index;

  for (index = 0; index < 7; index++) {
    ixs_node *linear =
        ixs_add(ctx, x, ixs_mul(ctx, ixs_int(ctx, (int64_t)index + 1), y));
    ixs_node *rounded;
    linear = ixs_add(ctx, linear, ixs_int(ctx, (int64_t)index));
    rounded = ixs_trunc(ctx, ixs_div(ctx, linear, ixs_int(ctx, 257 + index)));
    sum = ixs_add(ctx, sum,
                  ixs_mul(ctx, ixs_int(ctx, (int64_t)index + 1), rounded));
  }
  values[0] = sum;
  values[1] = ixs_add(ctx, sum, y);
  conditions[0] = ixs_cmp(ctx, guard, IXS_CMP_GT, ixs_int(ctx, 0));
  conditions[1] = ixs_true(ctx);
  return ixs_pw(ctx, 2, values, conditions);
}

static void test_public_group_union_dag_work_admission(void) {
  enum {
    GROUP_COUNT = 64,
    PAIR_COUNT = GROUP_COUNT * (GROUP_COUNT - 1) / 2,
    QUERIES_PER_PAIR = 3,
    DENSE_QUERY_COUNT = PAIR_COUNT * QUERIES_PER_PAIR,
    SPARSE_QUERY_COUNT = (GROUP_COUNT - 1) * QUERIES_PER_PAIR
  };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *complex = group_union_complex_repeated_operand(ctx);
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *predicate_storage[GROUP_COUNT][2];
  ixs_predicate_group groups[GROUP_COUNT];
  ixs_group_union_query dense_queries[DENSE_QUERY_COUNT];
  ixs_group_union_result dense_results[DENSE_QUERY_COUNT];
  ixs_group_union_query sparse_queries[SPARSE_QUERY_COUNT];
  ixs_group_union_result sparse_results[SPARSE_QUERY_COUNT];
  size_t dense_count = 0;
  size_t sparse_count = 0;
  size_t remaining_work = 1024 * 1024;
  size_t group;

  CHECK(ctx && complex && zero && one);
  for (group = 0; group < GROUP_COUNT; group++) {
    char name[48];
    ixs_node *symbol;
    snprintf(name, sizeof(name), "group_union_admission_group_%zu", group);
    symbol = ixs_sym(ctx, name);
    predicate_storage[group][0] =
        ixs_cmp(ctx, symbol, IXS_CMP_EQ, ixs_int(ctx, (int64_t)group));
    predicate_storage[group][1] =
        ixs_cmp(ctx, complex, IXS_CMP_NE, ixs_int(ctx, (int64_t)group + 1024));
    groups[group].predicates = predicate_storage[group];
    groups[group].n_predicates = 2;
  }
  for (group = 0; group < GROUP_COUNT; group++) {
    size_t peer;
    for (peer = group + 1u; peer < GROUP_COUNT; peer++) {
      dense_queries[dense_count++] = (ixs_group_union_query){
          group, peer, IXS_GROUP_UNION_EQUIVALENT, zero, zero};
      dense_queries[dense_count++] = (ixs_group_union_query){
          group, peer, IXS_GROUP_UNION_EQUIVALENT, one, one};
      dense_queries[dense_count++] = (ixs_group_union_query){
          group, peer, IXS_GROUP_UNION_CONSTANT_DIFFERENCE, zero, zero};
    }
  }
  CHECK(dense_count == DENSE_QUERY_COUNT && PAIR_COUNT == 2016);
  for (group = 0; group < DENSE_QUERY_COUNT; group++)
    dense_results[group] =
        (ixs_group_union_result){IXS_CHECK_TRUE, (int64_t)group + 1};
  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), groups, GROUP_COUNT,
                                 dense_queries, DENSE_QUERY_COUNT,
                                 dense_results,
                                 &remaining_work) == IXS_GROUP_UNION_EXHAUSTED);
  CHECK(remaining_work == 0);
  for (group = 0; group < DENSE_QUERY_COUNT; group++)
    CHECK(dense_results[group].status == IXS_CHECK_UNKNOWN &&
          dense_results[group].difference == 0);

  for (group = 0; group + 1u < GROUP_COUNT; group++) {
    sparse_queries[sparse_count++] = (ixs_group_union_query){
        group, group + 1u, IXS_GROUP_UNION_EQUIVALENT, zero, zero};
    sparse_queries[sparse_count++] = (ixs_group_union_query){
        group, group + 1u, IXS_GROUP_UNION_EQUIVALENT, one, one};
    sparse_queries[sparse_count++] = (ixs_group_union_query){
        group, group + 1u, IXS_GROUP_UNION_CONSTANT_DIFFERENCE, zero, zero};
  }
  CHECK(sparse_count == SPARSE_QUERY_COUNT);
  remaining_work = 4 * 1024 * 1024;
  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), groups, GROUP_COUNT,
                                 sparse_queries, SPARSE_QUERY_COUNT,
                                 sparse_results,
                                 &remaining_work) == IXS_GROUP_UNION_COMPLETE);
  CHECK(remaining_work < 4 * 1024 * 1024);
  for (group = 0; group < SPARSE_QUERY_COUNT; group++) {
    CHECK(sparse_results[group].status == IXS_CHECK_TRUE);
    if (sparse_queries[group].kind == IXS_GROUP_UNION_CONSTANT_DIFFERENCE)
      CHECK(sparse_results[group].difference == 0);
  }
  {
    ixs_predicate_group empty_groups[2] = {{NULL, 0}, {NULL, 0}};
    ixs_group_union_query query = {0, 1, IXS_GROUP_UNION_EQUIVALENT, complex,
                                   complex};
    ixs_group_union_result result = {IXS_CHECK_UNKNOWN, 0};
    remaining_work = 1;
    CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), empty_groups, 2,
                                   &query, 1, &result, &remaining_work) ==
          IXS_GROUP_UNION_COMPLETE);
    CHECK(remaining_work == 0 && result.status == IXS_CHECK_TRUE);
  }
  ixs_ctx_destroy(ctx);
}

static void test_public_group_union_sixty_five_group_registry(void) {
  enum {
    GROUP_COUNT = 65,
    PAIR_GROUP_COUNT = 64,
    PAIR_COUNT = PAIR_GROUP_COUNT * (PAIR_GROUP_COUNT - 1) / 2,
    QUERY_COUNT = PAIR_COUNT + 1
  };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *shared = ixs_sym(ctx, "group_union_large_shared");
  ixs_node *shared_bound = ixs_cmp(ctx, shared, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *values[GROUP_COUNT];
  ixs_node *predicate_storage[GROUP_COUNT][2];
  ixs_predicate_group groups[GROUP_COUNT];
  ixs_group_union_query queries[QUERY_COUNT];
  ixs_group_union_result results[QUERY_COUNT];
  size_t remaining_work = 1000000;
  size_t query_count = 0;
  size_t i;

  CHECK(ctx && shared && shared_bound);
  for (i = 0; i < GROUP_COUNT; i++) {
    char name[48];
    snprintf(name, sizeof(name), "group_union_large_value_%zu", i);
    values[i] = ixs_sym(ctx, name);
    predicate_storage[i][0] = shared_bound;
    predicate_storage[i][1] =
        ixs_cmp(ctx, values[i], IXS_CMP_EQ, ixs_int(ctx, (int64_t)i));
    groups[i].predicates = predicate_storage[i];
    groups[i].n_predicates = 2;
  }
  for (i = 0; i < PAIR_GROUP_COUNT; i++) {
    size_t j;
    for (j = i + 1u; j < PAIR_GROUP_COUNT; j++) {
      int64_t difference = (int64_t)(j - i);
      if ((query_count & 1u) == 0u) {
        queries[query_count] = (ixs_group_union_query){
            i, j, IXS_GROUP_UNION_CONSTANT_DIFFERENCE, values[j], values[i]};
      } else {
        queries[query_count] = (ixs_group_union_query){
            i, j, IXS_GROUP_UNION_EQUIVALENT, values[j],
            ixs_add(ctx, values[i], ixs_int(ctx, difference))};
      }
      query_count++;
    }
  }
  queries[query_count++] = (ixs_group_union_query){
      0, GROUP_COUNT - 1u, IXS_GROUP_UNION_CONSTANT_DIFFERENCE,
      values[GROUP_COUNT - 1u], values[0]};
  CHECK(query_count == QUERY_COUNT && PAIR_COUNT == 2016);
  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), groups, GROUP_COUNT,
                                 queries, query_count, results,
                                 &remaining_work) == IXS_GROUP_UNION_COMPLETE);
  CHECK(remaining_work < 1000000);
  for (i = 0; i < query_count; i++) {
    CHECK(results[i].status == IXS_CHECK_TRUE);
    if (queries[i].kind == IXS_GROUP_UNION_CONSTANT_DIFFERENCE)
      CHECK(results[i].difference ==
            (int64_t)(queries[i].rhs_group - queries[i].lhs_group));
  }
  ixs_ctx_destroy(ctx);
}

static void test_public_group_union_cross_closure_and_isolation(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "group_union_cross_x");
  ixs_node *y = ixs_sym(ctx, "group_union_cross_y");
  ixs_node *z = ixs_sym(ctx, "group_union_cross_z");
  ixs_node *bad = ixs_sym(ctx, "group_union_cross_bad");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *group0_predicates[1] = {
      ixs_cmp(ctx, ixs_add(ctx, x, y), IXS_CMP_GE, zero)};
  ixs_node *group1_predicates[2] = {
      ixs_cmp(ctx, ixs_add(ctx, y, z), IXS_CMP_EQ, zero),
      ixs_cmp(ctx, z, IXS_CMP_EQ, zero)};
  ixs_node *group2_predicates[2] = {
      ixs_cmp(ctx, bad, IXS_CMP_GE, ixs_int(ctx, 1)),
      ixs_cmp(ctx, bad, IXS_CMP_LE, zero)};
  ixs_predicate_group groups[3] = {
      {group0_predicates, 1}, {group1_predicates, 2}, {group2_predicates, 2}};
  ixs_group_union_query queries[4] = {
      {0, 1, IXS_GROUP_UNION_EQUIVALENT, ixs_max(ctx, x, zero), x},
      {0, 1, IXS_GROUP_UNION_CONSTANT_DIFFERENCE, ixs_add(ctx, x, y), x},
      {0, 2, IXS_GROUP_UNION_EQUIVALENT, ixs_max(ctx, x, zero), x},
      {0, 1, IXS_GROUP_UNION_EQUIVALENT, x, ixs_add(ctx, x, ixs_int(ctx, 1))}};
  ixs_group_union_result results[4];
  size_t remaining_work = 10000;
  size_t i;

  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), groups, 3, queries, 4,
                                 results,
                                 &remaining_work) == IXS_GROUP_UNION_COMPLETE);
  for (i = 0; i < 4; i++) {
    ixs_group_union_result scalar =
        scalar_group_union_query(ctx, groups, &queries[i]);
    CHECK(results[i].status == scalar.status);
    if (scalar.status == IXS_CHECK_TRUE &&
        queries[i].kind == IXS_GROUP_UNION_CONSTANT_DIFFERENCE)
      CHECK(results[i].difference == scalar.difference);
  }
  CHECK(results[0].status == IXS_CHECK_TRUE);
  CHECK(results[1].status == IXS_CHECK_TRUE && results[1].difference == 0);
  CHECK(results[2].status == IXS_CHECK_UNKNOWN);
  CHECK(results[3].status == IXS_CHECK_FALSE);
  ixs_ctx_destroy(ctx);
}

static void test_public_group_union_finite_domain_and_budget(void) {
  static const char finite_text[] =
      "Piecewise((1, x*(x - 1)*(x - 2)*(x - 3) == 0), (2, True))";
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *finite = ixs_parse_expr(ctx, finite_text, sizeof(finite_text) - 1u);
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *predicates[2] = {ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
                             ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 3))};
  ixs_predicate_group groups[2] = {{&predicates[0], 1}, {&predicates[1], 1}};
  ixs_group_union_query query = {0, 1, IXS_GROUP_UNION_FINITE_DOMAIN_EQUIVALENT,
                                 finite, one};
  ixs_group_union_result result;
  ixs_group_union_result scalar;
  size_t remaining_work = 1000;
  size_t used;

  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), groups, 2, &query, 1,
                                 &result,
                                 &remaining_work) == IXS_GROUP_UNION_COMPLETE);
  CHECK(result.status == IXS_CHECK_TRUE);
  scalar = scalar_group_union_query(ctx, groups, &query);
  CHECK(result.status == scalar.status);
  used = 1000 - remaining_work;
  CHECK(used > 4);

  remaining_work = used - 1u;
  result.status = IXS_CHECK_TRUE;
  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), groups, 2, &query, 1,
                                 &result,
                                 &remaining_work) == IXS_GROUP_UNION_EXHAUSTED);
  CHECK(result.status == IXS_CHECK_UNKNOWN && result.difference == 0);
  ixs_ctx_destroy(ctx);
}

static void test_public_group_union_finite_constant_difference(void) {
  static const char finite_text[] =
      "Piecewise((1, x*(x - 1)*(x - 2)*(x - 3) == 0), (2, True))";
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *finite = ixs_parse_expr(ctx, finite_text, sizeof(finite_text) - 1u);
  ixs_node *predicates[2] = {ixs_cmp(ctx, x, IXS_CMP_GE, zero),
                             ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 3))};
  ixs_predicate_group groups[2] = {{&predicates[0], 1}, {&predicates[1], 1}};
  ixs_group_union_query exact = {0, 1, IXS_GROUP_UNION_CONSTANT_DIFFERENCE,
                                 ixs_add(ctx, x, ixs_int(ctx, 7)), x};
  ixs_group_union_query finite_exact = exact;
  ixs_group_union_query queries[2];
  ixs_group_union_result results[2];
  size_t exact_work = 1000;
  size_t finite_exact_work = 1000;
  size_t remaining_work = 1000;
  size_t used;

  finite_exact.kind = IXS_GROUP_UNION_FINITE_DOMAIN_CONSTANT_DIFFERENCE;
  CHECK(ctx && x && zero && finite && exact.lhs);
  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), groups, 2, &exact, 1,
                                 results,
                                 &exact_work) == IXS_GROUP_UNION_COMPLETE);
  CHECK(results[0].status == IXS_CHECK_TRUE && results[0].difference == 7);
  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), groups, 2,
                                 &finite_exact, 1, results,
                                 &finite_exact_work) ==
        IXS_GROUP_UNION_COMPLETE);
  CHECK(results[0].status == IXS_CHECK_TRUE && results[0].difference == 7);
  CHECK(exact_work == finite_exact_work);

  queries[0] = finite_exact;
  queries[1] = (ixs_group_union_query){
      0, 1, IXS_GROUP_UNION_FINITE_DOMAIN_CONSTANT_DIFFERENCE, finite, zero};
  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), groups, 2, queries, 2,
                                 results,
                                 &remaining_work) == IXS_GROUP_UNION_COMPLETE);
  CHECK(results[0].status == IXS_CHECK_TRUE && results[0].difference == 7);
  CHECK(results[1].status == IXS_CHECK_TRUE && results[1].difference == 1);
  used = 1000 - remaining_work;
  CHECK(used >= 4u);

  remaining_work = used - 1u;
  results[0] = (ixs_group_union_result){IXS_CHECK_TRUE, 91};
  results[1] = (ixs_group_union_result){IXS_CHECK_TRUE, 92};
  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), groups, 2, queries, 2,
                                 results,
                                 &remaining_work) == IXS_GROUP_UNION_EXHAUSTED);
  CHECK(remaining_work == 3u);
  CHECK(results[0].status == IXS_CHECK_UNKNOWN && results[0].difference == 0 &&
        results[1].status == IXS_CHECK_UNKNOWN && results[1].difference == 0);

  remaining_work = used;
  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), groups, 2, queries, 2,
                                 results,
                                 &remaining_work) == IXS_GROUP_UNION_COMPLETE);
  CHECK(remaining_work == 0u && results[1].status == IXS_CHECK_TRUE &&
        results[1].difference == 1);

  queries[0] = (ixs_group_union_query){
      0, 1, IXS_GROUP_UNION_FINITE_DOMAIN_CONSTANT_DIFFERENCE, x, zero};
  remaining_work = 1000;
  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), groups, 2, queries, 1,
                                 results,
                                 &remaining_work) == IXS_GROUP_UNION_COMPLETE);
  CHECK(results[0].status == IXS_CHECK_UNKNOWN && results[0].difference == 0);

  {
    ixs_node *contradiction = ixs_false(ctx);
    ixs_predicate_group isolated_groups[3] = {
        groups[0], groups[1], {&contradiction, 1}};
    ixs_group_union_query isolated_queries[2] = {
        {0, 1, IXS_GROUP_UNION_FINITE_DOMAIN_CONSTANT_DIFFERENCE, finite, zero},
        {0, 2, IXS_GROUP_UNION_FINITE_DOMAIN_CONSTANT_DIFFERENCE, finite,
         zero}};
    remaining_work = 1000;
    CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), isolated_groups, 3,
                                   isolated_queries, 2, results,
                                   &remaining_work) ==
          IXS_GROUP_UNION_COMPLETE);
    CHECK(results[0].status == IXS_CHECK_TRUE && results[0].difference == 1);
    CHECK(results[1].status == IXS_CHECK_UNKNOWN && results[1].difference == 0);
  }

  ixs_ctx_destroy(ctx);
}

static void test_public_group_union_signed_wrap_successor(void) {
  static const char lhs_text[] =
      "-2147483648 + Mod(2147483648 + raw0 + raw1, 4294967296)";
  static const char rhs_text[] =
      "-2147483648 + Mod(1 + Mod(2147483648 + raw0 + raw1, "
      "4294967296), 4294967296)";
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *raw0 = ixs_sym(ctx, "raw0");
  ixs_node *raw1 = ixs_sym(ctx, "raw1");
  ixs_node *lhs = parse_bounds_expr(ctx, lhs_text);
  ixs_node *rhs = parse_bounds_expr(ctx, rhs_text);
  ixs_node *raw0_lower = parse_bounds_pred(ctx, "2147483648 + raw0 >= 0");
  ixs_node *raw0_upper = parse_bounds_pred(ctx, "-2147483647 + raw0 <= 0");
  ixs_node *raw1_lower = parse_bounds_pred(ctx, "2147483648 + raw1 >= 0");
  ixs_node *raw1_upper = parse_bounds_pred(ctx, "-2147483647 + raw1 <= 0");
  ixs_node *lhs_lower = ixs_cmp(ctx, lhs, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *lhs_upper = ixs_cmp(ctx, lhs, IXS_CMP_LE, ixs_int(ctx, 1073741823));
  ixs_node *rhs_lower = ixs_cmp(ctx, rhs, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *rhs_upper = ixs_cmp(ctx, rhs, IXS_CMP_LE, ixs_int(ctx, 1073741823));
  ixs_node *group0_predicates[6] = {raw0_lower, raw0_upper, raw1_lower,
                                    raw1_upper, lhs_lower,  lhs_upper};
  ixs_node *group1_predicates[6] = {raw0_lower, raw0_upper, raw1_lower,
                                    raw1_upper, rhs_lower,  rhs_upper};
  ixs_predicate_group groups[2] = {{group0_predicates, 6},
                                   {group1_predicates, 6}};
  ixs_group_union_query queries[3] = {
      {0, 1, IXS_GROUP_UNION_CONSTANT_DIFFERENCE, rhs, lhs},
      {0, 1, IXS_GROUP_UNION_FINITE_DOMAIN_EQUIVALENT, rhs,
       ixs_add(ctx, lhs, ixs_int(ctx, 1))},
      {0, 1, IXS_GROUP_UNION_FINITE_DOMAIN_CONSTANT_DIFFERENCE, rhs, lhs}};
  ixs_group_union_result results[3];
  ixs_group_union_result scalar;
  size_t remaining_work = 1000000;

  CHECK(ctx && raw0 && raw1 && lhs && rhs && queries[1].rhs);
  scalar = scalar_group_union_query(ctx, groups, &queries[0]);
  CHECK(scalar.status == IXS_CHECK_TRUE && scalar.difference == 1);
  scalar = scalar_group_union_query(ctx, groups, &queries[1]);
  CHECK(scalar.status == IXS_CHECK_TRUE);
  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), groups, 2, queries, 3,
                                 results,
                                 &remaining_work) == IXS_GROUP_UNION_COMPLETE);
  CHECK(results[0].status == IXS_CHECK_TRUE && results[0].difference == 1);
  CHECK(results[1].status == IXS_CHECK_TRUE && results[1].difference == 0);
  CHECK(results[2].status == IXS_CHECK_TRUE && results[2].difference == 1);
  ixs_ctx_destroy(ctx);
}

static void test_public_equivalence_common_guard_aligned_packet(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *origin = ixs_sym(ctx, "common_guard_origin");
  ixs_node *limit = ixs_sym(ctx, "common_guard_limit");
  ixs_node *row = ixs_sym(ctx, "common_guard_row");
  ixs_node *row_limit = ixs_sym(ctx, "common_guard_row_limit");
  ixs_node *next = ixs_add(ctx, origin, ixs_int(ctx, 1));
  ixs_node *outer = ixs_cmp(ctx, row, IXS_CMP_LT, row_limit);
  ixs_node *lhs = ixs_and(ctx, outer, ixs_cmp(ctx, origin, IXS_CMP_LT, limit));
  ixs_node *rhs = ixs_and(ctx, outer, ixs_cmp(ctx, next, IXS_CMP_LT, limit));
  ixs_node *predicates[10] = {
      ixs_cmp(ctx, origin, IXS_CMP_GE, ixs_int(ctx, INT32_MIN)),
      ixs_cmp(ctx, origin, IXS_CMP_LE, ixs_int(ctx, INT32_MAX)),
      ixs_cmp(ctx, ixs_mod(ctx, origin, ixs_int(ctx, 4)), IXS_CMP_EQ,
              ixs_int(ctx, 0)),
      ixs_cmp(ctx, next, IXS_CMP_GE, ixs_int(ctx, INT32_MIN)),
      ixs_cmp(ctx, next, IXS_CMP_LE, ixs_int(ctx, INT32_MAX)),
      ixs_cmp(ctx, limit, IXS_CMP_GE, ixs_int(ctx, INT32_MIN)),
      ixs_cmp(ctx, limit, IXS_CMP_LE, ixs_int(ctx, INT32_MAX)),
      ixs_cmp(ctx, ixs_mod(ctx, limit, ixs_int(ctx, 4)), IXS_CMP_EQ,
              ixs_int(ctx, 0)),
      ixs_cmp(ctx, row, IXS_CMP_GE, ixs_int(ctx, INT32_MIN)),
      ixs_cmp(ctx, row_limit, IXS_CMP_LE, ixs_int(ctx, INT32_MAX))};
  ixs_facts *facts = ixs_facts_create(ctx);

  CHECK(ctx && origin && limit && row && row_limit && next && outer && lhs &&
        rhs && facts);
  CHECK(ixs_facts_assume_preds(facts, predicates, 10));
  CHECK(test_ixs_equivalent_facts(facts, lhs, rhs) == IXS_CHECK_TRUE);
  ixs_ctx_destroy(ctx);
}

static void test_public_group_union_aligned_slot_packet(void) {
  enum { GROUP_COUNT = 4, COMMON_COUNT = 10, QUERY_COUNT = 6 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *raw = ixs_sym(ctx, "raw0");
  ixs_node *limit = ixs_sym(ctx, "limit");
  ixs_node *row = ixs_sym(ctx, "row");
  ixs_node *row_limit = ixs_sym(ctx, "row_limit");
  ixs_node *common[COMMON_COUNT] = {
      parse_bounds_pred(ctx, "2147483648 + raw0 >= 0"),
      parse_bounds_pred(ctx, "-2147483647 + raw0 <= 0"),
      parse_bounds_pred(ctx, "Mod(raw0, 4) == 0"),
      parse_bounds_pred(ctx, "2147483648 + limit >= 0"),
      parse_bounds_pred(ctx, "-2147483647 + limit <= 0"),
      parse_bounds_pred(ctx, "Mod(limit, 4) == 0"),
      parse_bounds_pred(ctx, "2147483648 + row >= 0"),
      parse_bounds_pred(ctx, "-2147483647 + row <= 0"),
      parse_bounds_pred(ctx, "2147483648 + row_limit >= 0"),
      parse_bounds_pred(ctx, "-2147483647 + row_limit <= 0")};
  ixs_node *predicate_storage[GROUP_COUNT][COMMON_COUNT + 2];
  ixs_node *addresses[GROUP_COUNT];
  ixs_node *masks[GROUP_COUNT];
  ixs_predicate_group groups[GROUP_COUNT];
  ixs_group_union_query queries[QUERY_COUNT];
  ixs_group_union_result results[QUERY_COUNT];
  ixs_node *outer = ixs_cmp(ctx, row, IXS_CMP_LT, row_limit);
  size_t remaining_work = 1000000;
  size_t query_count = 0;
  size_t group;

  CHECK(ctx && raw && limit && row && row_limit && outer);
  for (group = 0; group < GROUP_COUNT; group++) {
    size_t predicate;
    addresses[group] =
        group == 0 ? raw : ixs_add(ctx, raw, ixs_int(ctx, (int64_t)group));
    masks[group] =
        ixs_and(ctx, outer, ixs_cmp(ctx, addresses[group], IXS_CMP_LT, limit));
    for (predicate = 0; predicate < COMMON_COUNT; predicate++)
      predicate_storage[group][predicate] = common[predicate];
    if (group == 0) {
      groups[group] =
          (ixs_predicate_group){predicate_storage[group], COMMON_COUNT};
    } else {
      char lower[64];
      char upper[64];
      (void)snprintf(lower, sizeof(lower), "2147483648 + %zu + raw0 >= 0",
                     group);
      (void)snprintf(upper, sizeof(upper), "-2147483647 + %zu + raw0 <= 0",
                     group);
      predicate_storage[group][COMMON_COUNT] = parse_bounds_pred(ctx, lower);
      predicate_storage[group][COMMON_COUNT + 1u] =
          parse_bounds_pred(ctx, upper);
      groups[group] =
          (ixs_predicate_group){predicate_storage[group], COMMON_COUNT + 2u};
    }
  }
  for (group = 1; group < GROUP_COUNT; group++) {
    queries[query_count++] =
        (ixs_group_union_query){0, group, IXS_GROUP_UNION_CONSTANT_DIFFERENCE,
                                addresses[group], addresses[0]};
    queries[query_count++] = (ixs_group_union_query){
        0, group, IXS_GROUP_UNION_FINITE_DOMAIN_EQUIVALENT, masks[group],
        masks[0]};
  }
  CHECK(query_count == QUERY_COUNT);
  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), groups, GROUP_COUNT,
                                 queries, QUERY_COUNT, results,
                                 &remaining_work) == IXS_GROUP_UNION_COMPLETE);
  for (group = 0; group < QUERY_COUNT; group++) {
    CHECK(results[group].status == IXS_CHECK_TRUE);
    if (queries[group].kind == IXS_GROUP_UNION_CONSTANT_DIFFERENCE)
      CHECK(results[group].difference == (int64_t)queries[group].rhs_group);
  }
  ixs_ctx_destroy(ctx);
}

static void test_public_group_union_negative_remainder_successor(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *raw = ixs_sym(ctx, "raw0");
  ixs_node *lhs = parse_bounds_expr(ctx, "raw0 + 4*ceiling(-1/4*raw0)");
  ixs_node *rhs =
      parse_bounds_expr(ctx, "-3 + raw0 + 4*ceiling(3/4 - 1/4*raw0)");
  ixs_node *common[5] = {parse_bounds_pred(ctx, "2147483648 + raw0 >= 0"),
                         parse_bounds_pred(ctx, "-2147483647 + raw0 <= 0"),
                         parse_bounds_pred(ctx, "raw0 >= 0"),
                         parse_bounds_pred(ctx, "-1073741822 + raw0 <= 0"),
                         parse_bounds_pred(ctx, "Mod(raw0, 2) == 0")};
  ixs_node *group0_predicates[5];
  ixs_node *group1_predicates[7];
  ixs_predicate_group groups[2];
  ixs_group_union_query queries[3];
  ixs_group_union_result results[3];
  size_t remaining_work = 1000000;
  size_t i;

  CHECK(ctx && raw && lhs && rhs);
  for (i = 0; i < 5; i++) {
    group0_predicates[i] = common[i];
    group1_predicates[i] = common[i];
  }
  group1_predicates[5] = parse_bounds_pred(ctx, "2147483649 + raw0 >= 0");
  group1_predicates[6] = parse_bounds_pred(ctx, "-2147483646 + raw0 <= 0");
  groups[0] = (ixs_predicate_group){group0_predicates, 5};
  groups[1] = (ixs_predicate_group){group1_predicates, 7};
  queries[0] = (ixs_group_union_query){
      0, 1, IXS_GROUP_UNION_CONSTANT_DIFFERENCE, rhs, lhs};
  queries[1] =
      (ixs_group_union_query){0, 1, IXS_GROUP_UNION_FINITE_DOMAIN_EQUIVALENT,
                              rhs, ixs_add(ctx, lhs, ixs_int(ctx, 1))};
  queries[2] = (ixs_group_union_query){
      0, 1, IXS_GROUP_UNION_FINITE_DOMAIN_CONSTANT_DIFFERENCE, rhs, lhs};
  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), groups, 2, queries, 3,
                                 results,
                                 &remaining_work) == IXS_GROUP_UNION_COMPLETE);
  CHECK(results[0].status == IXS_CHECK_TRUE && results[0].difference == 1);
  CHECK(results[1].status == IXS_CHECK_TRUE && results[1].difference == 0);
  CHECK(results[2].status == IXS_CHECK_TRUE && results[2].difference == 1);
  ixs_ctx_destroy(ctx);
}

static void test_public_group_union_closed_validation_budget(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "group_union_closed_x");
  ixs_node *denominator = ixs_sym(ctx, "group_union_closed_denominator");
  ixs_node *predicate =
      ixs_cmp(ctx, ixs_div(ctx, x, denominator), IXS_CMP_EQ, ixs_int(ctx, 0));
  ixs_predicate_group group = {&predicate, 1};
  ixs_group_union_query query = {0, 0, IXS_GROUP_UNION_EQUIVALENT, x, x};
  ixs_group_union_result result;
  size_t remaining_work = 1000;
  size_t used;

  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), &group, 1, &query, 1,
                                 &result,
                                 &remaining_work) == IXS_GROUP_UNION_INVALID);
  used = 1000 - remaining_work;
  CHECK(used > 0);
  ixs_ctx_clear_errors(ctx);
  remaining_work = used - 1u;
  result = (ixs_group_union_result){IXS_CHECK_TRUE, 99};
  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), &group, 1, &query, 1,
                                 &result,
                                 &remaining_work) == IXS_GROUP_UNION_EXHAUSTED);
  CHECK(remaining_work == 0 && result.status == IXS_CHECK_UNKNOWN &&
        result.difference == 0);
  ixs_ctx_destroy(ctx);
}

static void test_public_group_union_growable_query_holds(void) {
  enum { QUERY_HOLD_COUNT = 8192 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "group_union_saturation_x");
  ixs_node *inner_values[2] = {x, ixs_int(ctx, 1)};
  ixs_node *inner_conditions[2] = {
      ixs_cmp(ctx, ixs_sym(ctx, "group_union_saturation_inner_guard"),
              IXS_CMP_GT, ixs_int(ctx, 0)),
      ixs_true(ctx)};
  ixs_node *inner = ixs_pw(ctx, 2, inner_values, inner_conditions);
  ixs_node *outer_values[2] = {inner, ixs_int(ctx, 2)};
  ixs_node *outer_conditions[2] = {
      ixs_cmp(ctx, ixs_sym(ctx, "group_union_saturation_outer_guard"),
              IXS_CMP_GT, ixs_int(ctx, 0)),
      ixs_true(ctx)};
  ixs_node *outer = ixs_pw(ctx, 2, outer_values, outer_conditions);
  ixs_node *predicate = ixs_cmp(ctx, outer, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_predicate_group group = {&predicate, 1};
  ixs_group_union_query query = {0, 0, IXS_GROUP_UNION_EQUIVALENT, x, x};
  ixs_group_union_result result;
  ixs_facts *holder = ixs_facts_create(ctx);
  size_t remaining_work = 1000;
  size_t i;
  size_t held_count = 0;
  bool entered = false;

  CHECK(ixs_node_contains_nested_piecewise(predicate));
  for (i = 0; i < QUERY_HOLD_COUNT; i++) {
    CHECK(ixs_bounds_query_hold_begin(&holder->bounds, predicate, &entered));
    CHECK(entered);
    held_count++;
    entered = false;
  }
  CHECK(held_count == QUERY_HOLD_COUNT && !holder->bounds.oom);
  result = (ixs_group_union_result){IXS_CHECK_TRUE, 99};
  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), &group, 1, &query, 1,
                                 &result,
                                 &remaining_work) == IXS_GROUP_UNION_COMPLETE);
  CHECK(remaining_work < 1000 && result.status == IXS_CHECK_TRUE &&
        result.difference == 0);
  for (i = 0; i < held_count; i++)
    ixs_bounds_query_hold_end(&holder->bounds);
  ixs_ctx_destroy(ctx);
}

static void test_public_group_union_exact_relation_no_walk_cap(void) {
  enum { CHAIN_LENGTH = 300, PREDICATE_COUNT = CHAIN_LENGTH + 2 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *two = ixs_int(ctx, 2);
  ixs_node *modulus = ixs_int(ctx, INT64_C(4294967296));
  ixs_node *nodes[CHAIN_LENGTH + 1];
  ixs_node *predicates[PREDICATE_COUNT];
  ixs_node *base;
  ixs_node *middle;
  ixs_node *tail;
  ixs_predicate_group group = {predicates, PREDICATE_COUNT};
  ixs_group_union_query queries[2];
  ixs_group_union_result results[2];
  size_t remaining_work = 100000;
  unsigned i;

  for (i = 0; i <= CHAIN_LENGTH; i++) {
    char name[48];
    (void)snprintf(name, sizeof(name), "group_exact_chain_%u", i);
    nodes[i] = ixs_mod(ctx, ixs_sym(ctx, name), modulus);
    if (i != 0)
      predicates[i - 1u] =
          ixs_cmp(ctx, nodes[i], IXS_CMP_EQ,
                  ixs_add(ctx, nodes[i - 1u], ixs_int(ctx, 1)));
  }
  base = ixs_floor(ctx, ixs_div(ctx, ixs_sym(ctx, "group_exact_base"), two));
  middle =
      ixs_floor(ctx, ixs_div(ctx, ixs_sym(ctx, "group_exact_middle"), two));
  tail = ixs_floor(ctx, ixs_div(ctx, ixs_sym(ctx, "group_exact_tail"), two));
  predicates[CHAIN_LENGTH] = ixs_cmp(
      ctx, middle, IXS_CMP_EQ, ixs_add(ctx, base, ixs_int(ctx, INT64_MAX)));
  predicates[CHAIN_LENGTH + 1u] =
      ixs_cmp(ctx, tail, IXS_CMP_EQ, ixs_add(ctx, middle, ixs_int(ctx, 1)));
  queries[0] = (ixs_group_union_query){
      0, 0, IXS_GROUP_UNION_CONSTANT_DIFFERENCE, nodes[CHAIN_LENGTH], nodes[0]};
  queries[1] = (ixs_group_union_query){
      0, 0, IXS_GROUP_UNION_CONSTANT_DIFFERENCE, tail, base};

  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), &group, 1, queries, 2,
                                 results,
                                 &remaining_work) == IXS_GROUP_UNION_COMPLETE);
  CHECK(results[0].status == IXS_CHECK_TRUE &&
        results[0].difference == CHAIN_LENGTH);
  CHECK(results[1].status == IXS_CHECK_UNKNOWN && results[1].difference == 0);
  ixs_ctx_destroy(ctx);
}

static void test_public_group_union_failures(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "group_union_failure_x");
  ixs_node *predicate = ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, 0));
  ixs_predicate_group group = {&predicate, 1};
  ixs_group_union_query query = {0, 0, IXS_GROUP_UNION_CONSTANT_DIFFERENCE, x,
                                 x};
  ixs_group_union_result result = {IXS_CHECK_TRUE, 99};
  size_t remaining_work = 0;

  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), NULL, 0, NULL, 0, NULL,
                                 &remaining_work) == IXS_GROUP_UNION_COMPLETE);

  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), &group, 1, &query, 1,
                                 &result,
                                 &remaining_work) == IXS_GROUP_UNION_EXHAUSTED);
  CHECK(remaining_work == 0 && result.status == IXS_CHECK_UNKNOWN &&
        result.difference == 0);

  query.rhs_group = 1;
  remaining_work = 0;
  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), &group, 1, &query, 1,
                                 &result,
                                 &remaining_work) == IXS_GROUP_UNION_INVALID);
  CHECK(remaining_work == 0 && result.status == IXS_CHECK_UNKNOWN &&
        result.difference == 0);
  query.rhs_group = 0;

  query.kind = (ixs_group_union_query_kind)99;
  remaining_work = 100;
  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), &group, 1, &query, 1,
                                 &result,
                                 &remaining_work) == IXS_GROUP_UNION_INVALID);
  CHECK(result.status == IXS_CHECK_UNKNOWN && result.difference == 0);

  query.kind = IXS_GROUP_UNION_EQUIVALENT;
  query.lhs = predicate;
  query.rhs = ixs_int(ctx, 1);
  remaining_work = 100;
  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), &group, 1, &query, 1,
                                 &result,
                                 &remaining_work) == IXS_GROUP_UNION_COMPLETE);
  CHECK(result.status == IXS_CHECK_TRUE && result.difference == 0);

  query.kind = IXS_GROUP_UNION_CONSTANT_DIFFERENCE;
  query.rhs = x;
  remaining_work = 100;
  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), &group, 1, &query, 1,
                                 &result,
                                 &remaining_work) == IXS_GROUP_UNION_COMPLETE);
  CHECK(result.status == IXS_CHECK_TRUE && result.difference == 1);

  query.lhs = x;
  query.rhs = x;

  {
    size_t hostile_query_count = SIZE_MAX / sizeof(ixs_group_union_query) + 1u;
    result.status = IXS_CHECK_TRUE;
    result.difference = 99;
    remaining_work = SIZE_MAX;
    CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), &group, 1, &query,
                                   hostile_query_count, &result,
                                   &remaining_work) == IXS_GROUP_UNION_INVALID);
    CHECK(result.status == IXS_CHECK_TRUE && result.difference == 99 &&
          remaining_work == SIZE_MAX);
  }

  {
    ixs_predicate_group hostile = {(const ixs_node *const *)(uintptr_t)1,
                                   SIZE_MAX / sizeof(ixs_node *) + 1u};
    result.status = IXS_CHECK_TRUE;
    result.difference = 99;
    remaining_work = SIZE_MAX;
    CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), &hostile, 1, &query,
                                   1, &result,
                                   &remaining_work) == IXS_GROUP_UNION_INVALID);
    CHECK(result.status == IXS_CHECK_UNKNOWN && result.difference == 0 &&
          remaining_work == SIZE_MAX);
  }

  remaining_work = 0;
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK((ixs_query_group_unions)(IXS_TEST_SESSION(ctx), &group, 1, &query, 1,
                                 &result,
                                 &remaining_work) == IXS_GROUP_UNION_OOM);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(remaining_work == 0 && result.status == IXS_CHECK_UNKNOWN &&
        result.difference == 0);
  ixs_ctx_destroy(ctx);
}

static int64_t modulo_recurrence_sample(ixs_ctx *ctx, ixs_node *expr,
                                        ixs_node *symbol, int64_t value) {
  ixs_node *substituted = ixs_subs(ctx, expr, symbol, ixs_int(ctx, value));
  ixs_node *simplified = ixs_simplify(ctx, substituted, NULL, 0);
  CHECK(simplified && ixs_node_tag(simplified) == IXS_INT);
  return ixs_node_int_val(simplified);
}

static void test_public_modulo_recurrence(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *i = ixs_sym(ctx, "modulo_recurrence_i");
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *two = ixs_int(ctx, 2);
  ixs_node *plus_two = ixs_add(ctx, i, two);
  ixs_node *minus_one = ixs_sub(ctx, i, one);
  ixs_node *predicate = ixs_cmp(ctx, i, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_facts *nonnegative = ixs_facts_create(ctx);
  ixs_facts *positive = ixs_facts_create(ctx);
  ixs_facts *signed_no_wrap = ixs_facts_create(ctx);
  ixs_facts *minus_one_point = ixs_facts_create(ctx);
  ixs_facts *empty = ixs_facts_create(ctx);
  ixs_modulo_recurrence_result result;

  CHECK(ctx && i && one && two && plus_two && minus_one && predicate &&
        nonnegative && positive && signed_no_wrap && minus_one_point && empty);
  CHECK(ixs_facts_assume_pred(nonnegative,
                              ixs_cmp(ctx, i, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(nonnegative,
                              ixs_cmp(ctx, i, IXS_CMP_LE, ixs_int(ctx, 100))));
  CHECK(ixs_facts_assume_pred(positive,
                              ixs_cmp(ctx, i, IXS_CMP_GE, ixs_int(ctx, 1))));
  CHECK(ixs_facts_assume_pred(positive,
                              ixs_cmp(ctx, i, IXS_CMP_LE, ixs_int(ctx, 100))));
  CHECK(ixs_facts_assume_pred(
      signed_no_wrap, ixs_cmp(ctx, i, IXS_CMP_GE, ixs_int(ctx, INT32_MIN))));
  CHECK(ixs_facts_assume_pred(
      signed_no_wrap,
      ixs_cmp(ctx, i, IXS_CMP_LE, ixs_int(ctx, INT32_MAX - 2))));
  CHECK(ixs_facts_assume_pred(minus_one_point,
                              ixs_cmp(ctx, i, IXS_CMP_EQ, ixs_int(ctx, -1))));

  /* Predicate-valued scalar expressions are ordinary integer 0/1 values.
   * Their width-one unsigned recurrence modulo one has the canonical zero
   * remainder, not the unreduced predicate bit pattern. */
  result = ixs_modulo_recurrence_facts(empty, predicate, predicate, predicate,
                                       IXS_REMAINDER_UNSIGNED, 1, 1);
  CHECK(result.status == IXS_MODULO_RECURRENCE_PROVEN &&
        result.increment == 0 && result.remainder == ixs_int(ctx, 0));

  result = ixs_modulo_recurrence_facts(nonnegative, plus_two, i, i,
                                       IXS_REMAINDER_SIGNED, 32, 5);
  CHECK(result.status == IXS_MODULO_RECURRENCE_PROVEN &&
        result.increment == 2 && result.remainder != NULL);
  CHECK(modulo_recurrence_sample(ctx, result.remainder, i, 7) == 2);

  /* A signed negative delta is Euclidean-normalized once all truncating
   * remainder operands are proved nonnegative. */
  result = ixs_modulo_recurrence_facts(positive, minus_one, i, i,
                                       IXS_REMAINDER_SIGNED, 32, 5);
  CHECK(result.status == IXS_MODULO_RECURRENCE_PROVEN &&
        result.increment == 4 && result.remainder != NULL);
  result = ixs_modulo_recurrence_facts(nonnegative, minus_one, i, i,
                                       IXS_REMAINDER_SIGNED, 32, 5);
  CHECK(result.status == IXS_MODULO_RECURRENCE_UNKNOWN &&
        result.increment == 0 && result.remainder == NULL);

  result = ixs_modulo_recurrence_facts(positive, minus_one, i, i,
                                       IXS_REMAINDER_UNSIGNED, 32, 5);
  CHECK(result.status == IXS_MODULO_RECURRENCE_PROVEN &&
        result.increment == 4 && result.remainder != NULL);
  result = ixs_modulo_recurrence_facts(nonnegative, plus_two, i, i,
                                       IXS_REMAINDER_UNSIGNED, 32, 5);
  CHECK(result.status == IXS_MODULO_RECURRENCE_PROVEN &&
        result.increment == 2 && result.remainder != NULL);

  /* A raw algebraic delta is not an unsigned fixed-width delta when the add
   * can wrap.  For an arbitrary divisor the two projected deltas have
   * different residues, so incomplete no-wrap facts must stay unknown. */
  result = ixs_modulo_recurrence_facts(empty, plus_two, i, i,
                                       IXS_REMAINDER_UNSIGNED, 32, 5);
  CHECK(result.status == IXS_MODULO_RECURRENCE_UNKNOWN &&
        result.increment == 0 && result.remainder == NULL);
  result = ixs_modulo_recurrence_facts(signed_no_wrap, plus_two, i, i,
                                       IXS_REMAINDER_UNSIGNED, 32, 5);
  CHECK(result.status == IXS_MODULO_RECURRENCE_UNKNOWN &&
        result.increment == 0 && result.remainder == NULL);

  /* When the fixed-width modulus is itself divisible by the divisor, every
   * possible wrap has residue zero and the raw delta is sufficient. */
  result = ixs_modulo_recurrence_facts(empty, plus_two, i, i,
                                       IXS_REMAINDER_UNSIGNED, 32, 8);
  CHECK(result.status == IXS_MODULO_RECURRENCE_PROVEN &&
        result.increment == 2 && result.remainder != NULL);

  /* Crossing the signed-view boundary is still an ordinary adjacent unsigned
   * increment/decrement. The 32-bit unsigned projection removes the apparent
   * +/- (2^32 - 1) signed delta. */
  result = ixs_modulo_recurrence_facts(empty, ixs_int(ctx, INT32_MIN),
                                       ixs_int(ctx, INT32_MAX), i,
                                       IXS_REMAINDER_UNSIGNED, 32, 5);
  CHECK(result.status == IXS_MODULO_RECURRENCE_PROVEN &&
        result.increment == 1 && result.remainder != NULL);
  result = ixs_modulo_recurrence_facts(empty, ixs_int(ctx, INT32_MAX),
                                       ixs_int(ctx, INT32_MIN), i,
                                       IXS_REMAINDER_UNSIGNED, 32, 5);
  CHECK(result.status == IXS_MODULO_RECURRENCE_PROVEN &&
        result.increment == 4 && result.remainder != NULL);

  /* Crossing the signed boundary is an unsigned fixed-width wrap.  For
   * UINT64_MAX -> 0 modulo 5 the apparent +1 delta has residue zero because
   * 2^64 also has residue one. */
  result = ixs_modulo_recurrence_facts(minus_one_point, ixs_add(ctx, i, one), i,
                                       i, IXS_REMAINDER_UNSIGNED, 64, 5);
  CHECK(result.status == IXS_MODULO_RECURRENCE_PROVEN &&
        result.increment == 0 && result.remainder != NULL);
  CHECK(modulo_recurrence_sample(ctx, result.remainder, i, -1) == 0);
  result = ixs_modulo_recurrence_facts(empty, ixs_add(ctx, i, one), i, i,
                                       IXS_REMAINDER_UNSIGNED, 64, 5);
  CHECK(result.status == IXS_MODULO_RECURRENCE_UNKNOWN &&
        result.increment == 0 && result.remainder == NULL);

  /* Upper-half divisors are passed as uint64_t bit patterns. Their exact
   * signed-view result never needs an unrepresentable positive literal. */
  result = ixs_modulo_recurrence_facts(empty, i, i, i, IXS_REMAINDER_UNSIGNED,
                                       32, UINT64_C(2147483651));
  CHECK(result.status == IXS_MODULO_RECURRENCE_PROVEN &&
        result.increment == 0 && result.remainder != NULL);
  CHECK(modulo_recurrence_sample(ctx, result.remainder, i, INT32_MIN) ==
        INT32_MIN);
  CHECK(modulo_recurrence_sample(ctx, result.remainder, i, -2147483645) == 0);
  CHECK(modulo_recurrence_sample(ctx, result.remainder, i, -1) == 2147483644);

  result = ixs_modulo_recurrence_facts(empty, i, i, i, IXS_REMAINDER_UNSIGNED,
                                       64, UINT64_C(9223372036854775808));
  CHECK(result.status == IXS_MODULO_RECURRENCE_PROVEN &&
        result.increment == 0 && result.remainder != NULL);
  CHECK(modulo_recurrence_sample(ctx, result.remainder, i, INT64_MIN) == 0);
  CHECK(modulo_recurrence_sample(ctx, result.remainder, i, -1) == INT64_MAX);

  ixs_ctx_destroy(ctx);
}

static void test_public_modulo_recurrence_failures(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *i = ixs_sym(ctx, "modulo_recurrence_failure_i");
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_modulo_recurrence_result result;

  CHECK(ctx && other && i && facts);
  result =
      ixs_modulo_recurrence_facts(facts, i, i, i, IXS_REMAINDER_UNSIGNED, 0, 5);
  CHECK(result.status == IXS_MODULO_RECURRENCE_INVALID &&
        result.increment == 0 && result.remainder == NULL);
  result = ixs_modulo_recurrence_facts(facts, i, i, i, IXS_REMAINDER_UNSIGNED,
                                       65, 5);
  CHECK(result.status == IXS_MODULO_RECURRENCE_INVALID &&
        result.increment == 0 && result.remainder == NULL);
  result =
      ixs_modulo_recurrence_facts(facts, i, i, i, IXS_REMAINDER_UNSIGNED, 8, 0);
  CHECK(result.status == IXS_MODULO_RECURRENCE_INVALID &&
        result.increment == 0 && result.remainder == NULL);
  result = ixs_modulo_recurrence_facts(facts, i, i, i, IXS_REMAINDER_UNSIGNED,
                                       8, 256);
  CHECK(result.status == IXS_MODULO_RECURRENCE_INVALID &&
        result.increment == 0 && result.remainder == NULL);
  result =
      ixs_modulo_recurrence_facts(facts, i, i, i, IXS_REMAINDER_SIGNED, 8, 128);
  CHECK(result.status == IXS_MODULO_RECURRENCE_INVALID &&
        result.increment == 0 && result.remainder == NULL);
  result = ixs_modulo_recurrence_facts(facts, i, i, i,
                                       (ixs_remainder_signedness)99, 8, 5);
  CHECK(result.status == IXS_MODULO_RECURRENCE_INVALID &&
        result.increment == 0 && result.remainder == NULL);
  result = ixs_modulo_recurrence_facts(
      facts, ixs_sym(other, "modulo_recurrence_foreign"), i, i,
      IXS_REMAINDER_UNSIGNED, 8, 5);
  CHECK(result.status == IXS_MODULO_RECURRENCE_INVALID &&
        result.increment == 0 && result.remainder == NULL);
  result = ixs_modulo_recurrence_facts(
      facts, ixs_cmp(ctx, i, IXS_CMP_EQ, ixs_int(ctx, 0)), i, i,
      IXS_REMAINDER_UNSIGNED, 8, 5);
  CHECK(result.status == IXS_MODULO_RECURRENCE_UNKNOWN &&
        result.increment == 0 && result.remainder == NULL);

  ixs_arena_set_fail_after(&ctx->arena, 0);
  result = ixs_modulo_recurrence_facts(facts, i, i, i, IXS_REMAINDER_UNSIGNED,
                                       32, 104729);
  ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
  CHECK(result.status == IXS_MODULO_RECURRENCE_OOM && result.increment == 0 &&
        result.remainder == NULL);
  result = ixs_modulo_recurrence_facts(facts, i, i, i, IXS_REMAINDER_UNSIGNED,
                                       32, 104729);
  CHECK(result.status == IXS_MODULO_RECURRENCE_PROVEN &&
        result.remainder != NULL);

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_public_modulo_recurrence_plan_failures(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *i = ixs_sym(ctx, "modulo_plan_failure_i");
  ixs_node *foreign = ixs_sym(other, "modulo_plan_failure_foreign");
  ixs_node *successor = ixs_add(ctx, i, ixs_int(ctx, 1));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_modulo_recurrence_target target = {
      facts, i, i, NULL, 0u, IXS_REMAINDER_SIGNED, 5u};
  ixs_modulo_recurrence_plan_group group;
  ixs_modulo_recurrence_plan_entry entry;
  ixs_modulo_recurrence_plan_result result;
  size_t budget;

  CHECK(ctx && other && i && foreign && successor && facts);
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, i, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, i, IXS_CMP_LE, ixs_int(ctx, 9))));

  target.value = foreign;
  group.divisor = 99u;
  entry.group_index = 0u;
  entry.increment = 99u;
  budget = 2u;
  result = ixs_plan_modulo_recurrences_facts(
      facts, successor, i, i, 8u, &target, 1u, &group, 1u, &entry, 1u, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_INVALID && result.ngroups == 0u &&
        budget == 2u && group.divisor == 0u && entry.group_index == SIZE_MAX &&
        entry.increment == 0u);

  target.value = i;
  target.divisor = 128u;
  budget = 2u;
  result = ixs_plan_modulo_recurrences_facts(
      facts, successor, i, i, 8u, &target, 1u, &group, 1u, &entry, 1u, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE && result.ngroups == 0u &&
        budget == 0u && entry.group_index == SIZE_MAX);

  target.divisor = 5u;
  group.divisor = 99u;
  entry.group_index = 0u;
  entry.increment = 99u;
  budget = 2u;
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  result = ixs_plan_modulo_recurrences_facts(
      facts, successor, i, i, 8u, &target, 1u, &group, 1u, &entry, 1u, &budget);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(result.status == IXS_FINITE_DOMAIN_OOM && result.ngroups == 0u &&
        budget == 0u && group.divisor == 0u && entry.group_index == SIZE_MAX &&
        entry.increment == 0u);

  budget = 2u;
  result = ixs_plan_modulo_recurrences_facts(
      facts, successor, i, i, 8u, &target, 1u, &group, 1u, &entry, 1u, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE && result.ngroups == 1u &&
        budget == 0u && group.divisor == 5u &&
        group.successor_increment == 1u && entry.group_index == 0u &&
        entry.increment == 0u);

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_public_modulo_recurrence_plan_local_limits(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *i = ixs_sym(ctx, "modulo_plan_limit_i");
  ixs_node *nested = make_nested_query_root(ctx, "modulo_plan_limit_nested");
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_modulo_recurrence_target target = {
      facts, i, i, NULL, 0u, IXS_REMAINDER_UNSIGNED, 5u};
  ixs_modulo_recurrence_plan_group group;
  ixs_modulo_recurrence_plan_entry entry;
  ixs_modulo_recurrence_plan_result result;
  ixs_modulo_recurrence_result scalar;
  ixs_bounds_test_transport observed;
  size_t budget;
  bool held = false;

  CHECK(ctx && i && nested && facts);
  CHECK(ixs_bounds_query_hold_begin(&facts->bounds, nested, &held) && held);
  CHECK(ixs_bounds_query_transport_probe(
      &facts->bounds, nested, IXS_BOUNDS_TEST_TRANSPORT_LIMITED, &observed));
  CHECK(observed == IXS_BOUNDS_TEST_TRANSPORT_LIMITED);

  scalar = ixs_modulo_recurrence_facts(facts, nested, i, i,
                                       IXS_REMAINDER_UNSIGNED, 8u, 5u);
  CHECK(scalar.status == IXS_MODULO_RECURRENCE_LIMITED &&
        scalar.remainder == NULL);

  /* A limited successor proof suppresses only its divisor group. */
  group.divisor = 99u;
  entry.group_index = 0u;
  entry.increment = 99u;
  budget = 2u;
  result = ixs_plan_modulo_recurrences_facts(
      facts, nested, i, i, 8u, &target, 1u, &group, 1u, &entry, 1u, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE && result.ngroups == 0u &&
        budget == 0u && group.divisor == 0u && entry.group_index == SIZE_MAX &&
        entry.increment == 0u);

  if (held)
    ixs_bounds_query_hold_end(&facts->bounds);
  ixs_ctx_destroy(ctx);
}

int main(void) {
  /* Interval arithmetic */
  test_iv_add_basic();
  test_iv_add_overflow_widens();
  test_iv_add_pos_overflow_widens();
  test_iv_add_invalid();
  test_iv_mul_const_basic();
  test_iv_mul_const_negative();
  test_iv_mul_const_zero();
  test_iv_mul_const_overflow_widens();
  test_iv_mul_const_neg_overflow_widens();
  test_iv_mul_basic();
  test_iv_mul_mixed_sign();
  test_iv_mul_overflow_widens();
  test_iv_mul_invalid();
  test_iv_recip_basic();
  test_iv_recip_unbounded();
  test_iv_recip_negative();
  test_iv_recip_contains_zero();
  test_iv_recip_invalid();
  test_iv_pow_sign_and_parity();
  test_iv_pow_limits_and_overflow();
  test_iv_intersect_basic();
  test_iv_intersect_empty();
  test_iv_intersect_one_invalid();
  test_iv_hull();

  /* Endpoint widening */
  test_iv_endpoint_widen_positive();
  test_iv_endpoint_widen_negative();
  test_iv_endpoint_widen_neg_neg();

  /* Bounds: assumptions */
  test_bounds_sym_ge();
  test_bounds_sym_lt();
  test_bounds_sym_eq();
  test_bounds_assumption_invalidates_cache();
  test_bounds_empty_cache_invalidation();
  test_bounds_two_sided();
  test_bounds_sym_gt();
  test_bounds_unknown_sym();

  /* Bounds: propagation */
  test_bounds_propagate_add();
  test_bounds_propagate_mul();
  test_bounds_propagate_mod();
  test_bounds_propagate_mod_tight();
  test_bounds_propagate_floor();

  /* Bounds: fork */
  test_bounds_fork();
  test_bounds_expr_index_fork();
  test_bounds_difference_fork();
  test_bounds_exact_fork();

  /* Bounds: modular congruence */
  test_bounds_modrem();
  test_bounds_modrem_zero();
  test_bounds_no_modrem();
  test_bounds_extrema_divisibility();

  /* Bounds: bitwise facts */
  test_bounds_bitfacts_pow2();
  test_bounds_bitfacts_masks();
  test_bounds_bitfacts_arithmetic();
  test_bounds_bitfacts_mod_requires_integer_dividend();
  test_bounds_bitfacts_mul_requires_integer_product();
  test_bounds_bitfacts_contradiction();
  test_bounds_mutual_query_budget_and_cache();
  test_bounds_piecewise_congruence_depth_envelope();
  test_bounds_piecewise_range_with_unrelated_congruence();
  test_bounds_flat_piecewise_keeps_case_limit();
  test_bounds_query_state_lazy_oom_and_lifecycle();
  test_bounds_contextless_query_arena_lifecycle_and_fork();
  test_bounds_query_hold_grows_and_unwinds();
  test_bounds_query_transport_poison_and_residue_retry();
  test_nested_piecewise_public_query_tracking();
  test_bounds_query_cache_rejects_stack_probes();
  test_piecewise_residue_domain_guards();

  /* Bounds: expression overrides */
  test_bounds_expr_override();
  test_bounds_expr_override_invalidates_cache();
  test_bounds_var_index_oom();
  test_bounds_expr_index_collision();
  test_bounds_expr_index_growth_and_merge();
  test_bounds_expr_index_oom();
  test_bounds_expr_le();

  /* Bounds: entailment check */
  test_bounds_check_true();
  test_bounds_check_false();
  test_bounds_check_unknown();
  test_bounds_check_eq();
  test_bounds_check_ne();
  test_bounds_check_mod_congruence();
  test_bounds_check_mod_remainder();
  test_bounds_check_composite_divisibility();
  test_bounds_check_pow2_fact();
  test_bounds_check_mask_fact();
  test_bounds_check_contradiction_unknown();
  test_public_pow2_fact();
  test_bounds_check_non_cmp();
  test_bounds_partial_predicate_is_semantic_unknown();
  test_public_fact_consistency();

  /* Bounds: public range API */
  test_public_range_basic();
  test_public_range_unbounded();
  test_public_range_rational();
  test_public_integer_range();
  test_public_range_unknown();
  test_public_range_int64_extrema();
  test_public_range_mod_int64_min_step();
  test_public_range_mod_requires_positive_divisor();
  test_public_range_mod_nonnegative_dividend_cap();
  test_public_range_mod_congruence_intersection();
  test_public_range_congruence_tightens_endpoints();
  test_public_range_congruence_alignment_overflow();
  test_public_range_difference_constraint_propagation();
  test_public_modular_projection_difference();
  test_public_range_nonnegative_signed_remainder_packet();
  test_public_dynamic_modular_projection_difference();
  test_public_modular_projection_unbounded_query_stack();
  test_public_modular_projection_exact_residual();
  test_public_constant_difference_no_round_piecewise_fast_path();
  test_public_exact_equality_direct();
  test_public_exact_equality_transitive();
  test_public_exact_equality_substitution_and_negatives();
  test_public_exact_equality_ignores_inequality_fanout();
  test_public_exact_equality_long_chain();
  test_public_exact_equality_cycles_and_overflow();
  test_public_exact_residual_relation_chain_and_boundaries();
  test_public_exact_residual_wide_term_partition();
  test_public_exact_relation_disconnected_fanout();
  test_public_exact_equality_range_projection();
  test_public_exact_scaled_residual_range_projection();
  test_bounds_exact_relation_fork_owns_graph();
  test_public_range_composite_predicate_fact();
  test_public_facts_batch_preserves_affine_range();
  test_public_facts_batch_a4w4_order_independent();
  test_public_range_proportional_add_edges();
  test_shifted_add_range_oom_and_contradiction();
  test_public_facts_range_and_transfer();
  test_public_range_powers();
  test_public_range_xor();
  test_public_range_associative_many();
  test_public_range_piecewise();
  test_failed_expand_is_not_expression_fact_alias();
  test_bounds_canonical_alias_cache();
  test_bounds_canonical_alias_failure_semantics();
  test_public_facts_assume_conjunction();
  test_public_facts_assume_batch();
  test_public_facts_assume_batch_closure();
  test_public_facts_assume_batch_saturates_until_stable();
  test_public_facts_assume_batch_has_no_round_limit();
  test_public_facts_assume_batch_mid_simplify_oom();
  test_public_difference_constraint_oom_is_atomic();
  test_public_exact_equality_oom_is_atomic();
  test_public_difference_potential_overflow_is_atomic();
  test_public_group_union_scalar_oracle_size(3);
  test_public_group_union_scalar_oracle_size(8);
  test_public_group_union_scalar_oracle_size(16);
  test_public_group_union_scalar_oracle_size(17);
  test_public_group_union_dag_work_admission();
  test_public_group_union_sixty_five_group_registry();
  test_public_group_union_cross_closure_and_isolation();
  test_public_group_union_finite_domain_and_budget();
  test_public_group_union_finite_constant_difference();
  test_public_group_union_signed_wrap_successor();
  test_public_equivalence_common_guard_aligned_packet();
  test_public_group_union_aligned_slot_packet();
  test_public_group_union_negative_remainder_successor();
  test_public_group_union_closed_validation_budget();
  test_public_group_union_growable_query_holds();
  test_public_group_union_exact_relation_no_walk_cap();
  test_public_group_union_failures();
  test_public_modulo_recurrence();
  test_public_modulo_recurrence_failures();
  test_public_modulo_recurrence_plan_failures();
  test_public_modulo_recurrence_plan_local_limits();
  test_ctx_node_ownership_uses_intern_table();
  test_compound_assumption_legacy_fact_parity();
  test_fact_check_xor_cancellation_parity();
  test_compound_assumption_rejection_is_atomic();
  test_compound_assumption_boolean_constants();
  test_public_facts_assume_deep_conjunction();
  test_public_facts_substitute_preserves_symbol_facts();
  test_public_facts_substitute_preserves_difference_graph();
  test_public_facts_substitute_multi_semantics();
  test_public_facts_substitute_inverse_facts();
  test_public_facts_substitute_contradiction_and_extrema();
  test_public_facts_substitute_failures_are_atomic();
  test_public_structural_and_assumption_integrality();
  test_public_fact_integrality_associative_many();
  test_public_fact_integrality_deep_mixed_dag();
  test_public_fact_integrality_piecewise();
  test_public_fact_integrality_nested_mod();
  test_public_fact_integrality_nested_mod_cancellation();
  test_public_fact_integrality_scaled_xor();
  test_public_fact_divisibility();
  test_public_fact_divisibility_rejects_reciprocal_factor();
  test_public_known_bits_propagation();
  test_public_known_bits_failures();
  test_public_symbol_congruence();
  test_public_congruence_query();
  test_public_predicate_tree_query();
  test_public_equivalence_congruent_signed_no_wrap();
  test_public_equivalence_ordered_congruence_forms();
  test_public_equivalence_ordered_candidate_growth();
  test_public_total_equivalence();
  test_public_trunc_primitive_constant_difference();
  test_public_truncating_remainder_equivalence();
  test_public_truncating_remainder_oom();
  test_public_remainder_projection_candidate_growth();
  test_public_remainder_projection_large_candidate_set();
  test_public_remainder_projection_shared_diamond();
  test_public_modulo_pow2_equivalence();
  test_public_finite_domain_equivalence();
  test_finite_domain_equivalence_growable_discovery();
  test_public_finite_domain_synthesis();
  test_public_mapped_expression_facts();
  test_public_mapped_bundle_facts();
  test_public_mapped_bundle_failures();
  test_public_mapped_expression_failures();
  test_public_mapped_constant_differences();
  test_public_finite_domain_batch();
  test_public_finite_domain_query_hold_oom_retry();
  test_public_finite_domain_composed_synthesis();
  test_total_equivalence_new_proof_oom();
  test_public_equivalence_invalid_inputs();
  test_public_affine_and_constant_difference();
  test_public_exact_quotient_decomposition();
  test_public_exact_quotient_invalid_and_oom();
  test_public_finite_difference_and_additive_split();
  test_public_invariant_under_step();
  test_public_cyclic_decomposition_shapes_and_facts();
  test_public_cyclic_decomposition_bound_oom();
  test_public_cyclic_decomposition_rejections();
  test_public_algebra_helpers_use_facts();
  test_public_algebra_helper_invalid_inputs();
  test_public_exact_divide_basic();
  test_public_exact_divide_fact_integer_bitwise_factor();
  test_public_exact_divide_fact_scaled_xor_quotient();
  test_public_exact_divide_requires_defined_product();
  test_public_exact_divide_fact_simplification();
  test_public_exact_divide_canonical_nonzero_factor();
  test_public_exact_divide_scaled_mod_domain();
  test_public_exact_divide_extrema_and_overflow();
  test_public_exact_divide_invalid_and_oom();
  test_public_integrality_invalid_and_contradictory();
  test_public_defined_reciprocal_and_children();
  test_public_defined_mod_contract();
  test_public_defined_bitwise_integrality();
  test_public_defined_piecewise_first_match();
  test_public_defined_piecewise_condition();
  test_public_defined_shared_rounding_piecewise();
  test_public_defined_facts_and_invalid();
  test_public_defined_total_memo_rejects_malformed_nodes();
  test_public_defined_expression_facts_do_not_close_domain();
  test_public_facts_closed_batch_contract();
  test_public_defined_traversal_bounds_and_sharing();
  test_fact_simplify_session_lifetime_and_oom();
  test_fact_query_arena_session_teardown();
  test_batch_rewrite_cache_oom_is_atomic();
  test_mod_rewrite_oom_propagates();
  test_same_bucket_floor_oom_is_conservative();
  test_associative_constructor_oom();
  test_deep_node_order_is_iterative();
  test_public_rational_intermediate_boundaries();
  test_public_rational_intermediate_compounds();
  test_public_rational_intermediate_piecewise_conditions();
  test_public_rational_intermediate_unsupported_extrema();
  test_public_rational_intermediate_piecewise_selector();
  test_public_rational_intermediate_mod_projection();
  test_public_rational_intermediate_order_independent_envelopes();
  test_public_rational_intermediate_oom_and_invalid();
  test_public_rational_intermediate_growable_and_shared_dag();

  printf("test_bounds: %d/%d passed\n", tests_passed, tests_run);
  return tests_passed == tests_run ? 0 : 1;
}
