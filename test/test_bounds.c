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

#include "test_check.h"
#include <ixsimpl.h>
#include <string.h>

#ifndef INT64_MIN
#define INT64_MIN (-9223372036854775807LL - 1)
#endif
#ifndef INT64_MAX
#define INT64_MAX 9223372036854775807LL
#endif

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

  ixs_bounds child;
  CHECK(ixs_bounds_fork(&child, &b));

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

  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));
  CHECK(ixs_bounds_is_known_divisible(&b, ixs_max(ctx, six_x, nine_y), 3));
  CHECK(ixs_bounds_is_known_divisible(&b, ixs_min(ctx, six_x, nine_y), 3));
  CHECK(!ixs_bounds_is_known_divisible(&b, ixs_max(ctx, six_x, ten_y), 3));
  CHECK(!ixs_bounds_is_known_divisible(&b, ixs_min(ctx, six_x, ten_y), 3));

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
  CHECK(ixs_check_facts(facts, query) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_get_pow2_fact_facts(facts, x) == IXS_POW2_UNKNOWN);
  CHECK(!ixs_range_facts(facts, x, &r));

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
  CHECK(ixs_check_facts(facts, ixs_true(ctx)) == IXS_CHECK_TRUE);
  CHECK(ixs_check_facts(facts, ixs_false(ctx)) == IXS_CHECK_FALSE);
  CHECK(ixs_check_facts(facts, ixs_int(ctx, 2)) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_facts(facts, x) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check(ctx, ixs_true(ctx), &falsehood, 1) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_facts_assume_pred(contradictory, falsehood));
  CHECK(ixs_check_facts(contradictory, ixs_true(ctx)) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_facts(contradictory, ixs_false(ctx)) == IXS_CHECK_UNKNOWN);
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

static void test_public_range_composite_predicate_fact(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *a = ixs_sym(ctx, "A");
  ixs_node *b = ixs_sym(ctx, "B");
  ixs_node *expr = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), a),
                           ixs_mul(ctx, ixs_int(ctx, 16), b));
  ixs_node *factored = ixs_mul(
      ctx, ixs_int(ctx, 2), ixs_add(ctx, a, ixs_mul(ctx, ixs_int(ctx, 8), b)));
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

  CHECK(ixs_range_facts(facts, scaled, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 2147483630 && r.upper_q == 1);

  CHECK(ixs_facts_substitute(subst, facts, orig, replacement));
  CHECK(ixs_range_facts(subst, replacement, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 1073741815 && r.upper_q == 1);

  CHECK(ixs_range_facts(subst, subst_scaled, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 2147483630 && r.upper_q == 1);

  CHECK(ixs_range_facts(subst, expanded_scaled, &r));
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
  CHECK(!ixs_range(ctx, raw_power(ctx, x, 65), assumes, 2, &r));
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
  CHECK(!ixs_range(ctx, expr, NULL, 0, &r));

  for (i = 0; i < MANY_CASES; i++) {
    many_cases[i].value = ixs_int(ctx, 1);
    many_cases[i].cond = ixs_true(ctx);
  }
  expr = ixs_node_pw(ctx, MANY_CASES, many_cases);
  CHECK(!ixs_range(ctx, expr, NULL, 0, &r));

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
  CHECK(ixs_facts_assume_range(facts, x65, &input));
  CHECK(ixs_ctx_nerrors(ctx) == 0);
  CHECK(ixs_range_facts(facts, x65, &r));
  CHECK(ixs_ctx_nerrors(ctx) == 0);
  CHECK(!ixs_range_facts(facts, y65, &r));
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
  CHECK(ixs_range_facts(facts, x, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(r.has_upper && r.upper_p == 10 && r.upper_q == 1);
  CHECK(!ixs_facts_assume_pred(unsupported, either));

  ixs_ctx_destroy(ctx);
}

static ixs_node *raw_logic_node(ixs_ctx *ctx, ixs_tag tag, uint32_t nargs,
                                ixs_node **args) {
  ixs_node *node = ixs_node_logic(ctx, tag, nargs, args);
  CHECK(node != NULL);
  return node;
}

static void test_ctx_node_ownership_uses_intern_table(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "owned_x");
  ixs_node *foreign = ixs_sym(other, "owned_x");
  ixs_node *raw = ixs_arena_alloc(&ctx->arena, sizeof(*raw), sizeof(void *));

  CHECK(raw != NULL);
  if (raw)
    memcpy(raw, x, sizeof(*raw));
  CHECK(ixs_ctx_owns_node(ctx, x));
  CHECK(!ixs_ctx_owns_node(ctx, foreign));
  if (raw)
    CHECK(!ixs_ctx_owns_node(ctx, raw));

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
  CHECK(ixs_range_facts(facts, x, &fact_range));
  CHECK(fact_range.has_lower == legacy_range.has_lower);
  CHECK(fact_range.has_upper == legacy_range.has_upper);
  CHECK(fact_range.lower_p == legacy_range.lower_p);
  CHECK(fact_range.lower_q == legacy_range.lower_q);
  CHECK(fact_range.upper_p == legacy_range.upper_p);
  CHECK(fact_range.upper_q == legacy_range.upper_q);
  CHECK(ixs_check_facts(facts, query) == IXS_CHECK_TRUE);
  CHECK(ixs_get_pow2_fact_facts(facts, d) == IXS_POW2_POSITIVE);

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
  CHECK(ixs_check_facts(facts, equal) == IXS_CHECK_TRUE);
  CHECK(ixs_check_predicate_facts(facts, equal) == IXS_CHECK_TRUE);
  CHECK(ixs_equivalent_facts(facts, nested, x) == IXS_CHECK_TRUE);

  CHECK(different != x);
  CHECK(ixs_check(ctx, not_equal, &range, 1) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_facts(facts, not_equal) == IXS_CHECK_UNKNOWN);

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
  CHECK(!ixs_range_facts(facts, x, &r));
  CHECK(!ixs_range_facts(facts, y, &r));
  CHECK(ixs_check_facts(facts, query) == IXS_CHECK_UNKNOWN);

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
  CHECK(ixs_range_facts(true_facts, value, &r));
  CHECK(ixs_facts_assume_pred(false_facts, falsehood));
  CHECK(!ixs_range_facts(false_facts, value, &r));

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
  CHECK(ixs_range_facts(facts, first, &r));
  CHECK(r.has_lower && r.lower_p == 0 && r.lower_q == 1);
  CHECK(ixs_range_facts(facts, last, &r));
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
  CHECK(ixs_get_pow2_fact_facts(src, d) == IXS_POW2_OR_ZERO);
  CHECK(ixs_facts_assume_range(dst, seed, &seed_range));

  CHECK(ixs_facts_substitute(dst, src, x, y));
  CHECK(ixs_get_pow2_fact_facts(dst, d) == IXS_POW2_OR_ZERO);

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
  CHECK(ixs_range_facts(dst, y, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 15 && range.upper_q == 1);
  CHECK(ixs_range_facts(dst, z, &range));
  CHECK(range.has_lower && range.lower_p == 20 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 30 && range.upper_q == 1);
  CHECK(ixs_range_facts(dst, seed, &range));
  CHECK(range.has_lower && range.lower_p == 100);
  CHECK(range.has_upper && range.upper_p == 200);
  CHECK(ixs_get_pow2_fact_facts(dst, d) == IXS_POW2_OR_ZERO);

  CHECK(ixs_facts_substitute_multi(duplicates, src, 2, duplicate_targets,
                                   duplicate_replacements));
  CHECK(ixs_range_facts(duplicates, a, &range));
  CHECK(range.has_lower && range.lower_p == 0);
  CHECK(range.has_upper && range.upper_p == 15);
  CHECK(!ixs_range_facts(duplicates, b, &range));

  CHECK(ixs_facts_substitute_multi(empty_copy, src, 0, NULL, NULL));
  CHECK(ixs_range_facts(empty_copy, x, &range));
  CHECK(range.has_lower && range.lower_p == 0);
  CHECK(range.has_upper && range.upper_p == 15);

  CHECK(ixs_facts_substitute_multi(src, src, 1, &x, &a));
  CHECK(ixs_range_facts(src, x, &range));
  CHECK(range.has_lower && range.lower_p == 0);
  CHECK(range.has_upper && range.upper_p == 15);
  CHECK(ixs_range_facts(src, a, &range));
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
  CHECK(ixs_check_congruent_facts(dst, k, 4, 0) == IXS_CHECK_TRUE);
  CHECK(ixs_check_congruent_facts(dst, k, 8, 0) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_get_known_bits_facts(dst, k, &bits));
  CHECK((bits.known_zero & 3u) == 3u);
  CHECK((bits.known_one & 3u) == 0);
  CHECK(ixs_get_pow2_fact_facts(dst, k) == IXS_POW2_POSITIVE);

  CHECK(ixs_facts_assume_pred(offset_src,
                              ixs_cmp(ctx, ixs_mod(ctx, y, ixs_int(ctx, 6)),
                                      IXS_CMP_EQ, ixs_int(ctx, 2))));
  CHECK(ixs_facts_substitute(offset_dst, offset_src, y, four_k_plus_two));
  CHECK(ixs_check_congruent_facts(offset_dst, k, 3, 0) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_substitute(nonlinear_dst, src, y, nonlinear));
  CHECK(ixs_check_congruent_facts(nonlinear_dst, k, 4, 0) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_get_pow2_fact_facts(nonlinear_dst, k) == IXS_POW2_UNKNOWN);

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
  CHECK(ixs_check_congruent_facts(contradictory, k, 2, 0) == IXS_CHECK_UNKNOWN);
  CHECK(!ixs_range_facts(contradictory, k, &range));

  CHECK(ixs_facts_assume_pred(
      extreme_src, ixs_cmp(ctx, ixs_mod(ctx, y, ixs_int(ctx, INT64_MAX)),
                           IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(ixs_facts_substitute(extreme_dst, extreme_src, y, min_k));
  CHECK(ixs_check_congruent_facts(extreme_dst, k, INT64_MAX, 0) ==
        IXS_CHECK_TRUE);
  CHECK(ixs_facts_assume_pred(
      residue_src, ixs_cmp(ctx, ixs_mod(ctx, y, ixs_int(ctx, INT64_MAX)),
                           IXS_CMP_EQ, ixs_int(ctx, INT64_MAX - 2))));
  CHECK(ixs_get_symbol_congruence_facts(residue_src, y, &modulus, &residue));
  CHECK(modulus == INT64_MAX);
  CHECK(residue == INT64_MAX - 2);
  CHECK(ixs_facts_substitute(residue_dst, residue_src, y, ixs_neg(ctx, k)));
  CHECK(ixs_get_symbol_congruence_facts(residue_dst, k, &modulus, &residue));
  CHECK(modulus == INT64_MAX);
  CHECK(residue == 2);
  CHECK(ixs_check_congruent_facts(residue_dst, k, INT64_MAX, 2) ==
        IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(
      merge_src, ixs_cmp(ctx, ixs_mod(ctx, y, ixs_int(ctx, 2147483629)),
                         IXS_CMP_EQ, ixs_int(ctx, 456))));
  CHECK(ixs_facts_assume_pred(
      merge_dst, ixs_cmp(ctx, ixs_mod(ctx, k, ixs_int(ctx, 2147483647)),
                         IXS_CMP_EQ, ixs_int(ctx, 123))));
  CHECK(ixs_facts_substitute(merge_dst, merge_src, y, k));
  CHECK(ixs_check_congruent_facts(merge_dst, k, 2147483629, 456) ==
        IXS_CHECK_TRUE);
  CHECK(ixs_check_congruent_facts(merge_dst, k, 2147483647, 123) ==
        IXS_CHECK_TRUE);

  input.has_lower = true;
  input.has_upper = true;
  input.lower_p = 0;
  input.lower_q = 1;
  input.upper_p = 1;
  input.upper_q = 1;
  CHECK(ixs_facts_assume_range(range_src, x, &input));
  CHECK(ixs_facts_substitute(range_dst, range_src, x, min_offset));
  CHECK(ixs_range_facts(range_dst, min_offset, &range));
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
  CHECK(!ixs_range_facts(wrong_node_dst, y, &range));
  CHECK(!ixs_facts_substitute_multi(wrong_src_dst, other_src, 1, targets,
                                    replacements));
  CHECK(!ixs_range_facts(wrong_src_dst, y, &range));
  CHECK(!ixs_facts_substitute_multi(sentinel_dst, src, 1, sentinel_targets,
                                    replacements));
  CHECK(!ixs_range_facts(sentinel_dst, y, &range));
  CHECK(
      !ixs_facts_substitute_multi(null_array_dst, src, 1, NULL, replacements));
  CHECK(!ixs_range_facts(null_array_dst, y, &range));

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(!ixs_facts_substitute_multi(oom_dst, src, 1, targets, replacements));
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(!ixs_range_facts(oom_dst, y, &range));
  CHECK(ixs_range_facts(src, x, &range));
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
  CHECK(ixs_check_integer_valued_facts(facts, piecewise) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_facts_assume_pred(facts, congruence));
  CHECK(ixs_check_integer_valued_facts(facts, scaled) == IXS_CHECK_TRUE);
  CHECK(ixs_check_integer_valued_facts(facts, piecewise) == IXS_CHECK_TRUE);

  unreachable_values[0] = ixs_div(ctx, ixs_int(ctx, 1), x);
  unreachable_values[1] = x;
  unreachable_conds[0] = ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 0));
  unreachable_conds[1] = ixs_true(ctx);
  unreachable = ixs_pw(ctx, 2, unreachable_values, unreachable_conds);
  CHECK(ixs_facts_assume_pred(range_facts,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_check_integer_valued_facts(range_facts, unreachable) ==
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
  CHECK(ixs_check_divisible_facts(facts, k, 32) == IXS_CHECK_TRUE);
  CHECK(ixs_check_divisible_facts(facts, k, -32) == IXS_CHECK_TRUE);
  CHECK(ixs_check_divisible_facts(facts, k, 64) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_divisible_facts(facts, ixs_int(ctx, 64), 32) ==
        IXS_CHECK_TRUE);
  CHECK(ixs_check_divisible_facts(facts, ixs_int(ctx, 65), 32) ==
        IXS_CHECK_FALSE);
  CHECK(ixs_check_divisible_facts(facts, ixs_rat(ctx, 1, 2), 1) ==
        IXS_CHECK_FALSE);
  CHECK(ixs_check_divisible_facts(facts, ixs_div(ctx, ixs_int(ctx, 1), k), 1) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_check_divisible_facts(facts, ixs_int(ctx, INT64_MIN), INT64_MIN) ==
        IXS_CHECK_TRUE);
  CHECK(ixs_check_divisible_facts(facts, ixs_int(ctx, INT64_MAX), INT64_MIN) ==
        IXS_CHECK_FALSE);
  CHECK(ixs_check_divisible_facts(facts, ixs_int(ctx, 0), INT64_MIN) ==
        IXS_CHECK_TRUE);
  CHECK(ixs_check_divisible_facts(facts, ixs_int(ctx, INT64_MIN), -1) ==
        IXS_CHECK_TRUE);

  ixs_ctx_clear_errors(ctx);
  CHECK(ixs_check_divisible_facts(facts, k, 0) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "modulus must be nonzero") != NULL);

  ixs_ctx_destroy(ctx);
}

static void test_public_known_bits_propagation(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *item = ixs_sym(ctx, "item");
  ixs_node *slot = ixs_sym(ctx, "slot");
  ixs_node *x = ixs_sym(ctx, "known_x");
  ixs_node *y = ixs_sym(ctx, "known_y");
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
                              ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 0))));

  CHECK(ixs_get_known_bits_facts(facts, ixs_int(ctx, 5), &bits));
  CHECK(bits.known_zero == ~(uint64_t)5);
  CHECK(bits.known_one == 5u);
  CHECK(bits.pow2 == IXS_POW2_UNKNOWN);

  CHECK(ixs_get_known_bits_facts(facts, slot, &bits));
  CHECK((bits.known_zero & ~(uint64_t)15) == ~(uint64_t)15);
  CHECK((bits.known_one & 15u) == 0);

  CHECK(
      ixs_get_known_bits_facts(facts, ixs_add(ctx, x, ixs_int(ctx, 3)), &bits));
  CHECK(((bits.known_zero | bits.known_one) & 15u) == 15u);
  CHECK((bits.known_one & 15u) == 8u);

  CHECK(ixs_get_known_bits_facts(facts, ixs_mul(ctx, ixs_int(ctx, 16), x),
                                 &bits));
  CHECK(((bits.known_zero | bits.known_one) & 255u) == 255u);
  CHECK((bits.known_one & 255u) == 80u);

  CHECK(ixs_get_known_bits_facts(facts, ixs_xor(ctx, x, y), &bits));
  CHECK(((bits.known_zero | bits.known_one) & 15u) == 15u);
  CHECK((bits.known_one & 15u) == 15u);

  CHECK(ixs_get_known_bits_facts(facts, scaled16, &a_bits));
  CHECK(ixs_get_known_bits_facts(facts, slot, &b_bits));
  CHECK(((~a_bits.known_zero) & (~b_bits.known_zero)) == 0);
  CHECK(ixs_get_known_bits_facts(facts, scaled8, &a_bits));
  CHECK((((~a_bits.known_zero) & (~b_bits.known_zero)) & 8u) != 0);

  /* Dividing by 2^62 can expose source bits 62 and 63 only.  Source bits
   * beyond the low-64 abstraction stay unknown. */
  CHECK(ixs_get_known_bits_facts(facts, wide, &bits));
  CHECK(((bits.known_zero | bits.known_one) & ~(uint64_t)3) == 0);

  CHECK(
      ixs_facts_assume_pred(src, ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, 7))));
  CHECK(ixs_facts_substitute(subst, src, x, y));
  CHECK(ixs_get_known_bits_facts(subst, y, &bits));
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

  CHECK(ixs_get_known_bits_facts(facts, x, &bits));
  CHECK(bits.known_zero == 0 && bits.known_one == 0);
  CHECK(ixs_get_known_bits_facts(facts, ixs_rat(ctx, 1, 2), &bits));
  CHECK(bits.known_zero == 0 && bits.known_one == 0);

  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 10))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 5))));
  bits.known_zero = ~(uint64_t)0;
  bits.known_one = ~(uint64_t)0;
  bits.pow2 = IXS_POW2_POSITIVE;
  CHECK(!ixs_get_known_bits_facts(contradictory, x, &bits));
  CHECK(bits.known_zero == 0 && bits.known_one == 0);
  CHECK(bits.pow2 == IXS_POW2_UNKNOWN);

  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_get_known_bits_facts(facts, ixs_sym(other, "x"), &bits));
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_get_known_bits_facts(facts, ctx->sentinel_error, &bits));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "sentinel") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_get_known_bits_facts(facts, NULL, &bits));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "NULL expression") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_get_known_bits_facts(facts, x, NULL));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "NULL output") != NULL);

  bits.known_zero = ~(uint64_t)0;
  bits.known_one = ~(uint64_t)0;
  CHECK(!ixs_get_known_bits_facts(NULL, x, &bits));
  CHECK(bits.known_zero == 0 && bits.known_one == 0);

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
  CHECK(ixs_get_symbol_congruence_facts(facts, k, &modulus, &residue));
  CHECK(modulus == 32 && residue == 5);

  CHECK(!ixs_get_symbol_congruence_facts(facts, x, &modulus, &residue));
  CHECK(modulus == 0 && residue == 0);
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, ixs_mod(ctx, k, ixs_int(ctx, 8)),
                                      IXS_CMP_EQ, ixs_int(ctx, 1))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, ixs_mod(ctx, k, ixs_int(ctx, 8)),
                                      IXS_CMP_EQ, ixs_int(ctx, 2))));
  CHECK(!ixs_get_symbol_congruence_facts(contradictory, k, &modulus, &residue));

  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_get_symbol_congruence_facts(facts, ixs_add(ctx, k, x), &modulus,
                                         &residue));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "must be a symbol") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_get_symbol_congruence_facts(facts, ixs_sym(other, "k"), &modulus,
                                         &residue));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_get_symbol_congruence_facts(facts, ctx->sentinel_error, &modulus,
                                         &residue));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "sentinel") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_get_symbol_congruence_facts(facts, k, &modulus, &modulus));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "distinct") != NULL);

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
  CHECK(ixs_check_congruent_facts(facts, k, 32, 5) == IXS_CHECK_TRUE);
  CHECK(ixs_check_congruent_facts(facts, k, 32, 6) == IXS_CHECK_FALSE);
  CHECK(ixs_check_congruent_facts(facts, k, -32, -27) == IXS_CHECK_TRUE);
  CHECK(ixs_check_congruent_facts(facts, k, 16, 5) == IXS_CHECK_TRUE);
  CHECK(ixs_check_congruent_facts(facts, k, 64, 5) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_congruent_facts(
            facts,
            ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 3), k), ixs_int(ctx, 2)), 32,
            17) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(nonpow,
                              ixs_cmp(ctx, ixs_mod(ctx, n, ixs_int(ctx, 15)),
                                      IXS_CMP_EQ, ixs_int(ctx, 4))));
  CHECK(ixs_check_congruent_facts(
            nonpow,
            ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 3), n), ixs_int(ctx, 2)), 15,
            14) == IXS_CHECK_TRUE);
  CHECK(ixs_check_congruent_facts(nonpow, ixs_mul(ctx, ixs_int(ctx, 5), n), 15,
                                  5) == IXS_CHECK_TRUE);
  CHECK(ixs_check_congruent_facts(
            nonpow,
            ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 6), x), ixs_int(ctx, 2)), 3,
            2) == IXS_CHECK_TRUE);

  CHECK(ixs_check_congruent_facts(facts, ixs_int(ctx, INT64_MIN), INT64_MIN,
                                  0) == IXS_CHECK_TRUE);
  CHECK(ixs_check_congruent_facts(facts, ixs_int(ctx, INT64_MAX), INT64_MIN,
                                  -1) == IXS_CHECK_TRUE);
  CHECK(ixs_check_congruent_facts(facts, int64_scaled, INT64_MIN, 7) ==
        IXS_CHECK_TRUE);
  CHECK(ixs_check_congruent_facts(facts, ixs_int(ctx, 65), 32, 1) ==
        IXS_CHECK_TRUE);
  CHECK(ixs_check_congruent_facts(facts, ixs_int(ctx, 65), 32, 2) ==
        IXS_CHECK_FALSE);
  CHECK(ixs_check_congruent_facts(facts, ixs_rat(ctx, 1, 2), 3, 1) ==
        IXS_CHECK_FALSE);

  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 10))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 5))));
  CHECK(ixs_check_congruent_facts(contradictory, ixs_int(ctx, 1), 2, 1) ==
        IXS_CHECK_UNKNOWN);

  ixs_ctx_clear_errors(ctx);
  CHECK(ixs_check_congruent_facts(facts, x, 0, 0) == IXS_CHECK_UNKNOWN);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "modulus must be nonzero") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(ixs_check_congruent_facts(facts, ixs_sym(other, "x"), 8, 0) ==
        IXS_CHECK_UNKNOWN);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(ixs_check_congruent_facts(facts, ctx->sentinel_error, 8, 0) ==
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
  ixs_facts *all_true = ixs_facts_create(ctx);
  ixs_facts *one_false = ixs_facts_create(ctx);
  ixs_facts *all_false = ixs_facts_create(ctx);
  ixs_facts *partial = ixs_facts_create(ctx);

  CHECK(ixs_facts_assume_pred(all_true, x_nonnegative));
  CHECK(ixs_facts_assume_pred(all_true, y_small));
  CHECK(ixs_facts_assume_pred(all_true,
                              ixs_cmp(ctx, y, IXS_CMP_NE, ixs_int(ctx, 2))));
  CHECK(ixs_check_predicate_facts(all_true, both) == IXS_CHECK_TRUE);
  CHECK(ixs_check_predicate_facts(
            all_true, ixs_cmp(ctx, y, IXS_CMP_NE, ixs_int(ctx, 2))) ==
        IXS_CHECK_TRUE);
  CHECK(ixs_check_predicate_facts(all_true, either) == IXS_CHECK_TRUE);
  CHECK(ixs_check_predicate_facts(all_true, ixs_not(ctx, both)) ==
        IXS_CHECK_FALSE);

  CHECK(ixs_facts_assume_pred(one_false,
                              ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 0))));
  CHECK(ixs_check_predicate_facts(one_false, both) == IXS_CHECK_FALSE);
  CHECK(ixs_check_predicate_facts(one_false, either) == IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(all_false,
                              ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(all_false,
                              ixs_cmp(ctx, y, IXS_CMP_GE, ixs_int(ctx, 4))));
  CHECK(ixs_check_predicate_facts(all_false, either) == IXS_CHECK_FALSE);
  CHECK(ixs_check_predicate_facts(all_false, ixs_not(ctx, either)) ==
        IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(partial,
                              ixs_cmp(ctx, x, IXS_CMP_GT, ixs_int(ctx, 0))));
  CHECK(ixs_check_predicate_facts(partial, not_x) == IXS_CHECK_FALSE);
  CHECK(ixs_check_predicate_facts(partial, ixs_not(ctx, y)) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_predicate_facts(partial, both) == IXS_CHECK_UNKNOWN);

  ixs_ctx_clear_errors(ctx);
  CHECK(ixs_check_predicate_facts(partial, ixs_and(ctx, x, ixs_int(ctx, 7))) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "not a predicate tree") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(ixs_check_predicate_facts(partial, ixs_or(ctx, x, y)) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "not a predicate tree") != NULL);

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

  CHECK(ixs_equivalent_facts(empty, x, x) == IXS_CHECK_TRUE);
  CHECK(ixs_equivalent_facts(empty, polynomial, expanded) == IXS_CHECK_TRUE);
  CHECK(ixs_equivalent_facts(empty, and_lhs, and_rhs) == IXS_CHECK_TRUE);
  CHECK(ixs_equivalent_facts(empty, or_lhs, or_rhs) == IXS_CHECK_TRUE);

  CHECK(ixs_equivalent_facts(empty, reciprocal, reciprocal) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_equivalent_facts(empty, reciprocal_algebraic_lhs,
                             reciprocal_algebraic_rhs) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_facts_assume_pred(nonzero,
                              ixs_cmp(ctx, x, IXS_CMP_NE, ixs_int(ctx, 0))));
  CHECK(ixs_equivalent_facts(nonzero, reciprocal, reciprocal) ==
        IXS_CHECK_TRUE);
  CHECK(ixs_equivalent_facts(nonzero, reciprocal_algebraic_lhs,
                             reciprocal_algebraic_rhs) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(xor_facts,
                              ixs_cmp(ctx, slot, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      xor_facts, ixs_cmp(ctx, slot, IXS_CMP_LE, ixs_int(ctx, 15))));
  CHECK(ixs_facts_assume_pred(xor_facts,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(xor_facts,
                              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 100))));
  CHECK(ixs_equivalent_facts(xor_facts, disjoint_xor, disjoint_add) ==
        IXS_CHECK_TRUE);
  CHECK(ixs_equivalent_facts(xor_facts, overlap_xor, overlap_add) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(mod_facts,
                              ixs_cmp(ctx, ixs_mod(ctx, k, ixs_int(ctx, 16)),
                                      IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(ixs_equivalent_facts(mod_facts, mod_lhs, mod_rhs) == IXS_CHECK_TRUE);
  CHECK(ixs_equivalent_facts(mod_facts, ordinary_lhs, ordinary_rhs) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_facts_assume_pred(grid_facts, x_grid));
  CHECK(ixs_equivalent_facts(grid_facts, x_zero, x_grid) == IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(opposite,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 10))));
  CHECK(ixs_equivalent_facts(opposite, ordinary_lhs,
                             ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 8))) ==
        IXS_CHECK_FALSE);
  CHECK(ixs_equivalent_facts(empty, ordinary_lhs,
                             ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 9))) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 10))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 5))));
  CHECK(ixs_equivalent_facts(contradictory, ixs_int(ctx, 1), ixs_int(ctx, 2)) ==
        IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_public_equivalence_invalid_inputs(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "equiv_invalid_x");
  ixs_facts *facts = ixs_facts_create(ctx);

  ixs_ctx_clear_errors(ctx);
  CHECK(ixs_equivalent_facts(facts, x, ixs_sym(other, "x")) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(ixs_equivalent_facts(facts, ctx->sentinel_error, ctx->sentinel_error) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "sentinel") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(ixs_check_predicate_facts(facts, ixs_sym(other, "p")) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(ixs_check_predicate_facts(facts, ctx->sentinel_parse_error) ==
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

  CHECK(ixs_constant_difference_facts(
      facts, ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 4), x), ixs_int(ctx, 4)),
      ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 4), x), ixs_int(ctx, 1)), &delta));
  CHECK(delta == 3);
  CHECK(ixs_constant_difference_facts(
      facts, ixs_mul(ctx, ixs_int(ctx, 4), ixs_add(ctx, x, ixs_int(ctx, 1))),
      ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 4), x), ixs_int(ctx, 1)), &delta));
  CHECK(delta == 3);
  delta = 9;
  CHECK(!ixs_constant_difference_facts(facts, ixs_int(ctx, INT64_MAX),
                                       ixs_int(ctx, -1), &delta));
  CHECK(delta == 0);

  CHECK(ixs_affine_decompose_facts(
      facts, ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 8), i), base), i,
      &coefficient, &residual));
  CHECK(ixs_same_node(coefficient, ixs_int(ctx, 8)));
  CHECK(ixs_same_node(residual, base));
  CHECK(ixs_affine_decompose_facts(
      facts, ixs_mul(ctx, ixs_int(ctx, 8), ixs_add(ctx, i, base)), i,
      &coefficient, &residual));
  CHECK(ixs_same_node(coefficient, ixs_int(ctx, 8)));
  CHECK(ixs_same_node(residual, ixs_mul(ctx, ixs_int(ctx, 8), base)));
  CHECK(ixs_affine_decompose_facts(facts, ixs_div(ctx, i, ixs_int(ctx, 2)), i,
                                   &coefficient, &residual));
  CHECK(ixs_same_node(coefficient, ixs_rat(ctx, 1, 2)));
  CHECK(ixs_same_node(residual, ixs_int(ctx, 0)));

  CHECK(!ixs_affine_decompose_facts(facts, ixs_mul(ctx, i, i), i, &coefficient,
                                    &residual));
  CHECK(coefficient == NULL && residual == NULL);
  CHECK(!ixs_affine_decompose_facts(facts, ixs_mul(ctx, base, i), i,
                                    &coefficient, &residual));
  CHECK(coefficient == NULL && residual == NULL);
  CHECK(!ixs_affine_decompose_facts(facts, ixs_mod(ctx, i, ixs_int(ctx, 8)), i,
                                    &coefficient, &residual));
  CHECK(coefficient == NULL && residual == NULL);

  ixs_ctx_destroy(ctx);
}

static void test_public_finite_difference_and_additive_split(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *i = ixs_sym(ctx, "difference_i");
  ixs_node *base = ixs_sym(ctx, "difference_base");
  ixs_node *one = ixs_int(ctx, 1);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_node *difference = NULL;
  ixs_node *residual = NULL;
  int64_t constant = 0;

  CHECK(ixs_finite_difference_facts(
      facts, ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 8), i), base), i, one,
      &difference));
  CHECK(ixs_same_node(difference, ixs_int(ctx, 8)));
  CHECK(ixs_finite_difference_facts(facts, ixs_mul(ctx, i, i), i, one,
                                    &difference));
  CHECK(ixs_same_node(difference, ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), i),
                                          ixs_int(ctx, 1))));
  CHECK(ixs_finite_difference_facts(
      facts, ixs_mul(ctx, ixs_int(ctx, 8), ixs_add(ctx, i, base)), i, one,
      &difference));
  CHECK(ixs_same_node(difference, ixs_int(ctx, 8)));
  CHECK(!ixs_finite_difference_facts(facts, i, i, i, &difference));
  CHECK(difference == NULL);
  CHECK(!ixs_finite_difference_facts(facts, ixs_add(ctx, i, ixs_int(ctx, 1)), i,
                                     ixs_int(ctx, INT64_MAX), &difference));
  CHECK(difference == NULL);

  CHECK(ixs_split_additive_constant_facts(
      facts, ixs_add(ctx, base, ixs_int(ctx, 96)), &residual, &constant));
  CHECK(ixs_same_node(residual, base));
  CHECK(constant == 96);
  CHECK(ixs_split_additive_constant_facts(
      facts,
      ixs_mul(ctx, ixs_int(ctx, 8), ixs_add(ctx, base, ixs_int(ctx, 12))),
      &residual, &constant));
  CHECK(ixs_same_node(residual, ixs_mul(ctx, ixs_int(ctx, 8), base)));
  CHECK(constant == 96);
  CHECK(ixs_split_additive_constant_facts(
      facts, ixs_add(ctx, base, ixs_int(ctx, INT64_MAX)), &residual,
      &constant));
  CHECK(ixs_same_node(residual, base) && constant == INT64_MAX);
  CHECK(ixs_split_additive_constant_facts(
      facts, ixs_add(ctx, base, ixs_int(ctx, INT64_MIN)), &residual,
      &constant));
  CHECK(ixs_same_node(residual, base) && constant == INT64_MIN);
  CHECK(ixs_split_additive_constant_facts(facts, base, &residual, &constant));
  CHECK(ixs_same_node(residual, base) && constant == 0);
  CHECK(!ixs_split_additive_constant_facts(
      facts, ixs_add(ctx, base, ixs_rat(ctx, 1, 2)), &residual, &constant));
  CHECK(residual == NULL && constant == 0);

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
  CHECK(!ixs_affine_decompose_facts(empty, piecewise, i, &coefficient,
                                    &residual));
  CHECK(ixs_facts_assume_pred(nonnegative, condition));
  CHECK(ixs_affine_decompose_facts(nonnegative, piecewise, i, &coefficient,
                                   &residual));
  CHECK(ixs_same_node(coefficient, ixs_int(ctx, 8)));
  CHECK(ixs_same_node(residual, base));

  CHECK(!ixs_constant_difference_facts(empty, reciprocal, reciprocal, &delta));
  CHECK(delta == 0);
  CHECK(ixs_facts_assume_pred(nonzero,
                              ixs_cmp(ctx, i, IXS_CMP_NE, ixs_int(ctx, 0))));
  CHECK(ixs_constant_difference_facts(nonzero, reciprocal, reciprocal, &delta));
  CHECK(delta == 0);

  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, i, IXS_CMP_GE, ixs_int(ctx, 10))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, i, IXS_CMP_LE, ixs_int(ctx, 5))));
  CHECK(!ixs_constant_difference_facts(contradictory, i, i, &delta));
  CHECK(!ixs_affine_decompose_facts(contradictory, i, i, &coefficient,
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
  CHECK(!ixs_constant_difference_facts(facts, x, other_x, &value));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_constant_difference_facts(facts, ctx->sentinel_error, x, &value));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "sentinel") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_affine_decompose_facts(facts, x, other_x, &first, &second));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_affine_decompose_facts(facts, x, ixs_add(ctx, x, ixs_int(ctx, 1)),
                                    &first, &second));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "must be a symbol") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_finite_difference_facts(facts, x, x, other_x, &first));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_finite_difference_facts(facts, ctx->sentinel_error, x,
                                     ixs_int(ctx, 1), &first));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "sentinel") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_split_additive_constant_facts(facts, other_x, &first, &value));
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_split_additive_constant_facts(facts, ctx->sentinel_error, &first,
                                           &value));
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
  CHECK(result.status == IXS_EXACT_DIVIDE_ERROR);
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
  ixs_node *expr = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 64), item),
                           ixs_mul(ctx, ixs_int(ctx, 32), slot));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);
  ixs_exact_divide_result result;

  CHECK(ixs_facts_assume_pred(
      contradictory, ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 10))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, item, IXS_CMP_LE, ixs_int(ctx, 5))));
  result = ixs_try_exact_divide_facts(contradictory, expr, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_UNKNOWN);
  CHECK(result.quotient == NULL);

  ixs_ctx_clear_errors(ctx);
  result = ixs_try_exact_divide_facts(facts, expr, 0);
  CHECK(result.status == IXS_EXACT_DIVIDE_ERROR);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "divisor must be nonzero") != NULL);
  result = ixs_try_exact_divide_facts(facts, ixs_sym(other, "item"), 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_ERROR);
  CHECK(strstr(ixs_ctx_error(ctx, 1), "different context") != NULL);
  result = ixs_try_exact_divide_facts(facts, ctx->sentinel_error, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_ERROR);
  CHECK(strstr(ixs_ctx_error(ctx, 2), "sentinel expression") != NULL);
  result = ixs_try_exact_divide_facts(facts, NULL, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_ERROR);
  CHECK(strstr(ixs_ctx_error(ctx, 3), "NULL expression") != NULL);

  ixs_ctx_clear_errors(ctx);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  result = ixs_try_exact_divide_facts(facts, expr, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_ERROR);
  CHECK(result.quotient == NULL);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "out of memory") != NULL);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  result = ixs_try_exact_divide_facts(facts, expr, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  CHECK(result.quotient != NULL);

  result = ixs_try_exact_divide_facts(NULL, expr, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_ERROR);
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
  CHECK(ixs_check_integer_valued_facts(contradictory, x) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_divisible_facts(contradictory, ixs_int(ctx, 64), 32) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_check_integer_valued(ctx, other_x, NULL, 0) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_integer_valued(ctx, ctx->sentinel_error, NULL, 0) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_integer_valued_facts(facts, other_x) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_integer_valued_facts(facts, ctx->sentinel_error) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_divisible_facts(facts, other_x, 8) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_divisible_facts(facts, ctx->sentinel_error, 8) ==
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

static void test_public_defined_facts_and_invalid(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "defined_fact_x");
  ixs_node *other_x = ixs_sym(other, "defined_fact_x");
  ixs_node *reciprocal = ixs_div(ctx, ixs_int(ctx, 1), x);
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
  CHECK(ixs_check_defined_facts(positive, reciprocal) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(zero,
                              ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(ixs_check_defined_facts(zero, reciprocal) == IXS_CHECK_FALSE);
  CHECK(ixs_facts_assume_pred(nonzero,
                              ixs_cmp(ctx, x, IXS_CMP_NE, ixs_int(ctx, 0))));
  CHECK(ixs_check_defined_facts(nonzero, reciprocal) == IXS_CHECK_TRUE);
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 2))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 1))));
  CHECK(ixs_check_defined_facts(contradictory, reciprocal) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_check_defined(ctx, NULL, NULL, 0) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_defined(ctx, ctx->sentinel_error, NULL, 0) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_defined(ctx, other_x, NULL, 0) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_defined_facts(positive, other_x) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_defined_facts(positive, ctx->sentinel_parse_error) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_defined_facts(NULL, x) == IXS_CHECK_UNKNOWN);

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(ixs_check_defined_facts(positive, reciprocal) == IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(ixs_check_defined_facts(positive, reciprocal) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(other);
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
  ixs_mulfactor guarded_factor;
  ixs_pwcase one_case;
  unsigned i;

  for (i = 0; i < 300; i++)
    shallow = ixs_node_floor(ctx, shallow);
  CHECK(ixs_check_defined(ctx, shallow, NULL, 0) == IXS_CHECK_TRUE);

  deep = shallow;
  for (i = 300; i < 1100; i++)
    deep = ixs_node_floor(ctx, deep);
  CHECK(ixs_check_defined(ctx, deep, NULL, 0) == IXS_CHECK_UNKNOWN);

  for (i = 0; i < 60; i++)
    shared = ixs_node_binary(ctx, IXS_MAX, shared, shared, IXS_CMP_EQ);
  CHECK(ixs_check_defined(ctx, shared, NULL, 0) == IXS_CHECK_TRUE);
  guarded_factor.base = shared;
  guarded_factor.exp = -1;
  guarded = ixs_node_mul(ctx, one, 1, &guarded_factor);
  CHECK(ixs_check_defined(ctx, guarded, &shared_positive, 1) == IXS_CHECK_TRUE);
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
  CHECK(ixs_check_defined(ctx, nested, NULL, 0) == IXS_CHECK_UNKNOWN);

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

  CHECK(ixs_facts_assume_pred(facts, lo));
  CHECK(ixs_facts_assume_pred(facts, hi));

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(ixs_simplify_facts(facts, piecewise) == NULL);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(ixs_simplify_facts(facts, mod) == x);

  batch[0] = mod;
  batch[1] = piecewise;
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  ixs_simplify_batch_facts(facts, batch, 2);
  CHECK(batch[0] == NULL);
  CHECK(batch[1] == NULL);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(ixs_simplify_facts(facts, mod) == x);

  poisoned = ixs_facts_create(ctx);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(!ixs_facts_assume_pred(poisoned, lo));
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(ixs_is_domain_error(ixs_simplify_facts(poisoned, mod)));
  CHECK(ixs_check_facts(poisoned, lo) == IXS_CHECK_UNKNOWN);

  (ixs_session_reset)(IXS_TEST_SESSION(ctx));
  CHECK(ixs_simplify_facts(facts, mod) == NULL);
  facts = ixs_facts_create(ctx);
  CHECK(facts != NULL);
  CHECK(ixs_simplify_facts(facts, mod) == mod);
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
    CHECK(ixs_simplify_facts(stale, raw_x) == NULL);

    ixs_session_init(&session, raw_ctx);
    CHECK(ixs_simplify_facts(stale, raw_x) == NULL);
    fresh = (ixs_facts_create)(&session);
    CHECK(fresh != NULL);
    CHECK(ixs_simplify_facts(fresh, raw_x) == raw_x);
    ixs_session_destroy(&session);
    (ixs_ctx_destroy)(raw_ctx);
  }
}

/* ------------------------------------------------------------------ */
/*  main                                                              */
/* ------------------------------------------------------------------ */

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

  /* Bounds: expression overrides */
  test_bounds_expr_override();
  test_bounds_expr_override_invalidates_cache();
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

  /* Bounds: public range API */
  test_public_range_basic();
  test_public_range_unbounded();
  test_public_range_rational();
  test_public_range_unknown();
  test_public_range_int64_extrema();
  test_public_range_mod_int64_min_step();
  test_public_range_mod_requires_positive_divisor();
  test_public_range_composite_predicate_fact();
  test_public_facts_range_and_transfer();
  test_public_range_powers();
  test_public_range_xor();
  test_public_range_piecewise();
  test_failed_expand_is_not_expression_fact_alias();
  test_public_facts_assume_conjunction();
  test_ctx_node_ownership_uses_intern_table();
  test_compound_assumption_legacy_fact_parity();
  test_fact_check_xor_cancellation_parity();
  test_compound_assumption_rejection_is_atomic();
  test_compound_assumption_boolean_constants();
  test_public_facts_assume_deep_conjunction();
  test_public_facts_substitute_preserves_symbol_facts();
  test_public_facts_substitute_multi_semantics();
  test_public_facts_substitute_inverse_facts();
  test_public_facts_substitute_contradiction_and_extrema();
  test_public_facts_substitute_failures_are_atomic();
  test_public_structural_and_assumption_integrality();
  test_public_fact_integrality_piecewise();
  test_public_fact_divisibility();
  test_public_known_bits_propagation();
  test_public_known_bits_failures();
  test_public_symbol_congruence();
  test_public_congruence_query();
  test_public_predicate_tree_query();
  test_public_total_equivalence();
  test_public_equivalence_invalid_inputs();
  test_public_affine_and_constant_difference();
  test_public_finite_difference_and_additive_split();
  test_public_algebra_helpers_use_facts();
  test_public_algebra_helper_invalid_inputs();
  test_public_exact_divide_basic();
  test_public_exact_divide_extrema_and_overflow();
  test_public_exact_divide_invalid_and_oom();
  test_public_integrality_invalid_and_contradictory();
  test_public_defined_reciprocal_and_children();
  test_public_defined_mod_contract();
  test_public_defined_piecewise_first_match();
  test_public_defined_piecewise_condition();
  test_public_defined_facts_and_invalid();
  test_public_defined_traversal_bounds_and_sharing();
  test_fact_simplify_session_lifetime_and_oom();

  printf("test_bounds: %d/%d passed\n", tests_passed, tests_run);
  return tests_passed == tests_run ? 0 : 1;
}
