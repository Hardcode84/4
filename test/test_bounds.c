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
  CHECK(b.predicate_equivalence_depth == 0u);

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

static void test_bounds_propagate_trunc(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_bounds b;
  ixs_node *x = ixs_sym(ctx, "trunc_bounds_x");
  ixs_node *expr = ixs_trunc(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)));
  ixs_interval iv;

  CHECK(ixs_bounds_init(&b, ixs_test_scratch(ctx)));
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, -8)));
  ixs_bounds_add_assumption(&b, ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 7)));
  iv = ixs_bounds_get(&b, expr);
  CHECK(iv.valid);
  CHECK(ixs_rat_cmp(iv.lo_p, iv.lo_q, -2, 1) == 0);
  CHECK(ixs_rat_cmp(iv.hi_p, iv.hi_q, 2, 1) == 0);

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
  b.predicate_equivalence_depth = 3u;
  CHECK(ixs_bounds_fork(&child, &b));
  CHECK(child.predicate_equivalence_depth == 3u);
  b.predicate_equivalence_depth = 0u;
  child.predicate_equivalence_depth = 0u;
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
  CHECK(child.predicate_equivalence_depth == 0u);
  ixs_bounds_destroy(&b);
  CHECK(b.predicate_equivalence_depth == 0u);
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

  CHECK(ixs_range_facts(facts, ixs_mod(ctx, value, modulus), &range));
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
  nested = make_nested_query_root(ctx, "finite_tracking");
  CHECK(ctx->bounds_query_state == NULL);
  (void)test_ixs_equivalent_facts(facts, flat, nested);
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

  for (query = 0; query < 4u; query++) {
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

static void check_radix_certificate_case(ixs_ctx *ctx, ixs_node *expr,
                                         ixs_node *domain,
                                         ixs_check_result expected) {
  ixs_node *query = ixs_cmp(ctx, expr, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_facts *facts = ixs_facts_create(ctx);

  CHECK(expr && domain && query && facts);
  CHECK(ixs_check(ctx, query, &domain, 1) == expected);
  CHECK(ixs_facts_assume_pred(facts, domain));
  CHECK(test_ixs_check_facts(facts, query) == expected);
}

static void test_bounds_check_wave_radix_floor_sums(void) {
  static const char asmbuf_text[] =
      "-65280*floor(wi/128) + 32768*floor(wi/64) - "
      "8176*floor(Mod(wi, 64)/16) + 512*Mod(wi, 64)";
  static const char aiter_text[] =
      "16*wi + 16384*raw1 + 3072*floor(wi/64) - 15872*floor(wi/256) - "
      "3840*floor(Mod(wi, 64)/32) + 1792*floor(Mod(wi, 64)/16)";
  static const char invalid_text[] =
      "-65280*floor(wi/128) + 32768*floor(wi/64) - "
      "8193*floor(Mod(wi, 64)/16) + 512*Mod(wi, 64)";
  static const char domain_text[] =
      "wi >= 0 & wi <= 255 & raw1 >= 0 & raw1 <= 1";
  static const char missing_lower_text[] = "wi <= 255 & raw1 >= 0 & raw1 <= 1";
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *asmbuf = ixs_parse_expr(ctx, asmbuf_text, strlen(asmbuf_text));
  ixs_node *offset = ixs_add(ctx, asmbuf, ixs_int(ctx, 8192));
  ixs_node *aiter = ixs_parse_expr(ctx, aiter_text, strlen(aiter_text));
  ixs_node *invalid = ixs_parse_expr(ctx, invalid_text, strlen(invalid_text));
  ixs_node *domain = ixs_parse_pred(ctx, domain_text, strlen(domain_text));
  ixs_node *missing_lower =
      ixs_parse_pred(ctx, missing_lower_text, strlen(missing_lower_text));
  ixs_node *wi_at_48 = ixs_parse_pred(ctx, "wi == 48", strlen("wi == 48"));
  ixs_node *contradiction =
      ixs_parse_pred(ctx, "wi >= 300", strlen("wi >= 300"));
  ixs_node *asmbuf_query = ixs_cmp(ctx, asmbuf, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *oom_facts = ixs_facts_create(ctx);
  ixs_node *contradictory_domain;
  size_t active_count;
  size_t nesting;

  CHECK(ctx && asmbuf && offset && aiter && invalid && domain &&
        missing_lower && wi_at_48 && contradiction && asmbuf_query && facts &&
        oom_facts);
  check_radix_certificate_case(ctx, asmbuf, domain, IXS_CHECK_TRUE);
  check_radix_certificate_case(ctx, offset, domain, IXS_CHECK_TRUE);
  check_radix_certificate_case(ctx, aiter, domain, IXS_CHECK_TRUE);
  check_radix_certificate_case(ctx, invalid, domain, IXS_CHECK_UNKNOWN);
  check_radix_certificate_case(ctx, invalid, wi_at_48, IXS_CHECK_FALSE);
  check_radix_certificate_case(ctx, asmbuf, missing_lower, IXS_CHECK_UNKNOWN);

  contradictory_domain = ixs_and(ctx, domain, contradiction);
  check_radix_certificate_case(ctx, asmbuf, contradictory_domain,
                               IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(facts, domain));
  CHECK(test_ixs_check_facts(facts, asmbuf_query) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(facts, asmbuf_query) == IXS_CHECK_TRUE);
  ixs_bounds_query_stats(&facts->bounds, NULL, NULL, NULL, NULL, NULL, NULL,
                         NULL, &active_count, &nesting);
  CHECK(facts->bounds.query_tracking_depth == 0 && active_count == 0 &&
        nesting == 0);

  CHECK(ixs_facts_assume_pred(oom_facts, domain));
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(test_ixs_check_facts(oom_facts, asmbuf_query) == IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  ixs_ctx_clear_errors(ctx);
  ixs_bounds_query_stats(&oom_facts->bounds, NULL, NULL, NULL, NULL, NULL, NULL,
                         NULL, &active_count, &nesting);
  CHECK(oom_facts->bounds.query_tracking_depth == 0 && active_count == 0 &&
        nesting == 0);
  CHECK(test_ixs_check_facts(oom_facts, asmbuf_query) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(oom_facts, asmbuf_query) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_bounds_check_radix_certificate_guards(void) {
  static const char domain_text[] = "wi >= 0 & wi <= 255";
  static const char four_symbol_domain_text[] =
      "a >= 0 & a <= 31 & b >= 0 & b <= 31 & "
      "c >= 0 & c <= 31 & d >= 0 & d <= 31";
  static const char five_symbol_domain_text[] =
      "a >= 0 & a <= 31 & b >= 0 & b <= 31 & "
      "c >= 0 & c <= 31 & d >= 0 & d <= 31 & x >= 0 & x <= 31";
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *domain = ixs_parse_pred(ctx, domain_text, strlen(domain_text));
  ixs_node *small_domain =
      ixs_parse_pred(ctx, "wi >= 0 & wi <= 31", strlen("wi >= 0 & wi <= 31"));
  ixs_node *four_symbol_domain = ixs_parse_pred(
      ctx, four_symbol_domain_text, strlen(four_symbol_domain_text));
  ixs_node *five_symbol_domain = ixs_parse_pred(
      ctx, five_symbol_domain_text, strlen(five_symbol_domain_text));
  ixs_node *nonintegral = ixs_parse_expr(ctx, "1/2*wi - 1/2*floor(wi/2)",
                                         strlen("1/2*wi - 1/2*floor(wi/2)"));
  ixs_node *negative_divisor = ixs_parse_expr(ctx, "-wi - 2*floor(-wi/2)",
                                              strlen("-wi - 2*floor(-wi/2)"));
  ixs_node *slot_limit = ixs_parse_expr(
      ctx,
      "a - floor(a/2) + b - floor(b/2) + c - floor(c/2) + "
      "d - floor(d/2)",
      strlen("a - floor(a/2) + b - floor(b/2) + c - floor(c/2) + "
             "d - floor(d/2)"));
  ixs_node *slot_overflow = ixs_parse_expr(
      ctx,
      "a - floor(a/2) + b - floor(b/2) + c - floor(c/2) + "
      "d - floor(d/2) + x",
      strlen("a - floor(a/2) + b - floor(b/2) + c - floor(c/2) + "
             "d - floor(d/2) + x"));
  ixs_node *slot_storage_limit =
      ixs_parse_expr(ctx,
                     "-floor(Max(a, 0)/2) - floor(Max(b, 0)/2) - "
                     "floor(Max(c, 0)/2) - floor(Max(d, 0)/2) - "
                     "floor(Max(e, 0)/2) - floor(Max(f, 0)/2) - "
                     "floor(Max(g, 0)/2) - floor(Max(h, 0)/2)",
                     strlen("-floor(Max(a, 0)/2) - floor(Max(b, 0)/2) - "
                            "floor(Max(c, 0)/2) - floor(Max(d, 0)/2) - "
                            "floor(Max(e, 0)/2) - floor(Max(f, 0)/2) - "
                            "floor(Max(g, 0)/2) - floor(Max(h, 0)/2)"));
  /* Canonical floor order makes the first chain take 11 transfers. The added
   * level takes exactly 16, so it reaches the fixed rejection ceiling. */
  ixs_node *step_limit =
      ixs_parse_expr(ctx,
                     "wi + floor(wi/2) + floor(wi/4) + floor(wi/8) + "
                     "floor(wi/16) - 62*floor(wi/32)",
                     strlen("wi + floor(wi/2) + floor(wi/4) + floor(wi/8) + "
                            "floor(wi/16) - 62*floor(wi/32)"));
  ixs_node *step_overflow =
      ixs_parse_expr(ctx,
                     "wi + floor(wi/2) + floor(wi/4) + floor(wi/8) + "
                     "floor(wi/16) + floor(wi/32) - 126*floor(wi/64)",
                     strlen("wi + floor(wi/2) + floor(wi/4) + floor(wi/8) + "
                            "floor(wi/16) + floor(wi/32) - 126*floor(wi/64)"));
  ixs_node *multiply_overflow =
      ixs_parse_expr(ctx, "9223372036854775807*wi - floor(wi/2)",
                     strlen("9223372036854775807*wi - floor(wi/2)"));
  ixs_node *addition_overflow = ixs_parse_expr(
      ctx, "4611686018427387903*wi + 2*floor(wi/2) - floor(wi/4)",
      strlen("4611686018427387903*wi + 2*floor(wi/2) - floor(wi/4)"));

  CHECK(ctx && domain && small_domain && four_symbol_domain &&
        five_symbol_domain && nonintegral && negative_divisor && slot_limit &&
        slot_overflow && slot_storage_limit && step_limit && step_overflow &&
        multiply_overflow && addition_overflow);
  check_radix_certificate_case(ctx, nonintegral, domain, IXS_CHECK_UNKNOWN);
  check_radix_certificate_case(ctx, negative_divisor, domain,
                               IXS_CHECK_UNKNOWN);
  check_radix_certificate_case(ctx, slot_limit, four_symbol_domain,
                               IXS_CHECK_TRUE);
  check_radix_certificate_case(ctx, slot_overflow, five_symbol_domain,
                               IXS_CHECK_UNKNOWN);
  /* Eight absent floor bases fill all 16 stack slots. */
  check_radix_certificate_case(ctx, slot_storage_limit, ixs_true(ctx),
                               IXS_CHECK_UNKNOWN);
  check_radix_certificate_case(ctx, step_limit, domain, IXS_CHECK_TRUE);
  check_radix_certificate_case(ctx, step_overflow, domain, IXS_CHECK_UNKNOWN);
  check_radix_certificate_case(ctx, multiply_overflow, small_domain,
                               IXS_CHECK_UNKNOWN);
  check_radix_certificate_case(ctx, addition_overflow, small_domain,
                               IXS_CHECK_UNKNOWN);

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

static void test_bounds_check_extreme_rhs_parity(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "extreme_rhs_x");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *minimum = ixs_int(ctx, INT64_MIN);
  ixs_node *assumptions[2] = {ixs_cmp(ctx, x, IXS_CMP_GE, zero),
                              ixs_cmp(ctx, x, IXS_CMP_LE, zero)};
  ixs_node *at_minimum = ixs_sub(ctx, minimum, x);
  ixs_node *nonnegative = ixs_cmp(ctx, at_minimum, IXS_CMP_GE, minimum);
  ixs_node *positive = ixs_cmp(ctx, at_minimum, IXS_CMP_GT, minimum);
  ixs_facts *facts = ixs_facts_create(ctx);

  CHECK(ctx && x && zero && minimum && at_minimum && nonnegative && positive &&
        facts);
  CHECK(nonnegative->tag == IXS_CMP && nonnegative->u.binary.rhs == minimum);
  CHECK(positive->tag == IXS_CMP && positive->u.binary.rhs == minimum);
  CHECK(ixs_facts_assume_preds(facts, assumptions, 2));
  ixs_ctx_clear_errors(ctx);
  CHECK(ixs_check(ctx, nonnegative, assumptions, 2) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_facts(facts, nonnegative) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_check_predicate_facts(facts, nonnegative) == IXS_CHECK_TRUE);
  CHECK(ixs_check(ctx, positive, assumptions, 2) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_facts(facts, positive) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_check_predicate_facts(facts, positive) == IXS_CHECK_FALSE);
  CHECK(ixs_ctx_nerrors(ctx) == 0);

  ixs_ctx_destroy(ctx);
}

static void test_bounds_partial_predicate_is_semantic_unknown(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "partial_predicate_x");
  ixs_node *partial = ixs_floor(
      ctx, ixs_div(ctx, ixs_int(ctx, 1), ixs_sub(ctx, x, ixs_int(ctx, 1))));
  ixs_node *query = ixs_cmp(ctx, partial, IXS_CMP_GE, ixs_int(ctx, -1));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_check_result result;

  CHECK(ctx && x && partial && query && facts);
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 31))));
  result = ixs_check_predicate_facts(facts, query);
  CHECK(result == IXS_CHECK_UNKNOWN);

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

static void test_public_range_tightens_integer_lattice(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "integer_lattice_x");
  ixs_node *composite =
      ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), x), ixs_int(ctx, 1));
  ixs_facts *bounded = ixs_facts_create(ctx);
  ixs_facts *aligned = ixs_facts_create(ctx);
  ixs_facts *empty = ixs_facts_create(ctx);
  ixs_range_result input = {0};
  ixs_range_result result;

  input.has_lower = true;
  input.has_upper = true;
  input.lower_p = 1;
  input.lower_q = 2;
  input.upper_p = 19;
  input.upper_q = 2;
  CHECK(ixs_facts_assume_range(bounded, x, &input));
  CHECK(test_ixs_range_facts(bounded, x, &result));
  CHECK(result.has_lower && result.lower_p == 1 && result.lower_q == 1);
  CHECK(result.has_upper && result.upper_p == 9 && result.upper_q == 1);

  input.lower_p = 0;
  input.lower_q = 1;
  input.upper_p = 10;
  input.upper_q = 1;
  CHECK(ixs_facts_assume_range(aligned, composite, &input));
  CHECK(test_ixs_range_facts(aligned, composite, &result));
  CHECK(result.has_lower && result.lower_p == 1 && result.lower_q == 1);
  CHECK(result.has_upper && result.upper_p == 9 && result.upper_q == 1);

  input.lower_p = 1;
  input.lower_q = 4;
  input.upper_p = 3;
  input.upper_q = 4;
  CHECK(ixs_facts_assume_range(empty, x, &input));
  CHECK(!test_ixs_range_facts(empty, x, &result));

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
  ixs_range_result result;

  CHECK(ctx && x && d && remainder && nonnegative && crossing);
  CHECK(ixs_facts_assume_range(nonnegative, x, &input));
  input.lower_p = 4;
  input.upper_p = 1000;
  CHECK(ixs_facts_assume_range(nonnegative, d, &input));
  CHECK(test_ixs_range_facts(nonnegative, remainder, &result));
  CHECK(result.has_lower && result.lower_p == 0 && result.lower_q == 1);
  CHECK(result.has_upper && result.upper_p == 100 && result.upper_q == 1);

  input.lower_p = -100;
  input.upper_p = 100;
  CHECK(ixs_facts_assume_range(crossing, x, &input));
  input.lower_p = 4;
  input.upper_p = 1000;
  CHECK(ixs_facts_assume_range(crossing, d, &input));
  CHECK(test_ixs_range_facts(crossing, remainder, &result));
  CHECK(result.has_lower && result.lower_p == 0 && result.lower_q == 1);
  CHECK(result.has_upper && result.upper_p == 999 && result.upper_q == 1);

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

static void test_public_range_grouped_mod_congruence(void) {
  static const char domain_text[] = "x >= 0 & x <= 255";
  static const char separate_domain_text[] =
      "x >= 0 & x <= 255 & y >= 0 & y <= 255";
  static const char aligned_domain_text[] =
      "x >= 0 & x <= 255 & Mod(x, 8) == 3";
  static const char symbolic_domain_text[] =
      "x >= 0 & x <= 255 & d >= 2 & d <= 64";
  static const char positive_text[] = "Mod(x, 64) - Mod(x, 16)";
  static const char negative_text[] = "Mod(x, 16) - Mod(x, 64)";
  static const char aligned_text[] = "Mod(x, 64) + Mod(x, 16)";
  static const char nested_text[] =
      "Mod(x, 64) - Mod(x, 16) + 16*Mod(Mod(x, 128), 32)";
  static const char separate_text[] = "Mod(x, 64) - Mod(y, 16)";
  static const char one_candidate_text[] = "Mod(x, 64) + x";
  static const char fractional_text[] = "3*Mod(x, 64)/2 - Mod(x, 16)";
  static const char symbolic_text[] = "Mod(x, d) - Mod(x, 16)";
  static const char noninteger_text[] = "Mod(x/2, 64) - Mod(x/2, 16)";
  static const char nontotal_text[] =
      "Mod(floor(x + 1/y), 64) - Mod(floor(x + 1/y), 16)";
  static const char overflow_text[] = "9223372036854775807*Mod(x, 64) + "
                                      "9223372036854775807*Mod(x, 16)";
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *domain = ixs_parse_pred(ctx, domain_text, sizeof(domain_text) - 1u);
  ixs_node *separate_domain = ixs_parse_pred(ctx, separate_domain_text,
                                             sizeof(separate_domain_text) - 1u);
  ixs_node *aligned_domain = ixs_parse_pred(ctx, aligned_domain_text,
                                            sizeof(aligned_domain_text) - 1u);
  ixs_node *symbolic_domain = ixs_parse_pred(ctx, symbolic_domain_text,
                                             sizeof(symbolic_domain_text) - 1u);
  ixs_node *positive =
      ixs_parse_expr(ctx, positive_text, sizeof(positive_text) - 1u);
  ixs_node *negative =
      ixs_parse_expr(ctx, negative_text, sizeof(negative_text) - 1u);
  ixs_node *aligned =
      ixs_parse_expr(ctx, aligned_text, sizeof(aligned_text) - 1u);
  ixs_node *nested = ixs_parse_expr(ctx, nested_text, sizeof(nested_text) - 1u);
  ixs_node *separate =
      ixs_parse_expr(ctx, separate_text, sizeof(separate_text) - 1u);
  ixs_node *one_candidate =
      ixs_parse_expr(ctx, one_candidate_text, sizeof(one_candidate_text) - 1u);
  ixs_node *fractional =
      ixs_parse_expr(ctx, fractional_text, sizeof(fractional_text) - 1u);
  ixs_node *symbolic =
      ixs_parse_expr(ctx, symbolic_text, sizeof(symbolic_text) - 1u);
  ixs_node *noninteger =
      ixs_parse_expr(ctx, noninteger_text, sizeof(noninteger_text) - 1u);
  ixs_node *nontotal =
      ixs_parse_expr(ctx, nontotal_text, sizeof(nontotal_text) - 1u);
  ixs_node *overflow =
      ixs_parse_expr(ctx, overflow_text, sizeof(overflow_text) - 1u);
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *mod64 = ixs_mod(ctx, x, ixs_int(ctx, 64));
  ixs_node *mod16 = ixs_mod(ctx, x, ixs_int(ctx, 16));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *separate_facts = ixs_facts_create(ctx);
  ixs_facts *aligned_facts = ixs_facts_create(ctx);
  ixs_facts *symbolic_facts = ixs_facts_create(ctx);
  ixs_facts *oom_facts = ixs_facts_create(ctx);
  ixs_range_result range;
  ixs_range_result assumption_range;

  CHECK(ctx && domain && separate_domain && aligned_domain && symbolic_domain &&
        positive && negative && aligned && nested && separate &&
        one_candidate && fractional && symbolic && noninteger && nontotal &&
        overflow && x && mod64 && mod16 && facts && separate_facts &&
        aligned_facts && symbolic_facts && oom_facts);
  CHECK(ixs_facts_assume_pred(facts, domain));
  CHECK(ixs_facts_assume_pred(separate_facts, separate_domain));
  CHECK(ixs_facts_assume_pred(aligned_facts, aligned_domain));
  CHECK(ixs_facts_assume_pred(symbolic_facts, symbolic_domain));
  CHECK(ixs_facts_assume_pred(oom_facts, domain));

  CHECK(test_ixs_range_facts(facts, positive, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 48 && range.upper_q == 1);
  CHECK(ixs_range(ctx, positive, &domain, 1, &assumption_range));
  CHECK(assumption_range.has_lower == range.has_lower &&
        assumption_range.lower_p == range.lower_p &&
        assumption_range.lower_q == range.lower_q &&
        assumption_range.has_upper == range.has_upper &&
        assumption_range.upper_p == range.upper_p &&
        assumption_range.upper_q == range.upper_q);

  CHECK(test_ixs_range_facts(facts, negative, &range));
  CHECK(range.has_lower && range.lower_p == -48 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 0 && range.upper_q == 1);
  CHECK(test_ixs_range_facts(facts, aligned, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 78 && range.upper_q == 1);
  CHECK(test_ixs_range_facts(aligned_facts, aligned, &range));
  CHECK(range.has_lower && range.lower_p == 6 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 70 && range.upper_q == 1);
  CHECK(test_ixs_range_facts(facts, nested, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 544 && range.upper_q == 1);

  /* Distinct representatives and ineligible terms remain independent. */
  CHECK(test_ixs_range_facts(separate_facts, separate, &range));
  CHECK(range.has_lower && range.lower_p == -15 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 63 && range.upper_q == 1);
  CHECK(test_ixs_range_facts(facts, one_candidate, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 318 && range.upper_q == 1);
  CHECK(test_ixs_range_facts(facts, fractional, &range));
  CHECK(range.has_lower && range.lower_p == -15 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 189 && range.upper_q == 2);
  CHECK(test_ixs_range_facts(symbolic_facts, symbolic, &range));
  CHECK(range.has_lower && range.lower_p == -15 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 63 && range.upper_q == 1);

  /* Congruence grouping requires a total integer representative. */
  CHECK(!test_ixs_range_facts(facts, noninteger, &range));
  CHECK(!test_ixs_range_facts(facts, nontotal, &range));
  CHECK(!test_ixs_range_facts(
      facts, ixs_add(ctx, ixs_mod(ctx, x, ixs_int(ctx, 0)), mod16), &range));
  CHECK(!test_ixs_range_facts(
      facts, ixs_add(ctx, ixs_mod(ctx, x, ixs_int(ctx, -2)), mod16), &range));

  /* Interval overflow widens rather than manufacturing a finite endpoint. */
  CHECK(test_ixs_range_facts(facts, overflow, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(!range.has_upper);

  /* The query-local group allocation is recoverable and leaves facts usable. */
  CHECK(test_ixs_range_facts(oom_facts, mod64, &range));
  CHECK(test_ixs_range_facts(oom_facts, mod16, &range));
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(!test_ixs_range_facts(oom_facts, positive, &range));
  CHECK(!range.has_lower && !range.has_upper && !oom_facts->bounds.oom);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(test_ixs_range_facts(oom_facts, positive, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 48 && range.upper_q == 1);

  ixs_ctx_destroy(ctx);
}

static void test_public_grouped_add_wave_identity(void) {
  static const char shifted_text[] = "Mod(item + floor(Mod(item,16)/4) - "
                                     "Mod(Mod(item,64),16),64)";
  static const char projected_text[] = "16*floor(Mod(item,64)/16) + "
                                       "floor(Mod(Mod(item,64),16)/4)";
  static const char expression_text[] =
      "16384*floor(item/64 + floor(Mod(item,16)/4)/64 - "
      "Mod(Mod(item,64),16)/64) - 16384*floor(item/64) - "
      "2048*floor(Mod(item,64)/16) - "
      "128*floor(Mod(Mod(item,64),16)/4) + 16*Mod(item,4) + "
      "128*Mod(item + floor(Mod(item,16)/4) - "
      "Mod(Mod(item,64),16),64) - 16*Mod(Mod(item,64),4)";
  static const char invalid_text[] =
      "16384*floor(item/64 + floor(Mod(item,16)/4)/64 - "
      "Mod(Mod(item,64),16)/64) - 16384*floor(item/64) - "
      "2048*floor(Mod(item,64)/16) - "
      "128*floor(Mod(Mod(item,64),16)/4) + 16*Mod(item,4) + "
      "127*Mod(item + floor(Mod(item,16)/4) - "
      "Mod(Mod(item,64),16),64) - 16*Mod(Mod(item,64),4)";
  static const char domain_text[] = "item >= 0 & item <= 255";
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *alloc_ctx = ixs_ctx_create();
  ixs_node *shifted =
      ixs_parse_expr(ctx, shifted_text, sizeof(shifted_text) - 1u);
  ixs_node *projected =
      ixs_parse_expr(ctx, projected_text, sizeof(projected_text) - 1u);
  ixs_node *wrong_projected = ixs_add(ctx, projected, ixs_int(ctx, 1));
  ixs_node *rational = ixs_rat(ctx, 3, 2);
  ixs_node *scaled_shifted = ixs_mul(ctx, rational, shifted);
  ixs_node *scaled_projected = ixs_mul(ctx, rational, projected);
  ixs_node *wrong_scaled_projected =
      ixs_add(ctx, scaled_projected, ixs_rat(ctx, 1, 2));
  ixs_node *extreme_scaled = ixs_mul(ctx, ixs_int(ctx, INT64_MAX), shifted);
  ixs_node *wrong_extreme_scaled = ixs_add(
      ctx, ixs_mul(ctx, ixs_int(ctx, INT64_MAX), projected), ixs_int(ctx, 1));
  ixs_node *expression =
      ixs_parse_expr(ctx, expression_text, sizeof(expression_text) - 1u);
  ixs_node *invalid =
      ixs_parse_expr(ctx, invalid_text, sizeof(invalid_text) - 1u);
  ixs_node *domain = ixs_parse_pred(ctx, domain_text, sizeof(domain_text) - 1u);
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *item = ixs_sym(ctx, "item");
  ixs_node *half = ixs_div(ctx, item, ixs_int(ctx, 2));
  ixs_node *noninteger = ixs_mod(ctx, half, ixs_int(ctx, 64));
  ixs_node *rounded_half = ixs_floor(ctx, half);
  ixs_node *wrap =
      ixs_mod(ctx, ixs_add(ctx, item, ixs_int(ctx, 1)), ixs_int(ctx, 64));
  ixs_node *unwrapped =
      ixs_add(ctx, ixs_mod(ctx, item, ixs_int(ctx, 64)), ixs_int(ctx, 1));
  ixs_node *partial =
      ixs_mod(ctx,
              ixs_floor(ctx, ixs_add(ctx, item,
                                     ixs_div(ctx, ixs_int(ctx, 1),
                                             ixs_sym(ctx, "wave_partial_d")))),
              ixs_int(ctx, 64));
  ixs_node *shifted_eq = ixs_cmp(ctx, shifted, IXS_CMP_EQ, projected);
  ixs_node *expression_eq = ixs_cmp(ctx, expression, IXS_CMP_EQ, zero);
  ixs_node *alloc_expression =
      ixs_parse_expr(alloc_ctx, expression_text, sizeof(expression_text) - 1u);
  ixs_node *alloc_domain =
      ixs_parse_pred(alloc_ctx, domain_text, sizeof(domain_text) - 1u);
  ixs_node *alloc_zero = ixs_int(alloc_ctx, 0);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *oom_facts = ixs_facts_create(ctx);
  ixs_facts *alloc_facts = ixs_facts_create(alloc_ctx);

  CHECK(ctx && alloc_ctx && shifted && projected && wrong_projected &&
        rational && scaled_shifted && scaled_projected &&
        wrong_scaled_projected && extreme_scaled && wrong_extreme_scaled &&
        expression && invalid && domain && zero && item && half && noninteger &&
        rounded_half && wrap && unwrapped && partial && shifted_eq &&
        expression_eq && alloc_expression && alloc_domain && alloc_zero &&
        facts && oom_facts && alloc_facts);
  CHECK(ixs_facts_assume_pred(facts, domain));
  CHECK(ixs_facts_assume_pred(oom_facts, domain));
  CHECK(ixs_facts_assume_pred(alloc_facts, alloc_domain));

  CHECK(ixs_bounds_equivalence_partition_limit_probe(
            facts, shifted, projected) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_facts(facts, shifted, projected) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(facts, shifted_eq) == IXS_CHECK_TRUE);
  CHECK(ixs_check(ctx, shifted_eq, &domain, 1) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, shifted, wrong_projected) !=
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, scaled_shifted, scaled_projected) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, scaled_shifted,
                                  wrong_scaled_projected) != IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, extreme_scaled,
                                  wrong_extreme_scaled) != IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(facts, expression_eq) == IXS_CHECK_TRUE);
  CHECK(ixs_check(ctx, expression_eq, &domain, 1) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, expression, zero) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(facts, ixs_cmp(ctx, invalid, IXS_CMP_EQ, zero)) !=
        IXS_CHECK_TRUE);

  /* Composition must not erase wrapping, partiality, or rational values. */
  CHECK(test_ixs_equivalent_facts(facts, wrap, unwrapped) != IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, noninteger, rounded_half) !=
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, partial, zero) != IXS_CHECK_TRUE);

  /* Query-local allocation failure remains UNKNOWN and is retryable. */
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(test_ixs_equivalent_facts(oom_facts, shifted, projected) ==
        IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(test_ixs_equivalent_facts(oom_facts, shifted, projected) ==
        IXS_CHECK_TRUE);

  ixs_arena_set_fail_after(&alloc_ctx->arena, 0);
  CHECK(test_ixs_equivalent_facts(alloc_facts, alloc_expression, alloc_zero) ==
        IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(&alloc_ctx->arena, IXS_ARENA_FAILURE_DISABLED);
  CHECK(test_ixs_equivalent_facts(alloc_facts, alloc_expression, alloc_zero) ==
        IXS_CHECK_TRUE);

  ixs_ctx_destroy(alloc_ctx);
  ixs_ctx_destroy(ctx);
}

static ixs_node *make_radix_reconstruction(ixs_ctx *ctx, ixs_node *numerator,
                                           ixs_node *remainder_dividend,
                                           int64_t radix) {
  ixs_node *radix_node = ixs_int(ctx, radix);
  ixs_node *quotient = ixs_floor(ctx, ixs_div(ctx, numerator, radix_node));
  ixs_node *high = ixs_mul(ctx, radix_node, quotient);
  ixs_node *low = ixs_mod(ctx, remainder_dividend, radix_node);
  return ixs_add(ctx, high, low);
}

static void test_public_congruent_radix_reconstruction(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *oom_ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "radix_reconstruction_x");
  ixs_node *y = ixs_sym(ctx, "radix_reconstruction_y");
  ixs_node *alias = ixs_sym(ctx, "radix_reconstruction_alias");
  ixs_node *dynamic = ixs_sym(ctx, "radix_reconstruction_dynamic");
  ixs_node *partial_divisor =
      ixs_sym(ctx, "radix_reconstruction_partial_divisor");
  ixs_node *eight = ixs_int(ctx, 8);
  ixs_node *x_residue =
      ixs_cmp(ctx, ixs_mod(ctx, x, eight), IXS_CMP_EQ, ixs_int(ctx, 3));
  ixs_node *y_residue =
      ixs_cmp(ctx, ixs_mod(ctx, y, eight), IXS_CMP_EQ, ixs_int(ctx, 3));
  ixs_node *alias_relation = ixs_cmp(ctx, alias, IXS_CMP_EQ, x);
  ixs_node *dynamic_positive =
      ixs_cmp(ctx, dynamic, IXS_CMP_GE, ixs_int(ctx, 2));
  ixs_node *reconstructed = make_radix_reconstruction(ctx, x, y, 8);
  ixs_node *equality = ixs_cmp(ctx, reconstructed, IXS_CMP_EQ, x);
  ixs_node *assumptions[4] = {x_residue, y_residue, alias_relation,
                              dynamic_positive};
  ixs_node *wrong_low =
      make_radix_reconstruction(ctx, x, ixs_add(ctx, y, ixs_int(ctx, 1)), 8);
  ixs_node *unequal_denominator =
      ixs_add(ctx, ixs_mul(ctx, eight, ixs_floor(ctx, ixs_div(ctx, x, eight))),
              ixs_mod(ctx, y, ixs_int(ctx, 5)));
  ixs_node *symbolic_denominator =
      ixs_add(ctx, ixs_mul(ctx, eight, ixs_floor(ctx, ixs_div(ctx, x, eight))),
              ixs_mod(ctx, y, dynamic));
  ixs_node *half = ixs_div(ctx, x, ixs_int(ctx, 2));
  ixs_node *noninteger_numerator = make_radix_reconstruction(ctx, half, y, 8);
  ixs_node *noninteger_remainder =
      make_radix_reconstruction(ctx, x, ixs_div(ctx, y, ixs_int(ctx, 2)), 8);
  ixs_node *partial = ixs_floor(ctx, ixs_div(ctx, x, partial_divisor));
  ixs_node *partial_reconstruction =
      make_radix_reconstruction(ctx, partial, y, 8);
  ixs_node *radix_one = make_radix_reconstruction(ctx, half, y, 1);
  ixs_node *malformed =
      ixs_add(ctx, ixs_mul(ctx, eight, ixs_ceil(ctx, ixs_div(ctx, x, eight))),
              ixs_mod(ctx, y, eight));
  ixs_node *extra = ixs_add(ctx, reconstructed, ixs_int(ctx, 1));
  ixs_node *wrong_coefficient = ixs_add(
      ctx,
      ixs_mul(ctx, ixs_int(ctx, 7), ixs_floor(ctx, ixs_div(ctx, x, eight))),
      ixs_mod(ctx, y, eight));
  ixs_node *wrong_shape =
      ixs_add(ctx, ixs_mul(ctx, eight, x), ixs_mod(ctx, y, eight));
  ixs_node *overflow_numerator = ixs_sub(ctx, x, ixs_int(ctx, 2));
  ixs_node *overflow_remainder = ixs_add(ctx, x, ixs_int(ctx, INT64_MAX));
  ixs_node *overflow =
      make_radix_reconstruction(ctx, overflow_numerator, overflow_remainder, 2);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *mismatch = ixs_facts_create(ctx);
  ixs_facts *cycle = ixs_facts_create(ctx);
  ixs_node *cycle_a = ixs_sym(ctx, "radix_reconstruction_cycle_a");
  ixs_node *cycle_b = ixs_sym(ctx, "radix_reconstruction_cycle_b");
  ixs_node *ox = ixs_sym(oom_ctx, "radix_reconstruction_oom_x");
  ixs_node *oy = ixs_sym(oom_ctx, "radix_reconstruction_oom_y");
  ixs_node *oom_reconstructed = make_radix_reconstruction(oom_ctx, ox, oy, 8);
  ixs_facts *oom_facts = ixs_facts_create(oom_ctx);
  ixs_node *slot = ixs_sym(ctx, "bounded_radix_slot");
  ixs_node *slot_half = ixs_floor(ctx, ixs_div(ctx, slot, ixs_int(ctx, 2)));
  ixs_node *t = ixs_mod(ctx,
                        ixs_add(ctx, ixs_mod(ctx, slot, ixs_int(ctx, 2)),
                                ixs_mod(ctx, slot_half, ixs_int(ctx, 2))),
                        ixs_int(ctx, 3));
  ixs_node *t_half = ixs_floor(ctx, ixs_div(ctx, t, ixs_int(ctx, 2)));
  ixs_node *high = ixs_mod(ctx, t_half, ixs_int(ctx, 2));
  ixs_node *low = ixs_mod(ctx, t, ixs_int(ctx, 2));
  ixs_node *witness_reconstructed =
      ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), high), low);
  ixs_node *wrapped = ixs_mod(ctx, witness_reconstructed, ixs_int(ctx, 3));
  ixs_node *bad_low =
      ixs_mod(ctx, ixs_add(ctx, t, ixs_int(ctx, 1)), ixs_int(ctx, 2));
  ixs_node *bad_witness =
      ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), t_half), bad_low);
  ixs_node *witness_alias = ixs_sym(ctx, "bounded_radix_alias");
  ixs_facts *witness_facts = ixs_facts_create(ctx);

  CHECK(ctx && oom_ctx && x && y && alias && dynamic && partial_divisor &&
        eight && x_residue && y_residue && alias_relation && dynamic_positive &&
        reconstructed && equality && wrong_low && unequal_denominator &&
        symbolic_denominator && half && noninteger_numerator &&
        noninteger_remainder && partial && partial_reconstruction &&
        radix_one && malformed && extra && wrong_coefficient && wrong_shape &&
        overflow_numerator && overflow_remainder && overflow && facts &&
        mismatch && cycle && cycle_a && cycle_b && ox && oy &&
        oom_reconstructed && oom_facts && slot && slot_half && t && t_half &&
        high && low && witness_reconstructed && wrapped && bad_low &&
        bad_witness && witness_alias && witness_facts);
  CHECK(ixs_facts_assume_preds(facts, assumptions, 4));
  CHECK(test_ixs_equivalent_facts(facts, reconstructed, x) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(facts, equality) == IXS_CHECK_TRUE);
  CHECK(ixs_check(ctx, equality, assumptions, 4) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, x, alias) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(witness_facts,
                              ixs_cmp(ctx, slot, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(witness_facts,
                              ixs_cmp(ctx, slot, IXS_CMP_LE, ixs_int(ctx, 3))));
  CHECK(ixs_facts_assume_pred(witness_facts,
                              ixs_cmp(ctx, witness_alias, IXS_CMP_EQ, t)));
  CHECK(test_ixs_equivalent_facts(witness_facts, t, witness_alias) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(witness_facts, high, t_half) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(witness_facts, witness_reconstructed, t) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(witness_facts, witness_reconstructed,
                                  witness_alias) == IXS_CHECK_TRUE);
  CHECK(ixs_bounds_equivalence_subproof_limit_probe(
            witness_facts, witness_reconstructed, witness_alias) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_facts(witness_facts, ixs_cmp(ctx, wrapped, IXS_CMP_EQ,
                                                    t)) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(witness_facts, bad_witness, t) !=
        IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(mismatch, ixs_cmp(ctx, ixs_mod(ctx, x, eight),
                                                IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(mismatch, ixs_cmp(ctx, ixs_mod(ctx, y, eight),
                                                IXS_CMP_EQ, ixs_int(ctx, 1))));
  CHECK(test_ixs_equivalent_facts(mismatch, reconstructed, x) !=
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, wrong_low, x) != IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, unequal_denominator, x) !=
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, symbolic_denominator, x) !=
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, noninteger_numerator, half) !=
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, noninteger_remainder, x) !=
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, partial_reconstruction, partial) !=
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, radix_one, half) != IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, malformed, x) != IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, extra, x) != IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, wrong_coefficient, x) !=
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, wrong_shape, x) != IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, overflow, overflow_numerator) !=
        IXS_CHECK_TRUE);

  CHECK(
      ixs_facts_assume_pred(cycle, ixs_cmp(ctx, ixs_sub(ctx, cycle_a, cycle_b),
                                           IXS_CMP_LE, ixs_int(ctx, -1))));
  CHECK(
      ixs_facts_assume_pred(cycle, ixs_cmp(ctx, ixs_sub(ctx, cycle_b, cycle_a),
                                           IXS_CMP_LE, ixs_int(ctx, 0))));
  CHECK(cycle->bounds.contradiction);
  CHECK(test_ixs_equivalent_facts(cycle, reconstructed, x) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(
      oom_facts, ixs_cmp(oom_ctx, ixs_mod(oom_ctx, ox, ixs_int(oom_ctx, 8)),
                         IXS_CMP_EQ, ixs_int(oom_ctx, 3))));
  CHECK(ixs_facts_assume_pred(
      oom_facts, ixs_cmp(oom_ctx, ixs_mod(oom_ctx, oy, ixs_int(oom_ctx, 8)),
                         IXS_CMP_EQ, ixs_int(oom_ctx, 3))));
  ixs_arena_set_fail_after(&oom_ctx->arena, 0);
  CHECK(test_ixs_equivalent_facts(oom_facts, oom_reconstructed, ox) ==
        IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(&oom_ctx->arena, IXS_ARENA_FAILURE_DISABLED);
  CHECK(test_ixs_equivalent_facts(oom_facts, oom_reconstructed, ox) ==
        IXS_CHECK_TRUE);
  ixs_arena_set_fail_after(ixs_test_scratch(oom_ctx), 0);
  CHECK(test_ixs_equivalent_facts(oom_facts, oom_reconstructed, ox) ==
        IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(ixs_test_scratch(oom_ctx),
                           IXS_ARENA_FAILURE_DISABLED);
  CHECK(test_ixs_equivalent_facts(oom_facts, oom_reconstructed, ox) ==
        IXS_CHECK_TRUE);

  ixs_ctx_destroy(oom_ctx);
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

static void check_public_exact_range(ixs_facts *facts, ixs_node *expr,
                                     int64_t expected) {
  ixs_range_result range;
  CHECK(test_ixs_range_facts(facts, expr, &range));
  CHECK(range.has_lower && range.lower_p == expected && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == expected && range.upper_q == 1);
}

static void check_public_range(ixs_facts *facts, ixs_node *expr, int64_t lower,
                               int64_t upper) {
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
    size_t errors = ixs_ctx_nerrors(ctx);
    delta = 99;
    CHECK(!ixs_constant_difference_facts(chain, uncached_appended, nodes[0],
                                         &delta));
    CHECK(delta == 0);
    CHECK(ixs_ctx_nerrors(ctx) == errors + 1);
    CHECK(strstr(ixs_ctx_error(ctx, errors), "out of memory") != NULL);
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
  check_public_exact_range(facts, lhs, 7);

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
  check_public_range(wrap32, s, 0, INT64_C(4294967295));

  CHECK(ixs_facts_assume_preds(forward_facts, forward, 2));
  CHECK(ixs_facts_assume_preds(reverse_facts, reverse, 2));
  check_public_range(forward_facts, s, 0, 7);
  check_public_range(reverse_facts, s, 0, 7);

  CHECK(ixs_facts_assume_pred(equality_first, dynamic));
  CHECK(!test_ixs_range_facts(equality_first, s, &range));
  CHECK(ixs_facts_assume_pred(equality_first, d_is_eight));
  check_public_range(equality_first, s, 0, 7);
  CHECK(ixs_facts_assume_pred(divisor_first, d_is_eight));
  CHECK(ixs_facts_assume_pred(divisor_first, dynamic));
  check_public_range(divisor_first, s, 0, 7);

  CHECK(ixs_facts_assume_pred(arbitrary,
                              ixs_cmp(ctx, floored, IXS_CMP_EQ, floored_wrap)));
  check_public_range(arbitrary, floored, 0, 15);

  CHECK(ixs_facts_assume_pred(substitution_source,
                              ixs_cmp(ctx, floored, IXS_CMP_EQ, floored_wrap)));
  CHECK(ixs_facts_substitute(substitution_result, substitution_source, x, z));
  check_public_range(substitution_result,
                     ixs_floor(ctx, ixs_div(ctx, z, ixs_int(ctx, 4))), 0, 15);

  CHECK(ixs_facts_assume_preds(transitive_facts, transitive, 2));
  CHECK(
      ixs_facts_assume_preds(reverse_transitive_facts, reverse_transitive, 2));
  check_public_range(transitive_facts, first, 0, 15);
  check_public_range(reverse_transitive_facts, first, 0, 15);

  CHECK(ixs_facts_assume_pred(partial_facts, partial_predicates[0]));
  CHECK(ixs_facts_assume_pred(partial_facts, partial_predicates[1]));
  CHECK(test_ixs_check_defined_facts(partial_facts, partial) ==
        IXS_CHECK_UNKNOWN);
  CHECK(!test_ixs_range_facts(partial_facts, s, &range));
  CHECK(ixs_facts_assume_pred(partial_facts, d_nonzero));
  CHECK(test_ixs_check_defined_facts(partial_facts, partial) == IXS_CHECK_TRUE);
  check_public_range(partial_facts, s, 0, 7);

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
  size_t errors;

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
  errors = ixs_ctx_nerrors(ctx);
  CHECK(!test_ixs_constant_difference_facts(negative, scaled_overflow_lhs,
                                            scaled_overflow_rhs, &delta));
  CHECK(ixs_ctx_nerrors(ctx) == errors);
  CHECK(
      test_ixs_constant_difference_facts(negative, extreme_low, raw0, &delta));
  CHECK(delta == INT64_MIN + 1);
  errors = ixs_ctx_nerrors(ctx);
  CHECK(!test_ixs_constant_difference_facts(negative, overflow_high,
                                            overflow_rhs, &delta));
  CHECK(ixs_ctx_nerrors(ctx) == errors);

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
  check_public_exact_range(affine_range, affine, 11);
  check_public_exact_range(affine_range, ixs_sub(ctx, affine, ixs_int(ctx, 11)),
                           0);
  CHECK(test_ixs_equivalent_facts(affine_range, affine, ixs_int(ctx, 11)) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_constant_difference_facts(affine_range, affine,
                                           ixs_int(ctx, 11), &delta));
  CHECK(delta == 0);

  CHECK(ixs_facts_assume_pred(
      direct, ixs_cmp(ctx, y, IXS_CMP_EQ, ixs_add(ctx, x, ixs_int(ctx, 4)))));
  check_public_exact_range(
      direct, ixs_sub(ctx, y, ixs_add(ctx, x, ixs_int(ctx, 4))), 0);
  CHECK(test_ixs_equivalent_facts(
            direct, y, ixs_add(ctx, x, ixs_int(ctx, 4))) == IXS_CHECK_TRUE);
  CHECK(test_ixs_constant_difference_facts(direct, y, x, &delta));
  CHECK(delta == 4);

  CHECK(assume_unit_difference_upper(ctx, complementary, x, y, IXS_CMP_LE, 4));
  CHECK(assume_unit_difference_upper(ctx, complementary, y, x, IXS_CMP_LE, -4));
  check_public_exact_range(complementary, ixs_sub(ctx, x, y), 4);
  CHECK(test_ixs_equivalent_facts(complementary, x,
                                  ixs_add(ctx, y, ixs_int(ctx, 4))) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_constant_difference_facts(complementary, x, y, &delta));
  CHECK(delta == 4);

  CHECK(ixs_facts_assume_pred(
      nonaffine,
      ixs_cmp(ctx, mod_x, IXS_CMP_EQ, ixs_add(ctx, mod_y, ixs_int(ctx, 4)))));
  check_public_exact_range(nonaffine, ixs_sub(ctx, mod_x, mod_y), 4);
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
  check_public_exact_range(forward, ixs_sub(ctx, x, z), 0);
  CHECK(test_ixs_equivalent_facts(forward, x, z) == IXS_CHECK_TRUE);
  CHECK(test_ixs_constant_difference_facts(forward, x, z, &delta));
  CHECK(delta == 0);
  CHECK(test_ixs_equivalent_facts(
            forward, ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 9)),
            ixs_cmp(ctx, z, IXS_CMP_LT, ixs_int(ctx, 9))) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(reverse, ixs_cmp(ctx, y, IXS_CMP_EQ, z)));
  CHECK(ixs_facts_assume_pred(reverse, ixs_cmp(ctx, x, IXS_CMP_EQ, y)));
  check_public_exact_range(reverse, ixs_sub(ctx, x, z), 0);
  CHECK(test_ixs_equivalent_facts(reverse, x, z) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(
      offset, ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_add(ctx, y, ixs_int(ctx, 3)))));
  CHECK(ixs_facts_assume_pred(
      offset, ixs_cmp(ctx, y, IXS_CMP_EQ, ixs_add(ctx, z, ixs_int(ctx, 4)))));
  check_public_exact_range(offset, ixs_sub(ctx, x, z), 7);
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
  check_public_exact_range(
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
  check_public_exact_range(facts, ixs_sub(ctx, x, z), 0);
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
  check_public_exact_range(facts, ixs_sub(ctx, nodes[0], nodes[LINKS]), LINKS);
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
    size_t errors = ixs_ctx_nerrors(ctx);
    result.has_lower = true;
    result.has_upper = true;
    CHECK(!ixs_range_facts(oom, shifted, &result));
    CHECK(!result.has_lower && !result.has_upper);
    CHECK(ixs_ctx_nerrors(ctx) == errors + 1);
    CHECK(strstr(ixs_ctx_error(ctx, errors), "out of memory") != NULL);
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
  CHECK(range.has_upper && range.upper_p == 2147483616 && range.upper_q == 1);
  CHECK(ixs_facts_assume_range(right_facts, b, &input));
  CHECK(test_ixs_range_facts(right_facts, a, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 2147483616 && range.upper_q == 1);
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

static void test_public_facts_assume_batch_closure_cache_keys(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "batch_cache_x");
  ixs_node *y = ixs_sym(ctx, "batch_cache_y");
  ixs_node *z = ixs_sym(ctx, "batch_cache_z");
  ixs_node *w = ixs_sym(ctx, "batch_cache_w");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *predicates[3] = {ixs_cmp(ctx, ixs_add(ctx, x, y), IXS_CMP_GE, zero),
                             ixs_cmp(ctx, ixs_add(ctx, y, z), IXS_CMP_EQ, zero),
                             ixs_cmp(ctx, z, IXS_CMP_EQ, zero)};
  ixs_node *reordered[3] = {predicates[2], predicates[1], predicates[0]};
  ixs_node *nearby[3] = {predicates[0], predicates[1],
                         ixs_cmp(ctx, z, IXS_CMP_EQ, one)};
  ixs_node *query = ixs_cmp(ctx, x, IXS_CMP_GE, zero);
  ixs_facts *cold = ixs_facts_create(ctx);
  ixs_facts *replay = ixs_facts_create(ctx);
  ixs_facts *ordered = ixs_facts_create(ctx);
  ixs_facts *changed = ixs_facts_create(ctx);
  ixs_facts *nonempty = ixs_facts_create(ctx);
  ixs_facts *rewarm;
  ixs_facts *after_reset;
  ixs_range_result w_range = {.has_lower = true,
                              .has_upper = true,
                              .lower_p = 0,
                              .lower_q = 1,
                              .upper_p = 4,
                              .upper_q = 1};
  ixs_facts_closure_cache_stats_result stats;
  ixs_facts_closure_cache_stats_result before;

  CHECK(ixs_facts_assume_preds(cold, predicates, 3));
  CHECK(test_ixs_check_facts(cold, query) == IXS_CHECK_TRUE);
  ixs_facts_closure_cache_stats(ctx, &stats);
  CHECK(stats.lookups == 1 && stats.hits == 0 && stats.stores == 1);

  CHECK(ixs_facts_assume_preds(replay, predicates, 3));
  CHECK(test_ixs_check_facts(replay, query) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(replay, predicates[0]) == IXS_CHECK_TRUE);
  ixs_facts_closure_cache_stats(ctx, &stats);
  CHECK(stats.lookups == 2 && stats.hits == 1 && stats.stores == 1);

  CHECK(ixs_facts_assume_preds(ordered, reordered, 3));
  CHECK(test_ixs_check_facts(ordered, query) == IXS_CHECK_TRUE);
  ixs_facts_closure_cache_stats(ctx, &stats);
  CHECK(stats.lookups == 3 && stats.hits == 1 && stats.stores == 2);

  CHECK(ixs_facts_assume_preds(changed, nearby, 3));
  CHECK(test_ixs_check_facts(changed, query) == IXS_CHECK_TRUE);
  ixs_facts_closure_cache_stats(ctx, &stats);
  CHECK(stats.lookups == 4 && stats.hits == 1 && stats.stores == 3);

  CHECK(ixs_facts_assume_range(nonempty, w, &w_range));
  ixs_facts_closure_cache_stats(ctx, &before);
  CHECK(ixs_facts_assume_preds(nonempty, predicates, 3));
  CHECK(test_ixs_check_facts(nonempty, query) == IXS_CHECK_TRUE);
  ixs_facts_closure_cache_stats(ctx, &stats);
  CHECK(stats.lookups == before.lookups && stats.hits == before.hits &&
        stats.stores == before.stores);

  rewarm = ixs_facts_create(ctx);
  CHECK(ixs_facts_assume_preds(rewarm, predicates, 3));
  ixs_facts_closure_cache_stats(ctx, &before);
  (ixs_session_reset)(IXS_TEST_SESSION(ctx));
  after_reset = ixs_facts_create(ctx);
  CHECK(ixs_facts_assume_preds(after_reset, predicates, 3));
  CHECK(test_ixs_check_facts(after_reset, query) == IXS_CHECK_TRUE);
  ixs_facts_closure_cache_stats(ctx, &stats);
  CHECK(stats.lookups == before.lookups + 1u &&
        stats.hits == before.hits + 1u && stats.stores == before.stores);

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_assume_batch_closure_cache_duplicates(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "batch_cache_duplicate_x");
  ixs_node *y = ixs_sym(ctx, "batch_cache_duplicate_y");
  ixs_node *z = ixs_sym(ctx, "batch_cache_duplicate_z");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *first = ixs_cmp(ctx, ixs_add(ctx, x, y), IXS_CMP_GE, zero);
  ixs_node *second = ixs_cmp(ctx, ixs_add(ctx, y, z), IXS_CMP_EQ, zero);
  ixs_node *third = ixs_cmp(ctx, z, IXS_CMP_EQ, zero);
  ixs_node *predicates[5] = {first, second, second, third, first};
  ixs_node *query = ixs_cmp(ctx, x, IXS_CMP_GE, zero);
  ixs_facts *cold = ixs_facts_create(ctx);
  ixs_facts *warm = ixs_facts_create(ctx);
  ixs_range_result cold_range;
  ixs_range_result warm_range;
  ixs_facts_closure_cache_stats_result stats;

  CHECK(ixs_facts_assume_preds(cold, predicates, 5));
  CHECK(ixs_facts_assume_preds(warm, predicates, 5));
  CHECK(test_ixs_check_facts(cold, query) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(warm, query) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(warm, predicates[2]) == IXS_CHECK_TRUE);
  CHECK(test_ixs_range_facts(cold, x, &cold_range));
  CHECK(test_ixs_range_facts(warm, x, &warm_range));
  CHECK(cold_range.has_lower == warm_range.has_lower);
  CHECK(cold_range.has_upper == warm_range.has_upper);
  CHECK(cold_range.lower_p == warm_range.lower_p);
  CHECK(cold_range.lower_q == warm_range.lower_q);
  CHECK(cold_range.upper_p == warm_range.upper_p);
  CHECK(cold_range.upper_q == warm_range.upper_q);
  ixs_facts_closure_cache_stats(ctx, &stats);
  CHECK(stats.lookups == 2 && stats.hits == 1 && stats.stores == 1);

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_assume_batch_closure_cache_collisions(void) {
  enum { BATCH_COUNT = 33 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *predicates[BATCH_COUNT][3];
  ixs_node *queries[BATCH_COUNT];
  ixs_facts_closure_cache_stats_result stats;
  size_t cold_stores;
  size_t i;

  for (i = 0; i < BATCH_COUNT; i++) {
    char x_name[48];
    char y_name[48];
    char z_name[48];
    ixs_node *x;
    ixs_node *y;
    ixs_node *z;
    ixs_facts *facts;
    (void)snprintf(x_name, sizeof(x_name), "batch_collision_x_%lu",
                   (unsigned long)i);
    (void)snprintf(y_name, sizeof(y_name), "batch_collision_y_%lu",
                   (unsigned long)i);
    (void)snprintf(z_name, sizeof(z_name), "batch_collision_z_%lu",
                   (unsigned long)i);
    x = ixs_sym(ctx, x_name);
    y = ixs_sym(ctx, y_name);
    z = ixs_sym(ctx, z_name);
    predicates[i][0] = ixs_cmp(ctx, ixs_add(ctx, x, y), IXS_CMP_GE, zero);
    predicates[i][1] = ixs_cmp(ctx, ixs_add(ctx, y, z), IXS_CMP_EQ, zero);
    predicates[i][2] = ixs_cmp(ctx, z, IXS_CMP_EQ, zero);
    queries[i] = ixs_cmp(ctx, x, IXS_CMP_GE, zero);
    facts = ixs_facts_create(ctx);
    CHECK(ixs_facts_assume_preds(facts, predicates[i], 3));
    CHECK(test_ixs_check_facts(facts, queries[i]) == IXS_CHECK_TRUE);
  }
  ixs_facts_closure_cache_stats(ctx, &stats);
  CHECK(stats.lookups == BATCH_COUNT && stats.hits == 0 &&
        stats.stores == BATCH_COUNT);
  CHECK(stats.entries <= 32u);
  CHECK(stats.retained_bytes <= stats.retained_limit);
  cold_stores = stats.stores;

  for (i = 0; i < BATCH_COUNT; i++) {
    ixs_facts *facts = ixs_facts_create(ctx);
    CHECK(ixs_facts_assume_preds(facts, predicates[i], 3));
    CHECK(test_ixs_check_facts(facts, queries[i]) == IXS_CHECK_TRUE);
  }
  ixs_facts_closure_cache_stats(ctx, &stats);
  CHECK(stats.lookups == 2u * BATCH_COUNT);
  CHECK(stats.stores > cold_stores);
  CHECK(stats.hits < BATCH_COUNT);
  CHECK(stats.retained_bytes <= stats.retained_limit);

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_assume_large_batch_closure_cache(void) {
  enum { PREDICATE_COUNT = 160 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *predicates[PREDICATE_COUNT];
  ixs_facts *cold = ixs_facts_create(ctx);
  ixs_facts *replay = ixs_facts_create(ctx);
  ixs_facts_closure_cache_stats_result stats;
  size_t i;

  for (i = 0; i < PREDICATE_COUNT; i++) {
    char name[48];
    ixs_node *symbol;
    (void)snprintf(name, sizeof(name), "large_batch_cache_%lu",
                   (unsigned long)i);
    symbol = ixs_sym(ctx, name);
    predicates[i] = ixs_cmp(ctx, symbol, IXS_CMP_GE, zero);
  }

  CHECK(ixs_facts_assume_preds(cold, predicates, PREDICATE_COUNT));
  CHECK(test_ixs_check_facts(cold, predicates[0]) == IXS_CHECK_TRUE);
  ixs_facts_closure_cache_stats(ctx, &stats);
  CHECK(stats.slot_node_capacity >= 2u * PREDICATE_COUNT);
  CHECK(stats.lookups == 1 && stats.hits == 0 && stats.stores == 1 &&
        stats.bypasses == 0);

  CHECK(ixs_facts_assume_preds(replay, predicates, PREDICATE_COUNT));
  CHECK(test_ixs_check_facts(replay, predicates[PREDICATE_COUNT - 1u]) ==
        IXS_CHECK_TRUE);
  ixs_facts_closure_cache_stats(ctx, &stats);
  CHECK(stats.lookups == 2 && stats.hits == 1 && stats.stores == 1 &&
        stats.bypasses == 0);

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_closure_cache_allocation_is_optional(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *predicates[1] = {ixs_true(ctx)};
  ixs_facts *uncached = ixs_facts_create(ctx);
  ixs_facts *cold = ixs_facts_create(ctx);
  ixs_facts *warm = ixs_facts_create(ctx);
  ixs_facts_closure_cache_stats_result stats;

  /* The root allocation succeeds; the first slot allocation fails. */
  ixs_arena_set_fail_after(&ctx->arena, 1);
  CHECK(ixs_facts_assume_preds(uncached, predicates, 1));
  ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
  CHECK(uncached->usable);
  ixs_facts_closure_cache_stats(ctx, &stats);
  CHECK(stats.lookups == 1 && stats.stores == 0 && stats.entries == 0);

  CHECK(ixs_facts_assume_preds(cold, predicates, 1));
  CHECK(ixs_facts_assume_preds(warm, predicates, 1));
  ixs_facts_closure_cache_stats(ctx, &stats);
  CHECK(stats.lookups == 3 && stats.hits == 1 && stats.stores == 1 &&
        stats.entries == 1);

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_closure_cache_replay_failure_is_atomic(void) {
  enum { MAX_FAIL_BUDGET = 64 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "cache_replay_oom_x");
  ixs_node *predicate = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_facts *cold = ixs_facts_create(ctx);
  ixs_facts_closure_cache_stats_result before_stats;
  ixs_facts_closure_cache_stats_result after_stats;
  bool found_replay_failure = false;
  size_t budget;

  CHECK(ixs_facts_assume_pred(cold, predicate));
  ixs_facts_closure_cache_stats(ctx, &before_stats);
  CHECK(before_stats.lookups == 1 && before_stats.hits == 0 &&
        before_stats.stores == 1);

  for (budget = 0; budget < MAX_FAIL_BUDGET; budget++) {
    ixs_facts *failed = ixs_facts_create(ctx);
    ixs_bounds before = failed->bounds;
    bool ok;
    ixs_facts_closure_cache_stats(ctx, &before_stats);
    ixs_arena_set_fail_after(ixs_test_scratch(ctx), budget);
    ok = ixs_facts_assume_pred(failed, predicate);
    ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
    ixs_facts_closure_cache_stats(ctx, &after_stats);
    if (!ok && after_stats.hits == before_stats.hits + 1u) {
      /* A hit precedes replay, and this path has no closed-domain check. */
      CHECK(!failed->usable);
      CHECK(failed->bounds.vars == before.vars);
      CHECK(failed->bounds.nvars == before.nvars);
      CHECK(failed->bounds.exprs == before.exprs);
      CHECK(failed->bounds.nexprs == before.nexprs);
      found_replay_failure = true;
      break;
    }
  }
  CHECK(found_replay_failure);

  {
    ixs_facts *recovered = ixs_facts_create(ctx);
    ixs_facts_closure_cache_stats(ctx, &before_stats);
    CHECK(ixs_facts_assume_pred(recovered, predicate));
    CHECK(test_ixs_check_facts(recovered, predicate) == IXS_CHECK_TRUE);
    ixs_facts_closure_cache_stats(ctx, &after_stats);
    CHECK(after_stats.hits == before_stats.hits + 1u &&
          after_stats.stores == before_stats.stores);
  }

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_closure_cache_hit_rejects_open_domain(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "cache_open_x");
  ixs_node *d = ixs_sym(ctx, "cache_open_d");
  ixs_node *predicate = ixs_cmp(ctx, ixs_floor(ctx, ixs_div(ctx, x, d)),
                                IXS_CMP_EQ, ixs_int(ctx, 0));
  ixs_node *predicates[1] = {predicate};
  ixs_facts *incremental = ixs_facts_create(ctx);
  ixs_facts *closed = ixs_facts_create(ctx);
  ixs_bounds before = closed->bounds;
  ixs_facts_closure_cache_stats_result stats;

  CHECK(ixs_facts_assume_pred(incremental, predicate));
  CHECK(incremental->usable);
  ixs_facts_closure_cache_stats(ctx, &stats);
  CHECK(stats.lookups == 1 && stats.hits == 0 && stats.stores == 1);

  CHECK(!ixs_facts_assume_preds(closed, predicates, 1));
  CHECK(!closed->usable);
  CHECK(closed->bounds.vars == before.vars);
  CHECK(closed->bounds.nvars == before.nvars);
  CHECK(closed->bounds.exprs == before.exprs);
  CHECK(closed->bounds.nexprs == before.nexprs);
  CHECK(closed->bounds.nonzero == before.nonzero);
  CHECK(closed->bounds.nnonzero == before.nnonzero);
  ixs_facts_closure_cache_stats(ctx, &stats);
  CHECK(stats.lookups == 2 && stats.hits == 1 && stats.stores == 1);

  ixs_ctx_destroy(ctx);
}

static void test_public_facts_assume_batch_has_no_round_limit(void) {
  enum { CHAIN_LINKS = 1024, PREDICATE_COUNT = CHAIN_LINKS + 1 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *symbols[PREDICATE_COUNT];
  ixs_node *predicates[PREDICATE_COUNT];
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts_closure_cache_stats_result stats;
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
  ixs_facts_closure_cache_stats(ctx, &stats);
  CHECK(stats.lookups == 1 && stats.hits == 0 && stats.stores == 0 &&
        stats.bypasses == 1);

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
  CHECK(ixs_check(ctx, not_equal, &range, 1) == IXS_CHECK_FALSE);
  CHECK(test_ixs_check_facts(facts, not_equal) == IXS_CHECK_FALSE);

  ixs_ctx_destroy(ctx);
}

static void test_exact_check_assumption_fact_parity(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "exact_check_x");
  ixs_node *y = ixs_sym(ctx, "exact_check_y");
  ixs_node *three = ixs_int(ctx, 3);
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *low_zero = ixs_cmp(ctx, ixs_and(ctx, x, three), IXS_CMP_EQ, zero);
  ixs_node *toggled = ixs_xor(ctx, three, x);
  ixs_node *equal = ixs_cmp(ctx, toggled, IXS_CMP_EQ, x);
  ixs_node *different = ixs_cmp(ctx, toggled, IXS_CMP_NE, x);
  ixs_node *unknown = ixs_cmp(ctx, ixs_xor(ctx, x, y), IXS_CMP_EQ, x);
  ixs_facts *facts = ixs_facts_create(ctx);

  CHECK(ctx && x && y && three && zero && low_zero && toggled && equal &&
        different && unknown && facts);
  CHECK(ixs_check(ctx, equal, &low_zero, 1) == IXS_CHECK_FALSE);
  CHECK(ixs_check(ctx, different, &low_zero, 1) == IXS_CHECK_TRUE);
  CHECK(ixs_check(ctx, unknown, &low_zero, 1) == IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(facts, low_zero));
  CHECK(test_ixs_check_facts(facts, equal) == IXS_CHECK_FALSE);
  CHECK(test_ixs_check_facts(facts, different) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(facts, unknown) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_predicate_facts(facts, equal) == IXS_CHECK_FALSE);

  /* Both query owners unwind after an inconclusive exact proof. */
  CHECK(ixs_check(ctx, equal, &low_zero, 1) == IXS_CHECK_FALSE);
  CHECK(test_ixs_check_facts(facts, different) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_exact_check_allocation_failure_is_reusable(void) {
  ixs_ctx *legacy_ctx = ixs_ctx_create();
  ixs_node *legacy_x = ixs_sym(legacy_ctx, "exact_check_oom_x");
  ixs_node *legacy_three = ixs_int(legacy_ctx, 3);
  ixs_node *legacy_zero = ixs_int(legacy_ctx, 0);
  ixs_node *legacy_assumption =
      ixs_cmp(legacy_ctx, ixs_and(legacy_ctx, legacy_x, legacy_three),
              IXS_CMP_EQ, legacy_zero);
  ixs_node *legacy_query =
      ixs_cmp(legacy_ctx, ixs_xor(legacy_ctx, legacy_three, legacy_x),
              IXS_CMP_EQ, legacy_x);
  ixs_ctx *facts_ctx = ixs_ctx_create();
  ixs_node *facts_x = ixs_sym(facts_ctx, "exact_fact_check_oom_x");
  ixs_node *facts_three = ixs_int(facts_ctx, 3);
  ixs_node *facts_zero = ixs_int(facts_ctx, 0);
  ixs_node *facts_assumption =
      ixs_cmp(facts_ctx, ixs_and(facts_ctx, facts_x, facts_three), IXS_CMP_EQ,
              facts_zero);
  ixs_node *facts_query = ixs_cmp(
      facts_ctx, ixs_xor(facts_ctx, facts_three, facts_x), IXS_CMP_EQ, facts_x);
  ixs_facts *facts = ixs_facts_create(facts_ctx);

  CHECK(legacy_ctx && legacy_x && legacy_three && legacy_zero &&
        legacy_assumption && legacy_query);
  CHECK(legacy_ctx->bounds_query_state == NULL);
  ixs_arena_set_fail_after(&legacy_ctx->arena, 0);
  CHECK(ixs_check(legacy_ctx, legacy_query, &legacy_assumption, 1) ==
        IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(&legacy_ctx->arena, IXS_ARENA_FAILURE_DISABLED);
  CHECK(ixs_check(legacy_ctx, legacy_query, &legacy_assumption, 1) ==
        IXS_CHECK_FALSE);

  CHECK(facts_ctx && facts_x && facts_three && facts_zero && facts_assumption &&
        facts_query && facts);
  CHECK(ixs_facts_assume_pred(facts, facts_assumption));
  ixs_arena_set_fail_after(ixs_test_scratch(facts_ctx), 0);
  CHECK(test_ixs_check_facts(facts, facts_query) == IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(ixs_test_scratch(facts_ctx),
                           IXS_ARENA_FAILURE_DISABLED);
  ixs_ctx_clear_errors(facts_ctx);
  CHECK(test_ixs_check_facts(facts, facts_query) == IXS_CHECK_FALSE);

  ixs_ctx_destroy(facts_ctx);
  ixs_ctx_destroy(legacy_ctx);
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
  ixs_check_result result;
  size_t errors;
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
  errors = ixs_ctx_nerrors(ctx);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  result = ixs_check_integer_valued_facts(facts, expr);
  CHECK(result == IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == errors + 1);
  CHECK(strstr(ixs_ctx_error(ctx, errors), "out of memory") != NULL);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  result = ixs_check_integer_valued_facts(facts, expr);
  CHECK(result == IXS_CHECK_TRUE);
  result = ixs_check_divisible_facts(facts, expr, 1);
  CHECK(result == IXS_CHECK_TRUE);

  /* An owned malformed node reaches the internal proof boundary.  The active
   * nested-Piecewise hold transports that producer violation as INVALID. */
  {
    ixs_node *arg[1] = {expr};
    ixs_node *malformed = ixs_node_assoc(ctx, IXS_MAX, 1, arg);
    errors = ixs_ctx_nerrors(ctx);
    result = ixs_check_integer_valued_facts(facts, malformed);
    CHECK(result == IXS_CHECK_UNKNOWN);
    CHECK(ixs_ctx_nerrors(ctx) == errors + 1);
    CHECK(strstr(ixs_ctx_error(ctx, errors), "invalid") != NULL);
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

static void test_generic_piecewise_scalar_selector(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "piecewise_scalar_x");
  ixs_node *condition = ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, 0));
  ixs_node *values[2] = {ixs_rat(ctx, 1, 2), ixs_int(ctx, 0)};
  ixs_node *conditions[2] = {condition, ixs_true(ctx)};
  ixs_node *piecewise = ixs_pw(ctx, 2, values, conditions);
  ixs_node *scaled = ixs_mul(ctx, ixs_int(ctx, 2), piecewise);
  ixs_node *indicator = ixs_mul(ctx, ixs_rat(ctx, 1, 2), condition);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_node *simplified;

  CHECK(ctx && x && condition && piecewise && scaled && indicator && facts);
  CHECK(test_ixs_equivalent_facts(facts, piecewise, indicator) ==
        IXS_CHECK_TRUE);
  simplified = test_ixs_simplify_facts(facts, scaled);
  CHECK(ixs_same_node(simplified, condition));
  CHECK(test_ixs_check_integer_valued_facts(facts, simplified) ==
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
  CHECK(!ixs_get_known_bits_facts(facts, ixs_sym(other, "x"), &bits));
  CHECK(bits.known_zero == 0 && bits.known_one == 0 &&
        bits.pow2 == IXS_POW2_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_get_known_bits_facts(facts, ctx->sentinel_error, &bits));
  CHECK(bits.known_zero == 0 && bits.known_one == 0 &&
        bits.pow2 == IXS_POW2_UNKNOWN);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "sentinel") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(!ixs_get_known_bits_facts(facts, NULL, &bits));
  CHECK(bits.known_zero == 0 && bits.known_one == 0 &&
        bits.pow2 == IXS_POW2_UNKNOWN);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "NULL expression") != NULL);

  CHECK(!ixs_get_known_bits_facts(NULL, x, &bits));
  CHECK(bits.known_zero == 0 && bits.known_one == 0 &&
        bits.pow2 == IXS_POW2_UNKNOWN);

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
  CHECK(ixs_get_symbol_congruence_facts(facts, k, &modulus, &residue));
  CHECK(modulus == 32 && residue == 5);

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

static void test_public_predicate_implications(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *row = ixs_sym(ctx, "predicate_implication_row");
  ixs_node *column = ixs_sym(ctx, "predicate_implication_column");
  ixs_node *row_domain =
      ixs_and(ctx, ixs_cmp(ctx, row, IXS_CMP_GE, ixs_int(ctx, 0)),
              ixs_cmp(ctx, row, IXS_CMP_LT, ixs_int(ctx, 8)));
  ixs_node *column_domain =
      ixs_and(ctx, ixs_cmp(ctx, column, IXS_CMP_GE, ixs_int(ctx, 0)),
              ixs_cmp(ctx, column, IXS_CMP_LT, ixs_int(ctx, 4)));
  ixs_node *coordinate_domain = ixs_and(ctx, row_domain, column_domain);
  ixs_node *linear = ixs_add(ctx, row, ixs_mul(ctx, ixs_int(ctx, 8), column));
  ixs_node *linear_domain =
      ixs_and(ctx, ixs_cmp(ctx, linear, IXS_CMP_GE, ixs_int(ctx, 0)),
              ixs_cmp(ctx, linear, IXS_CMP_LT, ixs_int(ctx, 32)));
  ixs_node *bounded =
      ixs_or(ctx, ixs_not(ctx, coordinate_domain), linear_domain);
  ixs_node *tight = ixs_or(ctx, ixs_not(ctx, coordinate_domain),
                           ixs_cmp(ctx, linear, IXS_CMP_LT, ixs_int(ctx, 31)));
  ixs_node *partial = ixs_or(ctx, ixs_not(ctx, coordinate_domain),
                             ixs_cmp(ctx, ixs_div(ctx, ixs_int(ctx, 1), row),
                                     IXS_CMP_GT, ixs_int(ctx, 0)));
  ixs_node *unsupported = ixs_or(
      ctx, ixs_not(ctx, row), ixs_cmp(ctx, row, IXS_CMP_GE, ixs_int(ctx, 0)));
  ixs_node *unsupported_antecedent =
      ixs_and(ctx,
              ixs_or(ctx, ixs_cmp(ctx, row, IXS_CMP_GE, ixs_int(ctx, 0)),
                     ixs_cmp(ctx, column, IXS_CMP_GE, ixs_int(ctx, 0))),
              ixs_cmp(ctx, row, IXS_CMP_LT, ixs_int(ctx, 8)));
  ixs_node *diagnostic_isolated =
      ixs_or(ctx, ixs_not(ctx, unsupported_antecedent), ixs_not(ctx, column));
  ixs_node *ternary_args[3] = {
      ixs_not(ctx, coordinate_domain),
      linear_domain,
      ixs_cmp(ctx, row, IXS_CMP_EQ, ixs_int(ctx, 99)),
  };
  ixs_node *ternary = ixs_or_many(ctx, 3, ternary_args);
  ixs_facts *empty = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);

  CHECK(ctx && row && column && coordinate_domain && linear && linear_domain &&
        bounded && tight && partial && unsupported && unsupported_antecedent &&
        diagnostic_isolated && ternary && empty && contradictory);
  CHECK(ixs_node_tag(bounded) == IXS_OR);
  CHECK(ixs_node_assoc_nargs(bounded) == 2);
  CHECK(test_ixs_check_predicate_facts(empty, bounded) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_predicate_facts(empty, tight) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_predicate_facts(empty, partial) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_node_tag(ternary) == IXS_OR);
  CHECK(ixs_node_assoc_nargs(ternary) == 3);
  CHECK(test_ixs_check_predicate_facts(empty, ternary) == IXS_CHECK_UNKNOWN);

  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_check_predicate_facts(empty, unsupported) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_predicate_facts(empty, diagnostic_isolated) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 0);

  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, row, IXS_CMP_GE, ixs_int(ctx, 10))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, row, IXS_CMP_LE, ixs_int(ctx, 5))));
  CHECK(test_ixs_check_predicate_facts(contradictory, bounded) ==
        IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_public_predicate_implication_oom_is_reusable(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *row = ixs_sym(ctx, "predicate_implication_oom_row");
  ixs_node *domain =
      ixs_and(ctx, ixs_cmp(ctx, row, IXS_CMP_GE, ixs_int(ctx, 0)),
              ixs_cmp(ctx, row, IXS_CMP_LT, ixs_int(ctx, 8)));
  ixs_node *query = ixs_or(ctx, ixs_not(ctx, domain),
                           ixs_cmp(ctx, row, IXS_CMP_LE, ixs_int(ctx, 7)));
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_arena *scratch = ixs_test_scratch(ctx);
  ixs_arena_mark mark = ixs_arena_save(scratch);
  size_t align = sizeof(void *);
  size_t offset = (scratch->current->used + align - 1u) & ~(align - 1u);
  size_t remaining = scratch->current->capacity - offset;

  CHECK(ctx && row && domain && query && facts);
  if (remaining > 0u)
    CHECK(ixs_arena_alloc(scratch, remaining, align) != NULL);
  ixs_ctx_clear_errors(ctx);
  ixs_arena_set_fail_after(scratch, 0);
  CHECK(test_ixs_check_predicate_facts(facts, query) == IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(scratch, IXS_ARENA_FAILURE_DISABLED);
  CHECK(!facts->bounds.oom);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  if (ixs_ctx_nerrors(ctx) != 0)
    CHECK(strstr(ixs_ctx_error(ctx, 0), "out of memory") != NULL);
  ixs_arena_restore(scratch, mark);

  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_check_predicate_facts(facts, query) == IXS_CHECK_TRUE);
  CHECK(ixs_ctx_nerrors(ctx) == 0);
  ixs_ctx_destroy(ctx);
}

static void test_public_predicate_comparison_implications(void) {
  static const ixs_cmp_op operations[] = {
      IXS_CMP_GT, IXS_CMP_GE, IXS_CMP_LT, IXS_CMP_LE, IXS_CMP_EQ, IXS_CMP_NE,
  };
  static const char folded_address_query[] =
      "-1 + Mod(slot, 4) >= 0 | "
      "-2016 + 1024*floor(1/32*xor(32, item)) + 2048*Mod(slot, 4) + "
      "32*xor(Mod(floor(1/32*xor(32, item)) + 2*Mod(slot, 4), 32), "
      "Mod(xor(32, item), 32)) <= 0";
  static const char *folded_address_facts[] = {
      "item == floor(item)", "item >= 0", "item < 64",
      "slot == floor(slot)", "slot >= 0", "slot < 4",
  };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "comparison_implication_x");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *two = ixs_int(ctx, 2);
  ixs_node *truth = ixs_true(ctx);
  ixs_facts *empty = ixs_facts_create(ctx);
  ixs_node
      *facts[sizeof(folded_address_facts) / sizeof(folded_address_facts[0])];
  ixs_facts *folded;
  size_t i;

  CHECK(ctx && x && zero && one && two && truth && empty);
  for (i = 0; i < sizeof(operations) / sizeof(operations[0]); i++) {
    ixs_node *disjunct = ixs_cmp(ctx, x, operations[i], zero);
    ixs_node *values[2] = {one, two};
    ixs_node *conditions[2] = {disjunct, truth};
    ixs_node *selected = ixs_pw(ctx, 2, values, conditions);
    ixs_node *consequent = ixs_cmp(ctx, selected, IXS_CMP_EQ, two);
    ixs_node *query = ixs_or(ctx, disjunct, consequent);

    CHECK(ixs_node_tag(query) == IXS_OR);
    CHECK(ixs_node_assoc_nargs(query) == 2);
    CHECK(test_ixs_check_predicate_facts(empty, query) == IXS_CHECK_TRUE);
  }

  for (i = 0;
       i < sizeof(folded_address_facts) / sizeof(folded_address_facts[0]); i++)
    facts[i] = ixs_parse_pred(ctx, folded_address_facts[i],
                              strlen(folded_address_facts[i]));
  folded = ixs_facts_create_preds(IXS_TEST_SESSION(ctx), facts,
                                  sizeof(folded_address_facts) /
                                      sizeof(folded_address_facts[0]));
  CHECK(folded);
  CHECK(test_ixs_check_predicate_facts(
            folded, ixs_parse_pred(ctx, folded_address_query,
                                   strlen(folded_address_query))) ==
        IXS_CHECK_TRUE);

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
  ixs_node *item = ixs_sym(ctx, "equiv_wave_item");
  ixs_node *item_wave = ixs_floor(ctx, ixs_div(ctx, item, ixs_int(ctx, 32)));
  ixs_node *xor_wave =
      ixs_floor(ctx, ixs_div(ctx, ixs_xor(ctx, item, ixs_int(ctx, 32)),
                             ixs_int(ctx, 32)));
  ixs_node *swizzled_wave = ixs_floor(
      ctx,
      ixs_div(ctx,
              ixs_xor(ctx, ixs_floor(ctx, ixs_div(ctx, item, ixs_int(ctx, 2))),
                      ixs_int(ctx, 32)),
              ixs_int(ctx, 32)));
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
  ixs_facts *wave_facts = ixs_facts_create(ctx);
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

  CHECK(ixs_facts_assume_pred(wave_facts,
                              ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      wave_facts, ixs_cmp(ctx, item, IXS_CMP_LE, ixs_int(ctx, 63))));
  CHECK(test_ixs_equivalent_facts(wave_facts, xor_wave, item_wave) ==
        IXS_CHECK_FALSE);
  /* The expressions agree on part of the domain.  A proof engine that cannot
   * establish total equivalence must not manufacture FALSE by sampling it. */
  CHECK(test_ixs_equivalent_facts(wave_facts, swizzled_wave, item_wave) ==
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

static ixs_node *test_unsigned_i32(ixs_ctx *ctx, ixs_node *value) {
  return ixs_mod(ctx, value, ixs_int(ctx, INT64_C(4294967296)));
}

static ixs_node *test_signed_i32(ixs_ctx *ctx, ixs_node *value) {
  return ixs_add(ctx, ixs_int(ctx, INT64_C(-2147483648)),
                 ixs_mod(ctx,
                         ixs_add(ctx, ixs_int(ctx, INT64_C(2147483648)), value),
                         ixs_int(ctx, INT64_C(4294967296))));
}

static ixs_node *test_unsigned_i32_remainder(ixs_ctx *ctx, ixs_node *value,
                                             int64_t divisor) {
  return test_signed_i32(
      ctx, ixs_mod(ctx, test_unsigned_i32(ctx, value), ixs_int(ctx, divisor)));
}

static void test_generic_modulo_recurrence_equivalence(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *i = ixs_sym(ctx, "generic_modulo_recurrence_i");
  ixs_node *x = ixs_sym(ctx, "generic_fixed_width_x");
  ixs_node *scaled_lhs =
      ixs_mul(ctx, ixs_int(ctx, 8192),
              ixs_mod(ctx, ixs_add(ctx, i, ixs_int(ctx, 1)), ixs_int(ctx, 4)));
  ixs_node *scaled_rhs =
      ixs_mod(ctx,
              ixs_add(ctx, ixs_int(ctx, 8192),
                      ixs_mul(ctx, ixs_int(ctx, 8192),
                              ixs_mod(ctx, i, ixs_int(ctx, 4)))),
              ixs_int(ctx, 32768));
  ixs_node *x_plus_two = ixs_add(ctx, x, ixs_int(ctx, 2));
  ixs_node *fixed_lhs =
      test_unsigned_i32_remainder(ctx, test_signed_i32(ctx, x_plus_two), 5);
  ixs_node *fixed_rhs = ixs_mod(
      ctx,
      ixs_add(ctx, test_unsigned_i32_remainder(ctx, x, 5), ixs_int(ctx, 2)),
      ixs_int(ctx, 5));
  ixs_node *no_wrap =
      ixs_cmp(ctx, ixs_add(ctx, test_unsigned_i32(ctx, x), ixs_int(ctx, 2)),
              IXS_CMP_LT, ixs_int(ctx, INT64_C(4294967296)));
  ixs_facts *empty = ixs_facts_create(ctx);
  ixs_facts *safe = ixs_facts_create(ctx);
  ixs_facts *wraps = ixs_facts_create(ctx);

  CHECK(ctx && i && x && scaled_lhs && scaled_rhs && fixed_lhs && fixed_rhs &&
        no_wrap && empty && safe && wraps);
  CHECK(test_ixs_equivalent_facts(empty, scaled_lhs, scaled_rhs) ==
        IXS_CHECK_TRUE);
  CHECK(ixs_facts_assume_pred(safe, no_wrap));
  CHECK(test_ixs_equivalent_facts(safe, fixed_lhs, fixed_rhs) ==
        IXS_CHECK_TRUE);
  CHECK(ixs_facts_assume_pred(
      wraps, ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, INT64_C(4294967295)))));
  CHECK(test_ixs_equivalent_facts(wraps, fixed_lhs, fixed_rhs) ==
        IXS_CHECK_FALSE);

  ixs_ctx_destroy(ctx);
}

static void test_generic_mod_reconstruction_from_quotient_fact(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *item = ixs_sym(ctx, "mod_reconstruct_item");
  ixs_node *rank = ixs_sym(ctx, "mod_reconstruct_rank");
  ixs_node *flat = ixs_mul(ctx, ixs_int(ctx, 8), item);
  ixs_node *mod = ixs_mod(ctx, flat, ixs_int(ctx, 64));
  ixs_node *quotient = ixs_floor(ctx, ixs_div(ctx, flat, ixs_int(ctx, 64)));
  ixs_node *reconstructed =
      ixs_sub(ctx, flat, ixs_mul(ctx, ixs_int(ctx, 64), quotient));
  ixs_node *observed =
      ixs_mul(ctx, ixs_int(ctx, 2),
              ixs_add(ctx, mod, ixs_mul(ctx, ixs_int(ctx, 64), rank)));
  ixs_node *expected = ixs_mul(ctx, ixs_int(ctx, 2), flat);
  ixs_node *equality = ixs_cmp(ctx, observed, IXS_CMP_EQ, expected);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *range_only = ixs_facts_create(ctx);

  CHECK(ctx && item && rank && flat && mod && quotient && reconstructed &&
        observed && expected && equality && facts && range_only);
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, item, IXS_CMP_LE, ixs_int(ctx, 63))));
  CHECK(ixs_facts_assume_pred(facts, ixs_cmp(ctx, quotient, IXS_CMP_EQ, rank)));
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, rank, IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(test_ixs_equivalent_facts(facts, quotient, rank) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, quotient, ixs_int(ctx, 0)) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, reconstructed, flat) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, mod, flat) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, observed, expected) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_predicate_facts(facts, equality) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(range_only,
                              ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      range_only, ixs_cmp(ctx, item, IXS_CMP_LE, ixs_int(ctx, 63))));
  CHECK(test_ixs_equivalent_facts(range_only, mod, flat) == IXS_CHECK_UNKNOWN);

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
  ixs_range_result range;

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
  CHECK(!ixs_range_facts(facts, direct, &range));
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(!range.has_lower && !range.has_upper);
  CHECK(ixs_range_facts(facts, direct, &range));

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

static ixs_node *test_low_bit_wrap(ixs_ctx *ctx, ixs_node *value,
                                   int64_t modulus) {
  return ixs_mod(ctx, value, ixs_int(ctx, modulus));
}

static void test_public_equivalence_low_bit_normalization(void) {
  const int64_t modulus = INT64_C(4294967296);
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "equiv_low_bits_x");
  ixs_node *y = ixs_sym(ctx, "equiv_low_bits_y");
  ixs_node *z = ixs_sym(ctx, "equiv_low_bits_z");
  ixs_node *wrapped_x = test_low_bit_wrap(ctx, x, modulus);
  ixs_node *wrapped_y = test_low_bit_wrap(ctx, y, modulus);
  ixs_node *wrapped_z = test_low_bit_wrap(ctx, z, modulus);
  ixs_node *targets[3] = {x, y, z};
  ixs_node *replacements[3] = {wrapped_x, wrapped_y, wrapped_z};
  ixs_node *add = ixs_add(
      ctx, ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 3), x), ixs_int(ctx, 7)),
      ixs_mul(ctx, ixs_int(ctx, -5), y));
  ixs_node *product = ixs_mul(ctx, ixs_add(ctx, x, ixs_int(ctx, 3)),
                              ixs_add(ctx, y, ixs_int(ctx, 5)));
  ixs_node *nested_product =
      ixs_mul(ctx, ixs_add(ctx, product, ixs_int(ctx, 7)),
              ixs_add(ctx, z, ixs_int(ctx, 9)));
  ixs_node *xor_expr = ixs_xor(ctx, x, ixs_int(ctx, 85));
  ixs_node *and_expr = ixs_and(ctx, x, ixs_int(ctx, 255));
  ixs_node *or_expr = ixs_or(ctx, y, ixs_int(ctx, 256));
  ixs_node *add_wrapped = ixs_subs_multi(ctx, add, 3, targets, replacements);
  ixs_node *product_wrapped =
      ixs_subs_multi(ctx, product, 3, targets, replacements);
  ixs_node *nested_product_wrapped =
      ixs_subs_multi(ctx, nested_product, 3, targets, replacements);
  ixs_node *xor_wrapped =
      ixs_subs_multi(ctx, xor_expr, 3, targets, replacements);
  ixs_node *and_wrapped =
      ixs_subs_multi(ctx, and_expr, 3, targets, replacements);
  ixs_node *or_wrapped = ixs_subs_multi(ctx, or_expr, 3, targets, replacements);
  ixs_node *add_lhs = test_low_bit_wrap(ctx, add, modulus);
  ixs_node *add_rhs = test_low_bit_wrap(ctx, add_wrapped, modulus);
  ixs_node *product_lhs = test_low_bit_wrap(ctx, product, modulus);
  ixs_node *product_rhs = test_low_bit_wrap(ctx, product_wrapped, modulus);
  ixs_node *nested_product_lhs =
      test_low_bit_wrap(ctx, nested_product, modulus);
  ixs_node *nested_product_rhs =
      test_low_bit_wrap(ctx, nested_product_wrapped, modulus);
  ixs_node *xor_lhs = test_low_bit_wrap(ctx, xor_expr, modulus);
  ixs_node *xor_rhs = test_low_bit_wrap(ctx, xor_wrapped, modulus);
  ixs_node *and_lhs = test_low_bit_wrap(ctx, and_expr, modulus);
  ixs_node *and_rhs = test_low_bit_wrap(ctx, and_wrapped, modulus);
  ixs_node *or_lhs = test_low_bit_wrap(ctx, or_expr, modulus);
  ixs_node *or_rhs = test_low_bit_wrap(ctx, or_wrapped, modulus);
  ixs_node *compatible_lhs = test_low_bit_wrap(ctx, product, 4);
  ixs_node *compatible_product =
      ixs_mul(ctx, ixs_add(ctx, test_low_bit_wrap(ctx, x, 16), ixs_int(ctx, 3)),
              ixs_add(ctx, y, ixs_int(ctx, 5)));
  ixs_node *compatible_rhs = test_low_bit_wrap(ctx, compatible_product, 4);
  ixs_node *equality = ixs_cmp(ctx, product_lhs, IXS_CMP_EQ, product_rhs);
  ixs_node *inequality = ixs_cmp(ctx, product_lhs, IXS_CMP_NE, product_rhs);
  ixs_node *assumption = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_facts *facts = ixs_facts_create(ctx);

  CHECK(ctx && x && y && z && wrapped_x && wrapped_y && wrapped_z && add &&
        product && nested_product && xor_expr && and_expr && or_expr &&
        add_wrapped && product_wrapped && nested_product_wrapped &&
        xor_wrapped && and_wrapped && or_wrapped && add_lhs && add_rhs &&
        product_lhs && product_rhs && nested_product_lhs &&
        nested_product_rhs && xor_lhs && xor_rhs && and_lhs && and_rhs &&
        or_lhs && or_rhs && compatible_lhs && compatible_product &&
        compatible_rhs && equality && inequality && assumption && facts);

  CHECK(test_ixs_equivalent_facts(facts, add_lhs, add_rhs) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, product_lhs, product_rhs) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, product_rhs, product_lhs) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, nested_product_lhs,
                                  nested_product_rhs) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, xor_lhs, xor_rhs) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, and_lhs, and_rhs) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, or_lhs, or_rhs) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, compatible_lhs, compatible_rhs) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(facts, equality) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(facts, inequality) == IXS_CHECK_FALSE);
  CHECK(ixs_check(ctx, equality, &assumption, 1) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_public_equivalence_low_bit_rejections(void) {
  const int64_t modulus = INT64_C(4294967296);
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "equiv_low_bits_reject_x");
  ixs_node *y = ixs_sym(ctx, "equiv_low_bits_reject_y");
  ixs_node *d = ixs_sym(ctx, "equiv_low_bits_reject_d");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *wrapped_x = test_low_bit_wrap(ctx, x, modulus);
  ixs_node *wrapped_y = test_low_bit_wrap(ctx, y, modulus);
  ixs_node *product = ixs_mul(ctx, ixs_add(ctx, x, ixs_int(ctx, 3)),
                              ixs_add(ctx, y, ixs_int(ctx, 5)));
  ixs_node *wrapped_product =
      ixs_mul(ctx, ixs_add(ctx, wrapped_x, ixs_int(ctx, 3)),
              ixs_add(ctx, wrapped_y, ixs_int(ctx, 5)));
  ixs_node *different_lhs = test_low_bit_wrap(ctx, product, modulus);
  ixs_node *different_rhs = test_low_bit_wrap(
      ctx, ixs_add(ctx, wrapped_product, ixs_int(ctx, 1)), modulus);
  ixs_node *nonpow_lhs = test_low_bit_wrap(ctx, product, 12);
  ixs_node *nonpow_product =
      ixs_mul(ctx, ixs_add(ctx, test_low_bit_wrap(ctx, x, 12), ixs_int(ctx, 3)),
              ixs_add(ctx, test_low_bit_wrap(ctx, y, 12), ixs_int(ctx, 5)));
  ixs_node *nonpow_rhs = test_low_bit_wrap(ctx, nonpow_product, 12);
  ixs_node *unequal_lhs = test_low_bit_wrap(ctx, product, 16);
  ixs_node *unequal_product =
      ixs_mul(ctx, ixs_add(ctx, test_low_bit_wrap(ctx, x, 32), ixs_int(ctx, 3)),
              ixs_add(ctx, test_low_bit_wrap(ctx, y, 32), ixs_int(ctx, 5)));
  ixs_node *unequal_rhs = test_low_bit_wrap(ctx, unequal_product, 32);
  ixs_node *dynamic_lhs = ixs_mod(ctx, product, d);
  ixs_node *dynamic_product =
      ixs_mul(ctx, ixs_add(ctx, ixs_mod(ctx, x, d), ixs_int(ctx, 3)),
              ixs_add(ctx, ixs_mod(ctx, y, d), ixs_int(ctx, 5)));
  ixs_node *dynamic_rhs = ixs_mod(ctx, dynamic_product, d);
  ixs_node *rational_lhs = test_low_bit_wrap(
      ctx,
      ixs_mul(ctx,
              ixs_add(ctx, ixs_div(ctx, x, ixs_int(ctx, 2)), ixs_int(ctx, 3)),
              ixs_add(ctx, y, ixs_int(ctx, 5))),
      16);
  ixs_node *rational_rhs = test_low_bit_wrap(
      ctx,
      ixs_mul(
          ctx,
          ixs_add(ctx,
                  ixs_div(ctx, test_low_bit_wrap(ctx, x, 16), ixs_int(ctx, 2)),
                  ixs_int(ctx, 3)),
          ixs_add(ctx, y, ixs_int(ctx, 5))),
      16);
  ixs_node *round_lhs = test_low_bit_wrap(
      ctx, ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 3))), 16);
  ixs_node *round_rhs = test_low_bit_wrap(
      ctx,
      ixs_floor(ctx,
                ixs_div(ctx, test_low_bit_wrap(ctx, x, 16), ixs_int(ctx, 3))),
      16);
  ixs_node *piecewise_values[2] = {x, zero};
  ixs_node *piecewise_conditions[2] = {ixs_cmp(ctx, x, IXS_CMP_GE, zero),
                                       ixs_true(ctx)};
  ixs_node *wrapped_piecewise_values[2] = {test_low_bit_wrap(ctx, x, 16), zero};
  ixs_node *wrapped_piecewise_conditions[2] = {
      ixs_cmp(ctx, test_low_bit_wrap(ctx, x, 16), IXS_CMP_GE, zero),
      ixs_true(ctx)};
  ixs_node *piecewise_lhs = test_low_bit_wrap(
      ctx, ixs_pw(ctx, 2, piecewise_values, piecewise_conditions), 16);
  ixs_node *piecewise_rhs = test_low_bit_wrap(
      ctx,
      ixs_pw(ctx, 2, wrapped_piecewise_values, wrapped_piecewise_conditions),
      16);
  ixs_node *shared_opaque_lhs = test_low_bit_wrap(
      ctx,
      ixs_add(ctx, wrapped_x,
              ixs_floor(ctx, ixs_div(ctx, wrapped_x, ixs_int(ctx, 3)))),
      modulus);
  ixs_node *shared_opaque_rhs = test_low_bit_wrap(
      ctx, ixs_add(ctx, x, ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)))),
      modulus);
  ixs_node *incompatible_lhs = test_low_bit_wrap(ctx, product, 4);
  ixs_node *incompatible_product =
      ixs_mul(ctx, ixs_add(ctx, test_low_bit_wrap(ctx, x, 6), ixs_int(ctx, 3)),
              ixs_add(ctx, y, ixs_int(ctx, 5)));
  ixs_node *incompatible_rhs = test_low_bit_wrap(ctx, incompatible_product, 4);
  ixs_node *reciprocal_lhs =
      test_low_bit_wrap(ctx,
                        ixs_mul(ctx, ixs_div(ctx, ixs_int(ctx, 1), x),
                                ixs_add(ctx, y, ixs_int(ctx, 1))),
                        16);
  ixs_node *reciprocal_rhs = test_low_bit_wrap(
      ctx,
      ixs_mul(ctx, ixs_div(ctx, ixs_int(ctx, 1), test_low_bit_wrap(ctx, x, 16)),
              ixs_add(ctx, y, ixs_int(ctx, 1))),
      16);
  ixs_node *undefined = test_low_bit_wrap(ctx, ixs_div(ctx, x, d), 16);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *dynamic_facts = ixs_facts_create(ctx);
  ixs_facts *contradictory = ixs_facts_create(ctx);
  ixs_node *other_x = ixs_sym(other, "equiv_low_bits_reject_x");
  ixs_node *other_y = ixs_sym(other, "equiv_low_bits_reject_y");
  ixs_node *other_product =
      ixs_mul(other,
              ixs_add(other, test_low_bit_wrap(other, other_x, modulus),
                      ixs_int(other, 3)),
              ixs_add(other, test_low_bit_wrap(other, other_y, modulus),
                      ixs_int(other, 5)));
  ixs_node *other_rhs = test_low_bit_wrap(other, other_product, modulus);

  CHECK(ctx && other && x && y && d && zero && wrapped_x && wrapped_y &&
        product && wrapped_product && different_lhs && different_rhs &&
        nonpow_lhs && nonpow_product && nonpow_rhs && unequal_lhs &&
        unequal_product && unequal_rhs && dynamic_lhs && dynamic_product &&
        dynamic_rhs && rational_lhs && rational_rhs && round_lhs && round_rhs &&
        piecewise_lhs && piecewise_rhs && shared_opaque_lhs &&
        shared_opaque_rhs && incompatible_lhs && incompatible_product &&
        incompatible_rhs && reciprocal_lhs && reciprocal_rhs && undefined &&
        facts && dynamic_facts && contradictory && other_x && other_y &&
        other_product && other_rhs);

  CHECK(test_ixs_equivalent_facts(facts, different_lhs, different_rhs) !=
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, nonpow_lhs, nonpow_rhs) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_facts(facts, unequal_lhs, unequal_rhs) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_facts_assume_pred(dynamic_facts,
                              ixs_cmp(ctx, d, IXS_CMP_GT, ixs_int(ctx, 0))));
  CHECK(test_ixs_equivalent_facts(dynamic_facts, dynamic_lhs, dynamic_rhs) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_facts(facts, rational_lhs, rational_rhs) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_facts(facts, round_lhs, round_rhs) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_facts(facts, piecewise_lhs, piecewise_rhs) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_facts(facts, shared_opaque_lhs,
                                  shared_opaque_rhs) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_facts(facts, incompatible_lhs, incompatible_rhs) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_facts(facts, reciprocal_lhs, reciprocal_rhs) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_facts(facts, undefined, undefined) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 2))));
  CHECK(ixs_facts_assume_pred(contradictory,
                              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 1))));
  CHECK(test_ixs_equivalent_facts(contradictory, different_lhs,
                                  different_lhs) == IXS_CHECK_UNKNOWN);

  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_equivalent_facts(facts, different_lhs, other_rhs) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "different context") != NULL);

  ixs_ctx_destroy(other);
  ixs_ctx_destroy(ctx);
}

static void test_public_equivalence_low_bit_growable_walk(void) {
  enum { DEEP_NODES = 96, WIDE_ARGS = 2200 };
  const int64_t modulus = INT64_C(4294967296);
  const size_t allowance = 4096u;
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "equiv_low_bits_deep_x");
  ixs_node *y = ixs_sym(ctx, "equiv_low_bits_deep_y");
  ixs_node *deep = x;
  ixs_node *deep_product;
  ixs_node *plain_product;
  ixs_node *deep_lhs;
  ixs_node *deep_rhs;
  ixs_node **wide_lhs_args = calloc(WIDE_ARGS, sizeof(*wide_lhs_args));
  ixs_node **wide_rhs_args = calloc(WIDE_ARGS, sizeof(*wide_rhs_args));
  ixs_node *wide_lhs;
  ixs_node *wide_rhs;
  ixs_node *product;
  ixs_node *wrapped_product;
  ixs_node *product_lhs;
  ixs_node *product_rhs;
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *probe = ixs_facts_create(ctx);
  size_t allocations;
  size_t failure_budget;
  unsigned i;
  char name[48];

  CHECK(ctx && x && y && wide_lhs_args && wide_rhs_args && facts && probe);
  if (!ctx || !x || !y || !wide_lhs_args || !wide_rhs_args || !facts ||
      !probe) {
    free(wide_lhs_args);
    free(wide_rhs_args);
    ixs_ctx_destroy(ctx);
    return;
  }

  for (i = 0; i < DEEP_NODES; i++)
    deep = test_low_bit_wrap(ctx, deep, 4096 - (int64_t)(2u * i));
  deep_product = ixs_mul(ctx, ixs_add(ctx, deep, ixs_int(ctx, 3)),
                         ixs_add(ctx, y, ixs_int(ctx, 5)));
  plain_product = ixs_mul(ctx, ixs_add(ctx, x, ixs_int(ctx, 3)),
                          ixs_add(ctx, y, ixs_int(ctx, 5)));
  deep_lhs = test_low_bit_wrap(ctx, deep_product, 2);
  deep_rhs = test_low_bit_wrap(ctx, plain_product, 2);
  CHECK(deep && deep_product && plain_product && deep_lhs && deep_rhs);
  CHECK(test_ixs_equivalent_facts(facts, deep_lhs, deep_rhs) == IXS_CHECK_TRUE);

  for (i = 0; i < WIDE_ARGS; i++) {
    (void)snprintf(name, sizeof(name), "equiv_low_bits_wide_%u", i);
    wide_lhs_args[i] = ixs_sym(ctx, name);
    wide_rhs_args[i] = test_low_bit_wrap(ctx, wide_lhs_args[i], modulus);
  }
  wide_lhs = ixs_xor_many(ctx, WIDE_ARGS, wide_lhs_args);
  wide_rhs = ixs_xor_many(ctx, WIDE_ARGS, wide_rhs_args);
  free(wide_lhs_args);
  free(wide_rhs_args);
  CHECK(wide_lhs && wide_rhs);
  CHECK(test_ixs_equivalent_facts(
            facts, test_low_bit_wrap(ctx, wide_lhs, modulus),
            test_low_bit_wrap(ctx, wide_rhs, modulus)) == IXS_CHECK_TRUE);

  product = ixs_mul(ctx, ixs_add(ctx, x, ixs_int(ctx, 3)),
                    ixs_add(ctx, y, ixs_int(ctx, 5)));
  wrapped_product = ixs_mul(
      ctx, ixs_add(ctx, test_low_bit_wrap(ctx, x, modulus), ixs_int(ctx, 3)),
      ixs_add(ctx, test_low_bit_wrap(ctx, y, modulus), ixs_int(ctx, 5)));
  product_lhs = test_low_bit_wrap(ctx, product, modulus);
  product_rhs = test_low_bit_wrap(ctx, wrapped_product, modulus);
  CHECK(product && wrapped_product && product_lhs && product_rhs);

  CHECK(test_ixs_equivalent_facts(probe, product_lhs, product_rhs) ==
        IXS_CHECK_TRUE);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), allowance);
  CHECK(test_ixs_equivalent_facts(probe, product_lhs, product_rhs) ==
        IXS_CHECK_TRUE);
  allocations = allowance - ixs_test_scratch(ctx)->fail_after;
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(allocations > 0u && allocations < allowance);
  failure_budget = allocations == 0u ? 0u : allocations - 1u;

  ixs_ctx_clear_errors(ctx);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), failure_budget);
  CHECK(test_ixs_equivalent_facts(probe, product_lhs, product_rhs) ==
        IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  if (ixs_ctx_nerrors(ctx) != 0)
    CHECK(strstr(ixs_ctx_error(ctx, 0), "out of memory") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_equivalent_facts(probe, product_lhs, product_rhs) ==
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
    CHECK(result.status == IXS_EXACT_DIVIDE_ERROR);
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

  ixs_ctx_clear_errors(ctx);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  result = ixs_try_exact_divide_facts(positive, guarded, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_ERROR);
  CHECK(result.quotient == NULL);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "out of memory") != NULL);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  result = ixs_try_exact_divide_facts(positive, guarded, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  CHECK(ixs_same_node(result.quotient, floor_reciprocal));

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
  ixs_node *strict_nodes[11];
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
  strict_nodes[4] = ixs_trunc(ctx, reciprocal);
  strict_nodes[5] = ixs_max(ctx, reciprocal, one);
  strict_nodes[6] = ixs_min(ctx, reciprocal, one);
  strict_nodes[7] = ixs_xor(ctx, reciprocal, one);
  strict_nodes[8] = ixs_cmp(ctx, reciprocal, IXS_CMP_GT, zero);
  strict_nodes[9] = ixs_and(ctx, strict_nodes[8], ixs_true(ctx));
  strict_nodes[10] = ixs_not(ctx, strict_nodes[8]);
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
    CHECK(ixs_node_nchildren(exprs[i]) == 3);
    CHECK(ixs_node_child(exprs[i], 2) == scaled);
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
  ixs_facts *closure_seed = ixs_facts_create(ctx);
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

  CHECK(ixs_facts_assume_pred(closure_seed, unclosed));
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
  const ixs_node *simplify_result;
  size_t errors;

  CHECK(ixs_facts_assume_pred(facts, lo));
  CHECK(ixs_facts_assume_pred(facts, hi));

  errors = ixs_ctx_nerrors(ctx);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  simplify_result = ixs_simplify_facts(facts, x);
  CHECK(simplify_result == NULL);
  CHECK(ixs_ctx_nerrors(ctx) == errors + 1);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  simplify_result = ixs_simplify_facts(facts, piecewise);
  CHECK(simplify_result == NULL);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(test_ixs_simplify_facts(facts, mod) == x);

  batch[0] = mod;
  batch[1] = piecewise;
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  ixs_simplify_batch_facts(facts, batch, 2);
  CHECK(batch[0] == mod);
  CHECK(batch[1] == piecewise);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(test_ixs_simplify_facts(facts, mod) == x);

  poisoned = ixs_facts_create(ctx);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(!ixs_facts_assume_pred(poisoned, lo));
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  simplify_result = ixs_simplify_facts(poisoned, mod);
  CHECK(ixs_is_domain_error(simplify_result));
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
  ixs_check_result result;

  ixs_session_init(&session, ctx);
  x = (ixs_sym)(&session, "fact_query_arena_teardown_x");
  zero = (ixs_int)(&session, 0);
  pred = (ixs_cmp)(&session, x, IXS_CMP_GE, zero);
  first = (ixs_facts_create)(&session);
  second = (ixs_facts_create)(&session);
  CHECK(first != NULL && second != NULL);

  result = (ixs_check_predicate_facts)(first, pred);
  CHECK(result == IXS_CHECK_UNKNOWN);
  result = (ixs_check_predicate_facts)(second, pred);
  CHECK(result == IXS_CHECK_UNKNOWN);
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
  CHECK(result == IXS_CHECK_UNKNOWN);

  after_reset = (ixs_facts_create)(&session);
  CHECK(after_reset != NULL);
  result = (ixs_check_predicate_facts)(after_reset, pred);
  CHECK(result == IXS_CHECK_UNKNOWN);
  CHECK(after_reset->bounds.query_arena.current != NULL ||
        after_reset->bounds.query_arena.spare != NULL);

  ixs_session_destroy(&session);
  CHECK(after_reset->impl == NULL && after_reset->epoch == 0 &&
        after_reset->bounds.query_arena.current == NULL &&
        after_reset->bounds.query_arena.spare == NULL);
  result = (ixs_check_predicate_facts)(after_reset, pred);
  CHECK(result == IXS_CHECK_UNKNOWN);
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
  ixs_node *minus_one = ixs_int(ctx, -1);

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(ixs_xor_many(ctx, 3, args) == NULL);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(ixs_node_tag(ixs_xor_many(ctx, 3, args)) == IXS_XOR);

  ixs_arena_set_fail_after(&ctx->arena, 0);
  CHECK(ixs_xor_many(ctx, 2, constants) == NULL);
  ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
  CHECK(ixs_xor_many(ctx, 2, constants) == ixs_int(ctx, 3));

  ixs_arena_set_fail_after(&ctx->arena, 0);
  CHECK(ixs_and(ctx, partial, minus_one) == NULL);
  ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
  CHECK(ixs_node_tag(ixs_and(ctx, partial, minus_one)) == IXS_AND);

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

static void test_mod_inverse_watchers_fixed_point_and_work(void) {
  enum { WATCHERS = 80, UNRELATED = 128 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_session_binding binding;
  ixs_bounds bounds;
  ixs_bounds forked;
  ixs_node *x = ixs_sym(ctx, "mod_watch_x");
  ixs_node *mod8 = ixs_mod(ctx, x, ixs_int(ctx, 8));
  ixs_node *mod16 = ixs_mod(ctx, x, ixs_int(ctx, 16));
  ixs_interval iv;
  size_t watcher_count;
  size_t visits;
  int modulus;
  int i;

  CHECK(ctx && x && mod8 && mod16);
  CHECK(ixs_session_bind(&binding, IXS_TEST_SESSION(ctx)) == ctx);
  CHECK(ixs_bounds_init_ctx(&bounds, ctx, &ctx->scratch));
  ixs_bounds_add_expr(&bounds, mod8, ixs_interval_exact(3, 1));
  ixs_bounds_add_expr(&bounds, mod16, ixs_interval_range(0, 1, 7, 1));
  watcher_count = bounds.nmod_inverse_watchers;
  ixs_bounds_add_expr(&bounds, mod8, ixs_interval_exact(3, 1));
  CHECK(bounds.nmod_inverse_watchers == watcher_count);
  ixs_bounds_add_expr(&bounds, x, ixs_interval_range(-7, 1, 7, 1));
  iv = ixs_bounds_get(&bounds, x);
  CHECK(iv.valid && !iv.lo_inf && !iv.hi_inf && iv.lo_p == 3 && iv.lo_q == 1 &&
        iv.hi_p == 3 && iv.hi_q == 1);

  CHECK(ixs_bounds_fork(&forked, &bounds));
  CHECK(forked.mod_inverse_heads != bounds.mod_inverse_heads);
  CHECK(forked.mod_inverse_watchers != bounds.mod_inverse_watchers);
  ixs_bounds_add_expr(&forked, x, ixs_interval_exact(3, 1));
  CHECK(!forked.oom && !bounds.oom);
  ixs_bounds_destroy(&forked);
  ixs_bounds_destroy(&bounds);

  CHECK(ixs_bounds_init_ctx(&bounds, ctx, &ctx->scratch));
  bounds.mod_inverse_watch_visits = 0;
  for (modulus = WATCHERS + 1; modulus >= 2; modulus--)
    ixs_bounds_add_expr(&bounds, ixs_mod(ctx, x, ixs_int(ctx, modulus)),
                        ixs_interval_range(0, 1, modulus - 2, 1));
  for (i = 0; i < UNRELATED; i++) {
    char name[48];
    int written = snprintf(name, sizeof(name), "mod_watch_unrelated_%d", i);
    ixs_node *other;
    CHECK(written > 0 && (size_t)written < sizeof(name));
    other = ixs_sym(ctx, name);
    CHECK(other != NULL);
    ixs_bounds_add_expr(&bounds, ixs_mod(ctx, other, ixs_int(ctx, 97)),
                        ixs_interval_range(0, 1, 95, 1));
  }
  CHECK(!bounds.oom);
  CHECK(bounds.mod_inverse_watch_visits == 0);
  ixs_bounds_add_expr(&bounds, x, ixs_interval_range(0, 1, WATCHERS, 1));
  visits = bounds.mod_inverse_watch_visits;
  iv = ixs_bounds_get(&bounds, x);
  CHECK(iv.valid && !iv.lo_inf && !iv.hi_inf && iv.lo_p == 0 && iv.hi_p == 0);
  CHECK(visits <= 2u * WATCHERS + 2u);
  ixs_bounds_destroy(&bounds);
  ixs_session_unbind(&binding);
  ixs_ctx_destroy(ctx);
}

static void test_mod_inverse_watcher_fork_oom_is_atomic(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "mod_watch_oom_x");
  ixs_node *mod8 = ixs_mod(ctx, x, ixs_int(ctx, 8));
  ixs_node *mod16 = ixs_mod(ctx, x, ixs_int(ctx, 16));
  ixs_range_result residue3 = {true, true, 3, 1, 3, 1};
  ixs_range_result residue0_to7 = {true, true, 0, 1, 7, 1};
  ixs_range_result x_range = {true, true, -7, 1, 7, 1};
  ixs_range_result observed;
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_session_binding binding;
  ixs_arena_mark mark;
  ixs_bounds candidate;
  bool candidate_ready = false;

  CHECK(ctx && x && mod8 && mod16 && facts);
  CHECK(ixs_facts_assume_range(facts, mod8, &residue3));
  CHECK(ixs_facts_assume_range(facts, mod16, &residue0_to7));
  CHECK(ixs_session_bind(&binding, IXS_TEST_SESSION(ctx)) == ctx);
  mark = ixs_arena_save(&ctx->scratch);
  candidate_ready = ixs_bounds_fork(&candidate, &facts->bounds);
  CHECK(candidate_ready);
  if (candidate_ready) {
    ixs_arena_set_fail_after(&candidate.query_arena, 0);
    ixs_bounds_add_expr(&candidate, x, ixs_interval_range(-7, 1, 7, 1));
    CHECK(candidate.oom);
    ixs_bounds_destroy(&candidate);
  }
  ixs_arena_restore(&ctx->scratch, mark);
  ixs_session_unbind(&binding);

  CHECK(test_ixs_range_facts(facts, x, &observed));
  CHECK(!observed.has_lower && !observed.has_upper);
  CHECK(ixs_facts_assume_range(facts, x, &x_range));
  CHECK(test_ixs_range_facts(facts, x, &observed));
  CHECK(observed.has_lower && observed.lower_p == 3 && observed.lower_q == 1);
  CHECK(observed.has_upper && observed.upper_p == 3 && observed.upper_q == 1);

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
  test_bounds_propagate_trunc();

  /* Bounds: fork */
  test_bounds_fork();
  test_bounds_expr_index_fork();
  test_bounds_difference_fork();
  test_bounds_exact_fork();
  test_mod_inverse_watchers_fixed_point_and_work();
  test_mod_inverse_watcher_fork_oom_is_atomic();

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
  test_bounds_check_wave_radix_floor_sums();
  test_bounds_check_radix_certificate_guards();
  test_bounds_check_composite_divisibility();
  test_bounds_check_pow2_fact();
  test_bounds_check_mask_fact();
  test_bounds_check_contradiction_unknown();
  test_public_pow2_fact();
  test_bounds_check_non_cmp();
  test_bounds_check_extreme_rhs_parity();
  test_bounds_partial_predicate_is_semantic_unknown();

  /* Bounds: public range API */
  test_public_range_basic();
  test_public_range_unbounded();
  test_public_range_rational();
  test_public_range_tightens_integer_lattice();
  test_public_range_unknown();
  test_public_range_int64_extrema();
  test_public_range_mod_int64_min_step();
  test_public_range_mod_requires_positive_divisor();
  test_public_range_mod_nonnegative_dividend_cap();
  test_public_range_mod_congruence_intersection();
  test_public_range_congruence_tightens_endpoints();
  test_public_range_grouped_mod_congruence();
  test_public_grouped_add_wave_identity();
  test_public_congruent_radix_reconstruction();
  test_public_range_congruence_alignment_overflow();
  test_public_range_difference_constraint_propagation();
  test_public_modular_projection_difference();
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
  test_public_facts_assume_batch_closure_cache_keys();
  test_public_facts_assume_batch_closure_cache_duplicates();
  test_public_facts_assume_batch_closure_cache_collisions();
  test_public_facts_assume_large_batch_closure_cache();
  test_public_facts_closure_cache_allocation_is_optional();
  test_public_facts_closure_cache_replay_failure_is_atomic();
  test_public_facts_closure_cache_hit_rejects_open_domain();
  test_public_facts_assume_batch_has_no_round_limit();
  test_public_facts_assume_batch_mid_simplify_oom();
  test_public_difference_constraint_oom_is_atomic();
  test_public_exact_equality_oom_is_atomic();
  test_public_difference_potential_overflow_is_atomic();
  test_public_equivalence_common_guard_aligned_packet();
  test_ctx_node_ownership_uses_intern_table();
  test_compound_assumption_legacy_fact_parity();
  test_fact_check_xor_cancellation_parity();
  test_exact_check_assumption_fact_parity();
  test_exact_check_allocation_failure_is_reusable();
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
  test_generic_piecewise_scalar_selector();
  test_public_fact_divisibility();
  test_public_fact_divisibility_rejects_reciprocal_factor();
  test_public_known_bits_propagation();
  test_public_known_bits_failures();
  test_public_symbol_congruence();
  test_public_congruence_query();
  test_public_predicate_tree_query();
  test_public_predicate_implications();
  test_public_predicate_implication_oom_is_reusable();
  test_public_predicate_comparison_implications();
  test_public_equivalence_congruent_signed_no_wrap();
  test_public_equivalence_ordered_congruence_forms();
  test_public_equivalence_ordered_candidate_growth();
  test_public_total_equivalence();
  test_generic_modulo_recurrence_equivalence();
  test_generic_mod_reconstruction_from_quotient_fact();
  test_public_trunc_primitive_constant_difference();
  test_public_truncating_remainder_equivalence();
  test_public_truncating_remainder_oom();
  test_public_remainder_projection_candidate_growth();
  test_public_remainder_projection_large_candidate_set();
  test_public_remainder_projection_shared_diamond();
  test_total_equivalence_new_proof_oom();
  test_public_equivalence_low_bit_normalization();
  test_public_equivalence_low_bit_rejections();
  test_public_equivalence_low_bit_growable_walk();
  test_public_equivalence_invalid_inputs();
  test_public_affine_and_constant_difference();
  test_public_finite_difference_and_additive_split();
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

  printf("test_bounds: %d/%d passed\n", tests_passed, tests_run);
  return tests_passed == tests_run ? 0 : 1;
}
