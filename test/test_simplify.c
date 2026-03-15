/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include <ixsimpl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int tests_run = 0;
static int tests_passed = 0;

#define CHECK(cond)                                                            \
  do {                                                                         \
    tests_run++;                                                               \
    if (!(cond)) {                                                             \
      fprintf(stderr, "FAIL: %s:%d: %s\n", __FILE__, __LINE__, #cond);         \
    } else {                                                                   \
      tests_passed++;                                                          \
    }                                                                          \
  } while (0)

static char buf[4096];

static const char *pr(ixs_node *n) {
  ixs_print(n, buf, sizeof(buf));
  return buf;
}

static void test_add_canonicalize(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");

  /* x + x → 2*x */
  ixs_node *r = ixs_add(ctx, x, x);
  CHECK(strcmp(pr(r), "2*x") == 0);

  /* x + 0 → x */
  r = ixs_add(ctx, x, ixs_int(ctx, 0));
  CHECK(r == x);

  /* 0 + x → x */
  r = ixs_add(ctx, ixs_int(ctx, 0), x);
  CHECK(r == x);

  /* 3 + 4 → 7 */
  r = ixs_add(ctx, ixs_int(ctx, 3), ixs_int(ctx, 4));
  CHECK(ixs_node_int_val(r) == 7);

  /* (x + y) + (x + y) → 2*x + 2*y */
  ixs_node *xy = ixs_add(ctx, x, y);
  r = ixs_add(ctx, xy, xy);
  CHECK(r && !ixs_is_error(r));

  ixs_ctx_destroy(ctx);
}

static void test_mul_canonicalize(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");

  /* x * 1 → x */
  ixs_node *r = ixs_mul(ctx, x, ixs_int(ctx, 1));
  CHECK(r == x);

  /* 1 * x → x */
  r = ixs_mul(ctx, ixs_int(ctx, 1), x);
  CHECK(r == x);

  /* x * 0 → 0 */
  r = ixs_mul(ctx, x, ixs_int(ctx, 0));
  CHECK(ixs_node_int_val(r) == 0);

  /* 3 * 4 → 12 */
  r = ixs_mul(ctx, ixs_int(ctx, 3), ixs_int(ctx, 4));
  CHECK(ixs_node_int_val(r) == 12);

  /* x * x → x**2 */
  r = ixs_mul(ctx, x, x);
  CHECK(r && !ixs_is_error(r));

  ixs_ctx_destroy(ctx);
}

static void test_hash_consing(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x1 = ixs_sym(ctx, "x");
  ixs_node *x2 = ixs_sym(ctx, "x");
  CHECK(x1 == x2);

  ixs_node *a = ixs_add(ctx, x1, ixs_int(ctx, 1));
  ixs_node *b = ixs_add(ctx, x2, ixs_int(ctx, 1));
  CHECK(a == b);

  ixs_ctx_destroy(ctx);
}

static void test_floor_rules(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");

  /* floor(5) → 5 */
  CHECK(ixs_floor(ctx, ixs_int(ctx, 5)) == ixs_int(ctx, 5));

  /* floor(7/2) → 3 */
  CHECK(ixs_node_int_val(ixs_floor(ctx, ixs_rat(ctx, 7, 2))) == 3);

  /* floor(floor(x)) → floor(x) */
  ixs_node *fx = ixs_floor(ctx, x);
  CHECK(ixs_floor(ctx, fx) == fx);

  /* floor(ceil(x)) → ceil(x) */
  ixs_node *cx = ixs_ceil(ctx, x);
  CHECK(ixs_floor(ctx, cx) == cx);

  /* floor(x + 3) → floor(x) + 3 */
  ixs_node *xp3 = ixs_add(ctx, x, ixs_int(ctx, 3));
  ixs_node *fxp3 = ixs_floor(ctx, xp3);
  ixs_node *fxp3_expected = ixs_add(ctx, ixs_floor(ctx, x), ixs_int(ctx, 3));
  CHECK(fxp3 == fxp3_expected);

  ixs_ctx_destroy(ctx);
}

static void test_mod_rules(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");

  /* Mod(floor(x), 1) → 0 (only integer-valued args fold) */
  CHECK(ixs_node_int_val(ixs_mod(ctx, ixs_floor(ctx, x), ixs_int(ctx, 1))) ==
        0);

  /* Mod(17, 5) → 2 */
  CHECK(ixs_node_int_val(ixs_mod(ctx, ixs_int(ctx, 17), ixs_int(ctx, 5))) == 2);

  /* Mod(Mod(x, 5), 5) → Mod(x, 5) */
  ixs_node *mx5 = ixs_mod(ctx, x, ixs_int(ctx, 5));
  CHECK(ixs_mod(ctx, mx5, ixs_int(ctx, 5)) == mx5);

  ixs_ctx_destroy(ctx);
}

static void test_boolean(void) {
  ixs_ctx *ctx = ixs_ctx_create();

  /* True & x → x */
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *cmp = ixs_cmp(ctx, x, IXS_CMP_GT, ixs_int(ctx, 0));
  CHECK(ixs_and(ctx, ixs_true(ctx), cmp) == cmp);

  /* False & x → False */
  CHECK(ixs_and(ctx, ixs_false(ctx), cmp) == ixs_false(ctx));

  /* True | x → True */
  CHECK(ixs_or(ctx, ixs_true(ctx), cmp) == ixs_true(ctx));

  /* ~True → False */
  CHECK(ixs_not(ctx, ixs_true(ctx)) == ixs_false(ctx));

  /* ~~x → x */
  CHECK(ixs_not(ctx, ixs_not(ctx, cmp)) == cmp);

  ixs_ctx_destroy(ctx);
}

static void test_simplify_with_bounds(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *T0 = ixs_sym(ctx, "$T0");

  ixs_node *assumptions[] = {
      ixs_cmp(ctx, T0, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, T0, IXS_CMP_LT, ixs_int(ctx, 256)),
  };

  /* Mod($T0, 256) with 0 <= $T0 < 256 → $T0 */
  ixs_node *expr = ixs_mod(ctx, T0, ixs_int(ctx, 256));
  ixs_node *simplified = ixs_simplify(ctx, expr, assumptions, 2);
  CHECK(simplified == T0);

  ixs_ctx_destroy(ctx);
}

static void test_substitution(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");

  /* x + 1 with x=5 → 6 */
  ixs_node *expr = ixs_add(ctx, x, ixs_int(ctx, 1));
  ixs_node *result = ixs_subs(ctx, expr, x, ixs_int(ctx, 5));
  CHECK(result && ixs_node_int_val(result) == 6);

  /* floor(x/2) with x=7 → 3 */
  expr = ixs_floor(ctx, ixs_mul(ctx, x, ixs_rat(ctx, 1, 2)));
  result = ixs_subs(ctx, expr, x, ixs_int(ctx, 7));
  CHECK(result && ixs_node_int_val(result) == 3);

  /* Subtree replacement: replace Mod(x,4) with y in a larger expression */
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *mod_x4 = ixs_mod(ctx, x, ixs_int(ctx, 4));
  expr = ixs_add(ctx, mod_x4, ixs_int(ctx, 10));
  result = ixs_subs(ctx, expr, mod_x4, y);
  CHECK(result && strcmp(pr(result), "10 + y") == 0);

  /* Replace constant: 2 → 3 in 2*x + 2 */
  ixs_node *two = ixs_int(ctx, 2);
  ixs_node *three = ixs_int(ctx, 3);
  expr = ixs_add(ctx, ixs_mul(ctx, two, x), two);
  result = ixs_subs(ctx, expr, two, three);
  CHECK(result && strcmp(pr(result), "3 + 3*x") == 0);

  /* No match: target not present leaves expression unchanged */
  expr = ixs_add(ctx, x, ixs_int(ctx, 1));
  result = ixs_subs(ctx, expr, y, ixs_int(ctx, 99));
  CHECK(result && strcmp(pr(result), "1 + x") == 0);

  /* Multi-occurrence: Mod(x,4) + 2*Mod(x,4) with Mod(x,4)→y gives 3*y */
  expr = ixs_add(ctx, mod_x4, ixs_mul(ctx, ixs_int(ctx, 2), mod_x4));
  result = ixs_subs(ctx, expr, mod_x4, y);
  CHECK(result && strcmp(pr(result), "3*y") == 0);

  ixs_ctx_destroy(ctx);
}

static void test_sentinel_propagation(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");

  /* NULL propagation */
  CHECK(ixs_add(ctx, NULL, x) == NULL);
  CHECK(ixs_mul(ctx, x, NULL) == NULL);

  /* Sentinel propagation */
  ixs_node *err = ixs_mod(ctx, x, ixs_int(ctx, 0));
  CHECK(ixs_is_domain_error(err));
  ixs_ctx_clear_errors(ctx);

  ixs_node *r = ixs_add(ctx, err, x);
  CHECK(ixs_is_domain_error(r));

  r = ixs_floor(ctx, err);
  CHECK(ixs_is_domain_error(r));

  ixs_ctx_destroy(ctx);
}

static void test_floor_bounds_collapse(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");

  ixs_node *assumptions[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 64)),
  };

  /* floor(x/64) with 0 <= x < 64 → 0 */
  ixs_node *expr = ixs_floor(ctx, ixs_mul(ctx, x, ixs_rat(ctx, 1, 64)));
  ixs_node *r = ixs_simplify(ctx, expr, assumptions, 2);
  CHECK(r && ixs_node_int_val(r) == 0);

  /* ceiling(x/64) with 0 <= x < 64: ceil(0/64)=0, ceil(63/64)=1 — NOT constant
   */
  expr = ixs_ceil(ctx, ixs_mul(ctx, x, ixs_rat(ctx, 1, 64)));
  r = ixs_simplify(ctx, expr, assumptions, 2);
  CHECK(r && !ixs_is_error(r));
  /* Should NOT fold to a constant (0 != 1). */
  CHECK(ixs_node_tag(r) != IXS_INT);

  /* floor(x/32) with 0 <= x < 32 → 0 */
  ixs_node *a32[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 32)),
  };
  expr = ixs_floor(ctx, ixs_mul(ctx, x, ixs_rat(ctx, 1, 32)));
  r = ixs_simplify(ctx, expr, a32, 2);
  CHECK(r && ixs_node_int_val(r) == 0);

  /* ceiling(x/32) with 0 <= x < 1 (i.e. x=0 only) → 0 */
  ixs_node *a01[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 1)),
  };
  expr = ixs_ceil(ctx, ixs_mul(ctx, x, ixs_rat(ctx, 1, 32)));
  r = ixs_simplify(ctx, expr, a01, 2);
  CHECK(r && ixs_node_int_val(r) == 0);

  /* sym > 5/2 with integer sym → sym >= 3 (floor(5/2) + 1 = 3) */
  ixs_node *agt[] = {
      ixs_cmp(ctx, x, IXS_CMP_GT, ixs_rat(ctx, 5, 2)),
      ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 32)),
  };
  expr = ixs_mod(ctx, x, ixs_int(ctx, 32));
  r = ixs_simplify(ctx, expr, agt, 2);
  CHECK(r == x);

  /* sym < 7/3 with integer sym → sym <= 1 (ceil(7/3) - 1 = 1) */
  ixs_node *alt[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, x, IXS_CMP_LT, ixs_rat(ctx, 7, 3)),
  };
  expr = ixs_mod(ctx, x, ixs_int(ctx, 16));
  r = ixs_simplify(ctx, expr, alt, 2);
  CHECK(r == x);

  /* 2*x >= 10 → x >= 5; 2*x < 20 → x < 10 → x <= 9.
   * With x in [5, 9], Mod(x, 16) = x. */
  ixs_node *csym[] = {
      ixs_cmp(ctx, ixs_mul(ctx, ixs_int(ctx, 2), x), IXS_CMP_GE,
              ixs_int(ctx, 10)),
      ixs_cmp(ctx, ixs_mul(ctx, ixs_int(ctx, 2), x), IXS_CMP_LT,
              ixs_int(ctx, 20)),
  };
  expr = ixs_mod(ctx, x, ixs_int(ctx, 16));
  r = ixs_simplify(ctx, expr, csym, 2);
  CHECK(r == x);

  ixs_ctx_destroy(ctx);
}

static void test_mod_bounds_tighten(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");

  /* Mod(x, 16) with 0 <= x < 8 → x (bounds tighter than [0,15]) */
  ixs_node *assumptions[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 8)),
  };
  ixs_node *expr = ixs_mod(ctx, x, ixs_int(ctx, 16));
  ixs_node *r = ixs_simplify(ctx, expr, assumptions, 2);
  CHECK(r == x);

  /* Mod(x, 100) with 0 <= x < 50 → x */
  ixs_node *a50[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 50)),
  };
  expr = ixs_mod(ctx, x, ixs_int(ctx, 100));
  r = ixs_simplify(ctx, expr, a50, 2);
  CHECK(r == x);

  /* Mod(3/2*x, 1) must NOT get bounds [0,0] — dividend is not integer.
   * ceiling(Mod(3/2*x, 1)) must not collapse to 0. */
  ixs_node *half_x = ixs_div(ctx, x, ixs_int(ctx, 2));
  ixs_node *three_half_x = ixs_add(ctx, half_x, x);
  ixs_node *mod1 = ixs_mod(ctx, three_half_x, ixs_int(ctx, 1));
  ixs_node *ce = ixs_ceil(ctx, mod1);
  r = ixs_simplify(ctx, ce, NULL, 0);
  CHECK(r != ixs_int(ctx, 0));

  ixs_ctx_destroy(ctx);
}

static void test_mod_extract_constant(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");

  /* Mod(4*x + 3, 16) → 3 + Mod(4*x, 16)
   * because |4| divides 16, x is integer-valued, and 3 < gcd(4)=4.
   * (floor(x) → x since x is integer-valued.) */
  ixs_node *term = ixs_mul(ctx, ixs_int(ctx, 4), x);
  ixs_node *sum = ixs_add(ctx, term, ixs_int(ctx, 3));
  ixs_node *expr = ixs_mod(ctx, sum, ixs_int(ctx, 16));
  ixs_node *r = ixs_simplify(ctx, expr, NULL, 0);
  CHECK(strcmp(pr(r), "3 + Mod(4*x, 16)") == 0);

  /* Mod(8*x + 7, 16) → 7 + Mod(8*x, 16) */
  term = ixs_mul(ctx, ixs_int(ctx, 8), x);
  sum = ixs_add(ctx, term, ixs_int(ctx, 7));
  expr = ixs_mod(ctx, sum, ixs_int(ctx, 16));
  r = ixs_simplify(ctx, expr, NULL, 0);
  CHECK(strcmp(pr(r), "7 + Mod(8*x, 16)") == 0);

  /* Mod(4*x + 4, 16): c=4 >= gcd(4)=4, extraction must NOT fire. */
  sum = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 4), x), ixs_int(ctx, 4));
  expr = ixs_mod(ctx, sum, ixs_int(ctx, 16));
  r = ixs_simplify(ctx, expr, NULL, 0);
  CHECK(r && !ixs_is_error(r));
  CHECK(strstr(pr(r), "4 + Mod(") == NULL);

  /* Mod(4*(x/2) + 3, 16) → Mod(2*x + 3, 16).
   * 4*(1/2) collapses to 2, so gcd(2)=2, and 3 >= 2: no extraction. */
  ixs_node *xhalf = ixs_mul(ctx, x, ixs_rat(ctx, 1, 2));
  term = ixs_mul(ctx, ixs_int(ctx, 4), xhalf);
  sum = ixs_add(ctx, term, ixs_int(ctx, 3));
  expr = ixs_mod(ctx, sum, ixs_int(ctx, 16));
  r = ixs_simplify(ctx, expr, NULL, 0);
  CHECK(r && !ixs_is_error(r));
  CHECK(strstr(pr(r), "3 + Mod(") == NULL);

  /* Multi-term: Mod(4*x + 6*y + 3, 12).
   * gcd(4, 6) = 2, and 3 >= 2: extraction must NOT fire.
   * (Wave's original min(4,6)=4 would wrongly allow 3 < 4.) */
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *t1 = ixs_mul(ctx, ixs_int(ctx, 4), x);
  ixs_node *t2 = ixs_mul(ctx, ixs_int(ctx, 6), y);
  sum = ixs_add(ctx, ixs_add(ctx, t1, t2), ixs_int(ctx, 3));
  expr = ixs_mod(ctx, sum, ixs_int(ctx, 12));
  r = ixs_simplify(ctx, expr, NULL, 0);
  CHECK(r && !ixs_is_error(r));
  CHECK(strstr(pr(r), "3 + Mod(") == NULL);

  /* Multi-term positive: Mod(4*x + 6*y + 1, 12).
   * gcd(4, 6) = 2, and 1 < 2: extraction fires. */
  sum = ixs_add(ctx, ixs_add(ctx, t1, t2), ixs_int(ctx, 1));
  expr = ixs_mod(ctx, sum, ixs_int(ctx, 12));
  r = ixs_simplify(ctx, expr, NULL, 0);
  CHECK(strstr(pr(r), "1 + Mod(") != NULL);

  ixs_ctx_destroy(ctx);
}

static void test_floor_drop_small_rational(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");

  /* floor(floor(x)/3 + 1/6) with floor(x) >= 0 → floor(floor(x)/3)
   * because floor(x) is non-neg integer, denom=3, r=1/6, 1/6 < 1/3. */
  ixs_node *assumptions[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
  };
  ixs_node *fx = ixs_floor(ctx, x);
  ixs_node *inner =
      ixs_add(ctx, ixs_mul(ctx, fx, ixs_rat(ctx, 1, 3)), ixs_rat(ctx, 1, 6));
  ixs_node *expr = ixs_floor(ctx, inner);
  ixs_node *r = ixs_simplify(ctx, expr, assumptions, 1);
  ixs_node *expected =
      ixs_simplify(ctx, ixs_floor(ctx, ixs_mul(ctx, fx, ixs_rat(ctx, 1, 3))),
                   assumptions, 1);
  CHECK(r == expected);

  /* floor(Mod(x, 8)/4 + 1/8) with 0 <= x → floor(Mod(x,8)/4)
   * Mod(x, 8) ∈ [0,7] (non-negative integer), denom=4, r=1/8, 1/8 < 1/4. */
  ixs_node *mx8 = ixs_mod(ctx, x, ixs_int(ctx, 8));
  inner =
      ixs_add(ctx, ixs_mul(ctx, mx8, ixs_rat(ctx, 1, 4)), ixs_rat(ctx, 1, 8));
  expr = ixs_floor(ctx, inner);
  r = ixs_simplify(ctx, expr, assumptions, 1);
  expected =
      ixs_simplify(ctx, ixs_floor(ctx, ixs_mul(ctx, mx8, ixs_rat(ctx, 1, 4))),
                   assumptions, 1);
  CHECK(r == expected);

  /* Multi-term: floor(floor(x)/3 + Mod(x,8)/4 + 1/13) with x >= 0.
   * L = lcm(3, 4) = 12, r = 1/13, 1/13 < 1/12: rational is dropped. */
  ixs_node *assumptions2[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
  };
  inner = ixs_add(ctx,
                  ixs_add(ctx, ixs_mul(ctx, fx, ixs_rat(ctx, 1, 3)),
                          ixs_mul(ctx, mx8, ixs_rat(ctx, 1, 4))),
                  ixs_rat(ctx, 1, 13));
  expr = ixs_floor(ctx, inner);
  r = ixs_simplify(ctx, expr, assumptions2, 1);
  expected = ixs_simplify(
      ctx,
      ixs_floor(ctx, ixs_add(ctx, ixs_mul(ctx, fx, ixs_rat(ctx, 1, 3)),
                             ixs_mul(ctx, mx8, ixs_rat(ctx, 1, 4)))),
      assumptions2, 1);
  CHECK(r == expected);

  /* floor(floor(x)/3 + 1/3) should NOT drop: 1/3 is not < 1/3. */
  inner =
      ixs_add(ctx, ixs_mul(ctx, fx, ixs_rat(ctx, 1, 3)), ixs_rat(ctx, 1, 3));
  expr = ixs_floor(ctx, inner);
  r = ixs_simplify(ctx, expr, assumptions, 1);
  CHECK(r && !ixs_is_error(r));
  ixs_node *without_r =
      ixs_simplify(ctx, ixs_floor(ctx, ixs_mul(ctx, fx, ixs_rat(ctx, 1, 3))),
                   assumptions, 1);
  CHECK(!ixs_same_node(r, without_r));

  ixs_ctx_destroy(ctx);
}

static void test_nested_floor_ceil(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");

  /* floor(floor(x/3) / 5) → floor(x/15) */
  ixs_node *inner = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)));
  ixs_node *e = ixs_floor(ctx, ixs_div(ctx, inner, ixs_int(ctx, 5)));
  CHECK(e && strcmp(pr(e), "floor(1/15*x)") == 0);

  /* ceiling(ceiling(x/4) / 3) → ceiling(x/12) */
  inner = ixs_ceil(ctx, ixs_div(ctx, x, ixs_int(ctx, 4)));
  e = ixs_ceil(ctx, ixs_div(ctx, inner, ixs_int(ctx, 3)));
  CHECK(e && strcmp(pr(e), "ceiling(1/12*x)") == 0);

  /* floor(floor(x/2) / 2) → floor(x/4) */
  inner = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 2)));
  e = ixs_floor(ctx, ixs_div(ctx, inner, ixs_int(ctx, 2)));
  CHECK(e && strcmp(pr(e), "floor(1/4*x)") == 0);

  /* Negative: floor(2*floor(x/3) / 5) should NOT collapse */
  inner = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)));
  e = ixs_floor(ctx, ixs_mul(ctx, ixs_rat(ctx, 2, 5), inner));
  CHECK(e && strstr(pr(e), "floor") != NULL);

  /* Mod(a*floor(x/a), a) → 0 */
  inner = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 4)));
  e = ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, 4), inner), ixs_int(ctx, 4));
  CHECK(e == ixs_int(ctx, 0));

  /* Mod(6*floor(x/3), 3) → 0 (6 is multiple of 3) */
  inner = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)));
  e = ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, 6), inner), ixs_int(ctx, 3));
  CHECK(e == ixs_int(ctx, 0));

  /* Negative: Mod(3*floor(x/4), 4) should NOT simplify to 0 */
  inner = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 4)));
  e = ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, 3), inner), ixs_int(ctx, 4));
  CHECK(e != ixs_int(ctx, 0));

  /* Negative: ceiling(2*ceiling(x/4) / 3) should NOT collapse */
  inner = ixs_ceil(ctx, ixs_div(ctx, x, ixs_int(ctx, 4)));
  e = ixs_ceil(ctx, ixs_mul(ctx, ixs_rat(ctx, 2, 3), inner));
  CHECK(e && strstr(pr(e), "ceiling") != NULL);

  /* Negative: floor(floor(x/3) * 2) → 2*floor(x/3) (integer, no nesting) */
  inner = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)));
  e = ixs_floor(ctx, ixs_mul(ctx, ixs_int(ctx, 2), inner));
  CHECK(e && strcmp(pr(e), "2*floor(1/3*x)") == 0);

  ixs_ctx_destroy(ctx);
}

static void test_same_node(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  CHECK(ixs_same_node(NULL, NULL));
  CHECK(!ixs_same_node(ixs_int(ctx, 1), NULL));
  CHECK(ixs_same_node(ixs_int(ctx, 42), ixs_int(ctx, 42)));
  ixs_ctx_destroy(ctx);
}

static void test_print_roundtrip(void) {
  ixs_ctx *ctx = ixs_ctx_create();

  const char *exprs[] = {
      "x + y",     "3*x + 2",   "floor(x/2)", "ceiling(x + 1)",
      "Mod(x, 5)", "Max(x, y)", "Min(x, y)",  "xor(x, y)",
  };
  size_t i;
  for (i = 0; i < sizeof(exprs) / sizeof(exprs[0]); i++) {
    ixs_node *n = ixs_parse(ctx, exprs[i], strlen(exprs[i]));
    CHECK(n && !ixs_is_error(n));

    char out[1024];
    ixs_print(n, out, sizeof(out));

    /* Re-parse the printed output. */
    ixs_node *n2 = ixs_parse(ctx, out, strlen(out));
    CHECK(n2 && !ixs_is_error(n2));
    CHECK(ixs_same_node(n, n2));
  }

  ixs_ctx_destroy(ctx);
}

static void test_divisibility_assumptions(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *K = ixs_sym(ctx, "K");
  ixs_node *N = ixs_sym(ctx, "N");
  ixs_node *M = ixs_sym(ctx, "M");
  ixs_node *r;

  /* Assumption: Mod(K, 32) == 0  (K is divisible by 32) */
  ixs_node *div_K_32[] = {
      ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 32)), IXS_CMP_EQ,
              ixs_int(ctx, 0)),
  };

  /* floor(K/32) → K/32 when 32 | K */
  ixs_node *e1 = ixs_floor(ctx, ixs_div(ctx, K, ixs_int(ctx, 32)));
  r = ixs_simplify(ctx, e1, div_K_32, 1);
  CHECK(strcmp(pr(r), "1/32*K") == 0);

  /* Mod(K, 32) → 0 when 32 | K */
  ixs_node *e2 = ixs_mod(ctx, K, ixs_int(ctx, 32));
  r = ixs_simplify(ctx, e2, div_K_32, 1);
  CHECK(r == ixs_int(ctx, 0));

  /* floor(K/16) → K/16 since 32 | K implies 16 | K */
  ixs_node *e3 = ixs_floor(ctx, ixs_div(ctx, K, ixs_int(ctx, 16)));
  r = ixs_simplify(ctx, e3, div_K_32, 1);
  CHECK(strcmp(pr(r), "1/16*K") == 0);

  /* Mod(K, 64) should NOT simplify to 0 (32 | K does not imply 64 | K) */
  ixs_node *e4 = ixs_mod(ctx, K, ixs_int(ctx, 64));
  r = ixs_simplify(ctx, e4, div_K_32, 1);
  CHECK(r != ixs_int(ctx, 0));

  /* Mod(3*K, 32) → 0 when 32 | K */
  ixs_node *e5 =
      ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, 3), K), ixs_int(ctx, 32));
  r = ixs_simplify(ctx, e5, div_K_32, 1);
  CHECK(r == ixs_int(ctx, 0));

  /* Multiple assumptions: Mod(K, 32)==0 and Mod(N, 16)==0 */
  ixs_node *multi_div[] = {
      ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 32)), IXS_CMP_EQ,
              ixs_int(ctx, 0)),
      ixs_cmp(ctx, ixs_mod(ctx, N, ixs_int(ctx, 16)), IXS_CMP_EQ,
              ixs_int(ctx, 0)),
  };
  r = ixs_simplify(ctx, ixs_mod(ctx, K, ixs_int(ctx, 32)), multi_div, 2);
  CHECK(r == ixs_int(ctx, 0));
  r = ixs_simplify(ctx, ixs_mod(ctx, N, ixs_int(ctx, 16)), multi_div, 2);
  CHECK(r == ixs_int(ctx, 0));
  r = ixs_simplify(ctx, ixs_floor(ctx, ixs_div(ctx, N, ixs_int(ctx, 16))),
                   multi_div, 2);
  CHECK(strcmp(pr(r), "1/16*N") == 0);

  /* Mixed: floor(K/32) + Mod(K, 32) → K/32 when 32 | K */
  ixs_node *e6 = ixs_add(ctx, ixs_floor(ctx, ixs_div(ctx, K, ixs_int(ctx, 32))),
                         ixs_mod(ctx, K, ixs_int(ctx, 32)));
  r = ixs_simplify(ctx, e6, div_K_32, 1);
  CHECK(strcmp(pr(r), "1/32*K") == 0);

  /* Stronger assumption implies weaker: Mod(M, 256)==0 with tile=128 */
  ixs_node *div_M_256[] = {
      ixs_cmp(ctx, ixs_mod(ctx, M, ixs_int(ctx, 256)), IXS_CMP_EQ,
              ixs_int(ctx, 0)),
  };
  r = ixs_simplify(ctx, ixs_mod(ctx, M, ixs_int(ctx, 128)), div_M_256, 1);
  CHECK(r == ixs_int(ctx, 0));
  r = ixs_simplify(ctx, ixs_floor(ctx, ixs_div(ctx, M, ixs_int(ctx, 128))),
                   div_M_256, 1);
  CHECK(strcmp(pr(r), "1/128*M") == 0);

  /* Negative: floor(K/64) with 32|K should NOT drop floor */
  ixs_node *e_neg = ixs_floor(ctx, ixs_div(ctx, K, ixs_int(ctx, 64)));
  r = ixs_simplify(ctx, e_neg, div_K_32, 1);
  CHECK(strstr(pr(r), "floor") != NULL);

  /* No assumptions: expressions pass through unchanged */
  ixs_node *e7 = ixs_floor(ctx, ixs_div(ctx, K, ixs_int(ctx, 32)));
  r = ixs_simplify(ctx, e7, NULL, 0);
  CHECK(strstr(pr(r), "floor") != NULL);

  /* ceiling(K/32) → K/32 when 32 | K */
  ixs_node *e8 = ixs_ceil(ctx, ixs_div(ctx, K, ixs_int(ctx, 32)));
  r = ixs_simplify(ctx, e8, div_K_32, 1);
  CHECK(strcmp(pr(r), "1/32*K") == 0);

  ixs_ctx_destroy(ctx);
}

static void test_large_expressions(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  int i;

  /* ADD with >256 distinct terms. */
  {
    ixs_node *sum = ixs_int(ctx, 0);
    char name[16];
    for (i = 0; i < 300; i++) {
      snprintf(name, sizeof(name), "s%d", i);
      sum = ixs_add(ctx, sum, ixs_sym(ctx, name));
      CHECK(sum != NULL && !ixs_is_error(sum));
    }
    CHECK(ixs_node_tag(sum) == IXS_ADD);
  }

  /* MUL with >256 distinct factors. */
  {
    ixs_node *prod = ixs_int(ctx, 1);
    char name[16];
    for (i = 0; i < 300; i++) {
      snprintf(name, sizeof(name), "m%d", i);
      prod = ixs_mul(ctx, prod, ixs_sym(ctx, name));
      CHECK(prod != NULL && !ixs_is_error(prod));
    }
    CHECK(ixs_node_tag(prod) == IXS_MUL);
  }

  /* AND with >256 distinct args. */
  {
    ixs_node *conj = ixs_true(ctx);
    char name[16];
    for (i = 0; i < 300; i++) {
      snprintf(name, sizeof(name), "a%d", i);
      ixs_node *cmp =
          ixs_cmp(ctx, ixs_sym(ctx, name), IXS_CMP_GT, ixs_int(ctx, 0));
      conj = ixs_and(ctx, conj, cmp);
      CHECK(conj != NULL && !ixs_is_error(conj));
    }
    CHECK(ixs_node_tag(conj) == IXS_AND);
  }

  /* Piecewise with >256 cases. */
  {
    ixs_node **vals = malloc(300 * sizeof(*vals));
    ixs_node **conds = malloc(300 * sizeof(*conds));
    CHECK(vals != NULL && conds != NULL);
    char name[16];
    for (i = 0; i < 299; i++) {
      snprintf(name, sizeof(name), "p%d", i);
      vals[i] = ixs_sym(ctx, name);
      conds[i] = ixs_cmp(ctx, ixs_sym(ctx, name), IXS_CMP_GT, ixs_int(ctx, 0));
    }
    vals[299] = ixs_int(ctx, 0);
    conds[299] = ixs_true(ctx);
    ixs_node *pw = ixs_pw(ctx, 300, vals, conds);
    CHECK(pw != NULL && !ixs_is_error(pw));
    free(vals);
    free(conds);
  }

  ixs_ctx_destroy(ctx);
}

int main(void) {
  test_add_canonicalize();
  test_mul_canonicalize();
  test_hash_consing();
  test_floor_rules();
  test_mod_rules();
  test_boolean();
  test_simplify_with_bounds();
  test_floor_bounds_collapse();
  test_mod_bounds_tighten();
  test_mod_extract_constant();
  test_floor_drop_small_rational();
  test_substitution();
  test_sentinel_propagation();
  test_nested_floor_ceil();
  test_same_node();
  test_print_roundtrip();
  test_divisibility_assumptions();
  test_large_expressions();

  printf("test_simplify: %d/%d passed\n", tests_passed, tests_run);
  return tests_passed == tests_run ? 0 : 1;
}
