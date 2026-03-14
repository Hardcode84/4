#include <ixsimpl.h>
#include <stdio.h>
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
  ixs_node *result = ixs_subs(ctx, expr, "x", ixs_int(ctx, 5));
  CHECK(result && ixs_node_int_val(result) == 6);

  /* floor(x/2) with x=7 → 3 */
  expr = ixs_floor(ctx, ixs_mul(ctx, x, ixs_rat(ctx, 1, 2)));
  result = ixs_subs(ctx, expr, "x", ixs_int(ctx, 7));
  CHECK(result && ixs_node_int_val(result) == 3);

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

  ixs_ctx_destroy(ctx);
}

static void test_mod_extract_constant(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");

  /* Mod(4*floor(x) + 3, 16) → Mod(4*floor(x), 16) + 3
   * because |4| divides 16, floor(x) is integer-valued, and 3 < gcd(4)=4. */
  ixs_node *fx = ixs_floor(ctx, x);
  ixs_node *term = ixs_mul(ctx, ixs_int(ctx, 4), fx);
  ixs_node *sum = ixs_add(ctx, term, ixs_int(ctx, 3));
  ixs_node *expr = ixs_mod(ctx, sum, ixs_int(ctx, 16));
  ixs_node *r = ixs_simplify(ctx, expr, NULL, 0);
  CHECK(strcmp(pr(r), "3 + Mod(4*floor(x), 16)") == 0);

  /* Mod(8*floor(x) + 7, 16) → 7 + Mod(8*floor(x), 16)
   * because 8 divides 16, and 7 < gcd(8) = 8. */
  term = ixs_mul(ctx, ixs_int(ctx, 8), fx);
  sum = ixs_add(ctx, term, ixs_int(ctx, 7));
  expr = ixs_mod(ctx, sum, ixs_int(ctx, 16));
  r = ixs_simplify(ctx, expr, NULL, 0);
  CHECK(strcmp(pr(r), "7 + Mod(8*floor(x), 16)") == 0);

  /* Mod(4*floor(x) + 4, 16): c=4 >= gcd(4)=4, extraction must NOT fire. */
  sum = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 4), fx), ixs_int(ctx, 4));
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

  /* Multi-term: Mod(4*floor(x) + 6*floor(y) + 3, 12).
   * gcd(4, 6) = 2, and 3 >= 2: extraction must NOT fire.
   * (Wave's original min(4,6)=4 would wrongly allow 3 < 4.) */
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *fy = ixs_floor(ctx, y);
  ixs_node *t1 = ixs_mul(ctx, ixs_int(ctx, 4), fx);
  ixs_node *t2 = ixs_mul(ctx, ixs_int(ctx, 6), fy);
  sum = ixs_add(ctx, ixs_add(ctx, t1, t2), ixs_int(ctx, 3));
  expr = ixs_mod(ctx, sum, ixs_int(ctx, 12));
  r = ixs_simplify(ctx, expr, NULL, 0);
  CHECK(r && !ixs_is_error(r));
  CHECK(strstr(pr(r), "3 + Mod(") == NULL);

  /* Multi-term positive: Mod(4*floor(x) + 6*floor(y) + 1, 12).
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
  test_same_node();
  test_print_roundtrip();

  printf("test_simplify: %d/%d passed\n", tests_passed, tests_run);
  return tests_passed == tests_run ? 0 : 1;
}
