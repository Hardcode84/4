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
  test_substitution();
  test_sentinel_propagation();
  test_same_node();
  test_print_roundtrip();

  printf("test_simplify: %d/%d passed\n", tests_passed, tests_run);
  return tests_passed == tests_run ? 0 : 1;
}
