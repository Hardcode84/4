#include <ixsimpl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int g_fail;

#define CHECK(cond)                                                            \
  do {                                                                         \
    if (!(cond)) {                                                             \
      fprintf(stderr, "FAIL: %s:%d: %s\n", __FILE__, __LINE__, #cond);         \
      g_fail = 1;                                                              \
    }                                                                          \
  } while (0)

static void test_rat_accessors(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *r = ixs_rat(ctx, 3, 7);
  CHECK(ixs_node_tag(r) == IXS_RAT);
  CHECK(ixs_node_rat_num(r) == 3);
  CHECK(ixs_node_rat_den(r) == 7);

  ixs_node *neg = ixs_rat(ctx, -5, 3);
  CHECK(ixs_node_rat_num(neg) == -5);
  CHECK(ixs_node_rat_den(neg) == 3);

  ixs_ctx_destroy(ctx);
  printf("  rat_accessors: OK\n");
}

static void test_sym_name(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *s = ixs_sym(ctx, "hello");
  CHECK(ixs_node_tag(s) == IXS_SYM);
  CHECK(strcmp(ixs_node_sym_name(s), "hello") == 0);

  ixs_node *s2 = ixs_sym(ctx, "x");
  CHECK(strcmp(ixs_node_sym_name(s2), "x") == 0);

  ixs_ctx_destroy(ctx);
  printf("  sym_name: OK\n");
}

static void test_add_accessors(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *a = ixs_sym(ctx, "a");
  ixs_node *b = ixs_sym(ctx, "b");
  ixs_node *expr = ixs_add(ctx, ixs_int(ctx, 3), ixs_add(ctx, a, b));

  CHECK(ixs_node_tag(expr) == IXS_ADD);
  CHECK(ixs_node_tag(ixs_node_add_coeff(expr)) == IXS_INT);
  CHECK(ixs_node_int_val(ixs_node_add_coeff(expr)) == 3);

  uint32_t n = ixs_node_add_nterms(expr);
  CHECK(n == 2);

  int found_a = 0, found_b = 0;
  uint32_t i;
  for (i = 0; i < n; i++) {
    ixs_node *term = ixs_node_add_term(expr, i);
    ixs_node *coeff = ixs_node_add_term_coeff(expr, i);
    CHECK(ixs_node_tag(coeff) == IXS_INT);
    CHECK(ixs_node_int_val(coeff) == 1);
    if (ixs_same_node(term, a))
      found_a = 1;
    else if (ixs_same_node(term, b))
      found_b = 1;
  }
  CHECK(found_a && found_b);

  ixs_ctx_destroy(ctx);
  printf("  add_accessors: OK\n");
}

static void test_mul_accessors(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *expr = ixs_mul(ctx, ixs_int(ctx, 5), x);

  CHECK(ixs_node_tag(expr) == IXS_MUL);
  CHECK(ixs_node_int_val(ixs_node_mul_coeff(expr)) == 5);
  CHECK(ixs_node_mul_nfactors(expr) == 1);
  CHECK(ixs_same_node(ixs_node_mul_factor_base(expr, 0), x));
  CHECK(ixs_node_mul_factor_exp(expr, 0) == 1);

  ixs_ctx_destroy(ctx);
  printf("  mul_accessors: OK\n");
}

static void test_unary_accessors(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *half = ixs_rat(ctx, 1, 2);
  ixs_node *arg = ixs_add(ctx, x, half);

  ixs_node *fl = ixs_floor(ctx, arg);
  CHECK(ixs_node_tag(fl) == IXS_FLOOR);
  CHECK(ixs_same_node(ixs_node_unary_arg(fl), arg));

  ixs_node *ce = ixs_ceil(ctx, arg);
  CHECK(ixs_node_tag(ce) == IXS_CEIL);
  CHECK(ixs_same_node(ixs_node_unary_arg(ce), arg));

  ixs_node *xr = ixs_xor(ctx, ixs_sym(ctx, "a"), ixs_sym(ctx, "b"));
  ixs_node *nt = ixs_not(ctx, xr);
  CHECK(ixs_node_tag(nt) == IXS_NOT);
  CHECK(ixs_same_node(ixs_node_unary_arg(nt), xr));

  ixs_ctx_destroy(ctx);
  printf("  unary_accessors: OK\n");
}

static void test_binary_accessors(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *a = ixs_sym(ctx, "a");
  ixs_node *b = ixs_sym(ctx, "b");

  ixs_node *mod = ixs_mod(ctx, a, b);
  CHECK(ixs_node_tag(mod) == IXS_MOD);
  CHECK(ixs_same_node(ixs_node_binary_lhs(mod), a));
  CHECK(ixs_same_node(ixs_node_binary_rhs(mod), b));

  ixs_node *mx = ixs_max(ctx, a, b);
  CHECK(ixs_node_tag(mx) == IXS_MAX);
  CHECK(ixs_same_node(ixs_node_binary_lhs(mx), a));
  CHECK(ixs_same_node(ixs_node_binary_rhs(mx), b));

  ixs_node *mn = ixs_min(ctx, a, b);
  CHECK(ixs_node_tag(mn) == IXS_MIN);
  CHECK(ixs_same_node(ixs_node_binary_lhs(mn), a));
  CHECK(ixs_same_node(ixs_node_binary_rhs(mn), b));

  ixs_node *xr = ixs_xor(ctx, a, b);
  CHECK(ixs_node_tag(xr) == IXS_XOR);
  CHECK(ixs_same_node(ixs_node_binary_lhs(xr), a));
  CHECK(ixs_same_node(ixs_node_binary_rhs(xr), b));

  ixs_node *diff = ixs_sub(ctx, a, b);
  ixs_node *cmp = ixs_cmp(ctx, diff, IXS_CMP_LT, ixs_int(ctx, 0));
  CHECK(ixs_node_tag(cmp) == IXS_CMP);
  CHECK(ixs_same_node(ixs_node_binary_lhs(cmp), diff));
  CHECK(ixs_same_node(ixs_node_binary_rhs(cmp), ixs_int(ctx, 0)));
  CHECK(ixs_node_cmp_op(cmp) == IXS_CMP_LT);

  ixs_ctx_destroy(ctx);
  printf("  binary_accessors: OK\n");
}

static void test_pw_accessors(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *v0 = ixs_int(ctx, 10);
  ixs_node *c0 = ixs_cmp(ctx, x, IXS_CMP_GT, ixs_int(ctx, 0));
  ixs_node *v1 = ixs_int(ctx, 20);
  ixs_node *c1 = ixs_true(ctx);
  ixs_node *vals[] = {v0, v1};
  ixs_node *conds[] = {c0, c1};
  ixs_node *pw = ixs_pw(ctx, 2, vals, conds);

  CHECK(ixs_node_tag(pw) == IXS_PIECEWISE);
  CHECK(ixs_node_pw_ncases(pw) == 2);
  CHECK(ixs_same_node(ixs_node_pw_value(pw, 0), v0));
  CHECK(ixs_same_node(ixs_node_pw_cond(pw, 0), c0));
  CHECK(ixs_same_node(ixs_node_pw_value(pw, 1), v1));
  CHECK(ixs_same_node(ixs_node_pw_cond(pw, 1), c1));

  ixs_ctx_destroy(ctx);
  printf("  pw_accessors: OK\n");
}

static void test_logic_accessors(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *c1 = ixs_cmp(ctx, x, IXS_CMP_GT, ixs_int(ctx, 0));
  ixs_node *c2 = ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 10));

  ixs_node *and_node = ixs_and(ctx, c1, c2);
  CHECK(ixs_node_tag(and_node) == IXS_AND);
  CHECK(ixs_node_logic_nargs(and_node) == 2);
  CHECK(ixs_same_node(ixs_node_logic_arg(and_node, 0), c1) ||
        ixs_same_node(ixs_node_logic_arg(and_node, 1), c1));
  CHECK(ixs_same_node(ixs_node_logic_arg(and_node, 0), c2) ||
        ixs_same_node(ixs_node_logic_arg(and_node, 1), c2));

  ixs_node *or_node = ixs_or(ctx, c1, c2);
  CHECK(ixs_node_tag(or_node) == IXS_OR);
  CHECK(ixs_node_logic_nargs(or_node) == 2);

  ixs_ctx_destroy(ctx);
  printf("  logic_accessors: OK\n");
}

int main(void) {
  printf("test_introspect:\n");
  test_rat_accessors();
  test_sym_name();
  test_add_accessors();
  test_mul_accessors();
  test_unary_accessors();
  test_binary_accessors();
  test_pw_accessors();
  test_logic_accessors();
  if (g_fail) {
    printf("SOME TESTS FAILED\n");
    return 1;
  }
  printf("all introspect tests passed\n");
  return 0;
}
