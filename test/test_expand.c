/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include <ixsimpl.h>
#include <string.h>

#ifndef IXS_TEST_AMALGAMATION
#include "bounds.h"
#include "node.h"
#endif

#include "test_check.h"

static char buf[4096];

static const char *pr(ixs_node *n) {
  ixs_print(n, buf, sizeof(buf));
  return buf;
}

static void test_expand_leaves(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *n5 = ixs_int(ctx, 5);

  CHECK(ixs_expand(ctx, x) == x);
  CHECK(ixs_expand(ctx, n5) == n5);
  CHECK(ixs_expand(ctx, NULL) == NULL);
  ixs_ctx_destroy(ctx);
}

static void test_expand_add_noop(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *sum = ixs_add(ctx, x, y);

  CHECK(ixs_expand(ctx, sum) == sum);
  ixs_ctx_destroy(ctx);
}

static void test_expand_const_times_add(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *a = ixs_sym(ctx, "a");
  ixs_node *b = ixs_sym(ctx, "b");

  /* 2*(a+b) -> 2*a + 2*b */
  ixs_node *expr = ixs_mul(ctx, ixs_int(ctx, 2), ixs_add(ctx, a, b));
  ixs_node *r = ixs_expand(ctx, expr);
  CHECK(strcmp(pr(r), "2*a + 2*b") == 0);
  ixs_ctx_destroy(ctx);
}

static void test_expand_two_sums(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *a = ixs_sym(ctx, "a");
  ixs_node *b = ixs_sym(ctx, "b");
  ixs_node *c = ixs_sym(ctx, "c");
  ixs_node *d = ixs_sym(ctx, "d");

  /* (a+b)*(c+d) -> canonical: a*d + a*c + b*c + b*d (SYM factors sorted) */
  ixs_node *expr = ixs_mul(ctx, ixs_add(ctx, a, b), ixs_add(ctx, c, d));
  ixs_node *r = ixs_expand(ctx, expr);
  const char *s = pr(r);
  CHECK(strstr(s, "a*d") != NULL);
  CHECK(strstr(s, "a*c") != NULL);
  CHECK(strstr(s, "b*c") != NULL);
  CHECK(strstr(s, "b*d") != NULL);
  ixs_ctx_destroy(ctx);
}

static void test_expand_sym_times_add(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *a = ixs_sym(ctx, "a");
  ixs_node *b = ixs_sym(ctx, "b");

  /* x*(a+b) -> a*x + b*x */
  ixs_node *expr = ixs_mul(ctx, x, ixs_add(ctx, a, b));
  ixs_node *r = ixs_expand(ctx, expr);
  const char *s = pr(r);
  CHECK(strstr(s, "a*x") != NULL);
  CHECK(strstr(s, "b*x") != NULL);
  CHECK(strstr(s, "+") != NULL);
  ixs_ctx_destroy(ctx);
}

static void test_expand_nested_add(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *a = ixs_sym(ctx, "a");
  ixs_node *b = ixs_sym(ctx, "b");

  /* 2*(a+b) + 3*(a+b) in an ADD should expand to 5*a + 5*b */
  ixs_node *e1 = ixs_mul(ctx, ixs_int(ctx, 2), ixs_add(ctx, a, b));
  ixs_node *e2 = ixs_mul(ctx, ixs_int(ctx, 3), ixs_add(ctx, a, b));
  ixs_node *expr = ixs_add(ctx, e1, e2);
  ixs_node *r = ixs_expand(ctx, expr);
  CHECK(strcmp(pr(r), "5*a + 5*b") == 0);
  ixs_ctx_destroy(ctx);
}

static void test_expand_inside_floor(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *a = ixs_sym(ctx, "a");
  ixs_node *b = ixs_sym(ctx, "b");

  /* floor(2*(a+b)) -> 2*a + 2*b (integer-valued, floor drops) */
  ixs_node *inner = ixs_mul(ctx, ixs_int(ctx, 2), ixs_add(ctx, a, b));
  ixs_node *expr = ixs_floor(ctx, inner);
  ixs_node *r = ixs_expand(ctx, expr);
  CHECK(strcmp(pr(r), "2*a + 2*b") == 0);
  ixs_ctx_destroy(ctx);
}

static void test_expand_inside_trunc(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *a = ixs_sym(ctx, "trunc_expand_a");
  ixs_node *b = ixs_sym(ctx, "trunc_expand_b");
  ixs_node *inner = ixs_div(
      ctx, ixs_mul(ctx, ixs_int(ctx, 2), ixs_add(ctx, a, b)), ixs_int(ctx, 3));
  ixs_node *expr = ixs_trunc(ctx, inner);
  ixs_node *expected = ixs_trunc(
      ctx,
      ixs_add(ctx,
              ixs_div(ctx, ixs_mul(ctx, ixs_int(ctx, 2), a), ixs_int(ctx, 3)),
              ixs_div(ctx, ixs_mul(ctx, ixs_int(ctx, 2), b), ixs_int(ctx, 3))));

  CHECK(ixs_expand(ctx, expr) == expected);
  ixs_ctx_destroy(ctx);
}

static void test_expand_already_expanded(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *a = ixs_sym(ctx, "a");
  ixs_node *b = ixs_sym(ctx, "b");
  ixs_node *c = ixs_sym(ctx, "c");

  /* a*b + c is already expanded */
  ixs_node *expr = ixs_add(ctx, ixs_mul(ctx, a, b), c);
  CHECK(ixs_expand(ctx, expr) == expr);
  ixs_ctx_destroy(ctx);
}

static void test_expand_three_factors(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *a = ixs_sym(ctx, "a");
  ixs_node *b = ixs_sym(ctx, "b");
  ixs_node *c = ixs_sym(ctx, "c");

  /* (a+b)*c*2 -> 2*a*c + 2*b*c */
  ixs_node *expr =
      ixs_mul(ctx, ixs_mul(ctx, ixs_add(ctx, a, b), c), ixs_int(ctx, 2));
  ixs_node *r = ixs_expand(ctx, expr);
  const char *s = pr(r);
  CHECK(strstr(s, "a*c") != NULL);
  CHECK(strstr(s, "b*c") != NULL);
  CHECK(strstr(s, "+") != NULL);
  ixs_ctx_destroy(ctx);
}

static void test_expand_piecewise(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *a = ixs_sym(ctx, "a");
  ixs_node *b = ixs_sym(ctx, "b");
  ixs_node *x = ixs_sym(ctx, "x");

  /* Piecewise((2*(a+b), x > 0), (0, True)) -> Piecewise((2*a+2*b, ...)) */
  ixs_node *vals[2];
  ixs_node *conds[2];
  vals[0] = ixs_mul(ctx, ixs_int(ctx, 2), ixs_add(ctx, a, b));
  conds[0] = ixs_cmp(ctx, x, IXS_CMP_GT, ixs_int(ctx, 0));
  vals[1] = ixs_int(ctx, 0);
  conds[1] = ixs_true(ctx);
  ixs_node *pw = ixs_pw(ctx, 2, vals, conds);
  ixs_node *r = ixs_expand(ctx, pw);
  const char *s = pr(r);
  CHECK(strstr(s, "2*a + 2*b") != NULL);
  CHECK(strstr(s, "Piecewise") != NULL);
  ixs_ctx_destroy(ctx);
}

static void test_expand_sentinel(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *err = ixs_parse(ctx, "???", 3);
  CHECK(ixs_is_error(err));
  CHECK(ixs_expand(ctx, err) == err);
  ixs_ctx_destroy(ctx);
}

#ifndef IXS_TEST_AMALGAMATION
static void test_expand_skips_dead_sentinel_branch(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "dead_sentinel_x");
  ixs_pwcase cases[2];
  ixs_node *expr;

  cases[0].value = ixs_mod(ctx, x, ixs_int(ctx, 0));
  cases[0].cond = ixs_false(ctx);
  cases[1].value = ixs_int(ctx, 42);
  cases[1].cond = ixs_true(ctx);
  expr = ixs_node_pw(ctx, 2, cases);
  CHECK(expr != NULL && ixs_node_tag(expr) == IXS_PIECEWISE);
  CHECK(ixs_expand(ctx, expr) == ixs_int(ctx, 42));

  {
    ixs_node *condition = ixs_cmp(ctx, x, IXS_CMP_GT, ixs_int(ctx, 0));
    ixs_pwcase branch_error_cases[2];
    ixs_pwcase condition_error_cases[2];
    ixs_pwcase value_error_cases[2];
    ixs_node *branch_error;
    ixs_node *condition_error;
    ixs_node *value_error;

    branch_error_cases[0].value = cases[0].value;
    branch_error_cases[0].cond = condition;
    branch_error_cases[1].value = ixs_int(ctx, 42);
    branch_error_cases[1].cond = ixs_true(ctx);
    condition_error_cases[0].value = ixs_int(ctx, 42);
    condition_error_cases[0].cond = condition;
    condition_error_cases[1].value = ixs_int(ctx, 7);
    condition_error_cases[1].cond = cases[0].value;
    value_error_cases[0].value = ixs_int(ctx, 42);
    value_error_cases[0].cond = condition;
    value_error_cases[1].value = cases[0].value;
    value_error_cases[1].cond = ixs_true(ctx);
    branch_error = ixs_expand(ctx, ixs_node_pw(ctx, 2, branch_error_cases));
    condition_error =
        ixs_expand(ctx, ixs_node_pw(ctx, 2, condition_error_cases));
    value_error = ixs_expand(ctx, ixs_node_pw(ctx, 2, value_error_cases));
    CHECK(ixs_node_tag(branch_error) == IXS_PIECEWISE);
    CHECK(condition_error == cases[0].value);
    CHECK(ixs_node_tag(value_error) == IXS_PIECEWISE);
    CHECK(ixs_subs(ctx, branch_error, x, ixs_int(ctx, 1)) == cases[0].value);
    CHECK(ixs_subs(ctx, branch_error, x, ixs_int(ctx, -1)) == ixs_int(ctx, 42));
    CHECK(ixs_subs(ctx, value_error, x, ixs_int(ctx, 1)) == ixs_int(ctx, 42));
    CHECK(ixs_subs(ctx, value_error, x, ixs_int(ctx, -1)) == cases[0].value);
  }
  ixs_ctx_destroy(ctx);
}
#endif

#ifndef IXS_TEST_AMALGAMATION
static void test_expand_cache(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_session other;
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *first = ixs_add(ctx, x, ixs_int(ctx, 1));
  ixs_node *expanded = ixs_expand(ctx, first);
  size_t i;

  CHECK(expanded == first);
  CHECK(ctx->transform_cache_used == 1);
  CHECK(ixs_node_transform_cache_lookup(ctx, first,
                                        IXS_NODE_TRANSFORM_EXPAND) == expanded);
  CHECK(ixs_expand(ctx, first) == expanded);
  CHECK(ctx->transform_cache_used == 1);

  ixs_session_init(&other, ctx);
  CHECK((ixs_expand)(&other, first) == expanded);
  CHECK(ctx->transform_cache_used == 1);
  ixs_session_destroy(&other);

  for (i = 2; i < 300; i++) {
    ixs_node *expr = ixs_add(ctx, x, ixs_int(ctx, (int64_t)i));
    CHECK(ixs_expand(ctx, expr) == expr);
  }
  CHECK(ctx->transform_cache_used == 299);
  CHECK(ctx->transform_cache_cap >= 512);
  CHECK(ixs_expand(ctx, first) == expanded);
  CHECK(ctx->transform_cache_used == 299);

  (ixs_session_reset)(IXS_TEST_SESSION(ctx));
  CHECK(ctx->transform_cache_used == 299);
  CHECK(ixs_expand(ctx, first) == expanded);
  CHECK(ctx->transform_cache_used == 299);

  ixs_ctx_stats_reset(ctx);
  CHECK(ctx->transform_cache_used == 0);
  CHECK(ixs_expand(ctx, first) == expanded);
  CHECK(ctx->transform_cache_used == 1);
  ixs_ctx_destroy(ctx);
}

static void test_expand_cache_failure_semantics(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *expr = ixs_add(ctx, x, ixs_int(ctx, 1));
  ixs_mulfactor factor;
  ixs_node *large_power;
  ixs_node *large_sum_power;
  ixs_node *min_negative_power;
  ixs_node *result;

  ixs_arena_set_fail_after(&ctx->arena, 0);
  CHECK(ixs_expand(ctx, expr) == expr);
  CHECK(ctx->transform_cache_used == 0);
  ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
  CHECK(ixs_expand(ctx, expr) == expr);
  CHECK(ctx->transform_cache_used == 1);

  factor.base = x;
  factor.exp = 65;
  large_power = ixs_node_mul(ctx, ixs_int(ctx, 1), 1, &factor);
  CHECK(large_power != NULL);
  ixs_ctx_clear_errors(ctx);
  result = ixs_expand(ctx, large_power);
  CHECK(result == large_power);
  CHECK(ixs_ctx_nerrors(ctx) == 0);

  factor.base = ixs_add(ctx, x, ixs_int(ctx, 1));
  factor.exp = 65;
  large_sum_power = ixs_node_mul(ctx, ixs_int(ctx, 1), 1, &factor);
  CHECK(large_sum_power != NULL);
  result = ixs_expand(ctx, large_sum_power);
  CHECK(result != NULL && !ixs_is_error(result));
  CHECK(ixs_node_tag(result) == IXS_ADD);
  CHECK(ixs_node_add_nterms(result) == 65u);

  factor.base = x;
  factor.exp = INT32_MIN;
  min_negative_power = ixs_node_mul(ctx, ixs_int(ctx, 1), 1, &factor);
  CHECK(min_negative_power != NULL);
  result = ixs_expand(ctx, min_negative_power);
  CHECK(result == min_negative_power);
  CHECK(ixs_ctx_nerrors(ctx) == 0);
  ixs_ctx_destroy(ctx);
}

static void test_expand_deep_iterative(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "expand_depth_x");
  ixs_node *child = x;
  size_t cached;
  unsigned i;

  for (i = 0; i < 4096u; i++)
    child = ixs_node_floor(ctx, child);
  CHECK(ixs_expand(ctx, child) == x);
  cached = ctx->transform_cache_used;
  CHECK(cached == 4096u);
  CHECK(ixs_expand(ctx, child) == x);
  CHECK(ctx->transform_cache_used == cached);
  CHECK(ixs_ctx_nerrors(ctx) == 0u);
  ixs_ctx_destroy(ctx);
}

static void test_expand_oom_retry(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "expand_oom_x");
  ixs_node *a = ixs_sym(ctx, "expand_oom_a");
  ixs_node *b = ixs_sym(ctx, "expand_oom_b");
  ixs_node *deep = x;
  ixs_node *product = ixs_mul(ctx, ixs_add(ctx, a, b), x);
  ixs_node *result;
  unsigned i;

  for (i = 0; i < 300u; i++)
    deep = ixs_node_floor(ctx, deep);

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(ixs_expand(ctx, deep) == NULL);
  CHECK(ctx->transform_cache_used == 0u);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(ixs_expand(ctx, deep) == x);

  ixs_ctx_stats_reset(ctx);
  ixs_arena_set_fail_after(&ctx->arena, 0);
  CHECK(ixs_expand(ctx, product) == NULL);
  CHECK(ixs_node_transform_cache_lookup(ctx, product,
                                        IXS_NODE_TRANSFORM_EXPAND) == NULL);
  ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
  result = ixs_expand(ctx, product);
  CHECK(result != NULL && !ixs_is_error(result));
  CHECK(strstr(pr(result), "a*expand_oom_x") != NULL);
  CHECK(strstr(pr(result), "b*expand_oom_x") != NULL);
  ixs_ctx_destroy(ctx);
}

static void test_expand_cycle_rejected(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  struct ixs_node_impl cycle;
  ixs_node *result;
  memset(&cycle, 0, sizeof(cycle));
  cycle.tag = IXS_FLOOR;
  cycle.u.unary.arg = (ixs_node *)&cycle;
  result = (ixs_expand)(IXS_TEST_SESSION(ctx), (ixs_node *)&cycle);
  CHECK(result != NULL && ixs_is_error(result));
  CHECK(ixs_ctx_nerrors(ctx) == 1u);
  if (ixs_ctx_nerrors(ctx) > 0u)
    CHECK(strstr(ixs_ctx_error(ctx, 0), "cyclic expression graph") != NULL);
  ixs_ctx_destroy(ctx);
}

static void test_simplify_signed_exponent_boundaries(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "signed_exp_x");
  ixs_node *k = ixs_sym(ctx, "signed_exp_k");
  ixs_node *one = ixs_int(ctx, 1);
  ixs_mulfactor factor;
  ixs_node *power;
  ixs_node *arg;
  ixs_node *expr;
  ixs_node *result;

  /* A representable inverse exponent above the former eager-fold cap still
   * participates in the rounding unwrap. */
  factor.base = k;
  factor.exp = -65;
  power = ixs_node_mul(ctx, one, 1, &factor);
  arg = ixs_mul(ctx, ixs_floor(ctx, x), power);
  expr = ixs_node_floor(ctx, arg);
  result = ixs_simplify(ctx, expr, NULL, 0);
  CHECK(result != NULL && !ixs_is_error(result));
  CHECK(strstr(pr(result), "floor(floor(") == NULL);

  /* Inverting INT32_MIN is not representable and would change definedness at
   * k == 0 if encoded as a nested reciprocal. The optional rule stays put. */
  factor.exp = INT32_MIN;
  power = ixs_node_mul(ctx, one, 1, &factor);
  arg = ixs_mul(ctx, ixs_floor(ctx, x), power);
  expr = ixs_node_floor(ctx, arg);
  result = ixs_simplify(ctx, expr, NULL, 0);
  CHECK(result != NULL && !ixs_is_error(result));
  CHECK(ixs_node_tag(result) == IXS_FLOOR);
  arg = ixs_node_unary_arg(result);
  CHECK(ixs_node_tag(arg) == IXS_MUL);
  {
    bool found = false;
    uint32_t i;
    for (i = 0; i < ixs_node_mul_nfactors(arg); i++) {
      if (ixs_node_mul_factor_base(arg, i) == k &&
          ixs_node_mul_factor_exp(arg, i) == INT32_MIN)
        found = true;
    }
    CHECK(found);
  }
  CHECK(ixs_ctx_nerrors(ctx) == 0u);

  ixs_ctx_destroy(ctx);
}

static void test_add_without_const_cache(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_addterm terms[2];
  ixs_node *shifted;
  ixs_node *pred;
  ixs_node *base;
  ixs_session_binding binding;
  ixs_bounds failed;
  ixs_bounds populated;
  ixs_bounds cached;

  terms[0].term = x;
  terms[0].coeff = one;
  terms[1].term = y;
  terms[1].coeff = one;
  if (ixs_node_cmp(ctx, terms[0].term, terms[1].term) > 0) {
    ixs_addterm swap = terms[0];
    terms[0] = terms[1];
    terms[1] = swap;
  }
  shifted = ixs_node_add(ctx, one, 2, terms);
  pred = ixs_cmp(ctx, shifted, IXS_CMP_GE, zero);
  CHECK(shifted != NULL && pred != NULL);
  CHECK(ixs_expand(ctx, shifted) == shifted);
  CHECK(ixs_node_transform_cache_lookup(ctx, shifted,
                                        IXS_NODE_TRANSFORM_EXPAND) == shifted);

  CHECK(ixs_session_bind(&binding, IXS_TEST_SESSION(ctx)) == ctx);
  CHECK(ixs_bounds_init_ctx(&failed, ctx, &ctx->scratch));
  ixs_arena_set_fail_after(&ctx->arena, 0);
  CHECK(!ixs_bounds_add_assumption(&failed, pred));
  CHECK(ixs_node_transform_cache_lookup(
            ctx, shifted, IXS_NODE_TRANSFORM_ADD_WITHOUT_CONST) == NULL);

  ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
  CHECK(ixs_bounds_init_ctx(&populated, ctx, &ctx->scratch));
  CHECK(ixs_bounds_add_assumption(&populated, pred));
  base = ixs_node_transform_cache_lookup(ctx, shifted,
                                         IXS_NODE_TRANSFORM_ADD_WITHOUT_CONST);
  CHECK(base != NULL);
  CHECK(strcmp(pr(base), "x + y") == 0);

  CHECK(ixs_bounds_init_ctx(&cached, ctx, &ctx->scratch));
  ixs_arena_set_fail_after(&ctx->arena, 0);
  CHECK(ixs_bounds_add_assumption(&cached, pred));
  CHECK(ixs_node_transform_cache_lookup(
            ctx, shifted, IXS_NODE_TRANSFORM_ADD_WITHOUT_CONST) == base);
  ixs_arena_set_fail_after(&ctx->arena, IXS_ARENA_FAILURE_DISABLED);
  ixs_session_unbind(&binding);

  ixs_ctx_stats_reset(ctx);
  CHECK(ixs_node_transform_cache_lookup(
            ctx, shifted, IXS_NODE_TRANSFORM_ADD_WITHOUT_CONST) == NULL);
  ixs_ctx_destroy(ctx);
}
#endif

static void test_expand_associative_nodes(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *a = ixs_sym(ctx, "assoc_expand_a");
  ixs_node *b = ixs_sym(ctx, "assoc_expand_b");
  ixs_node *c = ixs_sym(ctx, "assoc_expand_c");
  ixs_node *x = ixs_sym(ctx, "assoc_expand_x");
  ixs_node *y = ixs_sym(ctx, "assoc_expand_y");
  ixs_node *z = ixs_sym(ctx, "assoc_expand_z");
  ixs_node *args[3];
  ixs_node *expanded[3];
  ixs_node *expr;
  ixs_node *expected;

  args[0] = ixs_mul(ctx, x, ixs_add(ctx, a, b));
  args[1] = ixs_mul(ctx, y, ixs_add(ctx, b, c));
  args[2] = ixs_mul(ctx, z, ixs_add(ctx, c, a));
  expanded[0] = ixs_expand(ctx, args[0]);
  expanded[1] = ixs_expand(ctx, args[1]);
  expanded[2] = ixs_expand(ctx, args[2]);

  expr = ixs_max_many(ctx, 3, args);
  expected = ixs_max_many(ctx, 3, expanded);
  CHECK(ixs_expand(ctx, expr) == expected);
  expr = ixs_min_many(ctx, 3, args);
  expected = ixs_min_many(ctx, 3, expanded);
  CHECK(ixs_expand(ctx, expr) == expected);
  expr = ixs_xor_many(ctx, 3, args);
  expected = ixs_xor_many(ctx, 3, expanded);
  CHECK(ixs_expand(ctx, expr) == expected);
  expr = ixs_and_many(ctx, 3, args);
  expected = ixs_and_many(ctx, 3, expanded);
  CHECK(ixs_expand(ctx, expr) == expected);
  expr = ixs_or_many(ctx, 3, args);
  expected = ixs_or_many(ctx, 3, expanded);
  CHECK(ixs_expand(ctx, expr) == expected);

  ixs_ctx_destroy(ctx);
}

int main(void) {
  test_expand_leaves();
  test_expand_add_noop();
  test_expand_const_times_add();
  test_expand_two_sums();
  test_expand_sym_times_add();
  test_expand_nested_add();
  test_expand_inside_floor();
  test_expand_inside_trunc();
  test_expand_already_expanded();
  test_expand_three_factors();
  test_expand_piecewise();
  test_expand_sentinel();
  test_expand_associative_nodes();
#ifndef IXS_TEST_AMALGAMATION
  test_expand_skips_dead_sentinel_branch();
  test_expand_cache();
  test_expand_cache_failure_semantics();
  test_expand_deep_iterative();
  test_expand_oom_retry();
  test_expand_cycle_rejected();
  test_simplify_signed_exponent_boundaries();
  test_add_without_const_cache();
#endif

  printf("test_expand: %d/%d passed\n", tests_passed, tests_run);
  return tests_passed == tests_run ? 0 : 1;
}
