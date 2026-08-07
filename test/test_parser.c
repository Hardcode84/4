/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include <ixsimpl.h>
#include <stdlib.h>
#include <string.h>

#include "test_check.h"

static char buf[4096];

static const char *pr(ixs_node *n) {
  ixs_print(n, buf, sizeof(buf));
  return buf;
}

static void test_integers(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *n;
  const char *printed;

  n = ixs_parse_expr(ctx, "42", 2);
  CHECK(n && !ixs_is_error(n));
  CHECK(ixs_node_tag(n) == IXS_INT && ixs_node_int_val(n) == 42);

  n = ixs_parse_expr(ctx, "0", 1);
  CHECK(n && ixs_node_int_val(n) == 0);

  n = ixs_parse_expr(ctx, "9223372036854775807", 19);
  CHECK(n && !ixs_is_error(n));
  CHECK(ixs_node_tag(n) == IXS_INT && ixs_node_int_val(n) == INT64_MAX);

  n = ixs_parse_expr(ctx, "-9223372036854775808", 20);
  CHECK(n && !ixs_is_error(n));
  CHECK(ixs_node_tag(n) == IXS_INT && ixs_node_int_val(n) == INT64_MIN);
  printed = pr(n);
  CHECK(ixs_parse_expr(ctx, printed, strlen(printed)) == n);

  n = ixs_parse_expr(ctx, "---9223372036854775808", 22);
  CHECK(n && !ixs_is_error(n));
  CHECK(ixs_node_tag(n) == IXS_INT && ixs_node_int_val(n) == INT64_MIN);

  ixs_ctx_clear_errors(ctx);
  n = ixs_parse_expr(ctx, "9223372036854775808", 19);
  CHECK(n && ixs_is_domain_error(n));
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "integer literal overflow") != NULL);

  ixs_ctx_clear_errors(ctx);
  n = ixs_parse_expr(ctx, "--9223372036854775808", 21);
  CHECK(n && ixs_is_domain_error(n));
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "integer literal overflow") != NULL);

  ixs_ctx_clear_errors(ctx);
  n = ixs_parse_expr(ctx, "-9223372036854775809", 20);
  CHECK(n && ixs_is_domain_error(n));
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "integer literal overflow") != NULL);

  ixs_ctx_destroy(ctx);
}

static void test_symbols(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *n;

  n = ixs_parse_expr(ctx, "$T0", 3);
  CHECK(n && !ixs_is_error(n));
  CHECK(ixs_node_tag(n) == IXS_SYM);
  CHECK(strcmp(pr(n), "$T0") == 0);

  n = ixs_parse_expr(ctx, "_M_div_32", 9);
  CHECK(n && strcmp(pr(n), "_M_div_32") == 0);

  ixs_ctx_destroy(ctx);
}

static void test_arithmetic(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *n;

  /* 3 + 4 → 7 */
  n = ixs_parse_expr(ctx, "3 + 4", 5);
  CHECK(n && ixs_node_tag(n) == IXS_INT && ixs_node_int_val(n) == 7);

  /* 3 * 4 → 12 */
  n = ixs_parse_expr(ctx, "3 * 4", 5);
  CHECK(n && ixs_node_int_val(n) == 12);

  /* 7 / 2 → 7/2 (rational) */
  n = ixs_parse_expr(ctx, "7/2", 3);
  CHECK(n && ixs_node_tag(n) == IXS_RAT);

  /* x + x → 2*x */
  n = ixs_parse_expr(ctx, "x + x", 5);
  CHECK(n && !ixs_is_error(n));

  /* 3*x + 2*x → 5*x */
  n = ixs_parse_expr(ctx, "3*x + 2*x", 9);
  CHECK(n && !ixs_is_error(n));
  CHECK(strcmp(pr(n), "5*x") == 0);

  ixs_ctx_destroy(ctx);
}

static void test_floor_ceil(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *n;

  /* floor(7/2) → 3 */
  n = ixs_parse_expr(ctx, "floor(7/2)", 10);
  CHECK(n && ixs_node_tag(n) == IXS_INT && ixs_node_int_val(n) == 3);

  /* ceiling(7/2) → 4 */
  n = ixs_parse_expr(ctx, "ceiling(7/2)", 12);
  CHECK(n && ixs_node_tag(n) == IXS_INT && ixs_node_int_val(n) == 4);

  /* floor(x) → x (x is integer-valued) */
  n = ixs_parse_expr(ctx, "floor(x)", 8);
  CHECK(n && ixs_node_tag(n) == IXS_SYM);

  /* floor(floor(x)) → x */
  n = ixs_parse_expr(ctx, "floor(floor(x))", 15);
  CHECK(n && ixs_node_tag(n) == IXS_SYM);

  n = ixs_parse_expr(ctx, "Trunc(7/3)", strlen("Trunc(7/3)"));
  CHECK(n && ixs_node_tag(n) == IXS_INT && ixs_node_int_val(n) == 2);

  n = ixs_parse_expr(ctx, "Trunc(-7/3)", strlen("Trunc(-7/3)"));
  CHECK(n && ixs_node_tag(n) == IXS_INT && ixs_node_int_val(n) == -2);

  n = ixs_parse_expr(ctx, "Trunc(x/3)", strlen("Trunc(x/3)"));
  CHECK(n && ixs_node_tag(n) == IXS_TRUNC);
  CHECK(strcmp(pr(n), "Trunc(1/3*x)") == 0);
  CHECK(ixs_parse_expr(ctx, pr(n), strlen(pr(n))) == n);

  ixs_ctx_clear_errors(ctx);
  n = ixs_parse_expr(ctx, "Trunc(x, y)", strlen("Trunc(x, y)"));
  CHECK(n && ixs_is_parse_error(n));

  ixs_ctx_destroy(ctx);
}

static void test_mod(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *n;

  /* Mod(17, 5) → 2 */
  n = ixs_parse_expr(ctx, "Mod(17, 5)", 10);
  CHECK(n && ixs_node_int_val(n) == 2);

  /* Mod(floor(x), 1) → 0 (only integer-valued args fold) */
  n = ixs_parse_expr(ctx, "Mod(floor(x), 1)", 16);
  CHECK(n && ixs_node_int_val(n) == 0);

  ixs_ctx_destroy(ctx);
}

static void test_max_min_xor(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *n;
  const char *printed;

  n = ixs_parse_expr(ctx, "Max(3, 7)", 9);
  CHECK(n && ixs_node_int_val(n) == 7);

  n = ixs_parse_expr(ctx, "Min(3, 7)", 9);
  CHECK(n && ixs_node_int_val(n) == 3);

  n = ixs_parse_expr(ctx, "xor(5, 3)", 9);
  CHECK(n && ixs_node_int_val(n) == 6);

  n = ixs_parse_expr(ctx, "xor(x, x)", 9);
  CHECK(n && ixs_node_int_val(n) == 0);

  n = ixs_parse_expr(ctx, "xor(-9223372036854775808, 0)", 28);
  CHECK(n && !ixs_is_error(n));
  CHECK(ixs_node_tag(n) == IXS_INT && ixs_node_int_val(n) == INT64_MIN);

  n = ixs_parse_expr(ctx, "Max(x, y, z)", 12);
  CHECK(n && ixs_node_tag(n) == IXS_MAX);
  CHECK(ixs_node_assoc_nargs(n) == 3);
  printed = pr(n);
  CHECK(ixs_parse_expr(ctx, printed, strlen(printed)) == n);

  n = ixs_parse_expr(ctx, "Min(z, x, y)", 12);
  CHECK(n && ixs_node_tag(n) == IXS_MIN);
  CHECK(ixs_node_assoc_nargs(n) == 3);

  n = ixs_parse_expr(ctx, "xor(x, y, z)", 12);
  CHECK(n && ixs_node_tag(n) == IXS_XOR);
  CHECK(ixs_node_assoc_nargs(n) == 3);

  n = ixs_parse_expr(ctx, "x & y & z", 9);
  CHECK(n && ixs_node_tag(n) == IXS_AND);
  CHECK(ixs_node_assoc_nargs(n) == 3);

  n = ixs_parse_expr(ctx, "z | y | x", 9);
  CHECK(n && ixs_node_tag(n) == IXS_OR);
  CHECK(ixs_node_assoc_nargs(n) == 3);

  n = ixs_parse_expr(ctx, "Max(x)", 6);
  CHECK(n && ixs_node_tag(n) == IXS_SYM);
  n = ixs_parse_expr(ctx, "xor(x)", 6);
  CHECK(n && ixs_is_parse_error(n));
  ixs_ctx_clear_errors(ctx);

  ixs_ctx_destroy(ctx);
}

static void test_piecewise(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *n;

  /* Single True branch → value */
  n = ixs_parse_expr(ctx, "Piecewise((42, True))", 21);
  CHECK(n && ixs_node_int_val(n) == 42);

  /* False branch dropped */
  n = ixs_parse_expr(ctx, "Piecewise((1, False), (2, True))", 32);
  CHECK(n && ixs_node_int_val(n) == 2);

  ixs_ctx_destroy(ctx);
}

static void test_comparisons(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *n;

  n = ixs_parse_expr(ctx, "Piecewise((1, 3 > 2), (0, True))", 32);
  CHECK(n && ixs_node_int_val(n) == 1);

  n = ixs_parse_expr(ctx, "Piecewise((1, 1 > 2), (0, True))", 32);
  CHECK(n && ixs_node_int_val(n) == 0);

  ixs_ctx_destroy(ctx);
}

static void test_bitwise_condition_roundtrip(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *expr_node;
  ixs_node *and_node;
  ixs_node *or_node;
  ixs_node *cmp_node;
  ixs_node *roundtrip;
  const char *printed;

  expr_node = ixs_parse_expr(ctx, "x & 3", 5);
  CHECK(expr_node && !ixs_is_error(expr_node));
  CHECK(ixs_node_tag(expr_node) == IXS_AND);
  CHECK(ixs_node_assoc_nargs(expr_node) == 2);
  CHECK(!ixs_node_is_pred(expr_node));
  printed = pr(expr_node);
  roundtrip = ixs_parse_expr(ctx, printed, strlen(printed));
  CHECK(roundtrip && !ixs_is_error(roundtrip));
  CHECK(ixs_same_node(expr_node, roundtrip));

  expr_node = ixs_parse_expr(ctx, "x | y", 5);
  CHECK(expr_node && !ixs_is_error(expr_node));
  CHECK(ixs_node_tag(expr_node) == IXS_OR);
  CHECK(ixs_node_assoc_nargs(expr_node) == 2);
  CHECK(!ixs_node_is_pred(expr_node));
  printed = pr(expr_node);
  roundtrip = ixs_parse_expr(ctx, printed, strlen(printed));
  CHECK(roundtrip && !ixs_is_error(roundtrip));
  CHECK(ixs_same_node(expr_node, roundtrip));

  expr_node = ixs_parse_expr(ctx, "1 | x & 3", 9);
  CHECK(expr_node && !ixs_is_error(expr_node));
  CHECK(ixs_node_tag(expr_node) == IXS_OR);
  CHECK(ixs_node_tag(ixs_node_assoc_arg(expr_node, 0)) == IXS_AND ||
        ixs_node_tag(ixs_node_assoc_arg(expr_node, 1)) == IXS_AND);
  printed = pr(expr_node);
  roundtrip = ixs_parse_expr(ctx, printed, strlen(printed));
  CHECK(roundtrip && !ixs_is_error(roundtrip));
  CHECK(ixs_same_node(expr_node, roundtrip));

  cmp_node = ixs_parse_pred(ctx, "x & 3 == 1", 10);
  CHECK(cmp_node && !ixs_is_error(cmp_node));
  CHECK(ixs_node_tag(cmp_node) == IXS_CMP);
  CHECK(ixs_node_is_pred(cmp_node));
  CHECK(strcmp(pr(cmp_node), "-1 + (3 & x) == 0") == 0);

  printed = pr(cmp_node);
  roundtrip = ixs_parse_pred(ctx, printed, strlen(printed));
  CHECK(roundtrip && !ixs_is_error(roundtrip));
  CHECK(ixs_same_node(cmp_node, roundtrip));

  cmp_node = ixs_parse_pred(ctx, "(x & 3) == 1", 12);
  CHECK(cmp_node && !ixs_is_error(cmp_node));
  CHECK(ixs_node_tag(cmp_node) == IXS_CMP);
  CHECK(ixs_node_is_pred(cmp_node));
  CHECK(strcmp(pr(cmp_node), "-1 + (3 & x) == 0") == 0);

  cmp_node = ixs_parse_pred(ctx, "(x | y) == 0", 12);
  CHECK(cmp_node && !ixs_is_error(cmp_node));
  CHECK(ixs_node_tag(cmp_node) == IXS_CMP);
  CHECK(ixs_node_is_pred(cmp_node));
  CHECK(ixs_node_tag(ixs_node_binary_lhs(cmp_node)) == IXS_OR);
  CHECK(strcmp(pr(cmp_node), "(x | y) == 0") == 0);

  printed = pr(cmp_node);
  roundtrip = ixs_parse_pred(ctx, printed, strlen(printed));
  CHECK(roundtrip && !ixs_is_error(roundtrip));
  CHECK(ixs_same_node(cmp_node, roundtrip));

  and_node = ixs_parse_pred(ctx, "x & y", 5);
  CHECK(and_node && !ixs_is_error(and_node));
  CHECK(ixs_node_tag(and_node) == IXS_AND);
  CHECK(ixs_node_assoc_nargs(and_node) == 2);
  CHECK(ixs_node_is_pred(and_node));
  CHECK(strcmp(pr(and_node), "x != 0 & y != 0") == 0);

  printed = pr(and_node);
  roundtrip = ixs_parse_pred(ctx, printed, strlen(printed));
  CHECK(roundtrip && !ixs_is_error(roundtrip));
  CHECK(ixs_same_node(and_node, roundtrip));

  and_node = ixs_parse_pred(ctx, "x & y == 0", 10);
  CHECK(and_node && !ixs_is_error(and_node));
  CHECK(ixs_node_tag(and_node) == IXS_AND);
  CHECK(ixs_node_assoc_nargs(and_node) == 2);
  CHECK(ixs_node_is_pred(and_node));
  CHECK(strcmp(pr(and_node), "y == 0 & x != 0") == 0);

  or_node = ixs_parse_pred(ctx, "x | y == 0", 10);
  CHECK(or_node && !ixs_is_error(or_node));
  CHECK(ixs_node_tag(or_node) == IXS_OR);
  CHECK(ixs_node_assoc_nargs(or_node) == 2);
  CHECK(ixs_node_is_pred(or_node));
  CHECK(strcmp(pr(or_node), "y == 0 | x != 0") == 0);

  or_node = ixs_parse_pred(ctx, "x > 0 | y > 0", 13);
  CHECK(or_node && !ixs_is_error(or_node));
  CHECK(ixs_node_tag(or_node) == IXS_OR);
  CHECK(ixs_node_assoc_nargs(or_node) == 2);
  CHECK(ixs_node_is_pred(or_node));
  CHECK(strcmp(pr(or_node), "x > 0 | y > 0") == 0);

  or_node = ixs_parse_pred(ctx, "(x > 0) | (y > 0)", 17);
  CHECK(or_node && !ixs_is_error(or_node));
  CHECK(ixs_node_tag(or_node) == IXS_OR);
  CHECK(ixs_node_assoc_nargs(or_node) == 2);
  CHECK(ixs_node_is_pred(or_node));
  CHECK(strcmp(pr(or_node), "x > 0 | y > 0") == 0);

  printed = pr(or_node);
  roundtrip = ixs_parse_pred(ctx, printed, strlen(printed));
  CHECK(roundtrip && !ixs_is_error(roundtrip));
  CHECK(ixs_same_node(or_node, roundtrip));

  ixs_ctx_destroy(ctx);
}

static void test_kind_parsers_and_predicates(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *expr;
  ixs_node *pred;
  ixs_node *legacy;
  ixs_node *err;
  ixs_node *domain;

  expr = ixs_parse_expr(ctx, "x + 1", 5);
  CHECK(expr && !ixs_is_error(expr));
  CHECK(ixs_node_is_expr(expr));
  CHECK(!ixs_node_is_pred(expr));

  pred = ixs_parse_pred(ctx, "x > 0", 5);
  CHECK(pred && !ixs_is_error(pred));
  CHECK(ixs_node_is_pred(pred));
  CHECK(ixs_node_is_expr(pred));

  err = ixs_parse_pred(ctx, "x + 1", 5);
  CHECK(err && ixs_is_parse_error(err));
  CHECK(ixs_ctx_nerrors(ctx) > 0);
  CHECK(strstr(ixs_ctx_error(ctx, ixs_ctx_nerrors(ctx) - 1),
               "expected predicate, got expression") != NULL);
  ixs_ctx_clear_errors(ctx);

  err = ixs_parse_expr(ctx, "x > 0", 5);
  CHECK(err && ixs_is_parse_error(err));
  CHECK(ixs_ctx_nerrors(ctx) > 0);
  CHECK(strstr(ixs_ctx_error(ctx, ixs_ctx_nerrors(ctx) - 1),
               "expected expression, got predicate") != NULL);
  ixs_ctx_clear_errors(ctx);

  legacy = ixs_parse(ctx, "x > 0", 5);
  CHECK(legacy && ixs_is_parse_error(legacy));
  CHECK(ixs_ctx_nerrors(ctx) > 0);
  CHECK(strstr(ixs_ctx_error(ctx, ixs_ctx_nerrors(ctx) - 1),
               "expected expression, got predicate") != NULL);
  ixs_ctx_clear_errors(ctx);

  expr = ixs_parse_expr(ctx, "True", 4);
  CHECK(expr && !ixs_is_error(expr));
  CHECK(ixs_node_tag(expr) == IXS_INT && ixs_node_int_val(expr) == 1);
  CHECK(ixs_node_is_expr(expr));
  CHECK(ixs_node_is_pred(expr));

  err = ixs_parse_pred(ctx, "x", 1);
  CHECK(err && ixs_is_parse_error(err));
  CHECK(ixs_ctx_nerrors(ctx) > 0);
  CHECK(strstr(ixs_ctx_error(ctx, ixs_ctx_nerrors(ctx) - 1),
               "expected predicate, got expression") != NULL);
  ixs_ctx_clear_errors(ctx);

  domain = ixs_parse_expr(ctx, "x > 1/0", 7);
  CHECK(domain && ixs_is_domain_error(domain));
  CHECK(ixs_ctx_nerrors(ctx) > 0);
  CHECK(strstr(ixs_ctx_error(ctx, ixs_ctx_nerrors(ctx) - 1),
               "division by zero") != NULL);
  ixs_ctx_clear_errors(ctx);

  legacy = ixs_parse(ctx, "x > 1/0", 7);
  CHECK(legacy && ixs_is_domain_error(legacy));
  CHECK(ixs_ctx_nerrors(ctx) > 0);
  CHECK(strstr(ixs_ctx_error(ctx, ixs_ctx_nerrors(ctx) - 1),
               "division by zero") != NULL);
  ixs_ctx_clear_errors(ctx);

  CHECK(ixs_node_is_pred(ixs_true(ctx)));
  CHECK(ixs_node_is_pred(ixs_false(ctx)));
  CHECK(ixs_node_is_expr(ixs_true(ctx)));
  CHECK(ixs_node_tag(ixs_true(ctx)) == IXS_INT);
  CHECK(ixs_node_tag(ixs_false(ctx)) == IXS_INT);

  err = ixs_parse_expr(ctx, "???", 3);
  domain = ixs_parse_expr(ctx, "1/0", 3);
  CHECK(err && ixs_is_parse_error(err));
  CHECK(domain && ixs_is_domain_error(domain));
  CHECK(!ixs_node_is_expr(err));
  CHECK(!ixs_node_is_pred(err));
  CHECK(!ixs_node_is_expr(domain));
  CHECK(!ixs_node_is_pred(domain));

  ixs_ctx_destroy(ctx);
}

static void test_errors(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *n;

  /* Division by zero */
  n = ixs_parse_expr(ctx, "1/0", 3);
  CHECK(n && ixs_is_domain_error(n));
  CHECK(ixs_ctx_nerrors(ctx) > 0);
  ixs_ctx_clear_errors(ctx);

  /* Mod by zero */
  n = ixs_parse_expr(ctx, "Mod(x, 0)", 9);
  CHECK(n && ixs_is_domain_error(n));
  ixs_ctx_clear_errors(ctx);

  /* Mod requires a positive divisor. */
  n = ixs_parse_expr(ctx, "Mod(x, -3)", 10);
  CHECK(n && ixs_is_domain_error(n));
  CHECK(strstr(ixs_ctx_error(ctx, ixs_ctx_nerrors(ctx) - 1), "negative") !=
        NULL);
  ixs_ctx_clear_errors(ctx);

  n = ixs_parse_expr(ctx, "Mod(x, -1/2)", 12);
  CHECK(n && ixs_is_domain_error(n));
  ixs_ctx_clear_errors(ctx);

  n = ixs_parse_expr(ctx, "Mod(x, m)", 9);
  CHECK(n && !ixs_is_error(n) && ixs_node_tag(n) == IXS_MOD);

  n = ixs_parse_expr(ctx, "floor(Mod(x, 0))", strlen("floor(Mod(x, 0))"));
  CHECK(n && ixs_is_domain_error(n));
  ixs_ctx_clear_errors(ctx);

  n = ixs_parse_expr(ctx, "Max(Mod(x, 0), y)", strlen("Max(Mod(x, 0), y)"));
  CHECK(n && ixs_is_domain_error(n));
  ixs_ctx_clear_errors(ctx);

  n = ixs_parse_expr(ctx, "Min(x, Mod(y, 0), z)",
                     strlen("Min(x, Mod(y, 0), z)"));
  CHECK(n && ixs_is_domain_error(n));
  ixs_ctx_clear_errors(ctx);

  n = ixs_parse_expr(ctx, "xor(x, Mod(y, 0), z)",
                     strlen("xor(x, Mod(y, 0), z)"));
  CHECK(n && ixs_is_domain_error(n));
  ixs_ctx_clear_errors(ctx);

  n = ixs_parse_expr(ctx, "x & Mod(y, 0) & z", strlen("x & Mod(y, 0) & z"));
  CHECK(n && ixs_is_domain_error(n));
  ixs_ctx_clear_errors(ctx);

  n = ixs_parse_expr(ctx, "x | Mod(y, 0) | z", strlen("x | Mod(y, 0) | z"));
  CHECK(n && ixs_is_domain_error(n));
  ixs_ctx_clear_errors(ctx);

  n = ixs_parse_pred(ctx, "x > 0 & Mod(y, 0) > 0 | z > 0",
                     strlen("x > 0 & Mod(y, 0) > 0 | z > 0"));
  CHECK(n && ixs_is_domain_error(n));
  ixs_ctx_clear_errors(ctx);

  n = ixs_parse_expr(ctx, "Max(Mod(x, 0),)", strlen("Max(Mod(x, 0),)"));
  CHECK(n && ixs_is_parse_error(n));
  ixs_ctx_clear_errors(ctx);

  /* Parse error: trailing chars */
  n = ixs_parse_expr(ctx, "x y", 3);
  CHECK(n && ixs_is_parse_error(n));
  ixs_ctx_clear_errors(ctx);

  ixs_ctx_destroy(ctx);
}

static void test_complex_expr(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *n;

  const char *expr = "128*floor($T0/64) + 4*floor(Mod($T0, 64)/16)";
  n = ixs_parse_expr(ctx, expr, strlen(expr));
  CHECK(n && !ixs_is_error(n));

  ixs_ctx_destroy(ctx);
}

static void test_signed_wrap64_roundtrip(void) {
  static const char input[] =
      "-9223372036854775808 + Mod(4+x,4294967296) + "
      "4294967296*Mod(2147483648+floor((4+x)/4294967296),4294967296)";
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *expr = ixs_parse_expr(ctx, input, strlen(input));
  ixs_node *roundtrip;
  char printed[4096];

  CHECK(expr && !ixs_is_error(expr));
  CHECK(ixs_ctx_nerrors(ctx) == 0);
  CHECK(ixs_print(expr, printed, sizeof(printed)) < sizeof(printed));
  roundtrip = ixs_parse_expr(ctx, printed, strlen(printed));
  CHECK(roundtrip && !ixs_is_error(roundtrip));
  CHECK(ixs_same_node(expr, roundtrip));
  CHECK(ixs_ctx_nerrors(ctx) == 0);

  ixs_ctx_destroy(ctx);
}

static void test_negation(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *n;

  n = ixs_parse_expr(ctx, "-x", 2);
  CHECK(n && !ixs_is_error(n));
  CHECK(strcmp(pr(n), "-x") == 0);

  n = ixs_parse_expr(ctx, "-(x + y)", 8);
  CHECK(n && !ixs_is_error(n));

  ixs_ctx_destroy(ctx);
}

static char *nested_input(size_t depth, const char *leaf) {
  size_t leaf_len = strlen(leaf);
  char *text = malloc(depth * 2u + leaf_len + 1u);
  size_t i;
  if (!text)
    return NULL;
  for (i = 0; i < depth; i++)
    text[i] = '(';
  memcpy(text + depth, leaf, leaf_len);
  for (i = 0; i < depth; i++)
    text[depth + leaf_len + i] = ')';
  text[depth * 2u + leaf_len] = '\0';
  return text;
}

static void test_depth_limit_covers_signed_and_condition_parens(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  char *text = nested_input(255, "-1");
  ixs_node *n;

  CHECK(ctx != NULL && text != NULL);
  if (!ctx || !text) {
    free(text);
    ixs_ctx_destroy(ctx);
    return;
  }
  n = ixs_parse_expr(ctx, text, strlen(text));
  CHECK(n && !ixs_is_error(n));
  free(text);

  text = nested_input(256, "-1");
  CHECK(text != NULL);
  if (text) {
    n = ixs_parse_expr(ctx, text, strlen(text));
    CHECK(n && ixs_is_parse_error(n));
    free(text);
    ixs_ctx_clear_errors(ctx);
  }

  text = nested_input(257, "True");
  CHECK(text != NULL);
  if (text) {
    n = ixs_parse_pred(ctx, text, strlen(text));
    CHECK(n && ixs_is_parse_error(n));
    free(text);
  }
  ixs_ctx_destroy(ctx);
}

int main(void) {
  test_integers();
  test_symbols();
  test_arithmetic();
  test_floor_ceil();
  test_mod();
  test_max_min_xor();
  test_piecewise();
  test_comparisons();
  test_bitwise_condition_roundtrip();
  test_kind_parsers_and_predicates();
  test_errors();
  test_complex_expr();
  test_signed_wrap64_roundtrip();
  test_negation();
  test_depth_limit_covers_signed_and_condition_parens();

  printf("test_parser: %d/%d passed\n", tests_passed, tests_run);
  return tests_passed == tests_run ? 0 : 1;
}
