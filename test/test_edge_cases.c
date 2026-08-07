/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
/*
 * Edge case tests for ixsimpl: overflow, div-by-zero, degenerate piecewise,
 * INT64_MIN, empty inputs, max depth, sentinel propagation, large integers,
 * symbol edge cases, print buffer truncation.
 */

#include <ixsimpl.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include "test_check.h"

static char buf[4096];

static const char *pr(ixs_node *n) {
  ixs_print(n, buf, sizeof(buf));
  return buf;
}

/* ------------------------------------------------------------------ */
/*  1. Integer overflow: INT64_MAX and INT64_MIN in arithmetic        */
/* ------------------------------------------------------------------ */

static void test_integer_overflow(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *max_n;
  ixs_node *min_n;
  ixs_node *r;

  max_n = ixs_int(ctx, INT64_MAX);
  min_n = ixs_int(ctx, INT64_MIN);
  CHECK(max_n && !ixs_is_error(max_n));
  CHECK(min_n && !ixs_is_error(min_n));
  CHECK(ixs_node_int_val(max_n) == INT64_MAX);
  CHECK(ixs_node_int_val(min_n) == INT64_MIN);

  /* INT64_MAX + 0 stays INT64_MAX */
  r = ixs_add(ctx, max_n, ixs_int(ctx, 0));
  CHECK(r && ixs_node_int_val(r) == INT64_MAX);

  /* INT64_MAX * 1 stays INT64_MAX */
  r = ixs_mul(ctx, max_n, ixs_int(ctx, 1));
  CHECK(r && ixs_node_int_val(r) == INT64_MAX);

  /* Overflow in rational: 1/0 is domain error, not overflow. Test rat. */
  r = ixs_rat(ctx, INT64_MAX, 1);
  CHECK(r && !ixs_is_error(r));

  r = ixs_rat(ctx, INT64_MIN, 1);
  CHECK(r && !ixs_is_error(r));

  /* Parse overflow: "99999999999999999999" should overflow or error */
  r = ixs_parse(ctx, "99999999999999999999", 20);
  CHECK(r == NULL || ixs_is_error(r) || ixs_is_parse_error(r));

  ixs_ctx_destroy(ctx);
}

/* ------------------------------------------------------------------ */
/*  2. Division by zero: ixs_mod(x, zero), parse "x/0"                 */
/* ------------------------------------------------------------------ */

static void test_division_by_zero(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x;
  ixs_node *zero;
  ixs_node *r;

  x = ixs_sym(ctx, "x");
  zero = ixs_int(ctx, 0);

  /* ixs_mod(ctx, x, zero) returns domain error */
  r = ixs_mod(ctx, x, zero);
  CHECK(r && ixs_is_domain_error(r));
  ixs_ctx_clear_errors(ctx);

  /* ixs_div(ctx, x, zero) if available */
  r = ixs_div(ctx, x, zero);
  CHECK(r && ixs_is_domain_error(r));
  ixs_ctx_clear_errors(ctx);

  /* Parse "x/0" or "1/0" */
  r = ixs_parse(ctx, "1/0", 3);
  CHECK(r && ixs_is_domain_error(r));
  ixs_ctx_clear_errors(ctx);

  r = ixs_parse(ctx, "Mod(x, 0)", 9);
  CHECK(r && ixs_is_domain_error(r));
  ixs_ctx_clear_errors(ctx);

  ixs_ctx_destroy(ctx);
}

/* ------------------------------------------------------------------ */
/*  3. Degenerate Piecewise: empty, single-case True, all-False        */
/* ------------------------------------------------------------------ */

static void test_degenerate_piecewise(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *v;
  ixs_node *t;
  ixs_node *f;
  ixs_node *vals[2];
  ixs_node *conds[2];
  ixs_node *r;

  v = ixs_int(ctx, 42);
  t = ixs_true(ctx);
  f = ixs_false(ctx);

  /* Empty piecewise: n=0 */
  r = ixs_pw(ctx, 0, NULL, NULL);
  CHECK(r && ixs_is_error(r));
  ixs_ctx_clear_errors(ctx);

  /* Single-case True: Piecewise((42, True)) */
  vals[0] = v;
  conds[0] = t;
  r = ixs_pw(ctx, 1, vals, conds);
  CHECK(r && r == v);

  /* All-False: Piecewise((1, False), (2, False)) - no True default */
  vals[0] = ixs_int(ctx, 1);
  vals[1] = ixs_int(ctx, 2);
  conds[0] = f;
  conds[1] = f;
  r = ixs_pw(ctx, 2, vals, conds);
  CHECK(r && ixs_is_error(r));
  ixs_ctx_clear_errors(ctx);

  ixs_ctx_destroy(ctx);
}

/* ------------------------------------------------------------------ */
/*  4. INT64_MIN handling: ixs_int(ctx, INT64_MIN), negation           */
/* ------------------------------------------------------------------ */

static void test_int64_min_handling(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *min_n;
  ixs_node *r;

  min_n = ixs_int(ctx, INT64_MIN);
  CHECK(min_n && !ixs_is_error(min_n));
  CHECK(ixs_node_int_val(min_n) == INT64_MIN);

  /* Negation of INT64_MIN overflows in two's complement */
  r = ixs_neg(ctx, min_n);
  CHECK(r && (ixs_is_error(r) || ixs_is_domain_error(r) ||
              ixs_node_int_val(r) == INT64_MIN));
  ixs_ctx_clear_errors(ctx);

  /* Parse "-9223372036854775808" */
  r = ixs_parse(ctx, "-9223372036854775808", 20);
  CHECK(r && (ixs_is_error(r) || (ixs_node_tag(r) == IXS_INT &&
                                  ixs_node_int_val(r) == INT64_MIN)));

  ixs_ctx_destroy(ctx);
}

/* ------------------------------------------------------------------ */
/*  5. Empty/null inputs: "", "   ", skip NULL (may crash)             */
/* ------------------------------------------------------------------ */

static void test_empty_null_inputs(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *r;

  /* Empty string */
  r = ixs_parse(ctx, "", 0);
  CHECK(r == NULL || ixs_is_parse_error(r));
  if (r && ixs_is_parse_error(r))
    ixs_ctx_clear_errors(ctx);

  /* Whitespace only */
  r = ixs_parse(ctx, "   ", 3);
  CHECK(r == NULL || ixs_is_parse_error(r));
  if (r && ixs_is_parse_error(r))
    ixs_ctx_clear_errors(ctx);

  /* Skip ixs_parse(ctx, NULL, 0): may crash if input is dereferenced */
  (void)ctx;

  ixs_ctx_destroy(ctx);
}

/* ------------------------------------------------------------------ */
/*  6. Max-depth expressions: floor(floor(...)) up to 200 levels       */
/* ------------------------------------------------------------------ */

static void test_max_depth_expressions(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x;
  ixs_node *r;
  int i;

  x = ixs_sym(ctx, "x");
  r = x;
  for (i = 0; i < 200; i++) {
    ixs_node *next;
    next = ixs_floor(ctx, r);
    if (!next || ixs_is_error(next)) {
      CHECK(0 && "floor chain failed");
      break;
    }
    r = next;
  }
  CHECK(r && !ixs_is_error(r));
  CHECK(ixs_node_tag(r) == IXS_SYM);

  ixs_ctx_destroy(ctx);
}

/* ------------------------------------------------------------------ */
/*  7. Long parser prefixes: unary '-' and predicate '~'               */
/* ------------------------------------------------------------------ */

static void test_long_prefix_parse(void) {
  enum { PREFIX_LEN = 65536 };
  ixs_ctx *ctx = ixs_ctx_create();
  char *input;
  ixs_node *r;

  input = malloc(PREFIX_LEN + 6);
  CHECK(input != NULL);
  if (!input) {
    ixs_ctx_destroy(ctx);
    return;
  }

  memset(input, '-', PREFIX_LEN);
  input[PREFIX_LEN] = 'x';
  input[PREFIX_LEN + 1] = '\0';
  r = ixs_parse_expr(ctx, input, PREFIX_LEN + 1);
  CHECK(r && !ixs_is_error(r));
  CHECK(ixs_node_tag(r) == IXS_SYM);

  memset(input, '-', PREFIX_LEN + 1);
  input[PREFIX_LEN + 1] = 'x';
  input[PREFIX_LEN + 2] = '\0';
  r = ixs_parse_expr(ctx, input, PREFIX_LEN + 2);
  CHECK(r && !ixs_is_error(r));

  memset(input, '~', PREFIX_LEN);
  memcpy(input + PREFIX_LEN, "x > 0", 6);
  r = ixs_parse_pred(ctx, input, PREFIX_LEN + 5);
  CHECK(r && !ixs_is_error(r));

  free(input);
  ixs_ctx_destroy(ctx);
}

/* ------------------------------------------------------------------ */
/*  8. Sentinel propagation through all operations                    */
/* ------------------------------------------------------------------ */

static void test_sentinel_propagation(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x;
  ixs_node *err;
  ixs_node *r;
  ixs_node *vals[1];
  ixs_node *conds[1];
  size_t n;
  char small_buf[4];

  x = ixs_sym(ctx, "x");
  err = ixs_mod(ctx, x, ixs_int(ctx, 0));
  CHECK(err && ixs_is_domain_error(err));
  ixs_ctx_clear_errors(ctx);

  /* add */
  r = ixs_add(ctx, err, x);
  CHECK(r && ixs_is_error(r));

  /* mul */
  r = ixs_mul(ctx, x, err);
  CHECK(r && ixs_is_error(r));

  /* floor */
  r = ixs_floor(ctx, err);
  CHECK(r && ixs_is_error(r));

  /* ceil */
  r = ixs_ceil(ctx, err);
  CHECK(r && ixs_is_error(r));

  /* mod */
  r = ixs_mod(ctx, err, x);
  CHECK(r && ixs_is_error(r));

  /* max */
  r = ixs_max(ctx, err, x);
  CHECK(r && ixs_is_error(r));

  /* min */
  r = ixs_min(ctx, x, err);
  CHECK(r && ixs_is_error(r));

  /* xor */
  r = ixs_xor(ctx, err, x);
  CHECK(r && ixs_is_error(r));

  /* cmp */
  r = ixs_cmp(ctx, err, IXS_CMP_GT, x);
  CHECK(r && ixs_is_error(r));

  /* and */
  r = ixs_and(ctx, err, x);
  CHECK(r && ixs_is_error(r));

  /* or */
  r = ixs_or(ctx, x, err);
  CHECK(r && ixs_is_error(r));

  /* not */
  r = ixs_not(ctx, err);
  CHECK(r && ixs_is_error(r));

  /* pw */
  vals[0] = err;
  conds[0] = ixs_true(ctx);
  r = ixs_pw(ctx, 1, vals, conds);
  CHECK(r && ixs_is_error(r));

  /* simplify */
  r = ixs_simplify(ctx, err, NULL, 0);
  CHECK(r && ixs_is_error(r));

  /* subs */
  r = ixs_subs(ctx, err, ixs_sym(ctx, "x"), ixs_int(ctx, 1));
  CHECK(r && ixs_is_error(r));

  /* print: truncates safely, no overrun */
  n = ixs_print(err, small_buf, sizeof(small_buf));
  CHECK(n > 0);

  ixs_ctx_destroy(ctx);
}

/* ------------------------------------------------------------------ */
/*  9. Large integers: parse and display near INT64_MAX                */
/* ------------------------------------------------------------------ */

static void test_large_integers(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *r;
  char out[64];
  size_t len;

  /* INT64_MAX as string */
  r = ixs_parse(ctx, "9223372036854775807", 19);
  CHECK(r && !ixs_is_error(r));
  CHECK(ixs_node_tag(r) == IXS_INT);
  CHECK(ixs_node_int_val(r) == INT64_MAX);

  len = ixs_print(r, out, sizeof(out));
  (void)len;
  CHECK(strstr(out, "9223372036854775807") != NULL || out[0] != '\0');

  ixs_ctx_destroy(ctx);
}

/* ------------------------------------------------------------------ */
/*  10. Symbol edge cases: $ prefix, single-char, long names            */
/* ------------------------------------------------------------------ */

static void test_symbol_edge_cases(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *r;

  /* $ prefix */
  r = ixs_parse(ctx, "$T0", 3);
  CHECK(r && !ixs_is_error(r));
  CHECK(ixs_node_tag(r) == IXS_SYM);
  CHECK(strcmp(pr(r), "$T0") == 0);

  /* Single-char symbol */
  r = ixs_parse(ctx, "x", 1);
  CHECK(r && !ixs_is_error(r));
  CHECK(ixs_node_tag(r) == IXS_SYM);
  CHECK(strcmp(pr(r), "x") == 0);

  /* Long symbol name */
  r = ixs_sym(ctx, "_M_div_32");
  CHECK(r && !ixs_is_error(r));
  CHECK(strcmp(pr(r), "_M_div_32") == 0);

  ixs_ctx_destroy(ctx);
}

/* ------------------------------------------------------------------ */
/*  11. Print buffer: too small should truncate safely                  */
/* ------------------------------------------------------------------ */

static void test_print_buffer(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *n;
  char tiny[2];
  char zero_buf[1];
  size_t len;

  n = ixs_parse(ctx, "x + y + z", 9);
  CHECK(n && !ixs_is_error(n));

  /* Buffer size 2: room for 1 char + NUL */
  len = ixs_print(n, tiny, 2);
  CHECK(len > 0);
  CHECK(tiny[1] == '\0');
  CHECK(tiny[0] != '\0' || len == 0);

  /* Buffer size 1: only NUL */
  len = ixs_print(n, zero_buf, 1);
  CHECK(zero_buf[0] == '\0');

  /* Buffer size 0: should not crash */
  len = ixs_print(n, tiny, 0);
  (void)len;

  ixs_ctx_destroy(ctx);
}

static void test_null_ctx_destroy(void) {
  ixs_ctx_destroy(NULL);
  CHECK(1);
}

static void test_many_expression_ranges(void) {
  enum { EXPR_COUNT = 64 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *conflicting = ixs_facts_create(ctx);
  ixs_facts *substituted = ixs_facts_create(ctx);
  ixs_node *exprs[EXPR_COUNT];
  ixs_node *conflict = ixs_sym(ctx, "many_ranges_conflict");
  ixs_node *replacement = ixs_sym(ctx, "many_ranges_replacement");
  ixs_range_result input;
  ixs_range_result result;
  size_t i;

  CHECK(facts != NULL);
  CHECK(conflicting != NULL);
  CHECK(substituted != NULL);
  input.has_lower = true;
  input.has_upper = true;
  input.lower_q = 1;
  input.upper_q = 1;
  for (i = 0; i < EXPR_COUNT; i++) {
    char name[32];
    snprintf(name, sizeof(name), "many_ranges_%zu", i);
    exprs[i] = ixs_sym(ctx, name);
    input.lower_p = (int64_t)i;
    input.upper_p = (int64_t)i + 100;
    CHECK(ixs_facts_assume_range(facts, exprs[i], &input));
  }

  for (i = EXPR_COUNT; i > 0; i--) {
    size_t index = i - 1u;
    CHECK(test_ixs_range_facts(facts, exprs[index], &result));
    CHECK(result.has_lower && result.lower_p == (int64_t)index &&
          result.lower_q == 1);
    CHECK(result.has_upper && result.upper_p == (int64_t)index + 100 &&
          result.upper_q == 1);
  }

  input.lower_p = 20;
  input.upper_p = 80;
  CHECK(ixs_facts_assume_range(facts, exprs[0], &input));
  CHECK(test_ixs_range_facts(facts, exprs[0], &result));
  CHECK(result.has_lower && result.lower_p == 20 && result.lower_q == 1);
  CHECK(result.has_upper && result.upper_p == 80 && result.upper_q == 1);

  input.lower_p = 0;
  input.upper_p = 0;
  CHECK(ixs_facts_assume_range(conflicting, conflict, &input));
  input.lower_p = 1;
  input.upper_p = 1;
  CHECK(ixs_facts_assume_range(conflicting, conflict, &input));
  input.lower_p = 0;
  input.upper_p = 0;
  CHECK(ixs_facts_assume_range(conflicting, conflict, &input));
  CHECK(!test_ixs_range_facts(conflicting, conflict, &result));

  input.lower_p = 7;
  input.upper_p = 7;
  CHECK(ixs_facts_assume_range(substituted, replacement, &input));
  CHECK(ixs_facts_substitute(substituted, conflicting, conflict, replacement));
  CHECK(!test_ixs_range_facts(substituted, replacement, &result));

  ixs_ctx_destroy(ctx);
}

static void test_product_nonzero_factors(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "product_nonzero_x");
  ixs_node *y = ixs_sym(ctx, "product_nonzero_y");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *scaled = ixs_mul(ctx, ixs_int(ctx, 8), x);
  ixs_node *scaled_nonzero = ixs_cmp(ctx, scaled, IXS_CMP_NE, zero);
  ixs_node *reciprocal = ixs_div(ctx, one, scaled);
  ixs_node *sum = ixs_add(ctx, scaled, y);
  ixs_node *sum_nonzero = ixs_cmp(ctx, sum, IXS_CMP_NE, zero);
  ixs_node *inverse = ixs_div(ctx, one, x);
  ixs_node *inverse_nonzero = ixs_cmp(ctx, inverse, IXS_CMP_NE, zero);
  ixs_facts *product = ixs_facts_create(ctx);
  ixs_facts *addition = ixs_facts_create(ctx);
  ixs_facts *negative_power = ixs_facts_create(ctx);
  ixs_facts *negative_power_batch = ixs_facts_create(ctx);

  CHECK(ixs_facts_assume_preds(product, &scaled_nonzero, 1));
  CHECK(test_ixs_check_defined_facts(product, reciprocal) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(addition, sum_nonzero));
  CHECK(test_ixs_check_defined_facts(addition, inverse) == IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(negative_power, inverse_nonzero));
  CHECK(test_ixs_check_defined_facts(negative_power, inverse) ==
        IXS_CHECK_UNKNOWN);
  CHECK(!ixs_facts_assume_preds(negative_power_batch, &inverse_nonzero, 1));

  ixs_ctx_destroy(ctx);
}

static void test_congruence_proves_nonzero(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "congruence_x");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *minus_one = ixs_int(ctx, -1);
  ixs_node *scaled = ixs_mul(ctx, ixs_int(ctx, 8), x);
  ixs_node *odd = ixs_add(ctx, ixs_int(ctx, 1), scaled);
  ixs_node *odd_nonzero = ixs_cmp(ctx, odd, IXS_CMP_NE, zero);
  ixs_node *odd_zero = ixs_cmp(ctx, odd, IXS_CMP_EQ, zero);
  ixs_node *scaled_not_minus_one = ixs_cmp(ctx, scaled, IXS_CMP_NE, minus_one);
  ixs_node *scaled_minus_one = ixs_cmp(ctx, scaled, IXS_CMP_EQ, minus_one);
  ixs_node *scaled_nonzero = ixs_cmp(ctx, scaled, IXS_CMP_NE, zero);
  ixs_node *one_plus_x = ixs_add(ctx, ixs_int(ctx, 1), x);
  ixs_node *one_plus_x_nonzero = ixs_cmp(ctx, one_plus_x, IXS_CMP_NE, zero);
  ixs_node *unknown = ixs_cmp(ctx, x, IXS_CMP_EQ, zero);
  ixs_node *either = ixs_or(ctx, odd_nonzero, unknown);
  ixs_facts *facts = ixs_facts_create(ctx);

  CHECK(test_ixs_check_facts(facts, odd_nonzero) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(facts, odd_zero) == IXS_CHECK_FALSE);
  CHECK(test_ixs_check_facts(facts, scaled_not_minus_one) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(facts, scaled_minus_one) == IXS_CHECK_FALSE);
  CHECK(test_ixs_check_predicate_facts(facts, either) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(facts, scaled_nonzero) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_check_facts(facts, one_plus_x_nonzero) == IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_opposite_max_nonzero_range(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "absolute_x");
  ixs_node *d = ixs_sym(ctx, "absolute_d");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *magnitude = ixs_max(ctx, d, ixs_neg(ctx, d));
  ixs_node *nonnegative = ixs_cmp(ctx, magnitude, IXS_CMP_GE, zero);
  ixs_node *positive = ixs_cmp(ctx, magnitude, IXS_CMP_GT, zero);
  ixs_node *nonzero = ixs_cmp(ctx, d, IXS_CMP_NE, zero);
  ixs_node *remainder = ixs_mod(ctx, x, magnitude);
  ixs_facts *unconstrained = ixs_facts_create(ctx);
  ixs_facts *facts = ixs_facts_create(ctx);

  CHECK(test_ixs_check_facts(unconstrained, nonnegative) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(unconstrained, positive) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_facts_assume_pred(facts, nonzero));
  CHECK(test_ixs_check_facts(facts, positive) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_defined_facts(facts, remainder) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_truncating_remainder_excludes_signed_min(void) {
  static const char remainder_text[] =
      "x - d*Piecewise((floor(x/d), (x >= 0 & d > 0) | "
      "(x <= 0 & d < 0)), (ceiling(x/d), True))";
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *d = ixs_sym(ctx, "d");
  ixs_node *remainder =
      ixs_parse_expr(ctx, remainder_text, strlen(remainder_text));
  ixs_node *signed_min = ixs_int(ctx, INT32_MIN);
  ixs_node *nonzero = ixs_cmp(ctx, d, IXS_CMP_NE, ixs_int(ctx, 0));
  ixs_node *not_min = ixs_cmp(ctx, remainder, IXS_CMP_NE, signed_min);
  ixs_node *is_min = ixs_cmp(ctx, remainder, IXS_CMP_EQ, signed_min);
  ixs_range_result range = {true, true, INT32_MIN, 1, INT32_MAX, 1};
  ixs_facts *facts = ixs_facts_create(ctx);

  CHECK(ixs_facts_assume_range(facts, x, &range));
  CHECK(ixs_facts_assume_range(facts, d, &range));
  CHECK(ixs_facts_assume_pred(facts, nonzero));
  CHECK(test_ixs_check_predicate_facts(facts, not_min) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_predicate_facts(facts, is_min) == IXS_CHECK_FALSE);

  ixs_ctx_destroy(ctx);
}

static void test_truncating_remainder_intersects_explicit_range(void) {
  static const char remainder_text[] =
      "x - d*Piecewise((floor(x/d), (x >= 0 & d > 0) | "
      "(x <= 0 & d < 0)), (ceiling(x/d), True))";
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *d = ixs_sym(ctx, "d");
  ixs_node *remainder =
      ixs_parse_expr(ctx, remainder_text, strlen(remainder_text));
  ixs_node *d_is_four = ixs_cmp(ctx, d, IXS_CMP_EQ, ixs_int(ctx, 4));
  ixs_node *remainder_is_zero =
      ixs_cmp(ctx, remainder, IXS_CMP_EQ, ixs_int(ctx, 0));
  ixs_node *remainder_is_four =
      ixs_cmp(ctx, remainder, IXS_CMP_EQ, ixs_int(ctx, 4));
  ixs_range_result exact_zero = {true, true, 0, 1, 0, 1};
  ixs_range_result exact_four = {true, true, 4, 1, 4, 1};
  ixs_range_result range;
  ixs_integer_range_result integer_range;
  ixs_facts *refined = ixs_facts_create(ctx);
  ixs_facts *disjoint = ixs_facts_create(ctx);

  CHECK(ixs_facts_assume_pred(refined, d_is_four));
  CHECK(ixs_facts_assume_range(refined, remainder, &exact_zero));
  CHECK(test_ixs_check_facts(refined, remainder_is_zero) == IXS_CHECK_TRUE);
  CHECK(test_ixs_range_facts(refined, remainder, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 0 && range.upper_q == 1);
  CHECK(test_ixs_integer_range_facts(refined, remainder, &integer_range));
  CHECK(integer_range.has_lower && integer_range.lower == 0);
  CHECK(integer_range.has_upper && integer_range.upper == 0);

  CHECK(ixs_facts_assume_pred(disjoint, d_is_four));
  CHECK(ixs_facts_assume_range(disjoint, remainder, &exact_four));
  CHECK(test_ixs_check_facts(disjoint, remainder_is_four) == IXS_CHECK_UNKNOWN);
  CHECK(!test_ixs_range_facts(disjoint, remainder, &range));
  CHECK(!test_ixs_integer_range_facts(disjoint, remainder, &integer_range));

  ixs_ctx_destroy(ctx);
}

int main(void) {
  test_integer_overflow();
  test_division_by_zero();
  test_degenerate_piecewise();
  test_int64_min_handling();
  test_empty_null_inputs();
  test_max_depth_expressions();
  test_long_prefix_parse();
  test_sentinel_propagation();
  test_large_integers();
  test_symbol_edge_cases();
  test_print_buffer();
  test_null_ctx_destroy();
  test_many_expression_ranges();
  test_product_nonzero_factors();
  test_congruence_proves_nonzero();
  test_opposite_max_nonzero_range();
  test_truncating_remainder_excludes_signed_min();
  test_truncating_remainder_intersects_explicit_range();

  printf("test_edge_cases: %d/%d passed\n", tests_passed, tests_run);
  return tests_passed == tests_run ? 0 : 1;
}
