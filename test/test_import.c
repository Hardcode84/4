/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include <ixsimpl.h>

#include <stdio.h>
#include <string.h>

static int failures;

#define CHECK(expr)                                                            \
  do {                                                                         \
    if (!(expr)) {                                                             \
      fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, #expr);          \
      failures++;                                                              \
    }                                                                          \
  } while (0)

static int init_session(ixs_ctx **ctx, ixs_session *s) {
  *ctx = ixs_ctx_create();
  CHECK(*ctx != NULL);
  if (!*ctx)
    return 0;
  ixs_session_init(s, *ctx);
  return 1;
}

static void destroy_session(ixs_ctx *ctx, ixs_session *s) {
  if (!ctx)
    return;
  ixs_session_destroy(s);
  ixs_ctx_destroy(ctx);
}

static void check_same_print(ixs_node *src, ixs_node *dst) {
  char src_buf[256];
  char dst_buf[256];

  CHECK(src != NULL);
  CHECK(dst != NULL);
  if (!src || !dst)
    return;

  ixs_print(src, src_buf, sizeof(src_buf));
  ixs_print(dst, dst_buf, sizeof(dst_buf));
  CHECK(strcmp(src_buf, dst_buf) == 0);
}

static void test_same_store_reuse(void) {
  ixs_ctx *ctx = NULL;
  ixs_session s;
  ixs_node *x;
  ixs_node *expr;
  ixs_node *imported;

  if (!init_session(&ctx, &s))
    return;

  x = ixs_sym(&s, "x");
  expr = ixs_add(&s, x, ixs_int(&s, 1));
  imported = ixs_import_node(&s, expr);
  CHECK(imported == expr);

  destroy_session(ctx, &s);
}

static void test_cross_store_import(void) {
  ixs_ctx *src_ctx = NULL;
  ixs_ctx *dst_ctx = NULL;
  ixs_session src_s;
  ixs_session dst_s;
  ixs_node *x;
  ixs_node *y;
  ixs_node *expr;
  ixs_node *imported;
  ixs_node *combined;

  if (!init_session(&src_ctx, &src_s))
    return;
  if (!init_session(&dst_ctx, &dst_s)) {
    destroy_session(src_ctx, &src_s);
    return;
  }

  x = ixs_sym(&src_s, "x");
  y = ixs_sym(&src_s, "y");
  expr = ixs_add(&src_s, ixs_mul(&src_s, ixs_int(&src_s, 3), x),
                 ixs_mul(&src_s, ixs_int(&src_s, 2), y));
  imported = ixs_import_node(&dst_s, expr);

  CHECK(imported != NULL);
  check_same_print(expr, imported);
  CHECK(imported != expr);

  combined = ixs_add(&dst_s, imported, ixs_int(&dst_s, 1));
  CHECK(combined != NULL);
  CHECK(!ixs_is_error(combined));
  CHECK(ixs_import_node(&dst_s, imported) == imported);

  destroy_session(dst_ctx, &dst_s);
  destroy_session(src_ctx, &src_s);
}

static void test_cross_store_tag_smoke(void) {
  ixs_ctx *src_ctx = NULL;
  ixs_ctx *dst_ctx = NULL;
  ixs_session src_s;
  ixs_session dst_s;
  ixs_node *x;
  ixs_node *y;
  ixs_node *zero;
  ixs_node *two;
  ixs_node *three;
  ixs_node *four;
  ixs_node *five;
  ixs_node *gt0;
  ixs_node *lt4;
  ixs_node *not_lt4;
  ixs_node *roots[9];
  ixs_node *imported[9];
  ixs_node *pw_vals[2];
  ixs_node *pw_conds[2];
  size_t i;

  if (!init_session(&src_ctx, &src_s))
    return;
  if (!init_session(&dst_ctx, &dst_s)) {
    destroy_session(src_ctx, &src_s);
    return;
  }

  x = ixs_sym(&src_s, "x");
  y = ixs_sym(&src_s, "y");
  zero = ixs_int(&src_s, 0);
  two = ixs_int(&src_s, 2);
  three = ixs_int(&src_s, 3);
  four = ixs_int(&src_s, 4);
  five = ixs_int(&src_s, 5);
  gt0 = ixs_cmp(&src_s, x, IXS_CMP_GT, zero);
  lt4 = ixs_cmp(&src_s, y, IXS_CMP_LT, four);
  not_lt4 = ixs_not(&src_s, lt4);

  pw_vals[0] = ixs_max(&src_s, x, y);
  pw_vals[1] = ixs_min(&src_s, x, y);
  pw_conds[0] = gt0;
  pw_conds[1] = ixs_true(&src_s);

  roots[0] = gt0;
  roots[1] = ixs_and(&src_s, gt0, not_lt4);
  roots[2] = ixs_or(&src_s, gt0, lt4);
  roots[3] = ixs_floor(&src_s, ixs_div(&src_s, x, two));
  roots[4] = ixs_ceil(&src_s, ixs_div(&src_s, y, three));
  roots[5] = ixs_mod(&src_s, ixs_add(&src_s, x, three), five);
  roots[6] = ixs_xor(&src_s, x, y);
  roots[7] = ixs_pw(&src_s, 2, pw_vals, pw_conds);
  roots[8] = ixs_not(&src_s, gt0);

  CHECK(ixs_import_many(&dst_s, (const ixs_node *const *)roots,
                        sizeof(roots) / sizeof(roots[0]), imported));
  for (i = 0; i < sizeof(roots) / sizeof(roots[0]); i++) {
    CHECK(ixs_node_tag(imported[i]) == ixs_node_tag(roots[i]));
    check_same_print(roots[i], imported[i]);
  }

  destroy_session(dst_ctx, &dst_s);
  destroy_session(src_ctx, &src_s);
}

static void test_sentinel_mapping(void) {
  ixs_ctx *src_ctx = NULL;
  ixs_ctx *dst_ctx = NULL;
  ixs_session src_s;
  ixs_session dst_s;
  ixs_node *src_err;
  ixs_node *dst_err;
  ixs_node *src_parse;
  ixs_node *dst_parse;

  if (!init_session(&src_ctx, &src_s))
    return;
  if (!init_session(&dst_ctx, &dst_s)) {
    destroy_session(src_ctx, &src_s);
    return;
  }

  src_err = ixs_div(&src_s, ixs_int(&src_s, 1), ixs_int(&src_s, 0));
  dst_err = ixs_div(&dst_s, ixs_int(&dst_s, 1), ixs_int(&dst_s, 0));
  CHECK(src_err && ixs_is_domain_error(src_err));
  CHECK(dst_err && ixs_is_domain_error(dst_err));
  ixs_session_clear_errors(&src_s);
  ixs_session_clear_errors(&dst_s);

  CHECK(ixs_import_node(&dst_s, src_err) == dst_err);
  CHECK(ixs_session_nerrors(&dst_s) == 0);

  src_parse = ixs_parse(&src_s, "???", 3);
  dst_parse = ixs_parse(&dst_s, "???", 3);
  CHECK(src_parse && ixs_is_parse_error(src_parse));
  CHECK(dst_parse && ixs_is_parse_error(dst_parse));
  ixs_session_clear_errors(&src_s);
  ixs_session_clear_errors(&dst_s);

  CHECK(ixs_import_node(&dst_s, src_parse) == dst_parse);
  CHECK(ixs_session_nerrors(&dst_s) == 0);

  destroy_session(dst_ctx, &dst_s);
  destroy_session(src_ctx, &src_s);
}

static void test_import_many_zero(void) {
  ixs_ctx *ctx = NULL;
  ixs_session s;

  if (!init_session(&ctx, &s))
    return;

  /* count == 0 is a documented no-op success. */
  CHECK(ixs_import_many(&s, NULL, 0, NULL));

  destroy_session(ctx, &s);
}

static void test_import_null_inputs(void) {
  ixs_ctx *src_ctx = NULL;
  ixs_ctx *dst_ctx = NULL;
  ixs_session src_s;
  ixs_session dst_s;
  ixs_node *src[1];
  ixs_node *dst[1];
  ixs_node *x;

  if (!init_session(&src_ctx, &src_s))
    return;
  if (!init_session(&dst_ctx, &dst_s)) {
    destroy_session(src_ctx, &src_s);
    return;
  }

  x = ixs_sym(&src_s, "x");
  src[0] = x;
  dst[0] = ixs_false(&dst_s);

  CHECK(ixs_import_node(&dst_s, NULL) == NULL);
  CHECK(!ixs_import_many(&dst_s, NULL, 1, dst));
  CHECK(!ixs_import_many(&dst_s, (const ixs_node *const *)src, 1, NULL));
  CHECK(dst[0] == ixs_false(&dst_s));

  destroy_session(dst_ctx, &dst_s);
  destroy_session(src_ctx, &src_s);
}

static void test_import_many_failure_preserves_out(void) {
  ixs_ctx *src_ctx = NULL;
  ixs_ctx *dst_ctx = NULL;
  ixs_session src_s;
  ixs_session dst_s;
  ixs_node *shared;
  ixs_node *src[2];
  ixs_node *dst[2];
  ixs_node *old0;
  ixs_node *old1;

  if (!init_session(&src_ctx, &src_s))
    return;
  if (!init_session(&dst_ctx, &dst_s)) {
    destroy_session(src_ctx, &src_s);
    return;
  }

  shared = ixs_mul(&src_s, ixs_sym(&src_s, "x"), ixs_sym(&src_s, "y"));
  src[0] = ixs_add(&src_s, shared, ixs_int(&src_s, 1));
  src[1] = NULL;
  dst[0] = ixs_false(&dst_s);
  dst[1] = ixs_true(&dst_s);
  old0 = dst[0];
  old1 = dst[1];

  CHECK(!ixs_import_many(&dst_s, (const ixs_node *const *)src, 2, dst));
  CHECK(dst[0] == old0);
  CHECK(dst[1] == old1);
  CHECK(ixs_import_node(&dst_s, src[0]) != NULL);

  destroy_session(dst_ctx, &dst_s);
  destroy_session(src_ctx, &src_s);
}

static void test_import_many(void) {
  ixs_ctx *src_ctx = NULL;
  ixs_ctx *dst_ctx = NULL;
  ixs_session src_s;
  ixs_session dst_s;
  ixs_node *shared;
  ixs_node *src[2];
  ixs_node *dst[2];
  bool ok;

  if (!init_session(&src_ctx, &src_s))
    return;
  if (!init_session(&dst_ctx, &dst_s)) {
    destroy_session(src_ctx, &src_s);
    return;
  }

  shared = ixs_mul(&src_s, ixs_sym(&src_s, "x"), ixs_sym(&src_s, "y"));
  src[0] = ixs_add(&src_s, shared, ixs_int(&src_s, 1));
  src[1] = ixs_sub(&src_s, shared, ixs_int(&src_s, 1));
  dst[0] = ixs_false(&dst_s);
  dst[1] = ixs_true(&dst_s);

  ok = ixs_import_many(&dst_s, (const ixs_node *const *)src, 2, dst);
  CHECK(ok);
  CHECK(dst[0] && ixs_node_tag(dst[0]) == IXS_ADD);
  CHECK(dst[1] && ixs_node_tag(dst[1]) == IXS_ADD);
  CHECK(ixs_node_add_nterms(dst[0]) == 1);
  CHECK(ixs_node_add_nterms(dst[1]) == 1);
  CHECK(ixs_same_node(ixs_node_add_term(dst[0], 0),
                      ixs_node_add_term(dst[1], 0)));

  destroy_session(dst_ctx, &dst_s);
  destroy_session(src_ctx, &src_s);
}

int main(void) {
  test_same_store_reuse();
  test_cross_store_import();
  test_cross_store_tag_smoke();
  test_sentinel_mapping();
  test_import_many_zero();
  test_import_null_inputs();
  test_import_many_failure_preserves_out();
  test_import_many();

  if (failures != 0) {
    fprintf(stderr, "test_import: %d failure(s)\n", failures);
    return 1;
  }

  printf("test_import: OK\n");
  return 0;
}
