/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include <ixsimpl.h>

#include "node.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures;

#define TEST_SERIAL_MAGIC 0x42535849u
#define TEST_SERIAL_VERSION 1u
#define TEST_WIRE_INT 0u
#define TEST_WIRE_RAT 1u
#define TEST_WIRE_SYM 2u
#define TEST_WIRE_ADD 3u
#define TEST_WIRE_MUL 4u
#define TEST_WIRE_FLOOR 5u
#define TEST_WIRE_MOD 7u

#define CHECK(expr)                                                            \
  do {                                                                         \
    if (!(expr)) {                                                             \
      fprintf(stderr, "FAIL %s:%d: %s\n", __FILE__, __LINE__, #expr);          \
      failures++;                                                              \
    }                                                                          \
  } while (0)

typedef struct {
  unsigned char *data;
  size_t len;
  size_t cap;
  size_t fail_after;
} byte_buffer;

typedef struct {
  const unsigned char *data;
  size_t len;
  size_t pos;
} byte_reader;

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

static void buffer_reset(byte_buffer *buf) { buf->len = 0; }

static void buffer_destroy(byte_buffer *buf) {
  free(buf->data);
  memset(buf, 0, sizeof(*buf));
}

static bool buffer_write(void *userdata, const void *src, size_t len) {
  byte_buffer *buf = userdata;
  size_t needed;
  size_t new_cap;
  unsigned char *new_data;

  if (buf->len > buf->fail_after || len > buf->fail_after - buf->len)
    return false;
  if (len == 0)
    return true;
  needed = buf->len + len;
  if (needed <= buf->cap) {
    memcpy(buf->data + buf->len, src, len);
    buf->len = needed;
    return true;
  }

  new_cap = buf->cap ? buf->cap : 64u;
  while (new_cap < needed) {
    size_t doubled = new_cap * 2u;
    if (doubled <= new_cap)
      return false;
    new_cap = doubled;
  }
  new_data = realloc(buf->data, new_cap);
  if (!new_data)
    return false;
  buf->data = new_data;
  buf->cap = new_cap;
  memcpy(buf->data + buf->len, src, len);
  buf->len = needed;
  return true;
}

static bool reader_read(void *userdata, void *dst, size_t len) {
  byte_reader *reader = userdata;

  if (reader->pos > reader->len)
    return false;
  if (len > reader->len - reader->pos)
    return false;
  memcpy(dst, reader->data + reader->pos, len);
  reader->pos += len;
  return true;
}

static size_t reader_remaining(void *userdata) {
  byte_reader *reader = userdata;
  return reader->len - reader->pos;
}

static bool serialize_to_buffer(ixs_session *s, const ixs_node *node,
                                byte_buffer *buf) {
  ixs_writer writer;
  buffer_reset(buf);
  writer.write = buffer_write;
  writer.userdata = buf;
  return ixs_serialize_node(s, node, &writer);
}

static ixs_node *deserialize_from_buffer(ixs_session *s,
                                         const byte_buffer *buf) {
  byte_reader reader_state;
  ixs_reader reader;

  reader_state.data = buf->data;
  reader_state.len = buf->len;
  reader_state.pos = 0;
  reader.read = reader_read;
  reader.remaining = reader_remaining;
  reader.userdata = &reader_state;
  return ixs_deserialize_node(s, &reader);
}

static void store_le32(unsigned char *dst, uint32_t v) {
  /* Match the v1 wire format's little-endian uint32 fields. */
  dst[0] = (unsigned char)(v & 0xffu);
  dst[1] = (unsigned char)((v >> 8) & 0xffu);
  dst[2] = (unsigned char)((v >> 16) & 0xffu);
  dst[3] = (unsigned char)((v >> 24) & 0xffu);
}

static void store_le64(unsigned char *dst, int64_t v) {
  uint64_t u = (uint64_t)v;
  size_t i;

  for (i = 0; i < 8u; i++) {
    dst[i] = (unsigned char)(u & 0xffu);
    u >>= 8;
  }
}

static void append_u8(byte_buffer *buf, uint8_t value) {
  CHECK(buffer_write(buf, &value, sizeof(value)));
}

static void append_le32(byte_buffer *buf, uint32_t value) {
  unsigned char bytes[4];

  store_le32(bytes, value);
  CHECK(buffer_write(buf, bytes, sizeof(bytes)));
}

static void append_le64(byte_buffer *buf, int64_t value) {
  unsigned char bytes[8];

  store_le64(bytes, value);
  CHECK(buffer_write(buf, bytes, sizeof(bytes)));
}

static void append_int_node(byte_buffer *buf, int64_t value) {
  append_u8(buf, TEST_WIRE_INT);
  append_le64(buf, value);
}

static void append_rat_node(byte_buffer *buf, int64_t p, int64_t q) {
  append_u8(buf, TEST_WIRE_RAT);
  append_le64(buf, p);
  append_le64(buf, q);
}

static void append_sym_node(byte_buffer *buf, const char *name) {
  size_t len = strlen(name);

  CHECK(len <= UINT32_MAX);
  append_u8(buf, TEST_WIRE_SYM);
  append_le32(buf, (uint32_t)len);
  CHECK(buffer_write(buf, name, len));
}

static void append_mul_header(byte_buffer *buf, uint32_t count,
                              uint32_t coefficient) {
  append_u8(buf, TEST_WIRE_MUL);
  append_le32(buf, count);
  append_le32(buf, coefficient);
}

static void append_mul_factor(byte_buffer *buf, uint32_t base,
                              int64_t exponent) {
  append_le32(buf, base);
  append_le64(buf, exponent);
}

static void append_add_term(byte_buffer *buf, uint32_t term,
                            uint32_t coefficient) {
  append_le32(buf, term);
  append_le32(buf, coefficient);
}

static void build_bounds_alias_blob(byte_buffer *buf) {
  enum {
    ZERO,
    ONE,
    ONE_EIGHTH,
    EIGHT,
    OUTER,
    X,
    QUOTIENT,
    FLOOR_QUOTIENT,
    REMAINDER,
    FLOOR_TERM,
    REMAINDER_TERM,
    RAW_SUM,
    NODE_COUNT
  };

  buffer_reset(buf);
  append_le32(buf, TEST_SERIAL_MAGIC);
  append_le32(buf, TEST_SERIAL_VERSION);
  append_le32(buf, NODE_COUNT);

  append_int_node(buf, 0);
  append_int_node(buf, 1);
  append_rat_node(buf, 1, 8);
  append_int_node(buf, 8);
  append_sym_node(buf, "outer");
  append_sym_node(buf, "x");

  append_mul_header(buf, 1, ONE_EIGHTH);
  append_mul_factor(buf, X, 1);

  append_u8(buf, TEST_WIRE_FLOOR);
  append_le32(buf, QUOTIENT);

  append_u8(buf, TEST_WIRE_MOD);
  append_le32(buf, X);
  append_le32(buf, EIGHT);

  append_mul_header(buf, 2, EIGHT);
  append_mul_factor(buf, OUTER, 1);
  append_mul_factor(buf, FLOOR_QUOTIENT, 1);

  append_mul_header(buf, 2, ONE);
  append_mul_factor(buf, OUTER, 1);
  append_mul_factor(buf, REMAINDER, 1);

  append_u8(buf, TEST_WIRE_ADD);
  append_le32(buf, 2);
  append_le32(buf, ZERO);
  append_add_term(buf, FLOOR_TERM, ONE);
  append_add_term(buf, REMAINDER_TERM, ONE);
  append_le32(buf, RAW_SUM);
}

static void build_literal_mod_blob(byte_buffer *buf, int64_t divisor) {
  unsigned char blob[40];

  store_le32(blob + 0u, TEST_SERIAL_MAGIC);
  store_le32(blob + 4u, TEST_SERIAL_VERSION);
  store_le32(blob + 8u, 3u);
  blob[12] = TEST_WIRE_SYM;
  store_le32(blob + 13u, 1u);
  blob[17] = 'x';
  blob[18] = TEST_WIRE_INT;
  store_le64(blob + 19u, divisor);
  blob[27] = TEST_WIRE_MOD;
  store_le32(blob + 28u, 0u);
  store_le32(blob + 32u, 1u);
  store_le32(blob + 36u, 2u);
  buffer_reset(buf);
  CHECK(buffer_write(buf, blob, sizeof(blob)));
}

static void build_rational_mod_blob(byte_buffer *buf, int64_t numerator,
                                    int64_t denominator) {
  unsigned char blob[48];

  store_le32(blob + 0u, TEST_SERIAL_MAGIC);
  store_le32(blob + 4u, TEST_SERIAL_VERSION);
  store_le32(blob + 8u, 3u);
  blob[12] = TEST_WIRE_SYM;
  store_le32(blob + 13u, 1u);
  blob[17] = 'x';
  blob[18] = TEST_WIRE_RAT;
  store_le64(blob + 19u, numerator);
  store_le64(blob + 27u, denominator);
  blob[35] = TEST_WIRE_MOD;
  store_le32(blob + 36u, 0u);
  store_le32(blob + 40u, 1u);
  store_le32(blob + 44u, 2u);
  buffer_reset(buf);
  CHECK(buffer_write(buf, blob, sizeof(blob)));
}

static void check_same_print(ixs_node *a, ixs_node *b) {
  char lhs[512];
  char rhs[512];

  CHECK(a != NULL);
  CHECK(b != NULL);
  if (!a || !b)
    return;

  ixs_print(a, lhs, sizeof(lhs));
  ixs_print(b, rhs, sizeof(rhs));
  CHECK(strcmp(lhs, rhs) == 0);
}

static ixs_node *build_roundtrip_expr(ixs_session *s) {
  ixs_node *x = ixs_sym(s, "x");
  ixs_node *y = ixs_sym(s, "y");
  ixs_node *zero = ixs_int(s, 0);
  ixs_node *one = ixs_int(s, 1);
  ixs_node *two = ixs_int(s, 2);
  ixs_node *three = ixs_int(s, 3);
  ixs_node *five = ixs_int(s, 5);
  ixs_node *gt0 = ixs_cmp(s, x, IXS_CMP_GT, zero);
  ixs_node *lt5 = ixs_cmp(s, y, IXS_CMP_LT, five);
  ixs_node *not_lt5 = ixs_not(s, lt5);
  ixs_node *cond0 = ixs_or(s, gt0, not_lt5);
  ixs_node *vals[2];
  ixs_node *conds[2];
  ixs_node *pw;
  ixs_node *half_up;
  ixs_node *modded;
  ixs_node *arith;

  vals[0] = ixs_add(s, ixs_floor(s, ixs_div(s, ixs_add(s, x, one), two)),
                    ixs_xor(s, x, y));
  vals[1] = ixs_max(s, x, y);
  conds[0] = cond0;
  conds[1] = ixs_true(s);
  pw = ixs_pw(s, 2, vals, conds);
  half_up = ixs_ceil(s, ixs_div(s, ixs_add(s, y, three), two));
  modded = ixs_mod(s, ixs_add(s, x, three), five);
  arith = ixs_add(s, ixs_mul(s, two, pw), ixs_min(s, modded, half_up));
  return ixs_and(s, gt0, ixs_cmp(s, arith, IXS_CMP_GE, zero));
}

static void test_roundtrip_deterministic(void) {
  ixs_ctx *src_ctx = NULL;
  ixs_ctx *dst_ctx = NULL;
  ixs_session src_s;
  ixs_session dst_s;
  byte_buffer buf1 = {0};
  byte_buffer buf2 = {0};
  ixs_node *expr;
  ixs_node *decoded;
  ixs_node *decoded_again;
  ixs_node *roundtripped;

  buf1.fail_after = (size_t)-1;
  buf2.fail_after = (size_t)-1;

  if (!init_session(&src_ctx, &src_s))
    return;
  if (!init_session(&dst_ctx, &dst_s)) {
    destroy_session(src_ctx, &src_s);
    return;
  }

  expr = build_roundtrip_expr(&src_s);
  CHECK(expr != NULL);
  CHECK(!ixs_is_error(expr));

  CHECK(serialize_to_buffer(&src_s, expr, &buf1));
  decoded = deserialize_from_buffer(&dst_s, &buf1);
  CHECK(decoded != NULL);
  CHECK(!ixs_is_error(decoded));
  check_same_print(expr, decoded);

  decoded_again = deserialize_from_buffer(&dst_s, &buf1);
  CHECK(ixs_same_node(decoded, decoded_again));

  CHECK(serialize_to_buffer(&dst_s, decoded, &buf2));
  CHECK(buf1.len == buf2.len);
  CHECK(memcmp(buf1.data, buf2.data, buf1.len) == 0);

  roundtripped = deserialize_from_buffer(&src_s, &buf2);
  CHECK(ixs_same_node(roundtripped, expr));

  buffer_destroy(&buf2);
  buffer_destroy(&buf1);
  destroy_session(dst_ctx, &dst_s);
  destroy_session(src_ctx, &src_s);
}

static void test_singletons_and_sentinels(void) {
  ixs_ctx *src_ctx = NULL;
  ixs_ctx *dst_ctx = NULL;
  ixs_session src_s;
  ixs_session dst_s;
  byte_buffer buf = {0};
  ixs_node *nodes[4];
  ixs_node *decoded;
  ixs_node *dst_err;
  ixs_node *dst_parse;
  size_t i;

  buf.fail_after = (size_t)-1;

  if (!init_session(&src_ctx, &src_s))
    return;
  if (!init_session(&dst_ctx, &dst_s)) {
    destroy_session(src_ctx, &src_s);
    return;
  }

  nodes[0] = ixs_true(&src_s);
  nodes[1] = ixs_false(&src_s);
  nodes[2] = ixs_div(&src_s, ixs_int(&src_s, 1), ixs_int(&src_s, 0));
  nodes[3] = ixs_parse(&src_s, "???", 3);
  CHECK(nodes[2] && ixs_is_domain_error(nodes[2]));
  CHECK(nodes[3] && ixs_is_parse_error(nodes[3]));
  ixs_session_clear_errors(&src_s);

  dst_err = ixs_div(&dst_s, ixs_int(&dst_s, 1), ixs_int(&dst_s, 0));
  dst_parse = ixs_parse(&dst_s, "???", 3);
  CHECK(dst_err && ixs_is_domain_error(dst_err));
  CHECK(dst_parse && ixs_is_parse_error(dst_parse));
  ixs_session_clear_errors(&dst_s);

  for (i = 0; i < 4; i++) {
    ixs_session_clear_errors(&dst_s);
    CHECK(serialize_to_buffer(&src_s, nodes[i], &buf));
    decoded = deserialize_from_buffer(&dst_s, &buf);
    CHECK(decoded != NULL);
    CHECK(ixs_session_nerrors(&dst_s) == 0);
    if (i == 0)
      CHECK(decoded == ixs_true(&dst_s));
    else if (i == 1)
      CHECK(decoded == ixs_false(&dst_s));
    else if (i == 2)
      CHECK(decoded == dst_err);
    else
      CHECK(decoded == dst_parse);
  }

  buffer_destroy(&buf);
  destroy_session(dst_ctx, &dst_s);
  destroy_session(src_ctx, &src_s);
}

static void test_writer_failure_no_diagnostics(void) {
  ixs_ctx *ctx = NULL;
  ixs_session s;
  byte_buffer buf = {0};
  ixs_node *expr;

  buf.fail_after = 8u;

  if (!init_session(&ctx, &s))
    return;

  expr = build_roundtrip_expr(&s);
  CHECK(expr != NULL);
  ixs_session_clear_errors(&s);
  CHECK(!serialize_to_buffer(&s, expr, &buf));
  CHECK(ixs_session_nerrors(&s) == 0);

  buffer_destroy(&buf);
  destroy_session(ctx, &s);
}

static void test_bounds_canonical_alias_public(void) {
  ixs_ctx *ctx = NULL;
  ixs_session s;
  byte_buffer buf = {0};
  ixs_node *raw;
  ixs_node *canonical;
  ixs_node *outer;
  ixs_node *x;
  ixs_facts *raw_facts;
  ixs_facts *canonical_facts;
  ixs_range_result input;
  ixs_range_result result;

  buf.fail_after = (size_t)-1;
  if (!init_session(&ctx, &s))
    return;

  build_bounds_alias_blob(&buf);
  raw = deserialize_from_buffer(&s, &buf);
  outer = ixs_sym(&s, "outer");
  x = ixs_sym(&s, "x");
  canonical = ixs_mul(&s, outer, x);
  raw_facts = ixs_facts_create(&s);
  canonical_facts = ixs_facts_create(&s);

  CHECK(raw != NULL);
  CHECK(!ixs_is_error(raw));
  CHECK(!ixs_same_node(raw, canonical));
  CHECK(ixs_same_node(ixs_simplify(&s, raw, NULL, 0), canonical));
  CHECK(raw_facts != NULL);
  CHECK(canonical_facts != NULL);

  input.has_lower = true;
  input.lower_p = 0;
  input.lower_q = 1;
  input.has_upper = true;
  input.upper_p = 2147483632;
  input.upper_q = 1;

  CHECK(ixs_facts_assume_range(raw_facts, raw, &input));
  CHECK(ixs_range_facts(raw_facts, canonical, &result));
  CHECK(result.has_lower && result.lower_p == 0 && result.lower_q == 1);
  CHECK(result.has_upper && result.upper_p == 2147483632 &&
        result.upper_q == 1);

  CHECK(ixs_facts_assume_range(canonical_facts, canonical, &input));
  CHECK(ixs_range_facts(canonical_facts, raw, &result));
  CHECK(result.has_lower && result.lower_p == 0 && result.lower_q == 1);
  CHECK(result.has_upper && result.upper_p == 2147483632 &&
        result.upper_q == 1);
  CHECK(ixs_session_nerrors(&s) == 0);

  buffer_destroy(&buf);
  destroy_session(ctx, &s);
}

static void test_malformed_root_rejected_without_pollution(void) {
  ixs_ctx *src_ctx = NULL;
  ixs_ctx *dst_ctx = NULL;
  ixs_session src_s;
  ixs_session dst_s;
  byte_buffer good = {0};
  byte_buffer bad = {0};
  ixs_node *expr;
  ixs_node *decoded;
  size_t before_used;
  size_t after_used;

  good.fail_after = (size_t)-1;
  bad.fail_after = (size_t)-1;

  if (!init_session(&src_ctx, &src_s))
    return;
  if (!init_session(&dst_ctx, &dst_s)) {
    destroy_session(src_ctx, &src_s);
    return;
  }

  expr = ixs_add(&src_s, ixs_sym(&src_s, "x"), ixs_int(&src_s, 1));
  CHECK(expr != NULL);
  CHECK(serialize_to_buffer(&src_s, expr, &good));
  CHECK(buffer_write(&bad, good.data, good.len));
  CHECK(bad.len >= 4);
  store_le32(bad.data + bad.len - 4u, 99u);

  /* Internal regression check: malformed input must not grow the store. */
  before_used = dst_ctx->htab_used;
  ixs_session_clear_errors(&dst_s);
  decoded = deserialize_from_buffer(&dst_s, &bad);
  after_used = dst_ctx->htab_used;

  CHECK(decoded != NULL);
  CHECK(ixs_is_parse_error(decoded));
  CHECK(after_used == before_used);
  CHECK(ixs_session_nerrors(&dst_s) == 1);
  CHECK(strstr(ixs_session_error(&dst_s, 0), "root index") != NULL);

  decoded = deserialize_from_buffer(&dst_s, &good);
  CHECK(decoded != NULL);
  CHECK(!ixs_is_error(decoded));
  CHECK(dst_ctx->htab_used > before_used);

  buffer_destroy(&bad);
  buffer_destroy(&good);
  destroy_session(dst_ctx, &dst_s);
  destroy_session(src_ctx, &src_s);
}

/*
 * This regression fabricates a noncanonical MUL via raw constructors.
 * Those helpers are internal and disappear in the amalgamated build, so keep
 * this check on the normal multi-translation-unit path only.
 */
#ifndef IXS_TEST_AMALGAMATION
static void test_noncanonical_mul_rejected_on_serialize(void) {
  ixs_ctx *ctx = NULL;
  ixs_session s;
  byte_buffer buf = {0};
  ixs_node *x;
  ixs_node *bad;
  ixs_mulfactor factor;

  buf.fail_after = (size_t)-1;

  if (!init_session(&ctx, &s))
    return;

  x = ixs_sym(&s, "x");
  factor.base = x;
  factor.exp = 0;
  bad = ixs_node_mul(ctx, ixs_node_int(ctx, 1), 1, &factor);
  CHECK(bad != NULL);
  ixs_session_clear_errors(&s);
  CHECK(!serialize_to_buffer(&s, bad, &buf));
  CHECK(ixs_session_nerrors(&s) == 1);
  CHECK(strstr(ixs_session_error(&s, 0), "zero exponent") != NULL);

  buffer_destroy(&buf);
  destroy_session(ctx, &s);
}

static void test_nonpositive_mod_rejected_on_serialize(void) {
  ixs_ctx *ctx = NULL;
  ixs_session s;
  byte_buffer buf = {0};
  ixs_node *x;
  ixs_node *bad;

  buf.fail_after = (size_t)-1;

  if (!init_session(&ctx, &s))
    return;

  x = ixs_sym(&s, "x");
  bad = ixs_node_binary(ctx, IXS_MOD, x, ixs_node_int(ctx, -3), IXS_CMP_EQ);
  CHECK(bad != NULL);
  ixs_session_clear_errors(&s);
  CHECK(!serialize_to_buffer(&s, bad, &buf));
  CHECK(ixs_session_nerrors(&s) == 1);
  CHECK(strstr(ixs_session_error(&s, 0), "negative") != NULL);

  buffer_destroy(&buf);
  destroy_session(ctx, &s);
}
#endif

static void test_nonpositive_mod_rejected_on_deserialize(void) {
  static const int64_t invalid[] = {-3, 0, INT64_MIN};
  ixs_ctx *ctx = NULL;
  ixs_session s;
  byte_buffer buf = {0};
  size_t i;

  buf.fail_after = (size_t)-1;
  if (!init_session(&ctx, &s))
    return;

  for (i = 0; i < sizeof(invalid) / sizeof(invalid[0]); i++) {
    ixs_node *decoded;
    size_t before_used;

    build_literal_mod_blob(&buf, invalid[i]);
    before_used = ctx->htab_used;
    ixs_session_clear_errors(&s);
    decoded = deserialize_from_buffer(&s, &buf);
    CHECK(decoded != NULL);
    CHECK(ixs_is_parse_error(decoded));
    CHECK(ctx->htab_used == before_used);
    CHECK(ixs_session_nerrors(&s) == 1);
    CHECK(strstr(ixs_session_error(&s, 0), "not positive") != NULL);
  }

  build_rational_mod_blob(&buf, -1, 2);
  ixs_session_clear_errors(&s);
  CHECK(ixs_is_parse_error(deserialize_from_buffer(&s, &buf)));
  CHECK(ixs_session_nerrors(&s) == 1);
  CHECK(strstr(ixs_session_error(&s, 0), "not positive") != NULL);

  build_literal_mod_blob(&buf, 3);
  ixs_session_clear_errors(&s);
  {
    ixs_node *decoded = deserialize_from_buffer(&s, &buf);
    CHECK(decoded != NULL);
    CHECK(!ixs_is_error(decoded));
    CHECK(ixs_node_tag(decoded) == IXS_MOD);
    CHECK(ixs_session_nerrors(&s) == 0);
  }

  buffer_destroy(&buf);
  destroy_session(ctx, &s);
}

static void test_node_limit_rejected_without_pollution(void) {
  ixs_ctx *ctx = NULL;
  ixs_session s;
  byte_buffer buf = {0};
  ixs_node *decoded;
  size_t before_used;
  size_t after_used;
  unsigned char blob[16];

  if (!init_session(&ctx, &s))
    return;

  buf.fail_after = (size_t)-1;
  store_le32(blob + 0u, TEST_SERIAL_MAGIC);
  store_le32(blob + 4u, TEST_SERIAL_VERSION);
  store_le32(blob + 8u, UINT32_MAX);
  store_le32(blob + 12u, 0u);
  CHECK(buffer_write(&buf, blob, sizeof(blob)));

  /* Internal regression check: over-limit framing must not mutate the store. */
  before_used = ctx->htab_used;
  ixs_session_clear_errors(&s);
  decoded = deserialize_from_buffer(&s, &buf);
  after_used = ctx->htab_used;

  CHECK(decoded != NULL);
  CHECK(ixs_is_parse_error(decoded));
  CHECK(after_used == before_used);
  CHECK(ixs_session_nerrors(&s) == 1);
  CHECK(strstr(ixs_session_error(&s, 0), "implementation limit") != NULL);

  buffer_destroy(&buf);
  destroy_session(ctx, &s);
}

int main(void) {
  test_roundtrip_deterministic();
  test_singletons_and_sentinels();
  test_writer_failure_no_diagnostics();
  test_bounds_canonical_alias_public();
  test_malformed_root_rejected_without_pollution();
#ifndef IXS_TEST_AMALGAMATION
  test_noncanonical_mul_rejected_on_serialize();
  test_nonpositive_mod_rejected_on_serialize();
#endif
  test_nonpositive_mod_rejected_on_deserialize();
  test_node_limit_rejected_without_pollution();
  if (failures) {
    fprintf(stderr, "%d serialize test(s) failed\n", failures);
    return 1;
  }
  printf("serialize tests passed\n");
  return 0;
}
