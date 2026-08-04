/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include <ixsimpl.h>

#include "bounds.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures;

#define TEST_SERIAL_MAGIC 0x42535849u
#define TEST_SERIAL_VERSION 2u
#define TEST_WIRE_INT 0u
#define TEST_WIRE_RAT 1u
#define TEST_WIRE_SYM 2u
#define TEST_WIRE_ADD 3u
#define TEST_WIRE_MUL 4u
#define TEST_WIRE_FLOOR 5u
#define TEST_WIRE_MOD 7u
#define TEST_WIRE_PIECEWISE 8u
#define TEST_WIRE_MAX 9u
#define TEST_WIRE_MIN 10u
#define TEST_WIRE_XOR 11u
#define TEST_WIRE_AND 13u
#define TEST_WIRE_OR 14u
#define TEST_WIRE_ERROR 16u

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
  const ixs_writer writer = {buffer_write, buf};
  buffer_reset(buf);
  return ixs_serialize_node(s, node, &writer);
}

static ixs_node *deserialize_from_buffer(ixs_session *s,
                                         const byte_buffer *buf) {
  byte_reader reader_state;
  const ixs_reader reader = {reader_read, reader_remaining, &reader_state};

  reader_state.data = buf->data;
  reader_state.len = buf->len;
  reader_state.pos = 0;
  return ixs_deserialize_node(s, &reader);
}

static void store_le32(unsigned char *dst, uint32_t v) {
  /* Match the wire format's little-endian uint32 fields. */
  dst[0] = (unsigned char)(v & 0xffu);
  dst[1] = (unsigned char)((v >> 8) & 0xffu);
  dst[2] = (unsigned char)((v >> 16) & 0xffu);
  dst[3] = (unsigned char)((v >> 24) & 0xffu);
}

static uint32_t load_le32(const unsigned char *src) {
  return (uint32_t)src[0] | ((uint32_t)src[1] << 8) | ((uint32_t)src[2] << 16) |
         ((uint32_t)src[3] << 24);
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

static void append_assoc_node(byte_buffer *buf, uint8_t tag, uint32_t nargs,
                              const uint32_t *args) {
  uint32_t i;
  append_u8(buf, tag);
  append_le32(buf, nargs);
  for (i = 0; i < nargs; i++)
    append_le32(buf, args[i]);
}

static void begin_blob(byte_buffer *buf, uint32_t count) {
  buffer_reset(buf);
  append_le32(buf, TEST_SERIAL_MAGIC);
  append_le32(buf, TEST_SERIAL_VERSION);
  append_le32(buf, count);
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
  ixs_node *z = ixs_sym(s, "z");
  ixs_node *zero = ixs_int(s, 0);
  ixs_node *one = ixs_int(s, 1);
  ixs_node *two = ixs_int(s, 2);
  ixs_node *three = ixs_int(s, 3);
  ixs_node *five = ixs_int(s, 5);
  ixs_node *gt0 = ixs_cmp(s, x, IXS_CMP_GT, zero);
  ixs_node *lt5 = ixs_cmp(s, y, IXS_CMP_LT, five);
  ixs_node *not_lt5 = ixs_not(s, lt5);
  ixs_node *z_nonzero = ixs_cmp(s, z, IXS_CMP_NE, zero);
  ixs_node *assoc_args[3];
  ixs_node *cond_args[3];
  ixs_node *root_args[3];
  ixs_node *cond0;
  ixs_node *vals[2];
  ixs_node *conds[2];
  ixs_node *pw;
  ixs_node *half_up;
  ixs_node *modded;
  ixs_node *arith;

  assoc_args[0] = x;
  assoc_args[1] = y;
  assoc_args[2] = z;
  cond_args[0] = gt0;
  cond_args[1] = not_lt5;
  cond_args[2] = z_nonzero;
  cond0 = ixs_or_many(s, 3, cond_args);
  vals[0] = ixs_add(s, ixs_floor(s, ixs_div(s, ixs_add(s, x, one), two)),
                    ixs_xor_many(s, 3, assoc_args));
  vals[1] = ixs_max_many(s, 3, assoc_args);
  conds[0] = cond0;
  conds[1] = ixs_true(s);
  pw = ixs_pw(s, 2, vals, conds);
  half_up = ixs_ceil(s, ixs_div(s, ixs_add(s, y, three), two));
  modded = ixs_mod(s, ixs_add(s, x, three), five);
  assoc_args[0] = modded;
  assoc_args[1] = half_up;
  assoc_args[2] = z;
  arith = ixs_add(s, ixs_mul(s, two, pw), ixs_min_many(s, 3, assoc_args));
  root_args[0] = gt0;
  root_args[1] = ixs_cmp(s, arith, IXS_CMP_GE, zero);
  root_args[2] = z_nonzero;
  return ixs_and_many(s, 3, root_args);
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

typedef const ixs_node *(*assoc_many_fn)(ixs_session *, uint32_t,
                                         const ixs_node *const *);

static void check_permutation_encoding(
    ixs_session *lhs_s, ixs_session *rhs_s, assoc_many_fn fn, uint8_t tag,
    const ixs_node *lhs_a, const ixs_node *lhs_b, const ixs_node *lhs_c,
    const ixs_node *rhs_a, const ixs_node *rhs_b, const ixs_node *rhs_c,
    byte_buffer *lhs, byte_buffer *rhs) {
  const ixs_node *abc[3] = {lhs_a, lhs_b, lhs_c};
  const ixs_node *cab[3] = {rhs_c, rhs_a, rhs_b};
  const ixs_node *left = fn(lhs_s, 3, abc);
  const ixs_node *right = fn(rhs_s, 3, cab);
  const size_t root_record_size = 1u + 4u + 3u * 4u;

  CHECK(left != NULL);
  CHECK(right != NULL);
  CHECK(left != right);
  CHECK(serialize_to_buffer(lhs_s, left, lhs));
  CHECK(serialize_to_buffer(rhs_s, right, rhs));
  CHECK(lhs->len == rhs->len);
  if (lhs->len == rhs->len)
    CHECK(memcmp(lhs->data, rhs->data, lhs->len) == 0);
  CHECK(lhs->len >= root_record_size + 4u);
  if (lhs->len >= root_record_size + 4u) {
    size_t root_offset = lhs->len - 4u - root_record_size;
    CHECK(lhs->data[root_offset] == tag);
    CHECK(load_le32(lhs->data + root_offset + 1u) == 3u);
  }
}

static void test_associative_permutation_encoding(void) {
  ixs_ctx *lhs_ctx = NULL;
  ixs_ctx *rhs_ctx = NULL;
  ixs_session lhs_s;
  ixs_session rhs_s;
  byte_buffer lhs = {0};
  byte_buffer rhs = {0};
  const ixs_node *lhs_a;
  const ixs_node *lhs_b;
  const ixs_node *lhs_c;
  const ixs_node *rhs_a;
  const ixs_node *rhs_b;
  const ixs_node *rhs_c;

  lhs.fail_after = (size_t)-1;
  rhs.fail_after = (size_t)-1;
  if (!init_session(&lhs_ctx, &lhs_s))
    return;
  if (!init_session(&rhs_ctx, &rhs_s)) {
    destroy_session(lhs_ctx, &lhs_s);
    return;
  }

  lhs_a = ixs_sym(&lhs_s, "serial_assoc_a");
  lhs_b = ixs_sym(&lhs_s, "serial_assoc_b");
  lhs_c = ixs_sym(&lhs_s, "serial_assoc_c");
  rhs_c = ixs_sym(&rhs_s, "serial_assoc_c");
  rhs_a = ixs_sym(&rhs_s, "serial_assoc_a");
  rhs_b = ixs_sym(&rhs_s, "serial_assoc_b");

  check_permutation_encoding(&lhs_s, &rhs_s, ixs_max_many, TEST_WIRE_MAX, lhs_a,
                             lhs_b, lhs_c, rhs_a, rhs_b, rhs_c, &lhs, &rhs);
  check_permutation_encoding(&lhs_s, &rhs_s, ixs_min_many, TEST_WIRE_MIN, lhs_a,
                             lhs_b, lhs_c, rhs_a, rhs_b, rhs_c, &lhs, &rhs);
  check_permutation_encoding(&lhs_s, &rhs_s, ixs_xor_many, TEST_WIRE_XOR, lhs_a,
                             lhs_b, lhs_c, rhs_a, rhs_b, rhs_c, &lhs, &rhs);
  check_permutation_encoding(&lhs_s, &rhs_s, ixs_and_many, TEST_WIRE_AND, lhs_a,
                             lhs_b, lhs_c, rhs_a, rhs_b, rhs_c, &lhs, &rhs);
  check_permutation_encoding(&lhs_s, &rhs_s, ixs_or_many, TEST_WIRE_OR, lhs_a,
                             lhs_b, lhs_c, rhs_a, rhs_b, rhs_c, &lhs, &rhs);
  buffer_destroy(&rhs);
  buffer_destroy(&lhs);
  destroy_session(rhs_ctx, &rhs_s);
  destroy_session(lhs_ctx, &lhs_s);
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
    if (i < 2)
      CHECK(buf.len > 12u && buf.data[12] == TEST_WIRE_INT);
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

static bool arena_is_at_mark(const ixs_arena *arena, ixs_arena_mark mark) {
  return arena->current == mark.chunk &&
         (!arena->current || arena->current->used == mark.used);
}

static ixs_arena_mark arena_test_mark(const ixs_arena *arena) {
  ixs_arena_mark mark;
  mark.chunk = arena->current;
  mark.used = arena->current ? arena->current->used : 0;
  return mark;
}

static void test_facts_create_preds_public(void) {
  ixs_ctx *ctx = NULL;
  ixs_ctx *other_ctx = NULL;
  ixs_session s;
  ixs_session other_s;
  byte_buffer buf = {0};
  ixs_node *base;
  ixs_node *lane;
  ixs_node *divisor;
  ixs_node *divisor_eight;
  ixs_node *quotient;
  ixs_node *projected;
  ixs_node *query;
  ixs_node *domain;
  ixs_node *decoded_domain;
  ixs_node *other_divisor;
  ixs_node *other_divisor_eight;
  ixs_node *other_query;
  ixs_node *predicates[2];
  ixs_node *invalid[2];
  ixs_node *wrong_context[2];
  ixs_node *contradiction;
  ixs_arena *scratch;
  ixs_arena_mark mark;
  ixs_facts *raw;
  ixs_facts *closed;
  ixs_facts *empty;
  ixs_facts *contradictory;
  ixs_facts *serialized;
  ixs_facts *fresh;

  buf.fail_after = (size_t)-1;
  CHECK(ixs_facts_create_preds(NULL, NULL, 0) == NULL);
  if (!init_session(&ctx, &s))
    return;
  if (!init_session(&other_ctx, &other_s)) {
    destroy_session(ctx, &s);
    return;
  }
  scratch = &ixs_session_get(&s)->scratch;

  base = ixs_sym(&s, "create_preds_base");
  lane = ixs_sym(&s, "create_preds_lane");
  divisor = ixs_sym(&s, "create_preds_divisor");
  divisor_eight = ixs_cmp(&s, divisor, IXS_CMP_EQ, ixs_int(&s, 8));
  quotient =
      ixs_floor(&s, ixs_div(&s, ixs_mod(&s, lane, ixs_int(&s, 8)), divisor));
  projected =
      ixs_cmp(&s, ixs_add(&s, base, quotient), IXS_CMP_GE, ixs_int(&s, 0));
  query = ixs_cmp(&s, base, IXS_CMP_GE, ixs_int(&s, 0));
  predicates[0] = divisor_eight;
  predicates[1] = projected;

  raw = ixs_facts_create_preds(&s, predicates, 2);
  CHECK(raw != NULL);
  CHECK(ixs_check(&s, query, predicates, 2) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_check_facts(raw, query) == IXS_CHECK_UNKNOWN);

  closed = ixs_facts_create(&s);
  CHECK(closed != NULL);
  CHECK(ixs_facts_assume_preds(closed, predicates, 2));
  CHECK(ixs_check_facts(closed, query) == IXS_CHECK_TRUE);

  empty = ixs_facts_create_preds(&s, NULL, 0);
  CHECK(empty != NULL);
  CHECK(ixs_check_facts(empty, query) == IXS_CHECK_UNKNOWN);

  contradiction = ixs_false(&s);
  contradictory = ixs_facts_create_preds(&s, &contradiction, 1);
  CHECK(contradictory != NULL);
  CHECK(ixs_check_facts(contradictory, query) == IXS_CHECK_UNKNOWN);

  domain = ixs_and(&s, divisor_eight, projected);
  CHECK(serialize_to_buffer(&s, domain, &buf));
  decoded_domain = deserialize_from_buffer(&other_s, &buf);
  CHECK(decoded_domain != NULL);
  CHECK(!ixs_is_error(decoded_domain));
  serialized = ixs_facts_create_preds(&other_s, &decoded_domain, 1);
  CHECK(serialized != NULL);
  other_divisor = ixs_sym(&other_s, "create_preds_divisor");
  other_divisor_eight =
      ixs_cmp(&other_s, other_divisor, IXS_CMP_EQ, ixs_int(&other_s, 8));
  other_query = ixs_cmp(&other_s, ixs_sym(&other_s, "create_preds_base"),
                        IXS_CMP_GE, ixs_int(&other_s, 0));
  CHECK(ixs_check_facts(serialized, other_divisor_eight) == IXS_CHECK_TRUE);
  CHECK(ixs_check_facts(serialized, other_query) == IXS_CHECK_UNKNOWN);

  invalid[0] = divisor_eight;
  invalid[1] = ixs_or(&s, divisor_eight, projected);
  ixs_session_clear_errors(&s);
  mark = arena_test_mark(scratch);
  CHECK(ixs_facts_create_preds(&s, invalid, 2) == NULL);
  CHECK(arena_is_at_mark(scratch, mark));
  CHECK(ixs_session_nerrors(&s) == 1);
  CHECK(strstr(ixs_session_error(&s, 0), "assumptions: OR") != NULL);
  CHECK(ixs_check_facts(raw, query) == IXS_CHECK_UNKNOWN);

  ixs_session_clear_errors(&s);
  mark = arena_test_mark(scratch);
  CHECK(ixs_facts_create_preds(&s, NULL, 1) == NULL);
  CHECK(arena_is_at_mark(scratch, mark));
  CHECK(ixs_session_nerrors(&s) == 1);
  CHECK(strstr(ixs_session_error(&s, 0), "NULL array") != NULL);

  wrong_context[0] = divisor_eight;
  wrong_context[1] = decoded_domain;
  ixs_session_clear_errors(&s);
  mark = arena_test_mark(scratch);
  CHECK(ixs_facts_create_preds(&s, wrong_context, 2) == NULL);
  CHECK(arena_is_at_mark(scratch, mark));
  CHECK(ixs_session_nerrors(&s) == 1);
  CHECK(strstr(ixs_session_error(&s, 0), "different context") != NULL);

  ixs_session_clear_errors(&s);
  mark = arena_test_mark(scratch);
  scratch->fail_after = 1;
  CHECK(ixs_facts_create_preds(&s, predicates, 2) == NULL);
  scratch->fail_after = IXS_ARENA_FAILURE_DISABLED;
  CHECK(arena_is_at_mark(scratch, mark));
  CHECK(ixs_session_nerrors(&s) == 0);

  mark = arena_test_mark(scratch);
  ctx->arena.fail_after = 0;
  CHECK(ixs_facts_create_preds(&s, predicates, 2) == NULL);
  ctx->arena.fail_after = IXS_ARENA_FAILURE_DISABLED;
  CHECK(arena_is_at_mark(scratch, mark));
  CHECK(ixs_session_nerrors(&s) == 0);

  fresh = ixs_facts_create_preds(&s, predicates, 2);
  CHECK(fresh != NULL);
  CHECK(ixs_check_facts(fresh, divisor_eight) == IXS_CHECK_TRUE);
  ixs_session_reset(&s);
  CHECK(ixs_check_facts(fresh, divisor_eight) == IXS_CHECK_UNKNOWN);

  fresh = ixs_facts_create_preds(&s, predicates, 2);
  CHECK(fresh != NULL);
  ixs_session_destroy(&s);
  CHECK(ixs_check_facts(fresh, divisor_eight) == IXS_CHECK_UNKNOWN);
  ixs_session_init(&s, ctx);

  buffer_destroy(&buf);
  destroy_session(other_ctx, &other_s);
  destroy_session(ctx, &s);
}

static void test_facts_assume_preds_order_and_identity(void) {
  ixs_ctx *ctx = NULL;
  ixs_session s;
  byte_buffer buf = {0};
  ixs_node *raw;
  ixs_node *canonical;
  ixs_node *divisor;
  ixs_node *divisor_eight;
  ixs_node *fallback;
  ixs_node *conditions[2];
  ixs_node *raw_values[2];
  ixs_node *canonical_values[2];
  ixs_node *raw_predicate;
  ixs_node *canonical_predicate;
  ixs_node *query;
  ixs_node *repeated[3];
  ixs_node *distinct[3];
  ixs_facts *first_position;
  ixs_facts *distinct_inputs;

  buf.fail_after = (size_t)-1;
  if (!init_session(&ctx, &s))
    return;

  build_bounds_alias_blob(&buf);
  raw = deserialize_from_buffer(&s, &buf);
  canonical = ixs_mul(&s, ixs_sym(&s, "outer"), ixs_sym(&s, "x"));
  divisor = ixs_sym(&s, "duplicate_identity_divisor");
  divisor_eight = ixs_cmp(&s, divisor, IXS_CMP_EQ, ixs_int(&s, 8));
  fallback = ixs_sym(&s, "duplicate_identity_fallback");
  conditions[0] = divisor_eight;
  conditions[1] = ixs_true(&s);
  raw_values[0] = raw;
  raw_values[1] = fallback;
  canonical_values[0] = canonical;
  canonical_values[1] = fallback;
  raw_predicate = ixs_cmp(&s, ixs_pw(&s, 2, raw_values, conditions), IXS_CMP_GE,
                          ixs_int(&s, 0));
  canonical_predicate = ixs_cmp(&s, ixs_pw(&s, 2, canonical_values, conditions),
                                IXS_CMP_GE, ixs_int(&s, 0));
  query = ixs_cmp(&s, canonical, IXS_CMP_GE, ixs_int(&s, 0));

  CHECK(raw != NULL);
  CHECK(!ixs_is_error(raw));
  CHECK(!ixs_same_node(raw, canonical));
  CHECK(ixs_same_node(ixs_simplify(&s, raw, NULL, 0), canonical));
  CHECK(!ixs_same_node(raw_predicate, canonical_predicate));

  repeated[0] = canonical_predicate;
  repeated[1] = divisor_eight;
  repeated[2] = canonical_predicate;
  first_position = ixs_facts_create(&s);
  CHECK(first_position != NULL);
  CHECK(ixs_facts_assume_preds(first_position, repeated, 3));
  CHECK(ixs_check_facts(first_position, query) == IXS_CHECK_UNKNOWN);

  distinct[0] = raw_predicate;
  distinct[1] = divisor_eight;
  distinct[2] = canonical_predicate;
  distinct_inputs = ixs_facts_create(&s);
  CHECK(distinct_inputs != NULL);
  CHECK(ixs_facts_assume_preds(distinct_inputs, distinct, 3));
  CHECK(ixs_check_facts(distinct_inputs, query) == IXS_CHECK_TRUE);

  buffer_destroy(&buf);
  destroy_session(ctx, &s);
}

static ixs_node *build_duplicate_expensive_predicate(ixs_session *s) {
  ixs_node *x = ixs_sym(s, "duplicate_expensive_x");
  ixs_node *selector = ixs_sym(s, "duplicate_expensive_selector");
  ixs_node *values[2] = {x, ixs_sub(s, ixs_int(s, 0), x)};
  ixs_node *conditions[2] = {ixs_cmp(s, selector, IXS_CMP_GT, ixs_int(s, 0)),
                             ixs_true(s)};
  ixs_node *piecewise = ixs_pw(s, 2, values, conditions);
  return ixs_cmp(s, piecewise, IXS_CMP_GE, ixs_int(s, 0));
}

static void test_facts_assume_preds_duplicate_skip(void) {
  enum { DUPLICATE_COUNT = 300 };
  const size_t budget = 1024;
  ixs_ctx *measure_ctx = NULL;
  ixs_ctx *test_ctx = NULL;
  ixs_session measure_session;
  ixs_session test_session;
  ixs_node *measure_predicate;
  ixs_node *test_predicate;
  ixs_node *duplicates[DUPLICATE_COUNT];
  ixs_node *prefix;
  ixs_arena *test_scratch;
  ixs_arena_mark before_batch;
  ixs_arena_mark before_oom;
  ixs_arena_mark base_mark;
  ixs_facts *measure_facts;
  ixs_facts *test_facts;
  ixs_facts *oom_facts;
  ixs_bounds before;
  size_t allocations;
  size_t fork_allocations;
  size_t i;

  if (!init_session(&measure_ctx, &measure_session))
    return;
  if (!init_session(&test_ctx, &test_session)) {
    destroy_session(measure_ctx, &measure_session);
    return;
  }

  measure_predicate = build_duplicate_expensive_predicate(&measure_session);
  test_predicate = build_duplicate_expensive_predicate(&test_session);
  measure_facts = ixs_facts_create(&measure_session);
  test_facts = ixs_facts_create(&test_session);
  CHECK(measure_facts != NULL);
  CHECK(test_facts != NULL);

  ixs_session_get(&measure_session)->scratch.fail_after = budget;
  CHECK(ixs_facts_assume_pred(measure_facts, measure_predicate));
  allocations = budget - ixs_session_get(&measure_session)->scratch.fail_after;
  ixs_session_get(&measure_session)->scratch.fail_after =
      IXS_ARENA_FAILURE_DISABLED;
  CHECK(allocations > 0);

  for (i = 0; i < DUPLICATE_COUNT; i++)
    duplicates[i] = test_predicate;
  test_scratch = &ixs_session_get(&test_session)->scratch;
  before_batch = arena_test_mark(test_scratch);
  test_scratch->fail_after = allocations + 1u;
  CHECK(ixs_facts_assume_preds(test_facts, duplicates, DUPLICATE_COUNT));
  CHECK(test_scratch->fail_after == 0);
  test_scratch->fail_after = IXS_ARENA_FAILURE_DISABLED;
  CHECK(!arena_is_at_mark(test_scratch, before_batch));
  CHECK(ixs_check_facts(test_facts, test_predicate) == IXS_CHECK_TRUE);

  prefix =
      ixs_cmp(&test_session, ixs_sym(&test_session, "duplicate_set_oom_prefix"),
              IXS_CMP_GE, ixs_int(&test_session, 0));
  oom_facts = ixs_facts_create(&test_session);
  CHECK(oom_facts != NULL);
  CHECK(ixs_facts_assume_pred(oom_facts, prefix));
  before = oom_facts->bounds;
  fork_allocations = 1u + 2u * (before.nexprs != 0u) + (before.nnonzero != 0u);
  ixs_session_clear_errors(&test_session);
  before_oom = arena_test_mark(test_scratch);
  test_scratch->fail_after = fork_allocations;
  CHECK(!ixs_facts_assume_preds(oom_facts, duplicates, DUPLICATE_COUNT));
  CHECK(test_scratch->fail_after == 0);
  test_scratch->fail_after = IXS_ARENA_FAILURE_DISABLED;
  CHECK(arena_is_at_mark(test_scratch, before_oom));
  CHECK(ixs_session_nerrors(&test_session) == 0);
  CHECK(!oom_facts->usable);
  CHECK(oom_facts->bounds.vars == before.vars);
  CHECK(oom_facts->bounds.nvars == before.nvars);
  CHECK(oom_facts->bounds.exprs == before.exprs);
  CHECK(oom_facts->bounds.nexprs == before.nexprs);
  CHECK(oom_facts->bounds.expr_index == before.expr_index);
  CHECK(oom_facts->bounds.expr_index_cap == before.expr_index_cap);
  CHECK(oom_facts->bounds.nonzero == before.nonzero);
  CHECK(oom_facts->bounds.nnonzero == before.nnonzero);

  base_mark = ixs_session_get(&test_session)->base_mark;
  ixs_session_reset(&test_session);
  test_scratch = &ixs_session_get(&test_session)->scratch;
  CHECK(arena_is_at_mark(test_scratch, base_mark));
  CHECK(ixs_check_facts(test_facts, test_predicate) == IXS_CHECK_UNKNOWN);

  destroy_session(test_ctx, &test_session);
  destroy_session(measure_ctx, &measure_session);
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

static void test_associative_payload_validation(void) {
  static const uint8_t assoc_tags[] = {
      TEST_WIRE_MAX, TEST_WIRE_MIN, TEST_WIRE_XOR, TEST_WIRE_AND, TEST_WIRE_OR};
  static const assoc_many_fn assoc_fns[] = {
      ixs_max_many, ixs_min_many, ixs_xor_many, ixs_and_many, ixs_or_many};
  static const uint8_t empty_invalid[] = {TEST_WIRE_MAX, TEST_WIRE_MIN};
  static const uint8_t empty_identity[] = {TEST_WIRE_XOR, TEST_WIRE_AND,
                                           TEST_WIRE_OR};
  static const uint32_t inner_args[] = {0u, 1u};
  static const uint32_t outer_args[] = {2u, 3u, 1u};
  ixs_ctx *ctx = NULL;
  ixs_session s;
  byte_buffer buf = {0};
  uint32_t child = 0;
  size_t i;

  buf.fail_after = (size_t)-1;
  if (!init_session(&ctx, &s))
    return;

  for (i = 0; i < sizeof(empty_invalid) / sizeof(empty_invalid[0]); i++) {
    ixs_node *decoded;
    size_t before_used = ctx->htab_used;
    begin_blob(&buf, 1);
    append_assoc_node(&buf, empty_invalid[i], 0, NULL);
    append_le32(&buf, 0);
    ixs_session_clear_errors(&s);
    decoded = deserialize_from_buffer(&s, &buf);
    CHECK(decoded && ixs_is_parse_error(decoded));
    CHECK(ctx->htab_used == before_used);
    CHECK(ixs_session_nerrors(&s) == 1);
    CHECK(strstr(ixs_session_error(&s, 0), "no operands") != NULL);
  }

  for (i = 0; i < sizeof(empty_identity) / sizeof(empty_identity[0]); i++) {
    ixs_node *decoded;
    int64_t expected = empty_identity[i] == TEST_WIRE_AND ? -1 : 0;
    begin_blob(&buf, 1);
    append_assoc_node(&buf, empty_identity[i], 0, NULL);
    append_le32(&buf, 0);
    ixs_session_clear_errors(&s);
    decoded = deserialize_from_buffer(&s, &buf);
    CHECK(decoded && ixs_node_tag(decoded) == IXS_INT);
    CHECK(ixs_node_int_val(decoded) == expected);
    CHECK(ixs_session_nerrors(&s) == 0);
  }

  begin_blob(&buf, 2);
  append_int_node(&buf, 7);
  append_assoc_node(&buf, TEST_WIRE_MAX, 1, &child);
  append_le32(&buf, 1);
  ixs_session_clear_errors(&s);
  {
    ixs_node *decoded = deserialize_from_buffer(&s, &buf);
    CHECK(decoded && ixs_node_tag(decoded) == IXS_INT);
    CHECK(ixs_node_int_val(decoded) == 7);
    CHECK(ixs_session_nerrors(&s) == 0);
  }

  for (i = 0; i < sizeof(assoc_tags) / sizeof(assoc_tags[0]); i++) {
    const ixs_node *args[4];
    const ixs_node *decoded;
    const ixs_node *expected;

    begin_blob(&buf, 5);
    append_sym_node(&buf, "serial_noncanonical_c");
    append_sym_node(&buf, "serial_noncanonical_a");
    append_sym_node(&buf, "serial_noncanonical_b");
    append_assoc_node(&buf, assoc_tags[i], 2, inner_args);
    append_assoc_node(&buf, assoc_tags[i], 3, outer_args);
    append_le32(&buf, 4);
    ixs_session_clear_errors(&s);
    decoded = deserialize_from_buffer(&s, &buf);

    args[0] = ixs_sym(&s, "serial_noncanonical_b");
    args[1] = ixs_sym(&s, "serial_noncanonical_c");
    args[2] = ixs_sym(&s, "serial_noncanonical_a");
    args[3] = args[2];
    expected = assoc_fns[i](&s, 4, args);
    CHECK(decoded != NULL && !ixs_is_error(decoded));
    CHECK(ixs_same_node(decoded, expected));
    CHECK(ixs_session_nerrors(&s) == 0);
  }

  begin_blob(&buf, 2);
  append_rat_node(&buf, 1, 2);
  append_assoc_node(&buf, TEST_WIRE_XOR, 1, &child);
  append_le32(&buf, 1);
  {
    ixs_node *decoded;
    size_t before_used = ctx->htab_used;
    ixs_session_clear_errors(&s);
    decoded = deserialize_from_buffer(&s, &buf);
    CHECK(decoded && ixs_is_parse_error(decoded));
    CHECK(ctx->htab_used == before_used);
    CHECK(ixs_session_nerrors(&s) == 1);
    CHECK(strstr(ixs_session_error(&s, 0), "not integer-valued") != NULL);
  }

  {
    uint32_t rat_child = 0u;
    uint32_t max_child = 1u;
    ixs_node *decoded;
    size_t before_used;

    begin_blob(&buf, 3);
    append_rat_node(&buf, 23456789, 23456791);
    append_assoc_node(&buf, TEST_WIRE_MAX, 1, &rat_child);
    append_assoc_node(&buf, TEST_WIRE_XOR, 1, &max_child);
    append_le32(&buf, 2);
    before_used = ctx->htab_used;
    ixs_session_clear_errors(&s);
    decoded = deserialize_from_buffer(&s, &buf);
    CHECK(decoded && ixs_is_parse_error(decoded));
    CHECK(ctx->htab_used == before_used);
    CHECK(ixs_session_nerrors(&s) == 1);
    CHECK(strstr(ixs_session_error(&s, 0), "constructor rejected") != NULL);
  }

  {
    uint32_t negative_child = 1u;
    ixs_node *decoded;
    size_t before_used;

    begin_blob(&buf, 4);
    append_sym_node(&buf, "serial_hidden_negative_mod");
    append_int_node(&buf, -3);
    append_assoc_node(&buf, TEST_WIRE_MAX, 1, &negative_child);
    append_u8(&buf, TEST_WIRE_MOD);
    append_le32(&buf, 0);
    append_le32(&buf, 2);
    append_le32(&buf, 3);
    before_used = ctx->htab_used;
    ixs_session_clear_errors(&s);
    decoded = deserialize_from_buffer(&s, &buf);
    CHECK(decoded && ixs_is_parse_error(decoded));
    CHECK(ctx->htab_used == before_used);
    CHECK(ixs_session_nerrors(&s) == 1);
    CHECK(strstr(ixs_session_error(&s, 0), "constructor rejected") != NULL);
  }

  {
    ixs_node *decoded;
    size_t before_used;

    begin_blob(&buf, 3);
    append_int_node(&buf, 42);
    append_int_node(&buf, 0);
    append_u8(&buf, TEST_WIRE_PIECEWISE);
    append_le32(&buf, 1);
    append_le32(&buf, 0);
    append_le32(&buf, 1);
    append_le32(&buf, 2);
    before_used = ctx->htab_used;
    ixs_session_clear_errors(&s);
    decoded = deserialize_from_buffer(&s, &buf);
    CHECK(decoded && ixs_is_parse_error(decoded));
    CHECK(ctx->htab_used == before_used);
    CHECK(ixs_session_nerrors(&s) == 1);
    CHECK(strstr(ixs_session_error(&s, 0), "constructor rejected") != NULL);
  }

  begin_blob(&buf, 2);
  append_u8(&buf, TEST_WIRE_ERROR);
  append_assoc_node(&buf, TEST_WIRE_OR, 1, &child);
  append_le32(&buf, 1);
  {
    ixs_node *decoded;
    size_t before_used = ctx->htab_used;
    ixs_session_clear_errors(&s);
    decoded = deserialize_from_buffer(&s, &buf);
    CHECK(decoded && ixs_is_parse_error(decoded));
    CHECK(ctx->htab_used == before_used);
    CHECK(ixs_session_nerrors(&s) == 1);
    CHECK(strstr(ixs_session_error(&s, 0), "sentinel") != NULL);
  }

  begin_blob(&buf, 2);
  append_int_node(&buf, 123456789);
  append_u8(&buf, TEST_WIRE_MAX);
  {
    ixs_node *decoded;
    size_t before_used = ctx->htab_used;
    ixs_session_clear_errors(&s);
    decoded = deserialize_from_buffer(&s, &buf);
    CHECK(decoded && ixs_is_parse_error(decoded));
    CHECK(ctx->htab_used == before_used);
    CHECK(ixs_session_nerrors(&s) == 1);
    CHECK(strstr(ixs_session_error(&s, 0), "argument count") != NULL);
  }

  begin_blob(&buf, 2);
  append_int_node(&buf, 123456790);
  append_u8(&buf, TEST_WIRE_MAX);
  append_le32(&buf, 2);
  append_le32(&buf, 0);
  {
    ixs_node *decoded;
    size_t before_used = ctx->htab_used;
    ixs_session_clear_errors(&s);
    decoded = deserialize_from_buffer(&s, &buf);
    CHECK(decoded && ixs_is_parse_error(decoded));
    CHECK(ctx->htab_used == before_used);
    CHECK(ixs_session_nerrors(&s) == 1);
    CHECK(strstr(ixs_session_error(&s, 0), "payload exceeds") != NULL);
  }

  buffer_destroy(&buf);
  destroy_session(ctx, &s);
}

static void test_version_mismatch_stops_at_header(void) {
  static const uint32_t versions[] = {1u, 3u};
  ixs_ctx *ctx = NULL;
  ixs_session s;
  unsigned char blob[12];
  size_t i;

  if (!init_session(&ctx, &s))
    return;
  for (i = 0; i < sizeof(versions) / sizeof(versions[0]); i++) {
    byte_reader state;
    const ixs_reader reader = {reader_read, reader_remaining, &state};
    ixs_node *decoded;
    size_t before_used = ctx->htab_used;

    store_le32(blob, TEST_SERIAL_MAGIC);
    store_le32(blob + 4u, versions[i]);
    store_le32(blob + 8u, UINT32_MAX);
    state.data = blob;
    state.len = sizeof(blob);
    state.pos = 0;
    ixs_session_clear_errors(&s);
    decoded = ixs_deserialize_node(&s, &reader);
    CHECK(decoded != NULL && ixs_is_parse_error(decoded));
    CHECK(state.pos == 8u);
    CHECK(ctx->htab_used == before_used);
    CHECK(ixs_session_nerrors(&s) == 1u);
  }
  destroy_session(ctx, &s);
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

static void test_noncanonical_assoc_rejected_on_serialize(void) {
  ixs_ctx *ctx = NULL;
  ixs_session s;
  byte_buffer buf = {0};
  ixs_node *x;
  ixs_node *y;
  ixs_node *rat;
  ixs_node *inner;
  ixs_node *bad;
  ixs_node *args[2];

  buf.fail_after = (size_t)-1;
  if (!init_session(&ctx, &s))
    return;

  x = ixs_sym(&s, "serial_raw_assoc_x");
  y = ixs_sym(&s, "serial_raw_assoc_y");
  rat = ixs_rat(&s, 1, 2);

  bad = ixs_node_assoc(ctx, IXS_MAX, 0, NULL);
  CHECK(bad != NULL);
  ixs_session_clear_errors(&s);
  CHECK(!serialize_to_buffer(&s, bad, &buf));
  CHECK(buf.len == 0);
  CHECK(ixs_session_nerrors(&s) == 1);

  args[0] = rat;
  args[1] = x;
  bad = ixs_node_assoc(ctx, IXS_XOR, 2, args);
  CHECK(bad != NULL);
  ixs_session_clear_errors(&s);
  CHECK(!serialize_to_buffer(&s, bad, &buf));
  CHECK(buf.len == 0);
  CHECK(ixs_session_nerrors(&s) == 1);

  inner = ixs_max(&s, x, y);
  args[0] = inner;
  args[1] = x;
  bad = ixs_node_assoc(ctx, IXS_MAX, 2, args);
  CHECK(bad != NULL);
  ixs_session_clear_errors(&s);
  CHECK(!serialize_to_buffer(&s, bad, &buf));
  CHECK(buf.len == 0);
  CHECK(ixs_session_nerrors(&s) == 1);

  buffer_destroy(&buf);
  destroy_session(ctx, &s);
}

static void test_raw_child_count_limits(void) {
  ixs_ctx *ctx = NULL;
  ixs_session s;
  ixs_node *zero;

  if (!init_session(&ctx, &s))
    return;
  zero = ixs_int(&s, 0);

  CHECK(ixs_node_add(ctx, zero, (UINT32_MAX - 1u) / 2u + 1u, NULL) == NULL);
  CHECK(ixs_node_mul(ctx, zero, UINT32_MAX, NULL) == NULL);
  CHECK(ixs_node_pw(ctx, UINT32_MAX / 2u + 1u, NULL) == NULL);
  CHECK(ixs_is_domain_error(ixs_pw(&s, UINT32_MAX / 2u + 1u, NULL, NULL)));

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
  test_associative_permutation_encoding();
  test_singletons_and_sentinels();
  test_writer_failure_no_diagnostics();
  test_bounds_canonical_alias_public();
  test_facts_create_preds_public();
  test_facts_assume_preds_order_and_identity();
  test_facts_assume_preds_duplicate_skip();
  test_malformed_root_rejected_without_pollution();
  test_associative_payload_validation();
  test_version_mismatch_stops_at_header();
#ifndef IXS_TEST_AMALGAMATION
  test_noncanonical_mul_rejected_on_serialize();
  test_noncanonical_assoc_rejected_on_serialize();
  test_raw_child_count_limits();
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
