/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "node.h"

#include "rational.h"

#include <limits.h>
#include <string.h>

#define SERIAL_MAGIC 0x42535849u /* "IXSB" */
#define SERIAL_VERSION 1u

#define SERIAL_MEMO_INIT_CAP 64u
#define SERIAL_STACK_INIT_CAP 64u
#define SERIAL_ORDER_INIT_CAP 64u
#define SERIAL_INDEX_PENDING UINT32_MAX
/* Bound hostile inputs: tiny blobs must not demand unbounded scratch or work.
 */
#define SERIAL_MAX_NODE_COUNT 1048576u

/*
 * These numeric values are the v1 wire ABI. Keep them frozen even if the
 * public enums move later.
 */
typedef enum {
  WIRE_INT = 0,
  WIRE_RAT = 1,
  WIRE_SYM = 2,
  WIRE_ADD = 3,
  WIRE_MUL = 4,
  WIRE_FLOOR = 5,
  WIRE_CEIL = 6,
  WIRE_MOD = 7,
  WIRE_PIECEWISE = 8,
  WIRE_MAX = 9,
  WIRE_MIN = 10,
  WIRE_XOR = 11,
  WIRE_CMP = 12,
  WIRE_AND = 13,
  WIRE_OR = 14,
  WIRE_NOT = 15,
  WIRE_TRUE = 16,
  WIRE_FALSE = 17,
  WIRE_ERROR = 18,
  WIRE_PARSE_ERROR = 19
} wire_tag;

typedef enum {
  WIRE_CMP_GT = 0,
  WIRE_CMP_GE = 1,
  WIRE_CMP_LT = 2,
  WIRE_CMP_LE = 3,
  WIRE_CMP_EQ = 4,
  WIRE_CMP_NE = 5
} wire_cmp_op;

typedef struct {
  const ixs_node *node;
  uint32_t index;
} serial_entry;

typedef struct {
  const ixs_node *node;
  uint32_t next_child;
} serial_frame;

typedef struct {
  serial_entry *memo;
  size_t memo_cap;
  size_t memo_used;
  serial_frame *stack;
  size_t stack_cap;
  const ixs_node **order;
  size_t order_cap;
  size_t order_used;
} serial_state;

typedef struct {
  uint32_t term;
  uint32_t coeff;
} decode_addterm;

typedef struct {
  uint32_t base;
  int32_t exp;
} decode_mulfactor;

typedef struct {
  uint32_t value;
  uint32_t cond;
} decode_pwcase;

typedef struct {
  wire_tag tag;
  union {
    int64_t ival;
    struct {
      int64_t p;
      int64_t q;
    } rat;
    struct {
      char *name;
      uint32_t len;
    } sym;
    struct {
      uint32_t coeff;
      uint32_t nterms;
      decode_addterm *terms;
    } add;
    struct {
      uint32_t coeff;
      uint32_t nfactors;
      decode_mulfactor *factors;
    } mul;
    struct {
      uint32_t arg;
    } unary;
    struct {
      uint32_t lhs;
      uint32_t rhs;
      wire_cmp_op op;
    } binary;
    struct {
      uint32_t ncases;
      decode_pwcase *cases;
    } pw;
    struct {
      uint32_t nargs;
      uint32_t *args;
    } logic;
  } u;
} decode_node;

typedef struct {
  ixs_reader *reader;
  size_t offset;
} decode_input;

typedef enum { DECODE_OK, DECODE_PARSE_ERROR, DECODE_OOM } decode_status;

static bool size_mul_ok(size_t a, size_t b, size_t *out) {
  if (a != 0 && b > (size_t)-1 / a)
    return false;
  *out = a * b;
  return true;
}

static bool size_add_ok(size_t a, size_t b, size_t *out) {
  if (b > (size_t)-1 - a)
    return false;
  *out = a + b;
  return true;
}

static size_t serial_hash_ptr(const void *ptr) {
  uint64_t x = (uint64_t)(uintptr_t)ptr;
  x ^= x >> 33;
  x *= 0xff51afd7ed558ccdULL;
  x ^= x >> 33;
  return (size_t)x;
}

static bool serial_error(ixs_ctx *ctx, const char *msg);

static serial_entry *serial_memo_slot(serial_entry *entries, size_t cap,
                                      const ixs_node *node) {
  size_t mask = cap - 1u;
  size_t idx = serial_hash_ptr(node) & mask;
  while (entries[idx].node && entries[idx].node != node)
    idx = (idx + 1u) & mask;
  return &entries[idx];
}

static bool serial_memo_grow(ixs_ctx *ctx, serial_state *state) {
  size_t new_cap =
      state->memo_cap ? state->memo_cap * 2u : SERIAL_MEMO_INIT_CAP;
  size_t bytes;
  size_t i;
  serial_entry *entries;

  if (new_cap <= state->memo_cap ||
      !size_mul_ok(new_cap, sizeof(*entries), &bytes))
    return false;

  entries = ixs_arena_alloc(&ctx->scratch, bytes, sizeof(void *));
  if (!entries)
    return false;
  memset(entries, 0, bytes);

  for (i = 0; i < state->memo_cap; i++) {
    if (state->memo[i].node) {
      serial_entry *slot =
          serial_memo_slot(entries, new_cap, state->memo[i].node);
      *slot = state->memo[i];
    }
  }

  state->memo = entries;
  state->memo_cap = new_cap;
  return true;
}

static serial_entry *serial_memo_find(serial_state *state,
                                      const ixs_node *node) {
  serial_entry *slot;

  if (!state->memo_cap)
    return NULL;
  slot = serial_memo_slot(state->memo, state->memo_cap, node);
  return slot->node ? slot : NULL;
}

static serial_entry *serial_memo_get_or_insert(ixs_ctx *ctx,
                                               serial_state *state,
                                               const ixs_node *node,
                                               bool *is_new) {
  serial_entry *slot;

  if (!state->memo_cap && !serial_memo_grow(ctx, state))
    return NULL;

  slot = serial_memo_slot(state->memo, state->memo_cap, node);
  if (slot->node) {
    *is_new = false;
    return slot;
  }

  if (state->memo_used + 1u > state->memo_cap - state->memo_cap / 4u) {
    if (!serial_memo_grow(ctx, state))
      return NULL;
    slot = serial_memo_slot(state->memo, state->memo_cap, node);
    if (slot->node) {
      *is_new = false;
      return slot;
    }
  }

  slot->node = node;
  slot->index = SERIAL_INDEX_PENDING;
  state->memo_used++;
  *is_new = true;
  return slot;
}

static bool serial_stack_reserve(ixs_ctx *ctx, serial_state *state,
                                 size_t need) {
  size_t old_cap = state->stack_cap;
  size_t new_cap = old_cap ? old_cap : SERIAL_STACK_INIT_CAP;
  size_t old_bytes;
  size_t new_bytes;
  serial_frame *stack;

  if (need <= old_cap)
    return true;

  while (new_cap < need) {
    size_t doubled = new_cap * 2u;
    if (doubled <= new_cap)
      return false;
    new_cap = doubled;
  }

  if (!size_mul_ok(old_cap, sizeof(*stack), &old_bytes) ||
      !size_mul_ok(new_cap, sizeof(*stack), &new_bytes))
    return false;

  stack = ixs_arena_grow(&ctx->scratch, state->stack, old_bytes, new_bytes,
                         sizeof(void *));
  if (!stack)
    return false;

  state->stack = stack;
  state->stack_cap = new_cap;
  return true;
}

static bool serial_order_reserve(ixs_ctx *ctx, serial_state *state,
                                 size_t need) {
  size_t old_cap = state->order_cap;
  size_t new_cap = old_cap ? old_cap : SERIAL_ORDER_INIT_CAP;
  size_t old_bytes;
  size_t new_bytes;
  const ixs_node **order;

  if (need <= old_cap)
    return true;

  while (new_cap < need) {
    size_t doubled = new_cap * 2u;
    if (doubled <= new_cap)
      return false;
    new_cap = doubled;
  }

  if (!size_mul_ok(old_cap, sizeof(*order), &old_bytes) ||
      !size_mul_ok(new_cap, sizeof(*order), &new_bytes))
    return false;

  order = ixs_arena_grow(&ctx->scratch, state->order, old_bytes, new_bytes,
                         sizeof(void *));
  if (!order)
    return false;

  state->order = order;
  state->order_cap = new_cap;
  return true;
}

/*
 * Keep serial_child_count() and serial_child_at() in lockstep. serial_collect()
 * uses the count to bound next_child and child_at() to walk the exact same
 * per-tag order when it builds the topological node table.
 */
static bool serial_child_count(const ixs_node *node, uint32_t *out) {
  switch (node->tag) {
  case IXS_INT:
  case IXS_RAT:
  case IXS_SYM:
  case IXS_TRUE:
  case IXS_FALSE:
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    *out = 0;
    return true;
  case IXS_ADD:
    if (node->u.add.nterms > (UINT32_MAX - 1u) / 2u)
      return false;
    *out = 1u + 2u * node->u.add.nterms;
    return true;
  case IXS_MUL:
    if (node->u.mul.nfactors == UINT32_MAX)
      return false;
    *out = 1u + node->u.mul.nfactors;
    return true;
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_NOT:
    *out = 1u;
    return true;
  case IXS_MOD:
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_CMP:
    *out = 2u;
    return true;
  case IXS_PIECEWISE:
    if (node->u.pw.ncases > UINT32_MAX / 2u)
      return false;
    *out = 2u * node->u.pw.ncases;
    return true;
  case IXS_AND:
  case IXS_OR:
    *out = node->u.logic.nargs;
    return true;
  }
  return false;
}

static const ixs_node *serial_child_at(const ixs_node *node, uint32_t child) {
  switch (node->tag) {
  case IXS_ADD:
    if (child == 0)
      return node->u.add.coeff;
    child--;
    if ((child & 1u) == 0u)
      return node->u.add.terms[child / 2u].coeff;
    return node->u.add.terms[child / 2u].term;
  case IXS_MUL:
    if (child == 0)
      return node->u.mul.coeff;
    return node->u.mul.factors[child - 1u].base;
  case IXS_FLOOR:
  case IXS_CEIL:
    return node->u.unary.arg;
  case IXS_NOT:
    return node->u.unary_bool.arg;
  case IXS_MOD:
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_CMP:
    return child == 0 ? node->u.binary.lhs : node->u.binary.rhs;
  case IXS_PIECEWISE:
    if ((child & 1u) == 0u)
      return node->u.pw.cases[child / 2u].value;
    return node->u.pw.cases[child / 2u].cond;
  case IXS_AND:
  case IXS_OR:
    return node->u.logic.args[child];
  default:
    return NULL;
  }
}

static bool serial_collect(ixs_ctx *ctx, const ixs_node *root,
                           serial_state *state) {
  serial_entry *slot;
  size_t depth = 0;
  bool is_new;

  if (!root)
    return serial_error(ctx, "root is NULL");

  slot = serial_memo_get_or_insert(ctx, state, root, &is_new);
  if (!slot)
    return false;
  if (!is_new)
    return serial_error(ctx,
                        "root memoization did not start from a fresh slot");

  if (!serial_stack_reserve(ctx, state, 1))
    return false;
  state->stack[depth++] = (serial_frame){root, 0u};

  while (depth > 0) {
    serial_frame *frame = &state->stack[depth - 1u];
    uint32_t nchildren = 0;

    if (!serial_child_count(frame->node, &nchildren))
      return serial_error(ctx, "node has an unencodable child layout");

    if (frame->next_child < nchildren) {
      const ixs_node *child = serial_child_at(frame->node, frame->next_child++);
      serial_entry *child_slot;

      if (!child)
        return serial_error(ctx, "node has a NULL child reference");

      child_slot = serial_memo_get_or_insert(ctx, state, child, &is_new);
      if (!child_slot)
        return false;
      if (is_new) {
        if (!serial_stack_reserve(ctx, state, depth + 1u))
          return false;
        state->stack[depth++] = (serial_frame){child, 0u};
      } else if (child_slot->index == SERIAL_INDEX_PENDING) {
        return serial_error(ctx, "graph contains a cycle");
      }
      continue;
    }

    slot = serial_memo_find(state, frame->node);
    if (!slot || slot->index != SERIAL_INDEX_PENDING)
      return serial_error(ctx, "node table lost track of a pending entry");
    if (state->order_used == UINT32_MAX)
      return serial_error(ctx, "node table exceeds wire-format limits");
    if (!serial_order_reserve(ctx, state, state->order_used + 1u))
      return false;

    slot->index = (uint32_t)state->order_used;
    state->order[state->order_used++] = frame->node;
    depth--;
  }

  return true;
}

static bool writer_write(ixs_writer *w, const void *buf, size_t len) {
  if (!w || !w->write)
    return false;
  if (len == 0)
    return true;
  return w->write(w->userdata, buf, len);
}

static bool writer_u8(ixs_writer *w, uint8_t v) {
  return writer_write(w, &v, 1u);
}

static bool writer_u32(ixs_writer *w, uint32_t v) {
  unsigned char buf[4];
  buf[0] = (unsigned char)(v & 0xffu);
  buf[1] = (unsigned char)((v >> 8) & 0xffu);
  buf[2] = (unsigned char)((v >> 16) & 0xffu);
  buf[3] = (unsigned char)((v >> 24) & 0xffu);
  return writer_write(w, buf, sizeof(buf));
}

static bool writer_i64(ixs_writer *w, int64_t v) {
  unsigned char buf[8];
  uint64_t u = (uint64_t)v;
  size_t i;

  for (i = 0; i < sizeof(buf); i++) {
    buf[i] = (unsigned char)(u & 0xffu);
    u >>= 8;
  }
  return writer_write(w, buf, sizeof(buf));
}

static bool ixs_cmp_to_wire(ixs_cmp_op op, wire_cmp_op *out) {
  switch (op) {
  case IXS_CMP_GT:
    *out = WIRE_CMP_GT;
    return true;
  case IXS_CMP_GE:
    *out = WIRE_CMP_GE;
    return true;
  case IXS_CMP_LT:
    *out = WIRE_CMP_LT;
    return true;
  case IXS_CMP_LE:
    *out = WIRE_CMP_LE;
    return true;
  case IXS_CMP_EQ:
    *out = WIRE_CMP_EQ;
    return true;
  case IXS_CMP_NE:
    *out = WIRE_CMP_NE;
    return true;
  }
  return false;
}

static bool serial_error(ixs_ctx *ctx, const char *msg) {
  ixs_ctx_push_error(ctx, "serialize error: %s", msg);
  return false;
}

static bool serial_lookup_index(serial_state *state, const ixs_node *node,
                                uint32_t *out) {
  serial_entry *slot = serial_memo_find(state, node);
  if (!slot || slot->index == SERIAL_INDEX_PENDING)
    return false;
  *out = slot->index;
  return true;
}

static bool serial_write_ref(ixs_ctx *ctx, ixs_writer *w, serial_state *state,
                             const ixs_node *node) {
  uint32_t index;

  if (!serial_lookup_index(state, node, &index))
    return serial_error(ctx, "child reference is missing from the node table");
  return writer_u32(w, index);
}

static bool serial_write_symbol(ixs_ctx *ctx, ixs_writer *w,
                                const ixs_node *node) {
  size_t len = strlen(node->u.name);

  if (len > UINT32_MAX)
    return serial_error(ctx, "symbol name exceeds wire-format limits");
  return writer_u8(w, WIRE_SYM) && writer_u32(w, (uint32_t)len) &&
         writer_write(w, node->u.name, len);
}

static bool serial_write_add(ixs_ctx *ctx, ixs_writer *w, serial_state *state,
                             const ixs_node *node) {
  uint32_t i;

  if (!writer_u8(w, WIRE_ADD) || !writer_u32(w, node->u.add.nterms) ||
      !serial_write_ref(ctx, w, state, node->u.add.coeff))
    return false;
  for (i = 0; i < node->u.add.nterms; i++) {
    if (!serial_write_ref(ctx, w, state, node->u.add.terms[i].term) ||
        !serial_write_ref(ctx, w, state, node->u.add.terms[i].coeff))
      return false;
  }
  return true;
}

static bool serial_write_mul(ixs_ctx *ctx, ixs_writer *w, serial_state *state,
                             const ixs_node *node) {
  uint32_t i;

  if (!writer_u8(w, WIRE_MUL) || !writer_u32(w, node->u.mul.nfactors) ||
      !serial_write_ref(ctx, w, state, node->u.mul.coeff))
    return false;
  for (i = 0; i < node->u.mul.nfactors; i++) {
    /* Keep writer/reader semantics aligned on noncanonical MUL payloads. */
    if (node->u.mul.factors[i].exp == 0)
      return serial_error(ctx, "MUL factor has zero exponent");
    if (!serial_write_ref(ctx, w, state, node->u.mul.factors[i].base) ||
        !writer_i64(w, (int64_t)node->u.mul.factors[i].exp))
      return false;
  }
  return true;
}

static bool serial_write_unary(ixs_ctx *ctx, ixs_writer *w, serial_state *state,
                               uint8_t tag, const ixs_node *arg) {
  return writer_u8(w, tag) && serial_write_ref(ctx, w, state, arg);
}

static bool serial_write_binary(ixs_ctx *ctx, ixs_writer *w,
                                serial_state *state, uint8_t tag,
                                const ixs_node *lhs, const ixs_node *rhs) {
  return writer_u8(w, tag) && serial_write_ref(ctx, w, state, lhs) &&
         serial_write_ref(ctx, w, state, rhs);
}

static bool serial_write_piecewise(ixs_ctx *ctx, ixs_writer *w,
                                   serial_state *state, const ixs_node *node) {
  uint32_t i;

  if (!writer_u8(w, WIRE_PIECEWISE) || !writer_u32(w, node->u.pw.ncases))
    return false;
  for (i = 0; i < node->u.pw.ncases; i++) {
    if (!serial_write_ref(ctx, w, state, node->u.pw.cases[i].value) ||
        !serial_write_ref(ctx, w, state, node->u.pw.cases[i].cond))
      return false;
  }
  return true;
}

static bool serial_write_cmp(ixs_ctx *ctx, ixs_writer *w, serial_state *state,
                             const ixs_node *node) {
  wire_cmp_op op;

  if (!ixs_cmp_to_wire(node->u.binary.cmp_op, &op))
    return serial_error(ctx, "CMP node has an unknown operator");
  return writer_u8(w, WIRE_CMP) && writer_u8(w, (uint8_t)op) &&
         serial_write_ref(ctx, w, state, node->u.binary.lhs) &&
         serial_write_ref(ctx, w, state, node->u.binary.rhs);
}

static bool serial_write_logic(ixs_ctx *ctx, ixs_writer *w, serial_state *state,
                               const ixs_node *node) {
  wire_tag tag = node->tag == IXS_AND ? WIRE_AND : WIRE_OR;
  uint32_t i;

  if (!writer_u8(w, (uint8_t)tag) || !writer_u32(w, node->u.logic.nargs))
    return false;
  for (i = 0; i < node->u.logic.nargs; i++) {
    if (!serial_write_ref(ctx, w, state, node->u.logic.args[i]))
      return false;
  }
  return true;
}

static bool serial_write_node(ixs_ctx *ctx, ixs_writer *w, serial_state *state,
                              const ixs_node *node) {
  switch (node->tag) {
  case IXS_INT:
    return writer_u8(w, WIRE_INT) && writer_i64(w, node->u.ival);
  case IXS_RAT:
    return writer_u8(w, WIRE_RAT) && writer_i64(w, node->u.rat.p) &&
           writer_i64(w, node->u.rat.q);
  case IXS_SYM:
    return serial_write_symbol(ctx, w, node);
  case IXS_ADD:
    return serial_write_add(ctx, w, state, node);
  case IXS_MUL:
    return serial_write_mul(ctx, w, state, node);
  case IXS_FLOOR:
    return serial_write_unary(ctx, w, state, WIRE_FLOOR, node->u.unary.arg);
  case IXS_CEIL:
    return serial_write_unary(ctx, w, state, WIRE_CEIL, node->u.unary.arg);
  case IXS_MOD:
    return serial_write_binary(ctx, w, state, WIRE_MOD, node->u.binary.lhs,
                               node->u.binary.rhs);
  case IXS_PIECEWISE:
    return serial_write_piecewise(ctx, w, state, node);
  case IXS_MAX:
    return serial_write_binary(ctx, w, state, WIRE_MAX, node->u.binary.lhs,
                               node->u.binary.rhs);
  case IXS_MIN:
    return serial_write_binary(ctx, w, state, WIRE_MIN, node->u.binary.lhs,
                               node->u.binary.rhs);
  case IXS_XOR:
    return serial_write_binary(ctx, w, state, WIRE_XOR, node->u.binary.lhs,
                               node->u.binary.rhs);
  case IXS_CMP:
    return serial_write_cmp(ctx, w, state, node);
  case IXS_AND:
  case IXS_OR:
    return serial_write_logic(ctx, w, state, node);
  case IXS_NOT:
    return serial_write_unary(ctx, w, state, WIRE_NOT, node->u.unary_bool.arg);
  case IXS_TRUE:
    return writer_u8(w, WIRE_TRUE);
  case IXS_FALSE:
    return writer_u8(w, WIRE_FALSE);
  case IXS_ERROR:
    return writer_u8(w, WIRE_ERROR);
  case IXS_PARSE_ERROR:
    return writer_u8(w, WIRE_PARSE_ERROR);
  }
  return serial_error(ctx, "node has an unsupported tag");
}

static decode_status decode_error(ixs_ctx *ctx, const decode_input *in,
                                  const char *msg) {
  ixs_ctx_push_error(ctx, "deserialize error at offset %zu: %s", in->offset,
                     msg);
  return DECODE_PARSE_ERROR;
}

static decode_status reader_read_exact(ixs_ctx *ctx, decode_input *in,
                                       void *buf, size_t len, const char *msg) {
  size_t remaining;

  if (len == 0)
    return DECODE_OK;
  if (!in->reader || !in->reader->read || !in->reader->remaining)
    return decode_error(ctx, in, "invalid reader");

  remaining = in->reader->remaining(in->reader->userdata);
  if (len > remaining)
    return decode_error(ctx, in, msg);
  if (!in->reader->read(in->reader->userdata, buf, len))
    return decode_error(ctx, in, "reader failure");
  in->offset += len;
  return DECODE_OK;
}

static decode_status reader_u8(ixs_ctx *ctx, decode_input *in, uint8_t *out,
                               const char *msg) {
  return reader_read_exact(ctx, in, out, 1u, msg);
}

static decode_status reader_u32(ixs_ctx *ctx, decode_input *in, uint32_t *out,
                                const char *msg) {
  unsigned char buf[4];
  decode_status status = reader_read_exact(ctx, in, buf, sizeof(buf), msg);
  if (status != DECODE_OK)
    return status;
  *out = (uint32_t)buf[0] | ((uint32_t)buf[1] << 8) | ((uint32_t)buf[2] << 16) |
         ((uint32_t)buf[3] << 24);
  return DECODE_OK;
}

static decode_status reader_i64(ixs_ctx *ctx, decode_input *in, int64_t *out,
                                const char *msg) {
  unsigned char buf[8];
  uint64_t u = 0;
  size_t i;
  decode_status status = reader_read_exact(ctx, in, buf, sizeof(buf), msg);
  if (status != DECODE_OK)
    return status;
  for (i = 0; i < sizeof(buf); i++)
    u |= (uint64_t)buf[i] << (8u * i);
  *out = (int64_t)u;
  return DECODE_OK;
}

static size_t reader_remaining_bytes(const decode_input *in) {
  return in->reader->remaining(in->reader->userdata);
}

static decode_status decode_require_bytes(ixs_ctx *ctx, const decode_input *in,
                                          size_t need, const char *msg) {
  if (need > reader_remaining_bytes(in))
    return decode_error(ctx, in, msg);
  return DECODE_OK;
}

static bool decode_is_sentinel(wire_tag tag) {
  return tag == WIRE_ERROR || tag == WIRE_PARSE_ERROR;
}

static bool decode_is_numeric(wire_tag tag) {
  return tag == WIRE_INT || tag == WIRE_RAT;
}

static decode_status decode_validate_child(ixs_ctx *ctx, const decode_input *in,
                                           const decode_node *nodes,
                                           uint32_t index, uint32_t child) {
  if (child >= index)
    return decode_error(ctx, in, "child reference is not earlier in the table");
  if (decode_is_sentinel(nodes[child].tag))
    return decode_error(ctx, in, "compound node references a sentinel child");
  return DECODE_OK;
}

static decode_status decode_validate_numeric(ixs_ctx *ctx,
                                             const decode_input *in,
                                             const decode_node *nodes,
                                             uint32_t index, uint32_t child) {
  decode_status status = decode_validate_child(ctx, in, nodes, index, child);
  if (status != DECODE_OK)
    return status;
  if (!decode_is_numeric(nodes[child].tag))
    return decode_error(ctx, in, "coefficient is not an integer or rational");
  return DECODE_OK;
}

static decode_status decode_validate_rat(ixs_ctx *ctx, const decode_input *in,
                                         int64_t p, int64_t q) {
  int64_t rp;
  int64_t rq;

  if (!ixs_rat_normalize(p, q, &rp, &rq))
    return decode_error(ctx, in, "invalid rational payload");
  if (q == 1 || rp != p || rq != q)
    return decode_error(ctx, in, "rational payload is not normalized");
  return DECODE_OK;
}

static decode_status decode_read_symbol(ixs_ctx *ctx, decode_input *in,
                                        decode_node *node) {
  uint32_t len = 0;
  size_t alloc_len;
  char *name;
  uint32_t i;
  decode_status status = reader_u32(ctx, in, &len, "truncated symbol length");
  if (status != DECODE_OK)
    return status;
  if (!size_add_ok((size_t)len, 1u, &alloc_len))
    return decode_error(ctx, in, "symbol length overflows size_t");
  status = decode_require_bytes(ctx, in, (size_t)len,
                                "symbol length exceeds remaining bytes");
  if (status != DECODE_OK)
    return status;
  name = ixs_arena_alloc(&ctx->scratch, alloc_len, 1u);
  if (!name)
    return DECODE_OOM;
  status = reader_read_exact(ctx, in, name, len, "truncated symbol bytes");
  if (status != DECODE_OK)
    return status;
  for (i = 0; i < len; i++) {
    if (name[i] == '\0')
      return decode_error(ctx, in, "symbol contains an embedded NUL");
  }
  name[len] = '\0';
  node->tag = WIRE_SYM;
  node->u.sym.name = name;
  node->u.sym.len = len;
  return DECODE_OK;
}

static decode_status decode_read_rat_node(ixs_ctx *ctx, decode_input *in,
                                          decode_node *node) {
  decode_status status;

  node->tag = WIRE_RAT;
  status = reader_i64(ctx, in, &node->u.rat.p, "truncated rational numerator");
  if (status != DECODE_OK)
    return status;
  status =
      reader_i64(ctx, in, &node->u.rat.q, "truncated rational denominator");
  if (status != DECODE_OK)
    return status;
  return decode_validate_rat(ctx, in, node->u.rat.p, node->u.rat.q);
}

static decode_status decode_read_add(ixs_ctx *ctx, decode_input *in,
                                     decode_node *nodes, uint32_t index,
                                     decode_node *node) {
  size_t bytes = 0;
  size_t min_bytes = 0;
  uint32_t i;
  decode_status status;

  node->tag = WIRE_ADD;
  status = reader_u32(ctx, in, &node->u.add.nterms, "truncated add term count");
  if (status != DECODE_OK)
    return status;
  status =
      reader_u32(ctx, in, &node->u.add.coeff, "truncated add constant index");
  if (status != DECODE_OK)
    return status;
  status = decode_validate_numeric(ctx, in, nodes, index, node->u.add.coeff);
  if (status != DECODE_OK)
    return status;
  if (!size_mul_ok((size_t)node->u.add.nterms, sizeof(*node->u.add.terms),
                   &bytes))
    return decode_error(ctx, in, "add term count overflows size_t");
  if (!size_mul_ok((size_t)node->u.add.nterms, 2u * sizeof(uint32_t),
                   &min_bytes))
    return decode_error(ctx, in, "add term payload overflows size_t");
  status = decode_require_bytes(ctx, in, min_bytes,
                                "add term payload exceeds remaining bytes");
  if (status != DECODE_OK)
    return status;

  node->u.add.terms = NULL;
  if (bytes > 0) {
    node->u.add.terms = ixs_arena_alloc(&ctx->scratch, bytes, sizeof(void *));
    if (!node->u.add.terms)
      return DECODE_OOM;
  }

  for (i = 0; i < node->u.add.nterms; i++) {
    status = reader_u32(ctx, in, &node->u.add.terms[i].term,
                        "truncated add term index");
    if (status != DECODE_OK)
      return status;
    status =
        decode_validate_child(ctx, in, nodes, index, node->u.add.terms[i].term);
    if (status != DECODE_OK)
      return status;
    status = reader_u32(ctx, in, &node->u.add.terms[i].coeff,
                        "truncated add coefficient index");
    if (status != DECODE_OK)
      return status;
    status = decode_validate_numeric(ctx, in, nodes, index,
                                     node->u.add.terms[i].coeff);
    if (status != DECODE_OK)
      return status;
  }

  return DECODE_OK;
}

static decode_status decode_read_mul(ixs_ctx *ctx, decode_input *in,
                                     decode_node *nodes, uint32_t index,
                                     decode_node *node) {
  size_t bytes = 0;
  size_t min_bytes = 0;
  uint32_t i;
  decode_status status;

  node->tag = WIRE_MUL;
  status = reader_u32(ctx, in, &node->u.mul.nfactors,
                      "truncated multiply factor count");
  if (status != DECODE_OK)
    return status;
  status = reader_u32(ctx, in, &node->u.mul.coeff,
                      "truncated multiply coefficient index");
  if (status != DECODE_OK)
    return status;
  status = decode_validate_numeric(ctx, in, nodes, index, node->u.mul.coeff);
  if (status != DECODE_OK)
    return status;
  if (!size_mul_ok((size_t)node->u.mul.nfactors, sizeof(*node->u.mul.factors),
                   &bytes))
    return decode_error(ctx, in, "multiply factor count overflows size_t");
  if (!size_mul_ok((size_t)node->u.mul.nfactors,
                   sizeof(uint32_t) + sizeof(int64_t), &min_bytes))
    return decode_error(ctx, in, "multiply payload overflows size_t");
  status = decode_require_bytes(ctx, in, min_bytes,
                                "multiply payload exceeds remaining bytes");
  if (status != DECODE_OK)
    return status;

  node->u.mul.factors = NULL;
  if (bytes > 0) {
    node->u.mul.factors = ixs_arena_alloc(&ctx->scratch, bytes, sizeof(void *));
    if (!node->u.mul.factors)
      return DECODE_OOM;
  }

  for (i = 0; i < node->u.mul.nfactors; i++) {
    int64_t exp64 = 0;

    status = reader_u32(ctx, in, &node->u.mul.factors[i].base,
                        "truncated multiply base index");
    if (status != DECODE_OK)
      return status;
    status = decode_validate_child(ctx, in, nodes, index,
                                   node->u.mul.factors[i].base);
    if (status != DECODE_OK)
      return status;
    status = reader_i64(ctx, in, &exp64, "truncated multiply exponent");
    if (status != DECODE_OK)
      return status;
    if (exp64 < INT32_MIN || exp64 > INT32_MAX || exp64 == 0)
      return decode_error(ctx, in, "multiply exponent does not fit int32");
    node->u.mul.factors[i].exp = (int32_t)exp64;
  }

  return DECODE_OK;
}

static decode_status decode_read_unary(ixs_ctx *ctx, decode_input *in,
                                       decode_node *nodes, uint32_t index,
                                       decode_node *node, wire_tag tag) {
  decode_status status;

  node->tag = tag;
  status =
      reader_u32(ctx, in, &node->u.unary.arg, "truncated unary child index");
  if (status != DECODE_OK)
    return status;
  return decode_validate_child(ctx, in, nodes, index, node->u.unary.arg);
}

static decode_status decode_read_binary(ixs_ctx *ctx, decode_input *in,
                                        decode_node *nodes, uint32_t index,
                                        decode_node *node, wire_tag tag) {
  decode_status status;

  node->tag = tag;
  status =
      reader_u32(ctx, in, &node->u.binary.lhs, "truncated binary lhs index");
  if (status != DECODE_OK)
    return status;
  status = decode_validate_child(ctx, in, nodes, index, node->u.binary.lhs);
  if (status != DECODE_OK)
    return status;
  status =
      reader_u32(ctx, in, &node->u.binary.rhs, "truncated binary rhs index");
  if (status != DECODE_OK)
    return status;
  return decode_validate_child(ctx, in, nodes, index, node->u.binary.rhs);
}

static decode_status decode_read_cmp(ixs_ctx *ctx, decode_input *in,
                                     decode_node *nodes, uint32_t index,
                                     decode_node *node) {
  uint8_t raw_op = 0;
  decode_status status;

  status = reader_u8(ctx, in, &raw_op, "truncated cmp opcode");
  if (status != DECODE_OK)
    return status;
  if (raw_op > WIRE_CMP_NE)
    return decode_error(ctx, in, "unsupported cmp opcode");
  node->u.binary.op = (wire_cmp_op)raw_op;

  return decode_read_binary(ctx, in, nodes, index, node, WIRE_CMP);
}

static decode_status decode_read_piecewise(ixs_ctx *ctx, decode_input *in,
                                           decode_node *nodes, uint32_t index,
                                           decode_node *node) {
  size_t bytes = 0;
  size_t min_bytes = 0;
  uint32_t i;
  decode_status status;

  node->tag = WIRE_PIECEWISE;
  status =
      reader_u32(ctx, in, &node->u.pw.ncases, "truncated piecewise case count");
  if (status != DECODE_OK)
    return status;
  if (!size_mul_ok((size_t)node->u.pw.ncases, sizeof(*node->u.pw.cases),
                   &bytes))
    return decode_error(ctx, in, "piecewise case count overflows size_t");
  if (!size_mul_ok((size_t)node->u.pw.ncases, 2u * sizeof(uint32_t),
                   &min_bytes))
    return decode_error(ctx, in, "piecewise payload overflows size_t");
  status = decode_require_bytes(ctx, in, min_bytes,
                                "piecewise payload exceeds remaining bytes");
  if (status != DECODE_OK)
    return status;

  node->u.pw.cases = NULL;
  if (bytes > 0) {
    node->u.pw.cases = ixs_arena_alloc(&ctx->scratch, bytes, sizeof(void *));
    if (!node->u.pw.cases)
      return DECODE_OOM;
  }

  for (i = 0; i < node->u.pw.ncases; i++) {
    status = reader_u32(ctx, in, &node->u.pw.cases[i].value,
                        "truncated piecewise value index");
    if (status != DECODE_OK)
      return status;
    status =
        decode_validate_child(ctx, in, nodes, index, node->u.pw.cases[i].value);
    if (status != DECODE_OK)
      return status;
    status = reader_u32(ctx, in, &node->u.pw.cases[i].cond,
                        "truncated piecewise condition index");
    if (status != DECODE_OK)
      return status;
    status =
        decode_validate_child(ctx, in, nodes, index, node->u.pw.cases[i].cond);
    if (status != DECODE_OK)
      return status;
  }

  return DECODE_OK;
}

static decode_status decode_read_logic(ixs_ctx *ctx, decode_input *in,
                                       decode_node *nodes, uint32_t index,
                                       decode_node *node, wire_tag tag) {
  size_t bytes = 0;
  size_t min_bytes = 0;
  uint32_t i;
  decode_status status;

  node->tag = tag;
  status = reader_u32(ctx, in, &node->u.logic.nargs,
                      "truncated logic argument count");
  if (status != DECODE_OK)
    return status;
  if (!size_mul_ok((size_t)node->u.logic.nargs, sizeof(*node->u.logic.args),
                   &bytes))
    return decode_error(ctx, in, "logic argument count overflows size_t");
  if (!size_mul_ok((size_t)node->u.logic.nargs, sizeof(uint32_t), &min_bytes))
    return decode_error(ctx, in, "logic payload overflows size_t");
  status = decode_require_bytes(ctx, in, min_bytes,
                                "logic payload exceeds remaining bytes");
  if (status != DECODE_OK)
    return status;

  node->u.logic.args = NULL;
  if (bytes > 0) {
    node->u.logic.args = ixs_arena_alloc(&ctx->scratch, bytes, sizeof(void *));
    if (!node->u.logic.args)
      return DECODE_OOM;
  }

  for (i = 0; i < node->u.logic.nargs; i++) {
    status = reader_u32(ctx, in, &node->u.logic.args[i],
                        "truncated logic child index");
    if (status != DECODE_OK)
      return status;
    status =
        decode_validate_child(ctx, in, nodes, index, node->u.logic.args[i]);
    if (status != DECODE_OK)
      return status;
  }

  return DECODE_OK;
}

static decode_status decode_read_record(ixs_ctx *ctx, decode_input *in,
                                        decode_node *nodes, uint32_t index) {
  uint8_t raw_tag = 0;
  decode_node *node = &nodes[index];
  decode_status status = reader_u8(ctx, in, &raw_tag, "truncated node tag");
  if (status != DECODE_OK)
    return status;

  memset(node, 0, sizeof(*node));

  switch ((wire_tag)raw_tag) {
  case WIRE_INT:
    node->tag = WIRE_INT;
    return reader_i64(ctx, in, &node->u.ival, "truncated integer payload");

  case WIRE_RAT:
    return decode_read_rat_node(ctx, in, node);

  case WIRE_SYM:
    return decode_read_symbol(ctx, in, node);

  case WIRE_ADD:
    return decode_read_add(ctx, in, nodes, index, node);

  case WIRE_MUL:
    return decode_read_mul(ctx, in, nodes, index, node);

  case WIRE_FLOOR:
  case WIRE_CEIL:
  case WIRE_NOT:
    return decode_read_unary(ctx, in, nodes, index, node, (wire_tag)raw_tag);

  case WIRE_MOD:
  case WIRE_MAX:
  case WIRE_MIN:
  case WIRE_XOR:
    return decode_read_binary(ctx, in, nodes, index, node, (wire_tag)raw_tag);

  case WIRE_CMP:
    return decode_read_cmp(ctx, in, nodes, index, node);

  case WIRE_PIECEWISE:
    return decode_read_piecewise(ctx, in, nodes, index, node);

  case WIRE_AND:
  case WIRE_OR:
    return decode_read_logic(ctx, in, nodes, index, node, (wire_tag)raw_tag);

  case WIRE_TRUE:
  case WIRE_FALSE:
  case WIRE_ERROR:
  case WIRE_PARSE_ERROR:
    node->tag = (wire_tag)raw_tag;
    return DECODE_OK;
  }

  return decode_error(ctx, in, "unsupported wire tag");
}

static decode_status decode_validate_build_sizes(ixs_ctx *ctx,
                                                 const decode_input *in,
                                                 const decode_node *nodes,
                                                 uint32_t count) {
  uint32_t i;
  size_t bytes;

  if (!size_mul_ok((size_t)count, sizeof(ixs_node *), &bytes))
    return decode_error(ctx, in, "node table count overflows size_t");

  for (i = 0; i < count; i++) {
    switch (nodes[i].tag) {
    case WIRE_ADD:
      if (!size_mul_ok((size_t)nodes[i].u.add.nterms, sizeof(ixs_addterm),
                       &bytes))
        return decode_error(ctx, in, "add term count overflows size_t");
      break;
    case WIRE_MUL:
      if (!size_mul_ok((size_t)nodes[i].u.mul.nfactors, sizeof(ixs_mulfactor),
                       &bytes))
        return decode_error(ctx, in, "multiply factor count overflows size_t");
      break;
    case WIRE_PIECEWISE:
      if (!size_mul_ok((size_t)nodes[i].u.pw.ncases, sizeof(ixs_pwcase),
                       &bytes))
        return decode_error(ctx, in, "piecewise case count overflows size_t");
      break;
    case WIRE_AND:
    case WIRE_OR:
      if (!size_mul_ok((size_t)nodes[i].u.logic.nargs, sizeof(ixs_node *),
                       &bytes))
        return decode_error(ctx, in, "logic argument count overflows size_t");
      break;
    default:
      break;
    }
  }

  return DECODE_OK;
}

static bool ixs_cmp_from_wire(wire_cmp_op op, ixs_cmp_op *out) {
  switch (op) {
  case WIRE_CMP_GT:
    *out = IXS_CMP_GT;
    return true;
  case WIRE_CMP_GE:
    *out = IXS_CMP_GE;
    return true;
  case WIRE_CMP_LT:
    *out = IXS_CMP_LT;
    return true;
  case WIRE_CMP_LE:
    *out = IXS_CMP_LE;
    return true;
  case WIRE_CMP_EQ:
    *out = IXS_CMP_EQ;
    return true;
  case WIRE_CMP_NE:
    *out = IXS_CMP_NE;
    return true;
  }
  return false;
}

static ixs_node *decode_build_plain_binary(ixs_ctx *ctx, ixs_tag tag,
                                           ixs_node *lhs, ixs_node *rhs) {
  /*
   * ixs_node_binary() only consults cmp_op for IXS_CMP. The other binary tags
   * share the storage layout, so any placeholder op is fine here.
   */
  return ixs_node_binary(ctx, tag, lhs, rhs, IXS_CMP_EQ);
}

static ixs_node *decode_build_node(ixs_ctx *ctx, const decode_node *nodes,
                                   ixs_node *const *built, uint32_t index) {
  const decode_node *node = &nodes[index];

  switch (node->tag) {
  case WIRE_INT:
    return ixs_node_int(ctx, node->u.ival);
  case WIRE_RAT:
    return ixs_node_rat(ctx, node->u.rat.p, node->u.rat.q);
  case WIRE_SYM:
    return ixs_node_sym(ctx, node->u.sym.name, node->u.sym.len);
  case WIRE_ADD: {
    ixs_addterm *terms = NULL;
    uint32_t i;
    size_t bytes = 0;

    if (!size_mul_ok((size_t)node->u.add.nterms, sizeof(*terms), &bytes))
      return NULL;
    if (bytes > 0) {
      terms = ixs_arena_alloc(&ctx->scratch, bytes, sizeof(void *));
      if (!terms)
        return NULL;
    }
    for (i = 0; i < node->u.add.nterms; i++) {
      terms[i].term = built[node->u.add.terms[i].term];
      terms[i].coeff = built[node->u.add.terms[i].coeff];
    }
    return ixs_node_add(ctx, built[node->u.add.coeff], node->u.add.nterms,
                        terms);
  }
  case WIRE_MUL: {
    ixs_mulfactor *factors = NULL;
    uint32_t i;
    size_t bytes = 0;

    if (!size_mul_ok((size_t)node->u.mul.nfactors, sizeof(*factors), &bytes))
      return NULL;
    if (bytes > 0) {
      factors = ixs_arena_alloc(&ctx->scratch, bytes, sizeof(void *));
      if (!factors)
        return NULL;
    }
    for (i = 0; i < node->u.mul.nfactors; i++) {
      factors[i].base = built[node->u.mul.factors[i].base];
      factors[i].exp = node->u.mul.factors[i].exp;
    }
    return ixs_node_mul(ctx, built[node->u.mul.coeff], node->u.mul.nfactors,
                        factors);
  }
  case WIRE_FLOOR:
    return ixs_node_floor(ctx, built[node->u.unary.arg]);
  case WIRE_CEIL:
    return ixs_node_ceil(ctx, built[node->u.unary.arg]);
  case WIRE_MOD:
    return decode_build_plain_binary(ctx, IXS_MOD, built[node->u.binary.lhs],
                                     built[node->u.binary.rhs]);
  case WIRE_PIECEWISE: {
    ixs_pwcase *cases = NULL;
    uint32_t i;
    size_t bytes = 0;

    if (!size_mul_ok((size_t)node->u.pw.ncases, sizeof(*cases), &bytes))
      return NULL;
    if (bytes > 0) {
      cases = ixs_arena_alloc(&ctx->scratch, bytes, sizeof(void *));
      if (!cases)
        return NULL;
    }
    for (i = 0; i < node->u.pw.ncases; i++) {
      cases[i].value = built[node->u.pw.cases[i].value];
      cases[i].cond = built[node->u.pw.cases[i].cond];
    }
    return ixs_node_pw(ctx, node->u.pw.ncases, cases);
  }
  case WIRE_MAX:
    return decode_build_plain_binary(ctx, IXS_MAX, built[node->u.binary.lhs],
                                     built[node->u.binary.rhs]);
  case WIRE_MIN:
    return decode_build_plain_binary(ctx, IXS_MIN, built[node->u.binary.lhs],
                                     built[node->u.binary.rhs]);
  case WIRE_XOR:
    return decode_build_plain_binary(ctx, IXS_XOR, built[node->u.binary.lhs],
                                     built[node->u.binary.rhs]);
  case WIRE_CMP: {
    ixs_cmp_op op;
    if (!ixs_cmp_from_wire(node->u.binary.op, &op))
      return NULL;
    return ixs_node_binary(ctx, IXS_CMP, built[node->u.binary.lhs],
                           built[node->u.binary.rhs], op);
  }
  case WIRE_AND:
  case WIRE_OR: {
    ixs_node **args = NULL;
    ixs_tag tag = node->tag == WIRE_AND ? IXS_AND : IXS_OR;
    uint32_t i;
    size_t bytes = 0;

    if (!size_mul_ok((size_t)node->u.logic.nargs, sizeof(*args), &bytes))
      return NULL;
    if (bytes > 0) {
      args = ixs_arena_alloc(&ctx->scratch, bytes, sizeof(void *));
      if (!args)
        return NULL;
    }
    for (i = 0; i < node->u.logic.nargs; i++)
      args[i] = built[node->u.logic.args[i]];
    return ixs_node_logic(ctx, tag, node->u.logic.nargs, args);
  }
  case WIRE_NOT:
    return ixs_node_not(ctx, built[node->u.unary.arg]);
  case WIRE_TRUE:
    return ctx->node_true;
  case WIRE_FALSE:
    return ctx->node_false;
  case WIRE_ERROR:
    return ctx->sentinel_error;
  case WIRE_PARSE_ERROR:
    return ctx->sentinel_parse_error;
  }
  return NULL;
}

static bool serialize_stream(ixs_ctx *ctx, const ixs_node *root,
                             ixs_writer *w) {
  serial_state state;
  uint32_t root_index = 0;
  size_t i;

  memset(&state, 0, sizeof(state));

  if (!w || !w->write)
    return serial_error(ctx, "invalid writer");
  if (!serial_collect(ctx, root, &state))
    return false;
  if (state.order_used > SERIAL_MAX_NODE_COUNT)
    return serial_error(ctx, "node table exceeds implementation limit");
  if (!serial_lookup_index(&state, root, &root_index))
    return serial_error(ctx, "root is missing from the node table");

  if (!(writer_u32(w, SERIAL_MAGIC) && writer_u32(w, SERIAL_VERSION) &&
        writer_u32(w, (uint32_t)state.order_used)))
    return false;

  for (i = 0; i < state.order_used; i++) {
    if (!serial_write_node(ctx, w, &state, state.order[i]))
      return false;
  }

  return writer_u32(w, root_index);
}

static decode_status decode_stream(ixs_ctx *ctx, decode_input *in,
                                   ixs_node **out) {
  decode_node *nodes = NULL;
  ixs_node **built = NULL;
  uint32_t magic = 0;
  uint32_t version = 0;
  uint32_t count = 0;
  uint32_t root_index = 0;
  size_t framing_floor = 0;
  size_t node_bytes = 0;
  size_t built_bytes = 0;
  uint32_t i;
  decode_status status;

  *out = NULL;

  if (!in->reader || !in->reader->read || !in->reader->remaining) {
    (void)decode_error(ctx, in, "invalid reader");
    return DECODE_PARSE_ERROR;
  }

  status = reader_u32(ctx, in, &magic, "truncated header magic");
  if (status != DECODE_OK)
    return status;
  if (magic != SERIAL_MAGIC) {
    (void)decode_error(ctx, in, "bad magic");
    return DECODE_PARSE_ERROR;
  }

  status = reader_u32(ctx, in, &version, "truncated header version");
  if (status != DECODE_OK)
    return status;
  if (version != SERIAL_VERSION) {
    (void)decode_error(ctx, in, "unsupported version");
    return DECODE_PARSE_ERROR;
  }

  status = reader_u32(ctx, in, &count, "truncated node count");
  if (status != DECODE_OK)
    return status;
  if (count == 0) {
    (void)decode_error(ctx, in, "node table is empty");
    return DECODE_PARSE_ERROR;
  }
  if (count > SERIAL_MAX_NODE_COUNT) {
    (void)decode_error(ctx, in, "node table exceeds implementation limit");
    return DECODE_PARSE_ERROR;
  }
  if (!size_mul_ok((size_t)count, sizeof(*nodes), &node_bytes)) {
    (void)decode_error(ctx, in, "node table count overflows size_t");
    return DECODE_PARSE_ERROR;
  }
  if (!size_mul_ok((size_t)count, sizeof(*built), &built_bytes)) {
    (void)decode_error(ctx, in, "node table count overflows size_t");
    return DECODE_PARSE_ERROR;
  }
  if (!size_add_ok((size_t)count, sizeof(uint32_t), &framing_floor)) {
    (void)decode_error(ctx, in, "node count framing overflows size_t");
    return DECODE_PARSE_ERROR;
  }
  /* Cheap framing floor: one tag byte per node plus the final root index. */
  status = decode_require_bytes(
      ctx, in, framing_floor,
      "node count exceeds remaining bytes for record tags and root index");
  if (status != DECODE_OK)
    return status;

  nodes = ixs_arena_alloc(&ctx->scratch, node_bytes, sizeof(void *));
  if (!nodes)
    return DECODE_OOM;
  memset(nodes, 0, node_bytes);

  for (i = 0; i < count; i++) {
    status = decode_read_record(ctx, in, nodes, i);
    if (status != DECODE_OK)
      return status;
  }

  status = reader_u32(ctx, in, &root_index, "truncated root index");
  if (status != DECODE_OK)
    return status;
  if (root_index >= count) {
    (void)decode_error(ctx, in, "root index is out of range");
    return DECODE_PARSE_ERROR;
  }
  if (in->reader->remaining(in->reader->userdata) != 0) {
    (void)decode_error(ctx, in, "trailing bytes after root index");
    return DECODE_PARSE_ERROR;
  }

  status = decode_validate_build_sizes(ctx, in, nodes, count);
  if (status != DECODE_OK)
    return status;
  built = ixs_arena_alloc(&ctx->scratch, built_bytes, sizeof(void *));
  if (!built)
    return DECODE_OOM;

  for (i = 0; i < count; i++) {
    built[i] = decode_build_node(ctx, nodes, built, i);
    if (!built[i])
      return DECODE_OOM;
  }

  *out = built[root_index];
  return DECODE_OK;
}

bool ixs_serialize_node(ixs_session *s, const ixs_node *root, ixs_writer *w) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_arena_mark mark = ixs_arena_save(&ctx->scratch);
  bool ok = serialize_stream(ctx, root, w);

  ixs_arena_restore(&ctx->scratch, mark);
  ixs_session_unbind(&binding);
  return ok;
}

ixs_node *ixs_deserialize_node(ixs_session *s, ixs_reader *r) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_arena_mark mark = ixs_arena_save(&ctx->scratch);
  decode_input in;
  ixs_node *result = NULL;
  decode_status status;

  in.reader = r;
  in.offset = 0;
  status = decode_stream(ctx, &in, &result);
  if (status == DECODE_PARSE_ERROR)
    result = ctx->sentinel_parse_error;
  else if (status == DECODE_OOM)
    result = NULL;

  ixs_arena_restore(&ctx->scratch, mark);
  ixs_session_unbind(&binding);
  return result;
}
