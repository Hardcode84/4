/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "node.h"
#include "hash.h"

#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* ------------------------------------------------------------------ */
/*  Hashing                                                           */
/* ------------------------------------------------------------------ */

static uint32_t hash_mix(uint32_t h, uint32_t v) {
  h ^= v;
  h *= 0x9e3779b9u;
  h ^= h >> 16;
  return h;
}

static uint32_t hash_i64(int64_t v) {
  uint64_t u = (uint64_t)v;
  return (uint32_t)(u ^ (u >> 32));
}

static uint32_t hash_str(const char *s, size_t len) {
  uint32_t h = 5381;
  size_t i;
  for (i = 0; i < len; i++)
    h = ((h << 5) + h) ^ (unsigned char)s[i];
  return h;
}

static uint32_t compute_hash(const ixs_node *n) {
  uint32_t h = (uint32_t)n->tag * 2654435761u;
  switch (n->tag) {
  case IXS_INT:
    h = hash_mix(h, hash_i64(n->u.ival));
    break;
  case IXS_RAT:
    h = hash_mix(h, hash_i64(n->u.rat.p));
    h = hash_mix(h, hash_i64(n->u.rat.q));
    break;
  case IXS_SYM:
    h = hash_mix(h, hash_str(n->u.name, strlen(n->u.name)));
    break;
  case IXS_ADD: {
    h = hash_mix(h, n->u.add.coeff->hash);
    uint32_t i;
    for (i = 0; i < n->u.add.nterms; i++) {
      h = hash_mix(h, n->u.add.terms[i].term->hash);
      h = hash_mix(h, n->u.add.terms[i].coeff->hash);
    }
    break;
  }
  case IXS_MUL: {
    h = hash_mix(h, n->u.mul.coeff->hash);
    uint32_t i;
    for (i = 0; i < n->u.mul.nfactors; i++) {
      h = hash_mix(h, n->u.mul.factors[i].base->hash);
      h = hash_mix(h, (uint32_t)n->u.mul.factors[i].exp);
    }
    break;
  }
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
    h = hash_mix(h, n->u.unary.arg->hash);
    break;
  case IXS_MOD:
    h = hash_mix(h, n->u.binary.lhs->hash);
    h = hash_mix(h, n->u.binary.rhs->hash);
    break;
  case IXS_CMP:
    h = hash_mix(h, n->u.binary.lhs->hash);
    h = hash_mix(h, n->u.binary.rhs->hash);
    h = hash_mix(h, (uint32_t)n->u.binary.cmp_op);
    break;
  case IXS_PIECEWISE: {
    uint32_t i;
    for (i = 0; i < n->u.pw.ncases; i++) {
      h = hash_mix(h, n->u.pw.cases[i].value->hash);
      h = hash_mix(h, n->u.pw.cases[i].cond->hash);
    }
    break;
  }
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR: {
    uint32_t i;
    h = hash_mix(h, n->u.assoc.nargs);
    for (i = 0; i < n->u.assoc.nargs; i++)
      h = hash_mix(h, n->u.assoc.args[i]->hash);
    break;
  }
  case IXS_NOT:
    h = hash_mix(h, n->u.unary_bool.arg->hash);
    break;
  case IXS_ERROR:
    h = hash_mix(h, 0xDEAD);
    break;
  case IXS_PARSE_ERROR:
    h = hash_mix(h, 0xBEEF);
    break;
  }
  return h;
}

/* ------------------------------------------------------------------ */
/*  Node equality (structural)                                        */
/* ------------------------------------------------------------------ */

static bool node_equal_add(const ixs_node *a, const ixs_node *b) {
  uint32_t i;
  if (a->u.add.coeff != b->u.add.coeff)
    return false;
  if (a->u.add.nterms != b->u.add.nterms)
    return false;
  for (i = 0; i < a->u.add.nterms; i++) {
    if (a->u.add.terms[i].term != b->u.add.terms[i].term)
      return false;
    if (a->u.add.terms[i].coeff != b->u.add.terms[i].coeff)
      return false;
  }
  return true;
}

static bool node_equal_mul(const ixs_node *a, const ixs_node *b) {
  uint32_t i;
  if (a->u.mul.coeff != b->u.mul.coeff)
    return false;
  if (a->u.mul.nfactors != b->u.mul.nfactors)
    return false;
  for (i = 0; i < a->u.mul.nfactors; i++) {
    if (a->u.mul.factors[i].base != b->u.mul.factors[i].base)
      return false;
    if (a->u.mul.factors[i].exp != b->u.mul.factors[i].exp)
      return false;
  }
  return true;
}

static bool node_equal_pw(const ixs_node *a, const ixs_node *b) {
  uint32_t i;
  if (a->u.pw.ncases != b->u.pw.ncases)
    return false;
  for (i = 0; i < a->u.pw.ncases; i++) {
    if (a->u.pw.cases[i].value != b->u.pw.cases[i].value)
      return false;
    if (a->u.pw.cases[i].cond != b->u.pw.cases[i].cond)
      return false;
  }
  return true;
}

static bool node_equal_assoc(const ixs_node *a, const ixs_node *b) {
  uint32_t i;
  if (a->u.assoc.nargs != b->u.assoc.nargs)
    return false;
  for (i = 0; i < a->u.assoc.nargs; i++)
    if (a->u.assoc.args[i] != b->u.assoc.args[i])
      return false;
  return true;
}

IXS_STATIC bool ixs_node_equal(const ixs_node *a, const ixs_node *b) {
  if (a == b)
    return true;
  if (a->tag != b->tag)
    return false;
  switch (a->tag) {
  case IXS_INT:
    return a->u.ival == b->u.ival;
  case IXS_RAT:
    return a->u.rat.p == b->u.rat.p && a->u.rat.q == b->u.rat.q;
  case IXS_SYM:
    return strcmp(a->u.name, b->u.name) == 0;
  case IXS_ADD:
    return node_equal_add(a, b);
  case IXS_MUL:
    return node_equal_mul(a, b);
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
    return a->u.unary.arg == b->u.unary.arg;
  case IXS_CMP:
    return a->u.binary.lhs == b->u.binary.lhs &&
           a->u.binary.rhs == b->u.binary.rhs &&
           a->u.binary.cmp_op == b->u.binary.cmp_op;
  case IXS_MOD:
    return a->u.binary.lhs == b->u.binary.lhs &&
           a->u.binary.rhs == b->u.binary.rhs;
  case IXS_PIECEWISE:
    return node_equal_pw(a, b);
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
    return node_equal_assoc(a, b);
  case IXS_NOT:
    return a->u.unary_bool.arg == b->u.unary_bool.arg;
  default:
    return a->tag == IXS_ERROR || a->tag == IXS_PARSE_ERROR;
  }
}

/* ------------------------------------------------------------------ */
/*  Node comparison (total order)                                     */
/* ------------------------------------------------------------------ */

/*
 * Deterministic lexicographic order on nodes for canonical sorting.
 * Hash-consed identical subtrees stop at pointer equality. Unequal compound
 * nodes use an explicit depth stack so API-built DAG depth is not C-stack
 * depth. IXS_NODE_CMP_OOM is outside the comparison result range.
 */
static int cmp_u32(uint32_t a, uint32_t b) { return (a > b) - (a < b); }

static int cmp_i32(int32_t a, int32_t b) { return (a > b) - (a < b); }

typedef struct {
  const ixs_node *a;
  const ixs_node *b;
  uint64_t slot;
  bool entered;
} node_cmp_frame;

#define NODE_CMP_INLINE_DEPTH 8u

static bool node_cmp_push(ixs_ctx *ctx, node_cmp_frame **stack, size_t *cap,
                          size_t *depth, node_cmp_frame *inline_stack,
                          const ixs_node *a, const ixs_node *b) {
  node_cmp_frame *grown;
  size_t next;

  if (*depth == *cap) {
    if (*cap > (size_t)-1 / 2u)
      return false;
    next = *cap * 2u;
    if (next > (size_t)-1 / sizeof(**stack))
      return false;
    if (*stack == inline_stack) {
      grown =
          ixs_arena_alloc(&ctx->scratch, next * sizeof(*grown), sizeof(void *));
      if (grown)
        memcpy(grown, inline_stack, *depth * sizeof(*grown));
    } else {
      grown = ixs_arena_grow(&ctx->scratch, *stack, *cap * sizeof(*grown),
                             next * sizeof(*grown), sizeof(void *));
    }
    if (!grown)
      return false;
    *stack = grown;
    *cap = next;
  }

  (*stack)[*depth].a = a;
  (*stack)[*depth].b = b;
  (*stack)[*depth].slot = 0;
  (*stack)[*depth].entered = false;
  (*depth)++;
  return true;
}

static int node_cmp_result(ixs_ctx *ctx, ixs_arena_mark mark, int result) {
  ixs_arena_restore(&ctx->scratch, mark);
  return result;
}

#define NODE_CMP_MORE 3

typedef struct {
  ixs_ctx *ctx;
  node_cmp_frame **stack;
  size_t *cap;
  size_t *depth;
  node_cmp_frame *inline_stack;
} node_cmp_state;

static int node_cmp_push_pair(node_cmp_state *state, const ixs_node *a,
                              const ixs_node *b) {
  if (!node_cmp_push(state->ctx, state->stack, state->cap, state->depth,
                     state->inline_stack, a, b))
    return IXS_NODE_CMP_OOM;
  return NODE_CMP_MORE;
}

static int node_cmp_enter(node_cmp_frame *frame, size_t *depth) {
  int c;

  if (frame->a == frame->b) {
    (*depth)--;
    return NODE_CMP_MORE;
  }
  if ((int)frame->a->tag != (int)frame->b->tag)
    return (int)frame->a->tag < (int)frame->b->tag ? -1 : 1;

  switch (frame->a->tag) {
  case IXS_INT:
    c = (frame->a->u.ival > frame->b->u.ival) -
        (frame->a->u.ival < frame->b->u.ival);
    break;
  case IXS_RAT:
    c = ixs_rat_cmp(frame->a->u.rat.p, frame->a->u.rat.q, frame->b->u.rat.p,
                    frame->b->u.rat.q);
    c = (c > 0) - (c < 0);
    break;
  case IXS_SYM:
    c = strcmp(frame->a->u.name, frame->b->u.name);
    c = (c > 0) - (c < 0);
    break;
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    c = 0;
    break;
  default:
    frame->entered = true;
    return NODE_CMP_MORE;
  }
  if (c)
    return c;
  (*depth)--;
  return NODE_CMP_MORE;
}

static int node_cmp_step_add(node_cmp_state *state, node_cmp_frame *frame) {
  uint64_t child;
  uint64_t index;
  const ixs_node *child_a;
  const ixs_node *child_b;
  int c;

  if (frame->slot == 0) {
    frame->slot++;
    return node_cmp_push_pair(state, frame->a->u.add.coeff,
                              frame->b->u.add.coeff);
  }
  if (frame->slot == 1) {
    c = cmp_u32(frame->a->u.add.nterms, frame->b->u.add.nterms);
    frame->slot++;
    return c ? c : NODE_CMP_MORE;
  }

  child = frame->slot - 2u;
  index = child / 2u;
  if (index >= frame->a->u.add.nterms) {
    (*state->depth)--;
    return NODE_CMP_MORE;
  }
  if ((child & 1u) == 0u) {
    child_a = frame->a->u.add.terms[index].term;
    child_b = frame->b->u.add.terms[index].term;
  } else {
    child_a = frame->a->u.add.terms[index].coeff;
    child_b = frame->b->u.add.terms[index].coeff;
  }
  frame->slot++;
  return node_cmp_push_pair(state, child_a, child_b);
}

static int node_cmp_step_mul(node_cmp_state *state, node_cmp_frame *frame) {
  uint64_t child;
  uint64_t index;
  int c;

  if (frame->slot == 0) {
    frame->slot++;
    return node_cmp_push_pair(state, frame->a->u.mul.coeff,
                              frame->b->u.mul.coeff);
  }
  if (frame->slot == 1) {
    c = cmp_u32(frame->a->u.mul.nfactors, frame->b->u.mul.nfactors);
    frame->slot++;
    return c ? c : NODE_CMP_MORE;
  }

  child = frame->slot - 2u;
  index = child / 2u;
  if (index >= frame->a->u.mul.nfactors) {
    (*state->depth)--;
    return NODE_CMP_MORE;
  }
  if ((child & 1u) != 0u) {
    c = cmp_i32(frame->a->u.mul.factors[index].exp,
                frame->b->u.mul.factors[index].exp);
    frame->slot++;
    return c ? c : NODE_CMP_MORE;
  }
  frame->slot++;
  return node_cmp_push_pair(state, frame->a->u.mul.factors[index].base,
                            frame->b->u.mul.factors[index].base);
}

static int node_cmp_step_single(node_cmp_state *state, node_cmp_frame *frame,
                                const ixs_node *child_a,
                                const ixs_node *child_b) {
  if (frame->slot++ == 0)
    return node_cmp_push_pair(state, child_a, child_b);
  (*state->depth)--;
  return NODE_CMP_MORE;
}

static int node_cmp_step_binary(node_cmp_state *state, node_cmp_frame *frame) {
  uint64_t child;
  bool is_cmp = frame->a->tag == IXS_CMP;
  int c;

  if (is_cmp && frame->slot == 0) {
    c = ((int)frame->a->u.binary.cmp_op > (int)frame->b->u.binary.cmp_op) -
        ((int)frame->a->u.binary.cmp_op < (int)frame->b->u.binary.cmp_op);
    frame->slot++;
    return c ? c : NODE_CMP_MORE;
  }
  if (frame->slot >= (is_cmp ? 3u : 2u)) {
    (*state->depth)--;
    return NODE_CMP_MORE;
  }

  child = frame->slot;
  if (is_cmp)
    child--;
  frame->slot++;
  return node_cmp_push_pair(
      state, child == 0 ? frame->a->u.binary.lhs : frame->a->u.binary.rhs,
      child == 0 ? frame->b->u.binary.lhs : frame->b->u.binary.rhs);
}

static int node_cmp_step_pw(node_cmp_state *state, node_cmp_frame *frame) {
  uint64_t child;
  uint64_t index;
  const ixs_node *child_a;
  const ixs_node *child_b;
  int c;

  if (frame->slot == 0) {
    c = cmp_u32(frame->a->u.pw.ncases, frame->b->u.pw.ncases);
    frame->slot++;
    return c ? c : NODE_CMP_MORE;
  }

  child = frame->slot - 1u;
  index = child / 2u;
  if (index >= frame->a->u.pw.ncases) {
    (*state->depth)--;
    return NODE_CMP_MORE;
  }
  if ((child & 1u) == 0u) {
    child_a = frame->a->u.pw.cases[index].value;
    child_b = frame->b->u.pw.cases[index].value;
  } else {
    child_a = frame->a->u.pw.cases[index].cond;
    child_b = frame->b->u.pw.cases[index].cond;
  }
  frame->slot++;
  return node_cmp_push_pair(state, child_a, child_b);
}

static int node_cmp_step_assoc(node_cmp_state *state, node_cmp_frame *frame) {
  uint64_t index;
  int c;

  if (frame->slot == 0) {
    c = cmp_u32(frame->a->u.assoc.nargs, frame->b->u.assoc.nargs);
    frame->slot++;
    return c ? c : NODE_CMP_MORE;
  }

  index = frame->slot - 1u;
  if (index >= frame->a->u.assoc.nargs) {
    (*state->depth)--;
    return NODE_CMP_MORE;
  }
  frame->slot++;
  return node_cmp_push_pair(state, frame->a->u.assoc.args[index],
                            frame->b->u.assoc.args[index]);
}

static int node_cmp_step(node_cmp_state *state, node_cmp_frame *frame) {
  switch (frame->a->tag) {
  case IXS_ADD:
    return node_cmp_step_add(state, frame);
  case IXS_MUL:
    return node_cmp_step_mul(state, frame);
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
    return node_cmp_step_single(state, frame, frame->a->u.unary.arg,
                                frame->b->u.unary.arg);
  case IXS_CMP:
  case IXS_MOD:
    return node_cmp_step_binary(state, frame);
  case IXS_PIECEWISE:
    return node_cmp_step_pw(state, frame);
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
    return node_cmp_step_assoc(state, frame);
  case IXS_NOT:
    return node_cmp_step_single(state, frame, frame->a->u.unary_bool.arg,
                                frame->b->u.unary_bool.arg);
  default:
    (*state->depth)--;
    return NODE_CMP_MORE;
  }
}

static int node_cmp_iter(ixs_ctx *ctx, const ixs_node *a, const ixs_node *b) {
  node_cmp_frame inline_stack[NODE_CMP_INLINE_DEPTH];
  node_cmp_frame *stack = inline_stack;
  size_t cap = NODE_CMP_INLINE_DEPTH;
  size_t depth = 0;
  ixs_arena_mark mark = ixs_arena_save(&ctx->scratch);
  node_cmp_state state;
  int result;

  state.ctx = ctx;
  state.stack = &stack;
  state.cap = &cap;
  state.depth = &depth;
  state.inline_stack = inline_stack;

  if (!node_cmp_push(ctx, &stack, &cap, &depth, inline_stack, a, b))
    return node_cmp_result(ctx, mark, IXS_NODE_CMP_OOM);

  while (depth != 0) {
    node_cmp_frame *frame = &stack[depth - 1u];
    result = frame->entered ? node_cmp_step(&state, frame)
                            : node_cmp_enter(frame, &depth);
    if (result != NODE_CMP_MORE)
      return node_cmp_result(ctx, mark, result);
  }

  return node_cmp_result(ctx, mark, 0);
}

IXS_STATIC int ixs_node_cmp(ixs_ctx *ctx, const ixs_node *a,
                            const ixs_node *b) {
  int c;

  if (a == b)
    return 0;
  if ((int)a->tag != (int)b->tag)
    return (int)a->tag < (int)b->tag ? -1 : 1;

  switch (a->tag) {
  case IXS_INT:
    return (a->u.ival > b->u.ival) - (a->u.ival < b->u.ival);
  case IXS_RAT:
    c = ixs_rat_cmp(a->u.rat.p, a->u.rat.q, b->u.rat.p, b->u.rat.q);
    return (c > 0) - (c < 0);
  case IXS_SYM:
    c = strcmp(a->u.name, b->u.name);
    return (c > 0) - (c < 0);
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    return 0;
  default:
    return node_cmp_iter(ctx, a, b);
  }
}

/* ------------------------------------------------------------------ */
/*  Structural transform cache                                       */
/* ------------------------------------------------------------------ */

#define IXS_NODE_TRANSFORM_CACHE_INIT_CAP 256u

/* Load stays at or below 75%, so lookup and insertion are expected O(1). */
static size_t
node_transform_cache_index(const ixs_node_transform_cache_entry *entries,
                           size_t cap, const ixs_node *source) {
  size_t mask = cap - 1u;
  size_t index = ixs_hash_ptr(source) & mask;
  while (entries[index].source && entries[index].source != source)
    index = (index + 1u) & mask;
  return index;
}

static bool node_transform_cache_grow(ixs_ctx *ctx) {
  size_t new_cap = ctx->transform_cache_cap ? ctx->transform_cache_cap * 2u
                                            : IXS_NODE_TRANSFORM_CACHE_INIT_CAP;
  ixs_node_transform_cache_entry *entries;
  size_t i;

  if (new_cap <= ctx->transform_cache_cap ||
      new_cap > (size_t)-1 / sizeof(*entries))
    return false;
  entries =
      ixs_arena_alloc(&ctx->arena, new_cap * sizeof(*entries), sizeof(void *));
  if (!entries)
    return false;
  memset(entries, 0, new_cap * sizeof(*entries));

  for (i = 0; i < ctx->transform_cache_cap; i++) {
    if (ctx->transform_cache[i].source) {
      ixs_node_transform_cache_entry *slot =
          &entries[node_transform_cache_index(entries, new_cap,
                                              ctx->transform_cache[i].source)];
      *slot = ctx->transform_cache[i];
    }
  }
  ctx->transform_cache = entries;
  ctx->transform_cache_cap = new_cap;
  return true;
}

IXS_STATIC ixs_node *
ixs_node_transform_cache_lookup(const ixs_ctx *ctx, const ixs_node *source,
                                ixs_node_transform_kind kind) {
  const ixs_node_transform_cache_entry *slot;
  if (!ctx || !source || (unsigned)kind >= IXS_NODE_TRANSFORM_COUNT ||
      !ctx->transform_cache_cap)
    return NULL;
  slot = &ctx->transform_cache[node_transform_cache_index(
      ctx->transform_cache, ctx->transform_cache_cap, source)];
  return slot->source ? slot->results[kind] : NULL;
}

IXS_STATIC void ixs_node_transform_cache_store(ixs_ctx *ctx, ixs_node *source,
                                               ixs_node_transform_kind kind,
                                               ixs_node *result) {
  ixs_node_transform_cache_entry *slot;

  if (!ctx || !source || !result ||
      (unsigned)kind >= IXS_NODE_TRANSFORM_COUNT ||
      ixs_node_is_sentinel(source) || ixs_node_is_sentinel(result) ||
      !ixs_ctx_owns_node(ctx, source) || !ixs_ctx_owns_node(ctx, result))
    return;
  if (!ctx->transform_cache_cap && !node_transform_cache_grow(ctx))
    return;
  slot = &ctx->transform_cache[node_transform_cache_index(
      ctx->transform_cache, ctx->transform_cache_cap, source)];
  if (slot->source) {
    if (!slot->results[kind])
      slot->results[kind] = result;
    return;
  }
  if (ctx->transform_cache_used + 1u >
      ctx->transform_cache_cap - ctx->transform_cache_cap / 4u) {
    if (!node_transform_cache_grow(ctx))
      return;
    slot = &ctx->transform_cache[node_transform_cache_index(
        ctx->transform_cache, ctx->transform_cache_cap, source)];
  }
  slot->source = source;
  slot->results[kind] = result;
  ctx->transform_cache_used++;
}

IXS_STATIC ixs_node *ixs_node_expand_cache_lookup(const ixs_ctx *ctx,
                                                  const ixs_node *source,
                                                  unsigned depth) {
  const ixs_node_transform_cache_entry *slot;
  if (!ctx || !source || !ctx->transform_cache_cap)
    return NULL;
  slot = &ctx->transform_cache[node_transform_cache_index(
      ctx->transform_cache, ctx->transform_cache_cap, source)];
  if (!slot->source || slot->expand_depth_plus_one <= depth)
    return NULL;
  return slot->results[IXS_NODE_TRANSFORM_EXPAND];
}

IXS_STATIC void ixs_node_expand_cache_store(ixs_ctx *ctx, ixs_node *source,
                                            ixs_node *result, unsigned depth) {
  ixs_node_transform_cache_entry *slot;
  unsigned depth_plus_one = depth + 1u;
  ixs_node_transform_cache_store(ctx, source, IXS_NODE_TRANSFORM_EXPAND,
                                 result);
  if (!ctx || !source || !ctx->transform_cache_cap)
    return;
  slot = &ctx->transform_cache[node_transform_cache_index(
      ctx->transform_cache, ctx->transform_cache_cap, source)];
  if (slot->source == source &&
      slot->results[IXS_NODE_TRANSFORM_EXPAND] == result &&
      slot->expand_depth_plus_one < depth_plus_one)
    slot->expand_depth_plus_one = depth_plus_one;
}

IXS_STATIC void ixs_node_transform_cache_clear(ixs_ctx *ctx) {
  if (!ctx || !ctx->transform_cache)
    return;
  memset(ctx->transform_cache, 0,
         ctx->transform_cache_cap * sizeof(*ctx->transform_cache));
  ctx->transform_cache_used = 0;
}

/* ------------------------------------------------------------------ */
/*  Hash-consing table                                                */
/* ------------------------------------------------------------------ */

IXS_STATIC bool ixs_htab_init(ixs_ctx *ctx) {
  ctx->htab_cap = IXS_HTAB_INIT_CAP;
  ctx->htab_used = 0;
  ctx->htab = calloc(ctx->htab_cap, sizeof(ixs_node *));
  return ctx->htab != NULL;
}

IXS_STATIC void ixs_htab_destroy(ixs_ctx *ctx) {
  free(ctx->htab);
  ctx->htab = NULL;
}

static bool htab_rehash(ixs_ctx *ctx) {
  size_t new_cap = ctx->htab_cap * 2;
  if (new_cap < ctx->htab_cap)
    return false;

  ixs_node **new_buckets = calloc(new_cap, sizeof(ixs_node *));
  if (!new_buckets)
    return false;

  size_t mask = new_cap - 1;
  size_t i;
  for (i = 0; i < ctx->htab_cap; i++) {
    ixs_node *n = ctx->htab[i];
    if (!n)
      continue;
    size_t idx = n->hash & mask;
    while (new_buckets[idx])
      idx = (idx + 1) & mask;
    new_buckets[idx] = n;
  }

  free(ctx->htab);
  ctx->htab = new_buckets;
  ctx->htab_cap = new_cap;
  return true;
}

/* Single probe loop shared by lookup and intern.  Returns the index of
 * either the matching slot or the first empty slot.  Sets *found to the
 * matching node, or NULL if the slot is empty. */
static size_t htab_find_slot(const ixs_ctx *ctx, const ixs_node *probe,
                             ixs_node **found) {
  size_t mask = ctx->htab_cap - 1;
  size_t idx = probe->hash & mask;
  for (;;) {
    ixs_node *slot = ctx->htab[idx];
    if (!slot) {
      *found = NULL;
      return idx;
    }
    if (slot->hash == probe->hash && ixs_node_equal(slot, probe)) {
      *found = slot;
      return idx;
    }
    idx = (idx + 1) & mask;
  }
}

static ixs_node *htab_lookup(const ixs_ctx *ctx, const ixs_node *probe) {
  ixs_node *found;
  htab_find_slot(ctx, probe, &found);
  return found;
}

static bool node_property_integer(const ixs_node *node) {
  if (!node)
    return false;
  if ((node->properties & IXS_NODE_PROPERTY_VALID) != 0)
    return (node->properties & IXS_NODE_PROPERTY_INTEGER) != 0;
  return ixs_node_is_integer_valued(node);
}

static bool node_property_bool(const ixs_node *node) {
  if (!node)
    return false;
  if ((node->properties & IXS_NODE_PROPERTY_VALID) != 0)
    return (node->properties & IXS_NODE_PROPERTY_BOOL) != 0;
  return ixs_node_is_bool_valued(node);
}

static bool node_property_total(const ixs_node *node) {
  return node && (node->properties & IXS_NODE_PROPERTY_VALID) != 0 &&
         (node->properties & IXS_NODE_PROPERTY_TOTAL) != 0;
}

IXS_STATIC bool ixs_cmp_op_valid(ixs_cmp_op op) {
  switch (op) {
  case IXS_CMP_GT:
  case IXS_CMP_GE:
  case IXS_CMP_LT:
  case IXS_CMP_LE:
  case IXS_CMP_EQ:
  case IXS_CMP_NE:
    return true;
  }
  return false;
}

IXS_STATIC ixs_cmp_op ixs_cmp_op_negate(ixs_cmp_op op) {
  switch (op) {
  case IXS_CMP_GT:
    return IXS_CMP_LE;
  case IXS_CMP_GE:
    return IXS_CMP_LT;
  case IXS_CMP_LT:
    return IXS_CMP_GE;
  case IXS_CMP_LE:
    return IXS_CMP_GT;
  case IXS_CMP_EQ:
    return IXS_CMP_NE;
  case IXS_CMP_NE:
    return IXS_CMP_EQ;
  }
  return op;
}

static uint8_t node_pack_properties(bool integer, bool boolean, bool total,
                                    bool rounding, bool piecewise,
                                    bool nested_piecewise) {
  uint8_t properties = IXS_NODE_PROPERTY_VALID;

  if (integer)
    properties |= IXS_NODE_PROPERTY_INTEGER;
  if (boolean)
    properties |= IXS_NODE_PROPERTY_BOOL;
  if (total)
    properties |= IXS_NODE_PROPERTY_TOTAL;
  if (rounding)
    properties |= IXS_NODE_PROPERTY_ROUNDING;
  if (piecewise)
    properties |= IXS_NODE_PROPERTY_PIECEWISE;
  if (nested_piecewise)
    properties |= IXS_NODE_PROPERTY_NESTED_PIECEWISE;
  return properties;
}

static uint8_t node_descendant_properties(const ixs_node *node) {
  return node && (node->properties & IXS_NODE_PROPERTY_VALID) != 0
             ? node->properties
             : 0;
}

static uint8_t node_compute_add_properties(const ixs_node *node) {
  uint32_t i;
  bool integer = node_property_integer(node->u.add.coeff);
  bool total = node_property_total(node->u.add.coeff);
  uint8_t descendants = node_descendant_properties(node->u.add.coeff);

  for (i = 0; i < node->u.add.nterms; i++) {
    integer = integer && node_property_integer(node->u.add.terms[i].coeff) &&
              node_property_integer(node->u.add.terms[i].term);
    total = total && node_property_total(node->u.add.terms[i].coeff) &&
            node_property_total(node->u.add.terms[i].term);
    descendants |= node_descendant_properties(node->u.add.terms[i].coeff) |
                   node_descendant_properties(node->u.add.terms[i].term);
  }
  return node_pack_properties(
      integer, false, total, (descendants & IXS_NODE_PROPERTY_ROUNDING) != 0,
      (descendants & IXS_NODE_PROPERTY_PIECEWISE) != 0,
      (descendants & IXS_NODE_PROPERTY_NESTED_PIECEWISE) != 0);
}

static uint8_t node_compute_mul_properties(const ixs_node *node) {
  uint32_t i;
  bool integer = node_property_integer(node->u.mul.coeff);
  bool total = node_property_total(node->u.mul.coeff);
  uint8_t descendants = node_descendant_properties(node->u.mul.coeff);

  for (i = 0; i < node->u.mul.nfactors; i++) {
    integer = integer && node->u.mul.factors[i].exp > 0 &&
              node_property_integer(node->u.mul.factors[i].base);
    total = total && node->u.mul.factors[i].exp > 0 &&
            node_property_total(node->u.mul.factors[i].base);
    descendants |= node_descendant_properties(node->u.mul.factors[i].base);
  }
  return node_pack_properties(
      integer, false, total, (descendants & IXS_NODE_PROPERTY_ROUNDING) != 0,
      (descendants & IXS_NODE_PROPERTY_PIECEWISE) != 0,
      (descendants & IXS_NODE_PROPERTY_NESTED_PIECEWISE) != 0);
}

static uint8_t node_compute_pw_properties(const ixs_node *node) {
  uint32_t i;
  bool integer = node->u.pw.ncases > 0;
  bool boolean = integer;
  bool total = integer && ixs_node_is_known_true(
                              node->u.pw.cases[node->u.pw.ncases - 1u].cond);
  uint8_t descendants = 0;

  for (i = 0; i < node->u.pw.ncases; i++) {
    integer = integer && node_property_integer(node->u.pw.cases[i].value);
    boolean = boolean && node_property_bool(node->u.pw.cases[i].value);
    total = total && node_property_total(node->u.pw.cases[i].value) &&
            node_property_total(node->u.pw.cases[i].cond);
    descendants |= node_descendant_properties(node->u.pw.cases[i].value) |
                   node_descendant_properties(node->u.pw.cases[i].cond);
  }
  return node_pack_properties(
      integer, boolean, total, (descendants & IXS_NODE_PROPERTY_ROUNDING) != 0,
      true, (descendants & IXS_NODE_PROPERTY_PIECEWISE) != 0);
}

static uint8_t node_compute_assoc_properties(const ixs_node *node) {
  uint32_t i;
  bool canonical_arity = node->u.assoc.nargs >= 2;
  bool integer = canonical_arity;
  bool boolean =
      canonical_arity && (node->tag == IXS_AND || node->tag == IXS_OR);
  bool total = canonical_arity;
  uint8_t descendants = 0;

  for (i = 0; i < node->u.assoc.nargs; i++) {
    integer = integer && node_property_integer(node->u.assoc.args[i]);
    if (boolean)
      boolean = node_property_bool(node->u.assoc.args[i]);
    total = total && node_property_total(node->u.assoc.args[i]);
    descendants |= node_descendant_properties(node->u.assoc.args[i]);
  }
  if (node->tag == IXS_XOR || node->tag == IXS_AND || node->tag == IXS_OR)
    total = total && integer;
  return node_pack_properties(
      integer, boolean, total, (descendants & IXS_NODE_PROPERTY_ROUNDING) != 0,
      (descendants & IXS_NODE_PROPERTY_PIECEWISE) != 0,
      (descendants & IXS_NODE_PROPERTY_NESTED_PIECEWISE) != 0);
}

static uint8_t node_compute_simple_properties(const ixs_node *node) {
  bool integer = false;
  bool boolean = false;
  bool total = false;
  bool rounding = false;
  bool piecewise = false;
  bool nested_piecewise = false;

  switch ((ixs_tag)node->tag) {
  case IXS_INT:
    integer = true;
    boolean = node->u.ival == 0 || node->u.ival == 1;
    total = true;
    break;
  case IXS_RAT:
    integer = node->u.rat.q == 1;
    total = node->u.rat.q > 0;
    break;
  case IXS_SYM:
    integer = true;
    total = true;
    break;
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
    integer = true;
    total = node_property_total(node->u.unary.arg);
    rounding = true;
    piecewise = ixs_node_contains_piecewise(node->u.unary.arg);
    nested_piecewise = ixs_node_contains_nested_piecewise(node->u.unary.arg);
    break;
  case IXS_CMP:
    integer = ixs_cmp_op_valid(node->u.binary.cmp_op);
    boolean = integer;
    total = integer && node_property_total(node->u.binary.lhs) &&
            node_property_total(node->u.binary.rhs);
    rounding = ixs_node_contains_rounding(node->u.binary.lhs) ||
               ixs_node_contains_rounding(node->u.binary.rhs);
    piecewise = ixs_node_contains_piecewise(node->u.binary.lhs) ||
                ixs_node_contains_piecewise(node->u.binary.rhs);
    nested_piecewise = ixs_node_contains_nested_piecewise(node->u.binary.lhs) ||
                       ixs_node_contains_nested_piecewise(node->u.binary.rhs);
    break;
  case IXS_NOT:
    integer = true;
    boolean = true;
    total = node_property_total(node->u.unary_bool.arg);
    rounding = ixs_node_contains_rounding(node->u.unary_bool.arg);
    piecewise = ixs_node_contains_piecewise(node->u.unary_bool.arg);
    nested_piecewise =
        ixs_node_contains_nested_piecewise(node->u.unary_bool.arg);
    break;
  case IXS_MOD:
    integer = node_property_integer(node->u.binary.lhs) &&
              node_property_integer(node->u.binary.rhs);
    total = ixs_node_classify_mod_divisor(node->u.binary.rhs) ==
                IXS_MOD_DIVISOR_POSITIVE &&
            node_property_total(node->u.binary.lhs) &&
            node_property_total(node->u.binary.rhs);
    rounding = ixs_node_contains_rounding(node->u.binary.lhs) ||
               ixs_node_contains_rounding(node->u.binary.rhs);
    piecewise = ixs_node_contains_piecewise(node->u.binary.lhs) ||
                ixs_node_contains_piecewise(node->u.binary.rhs);
    nested_piecewise = ixs_node_contains_nested_piecewise(node->u.binary.lhs) ||
                       ixs_node_contains_nested_piecewise(node->u.binary.rhs);
    break;
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    break;
  default:
    break;
  }
  return node_pack_properties(integer, boolean, total, rounding, piecewise,
                              nested_piecewise);
}

static uint8_t node_compute_properties(const ixs_node *node) {
  switch ((ixs_tag)node->tag) {
  case IXS_ADD:
    return node_compute_add_properties(node);
  case IXS_MUL:
    return node_compute_mul_properties(node);
  case IXS_PIECEWISE:
    return node_compute_pw_properties(node);
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
    return node_compute_assoc_properties(node);
  default:
    return node_compute_simple_properties(node);
  }
}

IXS_STATIC ixs_node *ixs_htab_intern(ixs_ctx *ctx, struct ixs_node_impl *node) {
  ixs_node *found;
  node->properties = node_compute_properties(node);
  size_t idx = htab_find_slot(ctx, node, &found);
  if (found)
    return found;
  ctx->htab[idx] = node;
  ctx->htab_used++;
  if (ctx->htab_used * IXS_HTAB_LOAD_DEN > ctx->htab_cap * IXS_HTAB_LOAD_NUM) {
    if (!htab_rehash(ctx))
      return NULL;
  }
  return node;
}

/* ------------------------------------------------------------------ */
/*  Arena allocation helpers                                          */
/* ------------------------------------------------------------------ */

static struct ixs_node_impl *alloc_node(ixs_ctx *ctx) {
  struct ixs_node_impl *n =
      ixs_arena_alloc(&ctx->arena, sizeof(ixs_node), sizeof(void *));
  if (n)
    memset(n, 0, sizeof(*n));
  return n;
}

/* ------------------------------------------------------------------ */
/*  Raw node constructors                                             */
/* ------------------------------------------------------------------ */

IXS_STATIC ixs_node *ixs_node_int(ixs_ctx *ctx, int64_t val) {
  struct ixs_node_impl tmp;
  ixs_node *found;
  struct ixs_node_impl *n;
  memset(&tmp, 0, sizeof(tmp));
  tmp.tag = IXS_INT;
  tmp.u.ival = val;
  tmp.hash = compute_hash(&tmp);

  found = htab_lookup(ctx, &tmp);
  if (found)
    return found;

  n = alloc_node(ctx);
  if (!n)
    return NULL;
  *n = tmp;
  return ixs_htab_intern(ctx, n);
}

IXS_STATIC ixs_node *ixs_node_rat(ixs_ctx *ctx, int64_t p, int64_t q) {
  struct ixs_node_impl tmp;
  ixs_node *found;
  struct ixs_node_impl *n;
  if (q == 1)
    return ixs_node_int(ctx, p);

  memset(&tmp, 0, sizeof(tmp));
  tmp.tag = IXS_RAT;
  tmp.u.rat.p = p;
  tmp.u.rat.q = q;
  tmp.hash = compute_hash(&tmp);

  found = htab_lookup(ctx, &tmp);
  if (found)
    return found;

  n = alloc_node(ctx);
  if (!n)
    return NULL;
  *n = tmp;
  return ixs_htab_intern(ctx, n);
}

/* Cannot use htab_lookup: name may not be NUL-terminated, and
 * ixs_node_equal uses strcmp, so we probe with memcmp directly. */
IXS_STATIC ixs_node *ixs_node_sym(ixs_ctx *ctx, const char *name, size_t len) {
  uint32_t sym_hash;
  struct ixs_node_impl *n;
  char *interned;

  /* Compute hash from the bounded slice -- name may not be NUL-terminated. */
  sym_hash = (uint32_t)IXS_SYM * 2654435761u;
  sym_hash = hash_mix(sym_hash, hash_str(name, len));

  {
    size_t mask = ctx->htab_cap - 1;
    size_t idx = sym_hash & mask;
    for (;;) {
      ixs_node *slot = ctx->htab[idx];
      if (!slot)
        break;
      if (slot->hash == sym_hash && slot->tag == IXS_SYM &&
          strlen(slot->u.name) == len && memcmp(slot->u.name, name, len) == 0)
        return slot;
      idx = (idx + 1) & mask;
    }
  }

  interned = ixs_arena_strdup(&ctx->arena, name, len);
  if (!interned)
    return NULL;

  n = alloc_node(ctx);
  if (!n)
    return NULL;
  n->tag = IXS_SYM;
  n->u.name = interned;
  n->hash = sym_hash;
  return ixs_htab_intern(ctx, n);
}

IXS_STATIC ixs_node *ixs_node_add(ixs_ctx *ctx, ixs_node *coeff,
                                  uint32_t nterms, const ixs_addterm *terms) {
  struct ixs_node_impl tmp;
  ixs_node *found;
  struct ixs_node_impl *n;
  ixs_addterm *a;
  if (nterms > (UINT32_MAX - 1u) / 2u)
    return NULL;
  memset(&tmp, 0, sizeof(tmp));
  tmp.tag = IXS_ADD;
  tmp.u.add.coeff = coeff;
  tmp.u.add.nterms = nterms;
  tmp.u.add.terms = terms;
  tmp.hash = compute_hash(&tmp);

  found = htab_lookup(ctx, &tmp);
  if (found)
    return found;

  a = NULL;
  if (nterms > 0) {
    size_t sz = (size_t)nterms * sizeof(ixs_addterm);
    if (sz / sizeof(ixs_addterm) != nterms)
      return NULL;
    a = ixs_arena_alloc(&ctx->arena, sz, sizeof(void *));
    if (!a)
      return NULL;
    memcpy(a, terms, sz);
  }

  n = alloc_node(ctx);
  if (!n)
    return NULL;
  tmp.u.add.terms = a;
  *n = tmp;
  return ixs_htab_intern(ctx, n);
}

IXS_STATIC ixs_node *ixs_node_mul(ixs_ctx *ctx, ixs_node *coeff,
                                  uint32_t nfactors,
                                  const ixs_mulfactor *factors) {
  struct ixs_node_impl tmp;
  ixs_node *found;
  struct ixs_node_impl *n;
  ixs_mulfactor *f;
  if (nfactors == UINT32_MAX)
    return NULL;
  memset(&tmp, 0, sizeof(tmp));
  tmp.tag = IXS_MUL;
  tmp.u.mul.coeff = coeff;
  tmp.u.mul.nfactors = nfactors;
  tmp.u.mul.factors = factors;
  tmp.hash = compute_hash(&tmp);

  found = htab_lookup(ctx, &tmp);
  if (found)
    return found;

  f = NULL;
  if (nfactors > 0) {
    size_t sz = (size_t)nfactors * sizeof(ixs_mulfactor);
    if (sz / sizeof(ixs_mulfactor) != nfactors)
      return NULL;
    f = ixs_arena_alloc(&ctx->arena, sz, sizeof(void *));
    if (!f)
      return NULL;
    memcpy(f, factors, sz);
  }

  n = alloc_node(ctx);
  if (!n)
    return NULL;
  tmp.u.mul.factors = f;
  *n = tmp;
  return ixs_htab_intern(ctx, n);
}

IXS_STATIC ixs_node *ixs_node_floor(ixs_ctx *ctx, ixs_node *arg) {
  struct ixs_node_impl tmp;
  ixs_node *found;
  struct ixs_node_impl *n;
  memset(&tmp, 0, sizeof(tmp));
  tmp.tag = IXS_FLOOR;
  tmp.u.unary.arg = arg;
  tmp.hash = compute_hash(&tmp);

  found = htab_lookup(ctx, &tmp);
  if (found)
    return found;

  n = alloc_node(ctx);
  if (!n)
    return NULL;
  *n = tmp;
  return ixs_htab_intern(ctx, n);
}

IXS_STATIC ixs_node *ixs_node_ceil(ixs_ctx *ctx, ixs_node *arg) {
  struct ixs_node_impl tmp;
  ixs_node *found;
  struct ixs_node_impl *n;
  memset(&tmp, 0, sizeof(tmp));
  tmp.tag = IXS_CEIL;
  tmp.u.unary.arg = arg;
  tmp.hash = compute_hash(&tmp);

  found = htab_lookup(ctx, &tmp);
  if (found)
    return found;

  n = alloc_node(ctx);
  if (!n)
    return NULL;
  *n = tmp;
  return ixs_htab_intern(ctx, n);
}

IXS_STATIC ixs_node *ixs_node_trunc(ixs_ctx *ctx, ixs_node *arg) {
  struct ixs_node_impl tmp;
  ixs_node *found;
  struct ixs_node_impl *n;
  memset(&tmp, 0, sizeof(tmp));
  tmp.tag = IXS_TRUNC;
  tmp.u.unary.arg = arg;
  tmp.hash = compute_hash(&tmp);

  found = htab_lookup(ctx, &tmp);
  if (found)
    return found;

  n = alloc_node(ctx);
  if (!n)
    return NULL;
  *n = tmp;
  return ixs_htab_intern(ctx, n);
}

IXS_STATIC ixs_node *ixs_node_binary(ixs_ctx *ctx, ixs_tag tag, ixs_node *lhs,
                                     ixs_node *rhs, ixs_cmp_op op) {
  struct ixs_node_impl tmp;
  ixs_node *found;
  struct ixs_node_impl *n;
  memset(&tmp, 0, sizeof(tmp));
  tmp.tag = tag;
  tmp.u.binary.lhs = lhs;
  tmp.u.binary.rhs = rhs;
  tmp.u.binary.cmp_op = op;
  tmp.hash = compute_hash(&tmp);

  found = htab_lookup(ctx, &tmp);
  if (found)
    return found;

  n = alloc_node(ctx);
  if (!n)
    return NULL;
  *n = tmp;
  return ixs_htab_intern(ctx, n);
}

IXS_STATIC ixs_node *ixs_node_pw(ixs_ctx *ctx, uint32_t ncases,
                                 const ixs_pwcase *cases) {
  struct ixs_node_impl tmp;
  ixs_node *found;
  struct ixs_node_impl *n;
  ixs_pwcase *c;
  if (ncases > UINT32_MAX / 2u)
    return NULL;
  memset(&tmp, 0, sizeof(tmp));
  tmp.tag = IXS_PIECEWISE;
  tmp.u.pw.ncases = ncases;
  tmp.u.pw.cases = cases;
  tmp.hash = compute_hash(&tmp);

  found = htab_lookup(ctx, &tmp);
  if (found)
    return found;

  c = NULL;
  if (ncases > 0) {
    size_t sz = (size_t)ncases * sizeof(ixs_pwcase);
    if (sz / sizeof(ixs_pwcase) != ncases)
      return NULL;
    c = ixs_arena_alloc(&ctx->arena, sz, sizeof(void *));
    if (!c)
      return NULL;
    memcpy(c, cases, sz);
  }

  n = alloc_node(ctx);
  if (!n)
    return NULL;
  tmp.u.pw.cases = c;
  *n = tmp;
  return ixs_htab_intern(ctx, n);
}

IXS_STATIC ixs_node *ixs_node_assoc(ixs_ctx *ctx, ixs_tag tag, uint32_t nargs,
                                    ixs_node *const *args) {
  struct ixs_node_impl tmp;
  ixs_node *found;
  struct ixs_node_impl *n;
  ixs_node **a;
  memset(&tmp, 0, sizeof(tmp));
  tmp.tag = tag;
  tmp.u.assoc.nargs = nargs;
  tmp.u.assoc.args = args;
  tmp.hash = compute_hash(&tmp);

  found = htab_lookup(ctx, &tmp);
  if (found)
    return found;

  a = NULL;
  if (nargs > 0) {
    size_t sz = (size_t)nargs * sizeof(ixs_node *);
    if (sz / sizeof(ixs_node *) != nargs)
      return NULL;
    a = ixs_arena_alloc(&ctx->arena, sz, sizeof(void *));
    if (!a)
      return NULL;
    memcpy(a, args, sz);
  }

  n = alloc_node(ctx);
  if (!n)
    return NULL;
  tmp.u.assoc.args = a;
  *n = tmp;
  return ixs_htab_intern(ctx, n);
}

IXS_STATIC ixs_node *ixs_node_not(ixs_ctx *ctx, ixs_node *arg) {
  struct ixs_node_impl tmp;
  ixs_node *found;
  struct ixs_node_impl *n;
  memset(&tmp, 0, sizeof(tmp));
  tmp.tag = IXS_NOT;
  tmp.u.unary_bool.arg = arg;
  tmp.hash = compute_hash(&tmp);

  found = htab_lookup(ctx, &tmp);
  if (found)
    return found;

  n = alloc_node(ctx);
  if (!n)
    return NULL;
  *n = tmp;
  return ixs_htab_intern(ctx, n);
}

/* ------------------------------------------------------------------ */
/*  Utilities                                                         */
/* ------------------------------------------------------------------ */

IXS_STATIC bool ixs_node_is_const(const ixs_node *n) {
  return n->tag == IXS_INT || n->tag == IXS_RAT;
}

IXS_STATIC bool ixs_node_is_zero(const ixs_node *n) {
  return n->tag == IXS_INT && n->u.ival == 0;
}

IXS_STATIC bool ixs_node_is_one(const ixs_node *n) {
  return n->tag == IXS_INT && n->u.ival == 1;
}

IXS_STATIC void ixs_node_get_rat(const ixs_node *n, int64_t *p, int64_t *q) {
  if (n->tag == IXS_INT) {
    *p = n->u.ival;
    *q = 1;
  } else if (n->tag == IXS_RAT) {
    *p = n->u.rat.p;
    *q = n->u.rat.q;
  } else {
    *p = 0;
    *q = 1;
  }
}

IXS_STATIC ixs_mod_divisor_class
ixs_node_classify_mod_divisor(const ixs_node *n) {
  int64_t p, q;

  if (!n || !ixs_node_is_const(n))
    return IXS_MOD_DIVISOR_UNKNOWN;
  ixs_node_get_rat(n, &p, &q);
  (void)q;
  if (p > 0)
    return IXS_MOD_DIVISOR_POSITIVE;
  if (p == 0)
    return IXS_MOD_DIVISOR_ZERO;
  return IXS_MOD_DIVISOR_NEGATIVE;
}

IXS_STATIC bool ixs_node_is_known_false(const ixs_node *n) {
  int64_t p, q;
  if (!n)
    return false;
  if (!ixs_node_is_const(n))
    return false;
  ixs_node_get_rat(n, &p, &q);
  (void)q;
  return p == 0;
}

IXS_STATIC bool ixs_node_is_known_true(const ixs_node *n) {
  int64_t p, q;
  if (!n)
    return false;
  if (!ixs_node_is_const(n))
    return false;
  ixs_node_get_rat(n, &p, &q);
  (void)q;
  return p != 0;
}

IXS_STATIC bool ixs_node_is_sentinel(const ixs_node *n) {
  return n->tag == IXS_ERROR || n->tag == IXS_PARSE_ERROR;
}

IXS_STATIC bool ixs_node_is_expr_kind(const ixs_node *n) {
  if (!n)
    return false;
  switch (n->tag) {
  case IXS_INT:
  case IXS_RAT:
  case IXS_SYM:
  case IXS_ADD:
  case IXS_MUL:
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
  case IXS_MOD:
  case IXS_PIECEWISE:
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_CMP:
  case IXS_AND:
  case IXS_OR:
  case IXS_NOT:
    return true;
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    return false;
  }
  return false;
}

#define IXS_BOOL_STACK_CAP 1024u

typedef struct {
  const ixs_node *node;
  uint32_t next_child;
} bool_value_frame;

IXS_STATIC bool ixs_node_is_bool_valued(const ixs_node *n) {
  bool_value_frame stack[IXS_BOOL_STACK_CAP];
  size_t depth = 0;

  if (!n)
    return false;
  if ((n->properties & IXS_NODE_PROPERTY_VALID) != 0)
    return (n->properties & IXS_NODE_PROPERTY_BOOL) != 0;
  stack[depth].node = n;
  stack[depth++].next_child = 0;
  while (depth != 0) {
    bool_value_frame *frame = &stack[depth - 1u];
    const ixs_node *cur = frame->node;
    const ixs_node *child = NULL;
    uint32_t nchildren = 0;

    switch (cur->tag) {
    case IXS_INT:
      if (cur->u.ival != 0 && cur->u.ival != 1)
        return false;
      depth--;
      continue;
    case IXS_CMP:
    case IXS_NOT:
      depth--;
      continue;
    case IXS_AND:
    case IXS_OR:
      nchildren = cur->u.assoc.nargs;
      if (frame->next_child < nchildren)
        child = cur->u.assoc.args[frame->next_child++];
      break;
    case IXS_PIECEWISE:
      nchildren = cur->u.pw.ncases;
      if (frame->next_child < nchildren)
        child = cur->u.pw.cases[frame->next_child++].value;
      break;
    default:
      return false;
    }
    if (!child) {
      if (nchildren == 0)
        return false;
      depth--;
      continue;
    }
    if (depth == IXS_BOOL_STACK_CAP)
      return false;
    stack[depth].node = child;
    stack[depth++].next_child = 0;
  }
  return true;
}

IXS_STATIC bool ixs_node_is_pred_kind(const ixs_node *n) {
  return ixs_node_is_bool_valued(n);
}

IXS_STATIC bool ixs_node_is_known_total(const ixs_node *n) {
  return node_property_total(n);
}

/* ------------------------------------------------------------------ */
/*  Error list                                                        */
/* ------------------------------------------------------------------ */

IXS_STATIC void ixs_ctx_push_error(ixs_ctx *ctx, const char *fmt, ...) {
  char buf[512];
  va_list ap;
  va_start(ap, fmt);
  vsnprintf(buf, sizeof(buf), fmt, ap);
  va_end(ap);

  char *msg = ixs_arena_strdup(&ctx->diag, buf, strlen(buf));
  if (!msg)
    return;

  if (ctx->nerrors >= ctx->errors_cap) {
    size_t new_cap = ctx->errors_cap ? ctx->errors_cap * 2 : 16;
    if (new_cap <= ctx->errors_cap ||
        new_cap > (size_t)-1 / sizeof(const char *))
      return;
    const char **new_arr = ixs_arena_grow(
        &ctx->diag, (void *)ctx->errors, ctx->errors_cap * sizeof(const char *),
        new_cap * sizeof(const char *), sizeof(void *));
    if (!new_arr)
      return;
    ctx->errors = new_arr;
    ctx->errors_cap = new_cap;
  }
  ctx->errors[ctx->nerrors++] = msg;
}

/* ------------------------------------------------------------------ */
/*  NULL / sentinel propagation                                       */
/* ------------------------------------------------------------------ */

IXS_STATIC ixs_node *ixs_propagate1(ixs_node *a) {
  if (!a)
    return NULL;
  if (ixs_node_is_sentinel(a))
    return a;
  return NULL; /* clean */
}

/*
 * If either arg is a sentinel (ERROR or PARSE_ERROR), return it so
 * the caller can short-circuit.  NULL (OOM) returns NULL -- callers
 * propagate that by their own NULL return.  Both clean -> NULL.
 */
IXS_STATIC ixs_node *ixs_propagate2(ixs_node *a, ixs_node *b) {
  if (!a || !b)
    return NULL; /* OOM propagation -- caller returns NULL */
  if (a->tag == IXS_PARSE_ERROR || b->tag == IXS_PARSE_ERROR)
    return a->tag == IXS_PARSE_ERROR ? a : b;
  if (a->tag == IXS_ERROR)
    return a;
  if (b->tag == IXS_ERROR)
    return b;
  return NULL; /* both clean */
}

/* ------------------------------------------------------------------ */
/*  Integer-valued predicate                                          */
/* ------------------------------------------------------------------ */

static bool node_rat_is_integer(const ixs_node *n) {
  int64_t p, q;
  ixs_node_get_rat(n, &p, &q);
  (void)p;
  return q == 1;
}

static bool integer_stack_push(ixs_arena *arena, const ixs_node ***stack,
                               size_t *count, size_t *capacity,
                               const ixs_node *node) {
  const ixs_node **grown;
  size_t next;
  if (!node)
    return false;
  if ((node->properties & IXS_NODE_PROPERTY_VALID) != 0)
    return (node->properties & IXS_NODE_PROPERTY_INTEGER) != 0;
  if (*count < *capacity) {
    (*stack)[(*count)++] = node;
    return true;
  }
  next = *capacity * 2u;
  if (next <= *capacity || next > SIZE_MAX / sizeof(**stack))
    return false;
  grown = ixs_arena_grow(arena, (void *)*stack, *capacity * sizeof(**stack),
                         next * sizeof(**stack), sizeof(void *));
  if (!grown)
    return false;
  *stack = grown;
  *capacity = next;
  (*stack)[(*count)++] = node;
  return true;
}

static bool integer_assoc_children(ixs_arena *arena, const ixs_node *node,
                                   const ixs_node ***stack, size_t *count,
                                   size_t *capacity) {
  uint32_t i;
  if (node->u.assoc.nargs == 0)
    return false;
  for (i = 0; i < node->u.assoc.nargs; i++)
    if (!integer_stack_push(arena, stack, count, capacity,
                            node->u.assoc.args[i]))
      return false;
  return true;
}

static bool integer_add_children(ixs_arena *arena, const ixs_node *node,
                                 const ixs_node ***stack, size_t *count,
                                 size_t *capacity) {
  uint32_t i;
  if (!node_rat_is_integer(node->u.add.coeff))
    return false;
  for (i = 0; i < node->u.add.nterms; i++)
    if (!node_rat_is_integer(node->u.add.terms[i].coeff) ||
        !integer_stack_push(arena, stack, count, capacity,
                            node->u.add.terms[i].term))
      return false;
  return true;
}

static bool integer_mul_children(ixs_arena *arena, const ixs_node *node,
                                 const ixs_node ***stack, size_t *count,
                                 size_t *capacity) {
  uint32_t i;
  if (!node_rat_is_integer(node->u.mul.coeff))
    return false;
  for (i = 0; i < node->u.mul.nfactors; i++)
    if (node->u.mul.factors[i].exp < 0 ||
        !integer_stack_push(arena, stack, count, capacity,
                            node->u.mul.factors[i].base))
      return false;
  return true;
}

static bool integer_piecewise_children(ixs_arena *arena, const ixs_node *node,
                                       const ixs_node ***stack, size_t *count,
                                       size_t *capacity) {
  uint32_t i;
  if (node->u.pw.ncases == 0)
    return false;
  for (i = 0; i < node->u.pw.ncases; i++)
    if (!integer_stack_push(arena, stack, count, capacity,
                            node->u.pw.cases[i].value))
      return false;
  return true;
}

static bool integer_node_children(ixs_arena *arena, const ixs_node *node,
                                  const ixs_node ***stack, size_t *count,
                                  size_t *capacity) {
  switch (node->tag) {
  case IXS_INT:
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
  case IXS_SYM:
  case IXS_CMP:
  case IXS_NOT:
    return true;
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
    return integer_assoc_children(arena, node, stack, count, capacity);
  case IXS_ADD:
    return integer_add_children(arena, node, stack, count, capacity);
  case IXS_MUL:
    return integer_mul_children(arena, node, stack, count, capacity);
  case IXS_MOD:
    return integer_stack_push(arena, stack, count, capacity,
                              node->u.binary.lhs) &&
           integer_stack_push(arena, stack, count, capacity,
                              node->u.binary.rhs);
  case IXS_PIECEWISE:
    return integer_piecewise_children(arena, node, stack, count, capacity);
  default:
    return false;
  }
}

/* Canonical nodes stop at the cached property.  Only trusted raw probes use
 * the transient iterative traversal. */
bool ixs_node_is_integer_valued(const ixs_node *node) {
  const ixs_node *inline_stack[16];
  const ixs_node **stack = inline_stack;
  size_t count = 0;
  size_t capacity = sizeof(inline_stack) / sizeof(inline_stack[0]);
  ixs_arena arena;
  bool result = true;
  if (!node)
    return false;
  if ((node->properties & IXS_NODE_PROPERTY_VALID) != 0)
    return (node->properties & IXS_NODE_PROPERTY_INTEGER) != 0;
  ixs_arena_init(&arena, IXS_ARENA_DEFAULT_SIZE);
  stack[count++] = node;
  while (count != 0 && result)
    result = integer_node_children(&arena, stack[--count], &stack, &count,
                                   &capacity);
  ixs_arena_destroy_transient(&arena);
  return result;
}

/* ------------------------------------------------------------------ */
/*  Type-specific accessors                                           */
/* ------------------------------------------------------------------ */

int64_t ixs_node_rat_num(const ixs_node *node) {
  assert(node && node->tag == IXS_RAT);
  return node->u.rat.p;
}

int64_t ixs_node_rat_den(const ixs_node *node) {
  assert(node && node->tag == IXS_RAT);
  return node->u.rat.q;
}

const char *ixs_node_sym_name(const ixs_node *node) {
  assert(node && node->tag == IXS_SYM);
  return node->u.name;
}

ixs_node *ixs_node_add_coeff(const ixs_node *node) {
  assert(node && node->tag == IXS_ADD);
  return node->u.add.coeff;
}

uint32_t ixs_node_add_nterms(const ixs_node *node) {
  assert(node && node->tag == IXS_ADD);
  return node->u.add.nterms;
}

ixs_node *ixs_node_add_term(const ixs_node *node, uint32_t i) {
  assert(node && node->tag == IXS_ADD && i < node->u.add.nterms);
  return node->u.add.terms[i].term;
}

ixs_node *ixs_node_add_term_coeff(const ixs_node *node, uint32_t i) {
  assert(node && node->tag == IXS_ADD && i < node->u.add.nterms);
  return node->u.add.terms[i].coeff;
}

ixs_node *ixs_node_mul_coeff(const ixs_node *node) {
  assert(node && node->tag == IXS_MUL);
  return node->u.mul.coeff;
}

uint32_t ixs_node_mul_nfactors(const ixs_node *node) {
  assert(node && node->tag == IXS_MUL);
  return node->u.mul.nfactors;
}

ixs_node *ixs_node_mul_factor_base(const ixs_node *node, uint32_t i) {
  assert(node && node->tag == IXS_MUL && i < node->u.mul.nfactors);
  return node->u.mul.factors[i].base;
}

int32_t ixs_node_mul_factor_exp(const ixs_node *node, uint32_t i) {
  assert(node && node->tag == IXS_MUL && i < node->u.mul.nfactors);
  return node->u.mul.factors[i].exp;
}

ixs_node *ixs_node_unary_arg(const ixs_node *node) {
  assert(node && (node->tag == IXS_FLOOR || node->tag == IXS_CEIL ||
                  node->tag == IXS_TRUNC || node->tag == IXS_NOT));
  if (node->tag == IXS_NOT)
    return node->u.unary_bool.arg;
  return node->u.unary.arg;
}

ixs_node *ixs_node_binary_lhs(const ixs_node *node) {
  assert(node && (node->tag == IXS_MOD || node->tag == IXS_CMP));
  return node->u.binary.lhs;
}

ixs_node *ixs_node_binary_rhs(const ixs_node *node) {
  assert(node && (node->tag == IXS_MOD || node->tag == IXS_CMP));
  return node->u.binary.rhs;
}

ixs_cmp_op ixs_node_cmp_op(const ixs_node *node) {
  assert(node && node->tag == IXS_CMP);
  return node->u.binary.cmp_op;
}

uint32_t ixs_node_pw_ncases(const ixs_node *node) {
  assert(node && node->tag == IXS_PIECEWISE);
  return node->u.pw.ncases;
}

ixs_node *ixs_node_pw_value(const ixs_node *node, uint32_t i) {
  assert(node && node->tag == IXS_PIECEWISE && i < node->u.pw.ncases);
  return node->u.pw.cases[i].value;
}

ixs_node *ixs_node_pw_cond(const ixs_node *node, uint32_t i) {
  assert(node && node->tag == IXS_PIECEWISE && i < node->u.pw.ncases);
  return node->u.pw.cases[i].cond;
}

uint32_t ixs_node_assoc_nargs(const ixs_node *node) {
  assert(node &&
         (node->tag == IXS_MAX || node->tag == IXS_MIN ||
          node->tag == IXS_XOR || node->tag == IXS_AND || node->tag == IXS_OR));
  return node->u.assoc.nargs;
}

ixs_node *ixs_node_assoc_arg(const ixs_node *node, uint32_t i) {
  assert(node &&
         (node->tag == IXS_MAX || node->tag == IXS_MIN ||
          node->tag == IXS_XOR || node->tag == IXS_AND ||
          node->tag == IXS_OR) &&
         i < node->u.assoc.nargs);
  return node->u.assoc.args[i];
}

/* ------------------------------------------------------------------ */
/*  Generic child access                                              */
/* ------------------------------------------------------------------ */

uint32_t ixs_node_nchildren(const ixs_node *node) {
  assert(node);
  switch (node->tag) {
  case IXS_ADD:
    return 1 + 2 * node->u.add.nterms;
  case IXS_MUL:
    return 1 + node->u.mul.nfactors;
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
  case IXS_NOT:
    return 1;
  case IXS_MOD:
  case IXS_CMP:
    return 2;
  case IXS_PIECEWISE:
    return 2 * node->u.pw.ncases;
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
    return node->u.assoc.nargs;
  default:
    return 0;
  }
}

ixs_node *ixs_node_child(const ixs_node *node, uint32_t i) {
  assert(node && i < ixs_node_nchildren(node));
  switch (node->tag) {
  case IXS_ADD:
    if (i == 0)
      return node->u.add.coeff;
    {
      uint32_t j = i - 1;
      if (j % 2 == 0)
        return node->u.add.terms[j / 2].coeff;
      return node->u.add.terms[j / 2].term;
    }
  case IXS_MUL:
    if (i == 0)
      return node->u.mul.coeff;
    return node->u.mul.factors[i - 1].base;
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
    return node->u.unary.arg;
  case IXS_NOT:
    return node->u.unary_bool.arg;
  case IXS_MOD:
  case IXS_CMP:
    return i == 0 ? node->u.binary.lhs : node->u.binary.rhs;
  case IXS_PIECEWISE:
    if (i % 2 == 0)
      return node->u.pw.cases[i / 2].value;
    return node->u.pw.cases[i / 2].cond;
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
    return node->u.assoc.args[i];
  default:
    return NULL;
  }
}
