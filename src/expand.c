/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "expand.h"
#include "hash.h"
#include "node.h"
#include "simplify.h"

#include <string.h>

#define EXPAND_MEMO_INIT_CAP 64u
#define EXPAND_STACK_INIT_CAP 64u

typedef enum {
  EXPAND_MEMO_EMPTY = 0,
  EXPAND_MEMO_ACTIVE,
  EXPAND_MEMO_COMPLETE
} expand_memo_state;

typedef struct {
  ixs_node *source;
  ixs_node *result;
  expand_memo_state state;
} expand_memo_entry;

typedef struct {
  ixs_node *node;
  uint32_t next_child;
} expand_frame;

typedef struct {
  expand_memo_entry *memo;
  size_t memo_cap;
  size_t memo_used;
  expand_frame *stack;
  size_t stack_cap;
} expand_state;

static bool expand_cacheable(const ixs_node *expr) {
  return expr && !ixs_node_is_sentinel(expr) && expr->tag != IXS_INT &&
         expr->tag != IXS_RAT && expr->tag != IXS_SYM;
}

static expand_memo_entry *expand_memo_slot(expand_memo_entry *entries,
                                           size_t capacity,
                                           const ixs_node *source) {
  size_t mask = capacity - 1u;
  size_t slot = ixs_hash_ptr(source) & mask;
  while (entries[slot].source && entries[slot].source != source)
    slot = (slot + 1u) & mask;
  return &entries[slot];
}

static bool expand_memo_grow(ixs_ctx *ctx, expand_state *state) {
  size_t next = state->memo_cap ? state->memo_cap * 2u : EXPAND_MEMO_INIT_CAP;
  expand_memo_entry *grown;
  size_t i;

  if (next <= state->memo_cap || next > (size_t)-1 / sizeof(expand_memo_entry))
    return false;
  grown = ixs_arena_alloc(&ctx->scratch, next * sizeof(*grown), sizeof(void *));
  if (!grown)
    return false;
  memset(grown, 0, next * sizeof(*grown));
  for (i = 0; i < state->memo_cap; i++) {
    if (state->memo[i].source) {
      expand_memo_entry *slot =
          expand_memo_slot(grown, next, state->memo[i].source);
      *slot = state->memo[i];
    }
  }
  state->memo = grown;
  state->memo_cap = next;
  return true;
}

static expand_memo_entry *expand_memo_find(expand_state *state,
                                           const ixs_node *source) {
  expand_memo_entry *slot;
  if (!state->memo_cap)
    return NULL;
  slot = expand_memo_slot(state->memo, state->memo_cap, source);
  return slot->source ? slot : NULL;
}

static expand_memo_entry *expand_memo_ensure(ixs_ctx *ctx, expand_state *state,
                                             ixs_node *source) {
  expand_memo_entry *slot;
  if (!state->memo_cap && !expand_memo_grow(ctx, state))
    return NULL;
  slot = expand_memo_slot(state->memo, state->memo_cap, source);
  if (slot->source)
    return slot;
  if (state->memo_used + 1u > state->memo_cap - state->memo_cap / 4u) {
    if (!expand_memo_grow(ctx, state))
      return NULL;
    slot = expand_memo_slot(state->memo, state->memo_cap, source);
    if (slot->source)
      return slot;
  }
  slot->source = source;
  slot->result = NULL;
  slot->state = EXPAND_MEMO_EMPTY;
  state->memo_used++;
  return slot;
}

static bool expand_stack_reserve(ixs_ctx *ctx, expand_state *state,
                                 size_t need) {
  size_t old_cap = state->stack_cap;
  size_t next = old_cap ? old_cap : EXPAND_STACK_INIT_CAP;
  expand_frame *grown;
  if (need <= old_cap)
    return true;
  while (next < need) {
    size_t doubled = next * 2u;
    if (doubled <= next || doubled > (size_t)-1 / sizeof(expand_frame))
      return false;
    next = doubled;
  }
  grown = ixs_arena_grow(&ctx->scratch, state->stack, old_cap * sizeof(*grown),
                         next * sizeof(*grown), sizeof(void *));
  if (!grown)
    return false;
  state->stack = grown;
  state->stack_cap = next;
  return true;
}

static bool expand_child_count(const ixs_node *node, uint32_t *out) {
  switch (node->tag) {
  case IXS_INT:
  case IXS_RAT:
  case IXS_SYM:
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
  case IXS_TRUNC:
  case IXS_NOT:
    *out = 1;
    return true;
  case IXS_MOD:
  case IXS_CMP:
    *out = 2;
    return true;
  case IXS_PIECEWISE:
    if (node->u.pw.ncases > UINT32_MAX / 2u)
      return false;
    *out = 2u * node->u.pw.ncases;
    return true;
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
    *out = node->u.assoc.nargs;
    return true;
  }
  *out = 0;
  return true;
}

static ixs_node *expand_child_at(const ixs_node *node, uint32_t index) {
  switch (node->tag) {
  case IXS_ADD:
    if (index == 0)
      return node->u.add.coeff;
    index--;
    return (index & 1u) == 0 ? node->u.add.terms[index / 2u].coeff
                             : node->u.add.terms[index / 2u].term;
  case IXS_MUL:
    if (index == 0)
      return node->u.mul.coeff;
    return node->u.mul.factors[index - 1u].base;
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
    return node->u.unary.arg;
  case IXS_NOT:
    return node->u.unary_bool.arg;
  case IXS_MOD:
  case IXS_CMP:
    return index == 0 ? node->u.binary.lhs : node->u.binary.rhs;
  case IXS_PIECEWISE:
    return (index & 1u) == 0 ? node->u.pw.cases[index / 2u].value
                             : node->u.pw.cases[index / 2u].cond;
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
    return node->u.assoc.args[index];
  default:
    return NULL;
  }
}

static ixs_node *expand_resolved(ixs_ctx *ctx, expand_state *state,
                                 ixs_node *source) {
  expand_memo_entry *slot;
  ixs_node *cached;
  if (!source)
    return NULL;
  if (!expand_cacheable(source))
    return source;
  cached = ixs_node_expand_cache_lookup(ctx, source, 0);
  if (cached)
    return cached;
  slot = expand_memo_find(state, source);
  return slot && slot->state == EXPAND_MEMO_COMPLETE ? slot->result : NULL;
}

/*
 * Multiply a * b, distributing over ADD on either side. Both operands are
 * already expanded. Canonical ADD nodes are flat, so this helper's call depth
 * is bounded by the two operands rather than by input DAG depth.
 */
static ixs_node *mul_expand(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  uint32_t i;
  ixs_node *result;
  if (!a || !b)
    return NULL;
  if (ixs_node_is_sentinel(a))
    return a;
  if (ixs_node_is_sentinel(b))
    return b;

  if (a->tag == IXS_ADD) {
    result = mul_expand(ctx, a->u.add.coeff, b);
    if (!result || ixs_node_is_sentinel(result))
      return result;
    for (i = 0; i < a->u.add.nterms; i++) {
      ixs_node *term = mul_expand(ctx, a->u.add.terms[i].term, b);
      ixs_node *scaled;
      if (!term || ixs_node_is_sentinel(term))
        return term;
      scaled = mul_expand(ctx, a->u.add.terms[i].coeff, term);
      if (!scaled || ixs_node_is_sentinel(scaled))
        return scaled;
      result = simp_add(ctx, result, scaled);
      if (!result || ixs_node_is_sentinel(result))
        return result;
    }
    return result;
  }
  if (b->tag == IXS_ADD)
    return mul_expand(ctx, b, a);
  return simp_mul(ctx, a, b);
}

/* Every representable positive exponent takes logarithmic multiply steps. */
static ixs_node *expand_positive_power(ixs_ctx *ctx, ixs_node *base,
                                       uint32_t exponent) {
  ixs_node *result = ixs_node_int(ctx, 1);
  ixs_node *power = base;
  if (!result)
    return NULL;
  while (exponent != 0) {
    if ((exponent & 1u) != 0) {
      result = mul_expand(ctx, result, power);
      if (!result || ixs_node_is_sentinel(result))
        return result;
    }
    exponent >>= 1u;
    if (exponent != 0) {
      power = mul_expand(ctx, power, power);
      if (!power || ixs_node_is_sentinel(power))
        return power;
    }
  }
  return result;
}

/* Negative powers are not distributive. Preserve the signed int32 exponent
 * directly, including INT32_MIN, instead of negating it through a magnitude. */
static ixs_node *expand_negative_power(ixs_ctx *ctx, ixs_node *result,
                                       ixs_node *base, int32_t exponent) {
  ixs_mulfactor factor;
  ixs_node *one;
  ixs_node *power;
  factor.base = base;
  factor.exp = exponent;
  one = ixs_node_int(ctx, 1);
  if (!one)
    return NULL;
  power = ixs_node_mul(ctx, one, 1, &factor);
  return power ? simp_mul(ctx, result, power) : NULL;
}

static ixs_node *expand_build_add(ixs_ctx *ctx, expand_state *state,
                                  ixs_node *node) {
  uint32_t i;
  ixs_node *result = expand_resolved(ctx, state, node->u.add.coeff);
  if (!result || ixs_node_is_sentinel(result))
    return result;
  for (i = 0; i < node->u.add.nterms; i++) {
    ixs_node *coeff = expand_resolved(ctx, state, node->u.add.terms[i].coeff);
    ixs_node *term = expand_resolved(ctx, state, node->u.add.terms[i].term);
    ixs_node *scaled;
    if (!coeff || ixs_node_is_sentinel(coeff))
      return coeff;
    if (!term || ixs_node_is_sentinel(term))
      return term;
    scaled = mul_expand(ctx, coeff, term);
    if (!scaled || ixs_node_is_sentinel(scaled))
      return scaled;
    result = simp_add(ctx, result, scaled);
    if (!result || ixs_node_is_sentinel(result))
      return result;
  }
  return result;
}

static ixs_node *expand_build_mul(ixs_ctx *ctx, expand_state *state,
                                  ixs_node *node) {
  uint32_t i;
  ixs_node *result = expand_resolved(ctx, state, node->u.mul.coeff);
  if (!result || ixs_node_is_sentinel(result))
    return result;
  for (i = 0; i < node->u.mul.nfactors; i++) {
    int32_t exponent = node->u.mul.factors[i].exp;
    ixs_node *base = expand_resolved(ctx, state, node->u.mul.factors[i].base);
    if (!base || ixs_node_is_sentinel(base))
      return base;
    if (exponent == 0) {
      ixs_ctx_push_error(ctx, "expand: malformed zero exponent");
      return ctx->sentinel_error;
    }
    if (exponent > 0) {
      ixs_node *power = expand_positive_power(ctx, base, (uint32_t)exponent);
      if (!power || ixs_node_is_sentinel(power))
        return power;
      result = mul_expand(ctx, result, power);
    } else {
      result = expand_negative_power(ctx, result, base, exponent);
    }
    if (!result || ixs_node_is_sentinel(result))
      return result;
  }
  return result;
}

static ixs_node *expand_build_binary(ixs_ctx *ctx, expand_state *state,
                                     ixs_node *node) {
  ixs_node *lhs = expand_resolved(ctx, state, node->u.binary.lhs);
  ixs_node *rhs = expand_resolved(ctx, state, node->u.binary.rhs);
  if (!lhs || ixs_node_is_sentinel(lhs))
    return lhs;
  if (!rhs || ixs_node_is_sentinel(rhs))
    return rhs;
  if (node->tag == IXS_MOD)
    return simp_mod(ctx, lhs, rhs);
  return simp_cmp(ctx, lhs, node->u.binary.cmp_op, rhs);
}

static ixs_node *expand_build_pw(ixs_ctx *ctx, expand_state *state,
                                 ixs_node *node) {
  ixs_arena_mark mark = ixs_arena_save(&ctx->scratch);
  uint32_t count = node->u.pw.ncases;
  ixs_node **values = NULL;
  ixs_node **conditions = NULL;
  ixs_node *result = NULL;
  uint32_t i;
  if (count > 0) {
    size_t bytes = (size_t)count * sizeof(*values);
    if (bytes / sizeof(*values) != count)
      goto done;
    values = ixs_arena_alloc(&ctx->scratch, bytes, sizeof(void *));
    conditions = ixs_arena_alloc(&ctx->scratch, bytes, sizeof(void *));
    if (!values || !conditions)
      goto done;
    for (i = 0; i < count; i++) {
      values[i] = expand_resolved(ctx, state, node->u.pw.cases[i].value);
      conditions[i] = expand_resolved(ctx, state, node->u.pw.cases[i].cond);
      if (!values[i] || !conditions[i])
        goto done;
      if (ixs_node_is_sentinel(values[i])) {
        result = values[i];
        goto done;
      }
      if (ixs_node_is_sentinel(conditions[i])) {
        result = conditions[i];
        goto done;
      }
    }
  }
  result = simp_pw(ctx, count, values, conditions);
done:
  ixs_arena_restore(&ctx->scratch, mark);
  return result;
}

static ixs_node *expand_build_assoc(ixs_ctx *ctx, expand_state *state,
                                    ixs_node *node) {
  ixs_arena_mark mark = ixs_arena_save(&ctx->scratch);
  uint32_t count = node->u.assoc.nargs;
  ixs_node **args = NULL;
  ixs_node *result = NULL;
  uint32_t i;
  if (count > 0) {
    size_t bytes = (size_t)count * sizeof(*args);
    if (bytes / sizeof(*args) != count)
      goto done;
    args = ixs_arena_alloc(&ctx->scratch, bytes, sizeof(void *));
    if (!args)
      goto done;
    for (i = 0; i < count; i++) {
      args[i] = expand_resolved(ctx, state, node->u.assoc.args[i]);
      if (!args[i] || ixs_node_is_sentinel(args[i])) {
        result = args[i];
        goto done;
      }
    }
  }
  switch (node->tag) {
  case IXS_MAX:
    result = simp_max_many(ctx, count, args);
    break;
  case IXS_MIN:
    result = simp_min_many(ctx, count, args);
    break;
  case IXS_XOR:
    result = simp_xor_many(ctx, count, args);
    break;
  case IXS_AND:
    result = simp_and_many(ctx, count, args);
    break;
  case IXS_OR:
    result = simp_or_many(ctx, count, args);
    break;
  default:
    break;
  }
done:
  ixs_arena_restore(&ctx->scratch, mark);
  return result;
}

static ixs_node *expand_build_simple_node(ixs_ctx *ctx, expand_state *state,
                                          ixs_node *node) {
  ixs_node *arg;
  switch (node->tag) {
  case IXS_INT:
  case IXS_RAT:
  case IXS_SYM:
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    return node;
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
    arg = expand_resolved(ctx, state, node->u.unary.arg);
    if (!arg || ixs_node_is_sentinel(arg))
      return arg;
    if (node->tag == IXS_FLOOR)
      return simp_floor(ctx, arg);
    if (node->tag == IXS_CEIL)
      return simp_ceil(ctx, arg);
    return simp_trunc(ctx, arg);
  case IXS_MOD:
  case IXS_CMP:
    return expand_build_binary(ctx, state, node);
  case IXS_NOT:
    arg = expand_resolved(ctx, state, node->u.unary_bool.arg);
    return !arg || ixs_node_is_sentinel(arg) ? arg : simp_not(ctx, arg);
  default:
    return node;
  }
}

static ixs_node *expand_build_node(ixs_ctx *ctx, expand_state *state,
                                   ixs_node *node) {
  switch (node->tag) {
  case IXS_ADD:
    return expand_build_add(ctx, state, node);
  case IXS_MUL:
    return expand_build_mul(ctx, state, node);
  case IXS_PIECEWISE:
    return expand_build_pw(ctx, state, node);
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
    return expand_build_assoc(ctx, state, node);
  default:
    return expand_build_simple_node(ctx, state, node);
  }
}

static ixs_node *expand_root(ixs_ctx *ctx, expand_state *state,
                             ixs_node *root) {
  expand_memo_entry *slot;
  ixs_node *result;
  size_t depth = 0;

  if (!root)
    return NULL;
  result = expand_resolved(ctx, state, root);
  if (result)
    return result;
  slot = expand_memo_ensure(ctx, state, root);
  if (!slot)
    return NULL;
  slot->state = EXPAND_MEMO_ACTIVE;
  if (!expand_stack_reserve(ctx, state, 1))
    return NULL;
  state->stack[depth].node = root;
  state->stack[depth].next_child = 0;
  depth++;

  while (depth > 0) {
    expand_frame *frame = &state->stack[depth - 1u];
    ixs_node *node = frame->node;
    uint32_t child_count;
    if (!expand_child_count(node, &child_count)) {
      ixs_ctx_push_error(ctx, "expand: malformed child count");
      return ctx->sentinel_error;
    }
    if (frame->next_child < child_count) {
      ixs_node *child = expand_child_at(node, frame->next_child++);
      ixs_node *resolved;
      expand_memo_entry *child_slot;
      if (!child) {
        ixs_ctx_push_error(ctx, "expand: malformed null child");
        return ctx->sentinel_error;
      }
      resolved = expand_resolved(ctx, state, child);
      if (resolved)
        continue;
      child_slot = expand_memo_find(state, child);
      if (child_slot && child_slot->state == EXPAND_MEMO_ACTIVE) {
        ixs_ctx_push_error(ctx, "expand: cyclic expression graph");
        return ctx->sentinel_error;
      }
      if (!child_slot)
        child_slot = expand_memo_ensure(ctx, state, child);
      if (!child_slot)
        return NULL;
      child_slot->state = EXPAND_MEMO_ACTIVE;
      if (!expand_stack_reserve(ctx, state, depth + 1u))
        return NULL;
      state->stack[depth].node = child;
      state->stack[depth].next_child = 0;
      depth++;
      continue;
    }

    result = expand_build_node(ctx, state, node);
    if (!result)
      return NULL;
    slot = expand_memo_find(state, node);
    if (!slot || slot->state != EXPAND_MEMO_ACTIVE)
      return NULL;
    slot->result = result;
    slot->state = EXPAND_MEMO_COMPLETE;
    if (!ixs_node_is_sentinel(result))
      ixs_node_expand_cache_store(ctx, node, result, 0);
    depth--;
  }
  return expand_resolved(ctx, state, root);
}

IXS_STATIC ixs_node *expand_impl(ixs_ctx *ctx, ixs_node *expr) {
  ixs_arena_mark mark;
  expand_state state;
  ixs_node *result;
  if (!expr)
    return NULL;
  if (ixs_node_is_sentinel(expr))
    return expr;
  mark = ixs_arena_save(&ctx->scratch);
  memset(&state, 0, sizeof(state));
  result = expand_root(ctx, &state, expr);
  ixs_arena_restore(&ctx->scratch, mark);
  return result;
}
