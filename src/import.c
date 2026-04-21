/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "node.h"

#include <string.h>

#define IMPORT_MEMO_INIT_CAP 64u
#define IMPORT_STACK_INIT_CAP 64u

typedef struct {
  const ixs_node *src;
  ixs_node *dst;
} import_entry;

typedef struct {
  const ixs_node *src;
  uint32_t next_child;
} import_frame;

typedef struct {
  import_entry *memo;
  size_t memo_cap;
  size_t memo_used;
  import_frame *stack;
  size_t stack_cap;
} import_state;

typedef enum {
  IMPORT_DIRECT_NONE,
  IMPORT_DIRECT_READY,
  IMPORT_DIRECT_OOM
} import_direct_result;

static size_t import_hash_ptr(const void *ptr) {
  uint64_t x = (uint64_t)(uintptr_t)ptr;
  x ^= x >> 33;
  x *= 0xff51afd7ed558ccdULL;
  x ^= x >> 33;
  return (size_t)x;
}

static import_entry *import_memo_slot(import_entry *entries, size_t cap,
                                      const ixs_node *src) {
  size_t mask = cap - 1u;
  size_t idx = import_hash_ptr(src) & mask;
  while (entries[idx].src && entries[idx].src != src)
    idx = (idx + 1u) & mask;
  return &entries[idx];
}

static bool import_memo_grow(ixs_ctx *ctx, import_state *state) {
  size_t new_cap =
      state->memo_cap ? state->memo_cap * 2u : IMPORT_MEMO_INIT_CAP;
  size_t i;
  import_entry *entries;

  if (new_cap <= state->memo_cap || new_cap > (size_t)-1 / sizeof(import_entry))
    return false;

  entries = ixs_arena_alloc(&ctx->scratch, new_cap * sizeof(*entries),
                            sizeof(void *));
  if (!entries)
    return false;
  memset(entries, 0, new_cap * sizeof(*entries));

  for (i = 0; i < state->memo_cap; i++) {
    if (state->memo[i].src) {
      import_entry *slot =
          import_memo_slot(entries, new_cap, state->memo[i].src);
      *slot = state->memo[i];
    }
  }

  state->memo = entries;
  state->memo_cap = new_cap;
  return true;
}

static import_entry *import_memo_find(import_state *state,
                                      const ixs_node *src) {
  import_entry *slot;

  if (!state->memo_cap)
    return NULL;
  slot = import_memo_slot(state->memo, state->memo_cap, src);
  return slot->src ? slot : NULL;
}

static import_entry *import_memo_ensure(ixs_ctx *ctx, import_state *state,
                                        const ixs_node *src) {
  import_entry *slot;

  if (!state->memo_cap && !import_memo_grow(ctx, state))
    return NULL;

  slot = import_memo_slot(state->memo, state->memo_cap, src);
  if (slot->src)
    return slot;

  if (state->memo_used + 1u > state->memo_cap - state->memo_cap / 4u) {
    if (!import_memo_grow(ctx, state))
      return NULL;
    slot = import_memo_slot(state->memo, state->memo_cap, src);
    if (slot->src)
      return slot;
  }

  slot->src = src;
  slot->dst = NULL;
  state->memo_used++;
  return slot;
}

static bool import_stack_reserve(ixs_ctx *ctx, import_state *state,
                                 size_t need) {
  size_t old_cap = state->stack_cap;
  size_t new_cap = old_cap ? old_cap : IMPORT_STACK_INIT_CAP;
  import_frame *stack;

  if (need <= old_cap)
    return true;

  while (new_cap < need) {
    size_t doubled = new_cap * 2u;
    if (doubled <= new_cap || doubled > (size_t)-1 / sizeof(import_frame))
      return false;
    new_cap = doubled;
  }

  stack = ixs_arena_grow(&ctx->scratch, state->stack,
                         old_cap * sizeof(import_frame),
                         new_cap * sizeof(import_frame), sizeof(void *));
  if (!stack)
    return false;

  state->stack = stack;
  state->stack_cap = new_cap;
  return true;
}

static import_direct_result
import_map_direct(ixs_ctx *dst_ctx, const ixs_node *src, ixs_node **out) {
  ixs_node *dst;

  switch (src->tag) {
  case IXS_ERROR:
    *out = dst_ctx->sentinel_error;
    return IMPORT_DIRECT_READY;
  case IXS_PARSE_ERROR:
    *out = dst_ctx->sentinel_parse_error;
    return IMPORT_DIRECT_READY;
  default:
    break;
  }

  if (ixs_ctx_owns_node(dst_ctx, src)) {
    *out = (ixs_node *)src;
    return IMPORT_DIRECT_READY;
  }

  switch (src->tag) {
  case IXS_INT:
    dst = ixs_node_int(dst_ctx, src->u.ival);
    break;
  case IXS_RAT:
    dst = ixs_node_rat(dst_ctx, src->u.rat.p, src->u.rat.q);
    break;
  case IXS_SYM:
    dst = ixs_node_sym(dst_ctx, src->u.name, strlen(src->u.name));
    break;
  case IXS_TRUE:
    dst = dst_ctx->node_true;
    break;
  case IXS_FALSE:
    dst = dst_ctx->node_false;
    break;
  default:
    *out = NULL;
    return IMPORT_DIRECT_NONE;
  }

  if (!dst) {
    *out = NULL;
    return IMPORT_DIRECT_OOM;
  }

  *out = dst;
  return IMPORT_DIRECT_READY;
}

/*
 * Keep this child count and child set in sync with
 * ixs_node_nchildren()/ixs_node_child().
 *
 * ADD intentionally does not use the same per-index order as ixs_node_child():
 * it walks coeff, then term/coeff pairs so one imported addterm becomes ready
 * in a single forward pass.
 */
static bool import_child_count(const ixs_node *src, uint32_t *out) {
  switch (src->tag) {
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
    if (src->u.add.nterms > (UINT32_MAX - 1u) / 2u)
      return false;
    *out = 1u + 2u * src->u.add.nterms;
    return true;
  case IXS_MUL:
    if (src->u.mul.nfactors == UINT32_MAX)
      return false;
    *out = 1u + src->u.mul.nfactors;
    return true;
  case IXS_FLOOR:
  case IXS_CEIL:
    *out = 1;
    return true;
  case IXS_MOD:
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_CMP:
    *out = 2;
    return true;
  case IXS_PIECEWISE:
    if (src->u.pw.ncases > UINT32_MAX / 2u)
      return false;
    *out = 2u * src->u.pw.ncases;
    return true;
  case IXS_AND:
  case IXS_OR:
    *out = src->u.logic.nargs;
    return true;
  case IXS_NOT:
    *out = 1;
    return true;
  }
  return false;
}

static const ixs_node *import_child_at(const ixs_node *src, uint32_t idx) {
  switch (src->tag) {
  case IXS_ADD:
    if (idx == 0)
      return src->u.add.coeff;
    idx--;
    return (idx & 1u) == 0 ? src->u.add.terms[idx / 2u].term
                           : src->u.add.terms[idx / 2u].coeff;
  case IXS_MUL:
    if (idx == 0)
      return src->u.mul.coeff;
    return src->u.mul.factors[idx - 1u].base;
  case IXS_FLOOR:
  case IXS_CEIL:
    return src->u.unary.arg;
  case IXS_MOD:
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_CMP:
    return idx == 0 ? src->u.binary.lhs : src->u.binary.rhs;
  case IXS_PIECEWISE:
    return (idx & 1u) == 0 ? src->u.pw.cases[idx / 2u].value
                           : src->u.pw.cases[idx / 2u].cond;
  case IXS_AND:
  case IXS_OR:
    return src->u.logic.args[idx];
  case IXS_NOT:
    return src->u.unary_bool.arg;
  default:
    return NULL;
  }
}

static ixs_node *import_memo_dst(import_state *state, const ixs_node *src) {
  import_entry *slot = import_memo_find(state, src);
  return slot ? slot->dst : NULL;
}

/*
 * Imported source nodes are already in canonical structural form. Rebuild the
 * same shape in the destination store and let hash-consing collapse duplicates.
 */
static ixs_node *import_build_node(ixs_ctx *dst_ctx, import_state *state,
                                   const ixs_node *src) {
  uint32_t i;

  switch (src->tag) {
  case IXS_ADD: {
    ixs_node *coeff = import_memo_dst(state, src->u.add.coeff);
    ixs_addterm *terms = NULL;

    if (!coeff)
      return NULL;
    if (src->u.add.nterms > 0) {
      size_t sz = (size_t)src->u.add.nterms * sizeof(ixs_addterm);
      if (sz / sizeof(ixs_addterm) != src->u.add.nterms)
        return NULL;
      terms = ixs_arena_alloc(&dst_ctx->scratch, sz, sizeof(void *));
      if (!terms)
        return NULL;
      for (i = 0; i < src->u.add.nterms; i++) {
        terms[i].term = import_memo_dst(state, src->u.add.terms[i].term);
        terms[i].coeff = import_memo_dst(state, src->u.add.terms[i].coeff);
        if (!terms[i].term || !terms[i].coeff)
          return NULL;
      }
    }
    return ixs_node_add(dst_ctx, coeff, src->u.add.nterms, terms);
  }

  case IXS_MUL: {
    ixs_node *coeff = import_memo_dst(state, src->u.mul.coeff);
    ixs_mulfactor *factors = NULL;

    if (!coeff)
      return NULL;
    if (src->u.mul.nfactors > 0) {
      size_t sz = (size_t)src->u.mul.nfactors * sizeof(ixs_mulfactor);
      if (sz / sizeof(ixs_mulfactor) != src->u.mul.nfactors)
        return NULL;
      factors = ixs_arena_alloc(&dst_ctx->scratch, sz, sizeof(void *));
      if (!factors)
        return NULL;
      for (i = 0; i < src->u.mul.nfactors; i++) {
        factors[i].base = import_memo_dst(state, src->u.mul.factors[i].base);
        factors[i].exp = src->u.mul.factors[i].exp;
        if (!factors[i].base)
          return NULL;
      }
    }
    return ixs_node_mul(dst_ctx, coeff, src->u.mul.nfactors, factors);
  }

  case IXS_FLOOR:
  case IXS_CEIL: {
    ixs_node *arg = import_memo_dst(state, src->u.unary.arg);
    if (!arg)
      return NULL;
    return src->tag == IXS_FLOOR ? ixs_node_floor(dst_ctx, arg)
                                 : ixs_node_ceil(dst_ctx, arg);
  }

  case IXS_MOD:
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_CMP: {
    ixs_node *lhs = import_memo_dst(state, src->u.binary.lhs);
    ixs_node *rhs = import_memo_dst(state, src->u.binary.rhs);
    if (!lhs || !rhs)
      return NULL;
    return ixs_node_binary(dst_ctx, src->tag, lhs, rhs, src->u.binary.cmp_op);
  }

  case IXS_PIECEWISE: {
    ixs_pwcase *cases = NULL;

    if (src->u.pw.ncases > 0) {
      size_t sz = (size_t)src->u.pw.ncases * sizeof(ixs_pwcase);
      if (sz / sizeof(ixs_pwcase) != src->u.pw.ncases)
        return NULL;
      cases = ixs_arena_alloc(&dst_ctx->scratch, sz, sizeof(void *));
      if (!cases)
        return NULL;
      for (i = 0; i < src->u.pw.ncases; i++) {
        cases[i].value = import_memo_dst(state, src->u.pw.cases[i].value);
        cases[i].cond = import_memo_dst(state, src->u.pw.cases[i].cond);
        if (!cases[i].value || !cases[i].cond)
          return NULL;
      }
    }
    return ixs_node_pw(dst_ctx, src->u.pw.ncases, cases);
  }

  case IXS_AND:
  case IXS_OR: {
    ixs_node **args = NULL;

    if (src->u.logic.nargs > 0) {
      size_t sz = (size_t)src->u.logic.nargs * sizeof(ixs_node *);
      if (sz / sizeof(ixs_node *) != src->u.logic.nargs)
        return NULL;
      args = ixs_arena_alloc(&dst_ctx->scratch, sz, sizeof(void *));
      if (!args)
        return NULL;
      for (i = 0; i < src->u.logic.nargs; i++) {
        args[i] = import_memo_dst(state, src->u.logic.args[i]);
        if (!args[i])
          return NULL;
      }
    }
    return ixs_node_logic(dst_ctx, src->tag, src->u.logic.nargs, args);
  }

  case IXS_NOT: {
    ixs_node *arg = import_memo_dst(state, src->u.unary_bool.arg);
    if (!arg)
      return NULL;
    return ixs_node_not(dst_ctx, arg);
  }

  default:
    return NULL;
  }
}

static ixs_node *import_root(ixs_ctx *dst_ctx, import_state *state,
                             const ixs_node *src) {
  import_entry *slot;
  ixs_node *mapped;
  import_direct_result direct;
  size_t depth = 0;
  uint32_t nchildren;

  if (!src)
    return NULL;

  slot = import_memo_find(state, src);
  if (slot && slot->dst)
    return slot->dst;

  direct = import_map_direct(dst_ctx, src, &mapped);
  if (direct == IMPORT_DIRECT_OOM)
    return NULL;
  if (direct == IMPORT_DIRECT_READY) {
    if (!slot)
      slot = import_memo_ensure(dst_ctx, state, src);
    if (!slot)
      return NULL;
    slot->dst = mapped;
    return mapped;
  }

  if (!slot)
    slot = import_memo_ensure(dst_ctx, state, src);
  if (!slot || slot->dst)
    return slot ? slot->dst : NULL;

  if (!import_stack_reserve(dst_ctx, state, 1))
    return NULL;
  state->stack[depth].src = src;
  state->stack[depth].next_child = 0;
  depth++;

  while (depth > 0) {
    import_frame *frame = &state->stack[depth - 1u];
    const ixs_node *cur = frame->src;

    if (!import_child_count(cur, &nchildren))
      return NULL;

    if (frame->next_child < nchildren) {
      const ixs_node *child = import_child_at(cur, frame->next_child++);
      import_entry *child_slot;

      if (!child)
        return NULL;
      child_slot = import_memo_find(state, child);

      if (child_slot && child_slot->dst)
        continue;

      direct = import_map_direct(dst_ctx, child, &mapped);
      if (direct == IMPORT_DIRECT_OOM)
        return NULL;
      if (direct == IMPORT_DIRECT_READY) {
        if (!child_slot)
          child_slot = import_memo_ensure(dst_ctx, state, child);
        if (!child_slot)
          return NULL;
        child_slot->dst = mapped;
        continue;
      }

      if (!child_slot)
        child_slot = import_memo_ensure(dst_ctx, state, child);
      if (!child_slot)
        return NULL;
      if (child_slot->dst)
        continue;

      if (!import_stack_reserve(dst_ctx, state, depth + 1u))
        return NULL;
      state->stack[depth].src = child;
      state->stack[depth].next_child = 0;
      depth++;
      continue;
    }

    mapped = import_build_node(dst_ctx, state, cur);
    if (!mapped)
      return NULL;

    slot = import_memo_find(state, cur);
    if (!slot)
      return NULL;
    slot->dst = mapped;
    depth--;
  }

  slot = import_memo_find(state, src);
  return slot ? slot->dst : NULL;
}

ixs_node *ixs_import_node(ixs_session *s, const ixs_node *src) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_arena_mark mark = ixs_arena_save(&ctx->scratch);
  import_state state;
  ixs_node *result;

  if (!src) {
    ixs_session_unbind(&binding);
    return NULL;
  }

  memset(&state, 0, sizeof(state));
  result = import_root(ctx, &state, src);
  ixs_arena_restore(&ctx->scratch, mark);
  ixs_session_unbind(&binding);
  return result;
}

bool ixs_import_many(ixs_session *s, const ixs_node *const *src, size_t count,
                     ixs_node **out) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_arena_mark mark = ixs_arena_save(&ctx->scratch);
  import_state state;
  ixs_node **tmp = NULL;
  size_t i;
  bool ok = true;

  if (count == 0) {
    ixs_session_unbind(&binding);
    return true;
  }
  if (!src || !out) {
    ixs_session_unbind(&binding);
    return false;
  }

  memset(&state, 0, sizeof(state));

  {
    size_t sz = count * sizeof(ixs_node *);
    if (sz / sizeof(ixs_node *) != count) {
      ok = false;
    } else {
      tmp = ixs_arena_alloc(&ctx->scratch, sz, sizeof(void *));
      if (!tmp)
        ok = false;
    }
  }

  for (i = 0; ok && i < count; i++) {
    if (!src[i]) {
      ok = false;
      break;
    }
    tmp[i] = import_root(ctx, &state, src[i]);
    if (!tmp[i])
      ok = false;
  }

  if (ok) {
    for (i = 0; i < count; i++)
      out[i] = tmp[i];
  }

  ixs_arena_restore(&ctx->scratch, mark);
  ixs_session_unbind(&binding);
  return ok;
}
