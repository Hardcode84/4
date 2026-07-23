/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "expand.h"
#include "node.h"
#include "simplify.h"

#define EXPAND_MAX_DEPTH 256
#define EXPAND_MAX_EXP 64

static bool expand_cacheable(const ixs_node *expr) {
  return expr && !ixs_node_is_sentinel(expr) && expr->tag != IXS_INT &&
         expr->tag != IXS_RAT && expr->tag != IXS_SYM;
}

static ixs_node *do_expand(ixs_ctx *ctx, ixs_node *node, int depth);

/*
 * Multiply a * b, distributing over ADD on either side.
 * Both operands must already be expanded (no MUL-over-ADD internally).
 * Recursion depth is bounded by the ADD nesting depth of a and b,
 * which is at most 2 for already-expanded inputs.
 */
static ixs_node *mul_expand(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  if (!a || !b)
    return NULL;
  if (ixs_node_is_sentinel(a))
    return a;
  if (ixs_node_is_sentinel(b))
    return b;

  if (a->tag == IXS_ADD) {
    ixs_node *result = mul_expand(ctx, a->u.add.coeff, b);
    for (uint32_t i = 0; i < a->u.add.nterms; i++) {
      ixs_node *tc = a->u.add.terms[i].coeff;
      ixs_node *tt = a->u.add.terms[i].term;
      ixs_node *tb = mul_expand(ctx, tt, b);
      result = simp_add(ctx, result, mul_expand(ctx, tc, tb));
    }
    return result;
  }
  if (b->tag == IXS_ADD)
    return mul_expand(ctx, b, a);

  return simp_mul(ctx, a, b);
}

static ixs_node *expand_add(ixs_ctx *ctx, ixs_node *node, int depth) {
  uint32_t i;
  ixs_node *result = node->u.add.coeff;
  for (i = 0; i < node->u.add.nterms; i++) {
    ixs_node *tc = node->u.add.terms[i].coeff;
    ixs_node *tt = do_expand(ctx, node->u.add.terms[i].term, depth + 1);
    result = simp_add(ctx, result, mul_expand(ctx, tc, tt));
  }
  return result;
}

static bool expand_exp_mag(ixs_ctx *ctx, int32_t exp, int32_t *mag) {
  *mag = (exp > 0) ? exp : (exp == INT32_MIN) ? INT32_MAX : -exp;
  if (*mag <= EXPAND_MAX_EXP)
    return true;
  ixs_ctx_push_error(ctx, "expand: exponent magnitude (%d) exceeds limit",
                     *mag);
  return false;
}

static ixs_node *expand_negative_power(ixs_ctx *ctx, ixs_node *result,
                                       ixs_node *base, int32_t mag) {
  int32_t e;
  ixs_node *pow = base;
  for (e = 1; e < mag; e++)
    pow = simp_mul(ctx, pow, base);
  return simp_div(ctx, result, pow);
}

static ixs_node *expand_mul(ixs_ctx *ctx, ixs_node *node, int depth) {
  uint32_t i;
  ixs_node *result = node->u.mul.coeff;
  for (i = 0; i < node->u.mul.nfactors; i++) {
    int32_t e, mag;
    ixs_node *base = do_expand(ctx, node->u.mul.factors[i].base, depth + 1);
    int32_t exp = node->u.mul.factors[i].exp;
    if (!expand_exp_mag(ctx, exp, &mag))
      return ctx->sentinel_error;
    if (exp > 0) {
      for (e = 0; e < exp; e++)
        result = mul_expand(ctx, result, base);
    } else {
      result = expand_negative_power(ctx, result, base, mag);
    }
  }
  return result;
}

static ixs_node *expand_binary(ixs_ctx *ctx, ixs_node *node, int depth) {
  ixs_node *lhs = do_expand(ctx, node->u.binary.lhs, depth + 1);
  ixs_node *rhs = do_expand(ctx, node->u.binary.rhs, depth + 1);
  switch (node->tag) {
  case IXS_MOD:
    return simp_mod(ctx, lhs, rhs);
  case IXS_MAX:
    return simp_max(ctx, lhs, rhs);
  case IXS_MIN:
    return simp_min(ctx, lhs, rhs);
  case IXS_XOR:
    return simp_xor(ctx, lhs, rhs);
  case IXS_CMP:
    return simp_cmp(ctx, lhs, node->u.binary.cmp_op, rhs);
  default:
    return node;
  }
}

static ixs_node *expand_pw(ixs_ctx *ctx, ixs_node *node, int depth) {
  uint32_t i;
  uint32_t nc = node->u.pw.ncases;
  ixs_arena_mark sm = ixs_arena_save(&ctx->scratch);
  ixs_node **vals =
      ixs_arena_alloc(&ctx->scratch, nc * sizeof(*vals), sizeof(void *));
  ixs_node **conds =
      ixs_arena_alloc(&ctx->scratch, nc * sizeof(*conds), sizeof(void *));
  ixs_node *result;
  if (!vals || !conds) {
    ixs_arena_restore(&ctx->scratch, sm);
    return NULL;
  }
  for (i = 0; i < nc; i++) {
    vals[i] = do_expand(ctx, node->u.pw.cases[i].value, depth + 1);
    conds[i] = do_expand(ctx, node->u.pw.cases[i].cond, depth + 1);
  }
  result = simp_pw(ctx, nc, vals, conds);
  ixs_arena_restore(&ctx->scratch, sm);
  return result;
}

static ixs_node *expand_logic(ixs_ctx *ctx, ixs_node *node, int depth) {
  uint32_t i;
  uint32_t na = node->u.logic.nargs;
  ixs_node *result;
  if (na < 2)
    return node;
  result = do_expand(ctx, node->u.logic.args[0], depth + 1);
  for (i = 1; i < na; i++) {
    ixs_node *arg = do_expand(ctx, node->u.logic.args[i], depth + 1);
    result = (node->tag == IXS_AND) ? simp_and(ctx, result, arg)
                                    : simp_or(ctx, result, arg);
  }
  return result;
}

static ixs_node *do_expand(ixs_ctx *ctx, ixs_node *node, int depth) {
  if (!node)
    return NULL;
  if (ixs_node_is_sentinel(node))
    return node;
  if (depth >= EXPAND_MAX_DEPTH) {
    ixs_ctx_push_error(ctx, "expand: recursion depth limit (%d) exceeded",
                       EXPAND_MAX_DEPTH);
    return ctx->sentinel_error;
  }

  switch (node->tag) {
  case IXS_INT:
  case IXS_RAT:
  case IXS_SYM:
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    return node;

  case IXS_ADD:
    return expand_add(ctx, node, depth);

  case IXS_MUL:
    return expand_mul(ctx, node, depth);

  case IXS_FLOOR:
    return simp_floor(ctx, do_expand(ctx, node->u.unary.arg, depth + 1));
  case IXS_CEIL:
    return simp_ceil(ctx, do_expand(ctx, node->u.unary.arg, depth + 1));

  case IXS_MOD:
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_CMP:
    return expand_binary(ctx, node, depth);

  case IXS_PIECEWISE:
    return expand_pw(ctx, node, depth);

  case IXS_AND:
  case IXS_OR:
    return expand_logic(ctx, node, depth);

  case IXS_NOT:
    return simp_not(ctx, do_expand(ctx, node->u.unary_bool.arg, depth + 1));

  default:
    return node;
  }
}

IXS_STATIC ixs_node *expand_impl(ixs_ctx *ctx, ixs_node *expr) {
  ixs_node *cached;
  ixs_node *expanded;

  if (!expand_cacheable(expr))
    return do_expand(ctx, expr, 0);
  cached =
      ixs_node_transform_cache_lookup(ctx, expr, IXS_NODE_TRANSFORM_EXPAND);
  if (cached)
    return cached;

  expanded = do_expand(ctx, expr, 0);
  ixs_node_transform_cache_store(ctx, expr, IXS_NODE_TRANSFORM_EXPAND,
                                 expanded);
  return expanded;
}
