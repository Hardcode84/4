/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "node.h"
#include "simplify.h"
#include <ixsimpl.h>

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
      result = ixs_add(ctx, result, mul_expand(ctx, tc, tb));
    }
    return result;
  }
  if (b->tag == IXS_ADD)
    return mul_expand(ctx, b, a);

  return ixs_mul(ctx, a, b);
}

/*
 * Recursive expand: walk the DAG, distributing MUL factors that are ADD.
 * Recursion depth bounded by DAG depth.
 */
static ixs_node *do_expand(ixs_ctx *ctx, ixs_node *node) {
  if (!node)
    return NULL;
  if (ixs_node_is_sentinel(node))
    return node;

  switch (node->tag) {
  case IXS_INT:
  case IXS_RAT:
  case IXS_SYM:
  case IXS_TRUE:
  case IXS_FALSE:
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    return node;

  case IXS_ADD: {
    ixs_node *result = node->u.add.coeff;
    for (uint32_t i = 0; i < node->u.add.nterms; i++) {
      ixs_node *tc = node->u.add.terms[i].coeff;
      ixs_node *tt = do_expand(ctx, node->u.add.terms[i].term);
      result = ixs_add(ctx, result, mul_expand(ctx, tc, tt));
    }
    return result;
  }

  case IXS_MUL: {
    ixs_node *result = node->u.mul.coeff;
    for (uint32_t i = 0; i < node->u.mul.nfactors; i++) {
      ixs_node *base = do_expand(ctx, node->u.mul.factors[i].base);
      int32_t exp = node->u.mul.factors[i].exp;
      if (exp > 0) {
        for (int32_t e = 0; e < exp; e++)
          result = mul_expand(ctx, result, base);
      } else {
        ixs_node *pow = base;
        for (int32_t e = 1; e < -exp; e++)
          pow = ixs_mul(ctx, pow, base);
        result = ixs_div(ctx, result, pow);
      }
    }
    return result;
  }

  case IXS_FLOOR:
    return ixs_floor(ctx, do_expand(ctx, node->u.unary.arg));
  case IXS_CEIL:
    return ixs_ceil(ctx, do_expand(ctx, node->u.unary.arg));

  case IXS_MOD:
    return ixs_mod(ctx, do_expand(ctx, node->u.binary.lhs),
                   do_expand(ctx, node->u.binary.rhs));
  case IXS_MAX:
    return ixs_max(ctx, do_expand(ctx, node->u.binary.lhs),
                   do_expand(ctx, node->u.binary.rhs));
  case IXS_MIN:
    return ixs_min(ctx, do_expand(ctx, node->u.binary.lhs),
                   do_expand(ctx, node->u.binary.rhs));
  case IXS_XOR:
    return ixs_xor(ctx, do_expand(ctx, node->u.binary.lhs),
                   do_expand(ctx, node->u.binary.rhs));
  case IXS_CMP:
    return ixs_cmp(ctx, do_expand(ctx, node->u.binary.lhs),
                   node->u.binary.cmp_op, do_expand(ctx, node->u.binary.rhs));

  case IXS_PIECEWISE: {
    uint32_t nc = node->u.pw.ncases;
    ixs_node **vals =
        ixs_arena_alloc(&ctx->scratch, nc * sizeof(*vals), sizeof(void *));
    ixs_node **conds =
        ixs_arena_alloc(&ctx->scratch, nc * sizeof(*conds), sizeof(void *));
    if (!vals || !conds)
      return NULL;
    for (uint32_t i = 0; i < nc; i++) {
      vals[i] = do_expand(ctx, node->u.pw.cases[i].value);
      conds[i] = do_expand(ctx, node->u.pw.cases[i].cond);
    }
    return ixs_pw(ctx, nc, vals, conds);
  }

  case IXS_AND:
  case IXS_OR: {
    uint32_t na = node->u.logic.nargs;
    if (na < 2)
      return node;
    ixs_node *result = do_expand(ctx, node->u.logic.args[0]);
    for (uint32_t i = 1; i < na; i++) {
      ixs_node *arg = do_expand(ctx, node->u.logic.args[i]);
      result = (node->tag == IXS_AND) ? ixs_and(ctx, result, arg)
                                      : ixs_or(ctx, result, arg);
    }
    return result;
  }

  case IXS_NOT:
    return ixs_not(ctx, do_expand(ctx, node->u.unary_bool.arg));
  }

  return node;
}

ixs_node *expand_impl(ixs_ctx *ctx, ixs_node *expr) {
  return do_expand(ctx, expr);
}
