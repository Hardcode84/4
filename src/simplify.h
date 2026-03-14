#ifndef IXS_SIMPLIFY_H
#define IXS_SIMPLIFY_H

#include "node.h"

/*
 * Smart constructors: apply canonicalization rules, then hash-cons.
 * Called by the public API in ctx.c and by the parser.
 */

ixs_node *simp_add(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *simp_mul(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *simp_neg(ixs_ctx *ctx, ixs_node *a);
ixs_node *simp_sub(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *simp_div(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *simp_floor(ixs_ctx *ctx, ixs_node *x);
ixs_node *simp_ceil(ixs_ctx *ctx, ixs_node *x);
ixs_node *simp_mod(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *simp_max(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *simp_min(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *simp_xor(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *simp_pw(ixs_ctx *ctx, uint32_t n, ixs_node **values,
                  ixs_node **conds);
ixs_node *simp_cmp(ixs_ctx *ctx, ixs_node *a, ixs_cmp_op op, ixs_node *b);
ixs_node *simp_and(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *simp_or(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *simp_not(ixs_ctx *ctx, ixs_node *a);

/* Top-down simplification pass with assumptions + bound analysis. */
ixs_node *simp_simplify(ixs_ctx *ctx, ixs_node *expr,
                        ixs_node *const *assumptions, size_t n_assumptions);

/* Substitution: replace all occurrences of target with replacement. */
ixs_node *simp_subs(ixs_ctx *ctx, ixs_node *expr, ixs_node *target,
                    ixs_node *replacement);

#endif /* IXS_SIMPLIFY_H */
