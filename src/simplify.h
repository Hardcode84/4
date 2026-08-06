/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_SIMPLIFY_H
#define IXS_SIMPLIFY_H

#include "internal.h"

#include "bounds.h"
#include "node.h"

/*
 * Smart constructors: apply canonicalization rules, then hash-cons.
 * Called by the public API in ctx.c and by the parser.
 */

IXS_STATIC ixs_node *simp_add(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
IXS_STATIC ixs_node *simp_mul(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
IXS_STATIC ixs_node *simp_neg(ixs_ctx *ctx, ixs_node *a);
IXS_STATIC ixs_node *simp_sub(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
IXS_STATIC ixs_node *simp_div(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
IXS_STATIC ixs_node *simp_floor(ixs_ctx *ctx, ixs_node *x);
IXS_STATIC ixs_node *simp_ceil(ixs_ctx *ctx, ixs_node *x);
IXS_STATIC ixs_node *simp_trunc(ixs_ctx *ctx, ixs_node *x);
IXS_STATIC ixs_node *simp_mod(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
IXS_STATIC ixs_node *simp_max(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
IXS_STATIC ixs_node *simp_min(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
IXS_STATIC ixs_node *simp_xor(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
IXS_STATIC ixs_node *simp_max_many(ixs_ctx *ctx, uint32_t n,
                                   ixs_node *const *args);
IXS_STATIC ixs_node *simp_min_many(ixs_ctx *ctx, uint32_t n,
                                   ixs_node *const *args);
IXS_STATIC ixs_node *simp_xor_many(ixs_ctx *ctx, uint32_t n,
                                   ixs_node *const *args);
IXS_STATIC ixs_node *simp_pw(ixs_ctx *ctx, uint32_t n, ixs_node *const *values,
                             ixs_node *const *conds);
IXS_STATIC ixs_node *simp_cmp(ixs_ctx *ctx, ixs_node *a, ixs_cmp_op op,
                              ixs_node *b);
IXS_STATIC ixs_node *simp_and(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
IXS_STATIC ixs_node *simp_or(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
IXS_STATIC ixs_node *simp_and_many(ixs_ctx *ctx, uint32_t n,
                                   ixs_node *const *args);
IXS_STATIC ixs_node *simp_or_many(ixs_ctx *ctx, uint32_t n,
                                  ixs_node *const *args);
IXS_STATIC ixs_node *simp_not(ixs_ctx *ctx, ixs_node *a);

/* Top-down simplification pass with assumptions + bound analysis. */
IXS_STATIC ixs_node *simp_simplify_bounds(ixs_ctx *ctx, ixs_node *expr,
                                          ixs_bounds *bounds);

/* As above, but reports a root-hold nesting limit separately from OOM. */
IXS_STATIC ixs_node *simp_simplify_bounds_status(ixs_ctx *ctx, ixs_node *expr,
                                                 ixs_bounds *bounds,
                                                 bool *limited);

IXS_STATIC bool simp_simplify_batch_bounds(ixs_ctx *ctx, ixs_node **exprs,
                                           size_t n, ixs_bounds *bounds);

IXS_STATIC ixs_node *simp_simplify(ixs_ctx *ctx, ixs_node *expr,
                                   ixs_node *const *assumptions,
                                   size_t n_assumptions);

/* Batch: simplify exprs[0..n-1] in place, building bounds once. */
IXS_STATIC void simp_simplify_batch(ixs_ctx *ctx, ixs_node **exprs, size_t n,
                                    ixs_node *const *assumptions,
                                    size_t n_assumptions);

/* Entailment check: bounds-only, no rewriting. */
IXS_STATIC ixs_check_result simp_check(ixs_ctx *ctx, ixs_node *expr,
                                       ixs_node *const *assumptions,
                                       size_t n_assumptions);

IXS_STATIC ixs_check_result
simp_check_integer_valued(ixs_ctx *ctx, ixs_node *expr,
                          ixs_node *const *assumptions, size_t n_assumptions);
IXS_STATIC ixs_check_result simp_check_defined(ixs_ctx *ctx, ixs_node *expr,
                                               ixs_node *const *assumptions,
                                               size_t n_assumptions);

/* Power-of-two fact query: bounds-only, no rewriting. */
IXS_STATIC ixs_pow2_fact simp_get_pow2_fact(ixs_ctx *ctx, ixs_node *expr,
                                            ixs_node *const *assumptions,
                                            size_t n_assumptions);

/* Range inference: bounds-only, no rewriting. */
IXS_STATIC bool simp_range(ixs_ctx *ctx, ixs_node *expr,
                           ixs_node *const *assumptions, size_t n_assumptions,
                           ixs_range_result *out);

/* Defined, integer-valued range inference with internal bound rounding. */
IXS_STATIC bool simp_integer_range(ixs_ctx *ctx, ixs_node *expr,
                                   ixs_node *const *assumptions,
                                   size_t n_assumptions,
                                   ixs_integer_range_result *out);

/* Substitution: replace all occurrences of target with replacement. */
IXS_STATIC ixs_node *simp_subs(ixs_ctx *ctx, ixs_node *expr, ixs_node *target,
                               ixs_node *replacement);

/* Simultaneous multi-target substitution. */
IXS_STATIC ixs_node *simp_subs_multi(ixs_ctx *ctx, ixs_node *expr,
                                     uint32_t nsubs, ixs_node *const *targets,
                                     ixs_node *const *replacements);

/* Exact top-level rational product or common-denominator sum. */
IXS_STATIC bool simp_decompose_exact_quotient(ixs_ctx *ctx, ixs_node *expr,
                                              ixs_node **numerator,
                                              ixs_node **denominator);

#endif /* IXS_SIMPLIFY_H */
