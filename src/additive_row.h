/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_ADDITIVE_ROW_H
#define IXS_ADDITIVE_ROW_H

#include "algebra_status.h"
#include "node.h"

typedef enum {
  IXS_EUCLIDEAN_FLOOR = 1u,
  IXS_EUCLIDEAN_CEIL = 2u,
  IXS_EUCLIDEAN_MOD = 4u
} ixs_euclidean_atom_mask;

typedef struct {
  const ixs_addterm *terms;
  uint32_t nterms;
  ixs_addterm singleton;
} ixs_euclidean_row;

typedef struct {
  ixs_node *atom;
  ixs_node *numerator;
  ixs_node *denominator;
  ixs_node *scale;
  const ixs_addterm *source;
  uint32_t factor_index;
} ixs_euclidean_term_plan;

/* Recognizers allocate nothing; failure is an ordinary shape miss. */
IXS_STATIC bool ixs_additive_row_unit_value(ixs_node *expr, ixs_node **term,
                                            int64_t *value);
IXS_STATIC bool ixs_additive_row_unit_pair(ixs_node *expr, ixs_node **positive,
                                           ixs_node **negative,
                                           int64_t *constant);
IXS_STATIC ixs_algebra_status ixs_additive_row_without_constant(
    ixs_ctx *ctx, ixs_node *expr, ixs_node **result);
/* A direct selected round is allocation-free. Otherwise, split exactly one
 * coefficient-one selected round from an ADD and construct its exact residual
 * in O(T). Outputs are initialized only on MATCH; LIMITED is impossible. */
IXS_STATIC ixs_algebra_status ixs_additive_row_split_round(ixs_ctx *ctx,
                                                           ixs_node *value,
                                                           bool ceiling,
                                                           ixs_node **argument,
                                                           ixs_node **residual);
/* Bounds caches may own scratch independently of the expression context. */
IXS_STATIC ixs_algebra_status ixs_additive_row_relation(
    ixs_ctx *ctx, ixs_arena *scratch, ixs_node *lhs, ixs_node *rhs,
    ixs_node **positive, ixs_node **negative, int64_t *offset);

/* Borrow one canonical ADD row, or one synthetic coefficient-one row for a
 * scalar. The source expression must outlive the view. */
IXS_STATIC void ixs_euclidean_row_borrow(ixs_ctx *ctx, ixs_node *expr,
                                         ixs_euclidean_row *row);
IXS_STATIC void ixs_euclidean_row_borrow_terms(const ixs_addterm *terms,
                                               uint32_t nterms,
                                               ixs_euclidean_row *row);

/* Split an exact quotient into borrowed/interned numerator and denominator.
 * Shape recognition is O(T); scratch is restored before return. */
IXS_STATIC ixs_algebra_status ixs_euclidean_quotient_parts(
    ixs_ctx *ctx, ixs_node *expr, ixs_node **numerator, ixs_node **denominator);

/* Recover one selected Floor/Ceil/Mod atom and its full ADD-term scale. The
 * plan borrows its source term; that term must outlive the plan. Building a
 * compound scale or quotient may report OOM, INVALID, or UNREPRESENTABLE. */
IXS_STATIC ixs_algebra_status
ixs_euclidean_plan_addterm(ixs_ctx *ctx, const ixs_addterm *term, unsigned mask,
                           ixs_euclidean_term_plan *plan);
/* Rebuild only the source product factors outside the selected atom. The ADD
 * coefficient is deliberately excluded. */
IXS_STATIC ixs_algebra_status ixs_euclidean_plan_outer(
    ixs_ctx *ctx, const ixs_euclidean_term_plan *plan, ixs_node **outer);

/* Allocation-free prefilter for rows that contain a selected atom. */
IXS_STATIC bool ixs_euclidean_row_contains(const ixs_euclidean_row *row,
                                           unsigned mask);

#endif /* IXS_ADDITIVE_ROW_H */
