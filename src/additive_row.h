/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_ADDITIVE_ROW_H
#define IXS_ADDITIVE_ROW_H

#include "algebra_status.h"
#include "node.h"

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

#endif /* IXS_ADDITIVE_ROW_H */
