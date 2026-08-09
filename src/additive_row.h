/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_ADDITIVE_ROW_H
#define IXS_ADDITIVE_ROW_H

#include "node.h"

typedef enum {
  IXS_ADDITIVE_ROW_NO_MATCH,
  IXS_ADDITIVE_ROW_MATCH,
  IXS_ADDITIVE_ROW_OOM
} ixs_additive_row_status;

/* Recognizers allocate nothing; failure is an ordinary shape miss. */
IXS_STATIC bool ixs_additive_row_unit_value(ixs_node *expr, ixs_node **term,
                                            int64_t *value);
IXS_STATIC bool ixs_additive_row_unit_pair(ixs_node *expr, ixs_node **positive,
                                           ixs_node **negative,
                                           int64_t *constant);
IXS_STATIC ixs_additive_row_status ixs_additive_row_without_constant(
    ixs_ctx *ctx, ixs_node *expr, ixs_node **result);
/* Bounds caches may own scratch independently of the expression context. */
IXS_STATIC ixs_additive_row_status ixs_additive_row_relation(
    ixs_ctx *ctx, ixs_arena *scratch, ixs_node *lhs, ixs_node *rhs,
    ixs_node **positive, ixs_node **negative, int64_t *offset);

#endif /* IXS_ADDITIVE_ROW_H */
