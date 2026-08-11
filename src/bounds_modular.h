/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_MODULAR_H
#define IXS_BOUNDS_MODULAR_H

#include "bounds.h"

/* Prove one exact delta through relation residuals and paired Mod terms.
 * Failure leaves delta unchanged and reports only live transport failures. */
IXS_STATIC bool bounds_modular_exact_delta_detail(
    ixs_ctx *ctx, ixs_bounds *bounds, ixs_node *lhs, ixs_node *rhs,
    bool allow_expand, int64_t *delta, bool *invalid, bool *limited, bool *oom);

/* Project an already-normalized expression to one exact int64 value.  This
 * path never calls the simplifier, so fact-backed rewriting can use it without
 * recursive solver re-entry. */
IXS_STATIC bool bounds_modular_exact_normalized_value_detail(
    ixs_ctx *ctx, ixs_bounds *bounds, ixs_node *expr, int64_t *value,
    bool *invalid, bool *limited, bool *oom);

#endif /* IXS_BOUNDS_MODULAR_H */
