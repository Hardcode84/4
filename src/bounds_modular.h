/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_MODULAR_H
#define IXS_BOUNDS_MODULAR_H

#include "bounds.h"

/* Prove one Euclidean quotient bucket from existing boundary witnesses. The
 * optional dividend/delta pair enables the stride-congruence fallback. This
 * query constructs and simplifies no nodes and returns only MATCH, NO_MATCH,
 * OOM, or LIMITED. */
IXS_STATIC ixs_algebra_status bounds_modular_quotient_bucket(
    ixs_bounds *bounds, ixs_node *lower_witness, ixs_node *upper_witness,
    ixs_node *dividend, ixs_node *denominator, ixs_node *delta);

/* Prove one exact delta through relation residuals and paired Mod terms.
 * Failure leaves delta unchanged and reports only live transport failures. */
IXS_STATIC bool bounds_modular_exact_delta_detail(
    ixs_ctx *ctx, ixs_bounds *bounds, ixs_node *lhs, ixs_node *rhs,
    bool allow_expand, int64_t *delta, bool *invalid, bool *limited, bool *oom);

/* Prove that two original Mod nodes with one shared modulus have equal
 * remainders. The query reuses active bounds caches and never simplifies. */
IXS_STATIC ixs_algebra_status bounds_modular_remainders_equal(
    ixs_ctx *ctx, ixs_bounds *bounds, ixs_node *lhs, ixs_node *rhs);

/* Project an already-normalized expression to one exact int64 value.  This
 * path shares the active range, relation, modular, and bitfacts queries and
 * never calls the simplifier. */
IXS_STATIC ixs_algebra_status bounds_project_exact_integer(ixs_ctx *ctx,
                                                           ixs_bounds *bounds,
                                                           ixs_node *expr,
                                                           int64_t *value);

#endif /* IXS_BOUNDS_MODULAR_H */
