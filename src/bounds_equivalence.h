/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_EQUIVALENCE_H
#define IXS_BOUNDS_EQUIVALENCE_H

#include "bounds.h"

IXS_STATIC ixs_algebra_status
bounds_equivalence_query_detail(ixs_bounds *bounds, ixs_ctx *ctx, ixs_node *lhs,
                                ixs_node *rhs, ixs_check_result *result);
IXS_STATIC ixs_algebra_status bounds_constant_difference_query_detail(
    ixs_ctx *ctx, ixs_bounds *bounds, ixs_node *lhs, ixs_node *rhs,
    int64_t *delta, bool *matched);
IXS_STATIC ixs_check_result ixs_bounds_check_query(ixs_bounds *bounds,
                                                   ixs_node *cmp);

#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
IXS_STATIC ixs_check_result ixs_bounds_equivalence_subproof_limit_probe(
    ixs_facts *facts, const ixs_node *lhs, const ixs_node *rhs);
IXS_STATIC ixs_check_result ixs_bounds_equivalence_quotient_limit_probe(
    ixs_facts *facts, const ixs_node *lhs, const ixs_node *rhs);
#endif

#endif /* IXS_BOUNDS_EQUIVALENCE_H */
