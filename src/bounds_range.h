/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_RANGE_H
#define IXS_BOUNDS_RANGE_H

#include "bounds.h"
#include "bounds_relation.h"

#define BOUNDS_CACHE_DISABLED ((size_t)-1)

IXS_STATIC void bounds_range_init(ixs_bounds *bounds, bool allocate_cache);
IXS_STATIC void bounds_range_inherit_fork(ixs_bounds *dst,
                                          const ixs_bounds *src);
IXS_STATIC void bounds_range_invalidate_empty(ixs_bounds *bounds);
IXS_STATIC void bounds_range_invalidate_all(ixs_bounds *bounds);
IXS_STATIC ixs_algebra_status bounds_collect_relation_component(
    ixs_bounds *bounds, ixs_node *expr, bounds_relation_component *component);
IXS_STATIC bool
bounds_publish_relation_component(ixs_bounds *bounds,
                                  const bounds_relation_component *component);
IXS_STATIC ixs_algebra_status
bounds_relation_offset_checked(ixs_bounds *bounds, ixs_node *lhs, ixs_node *rhs,
                               ixs_relation_offset *offset);
IXS_STATIC ixs_algebra_status bounds_get_truncating_remainder_range(
    ixs_bounds *bounds, ixs_node *expr, bool expression_defined,
    ixs_interval *out);
IXS_STATIC void bounds_note_truncating_range_status(ixs_bounds *bounds,
                                                    ixs_algebra_status status);
IXS_STATIC bool bounds_refine_integral_interval(ixs_bounds *bounds,
                                                ixs_node *expr,
                                                bool expression_defined,
                                                ixs_interval *interval);
IXS_STATIC ixs_check_result bounds_range_check_relation(const ixs_interval *lhs,
                                                        const ixs_interval *rhs,
                                                        ixs_cmp_op op);
/* Interval-only comparison proof over defined evaluations. Intrinsic integer
 * refinements are intersected before explicit ranges can prove a result. */
IXS_STATIC ixs_check_result
bounds_range_check_relation_refined(ixs_bounds *bounds, ixs_node *comparison);
IXS_STATIC ixs_check_result bounds_range_check_raw(ixs_bounds *bounds,
                                                   ixs_node *comparison);
IXS_STATIC bool bounds_range_exact_integer_difference(ixs_bounds *bounds,
                                                      ixs_node *difference,
                                                      int64_t *delta);

#endif /* IXS_BOUNDS_RANGE_H */
