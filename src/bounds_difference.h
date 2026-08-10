/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_DIFFERENCE_H
#define IXS_BOUNDS_DIFFERENCE_H

#include "bounds.h"

/* lhs - rhs <= offset, equivalently the directed edge rhs -> lhs. Edge
 * objects are immutable after publication. Variable indices remain valid
 * across append-only table growth and transactional forks. */
struct ixs_difference_constraint {
  ixs_node *lhs;
  ixs_node *rhs;
  ixs_difference_constraint *next_lhs;
  ixs_difference_constraint *next_rhs;
  size_t lhs_var;
  size_t rhs_var;
  int64_t offset;
};

struct ixs_difference_var {
  ixs_difference_constraint *incoming;
  ixs_difference_constraint *outgoing;
  int64_t potential;
  size_t queue_epoch;
  size_t hops;
};

IXS_STATIC void bounds_difference_init(ixs_bounds *bounds);
/* Fork inheritance is allocation-free. Clone runs after the store var index
 * and allocates the edge index before the parallel variable table. Those
 * mutable arrays are private to the fork; their incident lists retain immutable
 * edge objects through the common scratch-arena lifetime. */
IXS_STATIC void bounds_difference_inherit_fork(ixs_bounds *dst,
                                               const ixs_bounds *src);
IXS_STATIC bool bounds_difference_clone_fork(ixs_bounds *dst,
                                             const ixs_bounds *src);
IXS_STATIC bool bounds_difference_is_empty(const ixs_bounds *bounds);

IXS_STATIC void bounds_difference_propagate_symbol(ixs_bounds *bounds,
                                                   const char *name);
IXS_STATIC void bounds_difference_add_range(ixs_bounds *bounds, ixs_node *expr,
                                            ixs_interval interval);
IXS_STATIC bool bounds_difference_exact_unit_value(ixs_bounds *bounds,
                                                   ixs_node *expr,
                                                   int64_t *value);

#endif /* IXS_BOUNDS_DIFFERENCE_H */
