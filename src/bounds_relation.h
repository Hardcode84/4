/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_RELATION_H
#define IXS_BOUNDS_RELATION_H

#include "bounds.h"

typedef struct {
  size_t endpoint_index;
  size_t defined_component;
  ixs_relation_offset defined_offset;
  ixs_interval range;
  ixs_check_result integer;
  ixs_check_result defined_with_equality;
  ixs_check_result defined_without_equality;
  bool range_complete;
  bool integer_complete;
  bool defined_component_complete;
  bool defined_with_equality_complete;
  bool defined_without_equality_complete;
  bool occupied;
} bounds_equality_projection_cache_entry;

IXS_STATIC void bounds_relation_projection_init(ixs_bounds *bounds,
                                                bool transient);
IXS_STATIC void bounds_relation_projection_inherit_fork(ixs_bounds *dst,
                                                        const ixs_bounds *src);
IXS_STATIC void bounds_relation_projection_destroy(ixs_bounds *bounds);
IXS_STATIC void bounds_relation_projection_invalidate(ixs_bounds *bounds);

#endif /* IXS_BOUNDS_RELATION_H */
