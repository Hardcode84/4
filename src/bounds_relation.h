/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_RELATION_H
#define IXS_BOUNDS_RELATION_H

#include "bounds.h"

enum {
  BOUNDS_PROJECTION_COMPLETE_RANGE = 1u << 0,
  BOUNDS_PROJECTION_COMPLETE_INTEGER = 1u << 1,
  BOUNDS_PROJECTION_COMPLETE_DEFINED_COMPONENT = 1u << 2,
  BOUNDS_PROJECTION_COMPLETE_DEFINED_WITH_EQUALITY = 1u << 3,
  BOUNDS_PROJECTION_COMPLETE_DEFINED_WITHOUT_EQUALITY = 1u << 4
};

typedef struct {
  size_t endpoint_index;
  size_t defined_component;
  ixs_relation_offset defined_offset;
  ixs_interval range;
  ixs_check_result integer;
  ixs_check_result defined_with_equality;
  ixs_check_result defined_without_equality;
  uint8_t completion;
  uint32_t generation;
} bounds_equality_projection_cache_entry;

IXS_STATIC void bounds_relation_projection_init(ixs_bounds *bounds,
                                                bool transient);
IXS_STATIC void bounds_relation_projection_inherit_fork(ixs_bounds *dst,
                                                        const ixs_bounds *src);
IXS_STATIC void bounds_relation_projection_destroy(ixs_bounds *bounds);
IXS_STATIC void bounds_relation_projection_invalidate(ixs_bounds *bounds);

#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
IXS_STATIC void
bounds_relation_projection_force_generation_wrap(ixs_bounds *bounds);
#endif

#endif /* IXS_BOUNDS_RELATION_H */
