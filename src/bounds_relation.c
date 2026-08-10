/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds_relation.h"
#include <string.h>

IXS_STATIC void bounds_relation_projection_init(ixs_bounds *b, bool transient) {
  b->equality_projection_cache = NULL;
  b->equality_projection_cache_count = 0;
  b->equality_projection_cache_capacity = 0;
  b->equality_projection_cache_generation = 1u;
  b->equality_projection_cache_transient = transient;
}

IXS_STATIC void bounds_relation_projection_inherit_fork(ixs_bounds *dst,
                                                        const ixs_bounds *src) {
  bounds_relation_projection_init(dst, true);
  dst->equality_disabled_depth = src->equality_disabled_depth;
}

IXS_STATIC void bounds_relation_projection_destroy(ixs_bounds *b) {
  bounds_relation_projection_init(b, false);
  b->equality_disabled_depth = 0;
}

IXS_STATIC void bounds_relation_projection_invalidate(ixs_bounds *b) {
  bounds_equality_projection_cache_entry *cache;
  if (!b)
    return;
  b->equality_projection_cache_count = 0;
  b->equality_projection_cache_generation++;
  if (b->equality_projection_cache_generation != 0)
    return;
  /* Zero denotes a cleared slot. Only generation wrap touches retained rows. */
  cache =
      (bounds_equality_projection_cache_entry *)b->equality_projection_cache;
  if (cache)
    memset(cache, 0, b->equality_projection_cache_capacity * sizeof(*cache));
  b->equality_projection_cache_generation = 1u;
}

#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
IXS_STATIC void
bounds_relation_projection_force_generation_wrap(ixs_bounds *b) {
  b->equality_projection_cache_generation = UINT32_MAX;
}
#endif
