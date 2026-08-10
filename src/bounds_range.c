/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds_range.h"
#include <string.h>

#define BOUNDS_CACHE_CAP 32u

IXS_STATIC void bounds_range_init(ixs_bounds *b, bool allocate_cache) {
  b->cache = NULL;
  b->cache_cap = 0;
  b->range_pw_depth = 0;
  b->empty_cache_valid = false;
  b->empty_cache_value = false;
  b->interval_evaluating = false;
  if (!allocate_cache)
    return;
  b->cache = ixs_arena_alloc(b->scratch, BOUNDS_CACHE_CAP * sizeof(*b->cache),
                             sizeof(void *));
  if (!b->cache) {
    b->cache_cap = BOUNDS_CACHE_DISABLED;
    return;
  }
  b->cache_cap = BOUNDS_CACHE_CAP;
  memset(b->cache, 0, b->cache_cap * sizeof(*b->cache));
}

IXS_STATIC void bounds_range_inherit_fork(ixs_bounds *dst,
                                          const ixs_bounds *src) {
  dst->cache = NULL;
  dst->cache_cap = BOUNDS_CACHE_DISABLED;
  dst->range_pw_depth = src->range_pw_depth;
  dst->empty_cache_valid = false;
  dst->empty_cache_value = false;
  dst->interval_evaluating = false;
}

IXS_STATIC void bounds_range_invalidate_empty(ixs_bounds *b) {
  if (b)
    b->empty_cache_valid = false;
}

IXS_STATIC void bounds_range_invalidate_all(ixs_bounds *b) {
  bounds_range_invalidate_empty(b);
  if (b && b->cache && b->cache_cap != BOUNDS_CACHE_DISABLED)
    memset(b->cache, 0, b->cache_cap * sizeof(*b->cache));
}
