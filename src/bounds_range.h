/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_RANGE_H
#define IXS_BOUNDS_RANGE_H

#include "bounds.h"

#define BOUNDS_CACHE_DISABLED ((size_t)-1)

IXS_STATIC void bounds_range_init(ixs_bounds *bounds, bool allocate_cache);
IXS_STATIC void bounds_range_inherit_fork(ixs_bounds *dst,
                                          const ixs_bounds *src);
IXS_STATIC void bounds_range_invalidate_empty(ixs_bounds *bounds);
IXS_STATIC void bounds_range_invalidate_all(ixs_bounds *bounds);

#endif /* IXS_BOUNDS_RANGE_H */
