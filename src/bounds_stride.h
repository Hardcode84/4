/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_STRIDE_H
#define IXS_BOUNDS_STRIDE_H

#include "internal.h"

#include <ixsimpl.h>

struct ixs_bounds;

IXS_STATIC bool bounds_known_stride(struct ixs_bounds *bounds, ixs_node *expr,
                                    uint64_t *stride);
IXS_STATIC bool bounds_known_residue_class(struct ixs_bounds *bounds,
                                           ixs_node *expr, uint64_t modulus,
                                           uint64_t *class_modulus,
                                           uint64_t *class_residue);

#endif /* IXS_BOUNDS_STRIDE_H */
