/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_RESIDUE_H
#define IXS_BOUNDS_RESIDUE_H

#include "internal.h"

#include <ixsimpl.h>

struct ixs_bounds;

IXS_STATIC bool bounds_known_residue(struct ixs_bounds *bounds, ixs_node *expr,
                                     uint64_t modulus, uint64_t *out);

#endif /* IXS_BOUNDS_RESIDUE_H */
