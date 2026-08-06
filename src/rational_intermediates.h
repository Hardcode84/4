/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_RATIONAL_INTERMEDIATES_H
#define IXS_RATIONAL_INTERMEDIATES_H

#include "internal.h"

#include "bounds.h"
#include "node.h"

IXS_STATIC ixs_rational_materialization_plan
ixs_bounds_plan_rational_materialization(ixs_ctx *ctx, ixs_bounds *bounds,
                                         ixs_node *expr, uint32_t word_bits);

#endif /* IXS_RATIONAL_INTERMEDIATES_H */
