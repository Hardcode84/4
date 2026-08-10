/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_INTEGER_H
#define IXS_BOUNDS_INTEGER_H

#include "internal.h"

#include <ixsimpl.h>

struct ixs_bounds;

IXS_STATIC bool ixs_bounds_is_known_divisible(struct ixs_bounds *bounds,
                                              ixs_node *expr, int64_t modulus);
IXS_STATIC bool ixs_bounds_is_integer_with_divinfo(struct ixs_bounds *bounds,
                                                   ixs_node *expr);
IXS_STATIC ixs_check_result bounds_integer_check_without_equality(
    struct ixs_bounds *bounds, ixs_node *expr);
IXS_STATIC ixs_check_result
ixs_bounds_check_integer_valued(struct ixs_bounds *bounds, ixs_node *expr);

#endif /* IXS_BOUNDS_INTEGER_H */
