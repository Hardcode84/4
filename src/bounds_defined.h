/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_DEFINED_H
#define IXS_BOUNDS_DEFINED_H

#include "bounds.h"

IXS_STATIC ixs_check_result bounds_defined_check_detail(ixs_bounds *bounds,
                                                        ixs_node *expr,
                                                        bool *oom,
                                                        bool *limited);
IXS_STATIC bool defined_child_count(ixs_node *node, uint32_t *count);
IXS_STATIC ixs_node *defined_child_at(ixs_node *node, uint32_t index);
/* Restrict one fork to valuations where expr is defined. The restriction is
 * opaque outside that fork and closes over eager children iteratively. */
IXS_STATIC bool bounds_defined_restrict_domain(ixs_bounds *bounds,
                                               ixs_node *expr);

#endif /* IXS_BOUNDS_DEFINED_H */
