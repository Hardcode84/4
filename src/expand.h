/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_EXPAND_H
#define IXS_EXPAND_H

#include "node.h"

/* Distribute MUL over ADD recursively (sum-of-products form). */
ixs_node *expand_impl(ixs_ctx *ctx, ixs_node *expr);

#endif /* IXS_EXPAND_H */
