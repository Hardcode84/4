/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_LOW_BITS_ALGEBRA_H
#define IXS_LOW_BITS_ALGEBRA_H

#include "algebra_status.h"
#include "bounds.h"

/* Project total integer dividends into Z/(2^bits). The caller has proved the
 * original outer Mods share modulus 2^bits, and both Mods and dividends are
 * total integers. On MATCH both outputs are initialized; every miss preserves
 * the input roots. bits <= 62 is a trusted producer invariant. This total
 * projector does not produce NO_MATCH or UNREPRESENTABLE. */
IXS_STATIC ixs_algebra_status ixs_low_bits_algebra_project(
    ixs_ctx *ctx, ixs_bounds *bounds, ixs_node *lhs, ixs_node *rhs,
    unsigned bits, ixs_node **projected_lhs, ixs_node **projected_rhs);

#endif /* IXS_LOW_BITS_ALGEBRA_H */
