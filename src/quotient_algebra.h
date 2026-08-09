/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_QUOTIENT_ALGEBRA_H
#define IXS_QUOTIENT_ALGEBRA_H

#include "bounds.h"

typedef struct {
  ixs_check_result check;
  bool limited;
  bool invalid;
  bool oom;
} ixs_quotient_algebra_result;

#define IXS_QUOTIENT_ALGEBRA_MAX_CANDIDATES 4u

/* Operands are already total. candidates counts consumed solve equations;
 * projection, congruence, and range transfer have independent caps. */
IXS_STATIC ixs_quotient_algebra_result ixs_quotient_algebra_check(
    ixs_ctx *ctx, ixs_bounds *bounds, const ixs_node *lhs, const ixs_node *rhs,
    unsigned candidates);

#endif /* IXS_QUOTIENT_ALGEBRA_H */
