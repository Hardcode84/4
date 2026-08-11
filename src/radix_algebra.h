/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_RADIX_ALGEBRA_H
#define IXS_RADIX_ALGEBRA_H

#include "bounds.h"

typedef struct {
  ixs_check_result check;
  bool limited; /* Local row exhaustion; independent tactics may continue. */
  bool oom;     /* Nested allocation failure; the caller must propagate it. */
} ixs_radix_algebra_result;

/* Check an ordered canonical ADD against zero. The expression is trusted and
 * already defined by the bounds query owner. */
IXS_STATIC ixs_radix_algebra_result ixs_radix_algebra_order(
    ixs_bounds *bounds, const ixs_node *expr, ixs_cmp_op op);

/* expr is a trusted, already-defined comparison operand. */
IXS_STATIC ixs_radix_algebra_result
ixs_radix_algebra_nonnegative(ixs_bounds *bounds, const ixs_node *expr);

/* Prove that two defined expressions encode the same complete mixed-radix
 * residue. Carriers must be integer-valued under bounds. */
IXS_STATIC ixs_radix_algebra_result ixs_radix_algebra_equivalent(
    ixs_bounds *bounds, const ixs_node *lhs, const ixs_node *rhs);

#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
/* Bind a fact set so tests can observe the component's local outcome. */
IXS_STATIC ixs_radix_algebra_result
ixs_radix_algebra_facts_probe(ixs_facts *facts, const ixs_node *expr);
#endif

#endif /* IXS_RADIX_ALGEBRA_H */
