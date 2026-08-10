/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_PREDICATE_H
#define IXS_BOUNDS_PREDICATE_H

#include "bounds.h"

IXS_STATIC ixs_check_result bounds_predicate_not(ixs_check_result result);
IXS_STATIC bool bounds_predicate_domain_proven(ixs_bounds *bounds,
                                               ixs_node *predicate);
IXS_STATIC ixs_check_result bounds_predicate_eval(ixs_bounds *bounds,
                                                  ixs_node *predicate,
                                                  bool *limited);
IXS_STATIC ixs_check_result bounds_predicate_implication(ixs_bounds *bounds,
                                                         ixs_node *predicate,
                                                         bool *limited);
IXS_STATIC ixs_check_result
bounds_predicate_bounded_finite_domain(ixs_bounds *bounds, ixs_node *predicate);

#endif /* IXS_BOUNDS_PREDICATE_H */
