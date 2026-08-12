/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_BITFACTS_H
#define IXS_BOUNDS_BITFACTS_H

#include "internal.h"

#include <ixsimpl.h>

struct ixs_bounds;

typedef struct {
  uint64_t known_zero; /* low 64 bits known to be zero */
  uint64_t known_one;  /* low 64 bits known to be one */
  ixs_pow2_fact pow2;
} ixs_bitfacts;

IXS_STATIC void bounds_bitfacts_apply_xor(ixs_bitfacts *out,
                                          const ixs_bitfacts *lhs,
                                          const ixs_bitfacts *rhs);
IXS_STATIC uint64_t bounds_bitfacts_value_span_mask(uint64_t upper);
IXS_STATIC bool ixs_bounds_get_bitfacts(struct ixs_bounds *bounds,
                                        ixs_node *expr, ixs_bitfacts *out);
/* True exactly when the tag-specific transfer can add information beyond the
 * interval seed used by ixs_bounds_get_bitfacts. Expected O(add terms) for an
 * ADD coefficient check and O(1) otherwise. */
IXS_STATIC bool bounds_bitfacts_may_refine(struct ixs_bounds *bounds,
                                           ixs_node *expr);
IXS_STATIC bool ixs_bounds_is_pow2_or_zero(struct ixs_bounds *bounds,
                                           ixs_node *expr);

#endif /* IXS_BOUNDS_BITFACTS_H */
