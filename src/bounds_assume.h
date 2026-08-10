/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_ASSUME_H
#define IXS_BOUNDS_ASSUME_H

#include "internal.h"

#include "interval.h"
#include "node.h"

struct ixs_bounds;

typedef enum {
  IXS_BOUNDS_BUILD_OK,
  IXS_BOUNDS_BUILD_INVALID,
  IXS_BOUNDS_BUILD_LIMIT,
  IXS_BOUNDS_BUILD_OOM
} ixs_bounds_build_status;

IXS_STATIC bool ixs_bounds_add_assumption(struct ixs_bounds *b,
                                          ixs_node *assumption);
IXS_STATIC void ixs_bounds_add_expr(struct ixs_bounds *b, ixs_node *expr,
                                    ixs_interval iv);
IXS_STATIC ixs_interval
bounds_assume_get_proportional_range(struct ixs_bounds *b, ixs_node *expr);

/* Recognition and publication policy shared with scalar proof consumers. */
IXS_STATIC void apply_modrem(struct ixs_bounds *b, const char *name,
                             int64_t modulus, int64_t remainder);
IXS_STATIC ixs_cmp_op flip_cmp(ixs_cmp_op op);
IXS_STATIC bool node_coeff_is(ixs_node *node, int64_t value);
IXS_STATIC bool extract_cmp_expr_const(ixs_node *cmp, ixs_node **expr,
                                       int64_t *value);
IXS_STATIC bool bounds_extract_unit_equality(ixs_node *expr, ixs_node **lhs,
                                             ixs_node **rhs);
IXS_STATIC bool bounds_extract_cmp_exact_relation(struct ixs_bounds *b,
                                                  ixs_node *cmp, ixs_node **lhs,
                                                  ixs_node **rhs,
                                                  int64_t *offset);
IXS_STATIC bool extract_pow2_and(ixs_node *expr, const char **name);
IXS_STATIC bool extract_bitop_sym_mask(ixs_node *expr, ixs_tag tag,
                                       const char **name, int64_t *mask);
IXS_STATIC void bounds_add_nonzero(struct ixs_bounds *b, ixs_node *expr);
IXS_STATIC ixs_bounds_build_status assumption_invalid(struct ixs_bounds *b,
                                                      const char *message);

IXS_STATIC ixs_bounds_build_status
bounds_assume_validate_predicate(struct ixs_bounds *b, ixs_node *predicate);
IXS_STATIC ixs_bounds_build_status
bounds_assume_ingest_predicate(struct ixs_bounds *b, ixs_node *predicate);
IXS_STATIC ixs_bounds_build_status bounds_assume_validate_predicates(
    struct ixs_bounds *b, ixs_node *const *predicates, size_t n_predicates);
IXS_STATIC ixs_bounds_build_status bounds_assume_ingest_predicates(
    struct ixs_bounds *b, ixs_node *const *predicates, size_t n_predicates);

IXS_STATIC ixs_bounds_build_status
ixs_bounds_build_ctx(struct ixs_bounds *b, ixs_ctx *ctx, ixs_arena *scratch,
                     ixs_node *const *assumptions, size_t n_assumptions);

#endif /* IXS_BOUNDS_ASSUME_H */
