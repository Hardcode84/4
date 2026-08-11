/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_LOW_BITS_ALGEBRA_H
#define IXS_LOW_BITS_ALGEBRA_H

#include "algebra_status.h"
#include "bounds.h"

typedef struct {
  void *user;
  ixs_node *(*rebuild)(void *user, ixs_node *root, uint32_t count,
                       ixs_node *const *targets, ixs_node *const *replacements);
  /* NULL keeps unsupported subtrees opaque. A residue projection supplies a
   * callback that maps each opaque integer leaf into Z/(2^bits). */
  ixs_node *(*project_leaf)(void *user, ixs_node *leaf);
} ixs_low_bits_algebra_ops;

/* Normalize roots in Z/(2^bits) with one shared iterative DAG memo. Without a
 * leaf projector, total integer ADD/MUL/bitwise nodes and compatible inner
 * Mods propagate. With one, only range-preserving XOR/AND/OR propagate and
 * opaque integer leaves are materialized by the caller. On failure every
 * output preserves its input root. bits <= 62 is trusted. */
IXS_STATIC ixs_algebra_status ixs_low_bits_algebra_project(
    ixs_ctx *ctx, ixs_bounds *bounds, ixs_node *const *roots, size_t count,
    unsigned bits, const ixs_low_bits_algebra_ops *ops, ixs_node **projected);

#endif /* IXS_LOW_BITS_ALGEBRA_H */
