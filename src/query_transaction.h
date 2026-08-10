/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_QUERY_TRANSACTION_H
#define IXS_QUERY_TRANSACTION_H

#include "bounds_query.h"

typedef struct {
  ixs_ctx *ctx;
  ixs_bounds *bounds;
  ixs_arena *scratch;
  ixs_arena_mark scratch_mark, diag_mark;
  const char **errors;
  size_t nerrors, errors_cap;
  ixs_bounds_transport_snapshot transport;
  bool old_oom;
} ixs_query_transaction;

typedef struct {
  bool new_oom;
  bool limited;
  bool invalid;
} ixs_query_observation;

/* A transaction independently snapshots the non-NULL diagnostic, bounds, and
 * scratch owners. Finish restores diagnostics and scratch, then reports raw
 * transport observations. The caller owns status precedence, result roots,
 * publication, and whether bounds-local OOM is restored. */
IXS_STATIC void ixs_query_transaction_begin(ixs_query_transaction *transaction,
                                            ixs_ctx *ctx, ixs_bounds *bounds,
                                            ixs_arena *scratch);
IXS_STATIC ixs_query_observation ixs_query_transaction_finish(
    const ixs_query_transaction *transaction, bool restore_oom);

#endif /* IXS_QUERY_TRANSACTION_H */
