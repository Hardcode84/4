/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "query_transaction.h"

IXS_STATIC void ixs_query_transaction_begin(ixs_query_transaction *transaction,
                                            ixs_ctx *ctx, ixs_bounds *bounds,
                                            ixs_arena *scratch) {
  transaction->ctx = ctx;
  transaction->bounds = bounds;
  transaction->scratch = scratch;
  if (bounds) {
    transaction->transport = ixs_bounds_query_transport_snapshot(bounds);
    transaction->old_oom = bounds->oom;
  }
  if (scratch)
    transaction->scratch_mark = ixs_arena_save(scratch);
  if (ctx) {
    transaction->diag_mark = ixs_arena_save(&ctx->diag);
    transaction->errors = ctx->errors;
    transaction->nerrors = ctx->nerrors;
    transaction->errors_cap = ctx->errors_cap;
  }
}

IXS_STATIC ixs_query_observation ixs_query_transaction_finish(
    const ixs_query_transaction *transaction, bool restore_oom) {
  ixs_query_observation result = {false, false, false};
  ixs_bounds *bounds = transaction->bounds;
  if (bounds) {
    ixs_bounds_transport_status transport =
        bounds_query_state_transport(bounds);
    result.new_oom = !transaction->old_oom && bounds->oom;
    result.limited = bounds_query_limited_since(bounds, transaction->transport);
    result.invalid = bounds_query_invalid_since(bounds, transaction->transport);
    if (ixs_bounds_query_transport_snapshot(bounds).generation !=
        transaction->transport.generation)
      result.invalid = true;
    if (transport == IXS_BOUNDS_TRANSPORT_LIMITED)
      result.limited = true;
    else if (transport == IXS_BOUNDS_TRANSPORT_INVALID)
      result.invalid = true;
    else if (transport == IXS_BOUNDS_TRANSPORT_OOM)
      result.new_oom = true;
  }
  if (transaction->scratch)
    ixs_arena_restore(transaction->scratch, transaction->scratch_mark);
  if (transaction->ctx) {
    ixs_ctx *ctx = transaction->ctx;
    ixs_arena_restore(&ctx->diag, transaction->diag_mark);
    ctx->errors = transaction->errors;
    ctx->nerrors = transaction->nerrors;
    ctx->errors_cap = transaction->errors_cap;
  }
  if (restore_oom && bounds)
    transaction->bounds->oom = transaction->old_oom;
  return result;
}
