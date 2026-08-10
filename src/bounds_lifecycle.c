/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds.h"
#include "bounds_difference.h"
#include "bounds_query.h"
#include "bounds_range.h"
#include "bounds_relation.h"
#include "bounds_store.h"

IXS_STATIC bool ixs_bounds_init(ixs_bounds *b, ixs_arena *scratch) {
  bool store_initialized;
  bounds_query_init(b);
  store_initialized = bounds_store_init(b, scratch);
  bounds_difference_init(b);
  bounds_relation_init(b, scratch, true);
  b->oom = false;
  b->equality_disabled_depth = 0;
  b->exact_proof_call_depth = 0;
  bounds_range_init(b, store_initialized);
  return store_initialized;
}

IXS_STATIC bool ixs_bounds_init_ctx(ixs_bounds *b, ixs_ctx *ctx,
                                    ixs_arena *scratch) {
  if (!ixs_bounds_init(b, scratch))
    return false;
  bounds_store_bind(b, ctx, scratch);
  return true;
}

IXS_STATIC void ixs_bounds_destroy(ixs_bounds *b) {
  if (!b)
    return;
  bounds_query_destroy(b);
  bounds_relation_destroy(b);
  b->equality_disabled_depth = 0;
  b->exact_proof_call_depth = 0;
}

IXS_STATIC bool ixs_bounds_fork(ixs_bounds *dst, const ixs_bounds *src) {
  if (!dst || !src || src->oom)
    return false;
  bounds_query_init(dst);
  if (!bounds_store_fork_begin(dst, src))
    goto failed;
  bounds_difference_inherit_fork(dst, src);
  bounds_relation_init(dst, dst->scratch, true);
  dst->oom = false;
  bounds_query_inherit_fork(dst, src);
  dst->equality_disabled_depth = src->equality_disabled_depth;
  dst->exact_proof_call_depth = src->exact_proof_call_depth;
  bounds_range_inherit_fork(dst, src);
  if (!bounds_store_fork_var_index(dst, src) ||
      !bounds_difference_clone_fork(dst, src) ||
      !bounds_store_fork_mod_inverse(dst, src) ||
      bounds_relation_clone_fork(dst, src) != IXS_RELATION_STATUS_OK ||
      !bounds_store_fork_expr(dst, src) || !bounds_store_fork_nonzero(dst, src))
    goto failed;
  return true;

failed:
  bounds_query_destroy(dst);
  return false;
}
