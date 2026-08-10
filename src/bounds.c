/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds.h"
#include "bounds_difference.h"
#include "bounds_query.h"
#include "bounds_range.h"
#include "bounds_relation.h"
#include "bounds_store.h"
#include "expand.h"
#include "facts_store.h"
#include "radix_algebra.h"
#include "simplify.h"

IXS_STATIC void ixs_bounds_reset_read_cache(ixs_bounds *b, bool old_oom) {
  bounds_store_invalidate_reads(b);
  if (b)
    b->oom = old_oom;
}

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

static ixs_node *bounds_simplify_fact_free(ixs_ctx *ctx, ixs_node *expr) {
  return simp_simplify_bounds(ctx, expr, NULL);
}

IXS_STATIC ixs_node *bounds_canonical_expr(ixs_bounds *b, ixs_node *expr) {
  ixs_node *cached, *canonical, *expanded;
  ixs_arena_mark diag_mark;
  const char **saved_errors;
  size_t saved_nerrors, saved_errors_cap;
  if (!b || !b->ctx || !expr || ixs_node_is_sentinel(expr))
    return expr;
  if (expr->tag == IXS_INT || expr->tag == IXS_RAT || expr->tag == IXS_SYM)
    return expr;

  cached = ixs_node_transform_cache_lookup(b->ctx, expr,
                                           IXS_NODE_TRANSFORM_BOUNDS_CANONICAL);
  if (cached)
    return cached;

  /* Alias
   * diagnostics must
   * not leak into
   * otherwise valid
   * range queries.
   */
  diag_mark = ixs_arena_save(&b->ctx->diag);
  saved_errors = b->ctx->errors;
  saved_nerrors = b->ctx->nerrors;
  saved_errors_cap = b->ctx->errors_cap;
  expanded = expand_impl(b->ctx, expr);
  canonical = expanded && !ixs_node_is_sentinel(expanded)
                  ? bounds_simplify_fact_free(b->ctx, expanded)
                  : expanded;
  ixs_arena_restore(&b->ctx->diag, diag_mark);
  b->ctx->errors = saved_errors;
  b->ctx->nerrors = saved_nerrors;
  b->ctx->errors_cap = saved_errors_cap;

  if (!expanded) {
    b->oom = true;
    return expr;
  }
  if (ixs_node_is_sentinel(expanded))
    return expr;
  if (!canonical) {
    b->oom = true;
    return expr;
  }
  if (ixs_node_is_sentinel(canonical))
    return expanded;
  ixs_node_transform_cache_store(
      b->ctx, expr, IXS_NODE_TRANSFORM_BOUNDS_CANONICAL, canonical);
  return canonical;
}

IXS_STATIC void bounds_admit_exact_relation(ixs_bounds *b, ixs_node *lhs,
                                            ixs_node *rhs, int64_t offset) {
  if (!b || !lhs || !rhs || b->oom || b->contradiction)
    return;
  bounds_store_publish_relation_status(
      b, ixs_relation_algebra_assert(&b->relations, lhs, rhs, offset));
}

#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
IXS_STATIC ixs_radix_algebra_result
ixs_radix_algebra_facts_probe(ixs_facts *facts, const ixs_node *expr) {
  ixs_radix_algebra_result result = {IXS_CHECK_UNKNOWN, false, false};
  ixs_session_binding binding;
  ixs_ctx *ctx;
  if (!expr || !facts_store_bind(facts, &binding, &ctx))
    return result;
  result = ixs_radix_algebra_nonnegative(&facts->bounds, expr);
  facts_store_unbind(facts, &binding);
  return result;
}
#endif
