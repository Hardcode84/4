/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds.h"
#include "additive_row.h"
#include "bounds_defined.h"
#include "bounds_difference.h"
#include "bounds_predicate.h"
#include "bounds_query.h"
#include "bounds_range.h"
#include "bounds_relation.h"
#include "bounds_store.h"
#include "division_algebra.h"
#include "expand.h"
#include "facts_store.h"
#include "hash.h"
#include "low_bits_algebra.h"
#include "query_walk.h"
#include "quotient_algebra.h"
#include "radix_algebra.h"
#include "simplify.h"
#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>

/* Transport detail is intentionally private.  The public fact-query API keeps
 * its original value/out-parameter contracts and reports transport failures
 * through the owning session's diagnostics. */
typedef enum {
  IXS_FACT_QUERY_COMPLETE,
  IXS_FACT_QUERY_LIMITED,
  IXS_FACT_QUERY_INVALID,
  IXS_FACT_QUERY_OOM
} ixs_fact_query_status;

typedef struct {
  ixs_fact_query_status status;
  ixs_check_result check;
} ixs_fact_check_result;

typedef struct {
  ixs_fact_query_status status;
  const ixs_node *value;
} ixs_simplify_result;

typedef struct {
  ixs_fact_query_status status;
  bool available;
  int64_t difference;
} ixs_constant_difference_result;

typedef struct {
  ixs_fact_query_status status;
  ixs_pow2_fact fact;
} ixs_pow2_query_result;

typedef struct {
  ixs_fact_query_status status;
  ixs_known_bits bits;
} ixs_known_bits_query_result;

typedef struct {
  ixs_fact_query_status status;
  bool available;
  ixs_range_result range;
} ixs_range_query_result;

typedef struct {
  ixs_fact_query_status status;
  bool available;
  int64_t modulus;
  int64_t residue;
} ixs_symbol_congruence_result;

typedef struct {
  ixs_fact_query_status status;
  bool available;
  const ixs_node *coefficient;
  const ixs_node *residual;
} ixs_affine_decomposition_result;

typedef struct {
  ixs_fact_query_status status;
  bool available;
  const ixs_node *difference;
} ixs_finite_difference_result;

typedef struct {
  ixs_fact_query_status status;
  bool available;
  const ixs_node *residual;
  int64_t constant;
} ixs_additive_constant_result;

static ixs_check_result bounds_check_defined_without_equality(ixs_bounds *b,
                                                              ixs_node *expr,
                                                              bool *oom,
                                                              bool *limited);
IXS_STATIC ixs_algebra_status bounds_collect_relation_component(
    ixs_bounds *b, ixs_node *expr, bounds_relation_component *component);
IXS_STATIC ixs_algebra_status bounds_relation_offset_checked(
    ixs_bounds *b, ixs_node *lhs, ixs_node *rhs, ixs_relation_offset *offset);
static ixs_algebra_status bounds_exact_relation_difference(ixs_bounds *b,
                                                           ixs_node *lhs,
                                                           ixs_node *rhs,
                                                           int64_t *delta);

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
  b->predicate_equivalence_depth = 0;
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
  b->predicate_equivalence_depth = 0;
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
  /* A fork made by a nested query remains inside the source predicate probe;
   * inheriting the guard prevents the fork from reopening the same cycle. */
  dst->predicate_equivalence_depth = src->predicate_equivalence_depth;
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

  /* Alias diagnostics must not leak into otherwise valid range queries. */
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

static ixs_check_result bounds_check_defined_without_equality(ixs_bounds *b,
                                                              ixs_node *expr,
                                                              bool *oom,
                                                              bool *limited) {
  ixs_check_result result;
  assert(b->equality_disabled_depth != UINT_MAX);
  b->equality_disabled_depth++;
  result = bounds_defined_check_detail(b, expr, oom, limited);
  b->equality_disabled_depth--;
  return result;
}

static ixs_algebra_status bounds_relation_require_defined(ixs_bounds *b,
                                                          ixs_node *expr) {
  bool defined_oom = false;
  bool defined_limited = false;
  if (bounds_check_defined_without_equality(b, expr, &defined_oom,
                                            &defined_limited) == IXS_CHECK_TRUE)
    return IXS_ALGEBRA_MATCH;
  if (defined_oom)
    return IXS_ALGEBRA_OOM;
  if (!defined_limited)
    return IXS_ALGEBRA_NO_MATCH;
  if (bounds_query_is_tracking(b))
    bounds_query_note_limit(b);
  return IXS_ALGEBRA_LIMITED;
}

/* Collect the independently defined component incident to expr. Traversal is
 * nonrecursive and grows with the component; there is no semantic walk cap. */
IXS_STATIC ixs_algebra_status bounds_collect_relation_component(
    ixs_bounds *b, ixs_node *expr, bounds_relation_component *component) {
  bounds_relation_cursor_step step;
  ixs_algebra_status status;
  ixs_node *candidate = NULL;
  size_t root_endpoint;
  component->scratch = NULL;
  if (!b || !expr || ixs_relation_algebra_edge_count(&b->relations) == 0 ||
      !ixs_relation_algebra_find_endpoint(&b->relations, expr, &root_endpoint))
    return IXS_ALGEBRA_NO_MATCH;
  status = bounds_relation_require_defined(b, expr);
  if (status != IXS_ALGEBRA_MATCH)
    return status;
  step = bounds_relation_component_begin(&b->relations, b->scratch,
                                         root_endpoint, component);
  for (;;) {
    if (step == BOUNDS_RELATION_CURSOR_READY) {
      step = bounds_relation_component_pull(component, &candidate);
      continue;
    }
    if (step == BOUNDS_RELATION_CURSOR_ADMISSION) {
      if (!candidate)
        abort();
      status = bounds_relation_require_defined(b, candidate);
      if (status == IXS_ALGEBRA_MATCH) {
        step = bounds_relation_component_resolve(component, true);
        continue;
      }
      if (status == IXS_ALGEBRA_NO_MATCH) {
        step = bounds_relation_component_resolve(component, false);
        continue;
      }
      return status;
    }
    if (step == BOUNDS_RELATION_CURSOR_COMPLETE)
      return IXS_ALGEBRA_MATCH;
    if (step == BOUNDS_RELATION_CURSOR_OOM) {
      b->oom = true;
      return IXS_ALGEBRA_OOM;
    }
    assert(step == BOUNDS_RELATION_CURSOR_INVALID);
    bounds_query_note_invalid(b);
    return IXS_ALGEBRA_INVALID;
  }
}

IXS_STATIC bool
bounds_publish_relation_component(ixs_bounds *b,
                                  const bounds_relation_component *component) {
  if (!bounds_query_is_tracking(b))
    return true;
  if (!bounds_relation_component_publish_defined(b, component)) {
    b->oom = true;
    return false;
  }
  return true;
}

IXS_STATIC ixs_algebra_status bounds_relation_offset_checked(
    ixs_bounds *b, ixs_node *lhs, ixs_node *rhs, ixs_relation_offset *offset) {
  bounds_relation_component component;
  ixs_algebra_status status;
  ixs_relation_query_status cached;
  size_t lhs_endpoint;
  size_t rhs_endpoint;
  size_t entry_index;
  if (!b || !lhs || !rhs || !offset || b->oom || b->contradiction)
    return IXS_ALGEBRA_NO_MATCH;
  if (lhs == rhs) {
    *offset = ixs_relation_offset_from_int64(0);
    return IXS_ALGEBRA_MATCH;
  }
  if (!ixs_relation_algebra_find_endpoint(&b->relations, lhs, &lhs_endpoint))
    return IXS_ALGEBRA_NO_MATCH;
  if (bounds_query_is_tracking(b) &&
      ixs_relation_algebra_find_endpoint(&b->relations, rhs, &rhs_endpoint)) {
    cached =
        bounds_relation_cached_offset(b, rhs_endpoint, rhs_endpoint, offset);
    if (cached == IXS_RELATION_QUERY_NONE) {
      status = bounds_collect_relation_component(b, rhs, &component);
      if (status != IXS_ALGEBRA_MATCH) {
        bounds_relation_component_destroy(&component);
        return status;
      }
      if (!bounds_publish_relation_component(b, &component)) {
        bounds_relation_component_destroy(&component);
        return IXS_ALGEBRA_OOM;
      }
      bounds_relation_component_destroy(&component);
    } else if (cached == IXS_RELATION_QUERY_INVALID) {
      bounds_query_note_invalid(b);
      return IXS_ALGEBRA_INVALID;
    }
    cached =
        bounds_relation_cached_offset(b, lhs_endpoint, rhs_endpoint, offset);
    if (cached == IXS_RELATION_QUERY_INVALID) {
      bounds_query_note_invalid(b);
      return IXS_ALGEBRA_INVALID;
    }
    return cached == IXS_RELATION_QUERY_FOUND ? IXS_ALGEBRA_MATCH
                                              : IXS_ALGEBRA_NO_MATCH;
  }
  status = bounds_collect_relation_component(b, rhs, &component);
  if (status != IXS_ALGEBRA_MATCH) {
    bounds_relation_component_destroy(&component);
    return status;
  }
  if (!bounds_relation_component_find(&component, lhs_endpoint, &entry_index)) {
    bounds_relation_component_destroy(&component);
    return IXS_ALGEBRA_NO_MATCH;
  }
  *offset = component.entries[entry_index].offset;
  bounds_relation_component_destroy(&component);
  return IXS_ALGEBRA_MATCH;
}

static ixs_algebra_status bounds_exact_relation_difference(ixs_bounds *b,
                                                           ixs_node *lhs,
                                                           ixs_node *rhs,
                                                           int64_t *delta) {
  ixs_algebra_status status;
  ixs_relation_offset offset;
  if (!b || !lhs || !rhs || !delta || b->oom || b->contradiction)
    return IXS_ALGEBRA_NO_MATCH;
  /* Preserve the weighted symbol forest as the hot path. */
  if (lhs->tag == IXS_SYM && rhs->tag == IXS_SYM &&
      ixs_relation_algebra_total_symbol_difference(&b->relations, lhs, rhs,
                                                   delta))
    return IXS_ALGEBRA_MATCH;
  status = bounds_relation_offset_checked(b, lhs, rhs, &offset);
  if (status != IXS_ALGEBRA_MATCH)
    return status;
  if (!ixs_relation_offset_to_int64(offset, delta))
    return IXS_ALGEBRA_UNREPRESENTABLE;
  return IXS_ALGEBRA_MATCH;
}

static void interval_to_range_result(ixs_interval iv, ixs_range_result *out) {
  out->has_lower = !iv.lo_inf;
  out->has_upper = !iv.hi_inf;
  out->lower_p = iv.lo_inf ? 0 : iv.lo_p;
  out->lower_q = iv.lo_inf ? 1 : iv.lo_q;
  out->upper_p = iv.hi_inf ? 0 : iv.hi_p;
  out->upper_q = iv.hi_inf ? 1 : iv.hi_q;
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

typedef struct {
  ixs_bounds *bounds;
  ixs_ctx *ctx;
  const char *query;
  ixs_bounds_query_state *query_state;
  ixs_bounds_transport_snapshot transport;
  size_t nerrors;
  bool old_oom;
  bool tracking_entered;
  bool tracking_limited;
  bool active;
} facts_read_query_scope;

static void facts_read_query_begin(facts_read_query_scope *scope,
                                   ixs_bounds *bounds, ixs_ctx *ctx,
                                   const char *query) {
  memset(scope, 0, sizeof(*scope));
  scope->bounds = bounds;
  scope->ctx = ctx;
  scope->query = query;
  scope->old_oom = bounds->oom;
  (void)bounds_query_force_hold_begin(bounds, &scope->tracking_entered);
  scope->query_state = bounds->query_state;
  scope->transport = ixs_bounds_query_transport_snapshot(bounds);
  scope->nerrors = ctx ? ctx->nerrors : 0u;
  scope->active = true;
}

typedef struct {
  bool new_oom;
  bool limited;
  bool invalid;
} facts_read_query_observation;

static facts_read_query_observation
facts_read_query_observe(facts_read_query_scope *scope) {
  facts_read_query_observation result = {false, false, false};
  ixs_bounds_transport_status transport = IXS_BOUNDS_TRANSPORT_CLEAN;
  ixs_bounds_transport_snapshot current =
      ixs_bounds_query_transport_snapshot(scope->bounds);
  if (scope->bounds->query_state) {
    if (scope->tracking_entered && scope->query_state &&
        (scope->bounds->query_state != scope->query_state ||
         current.generation != scope->transport.generation))
      transport = IXS_BOUNDS_TRANSPORT_INVALID;
    else
      transport = bounds_query_state_transport(scope->bounds);
  }
  result.new_oom = !scope->old_oom && scope->bounds->oom;
  result.limited = bounds_query_limited_since(scope->bounds, scope->transport);
  result.invalid = bounds_query_invalid_since(scope->bounds, scope->transport);
  if (scope->bounds->query_state != scope->query_state ||
      current.generation != scope->transport.generation)
    result.invalid = true;
  if (transport == IXS_BOUNDS_TRANSPORT_LIMITED)
    result.limited = true;
  else if (transport == IXS_BOUNDS_TRANSPORT_INVALID)
    result.invalid = true;
  else if (transport == IXS_BOUNDS_TRANSPORT_OOM)
    result.new_oom = true;
  return result;
}

static ixs_fact_query_status
facts_read_query_finish(facts_read_query_scope *scope,
                        ixs_fact_query_status status) {
  facts_read_query_observation observed;
  if (!scope || !scope->active)
    return status;
  observed = facts_read_query_observe(scope);
  if (observed.invalid)
    status = IXS_FACT_QUERY_INVALID;
  else if (observed.new_oom || scope->old_oom)
    status = IXS_FACT_QUERY_OOM;
  else if ((observed.limited || scope->tracking_limited) &&
           status == IXS_FACT_QUERY_COMPLETE)
    status = IXS_FACT_QUERY_LIMITED;
  if (observed.new_oom || observed.limited || scope->tracking_limited ||
      observed.invalid || status != IXS_FACT_QUERY_COMPLETE)
    bounds_store_invalidate_reads(scope->bounds);
  scope->bounds->oom = scope->old_oom;
  if (scope->ctx && scope->ctx->nerrors == scope->nerrors) {
    if (status == IXS_FACT_QUERY_OOM)
      ixs_ctx_push_error(scope->ctx, "%s: out of memory", scope->query);
    else if (status == IXS_FACT_QUERY_INVALID)
      ixs_ctx_push_error(scope->ctx, "%s: invalid internal relation state",
                         scope->query);
    else if (status == IXS_FACT_QUERY_LIMITED)
      ixs_ctx_push_error(scope->ctx, "%s: resource limit exceeded",
                         scope->query);
  }
  if (scope->tracking_entered)
    ixs_bounds_query_hold_end(scope->bounds);
  scope->active = false;
  return status;
}

static bool facts_query_node_ok(ixs_ctx *ctx, ixs_node *node,
                                const char *query) {
  if (!node) {
    ixs_ctx_push_error(ctx, "%s: NULL expression", query);
    return false;
  }
  if (ixs_node_is_sentinel(node)) {
    ixs_ctx_push_error(ctx, "%s: sentinel expression is not accepted", query);
    return false;
  }
  if (!ixs_ctx_owns_node(ctx, node)) {
    ixs_ctx_push_error(ctx, "%s: expression belongs to a different context",
                       query);
    return false;
  }
  return true;
}

static ixs_node *
facts_simplify_truncating_remainders(ixs_ctx *ctx, ixs_bounds *bounds,
                                     ixs_node *source, ixs_node *root,
                                     ixs_fact_query_status *status);

static bool facts_simplify_preflight(ixs_facts *facts, ixs_ctx *ctx,
                                     ixs_node *expr,
                                     ixs_simplify_result *result) {
  if (!facts_store_ready(facts)) {
    ixs_ctx_push_error(ctx, "facts: fact set is unusable");
    result->status = IXS_FACT_QUERY_COMPLETE;
    result->value = ctx->sentinel_error;
    return true;
  }
  if (!expr) {
    result->status = IXS_FACT_QUERY_COMPLETE;
    return true;
  }
  if (!ixs_ctx_owns_node(ctx, expr)) {
    ixs_ctx_push_error(ctx, "facts: expression belongs to a different context");
    result->status = IXS_FACT_QUERY_COMPLETE;
    result->value = ctx->sentinel_error;
    return true;
  }
  if (ixs_node_is_sentinel(expr)) {
    result->status = IXS_FACT_QUERY_COMPLETE;
    result->value = expr;
    return true;
  }
  return false;
}

static ixs_simplify_result facts_query_simplify(ixs_facts *facts,
                                                ixs_node *expr) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_arena_mark mark;
  ixs_ctx *ctx;
  ixs_node *value = NULL;
  ixs_simplify_result result = {IXS_FACT_QUERY_INVALID, NULL};
  bool old_oom;
  bool limited = false;
  bool query_held = false;

  if (!facts_store_bind(facts, &binding, &ctx))
    return result;
  if (facts_simplify_preflight(facts, ctx, expr, &result)) {
    facts_store_unbind(facts, &binding);
    return result;
  }
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "simplify");
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    result.value = expr;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(&facts->bounds, expr, &query_held)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_LIMITED;
    goto cleanup;
  }

  mark = ixs_arena_save(&ctx->scratch);
  old_oom = facts->bounds.oom;
  value = simp_simplify_bounds_status(ctx, expr, &facts->bounds, &limited);
  result.status = IXS_FACT_QUERY_COMPLETE;
  if (!limited && value && !ixs_node_is_sentinel(value) &&
      ixs_node_contains_rounding(value) && ixs_node_contains_piecewise(value))
    value = facts_simplify_truncating_remainders(ctx, &facts->bounds, expr,
                                                 value, &result.status);
  if (!limited && result.status == IXS_FACT_QUERY_COMPLETE && value &&
      !ixs_node_is_sentinel(value))
    value = simp_normalize_rational_carrier(ctx, &facts->bounds, value);
  if (limited) {
    result.status = IXS_FACT_QUERY_LIMITED;
  } else if (result.status != IXS_FACT_QUERY_COMPLETE) {
    value = NULL;
  } else if (!value || (!old_oom && facts->bounds.oom)) {
    result.status = IXS_FACT_QUERY_OOM;
    bounds_store_invalidate_reads(&facts->bounds);
  } else if (ixs_node_is_sentinel(value)) {
    result.status = IXS_FACT_QUERY_INVALID;
  } else {
    result.status = IXS_FACT_QUERY_COMPLETE;
    result.value = value;
  }
  facts->bounds.oom = old_oom;
  ixs_arena_restore(&ctx->scratch, mark);

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.value = NULL;
  facts_store_unbind(facts, &binding);
  return result;
}

static bool facts_simplify_batch_remainders(ixs_ctx *ctx, ixs_bounds *bounds,
                                            ixs_node *const *sources,
                                            ixs_node **exprs, size_t n,
                                            ixs_fact_query_status *status) {
  size_t i;
  for (i = 0; i < n; i++) {
    bool query_held = false;
    ixs_fact_query_status item_status = IXS_FACT_QUERY_COMPLETE;
    if (!exprs[i] || ixs_node_is_sentinel(exprs[i]) ||
        !ixs_node_contains_rounding(exprs[i]) ||
        !ixs_node_contains_piecewise(exprs[i]))
      continue;
    if (!ixs_bounds_query_hold_begin(bounds, exprs[i], &query_held)) {
      if (bounds->oom)
        return false;
      continue;
    }
    exprs[i] = facts_simplify_truncating_remainders(ctx, bounds, sources[i],
                                                    exprs[i], &item_status);
    if (query_held)
      ixs_bounds_query_hold_end(bounds);
    if (item_status != IXS_FACT_QUERY_COMPLETE) {
      *status = item_status;
      return false;
    }
    if (!exprs[i])
      return false;
  }
  return true;
}

static ixs_fact_query_status
facts_query_simplify_batch(ixs_facts *facts, ixs_node **exprs, size_t n) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_arena_mark mark;
  ixs_ctx *ctx;
  ixs_node **originals = NULL;
  bool ok;
  bool old_oom;
  size_t i;
  ixs_fact_query_status status = IXS_FACT_QUERY_INVALID;

  if (!facts_store_bind(facts, &binding, &ctx))
    return status;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "simplify batch");
  mark = ixs_arena_save(&ctx->scratch);
  if (n > 0 && !exprs) {
    ixs_ctx_push_error(ctx, "simplify batch: NULL batch with nonzero count");
    goto cleanup;
  }
  if (n > SIZE_MAX / sizeof(*originals)) {
    status = IXS_FACT_QUERY_OOM;
    goto cleanup;
  }
  if (!facts_store_ready(facts)) {
    status = facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "simplify batch: fact set is unusable");
    goto cleanup;
  }
  for (i = 0; i < n; i++) {
    if (!facts_query_node_ok(ctx, exprs[i], "simplify batch"))
      goto cleanup;
  }
  if (ixs_bounds_has_empty(&facts->bounds)) {
    status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }

  if (n > 0) {
    originals =
        ixs_arena_alloc(&ctx->scratch, n * sizeof(*originals), sizeof(void *));
    if (!originals) {
      status = IXS_FACT_QUERY_OOM;
      goto cleanup;
    }
    memcpy(originals, exprs, n * sizeof(*originals));
  }
  old_oom = facts->bounds.oom;
  ok = simp_simplify_batch_bounds(ctx, exprs, n, &facts->bounds);
  if (ok)
    ok = facts_simplify_batch_remainders(ctx, &facts->bounds, originals, exprs,
                                         n, &status);
  if (ok) {
    for (i = 0; i < n; i++) {
      exprs[i] = simp_normalize_rational_carrier(ctx, &facts->bounds, exprs[i]);
      if (!exprs[i]) {
        ok = false;
        break;
      }
    }
  }
  if (!ok || (!old_oom && facts->bounds.oom)) {
    if (status == IXS_FACT_QUERY_COMPLETE)
      status = bounds_query_limited_since(&facts->bounds, read_scope.transport)
                   ? IXS_FACT_QUERY_LIMITED
                   : IXS_FACT_QUERY_OOM;
    bounds_store_invalidate_reads(&facts->bounds);
  } else {
    status = IXS_FACT_QUERY_COMPLETE;
    for (i = 0; i < n; i++) {
      if (ixs_node_is_sentinel(exprs[i])) {
        status = IXS_FACT_QUERY_INVALID;
        break;
      }
    }
  }
  facts->bounds.oom = old_oom;

cleanup:
  status = facts_read_query_finish(&read_scope, status);
  if (status != IXS_FACT_QUERY_COMPLETE && originals)
    memcpy(exprs, originals, n * sizeof(*originals));
  ixs_arena_restore(&ctx->scratch, mark);
  facts_store_unbind(facts, &binding);
  return status;
}

typedef struct {
  ixs_node *lhs;
  ixs_node *rhs;
  ixs_check_result result;
  bool active;
  bool complete;
} equivalence_memo_entry;

typedef struct {
  ixs_ctx *ctx;
  ixs_bounds *bounds;
  ixs_arena_mark memo_mark;
  equivalence_memo_entry *memo;
  size_t memo_count;
  size_t memo_capacity;
  size_t visited;
  unsigned bounded_subproof_depth;
  unsigned xor_context_subproof_depth;
  bool limited;
  bool invalid;
  bool oom;
  bool arithmetic_unrepresentable;
} equivalence_state;

static ixs_check_result
equivalence_quotient_remainder_algebra(equivalence_state *state, ixs_node *lhs,
                                       ixs_node *rhs);

/* Algebraic bridge rules may nest only through this fixed allowance. */
#define EQUIVALENCE_BOUNDED_SUBPROOF_DEPTH 4u
/* The Piecewise fallback represents one complete selector domain in a mask. */
#define EQUIVALENCE_PIECEWISE_MAX_CASES 16u
#define EQUIVALENCE_PIECEWISE_MAX_POINTS 64u

static size_t equivalence_pair_hash(ixs_node *lhs, ixs_node *rhs) {
  uintptr_t left = (uintptr_t)lhs;
  uintptr_t right = (uintptr_t)rhs;
  left >>= 3u;
  right >>= 3u;
  return (size_t)(left ^ (right + (left << 6u) + (left >> 2u)));
}

static bool equivalence_memo_grow(equivalence_state *state) {
  size_t next_capacity = state->memo_capacity ? state->memo_capacity * 2u : 32u;
  equivalence_memo_entry *grown;
  size_t i;
  if (next_capacity <= state->memo_capacity ||
      next_capacity > SIZE_MAX / sizeof(*grown))
    return false;
  grown = ixs_arena_alloc(&state->bounds->query_arena,
                          next_capacity * sizeof(*grown), sizeof(void *));
  if (!grown)
    return false;
  memset(grown, 0, next_capacity * sizeof(*grown));
  for (i = 0; i < state->memo_capacity; i++) {
    equivalence_memo_entry entry = state->memo[i];
    size_t index;
    if (!entry.lhs)
      continue;
    index = equivalence_pair_hash(entry.lhs, entry.rhs) & (next_capacity - 1u);
    while (grown[index].lhs)
      index = (index + 1u) & (next_capacity - 1u);
    grown[index] = entry;
  }
  state->memo = grown;
  state->memo_capacity = next_capacity;
  return true;
}

static equivalence_memo_entry *equivalence_memo_get(equivalence_state *state,
                                                    ixs_node *lhs,
                                                    ixs_node *rhs,
                                                    bool create) {
  size_t index;
  if (create && (!state->memo_capacity ||
                 state->memo_count + 1u > state->memo_capacity / 2u)) {
    if (!equivalence_memo_grow(state))
      return NULL;
  }
  if (!state->memo_capacity)
    return NULL;
  index = equivalence_pair_hash(lhs, rhs) & (state->memo_capacity - 1u);
  while (state->memo[index].lhs &&
         (state->memo[index].lhs != lhs || state->memo[index].rhs != rhs))
    index = (index + 1u) & (state->memo_capacity - 1u);
  if (!state->memo[index].lhs) {
    if (!create)
      return NULL;
    state->memo[index].lhs = lhs;
    state->memo[index].rhs = rhs;
    state->memo[index].result = IXS_CHECK_UNKNOWN;
    state->memo_count++;
  }
  return &state->memo[index];
}

static void equivalence_state_init(equivalence_state *state, ixs_ctx *ctx,
                                   ixs_bounds *bounds) {
  memset(state, 0, sizeof(*state));
  state->ctx = ctx;
  state->bounds = bounds;
  state->memo_mark = ixs_arena_save(&bounds->query_arena);
}

static void equivalence_state_destroy(equivalence_state *state) {
  ixs_arena_restore(&state->bounds->query_arena, state->memo_mark);
}

static ixs_check_result equivalence_core(equivalence_state *state,
                                         ixs_node *lhs, ixs_node *rhs,
                                         unsigned depth);
static ixs_check_result equivalence_core_impl(equivalence_state *state,
                                              ixs_node *lhs, ixs_node *rhs,
                                              unsigned depth,
                                              bool allow_context);
static bool bounds_constant_delta_query(ixs_ctx *ctx, ixs_bounds *bounds,
                                        ixs_node *lhs, ixs_node *rhs,
                                        bool allow_expand, int64_t *delta);

static ixs_check_result equivalence_bounded_core(equivalence_state *state,
                                                 ixs_node *lhs, ixs_node *rhs,
                                                 unsigned depth) {
  ixs_check_result result;
  if (state->bounded_subproof_depth >= EQUIVALENCE_BOUNDED_SUBPROOF_DEPTH)
    return IXS_CHECK_UNKNOWN;
  state->bounded_subproof_depth++;
  result = equivalence_core(state, lhs, rhs, depth);
  state->bounded_subproof_depth--;
  return result;
}

static bool equivalence_context_shape(ixs_node *lhs, ixs_node *rhs,
                                      uint32_t *child_count) {
  uint32_t lhs_children;
  uint32_t rhs_children;
  uint32_t i;

  if (lhs->tag != rhs->tag || !defined_child_count(lhs, &lhs_children) ||
      !defined_child_count(rhs, &rhs_children) || lhs_children == 0u ||
      lhs_children != rhs_children)
    return false;
  switch (lhs->tag) {
  case IXS_ADD:
  case IXS_FLOOR:
  case IXS_CEIL:
    break;
  case IXS_MUL:
    if (lhs->u.mul.nfactors != rhs->u.mul.nfactors)
      return false;
    for (i = 0; i < lhs->u.mul.nfactors; i++)
      if (lhs->u.mul.factors[i].exp != rhs->u.mul.factors[i].exp)
        return false;
    break;
  default:
    return false;
  }
  *child_count = lhs_children;
  return true;
}

static bool equivalence_grouped_add_context(ixs_node *node) {
  ixs_tag first;
  ixs_tag second;

  if (node->tag != IXS_ADD || node->u.add.nterms != 2u)
    return false;
  first = (ixs_tag)node->u.add.terms[0].term->tag;
  second = (ixs_tag)node->u.add.terms[1].term->tag;
  return (first == IXS_MOD && (second == IXS_FLOOR || second == IXS_CEIL)) ||
         (second == IXS_MOD && (first == IXS_FLOOR || first == IXS_CEIL));
}

typedef struct {
  ixs_node *lhs;
  ixs_node *rhs;
} equivalence_context_pair;

typedef struct {
  equivalence_context_pair *pairs;
  size_t count;
  size_t capacity;
  equivalence_context_pair *seen;
  size_t seen_count;
  size_t seen_capacity;
} equivalence_context_worklist;

static bool
equivalence_context_seen_grow(equivalence_state *state,
                              equivalence_context_worklist *worklist) {
  size_t capacity =
      worklist->seen_capacity ? worklist->seen_capacity * 2u : 32u;
  equivalence_context_pair *grown;
  size_t i;

  if (capacity <= worklist->seen_capacity ||
      capacity > SIZE_MAX / sizeof(*grown))
    goto oom;
  grown = ixs_arena_alloc(&state->bounds->query_arena,
                          capacity * sizeof(*grown), sizeof(void *));
  if (!grown)
    goto oom;
  memset(grown, 0, capacity * sizeof(*grown));
  for (i = 0; i < worklist->seen_capacity; i++) {
    equivalence_context_pair pair = worklist->seen[i];
    size_t slot;
    if (!pair.lhs)
      continue;
    slot = equivalence_pair_hash(pair.lhs, pair.rhs) & (capacity - 1u);
    while (grown[slot].lhs)
      slot = (slot + 1u) & (capacity - 1u);
    grown[slot] = pair;
  }
  worklist->seen = grown;
  worklist->seen_capacity = capacity;
  return true;

oom:
  state->oom = true;
  return false;
}

static bool equivalence_context_enqueue(equivalence_state *state,
                                        equivalence_context_worklist *worklist,
                                        ixs_node *lhs, ixs_node *rhs) {
  size_t slot;

  if (!lhs || !rhs) {
    state->invalid = true;
    return false;
  }
  if ((uintptr_t)lhs > (uintptr_t)rhs) {
    ixs_node *tmp = lhs;
    lhs = rhs;
    rhs = tmp;
  }
  if (!worklist->seen_capacity ||
      worklist->seen_count + 1u > worklist->seen_capacity / 2u)
    if (!equivalence_context_seen_grow(state, worklist))
      return false;
  slot = equivalence_pair_hash(lhs, rhs) & (worklist->seen_capacity - 1u);
  while (worklist->seen[slot].lhs &&
         (worklist->seen[slot].lhs != lhs || worklist->seen[slot].rhs != rhs))
    slot = (slot + 1u) & (worklist->seen_capacity - 1u);
  if (worklist->seen[slot].lhs)
    return true;
  worklist->seen[slot].lhs = lhs;
  worklist->seen[slot].rhs = rhs;
  worklist->seen_count++;

  if (worklist->count == worklist->capacity) {
    size_t capacity = worklist->capacity ? worklist->capacity * 2u : 32u;
    equivalence_context_pair *grown;
    if (capacity <= worklist->capacity ||
        capacity > SIZE_MAX / sizeof(*grown)) {
      state->oom = true;
      return false;
    }
    grown = ixs_arena_grow(&state->bounds->query_arena, worklist->pairs,
                           worklist->capacity * sizeof(*grown),
                           capacity * sizeof(*grown), sizeof(void *));
    if (!grown) {
      state->oom = true;
      return false;
    }
    worklist->pairs = grown;
    worklist->capacity = capacity;
  }
  worklist->pairs[worklist->count].lhs = lhs;
  worklist->pairs[worklist->count].rhs = rhs;
  worklist->count++;
  return true;
}

static uint32_t equivalence_add_relation_size(ixs_node *node) {
  if (ixs_node_is_zero(node))
    return 0u;
  return node->tag == IXS_ADD ? node->u.add.nterms : 1u;
}

static bool equivalence_cancel_common_add(equivalence_state *state,
                                          ixs_node *lhs, ixs_node *rhs,
                                          ixs_node **lhs_residual,
                                          ixs_node **rhs_residual) {
  struct ixs_node_impl equality;
  ixs_node *relation_lhs;
  ixs_node *relation_rhs;
  int64_t offset;
  uint64_t original_size;
  uint64_t residual_size;

  if (lhs->tag != IXS_ADD || rhs->tag != IXS_ADD ||
      lhs->u.add.nterms == rhs->u.add.nterms)
    return false;
  memset(&equality, 0, sizeof(equality));
  equality.tag = IXS_CMP;
  equality.u.binary.lhs = lhs;
  equality.u.binary.rhs = rhs;
  equality.u.binary.cmp_op = IXS_CMP_EQ;
  if (!bounds_extract_cmp_exact_relation(
          state->bounds, &equality, &relation_lhs, &relation_rhs, &offset)) {
    if (state->bounds->oom)
      state->oom = true;
    return false;
  }
  if (offset != 0) {
    ixs_node *constant = ixs_node_int(state->ctx, offset);
    bool unrepresentable = false;
    if (!constant) {
      state->oom = true;
      return false;
    }
    relation_rhs =
        simp_try_add(state->ctx, relation_rhs, constant, &unrepresentable);
    if (unrepresentable)
      return false;
    if (!relation_rhs) {
      state->oom = true;
      return false;
    }
    if (ixs_node_is_sentinel(relation_rhs))
      return false;
  }
  original_size = (uint64_t)lhs->u.add.nterms + (uint64_t)rhs->u.add.nterms;
  residual_size = (uint64_t)equivalence_add_relation_size(relation_lhs) +
                  (uint64_t)equivalence_add_relation_size(relation_rhs);
  if (residual_size >= original_size ||
      ixs_bounds_check_defined(state->bounds, relation_lhs) != IXS_CHECK_TRUE ||
      ixs_bounds_check_defined(state->bounds, relation_rhs) != IXS_CHECK_TRUE) {
    if (state->bounds->oom)
      state->oom = true;
    return false;
  }
  *lhs_residual = relation_lhs;
  *rhs_residual = relation_rhs;
  return true;
}

static bool equivalence_xor_child_proven(equivalence_state *state,
                                         ixs_node *lhs, ixs_node *rhs,
                                         unsigned depth) {
  ixs_check_result result;
  state->xor_context_subproof_depth++;
  result = equivalence_bounded_core(state, lhs, rhs, depth);
  state->xor_context_subproof_depth--;
  return result == IXS_CHECK_TRUE;
}

/* Canonical XOR nodes are already flat. The production-backed binary case
 * pairs exact arguments before semantic candidates. The matcher remains
 * O(A^2) in its admitted arity A=2. */
static ixs_check_result equivalence_match_xor_context(equivalence_state *state,
                                                      ixs_node *lhs,
                                                      ixs_node *rhs,
                                                      unsigned depth) {
  ixs_node *left_zero;
  ixs_node *left_one;
  ixs_node *right_zero;
  ixs_node *right_one;

  if (lhs->u.assoc.nargs != 2u || rhs->u.assoc.nargs != 2u)
    return IXS_CHECK_UNKNOWN;
  left_zero = lhs->u.assoc.args[0];
  left_one = lhs->u.assoc.args[1];
  right_zero = rhs->u.assoc.args[0];
  right_one = rhs->u.assoc.args[1];

  /* Commit exact pairs first. The remaining child then has only one possible
   * partner, so this preserves deterministic matching without backtracking. */
  if (left_zero == right_zero)
    return equivalence_xor_child_proven(state, left_one, right_one, depth)
               ? IXS_CHECK_TRUE
               : IXS_CHECK_UNKNOWN;
  if (left_zero == right_one)
    return equivalence_xor_child_proven(state, left_one, right_zero, depth)
               ? IXS_CHECK_TRUE
               : IXS_CHECK_UNKNOWN;
  if (left_one == right_zero)
    return equivalence_xor_child_proven(state, left_zero, right_one, depth)
               ? IXS_CHECK_TRUE
               : IXS_CHECK_UNKNOWN;
  if (left_one == right_one)
    return equivalence_xor_child_proven(state, left_zero, right_zero, depth)
               ? IXS_CHECK_TRUE
               : IXS_CHECK_UNKNOWN;

  if (equivalence_xor_child_proven(state, left_zero, right_zero, depth) &&
      equivalence_xor_child_proven(state, left_one, right_one, depth))
    return IXS_CHECK_TRUE;
  if (state->limited || state->invalid || state->oom ||
      state->arithmetic_unrepresentable)
    return IXS_CHECK_UNKNOWN;
  return equivalence_xor_child_proven(state, left_zero, right_one, depth) &&
                 equivalence_xor_child_proven(state, left_one, right_zero,
                                              depth)
             ? IXS_CHECK_TRUE
             : IXS_CHECK_UNKNOWN;
}

static bool
equivalence_context_simplify_pair(equivalence_state *state,
                                  const equivalence_context_pair *pair,
                                  ixs_node **lhs, ixs_node **rhs) {
  bool lhs_limited = false;
  bool rhs_limited = false;

  *lhs = simp_simplify_bounds_status(state->ctx, pair->lhs, state->bounds,
                                     &lhs_limited);
  *rhs = simp_simplify_bounds_status(state->ctx, pair->rhs, state->bounds,
                                     &rhs_limited);
  if (lhs_limited || rhs_limited) {
    state->limited = true;
    return false;
  }
  if (!*lhs || !*rhs) {
    state->oom = true;
    return false;
  }
  if (ixs_node_is_sentinel(*lhs) || ixs_node_is_sentinel(*rhs)) {
    state->invalid = true;
    return false;
  }
  return true;
}

static bool
equivalence_context_enqueue_children(equivalence_state *state,
                                     equivalence_context_worklist *worklist,
                                     ixs_node *lhs, ixs_node *rhs) {
  uint32_t child_count;
  uint32_t i;

  if (!equivalence_context_shape(lhs, rhs, &child_count))
    return false;
  for (i = 0; i < child_count; i++)
    if (!equivalence_context_enqueue(state, worklist, defined_child_at(lhs, i),
                                     defined_child_at(rhs, i)))
      return false;
  return true;
}

static bool equivalence_context_process_pair(
    equivalence_state *state, equivalence_context_worklist *worklist,
    const equivalence_context_pair *pair, unsigned depth) {
  ixs_node *simplified_lhs;
  ixs_node *simplified_rhs;
  ixs_node *lhs_residual;
  ixs_node *rhs_residual;
  ixs_check_result result;

  if (!equivalence_context_simplify_pair(state, pair, &simplified_lhs,
                                         &simplified_rhs))
    return false;
  if (simplified_lhs == simplified_rhs)
    return true;

  result = equivalence_core_impl(state, simplified_lhs, simplified_rhs, depth,
                                 false);
  if (result == IXS_CHECK_TRUE)
    return true;
  if (state->limited || state->invalid || state->oom ||
      state->arithmetic_unrepresentable)
    return false;
  if (simplified_lhs->tag == IXS_XOR && simplified_rhs->tag == IXS_XOR &&
      simplified_lhs->u.assoc.nargs == 2u &&
      simplified_rhs->u.assoc.nargs == 2u)
    return equivalence_match_xor_context(state, simplified_lhs, simplified_rhs,
                                         depth) == IXS_CHECK_TRUE;

  if (equivalence_cancel_common_add(state, simplified_lhs, simplified_rhs,
                                    &lhs_residual, &rhs_residual))
    return equivalence_context_enqueue(state, worklist, lhs_residual,
                                       rhs_residual);
  if (state->oom)
    return false;
  return equivalence_context_enqueue_children(state, worklist, simplified_lhs,
                                              simplified_rhs);
}

/* Worklist insertion and lookup are expected O(N) in the paired canonical DAG.
 * Existing child proofs keep their own bounds; XOR may add O(A^2) bounded
 * child proofs after exact argument pairing. */
static ixs_check_result equivalence_same_context(equivalence_state *state,
                                                 ixs_node *lhs, ixs_node *rhs,
                                                 unsigned depth) {
  equivalence_context_worklist worklist;
  uint32_t child_count;
  bool xor_shape = lhs->tag == IXS_XOR && rhs->tag == IXS_XOR &&
                   lhs->u.assoc.nargs == 2u && rhs->u.assoc.nargs == 2u;
  bool round_shape = state->xor_context_subproof_depth != 0u &&
                     lhs->tag == rhs->tag &&
                     (lhs->tag == IXS_FLOOR || lhs->tag == IXS_CEIL);
  bool grouped_shape = equivalence_grouped_add_context(lhs) &&
                       equivalence_grouped_add_context(rhs);

  memset(&worklist, 0, sizeof(worklist));
  if ((!xor_shape && !round_shape && !grouped_shape) ||
      (!xor_shape && !equivalence_context_shape(lhs, rhs, &child_count)) ||
      !equivalence_context_enqueue(state, &worklist, lhs, rhs))
    return IXS_CHECK_UNKNOWN;

  while (worklist.count > 0u) {
    equivalence_context_pair pair = worklist.pairs[--worklist.count];
    if (!equivalence_context_process_pair(state, &worklist, &pair, depth))
      return IXS_CHECK_UNKNOWN;
  }
  return IXS_CHECK_TRUE;
}

/* Optional algebraic proof rules must not turn a valid query into a session
 * diagnostic merely because an intermediate rational cannot be represented.
 * Build their small linear intermediates directly from canonical nodes:
 * overflow is a rule miss and allocation failure remains OOM. */
typedef enum {
  EQUIVALENCE_BUILD_OK,
  EQUIVALENCE_BUILD_NO_MATCH,
  EQUIVALENCE_BUILD_OOM
} equivalence_build_status;

static ixs_node *equivalence_build_const(ixs_ctx *ctx, int64_t p, int64_t q) {
  return q == 1 ? ixs_node_int(ctx, p) : ixs_node_rat(ctx, p, q);
}

static equivalence_build_status
equivalence_build_scale_rat(equivalence_state *state, ixs_node *expr,
                            int64_t scale_p, int64_t scale_q,
                            ixs_node **result) {
  ixs_node *coefficient;
  bool unrepresentable = false;

  *result = NULL;
  if (!expr || ixs_node_is_sentinel(expr) || scale_q <= 0)
    return EQUIVALENCE_BUILD_NO_MATCH;
  coefficient = equivalence_build_const(state->ctx, scale_p, scale_q);
  if (!coefficient) {
    state->oom = true;
    return EQUIVALENCE_BUILD_OOM;
  }
  *result = simp_try_mul(state->ctx, coefficient, expr, &unrepresentable);
  if (unrepresentable) {
    state->arithmetic_unrepresentable = true;
    return EQUIVALENCE_BUILD_NO_MATCH;
  }
  if (!*result) {
    state->oom = true;
    return EQUIVALENCE_BUILD_OOM;
  }
  return EQUIVALENCE_BUILD_OK;
}

static equivalence_build_status equivalence_build_add(equivalence_state *state,
                                                      ixs_node *lhs,
                                                      ixs_node *rhs,
                                                      ixs_node **result) {
  bool unrepresentable = false;
  *result = simp_try_add(state->ctx, lhs, rhs, &unrepresentable);
  if (unrepresentable) {
    state->arithmetic_unrepresentable = true;
    return EQUIVALENCE_BUILD_NO_MATCH;
  }
  if (!*result) {
    state->oom = true;
    return EQUIVALENCE_BUILD_OOM;
  }
  return EQUIVALENCE_BUILD_OK;
}

static equivalence_build_status equivalence_build_neg(equivalence_state *state,
                                                      ixs_node *expr,
                                                      ixs_node **result) {
  equivalence_build_status status =
      equivalence_build_scale_rat(state, expr, -1, 1, result);
  if (status == EQUIVALENCE_BUILD_OOM)
    state->oom = true;
  return status;
}

static equivalence_build_status equivalence_build_sub(equivalence_state *state,
                                                      ixs_node *lhs,
                                                      ixs_node *rhs,
                                                      ixs_node **result) {
  ixs_node *negative;
  equivalence_build_status status =
      equivalence_build_neg(state, rhs, &negative);
  if (status != EQUIVALENCE_BUILD_OK)
    return status;
  return equivalence_build_add(state, lhs, negative, result);
}

static ixs_check_result equivalence_difference(equivalence_state *state,
                                               ixs_node *lhs, ixs_node *rhs) {
  struct ixs_node_impl nonzero;
  ixs_node *difference;
  ixs_check_result nonzero_result;
  int64_t delta;
  bool proved;
  if (equivalence_build_sub(state, lhs, rhs, &difference) !=
      EQUIVALENCE_BUILD_OK)
    return IXS_CHECK_UNKNOWN;
  proved = bounds_constant_delta_query(state->ctx, state->bounds, lhs, rhs,
                                       false, &delta);
  if (state->bounds->oom) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (proved)
    return delta == 0 ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;

  /* A variable difference need not be constant to prove that the two
   * expressions never agree.  Reuse the ordinary range, bit, and congruence
   * query for the canonical difference instead of teaching equivalence those
   * domains again. */
  if (ixs_node_is_sentinel(difference))
    return IXS_CHECK_UNKNOWN;
  memset(&nonzero, 0, sizeof(nonzero));
  nonzero.tag = IXS_CMP;
  nonzero.u.binary.lhs = difference;
  nonzero.u.binary.rhs = state->ctx->node_zero;
  nonzero.u.binary.cmp_op = IXS_CMP_NE;
  nonzero_result = ixs_bounds_check(state->bounds, &nonzero);
  if (state->bounds->oom) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (nonzero_result == IXS_CHECK_TRUE)
    return IXS_CHECK_FALSE;

  /* Integer equality is also bitwise equality.  Canonical xor cancels shared
   * subexpressions that an arithmetic difference deliberately preserves. */
  if (ixs_bounds_check_integer_valued(state->bounds, lhs) == IXS_CHECK_TRUE &&
      ixs_bounds_check_integer_valued(state->bounds, rhs) == IXS_CHECK_TRUE) {
    ixs_node *bit_difference = simp_xor(state->ctx, lhs, rhs);
    if (!bit_difference) {
      state->oom = true;
      return IXS_CHECK_UNKNOWN;
    }
    if (!ixs_node_is_sentinel(bit_difference)) {
      if (ixs_node_is_zero(bit_difference))
        return IXS_CHECK_TRUE;
      nonzero.u.binary.lhs = bit_difference;
      nonzero_result = ixs_bounds_check(state->bounds, &nonzero);
      if (state->bounds->oom) {
        state->oom = true;
        return IXS_CHECK_UNKNOWN;
      }
      if (nonzero_result == IXS_CHECK_TRUE)
        return IXS_CHECK_FALSE;
    }
  }
  return IXS_CHECK_UNKNOWN;
}

static bool equivalence_integer_delta(equivalence_state *state, ixs_node *lhs,
                                      ixs_node *rhs, int64_t *delta) {
  bool proved = bounds_constant_delta_query(state->ctx, state->bounds, lhs, rhs,
                                            true, delta);
  if (state->bounds->oom)
    state->oom = true;
  return proved && !state->oom;
}

typedef struct {
  uint64_t magnitude;
  bool negative;
} bounds_wide_integer;

static bounds_wide_integer bounds_wide_integer_from_int64(int64_t value) {
  bounds_wide_integer result;
  result.magnitude = ixs_int64_magnitude(value);
  result.negative = value < 0;
  return result;
}

static bounds_wide_integer
bounds_wide_integer_negate(bounds_wide_integer value) {
  if (value.magnitude != 0)
    value.negative = !value.negative;
  return value;
}

static bool bounds_wide_integer_add(bounds_wide_integer lhs,
                                    bounds_wide_integer rhs,
                                    bounds_wide_integer *result) {
  if (lhs.negative == rhs.negative) {
    if (lhs.magnitude > UINT64_MAX - rhs.magnitude)
      return false;
    result->magnitude = lhs.magnitude + rhs.magnitude;
    result->negative = lhs.negative;
  } else if (lhs.magnitude >= rhs.magnitude) {
    result->magnitude = lhs.magnitude - rhs.magnitude;
    result->negative = lhs.negative;
  } else {
    result->magnitude = rhs.magnitude - lhs.magnitude;
    result->negative = rhs.negative;
  }
  if (result->magnitude == 0)
    result->negative = false;
  return true;
}

static bool bounds_wide_integer_difference(int64_t lhs, int64_t rhs,
                                           bounds_wide_integer *result) {
  return bounds_wide_integer_add(
      bounds_wide_integer_from_int64(lhs),
      bounds_wide_integer_negate(bounds_wide_integer_from_int64(rhs)), result);
}

static int bounds_wide_integer_compare(bounds_wide_integer lhs,
                                       bounds_wide_integer rhs) {
  if (lhs.negative != rhs.negative)
    return lhs.negative ? -1 : 1;
  if (lhs.magnitude == rhs.magnitude)
    return 0;
  if (lhs.negative)
    return lhs.magnitude > rhs.magnitude ? -1 : 1;
  return lhs.magnitude < rhs.magnitude ? -1 : 1;
}

static bool bounds_wide_integer_to_int64(bounds_wide_integer value,
                                         int64_t *result) {
  uint64_t negative_limit = (uint64_t)INT64_MAX + 1u;
  if (!value.negative) {
    if (value.magnitude > (uint64_t)INT64_MAX)
      return false;
    *result = (int64_t)value.magnitude;
    return true;
  }
  if (value.magnitude > negative_limit)
    return false;
  if (value.magnitude == negative_limit) {
    *result = INT64_MIN;
    return true;
  }
  *result = -(int64_t)value.magnitude;
  return true;
}

static uint64_t bounds_wide_integer_residue(bounds_wide_integer value,
                                            uint64_t modulus) {
  uint64_t residue = value.magnitude % modulus;
  if (value.negative && residue != 0)
    residue = modulus - residue;
  return residue;
}

static bool bounds_integer_enclosure(ixs_bounds *bounds, ixs_node *expr,
                                     int64_t *lower, int64_t *upper) {
  ixs_interval interval;

  if (!bounds || !expr || bounds->oom || ixs_bounds_has_empty(bounds) ||
      ixs_bounds_check_defined(bounds, expr) != IXS_CHECK_TRUE ||
      ixs_bounds_check_integer_valued(bounds, expr) != IXS_CHECK_TRUE)
    return false;
  interval = ixs_bounds_get(bounds, expr);
  if (!bounds_refine_integral_interval(
          bounds, expr, /*expression_defined=*/true, &interval) ||
      interval.lo_inf || interval.hi_inf)
    return false;
  *lower = interval.lo_p;
  *upper = interval.hi_p;
  return true;
}

/* Each Mod result preserves its dividend modulo the positive literal divisor.
 * Independent finite ranges enclose every possible result difference. Exactly
 * one member of the required residue class makes that difference exact. */
static bool bounds_unique_modular_delta(ixs_bounds *bounds, ixs_node *lhs,
                                        ixs_node *rhs,
                                        int64_t representative_delta,
                                        int64_t modulus, int64_t *delta) {
  bounds_wide_integer lower;
  bounds_wide_integer upper;
  bounds_wide_integer candidate;
  bounds_wide_integer next;
  bounds_wide_integer shift;
  int64_t lhs_lower;
  int64_t lhs_upper;
  int64_t rhs_lower;
  int64_t rhs_upper;
  uint64_t current_residue;
  uint64_t expected_residue;
  uint64_t modulus_u = (uint64_t)modulus;
  uint64_t amount;

  if (modulus <= 1 ||
      !bounds_integer_enclosure(bounds, lhs, &lhs_lower, &lhs_upper) ||
      !bounds_integer_enclosure(bounds, rhs, &rhs_lower, &rhs_upper) ||
      !bounds_wide_integer_difference(lhs_lower, rhs_upper, &lower) ||
      !bounds_wide_integer_difference(lhs_upper, rhs_lower, &upper) ||
      bounds_wide_integer_compare(lower, upper) > 0)
    return false;

  expected_residue =
      (uint64_t)ixs_integer_congruence_residue(representative_delta, modulus);
  current_residue = bounds_wide_integer_residue(lower, modulus_u);
  amount = expected_residue >= current_residue
               ? expected_residue - current_residue
               : modulus_u - (current_residue - expected_residue);
  shift.magnitude = amount;
  shift.negative = false;
  if (!bounds_wide_integer_add(lower, shift, &candidate) ||
      bounds_wide_integer_compare(candidate, upper) > 0 ||
      !bounds_wide_integer_to_int64(candidate, delta))
    return false;

  shift.magnitude = modulus_u;
  if (bounds_wide_integer_add(candidate, shift, &next) &&
      bounds_wide_integer_compare(next, upper) <= 0)
    return false;
  return true;
}

static bool bounds_residue_shift_in_range(uint64_t residue, uint64_t modulus,
                                          int64_t shift) {
  uint64_t magnitude;
  if (shift >= 0) {
    uint64_t positive = (uint64_t)shift;
    return positive < modulus && residue < modulus - positive;
  }
  magnitude = ixs_int64_magnitude(shift);
  return magnitude <= residue;
}

/* If the dividend and positive divisor share a stride class, a shift which
 * stays within one stride bucket cannot cross a divisor boundary. */
static bool bounds_mod_shift_by_congruence(ixs_bounds *bounds,
                                           ixs_node *dividend,
                                           ixs_node *denominator,
                                           int64_t shift) {
  uint64_t modulus;
  uint64_t residue;
  if (!bounds_known_stride(bounds, dividend, &modulus) || modulus <= 1u ||
      modulus > (uint64_t)INT64_MAX ||
      !bounds_known_residue(bounds, dividend, modulus, &residue) ||
      ixs_bounds_check_divisible(bounds, denominator, (int64_t)modulus) !=
          IXS_CHECK_TRUE)
    return false;
  return bounds_residue_shift_in_range(residue, modulus, shift);
}

static bool bounds_denominator_proven_positive(ixs_bounds *bounds,
                                               ixs_node *denominator) {
  ixs_interval range = ixs_bounds_get(bounds, denominator);
  return range.valid && !range.lo_inf &&
         ixs_rat_cmp(range.lo_p, range.lo_q, 0, 1) > 0;
}

typedef enum {
  BOUNDS_DELTA_FRAME_INITIAL,
  BOUNDS_DELTA_FRAME_SEARCH,
  BOUNDS_DELTA_FRAME_REPRESENTATIVE,
  BOUNDS_DELTA_FRAME_RESIDUAL
} bounds_delta_frame_stage;

typedef struct {
  ixs_node *lhs;
  ixs_node *rhs;
  ixs_node *difference;
  uint32_t scan_positive;
  uint32_t scan_negative;
  uint32_t matched_positive;
  uint32_t matched_negative;
  int64_t modular_delta;
  bool allow_expand;
  bool tried_expand;
  bounds_delta_frame_stage stage;
} bounds_delta_frame;

typedef struct {
  ixs_ctx *ctx;
  ixs_bounds *bounds;
  bounds_delta_frame *frames;
  size_t depth;
  size_t capacity;
  bool child_proved;
  int64_t child_delta;
  bool frames_arena_owned;
  bool oom;
  bool invalid;
  bool limited;
} bounds_delta_query;

static bool bounds_delta_push(bounds_delta_query *query, ixs_node *lhs,
                              ixs_node *rhs, bool allow_expand) {
  bounds_delta_frame *frames;
  size_t capacity;
  size_t old_bytes;
  size_t new_bytes;
  if (query->depth == query->capacity) {
    capacity = query->capacity ? query->capacity : 4u;
    if (query->capacity) {
      if (capacity > SIZE_MAX / 2u)
        goto failed;
      capacity *= 2u;
    }
    if (query->capacity > SIZE_MAX / sizeof(*frames) ||
        capacity > SIZE_MAX / sizeof(*frames))
      goto failed;
    old_bytes = query->capacity * sizeof(*frames);
    new_bytes = capacity * sizeof(*frames);
    if (query->frames_arena_owned) {
      frames = ixs_arena_grow(query->bounds->scratch, query->frames, old_bytes,
                              new_bytes, sizeof(void *));
    } else {
      frames =
          ixs_arena_alloc(query->bounds->scratch, new_bytes, sizeof(void *));
      if (frames)
        memcpy(frames, query->frames, old_bytes);
    }
    if (!frames)
      goto failed;
    query->frames = frames;
    query->capacity = capacity;
    query->frames_arena_owned = true;
  }
  memset(&query->frames[query->depth], 0, sizeof(*query->frames));
  query->frames[query->depth].lhs = lhs;
  query->frames[query->depth].rhs = rhs;
  query->frames[query->depth].allow_expand = allow_expand;
  query->frames[query->depth].stage = BOUNDS_DELTA_FRAME_INITIAL;
  query->depth++;
  return true;

failed:
  query->bounds->oom = true;
  return false;
}

static void bounds_delta_complete(bounds_delta_query *query, bool proved,
                                  int64_t delta) {
  query->depth--;
  query->child_proved = proved;
  query->child_delta = proved ? delta : 0;
}

static ixs_node *bounds_delta_simplify(bounds_delta_query *query,
                                       ixs_node *expr) {
  if (!expr) {
    query->bounds->oom = true;
    return NULL;
  }
  if (ixs_node_is_sentinel(expr))
    return NULL;
  expr = simp_simplify_bounds(query->ctx, expr, query->bounds);
  if (!expr)
    query->bounds->oom = true;
  return expr && !ixs_node_is_sentinel(expr) ? expr : NULL;
}

static bool bounds_modular_pair(ixs_node *difference, uint32_t lhs_index,
                                uint32_t rhs_index, ixs_node **lhs_term,
                                ixs_node **rhs_term,
                                ixs_node **lhs_representative,
                                ixs_node **rhs_representative,
                                ixs_node **denominator, int64_t *coefficient) {
  int64_t lhs_p;
  int64_t lhs_q;
  int64_t rhs_p;
  int64_t rhs_q;
  int64_t opposite_rhs;
  ixs_node *lhs_denominator;
  ixs_node *rhs_denominator;

  *lhs_term = difference->u.add.terms[lhs_index].term;
  *rhs_term = difference->u.add.terms[rhs_index].term;
  ixs_node_get_rat(difference->u.add.terms[lhs_index].coeff, &lhs_p, &lhs_q);
  ixs_node_get_rat(difference->u.add.terms[rhs_index].coeff, &rhs_p, &rhs_q);
  if (lhs_q != 1 || rhs_q != 1 || lhs_p <= 0 || rhs_p >= 0 ||
      !ixs_safe_neg(rhs_p, &opposite_rhs) || lhs_p != opposite_rhs ||
      (*lhs_term)->tag != IXS_MOD || (*rhs_term)->tag != IXS_MOD)
    return false;
  *lhs_representative = (*lhs_term)->u.binary.lhs;
  *rhs_representative = (*rhs_term)->u.binary.lhs;
  lhs_denominator = (*lhs_term)->u.binary.rhs;
  rhs_denominator = (*rhs_term)->u.binary.rhs;
  if (lhs_denominator != rhs_denominator)
    return false;
  *denominator = lhs_denominator;
  *coefficient = lhs_p;
  return true;
}

static bool bounds_delta_next_modular_pair(bounds_delta_frame *frame) {
  uint32_t count = frame->difference->u.add.nterms;
  while (frame->scan_positive < count) {
    uint32_t positive = frame->scan_positive;
    int64_t p;
    int64_t q;
    ixs_node_get_rat(frame->difference->u.add.terms[positive].coeff, &p, &q);
    if (q != 1 || p <= 0 ||
        frame->difference->u.add.terms[positive].term->tag != IXS_MOD) {
      frame->scan_positive++;
      frame->scan_negative = 0;
      continue;
    }
    while (frame->scan_negative < count) {
      uint32_t negative = frame->scan_negative++;
      ixs_node *lhs_term;
      ixs_node *rhs_term;
      ixs_node *lhs_representative;
      ixs_node *rhs_representative;
      ixs_node *denominator;
      int64_t coefficient;
      if (!bounds_modular_pair(frame->difference, positive, negative, &lhs_term,
                               &rhs_term, &lhs_representative,
                               &rhs_representative, &denominator, &coefficient))
        continue;
      (void)lhs_term;
      (void)rhs_term;
      (void)lhs_representative;
      (void)rhs_representative;
      (void)denominator;
      frame->matched_positive = positive;
      frame->matched_negative = negative;
      (void)coefficient;
      return true;
    }
    frame->scan_positive++;
    frame->scan_negative = 0;
  }
  return false;
}

static bool bounds_modular_pair_valid(bounds_delta_query *query,
                                      ixs_node *lhs_term, ixs_node *rhs_term,
                                      ixs_node *lhs_representative,
                                      ixs_node *rhs_representative) {
  return ixs_bounds_check_defined(query->bounds, lhs_term) == IXS_CHECK_TRUE &&
         ixs_bounds_check_defined(query->bounds, rhs_term) == IXS_CHECK_TRUE &&
         ixs_bounds_check_defined(query->bounds, lhs_representative) ==
             IXS_CHECK_TRUE &&
         ixs_bounds_check_defined(query->bounds, rhs_representative) ==
             IXS_CHECK_TRUE &&
         ixs_bounds_check_integer_valued(query->bounds, lhs_term) ==
             IXS_CHECK_TRUE &&
         ixs_bounds_check_integer_valued(query->bounds, rhs_term) ==
             IXS_CHECK_TRUE &&
         ixs_bounds_check_integer_valued(query->bounds, lhs_representative) ==
             IXS_CHECK_TRUE &&
         ixs_bounds_check_integer_valued(query->bounds, rhs_representative) ==
             IXS_CHECK_TRUE;
}

static ixs_node *bounds_modular_delta_residual(bounds_delta_query *query,
                                               ixs_node *difference,
                                               uint32_t lhs_index,
                                               uint32_t rhs_index) {
  ixs_addterm *terms;
  uint32_t count = difference->u.add.nterms - 2u;
  uint32_t i;
  uint32_t write = 0;
  size_t bytes;
  if (count == 0)
    return difference->u.add.coeff;
  bytes = (size_t)count * sizeof(*terms);
  if (bytes / sizeof(*terms) != count) {
    query->bounds->oom = true;
    return NULL;
  }
  terms = ixs_arena_alloc(query->bounds->scratch, bytes, sizeof(void *));
  if (!terms) {
    query->bounds->oom = true;
    return NULL;
  }
  for (i = 0; i < difference->u.add.nterms; i++) {
    if (i != lhs_index && i != rhs_index)
      terms[write++] = difference->u.add.terms[i];
  }
  if (count == 1u) {
    ixs_node *result = simp_mul(query->ctx, terms[0].coeff, terms[0].term);
    if (!result) {
      query->bounds->oom = true;
      return NULL;
    }
    if (ixs_node_is_sentinel(result))
      return NULL;
    if (ixs_node_is_zero(difference->u.add.coeff))
      return result;
    result = simp_add(query->ctx, difference->u.add.coeff, result);
    if (!result)
      query->bounds->oom = true;
    return result && !ixs_node_is_sentinel(result) ? result : NULL;
  }
  {
    ixs_node *result =
        ixs_node_add(query->ctx, difference->u.add.coeff, count, terms);
    if (!result)
      query->bounds->oom = true;
    return result;
  }
}

static bool bounds_delta_prepare_difference(bounds_delta_query *query,
                                            bounds_delta_frame *frame,
                                            ixs_node *difference) {
  int64_t delta;
  frame->difference = difference;
  frame->scan_positive = 0;
  frame->scan_negative = 0;
  if (bounds_range_exact_integer_difference(query->bounds, difference,
                                            &delta)) {
    bounds_delta_complete(query, true, delta);
    return true;
  }
  if (difference->tag != IXS_ADD || difference->u.add.nterms < 2u)
    return false;
  frame->stage = BOUNDS_DELTA_FRAME_SEARCH;
  return true;
}

static bool bounds_delta_try_expanded(bounds_delta_query *query,
                                      bounds_delta_frame *frame) {
  ixs_node *expanded;
  if (!frame->allow_expand || frame->tried_expand)
    return false;
  frame->tried_expand = true;
  expanded =
      bounds_delta_simplify(query, expand_impl(query->ctx, frame->difference));
  if (!expanded || expanded == frame->difference)
    return false;
  return bounds_delta_prepare_difference(query, frame, expanded);
}

static void bounds_delta_step_initial(bounds_delta_query *query,
                                      size_t frame_index) {
  bounds_delta_frame *frame = &query->frames[frame_index];
  ixs_algebra_status relation_status;
  int64_t relation_delta;
  ixs_node *difference;
  bool lhs_oom = false;
  bool rhs_oom = false;
  bool lhs_limited = false;
  bool rhs_limited = false;
  if (bounds_defined_check_detail(query->bounds, frame->lhs, &lhs_oom,
                                  &lhs_limited) != IXS_CHECK_TRUE ||
      bounds_defined_check_detail(query->bounds, frame->rhs, &rhs_oom,
                                  &rhs_limited) != IXS_CHECK_TRUE) {
    query->oom = lhs_oom || rhs_oom;
    query->limited = lhs_limited || rhs_limited;
    if (query->oom || query->limited)
      return;
    bounds_delta_complete(query, false, 0);
    return;
  }
  if (frame->lhs == frame->rhs) {
    bounds_delta_complete(query, true, 0);
    return;
  }
  relation_status = bounds_exact_relation_difference(
      query->bounds, frame->lhs, frame->rhs, &relation_delta);
  if (relation_status == IXS_ALGEBRA_MATCH) {
    bounds_delta_complete(query, true, relation_delta);
    return;
  }
  if (relation_status == IXS_ALGEBRA_OOM) {
    query->oom = true;
    return;
  }
  if (relation_status == IXS_ALGEBRA_LIMITED) {
    query->limited = true;
    return;
  }
  if (relation_status == IXS_ALGEBRA_INVALID) {
    query->invalid = true;
    bounds_delta_complete(query, false, 0);
    return;
  }
  difference = bounds_delta_simplify(
      query, simp_sub(query->ctx, frame->lhs, frame->rhs));
  if (!difference) {
    if (!query->bounds->oom)
      bounds_delta_complete(query, false, 0);
    return;
  }
  if (!bounds_delta_prepare_difference(query, frame, difference) &&
      !bounds_delta_try_expanded(query, frame))
    bounds_delta_complete(query, false, 0);
}

static void bounds_delta_step_search(bounds_delta_query *query,
                                     size_t frame_index) {
  bounds_delta_frame *frame = &query->frames[frame_index];
  ixs_node *lhs_term;
  ixs_node *rhs_term;
  ixs_node *lhs_representative;
  ixs_node *rhs_representative;
  ixs_node *denominator;
  int64_t coefficient;
  if (!bounds_delta_next_modular_pair(frame)) {
    if (!bounds_delta_try_expanded(query, frame))
      bounds_delta_complete(query, false, 0);
    return;
  }
  if (!bounds_modular_pair(frame->difference, frame->matched_positive,
                           frame->matched_negative, &lhs_term, &rhs_term,
                           &lhs_representative, &rhs_representative,
                           &denominator, &coefficient) ||
      !bounds_modular_pair_valid(query, lhs_term, rhs_term, lhs_representative,
                                 rhs_representative))
    return;
  (void)denominator;
  (void)coefficient;
  frame->stage = BOUNDS_DELTA_FRAME_REPRESENTATIVE;
  (void)bounds_delta_push(query, lhs_representative, rhs_representative,
                          frame->allow_expand);
}

static bool bounds_delta_project_mod_pair(bounds_delta_query *query,
                                          bounds_delta_frame *frame,
                                          int64_t *scaled_delta) {
  ixs_node *lhs_term;
  ixs_node *rhs_term;
  ixs_node *lhs_representative;
  ixs_node *rhs_representative;
  ixs_node *denominator;
  int64_t coefficient;
  int64_t modular_delta;
  if (!query->child_proved ||
      !bounds_modular_pair(frame->difference, frame->matched_positive,
                           frame->matched_negative, &lhs_term, &rhs_term,
                           &lhs_representative, &rhs_representative,
                           &denominator, &coefficient))
    return false;
  if (denominator->tag == IXS_INT) {
    if (!bounds_unique_modular_delta(query->bounds, lhs_term, rhs_term,
                                     query->child_delta, denominator->u.ival,
                                     &modular_delta))
      return false;
  } else {
    if (!bounds_denominator_proven_positive(query->bounds, denominator) ||
        !bounds_mod_shift_by_congruence(query->bounds, rhs_representative,
                                        denominator, query->child_delta))
      return false;
    modular_delta = query->child_delta;
  }
  return ixs_safe_mul(modular_delta, coefficient, scaled_delta);
}

static void bounds_delta_step_representative(bounds_delta_query *query,
                                             size_t frame_index) {
  bounds_delta_frame *frame = &query->frames[frame_index];
  ixs_node *residual;
  if (!bounds_delta_project_mod_pair(query, frame, &frame->modular_delta)) {
    frame->stage = BOUNDS_DELTA_FRAME_SEARCH;
    return;
  }
  residual = bounds_modular_delta_residual(query, frame->difference,
                                           frame->matched_positive,
                                           frame->matched_negative);
  if (!residual) {
    if (!query->bounds->oom)
      frame->stage = BOUNDS_DELTA_FRAME_SEARCH;
    return;
  }
  frame->stage = BOUNDS_DELTA_FRAME_RESIDUAL;
  (void)bounds_delta_push(query, residual, query->ctx->node_zero,
                          frame->allow_expand);
}

static void bounds_delta_step_residual(bounds_delta_query *query,
                                       size_t frame_index) {
  bounds_delta_frame *frame = &query->frames[frame_index];
  int64_t result;
  if (query->child_proved &&
      ixs_safe_add(frame->modular_delta, query->child_delta, &result)) {
    bounds_delta_complete(query, true, result);
  } else {
    frame->stage = BOUNDS_DELTA_FRAME_SEARCH;
  }
}

/* This is an explicit proof stack, not a bounded recursive search. Every child
 * either enters a Mod dividend or removes a matched Mod pair from a canonical
 * ADD. Work is therefore finite in the queried expression DAG; stack growth
 * is geometric and allocation failure returns unknown. */
static bool bounds_delta_query_start(bounds_delta_query *query,
                                     bounds_delta_frame *initial_frame,
                                     ixs_ctx *ctx, ixs_bounds *bounds,
                                     ixs_node *lhs, ixs_node *rhs,
                                     bool allow_expand) {
  memset(query, 0, sizeof(*query));
  query->ctx = ctx;
  query->bounds = bounds;
  query->frames = initial_frame;
  query->capacity = 1u;
  return ctx && bounds && lhs && rhs && !bounds->oom &&
         !bounds->contradiction &&
         bounds_delta_push(query, lhs, rhs, allow_expand);
}

static void bounds_delta_query_run(bounds_delta_query *query) {
  while (query->depth != 0 && !query->bounds->oom && !query->oom &&
         !query->invalid && !query->limited) {
    size_t frame_index = query->depth - 1u;
    switch (query->frames[frame_index].stage) {
    case BOUNDS_DELTA_FRAME_INITIAL:
      bounds_delta_step_initial(query, frame_index);
      break;
    case BOUNDS_DELTA_FRAME_SEARCH:
      bounds_delta_step_search(query, frame_index);
      break;
    case BOUNDS_DELTA_FRAME_REPRESENTATIVE:
      bounds_delta_step_representative(query, frame_index);
      break;
    case BOUNDS_DELTA_FRAME_RESIDUAL:
      bounds_delta_step_residual(query, frame_index);
      break;
    }
  }
}

static bool bounds_delta_query_result(const bounds_delta_query *query,
                                      int64_t *delta, bool *invalid,
                                      bool *limited, bool *oom) {
  if (invalid)
    *invalid = query->invalid;
  if (limited)
    *limited = query->limited;
  if (oom)
    *oom = query->oom;
  if (query->bounds->oom || query->oom || query->invalid || query->limited ||
      query->depth != 0 || !query->child_proved)
    return false;
  *delta = query->child_delta;
  return true;
}

static bool bounds_constant_delta_query_detail(ixs_ctx *ctx, ixs_bounds *bounds,
                                               ixs_node *lhs, ixs_node *rhs,
                                               bool allow_expand,
                                               int64_t *delta, bool *invalid,
                                               bool *limited, bool *oom) {
  bounds_delta_query query;
  bounds_delta_frame initial_frame;
  if (invalid)
    *invalid = false;
  if (limited)
    *limited = false;
  if (oom)
    *oom = false;
  if (!delta || !bounds_delta_query_start(&query, &initial_frame, ctx, bounds,
                                          lhs, rhs, allow_expand))
    return false;
  bounds_delta_query_run(&query);
  return bounds_delta_query_result(&query, delta, invalid, limited, oom);
}

static bool bounds_constant_delta_query(ixs_ctx *ctx, ixs_bounds *bounds,
                                        ixs_node *lhs, ixs_node *rhs,
                                        bool allow_expand, int64_t *delta) {
  return bounds_constant_delta_query_detail(ctx, bounds, lhs, rhs, allow_expand,
                                            delta, NULL, NULL, NULL);
}

static bool equivalence_no_reachable_integer(equivalence_state *state,
                                             ixs_node *expr, int64_t lo,
                                             int64_t hi) {
  ixs_interval region;
  ixs_interval known;
  uint64_t stride;
  uint64_t residue;
  if (lo > hi)
    return true;
  region = ixs_interval_range(lo, 1, hi, 1);
  known = ixs_bounds_get(state->bounds, expr);
  if (state->bounds->oom) {
    state->oom = true;
    return false;
  }
  if (known.valid) {
    region = iv_intersect(region, known);
    if (!region.valid)
      return true;
  }
  if (!bounds_known_stride(state->bounds, expr, &stride) || stride <= 1u ||
      stride > (uint64_t)INT64_MAX ||
      !bounds_known_residue(state->bounds, expr, stride, &residue)) {
    if (state->bounds->oom)
      state->oom = true;
    return false;
  }
  return !ixs_interval_has_congruent_integer(&region, (int64_t)stride,
                                             (int64_t)residue);
}

static bool equivalence_ordered_cut(ixs_cmp_op op, bool *lower,
                                    int64_t *threshold) {
  switch (op) {
  case IXS_CMP_LT:
    *lower = false;
    *threshold = -1;
    return true;
  case IXS_CMP_LE:
    *lower = false;
    *threshold = 0;
    return true;
  case IXS_CMP_GT:
    *lower = true;
    *threshold = 1;
    return true;
  case IXS_CMP_GE:
    *lower = true;
    *threshold = 0;
    return true;
  default:
    return false;
  }
}

typedef struct {
  int64_t *slots;
  size_t capacity;
  size_t count;
} equivalence_modulus_set;

static size_t equivalence_modulus_hash(int64_t modulus) {
  uint64_t x = (uint64_t)modulus;
  x ^= x >> 33;
  x *= UINT64_C(0xff51afd7ed558ccd);
  x ^= x >> 33;
  return (size_t)x;
}

/* Rehashing is amortized O(1), and storage grows only with distinct moduli in
 * the two queried expression DAGs. */
static bool equivalence_modulus_set_grow(ixs_arena *arena,
                                         equivalence_modulus_set *set) {
  size_t new_capacity = set->capacity ? set->capacity * 2u : 8u;
  int64_t *slots;
  size_t i;
  if (new_capacity <= set->capacity || new_capacity > SIZE_MAX / sizeof(*slots))
    return false;
  slots = ixs_arena_alloc(arena, new_capacity * sizeof(*slots), sizeof(void *));
  if (!slots)
    return false;
  memset(slots, 0, new_capacity * sizeof(*slots));
  for (i = 0; i < set->capacity; i++) {
    if (set->slots[i] != 0) {
      size_t index =
          equivalence_modulus_hash(set->slots[i]) & (new_capacity - 1u);
      while (slots[index] != 0)
        index = (index + 1u) & (new_capacity - 1u);
      slots[index] = set->slots[i];
    }
  }
  set->slots = slots;
  set->capacity = new_capacity;
  return true;
}

static bool equivalence_modulus_set_insert(ixs_arena *arena,
                                           equivalence_modulus_set *set,
                                           int64_t modulus) {
  size_t index;
  if (modulus <= 1)
    return true;
  if (!set->capacity || set->count >= set->capacity / 2u) {
    if (!equivalence_modulus_set_grow(arena, set))
      return false;
  }
  index = equivalence_modulus_hash(modulus) & (set->capacity - 1u);
  while (set->slots[index] != 0 && set->slots[index] != modulus)
    index = (index + 1u) & (set->capacity - 1u);
  if (set->slots[index] == modulus)
    return true;
  set->slots[index] = modulus;
  set->count++;
  return true;
}

/* Discover congruence candidates by visiting each node in the two queried
 * residual DAGs once. Growable query-local storage avoids semantic depth,
 * visit, and candidate-count cutoffs without scanning unrelated context state.
 */
static bool equivalence_collect_congruences(equivalence_state *state,
                                            ixs_node *lhs, ixs_node *rhs,
                                            equivalence_modulus_set *moduli) {
  query_node_set visited;
  ixs_node **stack = NULL;
  size_t stack_capacity = 0;
  size_t stack_count = 0;

  memset(&visited, 0, sizeof(visited));
  if (!query_node_stack_push(&state->ctx->scratch, &stack, &stack_count,
                             &stack_capacity, lhs) ||
      !query_node_stack_push(&state->ctx->scratch, &stack, &stack_count,
                             &stack_capacity, rhs))
    goto oom;
  while (stack_count > 0) {
    ixs_node *node = stack[--stack_count];
    uint32_t child_count;
    uint32_t i;
    bool inserted;
    if (!query_node_set_insert(&state->ctx->scratch, &visited, node, &inserted))
      goto oom;
    if (!inserted)
      continue;
    if (node->tag == IXS_SYM) {
      int64_t modulus;
      int64_t remainder;
      bool known = bounds_store_get_modrem(state->bounds, node->u.name,
                                           &modulus, &remainder);
      if (state->bounds->oom)
        goto oom;
      if (known && !equivalence_modulus_set_insert(&state->ctx->scratch, moduli,
                                                   modulus))
        goto oom;
      (void)remainder;
    }
    child_count = ixs_node_nchildren(node);
    for (i = 0; i < child_count; i++) {
      if (!query_node_stack_push(&state->ctx->scratch, &stack, &stack_count,
                                 &stack_capacity, ixs_node_child(node, i)))
        goto oom;
    }
  }
  return true;

oom:
  state->oom = true;
  return false;
}

static ixs_node *equivalence_build_rounded_ordered(equivalence_state *state,
                                                   ixs_node *cmp,
                                                   int64_t divisor) {
  ixs_node *scale = ixs_node_int(state->ctx, divisor);
  ixs_node *quotient;
  ixs_node *rounded;
  if (!scale)
    return NULL;
  quotient = simp_div(state->ctx, cmp->u.binary.lhs, scale);
  if (!quotient)
    return NULL;
  switch (cmp->u.binary.cmp_op) {
  case IXS_CMP_LT:
  case IXS_CMP_GE:
    rounded = simp_floor(state->ctx, quotient);
    break;
  case IXS_CMP_LE:
  case IXS_CMP_GT:
    rounded = simp_ceil(state->ctx, quotient);
    break;
  default:
    return cmp;
  }
  if (!rounded)
    return NULL;
  return simp_cmp(state->ctx, rounded, cmp->u.binary.cmp_op,
                  state->ctx->node_zero);
}

static ixs_check_result
equivalence_ordered_congruence_forms(equivalence_state *state, ixs_node *lhs,
                                     ixs_node *rhs) {
  ixs_arena_mark mark = ixs_arena_save(&state->ctx->scratch);
  equivalence_modulus_set moduli;
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  size_t i;

  memset(&moduli, 0, sizeof(moduli));
  if (state->oom || state->limited ||
      !equivalence_collect_congruences(state, lhs->u.binary.lhs,
                                       rhs->u.binary.lhs, &moduli))
    goto cleanup;
  for (i = 0; i < moduli.capacity; i++) {
    ixs_node *normalized[2];
    if (moduli.slots[i] == 0)
      continue;
    normalized[0] =
        equivalence_build_rounded_ordered(state, lhs, moduli.slots[i]);
    normalized[1] =
        equivalence_build_rounded_ordered(state, rhs, moduli.slots[i]);
    if (!normalized[0] || !normalized[1] ||
        !simp_simplify_batch_bounds(state->ctx, normalized, 2, state->bounds) ||
        state->bounds->oom) {
      state->oom = true;
      goto cleanup;
    }
    if (!ixs_node_is_sentinel(normalized[0]) &&
        !ixs_node_is_sentinel(normalized[1]) &&
        normalized[0] == normalized[1]) {
      result = IXS_CHECK_TRUE;
      goto cleanup;
    }
  }

cleanup:
  ixs_arena_restore(&state->ctx->scratch, mark);
  return result;
}

static ixs_check_result
equivalence_ordered_comparisons(equivalence_state *state, ixs_node *lhs,
                                ixs_node *rhs) {
  bool left_lower, right_lower;
  int64_t left_threshold, right_threshold, delta, mapped_threshold;
  int64_t lo, hi;
  if (!lhs || !rhs || lhs->tag != IXS_CMP || rhs->tag != IXS_CMP ||
      !ixs_node_is_zero(lhs->u.binary.rhs) ||
      !ixs_node_is_zero(rhs->u.binary.rhs) ||
      !equivalence_ordered_cut(lhs->u.binary.cmp_op, &left_lower,
                               &left_threshold) ||
      !equivalence_ordered_cut(rhs->u.binary.cmp_op, &right_lower,
                               &right_threshold) ||
      left_lower != right_lower ||
      ixs_bounds_check_integer_valued(state->bounds, lhs->u.binary.lhs) !=
          IXS_CHECK_TRUE ||
      ixs_bounds_check_integer_valued(state->bounds, rhs->u.binary.lhs) !=
          IXS_CHECK_TRUE)
    return IXS_CHECK_UNKNOWN;
  if (equivalence_integer_delta(state, lhs->u.binary.lhs, rhs->u.binary.lhs,
                                &delta) &&
      ixs_safe_add(right_threshold, delta, &mapped_threshold)) {
    bool cut_valid;
    if (left_threshold == mapped_threshold)
      return IXS_CHECK_TRUE;
    lo = left_threshold < mapped_threshold ? left_threshold : mapped_threshold;
    hi = left_threshold < mapped_threshold ? mapped_threshold : left_threshold;
    cut_valid =
        left_lower ? ixs_safe_sub(hi, 1, &hi) : ixs_safe_add(lo, 1, &lo);
    if (cut_valid &&
        equivalence_no_reachable_integer(state, lhs->u.binary.lhs, lo, hi))
      return IXS_CHECK_TRUE;
  }
  return equivalence_ordered_congruence_forms(state, lhs, rhs);
}

static void equivalence_note_algebra_status(equivalence_state *state,
                                            ixs_algebra_status status) {
  if (status == IXS_ALGEBRA_UNREPRESENTABLE)
    state->arithmetic_unrepresentable = true;
  else if (status == IXS_ALGEBRA_LIMITED)
    state->limited = true;
  else if (status == IXS_ALGEBRA_INVALID)
    state->invalid = true;
  else if (status == IXS_ALGEBRA_OOM)
    state->oom = true;
}

static bool equivalence_remainder_integer_proven(equivalence_state *state,
                                                 ixs_node *node) {
  bool proven =
      ixs_bounds_check_integer_valued(state->bounds, node) == IXS_CHECK_TRUE;
  if (state->bounds->oom)
    state->oom = true;
  return proven;
}

static bool equivalence_split_affine_round(equivalence_state *state,
                                           ixs_node *value, bool ceiling,
                                           ixs_node **argument,
                                           ixs_node **residual) {
  ixs_algebra_status status = ixs_additive_row_split_round(
      state->ctx, value, ceiling, argument, residual);
  equivalence_note_algebra_status(state, status);
  return status == IXS_ALGEBRA_MATCH;
}

static ixs_check_result
equivalence_affine_round_context(equivalence_state *state, ixs_node *lhs,
                                 ixs_node *rhs, unsigned depth) {
  size_t i;

  for (i = 0; i < 2u; i++) {
    ixs_node *lhs_argument;
    ixs_node *lhs_residual;
    ixs_node *rhs_argument;
    ixs_node *rhs_residual;
    ixs_node *lhs_shifted;
    ixs_node *rhs_shifted;

    if (!equivalence_split_affine_round(state, lhs, i != 0u, &lhs_argument,
                                        &lhs_residual) ||
        !equivalence_split_affine_round(state, rhs, i != 0u, &rhs_argument,
                                        &rhs_residual) ||
        (ixs_node_is_zero(lhs_residual) && ixs_node_is_zero(rhs_residual)) ||
        !equivalence_remainder_integer_proven(state, lhs_residual) ||
        !equivalence_remainder_integer_proven(state, rhs_residual) ||
        equivalence_build_add(state, lhs_argument, lhs_residual,
                              &lhs_shifted) != EQUIVALENCE_BUILD_OK ||
        equivalence_build_add(state, rhs_argument, rhs_residual,
                              &rhs_shifted) != EQUIVALENCE_BUILD_OK ||
        ixs_node_is_sentinel(lhs_shifted) || ixs_node_is_sentinel(rhs_shifted))
      continue;
    if (equivalence_bounded_core(state, lhs_shifted, rhs_shifted, depth) ==
        IXS_CHECK_TRUE)
      return IXS_CHECK_TRUE;
    if (state->limited || state->invalid || state->oom ||
        state->arithmetic_unrepresentable)
      return IXS_CHECK_UNKNOWN;
  }
  return IXS_CHECK_UNKNOWN;
}

static bool equivalence_project_truncating_rounds(
    equivalence_state *state, ixs_node *source_lhs, ixs_node *root_lhs,
    ixs_node *source_rhs, ixs_node *root_rhs, unsigned depth,
    ixs_node **projected_lhs, ixs_node **projected_rhs) {
  ixs_division_projection_result result = ixs_division_algebra_project(
      state->ctx, state->bounds, source_lhs, root_lhs, source_rhs, root_rhs,
      depth == 0u ? IXS_DIVISION_PROJECT_ALL
                  : IXS_DIVISION_PROJECT_DIRECT_ONLY);
  equivalence_note_algebra_status(state, result.status);
  *projected_lhs = result.lhs;
  *projected_rhs = result.rhs;
  return result.status == IXS_ALGEBRA_MATCH;
}

static ixs_node *
facts_simplify_truncating_remainders(ixs_ctx *ctx, ixs_bounds *bounds,
                                     ixs_node *source, ixs_node *root,
                                     ixs_fact_query_status *status) {
  ixs_division_projection_result result = ixs_division_algebra_project(
      ctx, bounds, source, root, ctx->node_zero, ctx->node_zero,
      IXS_DIVISION_PROJECT_PIECEWISE_REDUCING);
  *status = IXS_FACT_QUERY_COMPLETE;
  if (result.status == IXS_ALGEBRA_OOM)
    *status = IXS_FACT_QUERY_OOM;
  else if (result.status == IXS_ALGEBRA_INVALID)
    *status = IXS_FACT_QUERY_INVALID;
  else if (result.status == IXS_ALGEBRA_LIMITED)
    *status = IXS_FACT_QUERY_LIMITED;
  if (*status != IXS_FACT_QUERY_COMPLETE)
    return NULL;
  return result.status == IXS_ALGEBRA_MATCH ? result.lhs : root;
}
static bool equivalence_flatten_logic(equivalence_state *state, ixs_node *root,
                                      ixs_tag tag, ixs_node ***terms,
                                      size_t *nterms, size_t *terms_capacity) {
  query_node_set visited;
  ixs_node **stack = NULL;
  size_t stack_capacity = 0;
  size_t nstack = 0;

  memset(&visited, 0, sizeof(visited));
  *nterms = 0;
  if (!query_node_stack_push(&state->ctx->scratch, &stack, &nstack,
                             &stack_capacity, root))
    goto oom;
  while (nstack > 0) {
    ixs_node *node = stack[--nstack];
    bool inserted;
    if (!query_node_set_insert(&state->ctx->scratch, &visited, node, &inserted))
      goto oom;
    /* AND and OR are idempotent, so sharing and repeated operands may be
     * visited once.  This also makes malformed cyclic nodes terminate. */
    if (!inserted)
      continue;
    if (node->tag == tag && ixs_node_is_bool_valued(node)) {
      uint32_t i;
      for (i = 0; i < node->u.assoc.nargs; i++) {
        if (!query_node_stack_push(&state->ctx->scratch, &stack, &nstack,
                                   &stack_capacity, node->u.assoc.args[i]))
          goto oom;
      }
    } else {
      if (!query_node_stack_push(&state->ctx->scratch, terms, nterms,
                                 terms_capacity, node))
        goto oom;
    }
  }
  return true;

oom:
  state->oom = true;
  return false;
}

static ixs_check_result equivalence_match_logic(equivalence_state *state,
                                                ixs_node *lhs, ixs_node *rhs,
                                                unsigned depth) {
  ixs_arena_mark mark = ixs_arena_save(&state->ctx->scratch);
  ixs_node **left_terms = NULL;
  ixs_node **right_terms = NULL;
  unsigned char *left_matched;
  unsigned char *right_matched;
  size_t left_capacity = 0;
  size_t right_capacity = 0;
  size_t nleft;
  size_t nright;
  size_t i;
  size_t j;
  ixs_check_result result = IXS_CHECK_UNKNOWN;

  if (!equivalence_flatten_logic(state, lhs, lhs->tag, &left_terms, &nleft,
                                 &left_capacity) ||
      !equivalence_flatten_logic(state, rhs, rhs->tag, &right_terms, &nright,
                                 &right_capacity) ||
      nleft != nright)
    goto cleanup;
  left_matched = ixs_arena_alloc(&state->ctx->scratch, nleft, 1);
  right_matched = ixs_arena_alloc(&state->ctx->scratch, nright, 1);
  if ((!left_matched || !right_matched) && nleft != 0) {
    state->oom = true;
    goto cleanup;
  }
  if (nleft != 0) {
    memset(left_matched, 0, nleft);
    memset(right_matched, 0, nright);
  }

  /* Exact terms first.  This makes matching deterministic and avoids proof
   * work on the common reordered-tree case. */
  for (i = 0; i < nleft; i++) {
    for (j = 0; j < nright; j++) {
      if (!right_matched[j] && left_terms[i] == right_terms[j]) {
        left_matched[i] = 1;
        right_matched[j] = 1;
        break;
      }
    }
  }
  for (i = 0; i < nleft; i++) {
    if (left_matched[i])
      continue;
    /* Nested associative matching is a conservative optional refinement.
     * Only the outer match starts subproofs, statically bounding C recursion;
     * each subproof still has unbounded growable traversal of its DAG. */
    if (depth != 0u)
      goto cleanup;
    for (j = 0; j < nright; j++) {
      if (!right_matched[j] &&
          equivalence_core(state, left_terms[i], right_terms[j], depth + 1u) ==
              IXS_CHECK_TRUE) {
        left_matched[i] = 1;
        right_matched[j] = 1;
        break;
      }
    }
    if (!left_matched[i])
      goto cleanup;
  }
  result = IXS_CHECK_TRUE;

cleanup:
  ixs_arena_restore(&state->ctx->scratch, mark);
  return result;
}

static ixs_check_result equivalence_predicate_shapes(equivalence_state *state,
                                                     ixs_node *lhs,
                                                     ixs_node *rhs,
                                                     unsigned depth) {
  if (lhs->tag == rhs->tag && (lhs->tag == IXS_AND || lhs->tag == IXS_OR))
    return equivalence_match_logic(state, lhs, rhs, depth);
  if (lhs->tag == IXS_NOT && rhs->tag == IXS_NOT) {
    if (depth != 0u)
      return IXS_CHECK_UNKNOWN;
    do {
      lhs = lhs->u.unary_bool.arg;
      rhs = rhs->u.unary_bool.arg;
    } while (lhs && rhs && lhs->tag == IXS_NOT && rhs->tag == IXS_NOT);
    return equivalence_core(state, lhs, rhs, depth + 1u);
  }
  if (lhs->tag == IXS_CMP && rhs->tag == IXS_CMP) {
    int64_t delta;
    ixs_check_result result = equivalence_ordered_comparisons(state, lhs, rhs);
    /* Comparisons are canonical residuals against a shared right operand. An
     * exact zero delta therefore preserves any common comparison operator. */
    if (result == IXS_CHECK_UNKNOWN &&
        lhs->u.binary.cmp_op == rhs->u.binary.cmp_op &&
        lhs->u.binary.rhs == rhs->u.binary.rhs &&
        equivalence_integer_delta(state, lhs->u.binary.lhs, rhs->u.binary.lhs,
                                  &delta) &&
        delta == 0)
      result = IXS_CHECK_TRUE;
    return result;
  }
  return IXS_CHECK_UNKNOWN;
}

static ixs_check_result equivalence_expanded(equivalence_state *state,
                                             ixs_node *lhs, ixs_node *rhs,
                                             unsigned depth) {
  ixs_node *expanded_lhs = expand_impl(state->ctx, lhs);
  ixs_node *expanded_rhs = expand_impl(state->ctx, rhs);
  ixs_check_result result;
  bool lhs_limited = false;
  bool rhs_limited = false;
  if (!expanded_lhs || !expanded_rhs) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (ixs_node_is_sentinel(expanded_lhs) ||
      ixs_node_is_sentinel(expanded_rhs)) {
    bounds_query_note_invalid(state->bounds);
    return IXS_CHECK_UNKNOWN;
  }
  expanded_lhs = simp_simplify_bounds_status(state->ctx, expanded_lhs,
                                             state->bounds, &lhs_limited);
  expanded_rhs = simp_simplify_bounds_status(state->ctx, expanded_rhs,
                                             state->bounds, &rhs_limited);
  if (lhs_limited || rhs_limited) {
    state->limited = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (!expanded_lhs || !expanded_rhs) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (ixs_node_is_sentinel(expanded_lhs) ||
      ixs_node_is_sentinel(expanded_rhs)) {
    bounds_query_note_invalid(state->bounds);
    return IXS_CHECK_UNKNOWN;
  }
  if (expanded_lhs == expanded_rhs)
    return IXS_CHECK_TRUE;
  result = equivalence_difference(state, expanded_lhs, expanded_rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  result =
      equivalence_quotient_remainder_algebra(state, expanded_lhs, expanded_rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  if (ixs_node_is_bool_valued(expanded_lhs) &&
      ixs_node_is_bool_valued(expanded_rhs))
    return equivalence_predicate_shapes(state, expanded_lhs, expanded_rhs,
                                        depth);
  return IXS_CHECK_UNKNOWN;
}

static bool equivalence_low_bits_modulus(ixs_node *lhs, ixs_node *rhs,
                                         unsigned *bits) {
  uint64_t modulus;
  *bits = 0u;
  if (!lhs || !rhs || lhs->tag != IXS_MOD || rhs->tag != IXS_MOD ||
      lhs->u.binary.rhs->tag != IXS_INT ||
      rhs->u.binary.rhs != lhs->u.binary.rhs || lhs->u.binary.rhs->u.ival <= 0)
    return false;
  modulus = (uint64_t)lhs->u.binary.rhs->u.ival;
  if ((modulus & (modulus - UINT64_C(1))) != 0u)
    return false;
  while (modulus > 1u) {
    modulus >>= 1u;
    (*bits)++;
  }
  return true;
}

static bool equivalence_low_bits_domain(equivalence_state *state,
                                        ixs_node *node) {
  ixs_algebra_status status =
      ixs_bounds_check_integer_domain(state->bounds, node);
  equivalence_note_algebra_status(state, status);
  return status == IXS_ALGEBRA_MATCH;
}

/* The original outer operations own the domain certificate. Projection never
 * substitutes a normalized root for that source obligation. */
static ixs_check_result equivalence_low_bits(equivalence_state *state,
                                             ixs_node *lhs, ixs_node *rhs,
                                             unsigned depth) {
  ixs_algebra_status status;
  ixs_node *projected_lhs;
  ixs_node *projected_rhs;
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  bool saved_unrepresentable;
  unsigned bits;
  if (!equivalence_low_bits_modulus(lhs, rhs, &bits) ||
      !equivalence_low_bits_domain(state, lhs) ||
      !equivalence_low_bits_domain(state, rhs) ||
      !equivalence_low_bits_domain(state, lhs->u.binary.lhs) ||
      !equivalence_low_bits_domain(state, rhs->u.binary.lhs))
    return result;
  status = ixs_low_bits_algebra_project(state->ctx, state->bounds,
                                        lhs->u.binary.lhs, rhs->u.binary.lhs,
                                        bits, &projected_lhs, &projected_rhs);
  equivalence_note_algebra_status(state, status);
  if (status != IXS_ALGEBRA_MATCH ||
      !equivalence_low_bits_domain(state, projected_lhs) ||
      !equivalence_low_bits_domain(state, projected_rhs))
    return result;
  if (projected_lhs == projected_rhs)
    return IXS_CHECK_TRUE;
  saved_unrepresentable = state->arithmetic_unrepresentable;
  state->arithmetic_unrepresentable = false;
  result =
      equivalence_bounded_core(state, projected_lhs, projected_rhs, depth + 1u);
  state->arithmetic_unrepresentable =
      saved_unrepresentable || state->arithmetic_unrepresentable;
  return result == IXS_CHECK_TRUE ? result : IXS_CHECK_UNKNOWN;
}

static ixs_check_result equivalence_core(equivalence_state *state,
                                         ixs_node *lhs, ixs_node *rhs,
                                         unsigned depth) {
  equivalence_memo_entry *entry;
  ixs_check_result result;

  if (!lhs || !rhs || state->limited || state->invalid || state->oom ||
      state->arithmetic_unrepresentable)
    return IXS_CHECK_UNKNOWN;
  if ((uintptr_t)lhs > (uintptr_t)rhs) {
    ixs_node *tmp = lhs;
    lhs = rhs;
    rhs = tmp;
  }
  entry = equivalence_memo_get(state, lhs, rhs, true);
  if (!entry) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (entry->complete)
    return entry->result;
  if (entry->active)
    return IXS_CHECK_UNKNOWN;
  entry->active = true;
  result = equivalence_core_impl(state, lhs, rhs, depth, true);
  entry = equivalence_memo_get(state, lhs, rhs, false);
  if (!entry) {
    state->invalid = true;
    return IXS_CHECK_UNKNOWN;
  }
  entry->active = false;
  if (!state->limited && !state->invalid && !state->oom) {
    entry->result = result;
    entry->complete = true;
  }
  return result;
}

#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
/* Start an otherwise ordinary equivalence query with the bounded child-proof
 * budget exhausted. This exercises the production stop condition without a
 * test-only branch in the proof rules. */
IXS_STATIC ixs_check_result ixs_bounds_equivalence_subproof_limit_probe(
    ixs_facts *facts, const ixs_node *lhs, const ixs_node *rhs) {
  equivalence_state state;
  ixs_check_result result;

  if (!facts || !facts->usable || !lhs || !rhs)
    return IXS_CHECK_UNKNOWN;
  equivalence_state_init(&state, facts->ctx, &facts->bounds);
  state.bounded_subproof_depth = EQUIVALENCE_BOUNDED_SUBPROOF_DEPTH;
  result = equivalence_core(&state, lhs, rhs, 0);
  if (state.limited || state.invalid || state.oom)
    result = IXS_CHECK_UNKNOWN;
  equivalence_state_destroy(&state);
  return result;
}

/* Exercise the production quotient-algebra budget without a test-only proof
 * branch. */
IXS_STATIC ixs_check_result ixs_bounds_equivalence_quotient_limit_probe(
    ixs_facts *facts, const ixs_node *lhs, const ixs_node *rhs) {
  ixs_quotient_algebra_result result;
  unsigned candidates = IXS_QUOTIENT_ALGEBRA_MAX_CANDIDATES;

  if (!facts || !facts->usable || !lhs || !rhs)
    return IXS_CHECK_UNKNOWN;
  result = ixs_quotient_algebra_check(facts->ctx, &facts->bounds, lhs, rhs,
                                      candidates);
  return result.check;
}
#endif

static ixs_check_result equivalence_predicate_truth(equivalence_state *state,
                                                    ixs_node *lhs,
                                                    ixs_node *rhs) {
  ixs_check_result lhs_truth;
  ixs_check_result rhs_truth;
  bool lhs_limited = false;
  bool rhs_limited = false;

  if (!ixs_node_is_bool_valued(lhs) || !ixs_node_is_bool_valued(rhs))
    return IXS_CHECK_UNKNOWN;
  lhs_truth = bounds_predicate_eval(state->bounds, lhs, &lhs_limited);
  rhs_truth = bounds_predicate_eval(state->bounds, rhs, &rhs_limited);
  if (lhs_limited || rhs_limited) {
    state->limited = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (lhs_truth == IXS_CHECK_UNKNOWN || rhs_truth == IXS_CHECK_UNKNOWN)
    return IXS_CHECK_UNKNOWN;
  return lhs_truth == rhs_truth ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
}

static ixs_check_result equivalence_projected(equivalence_state *state,
                                              ixs_node *lhs, ixs_node *rhs,
                                              unsigned depth) {
  ixs_node *projected_lhs;
  ixs_node *projected_rhs;
  ixs_check_result result;

  if (!equivalence_project_truncating_rounds(state, lhs, lhs, rhs, rhs, depth,
                                             &projected_lhs, &projected_rhs))
    return IXS_CHECK_UNKNOWN;
  if (projected_lhs == projected_rhs)
    return IXS_CHECK_TRUE;
  result = equivalence_difference(state, projected_lhs, projected_rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  result = equivalence_quotient_remainder_algebra(state, projected_lhs,
                                                  projected_rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  return equivalence_expanded(state, projected_lhs, projected_rhs, depth);
}

typedef struct {
  ixs_node *selector;
  const char *name;
  int64_t points[EQUIVALENCE_PIECEWISE_MAX_POINTS];
  size_t count;
  uint64_t remaining;
} equivalence_piecewise_domain;

static ixs_node *equivalence_piecewise_affine_symbol(ixs_node *expr) {
  if (expr->tag == IXS_SYM)
    return expr;
  if (expr->tag == IXS_MUL && expr->u.mul.nfactors == 1u &&
      expr->u.mul.factors[0].exp == 1 &&
      expr->u.mul.factors[0].base->tag == IXS_SYM)
    return expr->u.mul.factors[0].base;
  if (expr->tag == IXS_ADD && expr->u.add.nterms == 1u &&
      expr->u.add.terms[0].term->tag == IXS_SYM)
    return expr->u.add.terms[0].term;
  return NULL;
}

static bool equivalence_piecewise_affine_guard(ixs_node *condition,
                                               ixs_node **selector,
                                               int64_t *scale, int64_t *offset,
                                               ixs_cmp_op *op) {
  ixs_node *affine;
  const char *name;

  if (!condition || condition->tag != IXS_CMP)
    return false;
  *op = condition->u.binary.cmp_op;
  if (ixs_node_is_zero(condition->u.binary.rhs)) {
    affine = condition->u.binary.lhs;
  } else if (ixs_node_is_zero(condition->u.binary.lhs)) {
    affine = condition->u.binary.rhs;
    *op = flip_cmp(*op);
  } else {
    return false;
  }
  if (!bounds_extract_integer_affine(affine, &name, scale, offset))
    return false;
  *selector = equivalence_piecewise_affine_symbol(affine);
  return *selector && (*selector)->u.name == name;
}

static bool equivalence_piecewise_find_selector(ixs_node *piecewise,
                                                ixs_node **selector) {
  uint32_t i;

  *selector = NULL;
  for (i = 0; i < piecewise->u.pw.ncases; i++) {
    ixs_node *condition = piecewise->u.pw.cases[i].cond;
    int64_t scale;
    int64_t offset;
    ixs_cmp_op op;
    if (!condition)
      return false;
    if (ixs_node_is_known_true(condition) || ixs_node_is_known_false(condition))
      continue;
    if (!equivalence_piecewise_affine_guard(condition, selector, &scale,
                                            &offset, &op))
      return false;
    return true;
  }
  return false;
}

static bool
equivalence_piecewise_domain_init(equivalence_state *state, ixs_node *piecewise,
                                  equivalence_piecewise_domain *domain) {
  ixs_var_bound *var;
  int64_t modulus;
  int64_t remainder;
  int64_t lower;
  int64_t upper;
  int64_t point;

  memset(domain, 0, sizeof(*domain));
  if (!equivalence_piecewise_find_selector(piecewise, &domain->selector))
    return false;
  domain->name = domain->selector->u.name;
  var = bounds_store_find_var(state->bounds, domain->name);
  if (!var || !var->iv.valid || var->iv.lo_inf || var->iv.hi_inf)
    return false;
  lower = ixs_rat_ceil(var->iv.lo_p, var->iv.lo_q);
  upper = ixs_rat_floor(var->iv.hi_p, var->iv.hi_q);
  if (lower > upper)
    return false;
  modulus = var->modulus > 0 ? var->modulus : 1;
  remainder = var->modulus > 0 ? var->remainder : 0;
  if (!ixs_integer_align_congruence_up(lower, modulus, remainder, &point) ||
      point > upper)
    return false;

  for (;;) {
    int64_t next;
    if (domain->count == EQUIVALENCE_PIECEWISE_MAX_POINTS)
      return false;
    domain->points[domain->count++] = point;
    if (!ixs_safe_add(point, modulus, &next) || next > upper)
      break;
    point = next;
  }
  domain->remaining = domain->count == EQUIVALENCE_PIECEWISE_MAX_POINTS
                          ? UINT64_MAX
                          : (UINT64_C(1) << domain->count) - UINT64_C(1);
  return true;
}

static bool equivalence_piecewise_cmp_zero(ixs_cmp_op op, int64_t value) {
  switch (op) {
  case IXS_CMP_GT:
    return value > 0;
  case IXS_CMP_GE:
    return value >= 0;
  case IXS_CMP_LT:
    return value < 0;
  case IXS_CMP_LE:
    return value <= 0;
  case IXS_CMP_EQ:
    return value == 0;
  case IXS_CMP_NE:
    return value != 0;
  }
  return false;
}

static bool
equivalence_piecewise_guard_mask(const equivalence_piecewise_domain *domain,
                                 ixs_node *condition, uint64_t *mask) {
  ixs_node *selector;
  int64_t scale;
  int64_t offset;
  ixs_cmp_op op;
  size_t i;

  *mask = 0u;
  if (ixs_node_is_known_false(condition))
    return true;
  if (ixs_node_is_known_true(condition)) {
    *mask = domain->count == EQUIVALENCE_PIECEWISE_MAX_POINTS
                ? UINT64_MAX
                : (UINT64_C(1) << domain->count) - UINT64_C(1);
    return true;
  }
  if (!equivalence_piecewise_affine_guard(condition, &selector, &scale, &offset,
                                          &op) ||
      selector != domain->selector)
    return false;
  for (i = 0; i < domain->count; i++) {
    int64_t product;
    int64_t value;
    if (!ixs_safe_mul(scale, domain->points[i], &product) ||
        !ixs_safe_add(product, offset, &value))
      return false;
    if (equivalence_piecewise_cmp_zero(op, value))
      *mask |= UINT64_C(1) << i;
  }
  return true;
}

static bool equivalence_piecewise_single_point(uint64_t mask, size_t *index) {
  size_t i;

  if (mask == 0u || (mask & (mask - UINT64_C(1))) != 0u)
    return false;
  for (i = 0; i < EQUIVALENCE_PIECEWISE_MAX_POINTS; i++)
    if ((mask & (UINT64_C(1) << i)) != 0u) {
      *index = i;
      return true;
    }
  return false;
}

/* Piecewise arm substitution is admitted only for small complete DAGs. This
 * cap prevents branch count from multiplying reconstruction of a large peer. */
static bool equivalence_piecewise_small_operand(ixs_node *root) {
  ixs_node *stack[EQUIVALENCE_PIECEWISE_MAX_POINTS];
  ixs_node *seen[EQUIVALENCE_PIECEWISE_MAX_POINTS];
  size_t stack_count = 0u;
  size_t seen_count = 0u;

  if (!root)
    return false;
  stack[stack_count++] = root;
  while (stack_count != 0u) {
    ixs_node *node = stack[--stack_count];
    uint32_t child_count;
    uint32_t child;
    size_t i;
    for (i = 0; i < seen_count; i++)
      if (seen[i] == node)
        break;
    if (i != seen_count)
      continue;
    if (seen_count == EQUIVALENCE_PIECEWISE_MAX_POINTS ||
        node->tag == IXS_PIECEWISE ||
        !defined_child_count(node, &child_count) ||
        child_count > EQUIVALENCE_PIECEWISE_MAX_POINTS - stack_count)
      return false;
    seen[seen_count++] = node;
    for (child = 0; child < child_count; child++)
      stack[stack_count++] = defined_child_at(node, child);
  }
  return true;
}

static bool
equivalence_piecewise_prove_point(equivalence_state *state, ixs_node *value,
                                  ixs_node *other,
                                  const equivalence_piecewise_domain *domain,
                                  size_t point_index, unsigned depth) {
  ixs_ctx *ctx = state->ctx;
  ixs_arena_mark diag_mark = ixs_arena_save(&ctx->diag);
  const char **saved_errors = ctx->errors;
  size_t saved_nerrors = ctx->nerrors;
  size_t saved_errors_cap = ctx->errors_cap;
  ixs_node *point = ixs_node_int(ctx, domain->points[point_index]);
  ixs_node *substituted_value =
      point ? simp_subs(ctx, value, domain->selector, point) : NULL;
  ixs_node *substituted_other =
      point ? simp_subs(ctx, other, domain->selector, point) : NULL;
  bool value_oom = false;
  bool value_limited = false;
  bool other_oom = false;
  bool other_limited = false;
  ixs_check_result result = IXS_CHECK_UNKNOWN;

  ixs_arena_restore(&ctx->diag, diag_mark);
  ctx->errors = saved_errors;
  ctx->nerrors = saved_nerrors;
  ctx->errors_cap = saved_errors_cap;
  if (!point || !substituted_value || !substituted_other) {
    state->oom = true;
    return false;
  }
  if (ixs_node_is_sentinel(substituted_value) ||
      ixs_node_is_sentinel(substituted_other))
    return false;
  if (bounds_defined_check_detail(state->bounds, substituted_value, &value_oom,
                                  &value_limited) != IXS_CHECK_TRUE ||
      bounds_defined_check_detail(state->bounds, substituted_other, &other_oom,
                                  &other_limited) != IXS_CHECK_TRUE) {
    if (value_oom || other_oom || state->bounds->oom)
      state->oom = true;
    if (value_limited || other_limited)
      state->limited = true;
    return false;
  }
  result = equivalence_bounded_core(state, substituted_value, substituted_other,
                                    depth);
  return result == IXS_CHECK_TRUE;
}

/* Final bounded fallback for an exact root Piecewise. It tracks first-match
 * reachability in a complete finite congruent selector mask, then proves only
 * single-point arms. No fact-table fork or whole-operand Piecewise
 * substitution occurs. Work is bounded by 16 arms, 64 selector points, and
 * 64-node arm/peer DAGs. */
static ixs_check_result equivalence_piecewise_root(equivalence_state *state,
                                                   ixs_node *lhs, ixs_node *rhs,
                                                   unsigned depth) {
  equivalence_piecewise_domain domain;
  ixs_node *piecewise;
  ixs_node *other;
  bool have_reachable = false;
  uint32_t i;

  if ((lhs->tag == IXS_PIECEWISE) == (rhs->tag == IXS_PIECEWISE))
    return IXS_CHECK_UNKNOWN;
  piecewise = lhs->tag == IXS_PIECEWISE ? lhs : rhs;
  other = lhs->tag == IXS_PIECEWISE ? rhs : lhs;
  if (piecewise->u.pw.ncases == 0u || !piecewise->u.pw.cases) {
    state->invalid = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (piecewise->u.pw.ncases > EQUIVALENCE_PIECEWISE_MAX_CASES ||
      !equivalence_piecewise_small_operand(other) ||
      !equivalence_piecewise_domain_init(state, piecewise, &domain))
    return IXS_CHECK_UNKNOWN;

  for (i = 0; i < piecewise->u.pw.ncases; i++) {
    ixs_node *condition = piecewise->u.pw.cases[i].cond;
    ixs_node *value = piecewise->u.pw.cases[i].value;
    uint64_t condition_mask;
    uint64_t active;
    size_t point_index;

    if (domain.remaining == 0u)
      return have_reachable ? IXS_CHECK_TRUE : IXS_CHECK_UNKNOWN;
    if (!condition || !value ||
        !equivalence_piecewise_guard_mask(&domain, condition, &condition_mask))
      return IXS_CHECK_UNKNOWN;
    active = domain.remaining & condition_mask;
    if (active != 0u) {
      if (!equivalence_piecewise_single_point(active, &point_index) ||
          !equivalence_piecewise_small_operand(value) ||
          !equivalence_piecewise_prove_point(state, value, other, &domain,
                                             point_index, depth))
        return IXS_CHECK_UNKNOWN;
      have_reachable = true;
    }
    domain.remaining &= ~condition_mask;
  }
  return domain.remaining == 0u && have_reachable ? IXS_CHECK_TRUE
                                                  : IXS_CHECK_UNKNOWN;
}

static ixs_check_result
equivalence_quotient_remainder_algebra(equivalence_state *state, ixs_node *lhs,
                                       ixs_node *rhs) {
  ixs_bounds *bounds = state->bounds;
  ixs_bounds_transport_snapshot transport =
      ixs_bounds_query_transport_snapshot(bounds);
  size_t cycle_blocks = bounds_query_cycle_count(bounds);
  bool blocked;
  ixs_quotient_algebra_result result =
      ixs_quotient_algebra_check(state->ctx, bounds, lhs, rhs, 0u);
  blocked = result.limited || bounds_query_limited_since(bounds, transport) ||
            bounds_query_cycle_count(bounds) != cycle_blocks;
  state->invalid |=
      result.invalid || bounds_query_invalid_since(bounds, transport);
  state->oom |= result.oom;
  if (blocked || state->invalid || state->oom)
    return IXS_CHECK_UNKNOWN;
  return result.check;
}

static ixs_check_result
equivalence_direct_arithmetic(equivalence_state *state, ixs_node *lhs,
                              ixs_node *rhs, ixs_node *simplified_lhs,
                              ixs_node *simplified_rhs, unsigned depth) {
  ixs_check_result result;

  result = equivalence_difference(state, simplified_lhs, simplified_rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  if (state->arithmetic_unrepresentable)
    return equivalence_low_bits(state, lhs, rhs, depth);

  result = equivalence_affine_round_context(state, simplified_lhs,
                                            simplified_rhs, depth);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  if (state->arithmetic_unrepresentable)
    return equivalence_low_bits(state, lhs, rhs, depth);

  return IXS_CHECK_UNKNOWN;
}

static ixs_check_result
equivalence_context_composition(equivalence_state *state, ixs_node *lhs,
                                ixs_node *rhs, ixs_node *simplified_lhs,
                                ixs_node *simplified_rhs, unsigned depth,
                                bool allow_context) {
  ixs_check_result result;

  if (!allow_context)
    return IXS_CHECK_UNKNOWN;
  result =
      equivalence_same_context(state, simplified_lhs, simplified_rhs, depth);
  if (result == IXS_CHECK_UNKNOWN && state->arithmetic_unrepresentable)
    return equivalence_low_bits(state, lhs, rhs, depth);
  return result;
}

static ixs_check_result equivalence_core_impl(equivalence_state *state,
                                              ixs_node *lhs, ixs_node *rhs,
                                              unsigned depth,
                                              bool allow_context) {
  ixs_node *simplified_lhs;
  ixs_node *simplified_rhs;
  ixs_check_result result;
  bool lhs_limited = false;
  bool rhs_limited = false;

  if (state->visited != SIZE_MAX)
    state->visited++;
  if (lhs == rhs)
    return IXS_CHECK_TRUE;

  simplified_lhs =
      simp_simplify_bounds_status(state->ctx, lhs, state->bounds, &lhs_limited);
  simplified_rhs =
      simp_simplify_bounds_status(state->ctx, rhs, state->bounds, &rhs_limited);
  if (lhs_limited || rhs_limited) {
    state->limited = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (!simplified_lhs || !simplified_rhs) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (ixs_node_is_sentinel(simplified_lhs) ||
      ixs_node_is_sentinel(simplified_rhs)) {
    bounds_query_note_invalid(state->bounds);
    return IXS_CHECK_UNKNOWN;
  }
  if (simplified_lhs == simplified_rhs)
    return IXS_CHECK_TRUE;

  result = equivalence_predicate_truth(state, simplified_lhs, simplified_rhs);
  if (result != IXS_CHECK_UNKNOWN || state->limited)
    return result;

  result = equivalence_quotient_remainder_algebra(state, simplified_lhs,
                                                  simplified_rhs);
  if (result != IXS_CHECK_UNKNOWN || state->limited || state->invalid ||
      state->oom)
    return result;

  result = equivalence_direct_arithmetic(state, lhs, rhs, simplified_lhs,
                                         simplified_rhs, depth);
  if (result != IXS_CHECK_UNKNOWN || state->arithmetic_unrepresentable)
    return result;
  result = equivalence_context_composition(
      state, lhs, rhs, simplified_lhs, simplified_rhs, depth, allow_context);
  if (result != IXS_CHECK_UNKNOWN || state->arithmetic_unrepresentable)
    return result;
  result = equivalence_projected(state, lhs, rhs, depth);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  result = equivalence_expanded(state, simplified_lhs, simplified_rhs, depth);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  result = equivalence_low_bits(state, lhs, rhs, depth);
  if (result != IXS_CHECK_UNKNOWN || !allow_context)
    return result;
  return equivalence_piecewise_root(state, simplified_lhs, simplified_rhs,
                                    depth);
}

typedef enum {
  EQUIVALENCE_QUERY_COMPLETE,
  EQUIVALENCE_QUERY_LIMITED,
  EQUIVALENCE_QUERY_INVALID,
  EQUIVALENCE_QUERY_OOM
} equivalence_query_status;

static equivalence_query_status
equivalence_query_bounds_detail(ixs_bounds *bounds, ixs_ctx *ctx, ixs_node *lhs,
                                ixs_node *rhs, ixs_check_result *result) {
  ixs_arena_mark mark = ixs_arena_save(&ctx->scratch);
  equivalence_state state;
  ixs_bounds_transport_snapshot transport =
      ixs_bounds_query_transport_snapshot(bounds);
  ixs_bounds_transport_snapshot limit_transport = transport;
  bool old_oom = bounds->oom;
  bool track_limits = bounds_query_is_tracking(bounds);
  bool lhs_oom = false;
  bool rhs_oom = false;
  bool lhs_limited = false;
  bool rhs_limited = false;
  equivalence_query_status status = EQUIVALENCE_QUERY_COMPLETE;

  equivalence_state_init(&state, ctx, bounds);
  *result = IXS_CHECK_UNKNOWN;
  if (bounds_defined_check_detail(bounds, lhs, &lhs_oom, &lhs_limited) !=
          IXS_CHECK_TRUE ||
      bounds_defined_check_detail(bounds, rhs, &rhs_oom, &rhs_limited) !=
          IXS_CHECK_TRUE) {
    if (lhs_oom || rhs_oom || (!old_oom && bounds->oom))
      status = EQUIVALENCE_QUERY_OOM;
    else if (lhs_limited || rhs_limited)
      status = EQUIVALENCE_QUERY_LIMITED;
    goto restore;
  }
  limit_transport = ixs_bounds_query_transport_snapshot(bounds);
  *result = equivalence_core(&state, lhs, rhs, 0);
  if (state.invalid || bounds_query_invalid_since(bounds, transport)) {
    *result = IXS_CHECK_UNKNOWN;
    status = EQUIVALENCE_QUERY_INVALID;
  } else if (state.oom || (!old_oom && bounds->oom)) {
    *result = IXS_CHECK_UNKNOWN;
    status = EQUIVALENCE_QUERY_OOM;
  } else if (*result == IXS_CHECK_UNKNOWN &&
             (state.limited ||
              (track_limits &&
               bounds_query_limited_since(bounds, limit_transport)))) {
    *result = IXS_CHECK_UNKNOWN;
    status = EQUIVALENCE_QUERY_LIMITED;
  }

restore:
  equivalence_state_destroy(&state);
  if (!old_oom && bounds->oom)
    bounds_store_invalidate_reads(bounds);
  bounds->oom = old_oom;
  ixs_arena_restore(&ctx->scratch, mark);
  return status;
}

static equivalence_query_status
equivalence_query_bound_detail(ixs_facts *facts, ixs_ctx *ctx, ixs_node *lhs,
                               ixs_node *rhs, ixs_check_result *result) {
  return equivalence_query_bounds_detail(&facts->bounds, ctx, lhs, rhs, result);
}

typedef struct {
  ixs_node *unit_piecewise;
  int unit_piecewise_sign;
  bool has_piecewise;
  bool has_nonunit_scaled_mod;
} equivalence_atom_exact_sides;

static void
equivalence_atom_find_exact_sides(ixs_node *difference,
                                  equivalence_atom_exact_sides *sides) {
  uint32_t i;

  memset(sides, 0, sizeof(*sides));
  if (!difference || difference->tag != IXS_ADD)
    return;
  for (i = 0; i < difference->u.add.nterms; i++) {
    int64_t p;
    int64_t q;
    if (difference->u.add.terms[i].term->tag == IXS_PIECEWISE) {
      ixs_node_get_rat(difference->u.add.terms[i].coeff, &p, &q);
      if (!sides->has_piecewise && q == 1 && (p == -1 || p == 1)) {
        sides->unit_piecewise = difference->u.add.terms[i].term;
        sides->unit_piecewise_sign = p < 0 ? -1 : 1;
      } else {
        sides->unit_piecewise = NULL;
        sides->unit_piecewise_sign = 0;
      }
      sides->has_piecewise = true;
      continue;
    }
    if (difference->u.add.terms[i].term->tag != IXS_MOD)
      continue;
    ixs_node_get_rat(difference->u.add.terms[i].coeff, &p, &q);
    if (q == 1 && p != -1 && p != 0 && p != 1)
      sides->has_nonunit_scaled_mod = true;
  }
}

/* Isolate one unit Piecewise term from a normalized zero-sum ADD. Multiplying
 * every other coefficient by the opposite unit preserves canonical term
 * order, so the peer is rebuilt once without distributing into any arm. */
static bool bounds_isolate_piecewise_relation(ixs_bounds *bounds,
                                              ixs_node *difference,
                                              ixs_node *piecewise,
                                              int piecewise_sign,
                                              ixs_node **other) {
  ixs_arena_mark mark = ixs_arena_save(bounds->scratch);
  ixs_addterm *terms;
  ixs_node *constant;
  int64_t constant_p;
  int64_t constant_q;
  size_t bytes;
  uint32_t count = 0u;
  uint32_t i;
  bool ok = false;

  bytes = (size_t)difference->u.add.nterms * sizeof(*terms);
  if (bytes / sizeof(*terms) != difference->u.add.nterms) {
    bounds->oom = true;
    goto cleanup;
  }
  terms = ixs_arena_alloc(bounds->scratch, bytes, sizeof(void *));
  if (!terms) {
    bounds->oom = true;
    goto cleanup;
  }

  for (i = 0; i < difference->u.add.nterms; i++) {
    ixs_node *term = difference->u.add.terms[i].term;
    int64_t coefficient_p;
    int64_t coefficient_q;

    ixs_node_get_rat(difference->u.add.terms[i].coeff, &coefficient_p,
                     &coefficient_q);
    if (term == piecewise)
      continue;
    if (piecewise_sign > 0 && !ixs_rat_neg(coefficient_p, coefficient_q,
                                           &coefficient_p, &coefficient_q))
      goto cleanup;
    terms[count].term = term;
    terms[count].coeff =
        ixs_node_rat(bounds->ctx, coefficient_p, coefficient_q);
    if (!terms[count].coeff) {
      bounds->oom = true;
      goto cleanup;
    }
    count++;
  }

  ixs_node_get_rat(difference->u.add.coeff, &constant_p, &constant_q);
  if (piecewise_sign > 0 &&
      !ixs_rat_neg(constant_p, constant_q, &constant_p, &constant_q))
    goto cleanup;
  constant = ixs_node_rat(bounds->ctx, constant_p, constant_q);
  if (!constant) {
    bounds->oom = true;
    goto cleanup;
  }
  if (count == 0u)
    *other = constant;
  else if (count == 1u && ixs_node_is_zero(constant) &&
           ixs_node_is_one(terms[0].coeff))
    *other = terms[0].term;
  else
    *other = ixs_node_add(bounds->ctx, constant, count, terms);
  if (!*other) {
    bounds->oom = true;
    goto cleanup;
  }
  ok = !ixs_node_is_sentinel(*other);

cleanup:
  ixs_arena_restore(bounds->scratch, mark);
  return ok;
}

/* Predicate construction normalizes equality to a zero-sum ADD. Recover its
 * exact operands so the ordinary equivalence rules see the same scaled-Mod or
 * exact root-Piecewise relation as the direct API. Each path is O(T) in the
 * direct terms and uses O(T) query scratch. */
static void bounds_equivalence_atom_sides(ixs_bounds *bounds, ixs_node *cmp,
                                          ixs_node **lhs, ixs_node **rhs) {
  struct ixs_node_impl equality;
  ixs_node *relation_lhs;
  ixs_node *relation_rhs;
  int64_t offset;
  equivalence_atom_exact_sides sides;

  *lhs = cmp->u.binary.lhs;
  *rhs = cmp->u.binary.rhs;
  if (!ixs_node_is_zero(*rhs) || bounds_extract_unit_equality(*lhs, lhs, rhs))
    return;
  equivalence_atom_find_exact_sides(*lhs, &sides);
  if (sides.has_piecewise) {
    if (sides.unit_piecewise && bounds_isolate_piecewise_relation(
                                    bounds, *lhs, sides.unit_piecewise,
                                    sides.unit_piecewise_sign, &relation_rhs)) {
      *lhs = sides.unit_piecewise;
      *rhs = relation_rhs;
      return;
    }
    if (!sides.has_nonunit_scaled_mod)
      return;
  }
  if (!sides.has_nonunit_scaled_mod)
    return;

  equality = *(const struct ixs_node_impl *)cmp;
  equality.u.binary.cmp_op = IXS_CMP_EQ;
  if (!bounds_extract_cmp_exact_relation(bounds, &equality, &relation_lhs,
                                         &relation_rhs, &offset))
    return;
  if (offset != 0) {
    ixs_node *constant = ixs_node_int(bounds->ctx, offset);
    bool unrepresentable = false;
    relation_rhs = constant ? simp_try_add(bounds->ctx, relation_rhs, constant,
                                           &unrepresentable)
                            : NULL;
    if (!relation_rhs && !unrepresentable)
      bounds->oom = true;
    if (unrepresentable || !relation_rhs || ixs_node_is_sentinel(relation_rhs))
      return;
  }
  *lhs = relation_lhs;
  *rhs = relation_rhs;
}

static ixs_check_result bounds_check_equivalence_atom(ixs_bounds *bounds,
                                                      ixs_node *cmp) {
  bounds_query_owner_scope owner_scope;
  equivalence_query_status status;
  ixs_check_result equivalent = IXS_CHECK_UNKNOWN;
  ixs_node *lhs;
  ixs_node *rhs;

  if (!bounds || !bounds->ctx || !cmp || cmp->tag != IXS_CMP ||
      bounds->predicate_equivalence_depth != 0u ||
      (cmp->u.binary.cmp_op != IXS_CMP_EQ &&
       cmp->u.binary.cmp_op != IXS_CMP_NE) ||
      (ixs_node_is_pred_kind(cmp->u.binary.lhs) &&
       cmp->u.binary.lhs->tag != IXS_INT) ||
      (ixs_node_is_pred_kind(cmp->u.binary.rhs) &&
       cmp->u.binary.rhs->tag != IXS_INT))
    return IXS_CHECK_UNKNOWN;

  bounds_equivalence_atom_sides(bounds, cmp, &lhs, &rhs);

  bounds->predicate_equivalence_depth++;
  bounds_query_owner_scope_begin(bounds, &owner_scope);
  status = equivalence_query_bounds_detail(bounds, bounds->ctx, lhs, rhs,
                                           &equivalent);
  bounds_query_owner_scope_end(bounds, &owner_scope);
  bounds->predicate_equivalence_depth--;

  if (status == EQUIVALENCE_QUERY_LIMITED && bounds->query_state)
    bounds_query_note_limit(bounds);
  else if (status == EQUIVALENCE_QUERY_INVALID && bounds->query_state)
    bounds_query_note_invalid(bounds);
  else if (status == EQUIVALENCE_QUERY_OOM)
    bounds->oom = true;
  if (status != EQUIVALENCE_QUERY_COMPLETE)
    return IXS_CHECK_UNKNOWN;
  return cmp->u.binary.cmp_op == IXS_CMP_EQ ? equivalent
                                            : bounds_predicate_not(equivalent);
}

IXS_STATIC ixs_check_result ixs_bounds_check_query(ixs_bounds *bounds,
                                                   ixs_node *cmp) {
  ixs_check_result result;
  bool query_held = false;

  if (!ixs_bounds_query_hold_begin(bounds, cmp, &query_held))
    return IXS_CHECK_UNKNOWN;
  result = ixs_bounds_check(bounds, cmp);
  if (result == IXS_CHECK_UNKNOWN && cmp && cmp->tag == IXS_CMP &&
      ixs_node_is_zero(cmp->u.binary.rhs) &&
      (cmp->u.binary.cmp_op == IXS_CMP_EQ ||
       cmp->u.binary.cmp_op == IXS_CMP_NE))
    result = bounds_check_equivalence_atom(bounds, cmp);
  if (query_held)
    ixs_bounds_query_hold_end(bounds);
  return result;
}

IXS_STATIC ixs_check_result bounds_cmp_atom(ixs_bounds *bounds, ixs_node *cmp) {
  ixs_check_result result;

  /* A reflexive equality is the public predicate encoding for totality.
   * Do not send it through arithmetic simplification: a fact-proven domain
   * failure is a FALSE proof, not an invalid query or a diagnostic. */
  if (cmp->u.binary.cmp_op == IXS_CMP_EQ &&
      cmp->u.binary.lhs == cmp->u.binary.rhs)
    return ixs_bounds_check_defined(bounds, cmp->u.binary.lhs);
  result = ixs_bounds_check_query(bounds, cmp);
  if (result != IXS_CHECK_UNKNOWN || !ixs_node_is_zero(cmp->u.binary.rhs) ||
      (cmp->u.binary.cmp_op != IXS_CMP_EQ &&
       cmp->u.binary.cmp_op != IXS_CMP_NE) ||
      !bounds_store_contains_nonzero(bounds, cmp->u.binary.lhs))
    return result;
  return cmp->u.binary.cmp_op == IXS_CMP_NE ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
}

static ixs_fact_query_status
constant_difference_query_status(bool oom, bool invalid, bool limited, bool ok,
                                 int64_t result, int64_t *delta,
                                 bool *matched) {
  *matched = false;
  if (oom)
    return IXS_FACT_QUERY_OOM;
  if (invalid)
    return IXS_FACT_QUERY_INVALID;
  if (limited)
    return IXS_FACT_QUERY_LIMITED;
  if (ok) {
    *delta = result;
    *matched = true;
  }
  return IXS_FACT_QUERY_COMPLETE;
}

typedef struct {
  int64_t result;
  bool invalid;
  bool delta_limited;
  bool delta_oom;
  bool limited;
  bool oom;
  bool ok;
} constant_difference_attempt;

static void constant_difference_try_projection(
    ixs_ctx *ctx, ixs_bounds *bounds, ixs_node *lhs, ixs_node *rhs,
    ixs_bounds_transport_snapshot transport, bool old_oom,
    constant_difference_attempt *attempt) {
  equivalence_state projection;
  ixs_node *nodes[2] = {lhs, rhs};

  equivalence_state_init(&projection, ctx, bounds);
  if (equivalence_project_truncating_rounds(&projection, lhs, lhs, rhs, rhs, 0,
                                            &nodes[0], &nodes[1]) &&
      !projection.limited && !projection.invalid && !projection.oom) {
    bool projected_invalid = false;
    bool projected_limited = false;
    bool projected_oom = false;
    attempt->ok = bounds_constant_delta_query_detail(
        ctx, bounds, nodes[0], nodes[1], true, &attempt->result,
        &projected_invalid, &projected_limited, &projected_oom);
    attempt->invalid = attempt->invalid || projected_invalid;
    attempt->delta_limited = attempt->delta_limited || projected_limited;
    attempt->delta_oom = attempt->delta_oom || projected_oom;
  }
  attempt->invalid = attempt->invalid || projection.invalid;
  attempt->oom =
      attempt->delta_oom || projection.oom || (!old_oom && bounds->oom);
  attempt->limited = attempt->delta_limited || projection.limited ||
                     bounds_query_limited_since(bounds, transport);
  equivalence_state_destroy(&projection);
}

static bool
constant_difference_normalize_operands(ixs_ctx *ctx, ixs_bounds *bounds,
                                       ixs_node **lhs, ixs_node **rhs,
                                       constant_difference_attempt *attempt) {
  bool lhs_limited = false;
  bool rhs_limited = false;
  ixs_node *normalized_lhs =
      simp_simplify_bounds_status(ctx, *lhs, bounds, &lhs_limited);
  ixs_node *normalized_rhs =
      simp_simplify_bounds_status(ctx, *rhs, bounds, &rhs_limited);

  attempt->limited = lhs_limited || rhs_limited;
  if (attempt->limited)
    return false;
  if (!normalized_lhs || !normalized_rhs) {
    attempt->oom = true;
    return false;
  }
  if (ixs_node_is_sentinel(normalized_lhs) ||
      ixs_node_is_sentinel(normalized_rhs)) {
    attempt->invalid = true;
    return false;
  }
  *lhs = normalized_lhs;
  *rhs = normalized_rhs;
  return true;
}

static ixs_fact_query_status
constant_difference_query_bound_detail(ixs_ctx *ctx, ixs_bounds *bounds,
                                       ixs_node *lhs, ixs_node *rhs,
                                       int64_t *delta, bool *matched) {
  ixs_arena_mark mark = ixs_arena_save(&ctx->scratch);
  constant_difference_attempt attempt;
  ixs_node *original_lhs = lhs;
  ixs_node *original_rhs = rhs;
  ixs_bounds_transport_snapshot transport =
      ixs_bounds_query_transport_snapshot(bounds);
  bool old_oom = bounds->oom;
  bool lhs_oom = false;
  bool rhs_oom = false;
  bool lhs_limited = false;
  bool rhs_limited = false;
  bool has_rounding =
      ixs_node_contains_rounding(lhs) || ixs_node_contains_rounding(rhs);
  ixs_fact_query_status status = IXS_FACT_QUERY_COMPLETE;

  memset(&attempt, 0, sizeof(attempt));
  if (bounds_defined_check_detail(bounds, lhs, &lhs_oom, &lhs_limited) !=
          IXS_CHECK_TRUE ||
      bounds_defined_check_detail(bounds, rhs, &rhs_oom, &rhs_limited) !=
          IXS_CHECK_TRUE) {
    attempt.oom = lhs_oom || rhs_oom;
    attempt.limited = lhs_limited || rhs_limited;
    goto finish;
  }
  transport = ixs_bounds_query_transport_snapshot(bounds);

  /* Normalize each side before constructing the difference.  Rewriting only
   * lhs-rhs can erase the affine numerator shared by two exact remainder
   * encodings before either encoding is recognized. */
  if (has_rounding && !constant_difference_normalize_operands(ctx, bounds, &lhs,
                                                              &rhs, &attempt))
    goto finish;

  attempt.ok = bounds_constant_delta_query_detail(
      ctx, bounds, lhs, rhs, true, &attempt.result, &attempt.invalid,
      &attempt.delta_limited, &attempt.delta_oom);
  attempt.oom = attempt.delta_oom || (!old_oom && bounds->oom);
  attempt.limited =
      attempt.delta_limited || bounds_query_limited_since(bounds, transport);
  if (!attempt.ok && !attempt.oom && !attempt.limited && !attempt.invalid &&
      has_rounding) {
    /* Projection recognizes source-level truncating-remainder protocols.  A
     * useful partial normalization must not hide that independent proof
     * strategy when the normalized direct proof remains inconclusive. */
    constant_difference_try_projection(ctx, bounds, original_lhs, original_rhs,
                                       transport, old_oom, &attempt);
  }

finish:
  attempt.oom = attempt.oom || (!old_oom && bounds->oom);
  status = constant_difference_query_status(
      attempt.oom, attempt.invalid, attempt.limited && !attempt.ok, attempt.ok,
      attempt.result, delta, matched);
  if (!old_oom && bounds->oom)
    bounds_store_invalidate_reads(bounds);
  bounds->oom = old_oom;
  ixs_arena_restore(&ctx->scratch, mark);
  return status;
}

static ixs_fact_check_result fact_check_result(ixs_fact_query_status status,
                                               ixs_check_result check) {
  ixs_fact_check_result result;
  result.status = status;
  result.check = check;
  return result;
}

static ixs_fact_query_status
facts_status_from_equivalence(equivalence_query_status status) {
  switch (status) {
  case EQUIVALENCE_QUERY_COMPLETE:
    return IXS_FACT_QUERY_COMPLETE;
  case EQUIVALENCE_QUERY_LIMITED:
    return IXS_FACT_QUERY_LIMITED;
  case EQUIVALENCE_QUERY_INVALID:
    return IXS_FACT_QUERY_INVALID;
  case EQUIVALENCE_QUERY_OOM:
    return IXS_FACT_QUERY_OOM;
  }
  return IXS_FACT_QUERY_INVALID;
}

static ixs_fact_check_result facts_query_check_predicate(ixs_facts *facts,
                                                         ixs_node *predicate) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_node *simplified;
  ixs_fact_check_result result = {IXS_FACT_QUERY_INVALID, IXS_CHECK_UNKNOWN};
  bool predicate_limited = false;
  bool simplify_limited = false;
  bool query_held = false;
  if (!facts_store_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "predicate");
  if (!facts_store_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "predicate: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, predicate, "predicate"))
    goto cleanup;
  if (!ixs_node_is_pred_kind(predicate)) {
    ixs_ctx_push_error(ctx, "predicate: expression is not a predicate tree");
    goto cleanup;
  }
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(&facts->bounds, predicate, &query_held)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }

  /* The predicate engine owns proof semantics, including reflexive equality
   * as a totality witness.  Simplification remains a fallback for predicates
   * whose original form is inconclusive. */
  result.check =
      bounds_predicate_eval(&facts->bounds, predicate, &predicate_limited);
  if (!predicate_limited && result.check == IXS_CHECK_UNKNOWN)
    result.check = bounds_predicate_implication(&facts->bounds, predicate,
                                                &predicate_limited);
  if (predicate_limited) {
    result.status = IXS_FACT_QUERY_LIMITED;
    goto cleanup;
  }
  if (result.check != IXS_CHECK_UNKNOWN) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }

  mark = ixs_arena_save(&ctx->scratch);
  simplified = simp_simplify_bounds_status(ctx, predicate, &facts->bounds,
                                           &simplify_limited);
  if (simplify_limited) {
    result.status = IXS_FACT_QUERY_LIMITED;
  } else if (!simplified) {
    result.status = IXS_FACT_QUERY_OOM;
  } else if (ixs_node_is_sentinel(simplified)) {
    result.status = IXS_FACT_QUERY_INVALID;
  } else {
    result.check =
        bounds_predicate_eval(&facts->bounds, simplified, &predicate_limited);
    if (!predicate_limited && result.check == IXS_CHECK_UNKNOWN)
      result.check =
          bounds_predicate_bounded_finite_domain(&facts->bounds, predicate);
    result.status =
        predicate_limited ? IXS_FACT_QUERY_LIMITED : IXS_FACT_QUERY_COMPLETE;
  }
  ixs_arena_restore(&ctx->scratch, mark);

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.check = IXS_CHECK_UNKNOWN;
  facts_store_unbind(facts, &binding);
  return result;
}

static ixs_fact_check_result
facts_query_equivalent(ixs_facts *facts, ixs_node *lhs, ixs_node *rhs) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  ixs_node *nodes[2] = {lhs, rhs};
  equivalence_query_status detail;
  bool query_held = false;
  ixs_fact_check_result result = {IXS_FACT_QUERY_INVALID, IXS_CHECK_UNKNOWN};
  if (!facts_store_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "equivalence");
  if (!facts_store_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "equivalence: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, lhs, "equivalence") ||
      !facts_query_node_ok(ctx, rhs, "equivalence"))
    goto cleanup;
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(
          &facts->bounds, bounds_query_select_root(&facts->bounds, nodes, 2),
          &query_held)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  detail = equivalence_query_bound_detail(facts, ctx, lhs, rhs, &result.check);
  result.status = facts_status_from_equivalence(detail);

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.check = IXS_CHECK_UNKNOWN;
  facts_store_unbind(facts, &binding);
  return result;
}

typedef struct {
  ixs_session_binding binding;
  ixs_facts *facts;
  ixs_ctx *ctx;
  ixs_arena_mark scratch_mark;
  ixs_arena_mark diag_mark;
  const char **saved_errors;
  size_t saved_nerrors;
  size_t saved_errors_cap;
  facts_read_query_scope read_scope;
  ixs_fact_query_status status;
  bool bound;
  bool active;
  bool query_held;
} algebra_query_scope;

static bool algebra_query_begin(ixs_facts *facts, ixs_node *const *nodes,
                                size_t nnodes, const char *query,
                                bool outputs_ok, const char *output_error,
                                algebra_query_scope *scope) {
  size_t i;
  memset(scope, 0, sizeof(*scope));
  scope->status = IXS_FACT_QUERY_INVALID;
  if (!facts_store_bind(facts, &scope->binding, &scope->ctx))
    return false;
  scope->facts = facts;
  scope->bound = true;
  facts_read_query_begin(&scope->read_scope, &facts->bounds, scope->ctx, query);
  if (!facts_store_ready(facts)) {
    scope->status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(scope->ctx, "%s: fact set is unusable", query);
    goto fail;
  }
  if (!outputs_ok) {
    ixs_ctx_push_error(scope->ctx, "%s: %s", query, output_error);
    goto fail;
  }
  for (i = 0; i < nnodes; i++) {
    if (!facts_query_node_ok(scope->ctx, nodes[i], query))
      goto fail;
  }
  if (ixs_bounds_has_empty(&facts->bounds)) {
    scope->status = IXS_FACT_QUERY_COMPLETE;
    goto fail;
  }
  if (!ixs_bounds_query_hold_begin(
          &facts->bounds,
          bounds_query_select_root(&facts->bounds, nodes, nnodes),
          &scope->query_held)) {
    scope->status = IXS_FACT_QUERY_COMPLETE;
    goto fail;
  }
  scope->status = IXS_FACT_QUERY_COMPLETE;
  return true;

fail:
  if (scope->query_held) {
    ixs_bounds_query_hold_end(&facts->bounds);
    scope->query_held = false;
  }
  scope->status = facts_read_query_finish(&scope->read_scope, scope->status);
  facts_store_unbind(scope->facts, &scope->binding);
  scope->bound = false;
  return false;
}

static void algebra_query_start(algebra_query_scope *scope) {
  scope->scratch_mark = ixs_arena_save(&scope->ctx->scratch);
  scope->diag_mark = ixs_arena_save(&scope->ctx->diag);
  scope->saved_errors = scope->ctx->errors;
  scope->saved_nerrors = scope->ctx->nerrors;
  scope->saved_errors_cap = scope->ctx->errors_cap;
  scope->active = true;
}

static bool algebra_query_finish(algebra_query_scope *scope, bool success) {
  if (scope->active) {
    ixs_arena_restore(&scope->ctx->scratch, scope->scratch_mark);
    ixs_arena_restore(&scope->ctx->diag, scope->diag_mark);
    scope->ctx->errors = scope->saved_errors;
    scope->ctx->nerrors = scope->saved_nerrors;
    scope->ctx->errors_cap = scope->saved_errors_cap;
  }
  if (scope->query_held) {
    ixs_bounds_query_hold_end(&scope->facts->bounds);
    scope->query_held = false;
  }
  if (scope->read_scope.active)
    scope->status = facts_read_query_finish(&scope->read_scope, scope->status);
  if (scope->status != IXS_FACT_QUERY_COMPLETE)
    success = false;
  if (scope->bound)
    facts_store_unbind(scope->facts, &scope->binding);
  return success;
}

static ixs_node *algebra_query_normalize(algebra_query_scope *scope,
                                         ixs_node *expr) {
  bool limited = false;
  expr = simp_simplify_bounds_status(scope->ctx, expr, &scope->facts->bounds,
                                     &limited);
  if (limited) {
    scope->status = IXS_FACT_QUERY_LIMITED;
    return NULL;
  }
  if (!expr) {
    scope->status = IXS_FACT_QUERY_OOM;
    return NULL;
  }
  if (ixs_node_is_sentinel(expr)) {
    scope->status = IXS_FACT_QUERY_INVALID;
    return NULL;
  }
  expr = expand_impl(scope->ctx, expr);
  if (!expr) {
    scope->status = IXS_FACT_QUERY_OOM;
    return NULL;
  }
  if (ixs_node_is_sentinel(expr)) {
    scope->status = IXS_FACT_QUERY_INVALID;
    return NULL;
  }
  limited = false;
  expr = simp_simplify_bounds_status(scope->ctx, expr, &scope->facts->bounds,
                                     &limited);
  if (limited) {
    scope->status = IXS_FACT_QUERY_LIMITED;
    return NULL;
  }
  if (!expr) {
    scope->status = IXS_FACT_QUERY_OOM;
    return NULL;
  }
  if (ixs_node_is_sentinel(expr)) {
    scope->status = IXS_FACT_QUERY_INVALID;
    return NULL;
  }
  return expr;
}

static bool algebra_query_defined(algebra_query_scope *scope, ixs_node *expr) {
  bool oom = false;
  bool limited = false;
  ixs_check_result result =
      bounds_defined_check_detail(&scope->facts->bounds, expr, &oom, &limited);
  if (oom)
    scope->status = IXS_FACT_QUERY_OOM;
  else if (limited)
    scope->status = IXS_FACT_QUERY_LIMITED;
  return result == IXS_CHECK_TRUE && scope->status == IXS_FACT_QUERY_COMPLETE;
}

static bool algebra_contains_node(algebra_query_scope *scope, ixs_node *root,
                                  ixs_node *target, bool *contains) {
  ixs_arena_mark mark = ixs_arena_save(&scope->ctx->scratch);
  query_node_set visited;
  ixs_node **stack = NULL;
  size_t stack_count = 0;
  size_t stack_capacity = 0;
  bool ok = false;
  *contains = false;
  memset(&visited, 0, sizeof(visited));
  if (!root || !target) {
    scope->status = IXS_FACT_QUERY_INVALID;
    goto cleanup;
  }
  if (!query_node_stack_push(&scope->ctx->scratch, &stack, &stack_count,
                             &stack_capacity, root)) {
    scope->status = IXS_FACT_QUERY_OOM;
    goto cleanup;
  }
  while (stack_count > 0) {
    ixs_node *node = stack[--stack_count];
    uint32_t nchildren;
    uint32_t child;
    bool inserted;
    if (!node || !query_node_set_insert(&scope->ctx->scratch, &visited, node,
                                        &inserted)) {
      scope->status = node ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
      goto cleanup;
    }
    if (!inserted)
      continue;
    if (node == target) {
      *contains = true;
      ok = true;
      goto cleanup;
    }
    if (!defined_child_count(node, &nchildren)) {
      scope->status = IXS_FACT_QUERY_INVALID;
      goto cleanup;
    }
    for (child = 0; child < nchildren; child++) {
      if (!query_node_stack_push(&scope->ctx->scratch, &stack, &stack_count,
                                 &stack_capacity,
                                 defined_child_at(node, child))) {
        scope->status = IXS_FACT_QUERY_OOM;
        goto cleanup;
      }
    }
  }
  ok = true;

cleanup:
  ixs_arena_restore(&scope->ctx->scratch, mark);
  return ok;
}

static bool algebra_scalar_symbol(ixs_ctx *ctx, ixs_node *expr,
                                  ixs_node *symbol, ixs_node **coefficient) {
  if (expr == symbol) {
    *coefficient = ctx->node_one;
    return true;
  }
  if (expr->tag == IXS_MUL && expr->u.mul.nfactors == 1 &&
      expr->u.mul.factors[0].base == symbol &&
      expr->u.mul.factors[0].exp == 1) {
    *coefficient = expr->u.mul.coeff;
    return true;
  }
  return false;
}

static bool algebra_affine_extract(algebra_query_scope *scope, ixs_node *expr,
                                   ixs_node *symbol, ixs_node **coefficient,
                                   ixs_node **residual) {
  ixs_ctx *ctx = scope->ctx;
  ixs_node *symbol_coeff;
  bool contains;
  uint32_t i;

  if (algebra_scalar_symbol(ctx, expr, symbol, &symbol_coeff)) {
    *coefficient = symbol_coeff;
    *residual = ctx->node_zero;
    return true;
  }
  if (expr->tag != IXS_ADD) {
    if (!algebra_contains_node(scope, expr, symbol, &contains) || contains) {
      return false;
    }
    *coefficient = ctx->node_zero;
    *residual = expr;
    return true;
  }

  *coefficient = ctx->node_zero;
  *residual = expr->u.add.coeff;
  for (i = 0; i < expr->u.add.nterms; i++) {
    ixs_node *term = expr->u.add.terms[i].term;
    ixs_node *term_coeff = expr->u.add.terms[i].coeff;
    ixs_node *scaled;
    if (algebra_scalar_symbol(ctx, term, symbol, &symbol_coeff)) {
      scaled = simp_mul(ctx, term_coeff, symbol_coeff);
      if (!scaled || ixs_node_is_sentinel(scaled)) {
        scope->status = !scaled ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
        return false;
      }
      *coefficient = simp_add(ctx, *coefficient, scaled);
      if (!*coefficient || ixs_node_is_sentinel(*coefficient)) {
        scope->status =
            !*coefficient ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
        return false;
      }
      continue;
    }
    if (!algebra_contains_node(scope, term, symbol, &contains) || contains) {
      return false;
    }
    scaled = simp_mul(ctx, term_coeff, term);
    if (!scaled || ixs_node_is_sentinel(scaled)) {
      scope->status = !scaled ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
      return false;
    }
    *residual = simp_add(ctx, *residual, scaled);
    if (!*residual || ixs_node_is_sentinel(*residual)) {
      scope->status = !*residual ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
      return false;
    }
  }
  return ixs_node_is_const(*coefficient);
}

static ixs_constant_difference_result
facts_query_constant_difference(ixs_facts *facts, ixs_node *lhs,
                                ixs_node *rhs) {
  ixs_constant_difference_result result = {IXS_FACT_QUERY_INVALID, false, 0};
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  ixs_node *nodes[2] = {lhs, rhs};
  ixs_fact_query_status detail;
  bool query_held = false;
  if (!facts_store_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx,
                         "constant difference");
  if (!facts_store_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "constant difference: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, lhs, "constant difference") ||
      !facts_query_node_ok(ctx, rhs, "constant difference"))
    goto cleanup;
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(
          &facts->bounds, bounds_query_select_root(&facts->bounds, nodes, 2),
          &query_held)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  {
    ixs_arena_mark diag_mark = ixs_arena_save(&ctx->diag);
    const char **saved_errors = ctx->errors;
    size_t saved_nerrors = ctx->nerrors;
    size_t saved_errors_cap = ctx->errors_cap;
    detail = constant_difference_query_bound_detail(
        ctx, &facts->bounds, lhs, rhs, &result.difference, &result.available);
    ixs_arena_restore(&ctx->diag, diag_mark);
    ctx->errors = saved_errors;
    ctx->nerrors = saved_nerrors;
    ctx->errors_cap = saved_errors_cap;
  }
  result.status = detail;

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE) {
    result.available = false;
    result.difference = 0;
  }
  facts_store_unbind(facts, &binding);
  return result;
}

static ixs_affine_decomposition_result
facts_query_affine_decompose(ixs_facts *facts, ixs_node *expr,
                             ixs_node *symbol) {
  algebra_query_scope scope;
  ixs_affine_decomposition_result result = {IXS_FACT_QUERY_INVALID, false, NULL,
                                            NULL};
  ixs_node *nodes[2] = {expr, symbol};
  if (!algebra_query_begin(facts, nodes, 2, "affine decomposition", true, NULL,
                           &scope)) {
    result.status = scope.status;
    return result;
  }
  if (symbol->tag != IXS_SYM) {
    ixs_ctx_push_error(scope.ctx,
                       "affine decomposition: expression must be a symbol");
    scope.status = IXS_FACT_QUERY_INVALID;
    (void)algebra_query_finish(&scope, false);
    result.status = scope.status;
    return result;
  }
  algebra_query_start(&scope);
  if (!algebra_query_defined(&scope, expr))
    goto cleanup;
  expr = algebra_query_normalize(&scope, expr);
  if (!expr)
    goto cleanup;
  result.available = algebra_affine_extract(&scope, expr, symbol,
                                            (ixs_node **)&result.coefficient,
                                            (ixs_node **)&result.residual);

cleanup:
  (void)algebra_query_finish(&scope, result.available);
  result.status = scope.status;
  if (result.status != IXS_FACT_QUERY_COMPLETE) {
    result.available = false;
    result.coefficient = NULL;
    result.residual = NULL;
  }
  return result;
}

static ixs_node *algebra_finite_difference(algebra_query_scope *scope,
                                           ixs_node *expr, ixs_node *symbol,
                                           ixs_node *step) {
  ixs_node *shifted_symbol;
  ixs_node *shifted_expr;
  ixs_node *result;
  bool contains;
  if (!algebra_query_defined(scope, expr) ||
      !algebra_query_defined(scope, step))
    return NULL;
  if (!algebra_contains_node(scope, step, symbol, &contains) || contains)
    return NULL;
  shifted_symbol = simp_add(scope->ctx, symbol, step);
  if (!shifted_symbol) {
    scope->status = IXS_FACT_QUERY_OOM;
    return NULL;
  }
  if (ixs_node_is_sentinel(shifted_symbol)) {
    scope->status = IXS_FACT_QUERY_INVALID;
    return NULL;
  }
  shifted_expr = simp_subs(scope->ctx, expr, symbol, shifted_symbol);
  if (!shifted_expr) {
    scope->status = IXS_FACT_QUERY_OOM;
    return NULL;
  }
  if (ixs_node_is_sentinel(shifted_expr)) {
    scope->status = IXS_FACT_QUERY_INVALID;
    return NULL;
  }
  if (!algebra_query_defined(scope, shifted_expr))
    return NULL;
  result = simp_sub(scope->ctx, shifted_expr, expr);
  if (!result) {
    scope->status = IXS_FACT_QUERY_OOM;
    return NULL;
  }
  if (ixs_node_is_sentinel(result)) {
    scope->status = IXS_FACT_QUERY_INVALID;
    return NULL;
  }
  return algebra_query_normalize(scope, result);
}

static ixs_finite_difference_result
facts_query_finite_difference(ixs_facts *facts, ixs_node *expr,
                              ixs_node *symbol, ixs_node *step) {
  algebra_query_scope scope;
  ixs_finite_difference_result query_result = {IXS_FACT_QUERY_INVALID, false,
                                               NULL};
  ixs_node *nodes[3] = {expr, symbol, step};
  ixs_node *result = NULL;
  if (!algebra_query_begin(facts, nodes, 3, "finite difference", true, NULL,
                           &scope)) {
    query_result.status = scope.status;
    return query_result;
  }
  if (symbol->tag != IXS_SYM) {
    ixs_ctx_push_error(scope.ctx,
                       "finite difference: expression must be a symbol");
    scope.status = IXS_FACT_QUERY_INVALID;
    (void)algebra_query_finish(&scope, false);
    query_result.status = scope.status;
    return query_result;
  }
  algebra_query_start(&scope);
  result = algebra_finite_difference(&scope, expr, symbol, step);
  query_result.available = result != NULL;
  (void)algebra_query_finish(&scope, query_result.available);
  query_result.status = scope.status;
  if (query_result.status == IXS_FACT_QUERY_COMPLETE && query_result.available)
    query_result.difference = result;
  else {
    query_result.available = false;
    query_result.difference = NULL;
  }
  return query_result;
}

static ixs_additive_constant_result
facts_query_split_additive_constant(ixs_facts *facts, ixs_node *expr) {
  algebra_query_scope scope;
  ixs_additive_constant_result query_result = {IXS_FACT_QUERY_INVALID, false,
                                               NULL, 0};
  ixs_node *nodes[1] = {expr};
  ixs_node *result_residual = NULL;
  int64_t result_constant = 0;
  int64_t q;
  bool ok = false;
  if (!algebra_query_begin(facts, nodes, 1, "additive constant", true, NULL,
                           &scope)) {
    query_result.status = scope.status;
    return query_result;
  }
  algebra_query_start(&scope);
  if (!algebra_query_defined(&scope, expr))
    goto cleanup;
  expr = algebra_query_normalize(&scope, expr);
  if (!expr)
    goto cleanup;
  if (ixs_node_is_const(expr)) {
    ixs_node_get_rat(expr, &result_constant, &q);
    if (q != 1)
      goto cleanup;
    result_residual = scope.ctx->node_zero;
  } else if (expr->tag == IXS_ADD) {
    ixs_algebra_status status;
    ixs_node_get_rat(expr->u.add.coeff, &result_constant, &q);
    if (q != 1)
      goto cleanup;
    status =
        ixs_additive_row_without_constant(scope.ctx, expr, &result_residual);
    if (status != IXS_ALGEBRA_MATCH) {
      scope.status = status == IXS_ALGEBRA_OOM ? IXS_FACT_QUERY_OOM
                                               : IXS_FACT_QUERY_INVALID;
      goto cleanup;
    }
  } else {
    result_residual = expr;
  }
  ok = true;

cleanup:
  (void)algebra_query_finish(&scope, ok);
  query_result.status = scope.status;
  query_result.available = ok && scope.status == IXS_FACT_QUERY_COMPLETE;
  if (query_result.available) {
    query_result.residual = result_residual;
    query_result.constant = result_constant;
  }
  return query_result;
}

static ixs_fact_check_result facts_query_check(ixs_facts *facts,
                                               ixs_node *expr) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  ixs_fact_check_result result = {IXS_FACT_QUERY_INVALID, IXS_CHECK_UNKNOWN};
  if (!facts_store_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "check");
  if (!facts_store_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "check: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, expr, "check"))
    goto cleanup;
  if (!ixs_node_is_known_true(expr) && !ixs_node_is_known_false(expr) &&
      (expr->tag != IXS_CMP || !ixs_node_is_zero(expr->u.binary.rhs))) {
    ixs_ctx_push_error(ctx,
                       "check: expression must be a normalized comparison");
    goto cleanup;
  }
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  result.check = ixs_bounds_check_query(&facts->bounds, expr);
  result.status = IXS_FACT_QUERY_COMPLETE;

cleanup:
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.check = IXS_CHECK_UNKNOWN;
  facts_store_unbind(facts, &binding);
  return result;
}

static ixs_fact_check_result facts_query_check_integer_valued(ixs_facts *facts,
                                                              ixs_node *expr) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  bool query_held = false;
  ixs_fact_check_result result = {IXS_FACT_QUERY_INVALID, IXS_CHECK_UNKNOWN};
  if (!facts_store_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "integer valued");
  if (!facts_store_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "integer valued: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, expr, "integer valued"))
    goto cleanup;
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(&facts->bounds, expr, &query_held)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  result.check = ixs_bounds_check_integer_valued(&facts->bounds, expr);
  result.status = IXS_FACT_QUERY_COMPLETE;

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.check = IXS_CHECK_UNKNOWN;
  facts_store_unbind(facts, &binding);
  return result;
}

static ixs_fact_check_result facts_query_check_defined(ixs_facts *facts,
                                                       ixs_node *expr) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  bool oom = false;
  bool limited = false;
  bool query_held = false;
  ixs_fact_check_result result = {IXS_FACT_QUERY_INVALID, IXS_CHECK_UNKNOWN};
  if (!facts_store_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "defined");
  if (!facts_store_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "defined: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, expr, "defined"))
    goto cleanup;
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(&facts->bounds, expr, &query_held)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  result.check =
      bounds_defined_check_detail(&facts->bounds, expr, &oom, &limited);
  result.status = oom       ? IXS_FACT_QUERY_OOM
                  : limited ? IXS_FACT_QUERY_LIMITED
                            : IXS_FACT_QUERY_COMPLETE;

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.check = IXS_CHECK_UNKNOWN;
  facts_store_unbind(facts, &binding);
  return result;
}

static ixs_fact_check_result
facts_query_check_divisible(ixs_facts *facts, ixs_node *expr, int64_t modulus) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  bool query_held = false;
  ixs_fact_check_result result = {IXS_FACT_QUERY_INVALID, IXS_CHECK_UNKNOWN};
  if (!facts_store_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "divisibility");
  if (!facts_store_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "divisibility: fact set is unusable");
    goto cleanup;
  }
  if (modulus == 0) {
    ixs_ctx_push_error(ctx, "divisibility: modulus must be nonzero");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, expr, "divisibility"))
    goto cleanup;
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(&facts->bounds, expr, &query_held)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  result.check = ixs_bounds_check_divisible(&facts->bounds, expr, modulus);
  result.status = IXS_FACT_QUERY_COMPLETE;

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.check = IXS_CHECK_UNKNOWN;
  facts_store_unbind(facts, &binding);
  return result;
}

static ixs_exact_divide_result
exact_divide_result(ixs_exact_divide_status status, ixs_node *quotient) {
  ixs_exact_divide_result result;
  result.status = status;
  result.quotient = quotient;
  return result;
}

static ixs_exact_divide_result
exact_divide_failure(ixs_ctx *ctx, ixs_exact_divide_status status,
                     const char *message) {
  if (ctx && message)
    ixs_ctx_push_error(ctx, "exact divide: %s", message);
  return exact_divide_result(status, NULL);
}

static ixs_fact_query_status
exact_divide_simplify_facts(ixs_facts *facts, ixs_ctx *ctx, ixs_node *expr,
                            ixs_node **simplified) {
  /* Fact simplification is a proof probe; discard scratch and diagnostics. */
  ixs_arena_mark scratch_mark = ixs_arena_save(&ctx->scratch);
  ixs_arena_mark diag_mark = ixs_arena_save(&ctx->diag);
  const char **saved_errors = ctx->errors;
  size_t saved_nerrors = ctx->nerrors;
  size_t saved_errors_cap = ctx->errors_cap;
  bool old_oom = facts->bounds.oom;
  bool limited = false;
  ixs_node *result =
      simp_simplify_bounds_status(ctx, expr, &facts->bounds, &limited);
  ixs_fact_query_status status = IXS_FACT_QUERY_COMPLETE;

  *simplified = NULL;
  if (limited)
    status = IXS_FACT_QUERY_LIMITED;
  else if (!result || (!old_oom && facts->bounds.oom))
    status = IXS_FACT_QUERY_OOM;
  else if (ixs_node_is_sentinel(result))
    status = IXS_FACT_QUERY_INVALID;
  else
    *simplified = result;
  if (status == IXS_FACT_QUERY_OOM)
    bounds_store_invalidate_reads(&facts->bounds);
  facts->bounds.oom = old_oom;
  ixs_arena_restore(&ctx->scratch, scratch_mark);
  ixs_arena_restore(&ctx->diag, diag_mark);
  ctx->errors = saved_errors;
  ctx->nerrors = saved_nerrors;
  ctx->errors_cap = saved_errors_cap;
  return status;
}

static bool exact_divide_validate_request(ixs_facts *facts, ixs_ctx *ctx,
                                          ixs_node *expr, int64_t divisor,
                                          ixs_exact_divide_result *result) {
  if (!facts_store_ready(facts)) {
    *result = exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR,
                                   "fact set is unusable");
    return false;
  }
  if (!expr) {
    *result =
        exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR, "NULL expression");
    return false;
  }
  if (ixs_node_is_sentinel(expr)) {
    *result = exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR,
                                   "sentinel expression is not accepted");
    return false;
  }
  if (!ixs_ctx_owns_node(ctx, expr)) {
    *result = exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR,
                                   "expression belongs to a different context");
    return false;
  }
  if (divisor == 0) {
    *result = exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR,
                                   "divisor must be nonzero");
    return false;
  }
  return true;
}

static bool exact_divide_simplify_input(ixs_facts *facts, ixs_ctx *ctx,
                                        ixs_node *input, ixs_node **simplified,
                                        ixs_exact_divide_result *result) {
  ixs_fact_query_status status =
      exact_divide_simplify_facts(facts, ctx, input, simplified);
  if (status == IXS_FACT_QUERY_COMPLETE)
    return true;
  if (status == IXS_FACT_QUERY_OOM)
    *result =
        exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR, "out of memory");
  else if (status == IXS_FACT_QUERY_LIMITED)
    *result = exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR,
                                   "resource limit exceeded");
  else
    *result = exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR,
                                   "simplification produced invalid state");
  return false;
}

static bool exact_divide_input_defined(ixs_facts *facts, ixs_ctx *ctx,
                                       ixs_node *expr,
                                       ixs_exact_divide_result *result) {
  bool old_bounds_oom = facts->bounds.oom;
  bool defined_oom = false;
  bool defined_limited = false;
  ixs_check_result defined;

  if (ixs_node_is_known_total(expr))
    return true;
  defined = bounds_defined_check_detail(&facts->bounds, expr, &defined_oom,
                                        &defined_limited);
  if (defined_oom) {
    if (!old_bounds_oom && facts->bounds.oom) {
      bounds_store_invalidate_reads(&facts->bounds);
      facts->bounds.oom = old_bounds_oom;
    }
    *result =
        exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR, "out of memory");
    return false;
  }
  if (defined_limited) {
    *result = exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR,
                                   "resource limit exceeded");
    return false;
  }
  if (defined != IXS_CHECK_TRUE) {
    *result = exact_divide_result(IXS_EXACT_DIVIDE_UNKNOWN, NULL);
    return false;
  }
  return true;
}

static bool exact_divide_proven(ixs_facts *facts, ixs_ctx *ctx, ixs_node *expr,
                                int64_t divisor,
                                ixs_exact_divide_result *result) {
  bool old_bounds_oom = facts->bounds.oom;
  ixs_check_result proof =
      ixs_bounds_check_divisible(&facts->bounds, expr, divisor);
  if (facts->bounds.oom) {
    if (!old_bounds_oom)
      bounds_store_invalidate_reads(&facts->bounds);
    facts->bounds.oom = old_bounds_oom;
    *result =
        exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR, "out of memory");
    return false;
  }
  if (proof == IXS_CHECK_UNKNOWN) {
    *result = exact_divide_result(IXS_EXACT_DIVIDE_UNKNOWN, NULL);
    return false;
  }
  if (proof == IXS_CHECK_FALSE) {
    *result = exact_divide_result(IXS_EXACT_DIVIDE_NOT_EXACT, NULL);
    return false;
  }
  return true;
}

static ixs_node *
exact_divide_piecewise_quotient(ixs_ctx *ctx, ixs_node *expr, ixs_node *divisor,
                                ixs_fact_query_status *status) {
  ixs_arena_mark mark = ixs_arena_save(&ctx->scratch);
  ixs_node **values = NULL;
  ixs_node **conditions = NULL;
  ixs_node *quotient = NULL;
  size_t ncases = expr->u.pw.ncases;
  size_t i;

  if (ncases == 0u || !expr->u.pw.cases ||
      ncases > SIZE_MAX / sizeof(*values)) {
    *status = IXS_FACT_QUERY_INVALID;
    goto cleanup;
  }
  values =
      ixs_arena_alloc(&ctx->scratch, ncases * sizeof(*values), sizeof(void *));
  conditions = ixs_arena_alloc(&ctx->scratch, ncases * sizeof(*conditions),
                               sizeof(void *));
  if (!values || !conditions) {
    *status = IXS_FACT_QUERY_OOM;
    goto cleanup;
  }
  for (i = 0; i < ncases; i++) {
    values[i] = simp_div(ctx, expr->u.pw.cases[i].value, divisor);
    conditions[i] = expr->u.pw.cases[i].cond;
    if (!values[i]) {
      *status = IXS_FACT_QUERY_OOM;
      goto cleanup;
    }
    if (ixs_node_is_sentinel(values[i])) {
      *status = IXS_FACT_QUERY_INVALID;
      goto cleanup;
    }
  }
  quotient = simp_pw(ctx, (uint32_t)ncases, values, conditions);
  if (!quotient)
    *status = IXS_FACT_QUERY_OOM;
  else if (ixs_node_is_sentinel(quotient)) {
    *status = IXS_FACT_QUERY_INVALID;
    quotient = NULL;
  }

cleanup:
  ixs_arena_restore(&ctx->scratch, mark);
  return quotient;
}

static ixs_exact_divide_result
exact_divide_build_quotient(ixs_ctx *ctx, ixs_node *expr, int64_t divisor) {
  ixs_node *divisor_node = ixs_node_int(ctx, divisor);
  ixs_node *quotient;
  ixs_fact_query_status status = IXS_FACT_QUERY_COMPLETE;
  if (!divisor_node)
    return exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR, "out of memory");
  if (expr->tag == IXS_PIECEWISE) {
    quotient =
        exact_divide_piecewise_quotient(ctx, expr, divisor_node, &status);
  } else {
    quotient = simp_div(ctx, expr, divisor_node);
    if (!quotient)
      status = IXS_FACT_QUERY_OOM;
  }
  if (!quotient && status == IXS_FACT_QUERY_OOM)
    return exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR, "out of memory");
  if (!quotient || status == IXS_FACT_QUERY_INVALID ||
      ixs_node_is_sentinel(quotient))
    return exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR,
                                "quotient is not representable");
  quotient = expand_impl(ctx, quotient);
  if (!quotient)
    return exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR, "out of memory");
  if (ixs_node_is_sentinel(quotient))
    return exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR,
                                "quotient expansion failed");
  return exact_divide_result(IXS_EXACT_DIVIDE_PROVEN, quotient);
}

static ixs_exact_divide_result
exact_divide_finish_read_query(facts_read_query_scope *scope,
                               ixs_exact_divide_result result) {
  ixs_fact_query_status status = IXS_FACT_QUERY_COMPLETE;
  if (result.status == IXS_EXACT_DIVIDE_ERROR)
    status = IXS_FACT_QUERY_INVALID;
  status = facts_read_query_finish(scope, status);
  if (status != IXS_FACT_QUERY_COMPLETE)
    return exact_divide_result(IXS_EXACT_DIVIDE_ERROR, NULL);
  return result;
}

ixs_exact_divide_result
ixs_try_exact_divide_facts(ixs_facts *facts, ixs_node *expr, int64_t divisor) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  bool query_held = false;
  ixs_exact_divide_result result =
      exact_divide_result(IXS_EXACT_DIVIDE_ERROR, NULL);

  if (!facts_store_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "exact divide");
  if (!exact_divide_validate_request(facts, ctx, expr, divisor, &result))
    goto cleanup;
  if (!ixs_bounds_query_hold_begin(&facts->bounds, expr, &query_held)) {
    result =
        facts->bounds.oom
            ? exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR, "out of memory")
            : exact_divide_result(IXS_EXACT_DIVIDE_UNKNOWN, NULL);
    goto cleanup;
  }
  if (!exact_divide_input_defined(facts, ctx, expr, &result))
    goto cleanup;
  if (!exact_divide_simplify_input(facts, ctx, expr, &expr, &result))
    goto cleanup;
  if (!exact_divide_proven(facts, ctx, expr, divisor, &result))
    goto cleanup;
  result = exact_divide_build_quotient(ctx, expr, divisor);
  if (result.status == IXS_EXACT_DIVIDE_PROVEN) {
    ixs_node *quotient = result.quotient;
    if (!exact_divide_simplify_input(facts, ctx, quotient, &result.quotient,
                                     &result))
      goto cleanup;
  }

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result = exact_divide_finish_read_query(&read_scope, result);
  facts_store_unbind(facts, &binding);
  return result;
}

static ixs_pow2_fact bounds_pow2_fact_from_int64(int64_t value) {
  uint64_t u;
  if (value == 0)
    return IXS_POW2_OR_ZERO;
  if (value < 0)
    return IXS_POW2_UNKNOWN;
  u = (uint64_t)value;
  return (u & (u - 1u)) == 0 ? IXS_POW2_POSITIVE : IXS_POW2_UNKNOWN;
}

static ixs_pow2_query_result facts_query_get_pow2(ixs_facts *facts,
                                                  ixs_node *expr) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  ixs_bitfacts bits;
  ixs_interval iv;
  int64_t exact;
  bool defined_oom = false;
  bool defined_limited = false;
  bool query_held = false;
  ixs_pow2_query_result result = {IXS_FACT_QUERY_INVALID, IXS_POW2_UNKNOWN};
  if (!facts_store_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "power of two");
  if (!facts_store_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "power of two: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, expr, "power of two"))
    goto cleanup;
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(&facts->bounds, expr, &query_held)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (bounds_defined_check_detail(&facts->bounds, expr, &defined_oom,
                                  &defined_limited) != IXS_CHECK_TRUE ||
      ixs_bounds_check_integer_valued(&facts->bounds, expr) != IXS_CHECK_TRUE) {
    result.status = defined_oom       ? IXS_FACT_QUERY_OOM
                    : defined_limited ? IXS_FACT_QUERY_LIMITED
                                      : IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (ixs_bounds_get_bitfacts(&facts->bounds, expr, &bits))
    result.fact = bits.pow2;
  if (result.fact == IXS_POW2_UNKNOWN) {
    iv = ixs_bounds_get(&facts->bounds, expr);
    if (ixs_interval_is_point_int(iv, &exact))
      result.fact = bounds_pow2_fact_from_int64(exact);
  }
  result.status = IXS_FACT_QUERY_COMPLETE;

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.fact = IXS_POW2_UNKNOWN;
  facts_store_unbind(facts, &binding);
  return result;
}

static ixs_known_bits_query_result facts_query_get_known_bits(ixs_facts *facts,
                                                              ixs_node *expr) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  ixs_bitfacts bits = {0, 0, IXS_POW2_UNKNOWN};
  bool defined_oom = false;
  bool defined_limited = false;
  bool query_held = false;
  ixs_known_bits_query_result result;
  result.status = IXS_FACT_QUERY_INVALID;
  result.bits.known_zero = 0;
  result.bits.known_one = 0;
  result.bits.pow2 = IXS_POW2_UNKNOWN;
  if (!facts_store_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "known bits");
  if (!facts_store_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "known bits: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, expr, "known bits") ||
      ixs_bounds_has_empty(&facts->bounds)) {
    if (!ixs_bounds_has_empty(&facts->bounds))
      goto cleanup;
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(&facts->bounds, expr, &query_held)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }

  if (bounds_defined_check_detail(&facts->bounds, expr, &defined_oom,
                                  &defined_limited) == IXS_CHECK_TRUE &&
      ixs_bounds_check_integer_valued(&facts->bounds, expr) == IXS_CHECK_TRUE)
    (void)ixs_bounds_get_bitfacts(&facts->bounds, expr, &bits);
  result.status = defined_oom       ? IXS_FACT_QUERY_OOM
                  : defined_limited ? IXS_FACT_QUERY_LIMITED
                                    : IXS_FACT_QUERY_COMPLETE;
  result.bits.known_zero = bits.known_zero;
  result.bits.known_one = bits.known_one;
  result.bits.pow2 = bits.pow2;

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE) {
    result.bits.known_zero = 0;
    result.bits.known_one = 0;
    result.bits.pow2 = IXS_POW2_UNKNOWN;
  }
  facts_store_unbind(facts, &binding);
  return result;
}

static ixs_symbol_congruence_result
facts_query_get_symbol_congruence(ixs_facts *facts, ixs_node *symbol) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  ixs_symbol_congruence_result result = {IXS_FACT_QUERY_INVALID, false, 0, 0};
  if (!facts_store_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "symbol congruence");
  if (!facts_store_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "symbol congruence: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, symbol, "symbol congruence") ||
      ixs_bounds_has_empty(&facts->bounds)) {
    if (!ixs_bounds_has_empty(&facts->bounds))
      goto cleanup;
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (symbol->tag != IXS_SYM) {
    ixs_ctx_push_error(ctx, "symbol congruence: expression must be a symbol");
    goto cleanup;
  }
  result.available = bounds_store_get_modrem(&facts->bounds, symbol->u.name,
                                             &result.modulus, &result.residue);
  result.status = IXS_FACT_QUERY_COMPLETE;

cleanup:
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE) {
    result.available = false;
    result.modulus = 0;
    result.residue = 0;
  }
  facts_store_unbind(facts, &binding);
  return result;
}

static ixs_fact_check_result facts_query_check_congruent(ixs_facts *facts,
                                                         ixs_node *expr,
                                                         int64_t modulus,
                                                         int64_t residue) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  bool query_held = false;
  ixs_fact_check_result result =
      fact_check_result(IXS_FACT_QUERY_INVALID, IXS_CHECK_UNKNOWN);
  if (!facts_store_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "congruence");
  if (!facts_store_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "congruence: fact set is unusable");
    goto cleanup;
  }
  if (modulus == 0) {
    ixs_ctx_push_error(ctx, "congruence: modulus must be nonzero");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, expr, "congruence"))
    goto cleanup;
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(&facts->bounds, expr, &query_held)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  result.check =
      ixs_bounds_check_congruent(&facts->bounds, expr, modulus, residue);
  result.status = IXS_FACT_QUERY_COMPLETE;

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.check = IXS_CHECK_UNKNOWN;
  facts_store_unbind(facts, &binding);
  return result;
}

static ixs_range_query_result facts_query_range(ixs_facts *facts,
                                                ixs_node *expr) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  ixs_interval iv;
  ixs_interval truncating_remainder;
  bool defined_oom = false;
  bool defined_limited = false;
  bool query_held = false;
  ixs_check_result integer_valued;
  ixs_algebra_status truncating_status;
  ixs_range_query_result result;
  memset(&result, 0, sizeof(result));
  result.status = IXS_FACT_QUERY_INVALID;
  result.range.lower_q = 1;
  result.range.upper_q = 1;
  if (!facts_store_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "range");
  if (!facts_store_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "range: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, expr, "range"))
    goto cleanup;
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(&facts->bounds, expr, &query_held)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (bounds_defined_check_detail(&facts->bounds, expr, &defined_oom,
                                  &defined_limited) != IXS_CHECK_TRUE) {
    result.status = defined_oom       ? IXS_FACT_QUERY_OOM
                    : defined_limited ? IXS_FACT_QUERY_LIMITED
                                      : IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  result.status = IXS_FACT_QUERY_COMPLETE;
  integer_valued = ixs_bounds_check_integer_valued(&facts->bounds, expr);
  iv = ixs_bounds_get(&facts->bounds, expr);
  if (integer_valued == IXS_CHECK_TRUE) {
    if (!bounds_refine_integral_interval(&facts->bounds, expr,
                                         /*expression_defined=*/true, &iv))
      goto cleanup;
    interval_to_range_result(iv, &result.range);
    result.available = true;
    goto cleanup;
  }
  truncating_status = bounds_get_truncating_remainder_range(
      &facts->bounds, expr, /*expression_defined=*/false,
      &truncating_remainder);
  if (truncating_status == IXS_ALGEBRA_MATCH)
    iv = iv_intersect(iv, truncating_remainder);
  else if (truncating_status >= IXS_ALGEBRA_LIMITED) {
    result.status = truncating_status == IXS_ALGEBRA_OOM ? IXS_FACT_QUERY_OOM
                    : truncating_status == IXS_ALGEBRA_INVALID
                        ? IXS_FACT_QUERY_INVALID
                        : IXS_FACT_QUERY_LIMITED;
    goto cleanup;
  }
  if (!iv.valid || ixs_interval_is_empty(iv))
    goto cleanup;
  interval_to_range_result(iv, &result.range);
  result.available = true;
  result.status = IXS_FACT_QUERY_COMPLETE;

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE) {
    result.available = false;
    memset(&result.range, 0, sizeof(result.range));
    result.range.lower_q = 1;
    result.range.upper_q = 1;
  }
  facts_store_unbind(facts, &binding);
  return result;
}

static void facts_public_output_error(ixs_facts *facts, const char *query,
                                      const char *message) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  if (!facts_store_bind(facts, &binding, &ctx))
    return;
  ixs_ctx_push_error(ctx, "%s: %s", query, message);
  facts_store_unbind(facts, &binding);
}

const ixs_node *ixs_simplify_facts(ixs_facts *facts, const ixs_node *expr) {
  ixs_simplify_result result = facts_query_simplify(facts, (ixs_node *)expr);
  return result.status == IXS_FACT_QUERY_COMPLETE ? result.value : NULL;
}

void ixs_simplify_batch_facts(ixs_facts *facts, const ixs_node **exprs,
                              size_t n) {
  (void)facts_query_simplify_batch(facts, (ixs_node **)exprs, n);
}

ixs_check_result ixs_check_facts(ixs_facts *facts, const ixs_node *expr) {
  ixs_fact_check_result result = facts_query_check(facts, (ixs_node *)expr);
  return result.status == IXS_FACT_QUERY_COMPLETE ? result.check
                                                  : IXS_CHECK_UNKNOWN;
}

ixs_check_result ixs_check_predicate_facts(ixs_facts *facts,
                                           const ixs_node *predicate) {
  ixs_fact_check_result result =
      facts_query_check_predicate(facts, (ixs_node *)predicate);
  return result.status == IXS_FACT_QUERY_COMPLETE ? result.check
                                                  : IXS_CHECK_UNKNOWN;
}

ixs_check_result ixs_equivalent_facts(ixs_facts *facts, const ixs_node *lhs,
                                      const ixs_node *rhs) {
  ixs_fact_check_result result =
      facts_query_equivalent(facts, (ixs_node *)lhs, (ixs_node *)rhs);
  return result.status == IXS_FACT_QUERY_COMPLETE ? result.check
                                                  : IXS_CHECK_UNKNOWN;
}

bool ixs_constant_difference_facts(ixs_facts *facts, const ixs_node *lhs,
                                   const ixs_node *rhs, int64_t *delta) {
  ixs_constant_difference_result result;
  if (delta)
    *delta = 0;
  if (!delta) {
    facts_public_output_error(facts, "constant difference", "NULL output");
    return false;
  }
  result =
      facts_query_constant_difference(facts, (ixs_node *)lhs, (ixs_node *)rhs);
  if (result.status != IXS_FACT_QUERY_COMPLETE || !result.available)
    return false;
  *delta = result.difference;
  return true;
}

bool ixs_affine_decompose_facts(ixs_facts *facts, const ixs_node *expr,
                                const ixs_node *symbol,
                                const ixs_node **coefficient,
                                const ixs_node **residual) {
  ixs_affine_decomposition_result result;
  if (coefficient)
    *coefficient = NULL;
  if (residual)
    *residual = NULL;
  if (!coefficient || !residual || coefficient == residual) {
    facts_public_output_error(facts, "affine decomposition",
                              "outputs must be non-NULL and distinct");
    return false;
  }
  result =
      facts_query_affine_decompose(facts, (ixs_node *)expr, (ixs_node *)symbol);
  if (result.status != IXS_FACT_QUERY_COMPLETE || !result.available)
    return false;
  *coefficient = result.coefficient;
  *residual = result.residual;
  return true;
}

bool ixs_finite_difference_facts(ixs_facts *facts, const ixs_node *expr,
                                 const ixs_node *symbol, const ixs_node *step,
                                 const ixs_node **difference) {
  ixs_finite_difference_result result;
  if (difference)
    *difference = NULL;
  if (!difference) {
    facts_public_output_error(facts, "finite difference", "NULL output");
    return false;
  }
  result = facts_query_finite_difference(facts, (ixs_node *)expr,
                                         (ixs_node *)symbol, (ixs_node *)step);
  if (result.status != IXS_FACT_QUERY_COMPLETE || !result.available)
    return false;
  *difference = result.difference;
  return true;
}

bool ixs_split_additive_constant_facts(ixs_facts *facts, const ixs_node *expr,
                                       const ixs_node **residual,
                                       int64_t *constant) {
  ixs_additive_constant_result result;
  if (residual)
    *residual = NULL;
  if (constant)
    *constant = 0;
  if (!residual || !constant) {
    facts_public_output_error(facts, "additive constant",
                              "outputs must be non-NULL");
    return false;
  }
  result = facts_query_split_additive_constant(facts, (ixs_node *)expr);
  if (result.status != IXS_FACT_QUERY_COMPLETE || !result.available)
    return false;
  *residual = result.residual;
  *constant = result.constant;
  return true;
}

ixs_check_result ixs_check_integer_valued_facts(ixs_facts *facts,
                                                const ixs_node *expr) {
  ixs_fact_check_result result =
      facts_query_check_integer_valued(facts, (ixs_node *)expr);
  return result.status == IXS_FACT_QUERY_COMPLETE ? result.check
                                                  : IXS_CHECK_UNKNOWN;
}

ixs_check_result ixs_check_defined_facts(ixs_facts *facts,
                                         const ixs_node *expr) {
  ixs_fact_check_result result =
      facts_query_check_defined(facts, (ixs_node *)expr);
  return result.status == IXS_FACT_QUERY_COMPLETE ? result.check
                                                  : IXS_CHECK_UNKNOWN;
}

ixs_check_result ixs_check_divisible_facts(ixs_facts *facts,
                                           const ixs_node *expr,
                                           int64_t modulus) {
  ixs_fact_check_result result =
      facts_query_check_divisible(facts, (ixs_node *)expr, modulus);
  return result.status == IXS_FACT_QUERY_COMPLETE ? result.check
                                                  : IXS_CHECK_UNKNOWN;
}

ixs_pow2_fact ixs_get_pow2_fact_facts(ixs_facts *facts, const ixs_node *expr) {
  ixs_pow2_query_result result = facts_query_get_pow2(facts, (ixs_node *)expr);
  return result.status == IXS_FACT_QUERY_COMPLETE ? result.fact
                                                  : IXS_POW2_UNKNOWN;
}

bool ixs_get_known_bits_facts(ixs_facts *facts, const ixs_node *expr,
                              ixs_known_bits *out) {
  ixs_known_bits_query_result result;
  if (out) {
    out->known_zero = 0;
    out->known_one = 0;
    out->pow2 = IXS_POW2_UNKNOWN;
  }
  if (!out) {
    facts_public_output_error(facts, "known bits", "NULL output");
    return false;
  }
  result = facts_query_get_known_bits(facts, (ixs_node *)expr);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    return false;
  *out = result.bits;
  return true;
}

bool ixs_get_symbol_congruence_facts(ixs_facts *facts, const ixs_node *symbol,
                                     int64_t *modulus, int64_t *residue) {
  ixs_symbol_congruence_result result;
  if (modulus)
    *modulus = 0;
  if (residue)
    *residue = 0;
  if (!modulus || !residue || modulus == residue) {
    facts_public_output_error(facts, "symbol congruence",
                              "outputs must be non-NULL and distinct");
    return false;
  }
  result = facts_query_get_symbol_congruence(facts, (ixs_node *)symbol);
  if (result.status != IXS_FACT_QUERY_COMPLETE || !result.available)
    return false;
  *modulus = result.modulus;
  *residue = result.residue;
  return true;
}

ixs_check_result ixs_check_congruent_facts(ixs_facts *facts,
                                           const ixs_node *expr,
                                           int64_t modulus, int64_t residue) {
  ixs_fact_check_result result =
      facts_query_check_congruent(facts, (ixs_node *)expr, modulus, residue);
  return result.status == IXS_FACT_QUERY_COMPLETE ? result.check
                                                  : IXS_CHECK_UNKNOWN;
}

bool ixs_range_facts(ixs_facts *facts, const ixs_node *expr,
                     ixs_range_result *out) {
  ixs_range_query_result result;
  if (out)
    memset(out, 0, sizeof(*out));
  if (!out) {
    facts_public_output_error(facts, "range", "NULL output");
    return false;
  }
  result = facts_query_range(facts, (ixs_node *)expr);
  if (result.status != IXS_FACT_QUERY_COMPLETE || !result.available)
    return false;
  *out = result.range;
  return true;
}
