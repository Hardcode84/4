/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "additive_row.h"
#include "bounds.h"
#include "bounds_defined.h"
#include "bounds_predicate.h"
#include "bounds_query.h"
#include "bounds_range.h"
#include "bounds_store.h"
#include "division_algebra.h"
#include "expand.h"
#include "facts_store.h"
#include "query_walk.h"
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

static void interval_to_range_result(ixs_interval iv, ixs_range_result *out) {
  out->has_lower = !iv.lo_inf;
  out->has_upper = !iv.hi_inf;
  out->lower_p = iv.lo_inf ? 0 : iv.lo_p;
  out->lower_q = iv.lo_inf ? 1 : iv.lo_q;
  out->upper_p = iv.hi_inf ? 0 : iv.hi_p;
  out->upper_q = iv.hi_inf ? 1 : iv.hi_q;
}

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

static ixs_fact_query_status
facts_status_from_algebra(ixs_algebra_status status) {
  if (status == IXS_ALGEBRA_LIMITED)
    return IXS_FACT_QUERY_LIMITED;
  if (status == IXS_ALGEBRA_INVALID)
    return IXS_FACT_QUERY_INVALID;
  if (status == IXS_ALGEBRA_OOM)
    return IXS_FACT_QUERY_OOM;
  return IXS_FACT_QUERY_COMPLETE;
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
  ixs_algebra_status detail;
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
  detail = bounds_equivalence_query_detail(&facts->bounds, ctx, lhs, rhs,
                                           &result.check);
  result.status = facts_status_from_algebra(detail);

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
  ixs_algebra_status detail;
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
    detail = bounds_constant_difference_query_detail(
        ctx, &facts->bounds, lhs, rhs, &result.difference, &result.available);
    ixs_arena_restore(&ctx->diag, diag_mark);
    ctx->errors = saved_errors;
    ctx->nerrors = saved_nerrors;
    ctx->errors_cap = saved_errors_cap;
  }
  result.status = facts_status_from_algebra(detail);

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
  ixs_fact_check_result result = {IXS_FACT_QUERY_INVALID, IXS_CHECK_UNKNOWN};
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
