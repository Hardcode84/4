/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "additive_row.h"
#include "bounds.h"
#include "bounds_defined.h"
#include "bounds_equivalence.h"
#include "bounds_predicate.h"
#include "bounds_query.h"
#include "bounds_range.h"
#include "bounds_store.h"
#include "division_algebra.h"
#include "expand.h"
#include "facts_store.h"
#include "query_transaction.h"
#include "query_walk.h"
#include "rational.h"
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

/* Root-only semantic cancellation is quadratic in direct ADD terms. Explicit
 * equivalence queries remain available for larger sums. */
#define FACTS_ADDITIVE_IDENTITY_MAX_TERMS 64u

typedef struct {
  query_node_set set;
  ixs_node **ordered;
  size_t count;
  size_t capacity;
} facts_definition_targets;

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
  ixs_query_transaction transaction;
  size_t nerrors;
  bool tracking_entered;
  bool tracking_limited;
  bool active;
} facts_read_query_scope;

static void facts_read_query_begin(facts_read_query_scope *scope,
                                   ixs_bounds *bounds, ixs_ctx *ctx,
                                   const char *query) {
  bool old_oom = bounds->oom;
  memset(scope, 0, sizeof(*scope));
  scope->bounds = bounds;
  scope->ctx = ctx;
  scope->query = query;
  (void)bounds_query_force_hold_begin(bounds, &scope->tracking_entered);
  scope->query_state = bounds->query_state;
  ixs_query_transaction_begin(&scope->transaction, NULL, bounds, NULL);
  scope->transaction.old_oom = old_oom;
  scope->nerrors = ctx ? ctx->nerrors : 0u;
  scope->active = true;
}

static ixs_fact_query_status
facts_read_query_finish(facts_read_query_scope *scope,
                        ixs_fact_query_status status) {
  ixs_query_observation observed;
  if (!scope || !scope->active)
    return status;
  observed = ixs_query_transaction_finish(&scope->transaction, false);
  if (scope->bounds->query_state != scope->query_state)
    observed.invalid = true;
  if (observed.invalid)
    status = IXS_FACT_QUERY_INVALID;
  else if (observed.new_oom || scope->transaction.old_oom)
    status = IXS_FACT_QUERY_OOM;
  else if ((observed.limited || scope->tracking_limited) &&
           status == IXS_FACT_QUERY_COMPLETE)
    status = IXS_FACT_QUERY_LIMITED;
  if (observed.new_oom || observed.limited || scope->tracking_limited ||
      observed.invalid || status != IXS_FACT_QUERY_COMPLETE)
    bounds_store_invalidate_reads(scope->bounds);
  scope->bounds->oom = scope->transaction.old_oom;
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
static ixs_check_result facts_project_rewritten_predicate(ixs_bounds *bounds,
                                                          ixs_node *source,
                                                          ixs_node *rewritten,
                                                          bool *limited);
static ixs_node *facts_project_simplified_root(ixs_ctx *ctx, ixs_bounds *bounds,
                                               ixs_node *source,
                                               ixs_node *rewritten,
                                               ixs_fact_query_status *status,
                                               bool *limited);

static ixs_algebra_status
facts_definition_collect_targets(ixs_ctx *ctx, ixs_bounds *bounds,
                                 ixs_node *root,
                                 facts_definition_targets *targets) {
  query_node_set visited;
  ixs_node **stack = NULL;
  size_t stack_count = 0;
  size_t stack_capacity = 0;

  memset(&visited, 0, sizeof(visited));
  memset(targets, 0, sizeof(*targets));
  if (!query_node_stack_push(&ctx->scratch, &stack, &stack_count,
                             &stack_capacity, root))
    return IXS_ALGEBRA_OOM;
  while (stack_count > 0u) {
    ixs_node *node = stack[--stack_count];
    uint32_t child_count;
    uint32_t i;
    bool inserted;
    size_t endpoint_index;

    if (!query_node_set_insert(&ctx->scratch, &visited, node, &inserted))
      return IXS_ALGEBRA_OOM;
    if (!inserted)
      continue;
    if (ixs_relation_algebra_find_endpoint(&bounds->relations, node,
                                           &endpoint_index)) {
      (void)endpoint_index;
      if (!query_node_set_insert(&ctx->scratch, &targets->set, node, &inserted))
        return IXS_ALGEBRA_OOM;
      if (inserted &&
          !query_node_stack_push(&ctx->scratch, &targets->ordered,
                                 &targets->count, &targets->capacity, node))
        return IXS_ALGEBRA_OOM;
    }
    child_count = ixs_node_nchildren(node);
    for (i = 0; i < child_count; i++) {
      ixs_node *child = ixs_node_child(node, i);
      if (!child)
        return IXS_ALGEBRA_INVALID;
      if (!query_node_stack_push(&ctx->scratch, &stack, &stack_count,
                                 &stack_capacity, child))
        return IXS_ALGEBRA_OOM;
    }
  }
  return IXS_ALGEBRA_MATCH;
}

static ixs_algebra_status
facts_definition_descendants_intersect_targets(ixs_ctx *ctx, ixs_node *root,
                                               const query_node_set *targets,
                                               bool *intersects) {
  ixs_arena_mark mark = ixs_arena_save(&ctx->scratch);
  query_node_set visited;
  ixs_node **stack = NULL;
  size_t stack_count = 0;
  size_t stack_capacity = 0;
  ixs_algebra_status status = IXS_ALGEBRA_MATCH;
  uint32_t child_count;
  uint32_t i;

  *intersects = false;
  memset(&visited, 0, sizeof(visited));
  child_count = ixs_node_nchildren(root);
  for (i = 0; i < child_count; i++) {
    ixs_node *child = ixs_node_child(root, i);
    if (!child) {
      status = IXS_ALGEBRA_INVALID;
      goto cleanup;
    }
    if (!query_node_stack_push(&ctx->scratch, &stack, &stack_count,
                               &stack_capacity, child)) {
      status = IXS_ALGEBRA_OOM;
      goto cleanup;
    }
  }
  while (stack_count > 0u) {
    ixs_node *node = stack[--stack_count];
    bool inserted;
    if (query_node_set_contains(targets, node)) {
      *intersects = true;
      goto cleanup;
    }
    if (!query_node_set_insert(&ctx->scratch, &visited, node, &inserted)) {
      status = IXS_ALGEBRA_OOM;
      goto cleanup;
    }
    if (!inserted)
      continue;
    child_count = ixs_node_nchildren(node);
    for (i = 0; i < child_count; i++) {
      ixs_node *child = ixs_node_child(node, i);
      if (!child) {
        status = IXS_ALGEBRA_INVALID;
        goto cleanup;
      }
      if (!query_node_stack_push(&ctx->scratch, &stack, &stack_count,
                                 &stack_capacity, child)) {
        status = IXS_ALGEBRA_OOM;
        goto cleanup;
      }
    }
  }

cleanup:
  ixs_arena_restore(&ctx->scratch, mark);
  return status;
}

static ixs_algebra_status facts_definition_choose_canonical(
    ixs_ctx *ctx, const facts_definition_targets *definitions,
    const bounds_relation_component *component, size_t *canonical_index) {
  unsigned pass;
  size_t i;

  *canonical_index = SIZE_MAX;
  for (pass = 0; pass < 2u && *canonical_index == SIZE_MAX; pass++) {
    for (i = 0; i < component->count; i++) {
      ixs_node *candidate = component->entries[i].node;
      bool selected = query_node_set_contains(&definitions->set, candidate);
      bool intersects;
      ixs_algebra_status status;

      if (selected != (pass != 0u))
        continue;
      status = facts_definition_descendants_intersect_targets(
          ctx, candidate, &definitions->set, &intersects);
      if (status != IXS_ALGEBRA_MATCH)
        return status;
      if (!intersects) {
        *canonical_index = i;
        break;
      }
    }
  }
  return IXS_ALGEBRA_MATCH;
}

static ixs_algebra_status facts_definition_component_replacements(
    ixs_ctx *ctx, ixs_bounds *bounds, ixs_node *root,
    const facts_definition_targets *definitions, query_node_set *processed,
    ixs_node **targets, ixs_node **replacements, size_t *replacement_count) {
  bounds_relation_component component;
  ixs_algebra_status component_status;
  size_t canonical_index = SIZE_MAX;
  size_t i;

  component_status =
      bounds_collect_relation_component(bounds, root, &component);
  if (component_status == IXS_ALGEBRA_NO_MATCH) {
    bool inserted;
    return query_node_set_insert(&ctx->scratch, processed, root, &inserted)
               ? IXS_ALGEBRA_NO_MATCH
               : IXS_ALGEBRA_OOM;
  }
  if (component_status != IXS_ALGEBRA_MATCH) {
    bounds_relation_component_destroy(&component);
    return component_status;
  }

  /* Prefer a definition outside the query. If both sides occur, choose one
   * nonrecursive queried endpoint so every alias converges instead of swaps. */
  component_status = facts_definition_choose_canonical(
      ctx, definitions, &component, &canonical_index);
  if (component_status != IXS_ALGEBRA_MATCH) {
    bounds_relation_component_destroy(&component);
    return component_status;
  }
  if (canonical_index == SIZE_MAX) {
    for (i = 0; i < component.count; i++) {
      ixs_node *target = component.entries[i].node;
      bool inserted;
      if (!query_node_set_contains(&definitions->set, target))
        continue;
      if (!query_node_set_insert(&ctx->scratch, processed, target, &inserted)) {
        bounds_relation_component_destroy(&component);
        return IXS_ALGEBRA_OOM;
      }
    }
    bounds_relation_component_destroy(&component);
    return IXS_ALGEBRA_NO_MATCH;
  }

  for (i = 0; i < component.count; i++) {
    ixs_node *target = component.entries[i].node;
    ixs_node *replacement = component.entries[canonical_index].node;
    ixs_relation_offset delta;
    int64_t delta_value;
    bool inserted;

    if (!query_node_set_contains(&definitions->set, target))
      continue;
    if (!query_node_set_insert(&ctx->scratch, processed, target, &inserted)) {
      bounds_relation_component_destroy(&component);
      return IXS_ALGEBRA_OOM;
    }
    if (!inserted)
      continue;
    if (!ixs_relation_offset_add(component.entries[i].offset,
                                 ixs_relation_offset_negate(
                                     component.entries[canonical_index].offset),
                                 &delta) ||
        !ixs_relation_offset_to_int64(delta, &delta_value))
      continue;
    if (delta_value != 0) {
      ixs_node *constant = ixs_node_int(ctx, delta_value);
      bool unrepresentable = false;
      if (!constant) {
        bounds_relation_component_destroy(&component);
        return IXS_ALGEBRA_OOM;
      }
      replacement = simp_try_add(ctx, replacement, constant, &unrepresentable);
      if (!replacement) {
        if (unrepresentable)
          continue;
        bounds_relation_component_destroy(&component);
        return IXS_ALGEBRA_OOM;
      }
      if (ixs_node_is_sentinel(replacement)) {
        bounds_relation_component_destroy(&component);
        return IXS_ALGEBRA_INVALID;
      }
    }
    if (replacement == target)
      continue;
    assert(*replacement_count < definitions->count);
    targets[*replacement_count] = target;
    replacements[(*replacement_count)++] = replacement;
  }
  bounds_relation_component_destroy(&component);
  return IXS_ALGEBRA_MATCH;
}

/* Definitions are selected from the original query and applied once.
 * Replacements are never traversed. A replacement may name its component's
 * selected canonical root, but none of its descendants can be a selected
 * target, so exact equality cycles cannot become recursive rewrites. Work is
 * linear in the query DAG, the distinct incident relation components, and the
 * candidate DAGs inspected while choosing one representative per component. */
static ixs_algebra_status facts_definition_normalize(ixs_ctx *ctx,
                                                     ixs_bounds *bounds,
                                                     ixs_node *expr,
                                                     ixs_node **result) {
  facts_definition_targets definitions;
  query_node_set processed;
  ixs_node **targets;
  ixs_node **replacements;
  size_t replacement_count = 0;
  size_t i;
  ixs_query_transaction diagnostic_transaction;
  ixs_algebra_status status;

  *result = expr;
  if (ixs_relation_algebra_edge_count(&bounds->relations) == 0u)
    return IXS_ALGEBRA_NO_MATCH;
  status = facts_definition_collect_targets(ctx, bounds, expr, &definitions);
  if (status != IXS_ALGEBRA_MATCH || definitions.count == 0u)
    return status == IXS_ALGEBRA_MATCH ? IXS_ALGEBRA_NO_MATCH : status;
  if (definitions.count > UINT32_MAX ||
      definitions.count > SIZE_MAX / sizeof(*replacements))
    return IXS_ALGEBRA_OOM;
  memset(&processed, 0, sizeof(processed));
  if (!query_node_set_reserve(&ctx->scratch, &processed, definitions.count))
    return IXS_ALGEBRA_OOM;
  targets = ixs_arena_alloc(&ctx->scratch, definitions.count * sizeof(*targets),
                            sizeof(void *));
  replacements = ixs_arena_alloc(
      &ctx->scratch, definitions.count * sizeof(*replacements), sizeof(void *));
  if (!targets || !replacements)
    return IXS_ALGEBRA_OOM;
  for (i = 0; i < definitions.count; i++) {
    if (query_node_set_contains(&processed, definitions.ordered[i]))
      continue;
    status = facts_definition_component_replacements(
        ctx, bounds, definitions.ordered[i], &definitions, &processed, targets,
        replacements, &replacement_count);
    if (status != IXS_ALGEBRA_MATCH && status != IXS_ALGEBRA_NO_MATCH)
      return status;
  }
  if (replacement_count == 0u)
    return IXS_ALGEBRA_NO_MATCH;
  ixs_query_transaction_begin(&diagnostic_transaction, ctx, NULL, NULL);
  *result = simp_subs_multi(ctx, expr, (uint32_t)replacement_count, targets,
                            replacements);
  if (!*result)
    return IXS_ALGEBRA_OOM;
  if (ixs_node_is_sentinel(*result)) {
    (void)ixs_query_transaction_finish(&diagnostic_transaction, false);
    *result = expr;
    return IXS_ALGEBRA_NO_MATCH;
  }
  return *result == expr ? IXS_ALGEBRA_NO_MATCH : IXS_ALGEBRA_MATCH;
}

static ixs_fact_query_status
facts_status_from_algebra(ixs_algebra_status status);
static bool facts_simplify_cache_lookup(ixs_ctx *ctx, ixs_bounds *bounds,
                                        ixs_node *source, ixs_node **result);
static void facts_simplify_cache_store_result(ixs_ctx *ctx, ixs_bounds *bounds,
                                              ixs_node *source,
                                              ixs_simplify_result result);

static bool facts_simplify_preflight(ixs_facts *facts, ixs_ctx *ctx,
                                     ixs_node *expr,
                                     ixs_simplify_result *result) {
  ixs_node *cached;
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
  if (facts_simplify_cache_lookup(ctx, &facts->bounds, expr, &cached)) {
    result->status = IXS_FACT_QUERY_COMPLETE;
    result->value = cached;
    return true;
  }
  return false;
}

static ixs_node *facts_definition_simplify(ixs_ctx *ctx, ixs_bounds *bounds,
                                           ixs_node *expr,
                                           ixs_fact_query_status *status,
                                           bool *limited) {
  ixs_node *normalized;
  ixs_algebra_status definition_status =
      facts_definition_normalize(ctx, bounds, expr, &normalized);
  *status = facts_status_from_algebra(definition_status);
  if (*status != IXS_FACT_QUERY_COMPLETE)
    return NULL;
  return simp_simplify_bounds_status(ctx, normalized, bounds, limited);
}

/* Successful poison refinement discards diagnostics from dead children.
 * Failed simplification leaves its domain or transport diagnostic intact. */
static void
facts_simplify_finish_diagnostics(const ixs_query_transaction *transaction,
                                  bool discard) {
  if (discard)
    (void)ixs_query_transaction_finish(transaction, false);
}

static ixs_simplify_result facts_query_simplify(ixs_facts *facts,
                                                ixs_node *expr) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_query_transaction diagnostic_transaction;
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
  ixs_query_transaction_begin(&diagnostic_transaction, ctx, NULL, NULL);
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
  value = facts_definition_simplify(ctx, &facts->bounds, expr, &result.status,
                                    &limited);
  if (!limited && value && !ixs_node_is_sentinel(value) &&
      ixs_node_contains_rounding(value) && ixs_node_contains_piecewise(value))
    value = facts_simplify_truncating_remainders(ctx, &facts->bounds, expr,
                                                 value, &result.status);
  if (!limited && result.status == IXS_FACT_QUERY_COMPLETE && value &&
      !ixs_node_is_sentinel(value)) {
    value = simp_normalize_rational_carrier(ctx, &facts->bounds, value);
    value = facts_project_simplified_root(ctx, &facts->bounds, expr, value,
                                          &result.status, &limited);
  }
  if (limited) {
    result.status = IXS_FACT_QUERY_LIMITED;
  } else if (result.status != IXS_FACT_QUERY_COMPLETE) {
    value = NULL;
  } else if (!value || (!old_oom && facts->bounds.oom)) {
    result.status = IXS_FACT_QUERY_OOM;
    bounds_store_invalidate_reads(&facts->bounds);
  } else if (ixs_node_is_sentinel(value)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    result.value = value;
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
  facts_simplify_finish_diagnostics(&diagnostic_transaction,
                                    result.status == IXS_FACT_QUERY_COMPLETE &&
                                        result.value &&
                                        !ixs_node_is_sentinel(result.value));
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.value = NULL;
  facts_simplify_cache_store_result(ctx, &facts->bounds, expr, result);
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

static bool facts_simplify_batch_is_clean(ixs_node *const *exprs, size_t n) {
  size_t i;
  for (i = 0; i < n; i++) {
    if (ixs_node_is_sentinel(exprs[i]))
      return false;
  }
  return true;
}

static bool facts_simplify_batch_finalize(ixs_ctx *ctx, ixs_bounds *bounds,
                                          ixs_node *const *sources,
                                          ixs_node **exprs, size_t n,
                                          ixs_fact_query_status *status) {
  size_t i;
  for (i = 0; i < n; i++) {
    bool limited = false;
    exprs[i] = simp_normalize_rational_carrier(ctx, bounds, exprs[i]);
    if (!exprs[i])
      return false;
    exprs[i] = facts_project_simplified_root(ctx, bounds, sources[i], exprs[i],
                                             status, &limited);
    if (limited) {
      *status = IXS_FACT_QUERY_LIMITED;
      return false;
    }
  }
  return true;
}

static ixs_algebra_status facts_simplify_batch_definitions(ixs_ctx *ctx,
                                                           ixs_bounds *bounds,
                                                           ixs_node **exprs,
                                                           size_t n) {
  size_t i;
  for (i = 0; i < n; i++) {
    ixs_algebra_status status =
        facts_definition_normalize(ctx, bounds, exprs[i], &exprs[i]);
    if (status != IXS_ALGEBRA_MATCH && status != IXS_ALGEBRA_NO_MATCH)
      return status;
  }
  return IXS_ALGEBRA_MATCH;
}

static ixs_fact_query_status
facts_query_simplify_batch(ixs_facts *facts, ixs_node **exprs, size_t n) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_query_transaction diagnostic_transaction;
  ixs_arena_mark mark;
  ixs_ctx *ctx;
  ixs_node **originals = NULL;
  bool ok;
  bool old_oom;
  bool clean_result = true;
  size_t i;
  ixs_algebra_status definition_status = IXS_ALGEBRA_MATCH;
  ixs_fact_query_status status = IXS_FACT_QUERY_INVALID;

  if (!facts_store_bind(facts, &binding, &ctx))
    return status;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "simplify batch");
  ixs_query_transaction_begin(&diagnostic_transaction, ctx, NULL, NULL);
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
  definition_status =
      facts_simplify_batch_definitions(ctx, &facts->bounds, exprs, n);
  status = facts_status_from_algebra(definition_status);
  ok = status == IXS_FACT_QUERY_COMPLETE &&
       simp_simplify_batch_bounds(ctx, exprs, n, &facts->bounds);
  if (ok)
    ok = facts_simplify_batch_remainders(ctx, &facts->bounds, originals, exprs,
                                         n, &status);
  if (ok)
    ok = facts_simplify_batch_finalize(ctx, &facts->bounds, originals, exprs, n,
                                       &status);
  if (!ok || (!old_oom && facts->bounds.oom)) {
    if (status == IXS_FACT_QUERY_COMPLETE)
      status = bounds_query_limited_since(&facts->bounds,
                                          read_scope.transaction.transport)
                   ? IXS_FACT_QUERY_LIMITED
                   : IXS_FACT_QUERY_OOM;
    bounds_store_invalidate_reads(&facts->bounds);
  } else {
    status = IXS_FACT_QUERY_COMPLETE;
    clean_result = facts_simplify_batch_is_clean(exprs, n);
  }
  facts->bounds.oom = old_oom;

cleanup:
  status = facts_read_query_finish(&read_scope, status);
  facts_simplify_finish_diagnostics(&diagnostic_transaction,
                                    status == IXS_FACT_QUERY_COMPLETE &&
                                        clean_result);
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
  ixs_node *projected;
  bool limited = false;
  *status = IXS_FACT_QUERY_COMPLETE;
  if (result.status == IXS_ALGEBRA_OOM)
    *status = IXS_FACT_QUERY_OOM;
  else if (result.status == IXS_ALGEBRA_INVALID)
    *status = IXS_FACT_QUERY_INVALID;
  else if (result.status == IXS_ALGEBRA_LIMITED)
    *status = IXS_FACT_QUERY_LIMITED;
  if (*status != IXS_FACT_QUERY_COMPLETE)
    return NULL;
  if (result.status != IXS_ALGEBRA_MATCH)
    return root;
  projected = simp_simplify_bounds_status(ctx, result.lhs, bounds, &limited);
  if (limited) {
    *status = IXS_FACT_QUERY_LIMITED;
    return NULL;
  }
  return projected;
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

static bool facts_query_cache_enabled(ixs_ctx *ctx, ixs_bounds *bounds) {
  return ctx->arena.fail_after == IXS_ARENA_FAILURE_DISABLED &&
         ctx->scratch.fail_after == IXS_ARENA_FAILURE_DISABLED &&
         bounds->query_arena.fail_after == IXS_ARENA_FAILURE_DISABLED &&
         bounds->query_state_arena.fail_after == IXS_ARENA_FAILURE_DISABLED &&
         bounds_query_state_transport(bounds) == IXS_BOUNDS_TRANSPORT_CLEAN;
}

static bool facts_simplify_cache_lookup(ixs_ctx *ctx, ixs_bounds *bounds,
                                        ixs_node *source, ixs_node **result) {
  facts_query_cache *cache = bounds->facts_query_cache;
  facts_query_simplify_entry *entry;
  if (!cache || cache->generation != bounds->facts_query_generation ||
      !facts_query_cache_enabled(ctx, bounds))
    return false;
  entry = &cache->simplify[source->hash & (FACTS_SIMPLIFY_CACHE_CAP - 1u)];
  if (entry->generation != cache->generation || entry->source != source)
    return false;
  *result = entry->result;
#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
  cache->simplify_hits++;
#endif
  return true;
}

static void facts_simplify_cache_store(ixs_ctx *ctx, ixs_bounds *bounds,
                                       ixs_node *source, ixs_node *result) {
  facts_query_cache *cache = bounds->facts_query_cache;
  facts_query_simplify_entry *entry;
  if (!cache || cache->generation != bounds->facts_query_generation ||
      !facts_query_cache_enabled(ctx, bounds))
    return;
  entry = &cache->simplify[source->hash & (FACTS_SIMPLIFY_CACHE_CAP - 1u)];
  entry->source = source;
  entry->result = result;
  entry->generation = cache->generation;
#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
  cache->simplify_stores++;
#endif
}

static void facts_simplify_cache_store_result(ixs_ctx *ctx, ixs_bounds *bounds,
                                              ixs_node *source,
                                              ixs_simplify_result result) {
  if (result.status == IXS_FACT_QUERY_COMPLETE && result.value &&
      !ixs_node_is_sentinel(result.value))
    facts_simplify_cache_store(ctx, bounds, source, result.value);
}

/* One root truth pipeline is shared by check and simplification. Structural
 * predicate folding, exact comparison proof, and local implication retain
 * their distinct bounded engines but no public entry may omit one of them. */
static ixs_check_result
facts_predicate_truth(ixs_bounds *bounds, ixs_node *predicate, bool *limited) {
  ixs_check_result result = bounds_predicate_eval(bounds, predicate, limited);
  if (!*limited && result == IXS_CHECK_UNKNOWN && predicate->tag == IXS_CMP)
    result = ixs_bounds_check_query(bounds, predicate);
  if (!*limited && result == IXS_CHECK_UNKNOWN)
    result = bounds_predicate_implication(bounds, predicate, limited);
  return result;
}

/* Project only after the caller's one fact rewrite. This is deliberately a
 * root operation: finite-domain proof must not re-enter per-node rewriting. */
static ixs_check_result facts_project_rewritten_predicate(ixs_bounds *bounds,
                                                          ixs_node *source,
                                                          ixs_node *rewritten,
                                                          bool *limited) {
  ixs_check_result result = facts_predicate_truth(bounds, rewritten, limited);
  if (!*limited && result == IXS_CHECK_UNKNOWN)
    result = bounds_predicate_bounded_finite_domain(bounds, source);
  return result;
}

/* Zero is the unique canonical representative of a proved additive identity.
 * This root projection shares the ordinary equivalence engine; it does not
 * re-enter the per-node fact rewrite. */
static bool facts_additive_identity_candidate(ixs_node *node) {
  uint32_t i;
  uint32_t j;

  if (!node || node->tag != IXS_ADD || node->u.add.nterms < 3u ||
      node->u.add.nterms > FACTS_ADDITIVE_IDENTITY_MAX_TERMS ||
      !ixs_node_is_zero(node->u.add.coeff))
    return false;
  for (i = 0; i < node->u.add.nterms; i++) {
    int64_t left_p;
    int64_t left_q;
    ixs_node_get_rat(node->u.add.terms[i].coeff, &left_p, &left_q);
    for (j = i + 1u; j < node->u.add.nterms; j++) {
      int64_t right_p;
      int64_t right_q;
      ixs_node_get_rat(node->u.add.terms[j].coeff, &right_p, &right_q);
      if ((left_p < 0) == (right_p < 0) || left_q != right_q)
        continue;
      if (ixs_int64_magnitude(left_p) == ixs_int64_magnitude(right_p) &&
          node->u.add.terms[i].term->tag == node->u.add.terms[j].term->tag)
        return true;
    }
  }
  return false;
}

static ixs_node *facts_project_additive_identity(ixs_ctx *ctx,
                                                 ixs_bounds *bounds,
                                                 ixs_node *rewritten,
                                                 ixs_fact_query_status *status,
                                                 bool *limited) {
  facts_query_cache *cache = bounds->facts_query_cache;
  facts_query_identity_entry *entry = NULL;
  ixs_check_result equivalent;
  ixs_algebra_status detail;

  if (!facts_additive_identity_candidate(rewritten))
    return rewritten;
  if (cache && cache->generation == bounds->facts_query_generation &&
      facts_query_cache_enabled(ctx, bounds)) {
    entry = &cache->identity[rewritten->hash &
                             (FACTS_QUERY_IDENTITY_CACHE_CAP - 1u)];
    if (entry->generation == cache->generation && entry->source == rewritten) {
#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
      cache->identity_hits++;
#endif
      return entry->result == IXS_CHECK_TRUE ? ctx->node_zero : rewritten;
    }
  }
  detail = bounds_equivalence_simplified_query_detail(
      bounds, ctx, rewritten, ctx->node_zero, &equivalent);
  if (detail == IXS_ALGEBRA_LIMITED) {
    *limited = true;
    return rewritten;
  }
  *status = facts_status_from_algebra(detail);
  if (*status != IXS_FACT_QUERY_COMPLETE)
    return NULL;
  if (entry) {
    entry->source = rewritten;
    entry->result = equivalent;
    entry->generation = cache->generation;
#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
    cache->identity_stores++;
#endif
  }
  return equivalent == IXS_CHECK_TRUE ? ctx->node_zero : rewritten;
}

/* A structurally total root with one finite interval value has that rational
 * as its canonical result.  This is the same typed interval proof used by
 * checks; it does not add an expression-shape rule to the simplifier. */
static ixs_node *facts_project_exact_root(ixs_ctx *ctx, ixs_bounds *bounds,
                                          ixs_node *source, ixs_node *rewritten,
                                          ixs_fact_query_status *status) {
  ixs_interval interval;
  ixs_node *exact;

  if (ixs_node_is_pred_kind(source) || !ixs_node_is_known_total(source))
    return rewritten;
  interval = ixs_bounds_get(bounds, source);
  if (!interval.valid || interval.lo_inf || interval.hi_inf ||
      ixs_rat_cmp(interval.lo_p, interval.lo_q, interval.hi_p, interval.hi_q) !=
          0)
    return rewritten;
  exact = ixs_node_rat(ctx, interval.lo_p, interval.lo_q);
  if (!exact)
    *status = IXS_FACT_QUERY_OOM;
  return exact;
}

static ixs_node *facts_project_simplified_root(ixs_ctx *ctx, ixs_bounds *bounds,
                                               ixs_node *source,
                                               ixs_node *rewritten,
                                               ixs_fact_query_status *status,
                                               bool *limited) {
  ixs_check_result projected;
  rewritten =
      facts_project_additive_identity(ctx, bounds, rewritten, status, limited);
  if (!*limited && *status == IXS_FACT_QUERY_COMPLETE && rewritten &&
      !ixs_node_is_sentinel(rewritten))
    rewritten =
        facts_project_exact_root(ctx, bounds, source, rewritten, status);
  if (!rewritten || ixs_node_is_sentinel(rewritten) ||
      !ixs_node_is_pred_kind(source) || ixs_node_is_known_true(rewritten) ||
      ixs_node_is_known_false(rewritten))
    return rewritten;
  projected = facts_predicate_truth(bounds, source, limited);
  if (!*limited && projected == IXS_CHECK_UNKNOWN)
    projected =
        facts_project_rewritten_predicate(bounds, source, rewritten, limited);
  if (projected == IXS_CHECK_TRUE)
    return ctx->node_true;
  if (projected == IXS_CHECK_FALSE)
    return ctx->node_false;
  return rewritten;
}

static ixs_fact_check_result facts_query_check_predicate(ixs_facts *facts,
                                                         ixs_node *predicate) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_node *simplified;
  ixs_node *normalized;
  ixs_algebra_status definition_status;
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

  /* The predicate engine owns structural truth. Exact EQ/NE fallback belongs
   * to equivalence and is applied here at the public query boundary. */
  result.check =
      facts_predicate_truth(&facts->bounds, predicate, &predicate_limited);
  if (predicate_limited) {
    result.status = IXS_FACT_QUERY_LIMITED;
    goto cleanup;
  }
  if (result.check != IXS_CHECK_UNKNOWN) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }

  mark = ixs_arena_save(&ctx->scratch);
  definition_status =
      facts_definition_normalize(ctx, &facts->bounds, predicate, &normalized);
  result.status = facts_status_from_algebra(definition_status);
  simplified = NULL;
  if (result.status == IXS_FACT_QUERY_COMPLETE)
    simplified = simp_simplify_bounds_status(ctx, normalized, &facts->bounds,
                                             &simplify_limited);
  if (result.status != IXS_FACT_QUERY_COMPLETE) {
    result.check = IXS_CHECK_UNKNOWN;
  } else if (simplify_limited) {
    result.status = IXS_FACT_QUERY_LIMITED;
  } else if (!simplified) {
    result.status = IXS_FACT_QUERY_OOM;
  } else if (ixs_node_is_sentinel(simplified)) {
    result.status = IXS_FACT_QUERY_INVALID;
  } else {
    result.check = facts_project_rewritten_predicate(
        &facts->bounds, predicate, simplified, &predicate_limited);
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
  ixs_node *normalized_lhs;
  ixs_arena_mark mark;
  ixs_algebra_status definition_status;
  ixs_algebra_status detail;
  bool query_held = false;
  bool scratch_saved = false;
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
  mark = ixs_arena_save(&ctx->scratch);
  scratch_saved = true;
  detail = bounds_equivalence_query_detail(&facts->bounds, ctx, lhs, rhs,
                                           &result.check);
  result.status = facts_status_from_algebra(detail);
  if (result.status != IXS_FACT_QUERY_COMPLETE ||
      result.check != IXS_CHECK_UNKNOWN)
    goto cleanup;
  definition_status =
      facts_definition_normalize(ctx, &facts->bounds, lhs, &normalized_lhs);
  result.status = facts_status_from_algebra(definition_status);
  if (result.status != IXS_FACT_QUERY_COMPLETE || normalized_lhs == lhs)
    goto cleanup;
  detail = bounds_equivalence_query_detail(&facts->bounds, ctx, normalized_lhs,
                                           rhs, &result.check);
  result.status = facts_status_from_algebra(detail);

cleanup:
  if (scratch_saved)
    ixs_arena_restore(&ctx->scratch, mark);
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
  ixs_query_transaction transaction;
  facts_read_query_scope read_scope;
  ixs_fact_query_status status;
  bool bound;
  bool active;
  bool query_held;
} facts_query_operation;

static bool facts_query_operation_begin(ixs_facts *facts,
                                        ixs_node *const *nodes, size_t nnodes,
                                        const char *query, bool outputs_ok,
                                        const char *output_error,
                                        facts_query_operation *scope) {
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

static void facts_query_operation_start(facts_query_operation *scope) {
  ixs_query_transaction_begin(&scope->transaction, scope->ctx, NULL,
                              &scope->ctx->scratch);
  scope->active = true;
}

static bool facts_query_operation_finish(facts_query_operation *scope,
                                         bool success) {
  if (scope->active) {
    (void)ixs_query_transaction_finish(&scope->transaction, false);
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

static ixs_node *algebra_query_normalize(facts_query_operation *scope,
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

static bool algebra_query_defined(facts_query_operation *scope,
                                  ixs_node *expr) {
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

static bool algebra_contains_node(facts_query_operation *scope, ixs_node *root,
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

static bool algebra_affine_extract(facts_query_operation *scope, ixs_node *expr,
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

static ixs_affine_decomposition_result
facts_query_affine_decompose(ixs_facts *facts, ixs_node *expr,
                             ixs_node *symbol) {
  facts_query_operation scope;
  ixs_affine_decomposition_result result = {IXS_FACT_QUERY_INVALID, false, NULL,
                                            NULL};
  ixs_node *nodes[2] = {expr, symbol};
  if (!facts_query_operation_begin(facts, nodes, 2, "affine decomposition",
                                   true, NULL, &scope)) {
    result.status = scope.status;
    return result;
  }
  if (symbol->tag != IXS_SYM) {
    ixs_ctx_push_error(scope.ctx,
                       "affine decomposition: expression must be a symbol");
    scope.status = IXS_FACT_QUERY_INVALID;
    (void)facts_query_operation_finish(&scope, false);
    result.status = scope.status;
    return result;
  }
  facts_query_operation_start(&scope);
  if (!algebra_query_defined(&scope, expr))
    goto cleanup;
  expr = algebra_query_normalize(&scope, expr);
  if (!expr)
    goto cleanup;
  result.available = algebra_affine_extract(&scope, expr, symbol,
                                            (ixs_node **)&result.coefficient,
                                            (ixs_node **)&result.residual);

cleanup:
  (void)facts_query_operation_finish(&scope, result.available);
  result.status = scope.status;
  if (result.status != IXS_FACT_QUERY_COMPLETE) {
    result.available = false;
    result.coefficient = NULL;
    result.residual = NULL;
  }
  return result;
}

static ixs_additive_constant_result
facts_query_split_additive_constant(ixs_facts *facts, ixs_node *expr) {
  facts_query_operation scope;
  ixs_additive_constant_result query_result = {IXS_FACT_QUERY_INVALID, false,
                                               NULL, 0};
  ixs_node *nodes[1] = {expr};
  ixs_node *result_residual = NULL;
  int64_t result_constant = 0;
  int64_t q;
  bool ok = false;
  if (!facts_query_operation_begin(facts, nodes, 1, "additive constant", true,
                                   NULL, &scope)) {
    query_result.status = scope.status;
    return query_result;
  }
  facts_query_operation_start(&scope);
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
  (void)facts_query_operation_finish(&scope, ok);
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
  ixs_node *normalized;
  ixs_arena_mark mark;
  ixs_algebra_status definition_status;
  ixs_fact_check_result result = {IXS_FACT_QUERY_INVALID, IXS_CHECK_UNKNOWN};
  bool predicate_limited = false;
  bool scratch_saved = false;
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
  result.check =
      expr->tag == IXS_CMP
          ? facts_predicate_truth(&facts->bounds, expr, &predicate_limited)
          : ixs_bounds_check_query(&facts->bounds, expr);
  if (predicate_limited) {
    result.status = IXS_FACT_QUERY_LIMITED;
    goto cleanup;
  }
  result.status = IXS_FACT_QUERY_COMPLETE;
  if (result.check != IXS_CHECK_UNKNOWN || facts->bounds.oom ||
      bounds_query_state_transport(&facts->bounds) !=
          IXS_BOUNDS_TRANSPORT_CLEAN)
    goto cleanup;
  mark = ixs_arena_save(&ctx->scratch);
  scratch_saved = true;
  definition_status =
      facts_definition_normalize(ctx, &facts->bounds, expr, &normalized);
  result.status = facts_status_from_algebra(definition_status);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    goto cleanup;
  if (normalized != expr) {
    result.check = normalized->tag == IXS_CMP
                       ? facts_predicate_truth(&facts->bounds, normalized,
                                               &predicate_limited)
                       : ixs_bounds_check_query(&facts->bounds, normalized);
    if (predicate_limited) {
      result.status = IXS_FACT_QUERY_LIMITED;
      goto cleanup;
    }
  }
  result.status = IXS_FACT_QUERY_COMPLETE;

cleanup:
  if (scratch_saved)
    ixs_arena_restore(&ctx->scratch, mark);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.check = IXS_CHECK_UNKNOWN;
  facts_store_unbind(facts, &binding);
  return result;
}

static ixs_fact_check_result facts_query_check_integer_valued(ixs_facts *facts,
                                                              ixs_node *expr) {
  facts_query_operation scope;
  ixs_node *nodes[1] = {expr};
  ixs_fact_check_result result = {IXS_FACT_QUERY_INVALID, IXS_CHECK_UNKNOWN};
  if (!facts_query_operation_begin(facts, nodes, 1, "integer valued", true,
                                   NULL, &scope)) {
    result.status = scope.status;
    return result;
  }
  result.check = ixs_bounds_check_integer_valued(&facts->bounds, expr);
  (void)facts_query_operation_finish(&scope, true);
  result.status = scope.status;
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.check = IXS_CHECK_UNKNOWN;
  return result;
}

static ixs_fact_check_result facts_query_check_defined(ixs_facts *facts,
                                                       ixs_node *expr) {
  facts_query_operation scope;
  ixs_node *nodes[1] = {expr};
  bool oom = false;
  bool limited = false;
  ixs_fact_check_result result = {IXS_FACT_QUERY_INVALID, IXS_CHECK_UNKNOWN};
  if (!facts_query_operation_begin(facts, nodes, 1, "defined", true, NULL,
                                   &scope)) {
    result.status = scope.status;
    return result;
  }
  result.check =
      bounds_defined_check_detail(&facts->bounds, expr, &oom, &limited);
  scope.status = oom       ? IXS_FACT_QUERY_OOM
                 : limited ? IXS_FACT_QUERY_LIMITED
                           : IXS_FACT_QUERY_COMPLETE;
  (void)facts_query_operation_finish(&scope, true);
  result.status = scope.status;
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.check = IXS_CHECK_UNKNOWN;
  return result;
}

static ixs_fact_check_result
facts_query_check_divisible(ixs_facts *facts, ixs_node *expr, int64_t modulus) {
  facts_query_operation scope;
  ixs_node *nodes[1] = {expr};
  ixs_fact_check_result result = {IXS_FACT_QUERY_INVALID, IXS_CHECK_UNKNOWN};
  if (!facts_query_operation_begin(facts, nodes, 1, "divisibility",
                                   modulus != 0, "modulus must be nonzero",
                                   &scope)) {
    result.status = scope.status;
    return result;
  }
  result.check = ixs_bounds_check_divisible(&facts->bounds, expr, modulus);
  (void)facts_query_operation_finish(&scope, true);
  result.status = scope.status;
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.check = IXS_CHECK_UNKNOWN;
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
  ixs_query_transaction transaction;
  bool old_oom = facts->bounds.oom;
  bool limited = false;
  ixs_node *result;
  ixs_fact_query_status status = IXS_FACT_QUERY_COMPLETE;

  ixs_query_transaction_begin(&transaction, ctx, NULL, &ctx->scratch);
  result = simp_simplify_bounds_status(ctx, expr, &facts->bounds, &limited);
  (void)ixs_query_transaction_finish(&transaction, false);
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

static bool exact_divide_input_not_undefined(ixs_facts *facts, ixs_ctx *ctx,
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
  /* UNKNOWN admits a poison-refining quotient: the constructed value need only
   * agree where the source is defined. A source proved undefined everywhere
   * has no defined evaluation from which to construct a quotient. */
  if (defined == IXS_CHECK_FALSE) {
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
  if (!exact_divide_input_not_undefined(facts, ctx, expr, &result))
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
  if (ixs_bounds_check_integer_valued(&facts->bounds, expr) != IXS_CHECK_TRUE) {
    result.status = IXS_FACT_QUERY_COMPLETE;
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

  if (ixs_bounds_check_integer_valued(&facts->bounds, expr) == IXS_CHECK_TRUE)
    (void)ixs_bounds_get_bitfacts(&facts->bounds, expr, &bits);
  result.status = IXS_FACT_QUERY_COMPLETE;
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
  result.status = IXS_FACT_QUERY_COMPLETE;
  integer_valued = ixs_bounds_check_integer_valued(&facts->bounds, expr);
  iv = ixs_bounds_get(&facts->bounds, expr);
  if (integer_valued == IXS_CHECK_TRUE) {
    if (!bounds_refine_integral_interval(&facts->bounds, expr,
                                         /*expression_defined=*/false, &iv))
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
