/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds.h"
#include "additive_row.h"
#include "bounds_difference.h"
#include "bounds_query.h"
#include "bounds_range.h"
#include "bounds_relation.h"
#include "bounds_store.h"
#include "division_algebra.h"
#include "expand.h"
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

#define FACT_WORK_INIT_CAP 64u
static ixs_node *bounds_condition_assumption(ixs_bounds *b, ixs_node *cond,
                                             bool value,
                                             struct ixs_node_impl *storage);
static ixs_check_result bounds_condition_truth(ixs_bounds *b, ixs_node *cond);
static bool bounds_known_stride(ixs_bounds *bounds, ixs_node *expr,
                                uint64_t *stride);
static ixs_check_result bounds_check_defined_without_equality(ixs_bounds *b,
                                                              ixs_node *expr,
                                                              bool *oom,
                                                              bool *limited);
static ixs_check_result bounds_check_defined_detail(ixs_bounds *b,
                                                    ixs_node *expr, bool *oom,
                                                    bool *limited);
static ixs_algebra_status
bounds_collect_relation_component(ixs_bounds *b, ixs_node *expr,
                                  bounds_relation_component *component);
static ixs_algebra_status
bounds_relation_offset_checked(ixs_bounds *b, ixs_node *lhs, ixs_node *rhs,
                               ixs_relation_offset *offset);
static ixs_algebra_status bounds_exact_relation_difference(ixs_bounds *b,
                                                           ixs_node *lhs,
                                                           ixs_node *rhs,
                                                           int64_t *delta);

static bool bounds_cache_lookup(ixs_bounds *b, ixs_node *expr,
                                ixs_interval *out) {
  size_t idx;
  if (!b || !expr || !out || !b->cache || b->cache_cap == BOUNDS_CACHE_DISABLED)
    return false;
  idx = expr->hash & (b->cache_cap - 1u);
  if (b->cache[idx].expr != expr ||
      b->cache[idx].equality_disabled != (b->equality_disabled_depth != 0))
    return false;
  *out = b->cache[idx].iv;
  return true;
}

static void bounds_cache_store(ixs_bounds *b, ixs_node *expr, ixs_interval iv) {
  size_t idx;
  if (!expr || !b || !b->cache || b->cache_cap == BOUNDS_CACHE_DISABLED)
    return;
  idx = expr->hash & (b->cache_cap - 1u);
  b->cache[idx].expr = expr;
  b->cache[idx].iv = iv;
  b->cache[idx].equality_disabled = b->equality_disabled_depth != 0;
}

IXS_STATIC void ixs_bounds_reset_read_cache(ixs_bounds *b, bool old_oom) {
  bounds_store_invalidate_reads(b);
  if (b)
    b->oom = old_oom;
}

static bool bounds_cacheable_expr(ixs_node *expr) {
  return expr && expr->tag != IXS_INT && expr->tag != IXS_RAT &&
         expr->tag != IXS_SYM;
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

static void bounds_projection_cache_reset_storage(ixs_bounds *b,
                                                  bool transient) {
  bounds_query_reset_arena(b);
  bounds_relation_projection_reset(b, transient);
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

static void bounds_destroy_if_initialized(ixs_bounds *b, bool initialized) {
  if (initialized)
    ixs_bounds_destroy(b);
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
  result = bounds_check_defined_detail(b, expr, oom, limited);
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
static ixs_algebra_status
bounds_collect_relation_component(ixs_bounds *b, ixs_node *expr,
                                  bounds_relation_component *component) {
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

static bool
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

static ixs_algebra_status
bounds_relation_offset_checked(ixs_bounds *b, ixs_node *lhs, ixs_node *rhs,
                               ixs_relation_offset *offset) {
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

/* GCD of a positive modulus and a conservative dividend step. Computing the
 * GCD directly keeps the result representable when a coefficient is
 * INT64_MIN, whose magnitude is one past INT64_MAX. */
static int64_t mod_dividend_gcd(ixs_node *expr, int64_t modulus) {
  int64_t p, q, g;
  uint32_t i;
  switch (expr->tag) {
  case IXS_MUL:
    ixs_node_get_rat(expr->u.mul.coeff, &p, &q);
    return (q == 1) ? ixs_gcd(p, modulus) : 1;
  case IXS_ADD:
    ixs_node_get_rat(expr->u.add.coeff, &p, &q);
    if (q != 1)
      return 1;
    g = ixs_gcd(p, modulus);
    for (i = 0; i < expr->u.add.nterms; i++) {
      ixs_node_get_rat(expr->u.add.terms[i].coeff, &p, &q);
      if (q != 1)
        return 1;
      g = ixs_gcd(g, p);
    }
    return g;
  default:
    return 1;
  }
}

static ixs_check_result bounds_project_equality_integer(ixs_bounds *b,
                                                        ixs_node *expr) {
  bounds_relation_component component;
  ixs_algebra_status status;
  ixs_check_result cached;
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  ixs_bounds_transport_snapshot transport =
      ixs_bounds_query_transport_snapshot(b);
  size_t endpoint_index;
  size_t i;

  if (!ixs_relation_algebra_find_endpoint(&b->relations, expr, &endpoint_index))
    return bounds_integer_check_without_equality(b, expr);
  if (bounds_query_is_tracking(b) &&
      bounds_relation_projection_lookup_integer(b, endpoint_index, &cached))
    return cached;
  status = bounds_collect_relation_component(b, expr, &component);
  if (status == IXS_ALGEBRA_NO_MATCH)
    return bounds_integer_check_without_equality(b, expr);
  if (status != IXS_ALGEBRA_MATCH) {
    bounds_relation_component_destroy(&component);
    return IXS_CHECK_UNKNOWN;
  }
  if (!bounds_publish_relation_component(b, &component)) {
    bounds_relation_component_destroy(&component);
    return IXS_CHECK_UNKNOWN;
  }
  for (i = 0; i < component.count; i++) {
    ixs_check_result current =
        bounds_integer_check_without_equality(b, component.entries[i].node);
    if (b->oom) {
      result = IXS_CHECK_UNKNOWN;
      break;
    }
    if (current != IXS_CHECK_UNKNOWN) {
      if (result != IXS_CHECK_UNKNOWN && result != current) {
        result = IXS_CHECK_UNKNOWN;
        break;
      }
      result = current;
    }
  }
  if (bounds_query_limited_since(b, transport)) {
    result = IXS_CHECK_UNKNOWN;
  } else if (!b->oom && bounds_query_is_tracking(b))
    bounds_relation_projection_complete_integer_component(b, &component,
                                                          result);
  bounds_relation_component_destroy(&component);
  if (b->oom)
    return IXS_CHECK_UNKNOWN;
  return bounds_query_is_tracking(b) &&
                 bounds_relation_projection_lookup_integer(b, endpoint_index,
                                                           &cached)
             ? cached
             : result;
}

IXS_STATIC ixs_check_result ixs_bounds_check_integer_valued(ixs_bounds *b,
                                                            ixs_node *expr) {
  if (!b || !expr || b->oom || ixs_bounds_has_empty(b))
    return IXS_CHECK_UNKNOWN;
  if (b->equality_disabled_depth != 0 ||
      ixs_relation_algebra_edge_count(&b->relations) == 0)
    return bounds_integer_check_without_equality(b, expr);
  return bounds_project_equality_integer(b, expr);
}

static bool bounds_int64_divisible_by_u64(int64_t value, uint64_t modulus) {
  return ixs_int64_magnitude(value) % modulus == 0;
}

static uint64_t bounds_pow_mod(uint64_t base, int32_t exponent,
                               uint64_t modulus) {
  uint64_t result = 1u % modulus;
  while (exponent > 0) {
    if ((exponent & 1) != 0)
      result = ixs_u64_mul_mod(result, base, modulus);
    exponent >>= 1;
    if (exponent != 0)
      base = ixs_u64_mul_mod(base, base, modulus);
  }
  return result;
}

typedef struct {
  ixs_node *representative;
  uint64_t coefficient;
} bounds_residue_group;

static size_t bounds_residue_group_hash(const ixs_node *node) {
  uint64_t mixed = (uint64_t)((uintptr_t)node >> 3);
  mixed ^= mixed >> 33;
  mixed *= UINT64_C(0xff51afd7ed558ccd);
  mixed ^= mixed >> 33;
  return (size_t)mixed;
}

static bool bounds_residue_group_table(ixs_bounds *b, size_t count,
                                       bounds_residue_group **groups,
                                       size_t *capacity) {
  size_t needed;
  size_t result = 16u;
  if (count > SIZE_MAX - count) {
    b->oom = true;
    return false;
  }
  needed = count + count;
  while (result < needed) {
    if (result > SIZE_MAX / 2u || result * 2u > SIZE_MAX / sizeof(**groups)) {
      b->oom = true;
      return false;
    }
    result *= 2u;
  }
  *groups =
      ixs_arena_alloc(b->scratch, result * sizeof(**groups), sizeof(void *));
  if (!*groups) {
    b->oom = true;
    return false;
  }
  memset(*groups, 0, result * sizeof(**groups));
  *capacity = result;
  return true;
}

static bool bounds_add_denominator_lcm(ixs_node *expr, uint64_t *out) {
  uint64_t denominator = 1u;
  uint32_t i;
  int64_t p;
  int64_t q;

  ixs_node_get_rat(expr->u.add.coeff, &p, &q);
  (void)p;
  for (i = 0;; i++) {
    uint64_t factor;
    uint64_t divisor;
    if (q <= 0)
      return false;
    divisor = (uint64_t)q;
    factor = divisor / ixs_u64_gcd(denominator, divisor);
    if (factor != 0 && denominator > (uint64_t)INT64_MAX / factor)
      return false;
    denominator *= factor;
    if (i == expr->u.add.nterms)
      break;
    ixs_node_get_rat(expr->u.add.terms[i].coeff, &p, &q);
  }
  *out = denominator;
  return true;
}

/* Mod(x, k) and x have the same residue modulo every positive divisor of k.
 * Strip only literal, positive moduli and only across integer-valued operands;
 * pointer identity then gives a cheap canonical congruence representative.
 */
static ixs_node *bounds_residue_representative(ixs_bounds *b, ixs_node *expr,
                                               uint64_t modulus,
                                               bool proof_independent) {
  while (
      expr->tag == IXS_MOD && expr->u.binary.rhs->tag == IXS_INT &&
      expr->u.binary.rhs->u.ival > 0 &&
      (uint64_t)expr->u.binary.rhs->u.ival % modulus == 0 &&
      (proof_independent
           ? ixs_node_is_integer_valued(expr->u.binary.lhs) &&
                 ixs_node_is_integer_valued(expr->u.binary.rhs)
           : ixs_bounds_is_integer_with_divinfo(b, expr->u.binary.lhs) &&
                 ixs_bounds_is_integer_with_divinfo(b, expr->u.binary.rhs))) {
    expr = expr->u.binary.lhs;
  }
  return expr;
}

static bool bounds_residue_collect_add_groups(ixs_bounds *b, ixs_node *expr,
                                              uint64_t scale, uint64_t modulus,
                                              bool proof_independent,
                                              bounds_residue_group *groups,
                                              size_t group_capacity,
                                              size_t *ngroups) {
  size_t i;
  int64_t p;
  int64_t q;

  for (i = 0; i < expr->u.add.nterms; i++) {
    ixs_node *term = expr->u.add.terms[i].term;
    ixs_node *representative;
    uint64_t coefficient;
    size_t group;

    ixs_node_get_rat(expr->u.add.terms[i].coeff, &p, &q);
    if (q <= 0 || scale % (uint64_t)q != 0 ||
        (!proof_independent && !ixs_bounds_is_integer_with_divinfo(b, term)))
      return false;
    coefficient = ixs_u64_mul_mod(ixs_int64_normalize_residue(p, modulus),
                                  (scale / (uint64_t)q) % modulus, modulus);
    if (coefficient == 0)
      continue;
    representative =
        bounds_residue_representative(b, term, modulus, proof_independent);
    group = bounds_residue_group_hash(representative) & (group_capacity - 1u);
    while (groups[group].representative &&
           groups[group].representative != representative)
      group = (group + 1u) & (group_capacity - 1u);
    if (!groups[group].representative) {
      groups[group].representative = representative;
      (*ngroups)++;
    }
    groups[group].coefficient =
        ixs_u64_add_mod(groups[group].coefficient, coefficient, modulus);
  }
  return true;
}

static bool bounds_residue_accumulate_add_groups(
    ixs_bounds *b, bounds_residue_group *groups, size_t group_capacity,
    size_t ngroups, uint64_t modulus, bool proof_independent,
    uint64_t *result) {
  size_t i;

  for (i = 0; i < group_capacity && ngroups != 0; i++) {
    uint64_t coefficient = groups[i].coefficient;
    uint64_t reduced;
    uint64_t residue;
    if (!groups[i].representative)
      continue;
    ngroups--;
    if (coefficient == 0)
      continue;
    reduced = modulus / ixs_u64_gcd(coefficient, modulus);
    if (reduced == 1u)
      continue;
    if (!(proof_independent
              ? bounds_known_residue_independent(b, groups[i].representative,
                                                 reduced, &residue)
              : bounds_known_residue(b, groups[i].representative, reduced,
                                     &residue)))
      return false;
    *result = ixs_u64_add_mod(
        *result, ixs_u64_mul_mod(coefficient, residue, modulus), modulus);
  }
  return true;
}

/* Group equal congruence representatives before recursive residue queries.
 * Scratch hashing keeps wide additions linear without a semantic term cap. */
static bool bounds_known_scaled_add_residue(ixs_bounds *b, ixs_node *expr,
                                            uint64_t scale, uint64_t modulus,
                                            uint64_t *out,
                                            bool proof_independent) {
  ixs_arena_mark mark;
  bounds_residue_group *groups;
  size_t group_capacity;
  size_t ngroups = 0;
  uint64_t result;
  int64_t p;
  int64_t q;
  bool success = false;

  if (!b || !expr || expr->tag != IXS_ADD || !out || scale == 0 || modulus == 0)
    return false;
  mark = ixs_arena_save(b->scratch);
  if (!bounds_residue_group_table(b, (size_t)expr->u.add.nterms, &groups,
                                  &group_capacity))
    goto cleanup;

  ixs_node_get_rat(expr->u.add.coeff, &p, &q);
  if (q <= 0 || scale % (uint64_t)q != 0)
    goto cleanup;
  result = ixs_u64_mul_mod(ixs_int64_normalize_residue(p, modulus),
                           (scale / (uint64_t)q) % modulus, modulus);
  if (!bounds_residue_collect_add_groups(b, expr, scale, modulus,
                                         proof_independent, groups,
                                         group_capacity, &ngroups) ||
      !bounds_residue_accumulate_add_groups(b, groups, group_capacity, ngroups,
                                            modulus, proof_independent,
                                            &result))
    goto cleanup;
  *out = result;
  success = true;

cleanup:
  ixs_arena_restore(b->scratch, mark);
  return success;
}

IXS_STATIC bool bounds_add_known_divisible(ixs_bounds *b, ixs_node *expr,
                                           int64_t modulus) {
  uint64_t denominator;
  uint64_t scaled_modulus;
  uint64_t residue;
  uint32_t i;
  int64_t p;
  int64_t q;
  bool has_rational_coefficient;

  if (!b || !expr || expr->tag != IXS_ADD || modulus <= 0)
    return false;
  ixs_node_get_rat(expr->u.add.coeff, &p, &q);
  (void)p;
  has_rational_coefficient = q != 1;
  for (i = 0; !has_rational_coefficient && i < expr->u.add.nterms; i++) {
    ixs_node_get_rat(expr->u.add.terms[i].coeff, &p, &q);
    has_rational_coefficient = q != 1;
  }
  if (!has_rational_coefficient)
    return false;
  if (!bounds_add_denominator_lcm(expr, &denominator) ||
      (uint64_t)modulus > (uint64_t)INT64_MAX / denominator)
    return false;
  scaled_modulus = (uint64_t)modulus * denominator;
  return bounds_known_scaled_add_residue(b, expr, denominator, scaled_modulus,
                                         &residue, true) &&
         residue == 0;
}

static bool bounds_known_symbol_residue(ixs_bounds *b, ixs_node *expr,
                                        uint64_t modulus, uint64_t *out) {
  int64_t stored_modulus;
  int64_t stored_residue;
  if (modulus > (uint64_t)INT64_MAX ||
      !bounds_store_get_modrem(b, expr->u.name, &stored_modulus,
                               &stored_residue) ||
      (uint64_t)stored_modulus % modulus != 0)
    return false;
  *out = (uint64_t)stored_residue % modulus;
  return true;
}

typedef enum {
  BOUNDS_RESIDUE_INITIAL,
  BOUNDS_RESIDUE_ADD_SCAN,
  BOUNDS_RESIDUE_ADD_CHILD,
  BOUNDS_RESIDUE_MUL_SCAN,
  BOUNDS_RESIDUE_MUL_CHILD,
  BOUNDS_RESIDUE_MOD_CHILD,
  BOUNDS_RESIDUE_ASSOC_SCAN,
  BOUNDS_RESIDUE_ASSOC_CHILD,
  BOUNDS_RESIDUE_PW_TOTAL_SCAN,
  BOUNDS_RESIDUE_PW_TOTAL_CHILD,
  BOUNDS_RESIDUE_PW_REACH_SCAN,
  BOUNDS_RESIDUE_PW_REACH_CHILD
} bounds_residue_stage;

typedef struct {
  ixs_node *expr;
  ixs_bounds *bounds;
  uint64_t modulus;
  bounds_query_scope scope;
  bounds_residue_group *groups;
  size_t group_capacity;
  size_t group_index;
  uint64_t result;
  uint64_t coefficient;
  uint64_t reduced_modulus;
  uint32_t index;
  bounds_residue_stage stage;
  ixs_bounds *remaining;
  ixs_bounds *active;
  ixs_check_result branch_truth;
  bool tracked;
  bool have_result;
  bool covered;
  bool remaining_ready;
  bool active_ready;
} bounds_residue_frame;

typedef struct {
  ixs_bounds *root;
  ixs_query_walk walk;
  uint64_t child_residue;
  bool child_success;
  bool proof_independent;
} bounds_residue_query;

static ixs_query_walk_step bounds_residue_push(bounds_residue_query *query,
                                               ixs_bounds *b, ixs_node *expr,
                                               uint64_t modulus) {
  bounds_residue_frame *frame;
  ixs_query_walk_step step;
  if (!b || !expr || modulus == 0 || b->oom)
    return b && b->oom ? IXS_QUERY_WALK_OOM : IXS_QUERY_WALK_STOP;
  step = ixs_query_walk_push(&query->walk, expr);
  if (step != IXS_QUERY_WALK_ADVANCED)
    return step;
  frame = IXS_QUERY_WALK_TOP(&query->walk);
  frame->bounds = b;
  frame->modulus = modulus;
  frame->stage = BOUNDS_RESIDUE_INITIAL;
  return IXS_QUERY_WALK_ADVANCED;
}

static void bounds_residue_destroy_fork(bounds_residue_query *query,
                                        bounds_residue_frame *frame,
                                        bool active) {
  ixs_bounds **fork = active ? &frame->active : &frame->remaining;
  bool *ready = active ? &frame->active_ready : &frame->remaining_ready;
  if (!*ready)
    return;
  if ((*fork)->oom)
    query->root->oom = true;
  ixs_bounds_destroy(*fork);
  *ready = false;
  *fork = NULL;
}

static void bounds_residue_close(bounds_residue_query *query,
                                 bounds_residue_frame *frame, bool success,
                                 uint64_t residue) {
  bounds_residue_destroy_fork(query, frame, true);
  bounds_residue_destroy_fork(query, frame, false);
  if (frame->tracked) {
    bounds_query_cache_entry *entry =
        bounds_query_finish(&frame->scope, success);
    if (entry->outcome == BOUNDS_QUERY_OUTCOME_VALUE)
      entry->result.residue = residue;
    else
      success = false;
  }
  query->child_success = success;
  query->child_residue = residue;
}

static ixs_query_walk_step bounds_residue_complete(bounds_residue_query *query,
                                                   bool success,
                                                   uint64_t residue) {
  bounds_residue_close(query, IXS_QUERY_WALK_TOP(&query->walk), success,
                       residue);
  IXS_QUERY_WALK_POP(&query->walk);
  return IXS_QUERY_WALK_ADVANCED;
}

/* hot */
static void bounds_residue_abort(void *state, void *top) {
  bounds_residue_close(state, top, false, 0);
}

static bool bounds_residue_prepare_add(bounds_residue_query *query,
                                       bounds_residue_frame *frame,
                                       uint64_t scale) {
  ixs_node *expr = frame->expr;
  ixs_bounds *b = frame->bounds;
  size_t group_needed = (size_t)expr->u.add.nterms;
  size_t capacity = 16u;
  size_t i;
  int64_t p;
  int64_t q;

  if (group_needed > SIZE_MAX - group_needed) {
    query->root->oom = true;
    return false;
  }
  group_needed += group_needed;
  while (capacity < group_needed) {
    if (capacity > SIZE_MAX / 2u ||
        capacity * 2u > SIZE_MAX / sizeof(*frame->groups)) {
      query->root->oom = true;
      return false;
    }
    capacity *= 2u;
  }
  frame->groups = ixs_arena_alloc(
      query->root->scratch, capacity * sizeof(*frame->groups), sizeof(void *));
  if (!frame->groups) {
    query->root->oom = true;
    return false;
  }
  memset(frame->groups, 0, capacity * sizeof(*frame->groups));
  frame->group_capacity = capacity;

  ixs_node_get_rat(expr->u.add.coeff, &p, &q);
  if (q <= 0 || scale % (uint64_t)q != 0)
    return false;
  frame->result =
      ixs_u64_mul_mod(ixs_int64_normalize_residue(p, frame->modulus),
                      (scale / (uint64_t)q) % frame->modulus, frame->modulus);

  for (i = 0; i < expr->u.add.nterms; i++) {
    ixs_node *term = expr->u.add.terms[i].term;
    ixs_node *representative;
    uint64_t coefficient;
    size_t group;
    ixs_node_get_rat(expr->u.add.terms[i].coeff, &p, &q);
    if (q <= 0 || scale % (uint64_t)q != 0 ||
        (!query->proof_independent &&
         !ixs_bounds_is_integer_with_divinfo(b, term)))
      return false;
    if (b->oom) {
      query->root->oom = true;
      return false;
    }
    coefficient =
        ixs_u64_mul_mod(ixs_int64_normalize_residue(p, frame->modulus),
                        (scale / (uint64_t)q) % frame->modulus, frame->modulus);
    if (coefficient == 0)
      continue;
    representative = bounds_residue_representative(b, term, frame->modulus,
                                                   query->proof_independent);
    group = bounds_residue_group_hash(representative) & (capacity - 1u);
    while (frame->groups[group].representative &&
           frame->groups[group].representative != representative)
      group = (group + 1u) & (capacity - 1u);
    frame->groups[group].representative = representative;
    frame->groups[group].coefficient = ixs_u64_add_mod(
        frame->groups[group].coefficient, coefficient, frame->modulus);
  }
  frame->group_index = 0;
  frame->stage = BOUNDS_RESIDUE_ADD_SCAN;
  return true;
}

static bool bounds_residue_alloc_fork(bounds_residue_query *query,
                                      bounds_residue_frame *frame,
                                      const ixs_bounds *source, bool active) {
  ixs_bounds **fork = active ? &frame->active : &frame->remaining;
  bool *ready = active ? &frame->active_ready : &frame->remaining_ready;
  *fork = ixs_arena_alloc(query->root->scratch, sizeof(**fork), sizeof(void *));
  if (!*fork) {
    query->root->oom = true;
    return false;
  }
  memset(*fork, 0, sizeof(**fork));
  if (!ixs_bounds_fork(*fork, source)) {
    query->root->oom = true;
    return false;
  }
  *ready = true;
  return true;
}

static bool bounds_residue_start_reachable(bounds_residue_query *query,
                                           bounds_residue_frame *frame) {
  if (!frame->bounds->ctx || frame->expr->u.pw.ncases == 0 ||
      !frame->expr->u.pw.cases)
    return false;
  frame->result = 0;
  frame->have_result = false;
  frame->covered = false;
  frame->index = 0;
  if (!bounds_residue_alloc_fork(query, frame, frame->bounds, false))
    return false;
  frame->stage = BOUNDS_RESIDUE_PW_REACH_SCAN;
  return true;
}

static bool bounds_residue_merge(uint64_t branch, uint64_t *result,
                                 bool *have_result) {
  if (!*have_result) {
    *result = branch;
    *have_result = true;
    return true;
  }
  return *result == branch;
}

static ixs_query_walk_step
bounds_residue_track_frame(bounds_residue_query *query,
                           bounds_residue_frame *frame) {
  bounds_query_cache_entry *cached = NULL;
  bounds_query_enter_result enter;
  if (!bounds_query_should_track(frame->bounds, frame->expr))
    return IXS_QUERY_WALK_NEXT;
  enter = bounds_query_begin(frame->bounds, BOUNDS_QUERY_RESIDUE, frame->expr,
                             frame->modulus, &frame->scope, &cached);
  if (enter == BOUNDS_QUERY_ENTER_CACHED) {
    return bounds_residue_complete(
        query, cached->success, cached->success ? cached->result.residue : 0);
  }
  if (enter != BOUNDS_QUERY_ENTER_STARTED) {
    return bounds_residue_complete(query, false, 0);
  }
  frame->tracked = true;
  return IXS_QUERY_WALK_NEXT;
}

static bool bounds_residue_structural_first(const ixs_node *node) {
  return (node->tag == IXS_ADD || node->tag == IXS_MOD ||
          node->tag == IXS_PIECEWISE) &&
         ixs_node_is_integer_valued(node) && ixs_node_is_known_total(node);
}

static ixs_query_walk_step
bounds_residue_direct_independent(bounds_residue_query *query,
                                  bounds_residue_frame *frame) {
  ixs_bounds *current = frame->bounds;
  ixs_node *node = frame->expr;
  ixs_var_bound *var = NULL;
  ixs_interval iv;
  ixs_bitfacts bits;
  int64_t exact;

  /* Public integrality would re-enter the live exact-proof stack. */
  if (!ixs_node_is_known_total(node)) {
    return bounds_residue_complete(query, false, 0);
  }
  if (node->tag == IXS_ADD &&
      bounds_difference_exact_unit_value(current, node, &exact)) {
    return bounds_residue_complete(
        query, true, ixs_int64_normalize_residue(exact, frame->modulus));
  }
  if (ixs_node_is_integer_valued(node) && frame->modulus == 1u) {
    return bounds_residue_complete(query, true, 0);
  }
  iv = bounds_store_expr_interval(current, node);
  if (node->tag == IXS_SYM)
    var = bounds_store_find_var(current, node->u.name);
  if (var)
    iv = iv.valid ? iv_intersect(iv, var->iv) : var->iv;
  if (ixs_interval_is_point_int(iv, &exact)) {
    return bounds_residue_complete(
        query, true, ixs_int64_normalize_residue(exact, frame->modulus));
  }
  if (ixs_node_is_integer_valued(node) && ixs_u64_is_pow2(frame->modulus) &&
      ixs_bounds_get_bitfacts(current, node, &bits)) {
    uint64_t mask = frame->modulus - 1u;
    if (((bits.known_zero | bits.known_one) & mask) == mask) {
      return bounds_residue_complete(query, true, bits.known_one & mask);
    }
  }
  if (current->oom) {
    query->root->oom = true;
    return IXS_QUERY_WALK_OOM;
  }
  return IXS_QUERY_WALK_NEXT;
}

static ixs_query_walk_step
bounds_residue_direct_tracked(bounds_residue_query *query,
                              bounds_residue_frame *frame) {
  ixs_bounds *current = frame->bounds;
  ixs_node *node = frame->expr;
  ixs_interval iv;
  ixs_bitfacts bits;
  int64_t exact;

  /* Structural ADD skips recursive interval propagation, but an exact unit
   * difference is an O(1) producer invariant and retains its affine offset. */
  if (node->tag == IXS_ADD &&
      bounds_difference_exact_unit_value(current, node, &exact)) {
    return bounds_residue_complete(
        query, true, ixs_int64_normalize_residue(exact, frame->modulus));
  }
  if (bounds_residue_structural_first(node))
    return IXS_QUERY_WALK_NEXT;
  if (ixs_bounds_check_integer_valued(current, node) != IXS_CHECK_TRUE ||
      !ixs_node_is_known_total(node)) {
    if (current->oom)
      query->root->oom = true;
    if (query->root->oom)
      return IXS_QUERY_WALK_OOM;
    return bounds_residue_complete(query, false, 0);
  }
  if (frame->modulus == 1u) {
    return bounds_residue_complete(query, true, 0);
  }
  iv = bounds_get_tracked(current, node);
  if (current->oom) {
    query->root->oom = true;
    return IXS_QUERY_WALK_OOM;
  }
  if (ixs_interval_is_point_int(iv, &exact)) {
    return bounds_residue_complete(
        query, true, ixs_int64_normalize_residue(exact, frame->modulus));
  }
  if (ixs_u64_is_pow2(frame->modulus) &&
      ixs_bounds_get_bitfacts(current, node, &bits)) {
    uint64_t mask = frame->modulus - 1u;
    if (((bits.known_zero | bits.known_one) & mask) == mask) {
      return bounds_residue_complete(query, true, bits.known_one & mask);
    }
  }
  if (current->oom) {
    query->root->oom = true;
    return IXS_QUERY_WALK_OOM;
  }
  return IXS_QUERY_WALK_NEXT;
}

static ixs_query_walk_step
bounds_residue_direct_fact(bounds_residue_query *query,
                           bounds_residue_frame *frame) {
  if (query->proof_independent)
    return bounds_residue_direct_independent(query, frame);
  return bounds_residue_direct_tracked(query, frame);
}

static ixs_query_walk_step
bounds_residue_start_mul(bounds_residue_query *query,
                         bounds_residue_frame *frame) {
  ixs_node *node = frame->expr;
  int64_t p;
  int64_t q;
  ixs_node_get_rat(node->u.mul.coeff, &p, &q);
  if (q != 1) {
    return bounds_residue_complete(query, false, 0);
  }
  frame->coefficient = ixs_int64_normalize_residue(p, frame->modulus);
  frame->reduced_modulus =
      frame->modulus / ixs_u64_gcd(frame->coefficient, frame->modulus);
  if (frame->reduced_modulus == 1u) {
    return bounds_residue_complete(query, true, 0);
  }
  frame->result = 1u % frame->reduced_modulus;
  frame->index = 0;
  frame->stage = BOUNDS_RESIDUE_MUL_SCAN;
  return IXS_QUERY_WALK_ADVANCED;
}

static ixs_query_walk_step
bounds_residue_start_assoc(bounds_residue_query *query,
                           bounds_residue_frame *frame, bool bitwise) {
  ixs_node *node = frame->expr;
  if ((bitwise && !ixs_u64_is_pow2(frame->modulus)) ||
      node->u.assoc.nargs == 0 || !node->u.assoc.args) {
    return bounds_residue_complete(query, false, 0);
  }
  frame->index = 0;
  frame->have_result = false;
  frame->stage = BOUNDS_RESIDUE_ASSOC_SCAN;
  return IXS_QUERY_WALK_ADVANCED;
}

static ixs_query_walk_step
bounds_residue_start_frame(bounds_residue_query *query,
                           bounds_residue_frame *frame) {
  ixs_node *node = frame->expr;
  switch (node->tag) {
  case IXS_INT:
    return bounds_residue_complete(
        query, true, ixs_int64_normalize_residue(node->u.ival, frame->modulus));
  case IXS_RAT:
    return bounds_residue_complete(
        query, node->u.rat.q == 1,
        node->u.rat.q == 1
            ? ixs_int64_normalize_residue(node->u.rat.p, frame->modulus)
            : 0);
  case IXS_SYM: {
    uint64_t residue = 0;
    bool success = bounds_known_symbol_residue(frame->bounds, node,
                                               frame->modulus, &residue);
    return bounds_residue_complete(query, success, residue);
  }
  case IXS_ADD:
    if (!bounds_residue_prepare_add(query, frame, 1u)) {
      if (query->root->oom)
        return IXS_QUERY_WALK_OOM;
      return bounds_residue_complete(query, false, 0);
    }
    return IXS_QUERY_WALK_ADVANCED;
  case IXS_MUL:
    return bounds_residue_start_mul(query, frame);
  case IXS_MOD:
    if (node->u.binary.rhs->tag != IXS_INT || node->u.binary.rhs->u.ival <= 0 ||
        (uint64_t)node->u.binary.rhs->u.ival % frame->modulus != 0) {
      return bounds_residue_complete(query, false, 0);
    }
    frame->stage = BOUNDS_RESIDUE_MOD_CHILD;
    return bounds_residue_push(query, frame->bounds, node->u.binary.lhs,
                               frame->modulus);
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
    return bounds_residue_start_assoc(query, frame, true);
  case IXS_MAX:
  case IXS_MIN:
    return bounds_residue_start_assoc(query, frame, false);
  case IXS_PIECEWISE:
    if (!frame->bounds->ctx || node->u.pw.ncases == 0 || !node->u.pw.cases) {
      return bounds_residue_complete(query, false, 0);
    }
    frame->index = 0;
    frame->have_result = false;
    frame->stage = BOUNDS_RESIDUE_PW_TOTAL_SCAN;
    return IXS_QUERY_WALK_ADVANCED;
  default:
    return bounds_residue_complete(query, false, 0);
  }
}

static ixs_query_walk_step
bounds_residue_resume_add(bounds_residue_query *query,
                          bounds_residue_frame *frame) {
  if (frame->stage == BOUNDS_RESIDUE_ADD_CHILD) {
    if (!query->child_success) {
      return bounds_residue_complete(query, false, 0);
    }
    frame->result =
        ixs_u64_add_mod(frame->result,
                        ixs_u64_mul_mod(frame->coefficient,
                                        query->child_residue, frame->modulus),
                        frame->modulus);
    frame->stage = BOUNDS_RESIDUE_ADD_SCAN;
    return IXS_QUERY_WALK_ADVANCED;
  }
  while (frame->group_index < frame->group_capacity) {
    bounds_residue_group *group = &frame->groups[frame->group_index++];
    if (!group->representative || group->coefficient == 0)
      continue;
    frame->coefficient = group->coefficient;
    frame->reduced_modulus =
        frame->modulus / ixs_u64_gcd(frame->coefficient, frame->modulus);
    if (frame->reduced_modulus == 1u)
      continue;
    frame->stage = BOUNDS_RESIDUE_ADD_CHILD;
    return bounds_residue_push(query, frame->bounds, group->representative,
                               frame->reduced_modulus);
  }
  return bounds_residue_complete(query, true, frame->result);
}

static ixs_query_walk_step
bounds_residue_resume_mul(bounds_residue_query *query,
                          bounds_residue_frame *frame) {
  ixs_node *node = frame->expr;
  if (frame->stage == BOUNDS_RESIDUE_MUL_CHILD) {
    if (!query->child_success) {
      return bounds_residue_complete(query, false, 0);
    }
    frame->result =
        ixs_u64_mul_mod(frame->result,
                        bounds_pow_mod(query->child_residue,
                                       node->u.mul.factors[frame->index].exp,
                                       frame->reduced_modulus),
                        frame->reduced_modulus);
    frame->index++;
    frame->stage = BOUNDS_RESIDUE_MUL_SCAN;
    return IXS_QUERY_WALK_ADVANCED;
  }
  /* Ordinary residue queries have already proved every factor integral and
   * may stop after a zero product.  Independent exact-proof queries have no
   * such callback: visit the remaining factors so a divisible integer factor
   * cannot hide a rational one. */
  if ((!query->proof_independent && frame->result == 0) ||
      frame->index == node->u.mul.nfactors) {
    return bounds_residue_complete(
        query, true,
        ixs_u64_mul_mod(frame->coefficient, frame->result, frame->modulus));
  }
  if (node->u.mul.factors[frame->index].exp < 0) {
    return bounds_residue_complete(query, false, 0);
  }
  frame->stage = BOUNDS_RESIDUE_MUL_CHILD;
  return bounds_residue_push(query, frame->bounds,
                             node->u.mul.factors[frame->index].base,
                             frame->reduced_modulus);
}

static ixs_query_walk_step
bounds_residue_resume_assoc(bounds_residue_query *query,
                            bounds_residue_frame *frame) {
  ixs_node *node = frame->expr;
  if (frame->stage == BOUNDS_RESIDUE_ASSOC_SCAN) {
    if (frame->index == node->u.assoc.nargs) {
      uint64_t result = frame->result;
      if (node->tag == IXS_XOR || node->tag == IXS_AND || node->tag == IXS_OR)
        result &= frame->modulus - 1u;
      return bounds_residue_complete(query, frame->have_result, result);
    }
    frame->stage = BOUNDS_RESIDUE_ASSOC_CHILD;
    return bounds_residue_push(
        query, frame->bounds, node->u.assoc.args[frame->index], frame->modulus);
  }
  if (!query->child_success) {
    return bounds_residue_complete(query, false, 0);
  }
  if (!frame->have_result) {
    frame->result = query->child_residue;
    frame->have_result = true;
  } else if (node->tag == IXS_XOR) {
    frame->result ^= query->child_residue;
  } else if (node->tag == IXS_AND) {
    frame->result &= query->child_residue;
  } else if (node->tag == IXS_OR) {
    frame->result |= query->child_residue;
  } else if (frame->result != query->child_residue) {
    return bounds_residue_complete(query, false, 0);
  }
  frame->index++;
  frame->stage = BOUNDS_RESIDUE_ASSOC_SCAN;
  return IXS_QUERY_WALK_ADVANCED;
}

static bool bounds_residue_add_condition(bounds_residue_query *query,
                                         ixs_bounds *target, ixs_node *cond,
                                         bool truth) {
  struct ixs_node_impl assumption;
  if (ixs_bounds_add_assumption(target, bounds_condition_assumption(
                                            target, cond, truth, &assumption)))
    return true;
  if (target->oom)
    query->root->oom = true;
  return false;
}

static ixs_query_walk_step
bounds_residue_resume_pw_total(bounds_residue_query *query,
                               bounds_residue_frame *frame) {
  ixs_node *node = frame->expr;
  if (frame->stage == BOUNDS_RESIDUE_PW_TOTAL_SCAN) {
    if (frame->index == node->u.pw.ncases) {
      return bounds_residue_complete(query, frame->have_result, frame->result);
    }
    frame->stage = BOUNDS_RESIDUE_PW_TOTAL_CHILD;
    return bounds_residue_push(query, frame->bounds,
                               node->u.pw.cases[frame->index].value,
                               frame->modulus);
  }
  if (!query->child_success ||
      !bounds_residue_merge(query->child_residue, &frame->result,
                            &frame->have_result)) {
    if (query->root->oom)
      return IXS_QUERY_WALK_OOM;
    if (query->proof_independent) {
      return bounds_residue_complete(query, false, 0);
    }
    if (!bounds_residue_start_reachable(query, frame)) {
      if (query->root->oom)
        return IXS_QUERY_WALK_OOM;
      return bounds_residue_complete(query, false, 0);
    }
    return IXS_QUERY_WALK_ADVANCED;
  }
  frame->index++;
  frame->stage = BOUNDS_RESIDUE_PW_TOTAL_SCAN;
  return IXS_QUERY_WALK_ADVANCED;
}

static ixs_query_walk_step
bounds_residue_resume_pw_reach_scan(bounds_residue_query *query,
                                    bounds_residue_frame *frame) {
  ixs_node *node = frame->expr;
  ixs_node *cond;
  ixs_node *value;
  ixs_check_result truth;
  if (frame->remaining->oom) {
    query->root->oom = true;
    return IXS_QUERY_WALK_OOM;
  }
  if (ixs_bounds_has_empty(frame->remaining)) {
    frame->covered = true;
    return bounds_residue_complete(query, frame->have_result, frame->result);
  }
  if (frame->index == node->u.pw.ncases) {
    return bounds_residue_complete(query, frame->covered && frame->have_result,
                                   frame->result);
  }
  cond = node->u.pw.cases[frame->index].cond;
  value = node->u.pw.cases[frame->index].value;
  if (!cond || !value ||
      ixs_bounds_check_defined(frame->remaining, cond) != IXS_CHECK_TRUE) {
    if (frame->remaining->oom)
      query->root->oom = true;
    if (query->root->oom)
      return IXS_QUERY_WALK_OOM;
    return bounds_residue_complete(query, false, 0);
  }
  truth = bounds_condition_truth(frame->remaining, cond);
  if (truth == IXS_CHECK_FALSE) {
    frame->index++;
    return IXS_QUERY_WALK_ADVANCED;
  }
  if (!bounds_residue_alloc_fork(query, frame, frame->remaining, true))
    return IXS_QUERY_WALK_OOM;
  if (!bounds_residue_add_condition(query, frame->active, cond, true)) {
    if (query->root->oom)
      return IXS_QUERY_WALK_OOM;
    return bounds_residue_complete(query, false, 0);
  }
  if (ixs_bounds_has_empty(frame->active)) {
    bounds_residue_destroy_fork(query, frame, true);
    if (truth == IXS_CHECK_TRUE) {
      frame->covered = true;
      return bounds_residue_complete(query, frame->have_result, frame->result);
    }
    if (!bounds_residue_add_condition(query, frame->remaining, cond, false)) {
      if (query->root->oom)
        return IXS_QUERY_WALK_OOM;
      return bounds_residue_complete(query, false, 0);
    }
    frame->index++;
    return IXS_QUERY_WALK_ADVANCED;
  }
  if (ixs_bounds_check_defined(frame->active, value) != IXS_CHECK_TRUE) {
    if (frame->active->oom)
      query->root->oom = true;
    if (query->root->oom)
      return IXS_QUERY_WALK_OOM;
    return bounds_residue_complete(query, false, 0);
  }
  frame->branch_truth = truth;
  frame->stage = BOUNDS_RESIDUE_PW_REACH_CHILD;
  return bounds_residue_push(query, frame->active, value, frame->modulus);
}

static ixs_query_walk_step
bounds_residue_resume_pw_reach_child(bounds_residue_query *query,
                                     bounds_residue_frame *frame) {
  ixs_node *cond = frame->expr->u.pw.cases[frame->index].cond;
  if (!query->child_success ||
      !bounds_residue_merge(query->child_residue, &frame->result,
                            &frame->have_result)) {
    return bounds_residue_complete(query, false, 0);
  }
  bounds_residue_destroy_fork(query, frame, true);
  if (frame->branch_truth == IXS_CHECK_TRUE) {
    frame->covered = true;
    return bounds_residue_complete(query, true, frame->result);
  }
  if (!bounds_residue_add_condition(query, frame->remaining, cond, false)) {
    if (query->root->oom)
      return IXS_QUERY_WALK_OOM;
    return bounds_residue_complete(query, false, 0);
  }
  frame->index++;
  frame->stage = BOUNDS_RESIDUE_PW_REACH_SCAN;
  return IXS_QUERY_WALK_ADVANCED;
}

static ixs_query_walk_step
bounds_residue_resume_frame(bounds_residue_query *query,
                            bounds_residue_frame *frame) {
  switch (frame->stage) {
  case BOUNDS_RESIDUE_ADD_SCAN:
  case BOUNDS_RESIDUE_ADD_CHILD:
    return bounds_residue_resume_add(query, frame);
  case BOUNDS_RESIDUE_MUL_SCAN:
  case BOUNDS_RESIDUE_MUL_CHILD:
    return bounds_residue_resume_mul(query, frame);
  case BOUNDS_RESIDUE_MOD_CHILD:
    return bounds_residue_complete(query, query->child_success,
                                   query->child_success ? query->child_residue
                                                        : 0);
  case BOUNDS_RESIDUE_ASSOC_SCAN:
  case BOUNDS_RESIDUE_ASSOC_CHILD:
    return bounds_residue_resume_assoc(query, frame);
  case BOUNDS_RESIDUE_PW_TOTAL_SCAN:
  case BOUNDS_RESIDUE_PW_TOTAL_CHILD:
    return bounds_residue_resume_pw_total(query, frame);
  case BOUNDS_RESIDUE_PW_REACH_SCAN:
    return bounds_residue_resume_pw_reach_scan(query, frame);
  case BOUNDS_RESIDUE_PW_REACH_CHILD:
    return bounds_residue_resume_pw_reach_child(query, frame);
  case BOUNDS_RESIDUE_INITIAL:
    return bounds_residue_complete(query, false, 0);
  }
  return IXS_QUERY_WALK_ADVANCED;
}

/* hot */
static ixs_query_walk_step bounds_residue_advance(void *state, void *top) {
  bounds_residue_query *query = state;
  bounds_residue_frame *frame = top;
  ixs_query_walk_step step;
  if (frame->stage != BOUNDS_RESIDUE_INITIAL)
    return bounds_residue_resume_frame(query, frame);
  step = bounds_residue_track_frame(query, frame);
  if (step == IXS_QUERY_WALK_NEXT)
    step = bounds_residue_direct_fact(query, frame);
  if (step == IXS_QUERY_WALK_NEXT)
    step = bounds_residue_start_frame(query, frame);
  return step;
}

static bool bounds_known_residue_mode(ixs_bounds *b, ixs_node *expr,
                                      uint64_t modulus, uint64_t *out,
                                      bool proof_independent) {
  ixs_arena_mark mark;
  bounds_residue_query query;
  ixs_query_walk_step step;
  if (!b || !expr || !out || modulus == 0 || b->oom)
    return false;

  mark = ixs_arena_save(b->scratch);
  memset(&query, 0, sizeof(query));
  query.root = b;
  query.proof_independent = proof_independent;
  IXS_QUERY_WALK_INIT(&query.walk, b->scratch, &b->oom, bounds_residue_frame,
                      expr);
  step = bounds_residue_push(&query, b, expr, modulus);
  if (step == IXS_QUERY_WALK_ADVANCED)
    step = ixs_query_walk_drive(&query.walk, &query, bounds_residue_advance,
                                bounds_residue_abort);
  if (query.child_success)
    *out = query.child_residue;
  ixs_arena_restore(b->scratch, mark);
  return step == IXS_QUERY_WALK_ADVANCED && query.child_success;
}

IXS_STATIC bool bounds_known_residue(ixs_bounds *b, ixs_node *expr,
                                     uint64_t modulus, uint64_t *out) {
  return bounds_known_residue_mode(b, expr, modulus, out, false);
}

IXS_STATIC bool bounds_known_residue_independent(ixs_bounds *b, ixs_node *expr,
                                                 uint64_t modulus,
                                                 uint64_t *out) {
  return bounds_known_residue_mode(b, expr, modulus, out, true);
}

#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
IXS_STATIC bool ixs_bounds_known_residue_probe(ixs_bounds *b, ixs_node *expr,
                                               uint64_t modulus,
                                               uint64_t *residue) {
  return bounds_known_residue(b, expr, modulus, residue);
}
#endif

IXS_STATIC ixs_check_result ixs_bounds_check_divisible(ixs_bounds *b,
                                                       ixs_node *expr,
                                                       int64_t modulus) {
  ixs_check_result integer_result;
  ixs_interval iv;
  ixs_bitfacts bits;
  uint64_t magnitude;
  uint64_t residue;
  int64_t exact;

  if (!b || !expr || modulus == 0 || b->oom || ixs_bounds_has_empty(b))
    return IXS_CHECK_UNKNOWN;

  integer_result = ixs_bounds_check_integer_valued(b, expr);
  if (integer_result != IXS_CHECK_TRUE)
    return integer_result;

  magnitude = ixs_int64_magnitude(modulus);
  if (magnitude == 1u)
    return IXS_CHECK_TRUE;

  iv = ixs_bounds_get(b, expr);
  if (b->oom)
    return IXS_CHECK_UNKNOWN;
  if (ixs_interval_is_point_int(iv, &exact))
    return bounds_int64_divisible_by_u64(exact, magnitude) ? IXS_CHECK_TRUE
                                                           : IXS_CHECK_FALSE;

  if (magnitude <= (uint64_t)INT64_MAX) {
    bool proven = ixs_bounds_is_known_divisible(b, expr, (int64_t)magnitude);
    if (b->oom)
      return IXS_CHECK_UNKNOWN;
    if (proven)
      return IXS_CHECK_TRUE;
  }

  if (magnitude == (uint64_t)INT64_MAX + 1u) {
    bool has_bits = ixs_bounds_get_bitfacts(b, expr, &bits);
    if (b->oom)
      return IXS_CHECK_UNKNOWN;
    if (has_bits && (bits.known_zero & (magnitude - 1u)) == magnitude - 1u)
      return IXS_CHECK_TRUE;
  }

  /* The residue engine is branch-sensitive for Piecewise and can prove a
   * uniform zero residue even when interval and low-bit joins lose it.  Reuse
   * that exact proof here instead of teaching divisibility a second Piecewise
   * traversal. */
  if (bounds_known_residue(b, expr, magnitude, &residue))
    return residue == 0u ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
  if (b->oom)
    return IXS_CHECK_UNKNOWN;

  return IXS_CHECK_UNKNOWN;
}

IXS_STATIC ixs_check_result ixs_bounds_check_congruent(ixs_bounds *b,
                                                       ixs_node *expr,
                                                       int64_t modulus,
                                                       int64_t residue) {
  ixs_check_result integer_result;
  uint64_t actual;
  uint64_t magnitude;
  uint64_t expected;
  if (!b || !expr || modulus == 0 || b->oom || ixs_bounds_has_empty(b))
    return IXS_CHECK_UNKNOWN;
  integer_result = ixs_bounds_check_integer_valued(b, expr);
  if (integer_result != IXS_CHECK_TRUE)
    return integer_result;
  magnitude = ixs_int64_magnitude(modulus);
  expected = ixs_int64_normalize_residue(residue, magnitude);
  if (!bounds_known_residue(b, expr, magnitude, &actual))
    return IXS_CHECK_UNKNOWN;
  return actual == expected ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
}

static ixs_interval bounds_get_and_mask(ixs_bounds *b, ixs_node *expr) {
  int64_t mask = 0;
  uint32_t i;
  bool have_mask = false;
  if (expr->u.assoc.nargs == 0 || !expr->u.assoc.args)
    return ixs_interval_unknown();
  for (i = 0; i < expr->u.assoc.nargs; i++) {
    ixs_node *arg = expr->u.assoc.args[i];
    if (!ixs_bounds_is_integer_with_divinfo(b, arg))
      return ixs_interval_unknown();
    if (arg->tag == IXS_INT && arg->u.ival >= 0 &&
        (!have_mask || arg->u.ival < mask)) {
      mask = arg->u.ival;
      have_mask = true;
    }
  }
  return have_mask ? ixs_interval_range(0, 1, mask, 1) : ixs_interval_unknown();
}

static ixs_interval bounds_get_xor(ixs_bounds *b, ixs_node *expr) {
  ixs_interval arg_iv, result;
  ixs_bitfacts arg_bits, next_bits, result_bits;
  int64_t arg_hi, max_hi = 0;
  uint64_t span, possible, required;
  uint32_t i;
  bool have_bits;

  if (expr->u.assoc.nargs == 0 || !expr->u.assoc.args)
    return ixs_interval_unknown();

  result = ixs_interval_unknown();
  result.valid = true;
  result.lo_p = 0;
  result.lo_q = 1;
  result.lo_inf = false;
  result.hi_inf = false;
  for (i = 0; i < expr->u.assoc.nargs; i++) {
    ixs_node *arg = expr->u.assoc.args[i];
    if (!ixs_bounds_is_integer_with_divinfo(b, arg))
      return ixs_interval_unknown();
    arg_iv = ixs_bounds_get(b, arg);
    if (!ixs_interval_lower_at_least(&arg_iv, 0, 1))
      return ixs_interval_unknown();
    if (arg_iv.hi_inf) {
      result.hi_inf = true;
      continue;
    }
    arg_hi = ixs_rat_floor(arg_iv.hi_p, arg_iv.hi_q);
    if (arg_hi > max_hi)
      max_hi = arg_hi;
  }
  if (result.hi_inf) {
    ixs_interval_set_hi_pos_inf(&result);
    return result;
  }

  span = bounds_bitfacts_value_span_mask((uint64_t)max_hi);
  possible = span;
  required = 0;
  have_bits = ixs_bounds_get_bitfacts(b, expr->u.assoc.args[0], &result_bits);
  for (i = 1; have_bits && i < expr->u.assoc.nargs; i++) {
    if (!ixs_bounds_get_bitfacts(b, expr->u.assoc.args[i], &arg_bits)) {
      have_bits = false;
      break;
    }
    bounds_bitfacts_apply_xor(&next_bits, &result_bits, &arg_bits);
    result_bits = next_bits;
  }
  if (have_bits) {
    possible &= ~result_bits.known_zero;
    required = result_bits.known_one & span;
  }
  if (required > possible)
    return ixs_interval_unknown();
  result.lo_p = (int64_t)required;
  result.hi_p = (int64_t)possible;
  result.hi_q = 1;
  return result;
}

static ixs_algebra_status bounds_get_truncating_remainder_range(
    ixs_bounds *b, ixs_node *expr, bool expression_defined, ixs_interval *out);

static void bounds_note_truncating_range_status(ixs_bounds *b,
                                                ixs_algebra_status status) {
  if (status == IXS_ALGEBRA_OOM)
    b->oom = true;
  else if (status == IXS_ALGEBRA_INVALID)
    bounds_query_note_invalid(b);
  else if (status == IXS_ALGEBRA_LIMITED)
    bounds_query_note_limit(b);
}

typedef struct {
  ixs_node *representative;
  ixs_interval interval;
  uint64_t modulus;
  uint64_t coefficient;
  uint32_t count;
} bounds_add_residue_group;

/* A chain of positive literal Mods preserves its dividend modulo the gcd of
 * those literals. Structural domain proofs avoid a recursive range query
 * while bounds_get_add is already aggregating the surrounding ADD. */
static bool bounds_add_mod_chain(ixs_node *term, ixs_node **representative,
                                 uint64_t *modulus) {
  uint64_t result = 0;

  while (term->tag == IXS_MOD && term->u.binary.rhs->tag == IXS_INT &&
         term->u.binary.rhs->u.ival > 0) {
    uint64_t divisor = (uint64_t)term->u.binary.rhs->u.ival;
    ixs_node *dividend = term->u.binary.lhs;
    if (!ixs_node_is_integer_valued(dividend) ||
        !ixs_node_is_known_total(dividend))
      return false;
    result = result == 0 ? divisor : ixs_u64_gcd(result, divisor);
    term = dividend;
  }
  if (result <= 1u)
    return false;
  *representative = term;
  *modulus = result;
  return true;
}

/* Direct Mod chains with one representative form congruent sub-sums. Build
 * each independent sub-sum once, then intersect it with the residue already
 * understood by the generic residue engine. Scratch hashing makes this
 * expected O(n) in the number of ADD terms. */
static bool bounds_get_add_residue_groups(ixs_bounds *b, ixs_node *expr,
                                          size_t candidate_count,
                                          ixs_interval *out) {
  ixs_arena_mark mark;
  bounds_add_residue_group *groups;
  size_t needed;
  size_t capacity = 16u;
  size_t ngroups = 0;
  size_t slot;
  uint32_t i;
  ixs_interval baseline;
  ixs_interval result;

  if (candidate_count < 2u || candidate_count > SIZE_MAX - candidate_count)
    return false;
  needed = candidate_count + candidate_count;
  while (capacity < needed) {
    if (capacity > SIZE_MAX / 2u ||
        capacity * 2u > SIZE_MAX / sizeof(*groups)) {
      b->oom = true;
      return false;
    }
    capacity *= 2u;
  }

  mark = ixs_arena_save(b->scratch);
  groups =
      ixs_arena_alloc(b->scratch, capacity * sizeof(*groups), sizeof(void *));
  if (!groups) {
    b->oom = true;
    ixs_arena_restore(b->scratch, mark);
    return false;
  }
  memset(groups, 0, capacity * sizeof(*groups));
  result = ixs_bounds_get(b, expr->u.add.coeff);
  /* Regrouping changes addition order. Retain the original accumulation so
   * overflow widening can only be tightened, never replaced. */
  baseline = result;

  for (i = 0; i < expr->u.add.nterms; i++) {
    ixs_node *term = expr->u.add.terms[i].term;
    ixs_node *representative;
    ixs_interval term_interval = ixs_bounds_get(b, term);
    ixs_interval scaled;
    uint64_t modulus;
    int64_t p;
    int64_t q;
    size_t group;

    ixs_node_get_rat(expr->u.add.terms[i].coeff, &p, &q);
    scaled = iv_mul_const(term_interval, p, q);
    baseline = iv_add(baseline, scaled);
    if (q != 1 || !bounds_add_mod_chain(term, &representative, &modulus)) {
      result = iv_add(result, scaled);
      continue;
    }

    group = bounds_residue_group_hash(representative) & (capacity - 1u);
    while (groups[group].representative &&
           groups[group].representative != representative)
      group = (group + 1u) & (capacity - 1u);
    if (!groups[group].representative) {
      groups[group].representative = representative;
      groups[group].interval = scaled;
      groups[group].modulus = modulus;
      groups[group].coefficient = ixs_int64_normalize_residue(p, modulus);
      groups[group].count = 1u;
      ngroups++;
      continue;
    }

    groups[group].interval = iv_add(groups[group].interval, scaled);
    groups[group].modulus = ixs_u64_gcd(groups[group].modulus, modulus);
    groups[group].coefficient %= groups[group].modulus;
    groups[group].coefficient =
        ixs_u64_add_mod(groups[group].coefficient,
                        ixs_int64_normalize_residue(p, groups[group].modulus),
                        groups[group].modulus);
    groups[group].count++;
  }

  for (slot = 0; slot < capacity && ngroups != 0; slot++) {
    bounds_add_residue_group *group = &groups[slot];
    ixs_interval interval;
    uint64_t reduced;
    uint64_t representative_residue = 0;
    uint64_t residue;

    if (!group->representative)
      continue;
    ngroups--;
    interval = group->interval;
    reduced = group->modulus / ixs_u64_gcd(group->coefficient, group->modulus);
    if (group->count > 1u &&
        (reduced == 1u ||
         bounds_known_residue(b, group->representative, reduced,
                              &representative_residue))) {
      residue = ixs_u64_mul_mod(group->coefficient, representative_residue,
                                group->modulus);
      interval = ixs_interval_intersect_congruence(
          interval, (int64_t)group->modulus, (int64_t)residue);
    }
    result = iv_add(result, interval);
  }

  if (b->oom) {
    ixs_arena_restore(b->scratch, mark);
    return false;
  }
  *out = iv_intersect(baseline, result);
  ixs_arena_restore(b->scratch, mark);
  return true;
}

static inline ixs_interval bounds_get_add(ixs_bounds *b, ixs_node *expr) {
  uint32_t i;
  size_t residue_candidate_count = 0;
  ixs_interval result;

  for (i = 0; i < expr->u.add.nterms; i++) {
    ixs_node *term = expr->u.add.terms[i].term;
    if (term->tag == IXS_MOD && term->u.binary.rhs->tag == IXS_INT &&
        term->u.binary.rhs->u.ival > 0)
      residue_candidate_count++;
  }

  result = ixs_bounds_get(b, expr->u.add.coeff);
  if (residue_candidate_count >= 2u) {
    (void)bounds_get_add_residue_groups(b, expr, residue_candidate_count,
                                        &result);
  } else {
    for (i = 0; i < expr->u.add.nterms; i++) {
      int64_t cp;
      int64_t cq;
      ixs_interval ti = ixs_bounds_get(b, expr->u.add.terms[i].term);
      ixs_interval scaled;

      ixs_node_get_rat(expr->u.add.terms[i].coeff, &cp, &cq);
      scaled = iv_mul_const(ti, cp, cq);
      result = iv_add(result, scaled);
    }
  }
  if (!b->oom && b->nexprs != 0)
    result =
        iv_intersect(result, bounds_assume_get_proportional_range(b, expr));
  if (!b->oom && b->ctx && b->nexprs != 0 &&
      !ixs_node_is_zero(expr->u.add.coeff)) {
    ixs_node *base;
    ixs_algebra_status status =
        ixs_additive_row_without_constant(b->ctx, expr, &base);
    if (status == IXS_ALGEBRA_OOM) {
      b->oom = true;
    } else if (status == IXS_ALGEBRA_MATCH && base != expr) {
      ixs_interval base_iv = ixs_bounds_get(b, base);
      ixs_interval offset = ixs_bounds_get(b, expr->u.add.coeff);
      result = iv_intersect(result, iv_add(base_iv, offset));
    }
  }
  return result;
}

static inline ixs_interval bounds_get_mul(ixs_bounds *b, ixs_node *expr) {
  uint32_t i;
  int64_t cp, cq;
  ixs_interval result;
  ixs_node_get_rat(expr->u.mul.coeff, &cp, &cq);
  result = ixs_interval_exact(cp, cq);
  for (i = 0; i < expr->u.mul.nfactors; i++) {
    int32_t exp = expr->u.mul.factors[i].exp;
    int64_t exp64 = exp;
    uint32_t magnitude;
    ixs_interval fi = ixs_bounds_get(b, expr->u.mul.factors[i].base);
    ixs_interval powered;
    if (!fi.valid)
      return ixs_interval_unknown();
    if (exp == 0)
      return ixs_interval_unknown();
    magnitude = (uint32_t)(exp64 < 0 ? -exp64 : exp64);
    powered = iv_pow(fi, magnitude);
    if (exp < 0)
      powered = iv_recip(powered);
    if (!powered.valid)
      return ixs_interval_unknown();
    result = iv_mul(result, powered);
  }
  return result;
}

typedef struct {
  uint64_t hi;
  uint64_t lo;
} bounds_u128;

static bounds_u128 bounds_u128_mul(uint64_t lhs, uint64_t rhs) {
  uint64_t lhs_lo = (uint32_t)lhs;
  uint64_t lhs_hi = lhs >> 32;
  uint64_t rhs_lo = (uint32_t)rhs;
  uint64_t rhs_hi = rhs >> 32;
  uint64_t p0 = lhs_lo * rhs_lo;
  uint64_t p1 = lhs_lo * rhs_hi;
  uint64_t p2 = lhs_hi * rhs_lo;
  bounds_u128 result;
  uint64_t add;
  uint64_t before;
  uint64_t carry = 0;

  result.lo = p0;
  result.hi = lhs_hi * rhs_hi + (p1 >> 32) + (p2 >> 32);
  add = p1 << 32;
  before = result.lo;
  result.lo += add;
  carry += result.lo < before;
  add = p2 << 32;
  before = result.lo;
  result.lo += add;
  carry += result.lo < before;
  result.hi += carry;
  return result;
}

static bounds_u128 bounds_u128_add_u64(bounds_u128 value, uint64_t addend) {
  uint64_t before = value.lo;
  value.lo += addend;
  value.hi += value.lo < before;
  return value;
}

/* Divide a two-limb unsigned integer by a nonzero 64-bit divisor.  Callers
 * prove the quotient fits one limb; reject rather than truncate if that
 * contract is violated. */
static bool bounds_u128_divmod_u64(bounds_u128 value, uint64_t divisor,
                                   uint64_t *quotient, uint64_t *remainder) {
  uint64_t q = 0;
  uint64_t r = 0;
  unsigned bit = 128u;
  if (!divisor || !quotient || !remainder)
    return false;
  while (bit-- != 0u) {
    uint64_t incoming =
        bit >= 64u ? (value.hi >> (bit - 64u)) & 1u : (value.lo >> bit) & 1u;
    bool high = (r >> 63) != 0;
    r = (r << 1) | incoming;
    if (high || r >= divisor) {
      r -= divisor;
      if (bit >= 64u)
        return false;
      q |= UINT64_C(1) << bit;
    }
  }
  *quotient = q;
  *remainder = r;
  return true;
}

static uint64_t bounds_triangular_mod_u64(uint64_t n) {
  uint64_t prior = n - 1u;
  if ((n & 1u) == 0)
    n >>= 1;
  else
    prior >>= 1;
  return n * prior;
}

/* The result is intentionally modulo 2^64.  Subtracting two such sums below
 * recovers an exact count because that difference is at most n. */
static bool bounds_floor_sum_mod_u64(uint64_t n, uint64_t modulus, uint64_t a,
                                     uint64_t b, uint64_t *out) {
  uint64_t answer = 0;
  if (!modulus || !out)
    return false;
  for (;;) {
    if (a >= modulus) {
      uint64_t quotient = a / modulus;
      answer += bounds_triangular_mod_u64(n) * quotient;
      a %= modulus;
    }
    if (b >= modulus) {
      answer += n * (b / modulus);
      b %= modulus;
    }
    {
      bounds_u128 top = bounds_u128_add_u64(bounds_u128_mul(a, n), b);
      uint64_t next_n;
      uint64_t next_b;
      uint64_t previous_modulus;
      if (!bounds_u128_divmod_u64(top, modulus, &next_n, &next_b))
        return false;
      if (next_n == 0)
        break;
      n = next_n;
      b = next_b;
      previous_modulus = modulus;
      modulus = a;
      a = previous_modulus;
      if (modulus == 0)
        return false;
    }
  }
  *out = answer;
  return true;
}

static bool bounds_mod_progression_count_less(uint64_t count, uint64_t modulus,
                                              uint64_t step, uint64_t first,
                                              uint64_t threshold,
                                              uint64_t *out) {
  uint64_t base_sum;
  uint64_t shifted_sum;
  uint64_t at_least;
  if (!out || threshold > modulus || first >= modulus || step >= modulus)
    return false;
  if (threshold == 0) {
    *out = 0;
    return true;
  }
  if (threshold == modulus) {
    *out = count;
    return true;
  }
  if (!bounds_floor_sum_mod_u64(count, modulus, step, first, &base_sum) ||
      !bounds_floor_sum_mod_u64(count, modulus, step,
                                first + modulus - threshold, &shifted_sum))
    return false;
  at_least = shifted_sum - base_sum;
  if (at_least > count)
    return false;
  *out = count - at_least;
  return true;
}

static bool bounds_mod_progression_min(uint64_t count, uint64_t modulus,
                                       uint64_t step, uint64_t first,
                                       uint64_t *out) {
  uint64_t lower = 0;
  uint64_t upper;
  if (!count || !modulus || !out)
    return false;
  step %= modulus;
  first %= modulus;
  upper = modulus - 1u;
  while (lower < upper) {
    uint64_t midpoint = lower + (upper - lower) / 2u;
    uint64_t below;
    if (!bounds_mod_progression_count_less(count, modulus, step, first,
                                           midpoint + 1u, &below))
      return false;
    if (below != 0)
      upper = midpoint;
    else
      lower = midpoint + 1u;
  }
  *out = lower;
  return true;
}

static bool bounds_mod_progression_extrema(uint64_t count, uint64_t modulus,
                                           uint64_t step, uint64_t first,
                                           uint64_t *minimum,
                                           uint64_t *maximum) {
  uint64_t reflected_minimum;
  step %= modulus;
  first %= modulus;
  if (!bounds_mod_progression_min(count, modulus, step, first, minimum) ||
      !bounds_mod_progression_min(count, modulus,
                                  step == 0 ? 0 : modulus - step,
                                  modulus - 1u - first, &reflected_minimum))
    return false;
  *maximum = modulus - 1u - reflected_minimum;
  return true;
}

/* O(1) for a full residue cycle and O(log^2 modulus) for a partial cycle.
 * The latter uses floor-sum counting to avoid an arbitrary enumeration cap. */
static bool bounds_symbol_mod_range(ixs_bounds *b, ixs_node *symbol,
                                    const ixs_interval *iv, int64_t modulus,
                                    ixs_interval *out) {
  int64_t known_modulus, known_remainder, lo, hi, current, delta, first;
  uint64_t steps, cycle, step, residue, min_residue, max_residue;
  uint64_t g;

  if (symbol->tag != IXS_SYM || !iv->valid || iv->lo_inf || iv->hi_inf ||
      modulus <= 0 ||
      !bounds_store_get_modrem(b, symbol->u.name, &known_modulus,
                               &known_remainder))
    return false;

  lo = ixs_rat_ceil(iv->lo_p, iv->lo_q);
  hi = ixs_rat_floor(iv->hi_p, iv->hi_q);
  if (lo > hi)
    return false;
  current = lo % known_modulus;
  if (current < 0)
    current += known_modulus;
  delta = known_remainder >= current
              ? known_remainder - current
              : known_modulus - (current - known_remainder);
  if (!ixs_safe_add(lo, delta, &first) || first > hi)
    return false;

  steps = ((uint64_t)hi - (uint64_t)first) / (uint64_t)known_modulus;
  step = (uint64_t)known_modulus % (uint64_t)modulus;
  residue = ixs_int64_normalize_residue(first, (uint64_t)modulus);
  g = ixs_u64_gcd(step, (uint64_t)modulus);
  cycle = (uint64_t)modulus / g;
  if (steps >= cycle - 1u) {
    min_residue = residue % g;
    max_residue = min_residue + (uint64_t)modulus - g;
  } else {
    if (!bounds_mod_progression_extrema(steps + 1u, (uint64_t)modulus, step,
                                        residue, &min_residue, &max_residue))
      return false;
  }

  *out = ixs_interval_range((int64_t)min_residue, 1, (int64_t)max_residue, 1);
  return true;
}

/* An expression-wide stride class maps through Mod to one class modulo the
 * gcd of that stride and the positive literal divisor.  This gives the full
 * sound residue envelope without first expanding a Piecewise interval. */
static bool bounds_structural_mod_range(ixs_bounds *b, ixs_node *dividend,
                                        int64_t modulus, ixs_interval *out) {
  uint64_t stride;
  uint64_t common;
  uint64_t residue;
  uint64_t upper;
  if (modulus <= 0 || !bounds_known_stride(b, dividend, &stride))
    return false;
  common = ixs_u64_gcd(stride, (uint64_t)modulus);
  if (common <= 1u || !bounds_known_residue(b, dividend, common, &residue))
    return false;
  residue %= common;
  upper = residue + (uint64_t)modulus - common;
  if (upper > (uint64_t)INT64_MAX)
    return false;
  *out = ixs_interval_range((int64_t)residue, 1, (int64_t)upper, 1);
  return true;
}

static ixs_interval bounds_get_positive_mod(ixs_bounds *b, ixs_node *lhs,
                                            int64_t modulus) {
  bool residue_tried = false;
  ixs_interval pi;
  int64_t exact_lhs;
  uint64_t residue;
  ixs_interval congruent;

  if (b->has_modrem && ixs_node_contains_piecewise(lhs) &&
      ixs_node_is_integer_valued(lhs) && ixs_node_is_known_total(lhs)) {
    residue_tried = true;
    if (bounds_structural_mod_range(b, lhs, modulus, &congruent))
      return congruent;
    if (bounds_known_residue(b, lhs, (uint64_t)modulus, &residue))
      return ixs_interval_exact((int64_t)residue, 1);
  }
  pi = ixs_bounds_get(b, lhs);
  if (ixs_interval_is_point_int(pi, &exact_lhs))
    return ixs_interval_exact(
        (int64_t)ixs_int64_normalize_residue(exact_lhs, (uint64_t)modulus), 1);
  if (b->has_modrem && !residue_tried &&
      bounds_known_residue(b, lhs, (uint64_t)modulus, &residue))
    return ixs_interval_exact((int64_t)residue, 1);
  if (b->has_modrem &&
      bounds_symbol_mod_range(b, lhs, &pi, modulus, &congruent))
    return congruent;
  if (pi.valid && pi.lo_q == 1 && pi.hi_q == 1 && pi.lo_p >= 0 &&
      pi.hi_p < modulus)
    return pi;
  if (ixs_node_is_integer_valued(lhs)) {
    int64_t divisor = mod_dividend_gcd(lhs, modulus);
    return ixs_interval_range(0, 1, modulus - divisor, 1);
  }
  return ixs_interval_unknown();
}

static inline ixs_interval bounds_get_mod(ixs_bounds *b, ixs_node *expr) {
  ixs_node *lhs = expr->u.binary.lhs;
  ixs_node *m = expr->u.binary.rhs;
  ixs_interval mi = ixs_bounds_get(b, m);
  int64_t exact_m;

  if (ixs_interval_is_point_int(mi, &exact_m) && exact_m > 0)
    return bounds_get_positive_mod(b, lhs, exact_m);

  if (ixs_node_is_integer_valued(lhs) && ixs_node_is_integer_valued(m) &&
      ixs_interval_lower_at_least(&mi, 1, 1)) {
    ixs_interval li = ixs_bounds_get(b, lhs);
    ixs_interval result = ixs_interval_unknown();
    result.valid = true;
    result.lo_inf = false;
    result.lo_p = 0;
    result.lo_q = 1;
    if (mi.hi_inf) {
      ixs_interval_set_hi_pos_inf(&result);
    } else {
      int64_t upper = ixs_rat_floor(mi.hi_p, mi.hi_q);
      if (!ixs_safe_sub(upper, 1, &result.hi_p))
        ixs_interval_set_hi_pos_inf(&result);
      else {
        result.hi_q = 1;
        result.hi_inf = false;
      }
    }
    /* For a nonnegative dividend and positive divisor, Mod(lhs, m) <= lhs.
     * Keep only the dividend's upper endpoint: its lower endpoint is not a
     * lower bound on the remainder. */
    if (ixs_interval_lower_at_least(&li, 0, 1) && !li.hi_inf &&
        (result.hi_inf ||
         ixs_rat_cmp(li.hi_p, li.hi_q, result.hi_p, result.hi_q) < 0)) {
      result.hi_p = li.hi_p;
      result.hi_q = li.hi_q;
      result.hi_inf = false;
    }
    return result;
  }
  return ixs_interval_unknown();
}

static inline ixs_interval bounds_get_round(ixs_bounds *b, ixs_node *expr,
                                            bool is_ceil) {
  ixs_interval ai = ixs_bounds_get(b, expr->u.unary.arg);
  ixs_interval result;
  if (!ai.valid)
    return ixs_interval_unknown();
  if (is_ceil) {
    result = ixs_interval_range(ixs_rat_ceil(ai.lo_p, ai.lo_q), 1,
                                ixs_rat_ceil(ai.hi_p, ai.hi_q), 1);
  } else {
    result = ixs_interval_range(ixs_rat_floor(ai.lo_p, ai.lo_q), 1,
                                ixs_rat_floor(ai.hi_p, ai.hi_q), 1);
  }
  result.lo_inf = ai.lo_inf;
  result.hi_inf = ai.hi_inf;
  return result;
}

static inline ixs_interval bounds_get_trunc(ixs_bounds *b, ixs_node *expr) {
  ixs_interval ai = ixs_bounds_get(b, expr->u.unary.arg);
  ixs_interval result;
  if (!ai.valid)
    return ixs_interval_unknown();
  result = ixs_interval_range(ai.lo_p / ai.lo_q, 1, ai.hi_p / ai.hi_q, 1);
  result.lo_inf = ai.lo_inf;
  result.hi_inf = ai.hi_inf;
  return result;
}

static inline void interval_set_max_lower(ixs_interval *result,
                                          const ixs_interval *li,
                                          const ixs_interval *ri) {
  if (li->lo_inf && !ri->lo_inf) {
    result->lo_p = ri->lo_p;
    result->lo_q = ri->lo_q;
  } else if (!li->lo_inf && ri->lo_inf) {
    result->lo_p = li->lo_p;
    result->lo_q = li->lo_q;
  } else if (ixs_rat_cmp(li->lo_p, li->lo_q, ri->lo_p, ri->lo_q) >= 0) {
    result->lo_p = li->lo_p;
    result->lo_q = li->lo_q;
    result->lo_inf = li->lo_inf;
  } else {
    result->lo_p = ri->lo_p;
    result->lo_q = ri->lo_q;
    result->lo_inf = ri->lo_inf;
  }
}

static inline void interval_set_max_upper(ixs_interval *result,
                                          const ixs_interval *li,
                                          const ixs_interval *ri) {
  if (li->hi_inf || ri->hi_inf) {
    ixs_interval_set_hi_pos_inf(result);
  } else if (ixs_rat_cmp(li->hi_p, li->hi_q, ri->hi_p, ri->hi_q) >= 0) {
    result->hi_p = li->hi_p;
    result->hi_q = li->hi_q;
  } else {
    result->hi_p = ri->hi_p;
    result->hi_q = ri->hi_q;
  }
}

static inline void interval_set_min_lower(ixs_interval *result,
                                          const ixs_interval *li,
                                          const ixs_interval *ri) {
  if (li->lo_inf || ri->lo_inf) {
    ixs_interval_set_lo_neg_inf(result);
  } else if (ixs_rat_cmp(li->lo_p, li->lo_q, ri->lo_p, ri->lo_q) <= 0) {
    result->lo_p = li->lo_p;
    result->lo_q = li->lo_q;
  } else {
    result->lo_p = ri->lo_p;
    result->lo_q = ri->lo_q;
  }
}

static inline void interval_set_min_upper(ixs_interval *result,
                                          const ixs_interval *li,
                                          const ixs_interval *ri) {
  if (li->hi_inf && !ri->hi_inf) {
    result->hi_p = ri->hi_p;
    result->hi_q = ri->hi_q;
  } else if (!li->hi_inf && ri->hi_inf) {
    result->hi_p = li->hi_p;
    result->hi_q = li->hi_q;
  } else if (ixs_rat_cmp(li->hi_p, li->hi_q, ri->hi_p, ri->hi_q) <= 0) {
    result->hi_p = li->hi_p;
    result->hi_q = li->hi_q;
    result->hi_inf = li->hi_inf;
  } else {
    result->hi_p = ri->hi_p;
    result->hi_q = ri->hi_q;
    result->hi_inf = ri->hi_inf;
  }
}

static bool bounds_rationals_are_opposites(ixs_node *lhs, ixs_node *rhs) {
  int64_t lhs_p, lhs_q, rhs_p, rhs_q, negative_lhs;
  ixs_node_get_rat(lhs, &lhs_p, &lhs_q);
  ixs_node_get_rat(rhs, &rhs_p, &rhs_q);
  return lhs_q == rhs_q && ixs_safe_neg(lhs_p, &negative_lhs) &&
         negative_lhs == rhs_p;
}

static bool bounds_nodes_are_opposites(ixs_node *lhs, ixs_node *rhs) {
  uint32_t i;
  if (lhs->tag == IXS_MUL || rhs->tag == IXS_MUL) {
    if (lhs->tag != IXS_MUL)
      return rhs->u.mul.nfactors == 1u && rhs->u.mul.factors[0].base == lhs &&
             rhs->u.mul.factors[0].exp == 1 &&
             node_coeff_is(rhs->u.mul.coeff, -1);
    if (rhs->tag != IXS_MUL)
      return bounds_nodes_are_opposites(rhs, lhs);
    if (lhs->u.mul.nfactors != rhs->u.mul.nfactors ||
        !bounds_rationals_are_opposites(lhs->u.mul.coeff, rhs->u.mul.coeff))
      return false;
    for (i = 0; i < lhs->u.mul.nfactors; i++) {
      if (lhs->u.mul.factors[i].base != rhs->u.mul.factors[i].base ||
          lhs->u.mul.factors[i].exp != rhs->u.mul.factors[i].exp)
        return false;
    }
    return true;
  }
  if (lhs->tag != IXS_ADD)
    return rhs->tag == IXS_ADD && ixs_node_is_zero(rhs->u.add.coeff) &&
           rhs->u.add.nterms == 1u && rhs->u.add.terms[0].term == lhs &&
           node_coeff_is(rhs->u.add.terms[0].coeff, -1);
  if (rhs->tag != IXS_ADD)
    return bounds_nodes_are_opposites(rhs, lhs);
  if (lhs->u.add.nterms != rhs->u.add.nterms ||
      !bounds_rationals_are_opposites(lhs->u.add.coeff, rhs->u.add.coeff))
    return false;
  for (i = 0; i < lhs->u.add.nterms; i++) {
    if (lhs->u.add.terms[i].term != rhs->u.add.terms[i].term ||
        !bounds_rationals_are_opposites(lhs->u.add.terms[i].coeff,
                                        rhs->u.add.terms[i].coeff))
      return false;
  }
  return true;
}

static inline ixs_interval bounds_get_extrema(ixs_bounds *b, ixs_node *expr,
                                              bool is_max) {
  ixs_interval result, arg, merged, absolute_lower;
  uint32_t i;
  if (expr->u.assoc.nargs == 0 || !expr->u.assoc.args)
    return ixs_interval_unknown();
  absolute_lower = ixs_interval_unknown();
  if (is_max) {
    for (i = 0; i < expr->u.assoc.nargs; i++) {
      uint32_t j;
      for (j = i + 1u; j < expr->u.assoc.nargs; j++) {
        int64_t lower;
        if (!bounds_nodes_are_opposites(expr->u.assoc.args[i],
                                        expr->u.assoc.args[j]))
          continue;
        lower =
            (bounds_store_contains_nonzero(b, expr->u.assoc.args[i]) ||
             bounds_store_contains_nonzero(b, expr->u.assoc.args[j])) &&
                    ixs_bounds_is_integer_with_divinfo(b, expr->u.assoc.args[i])
                ? 1
                : 0;
        absolute_lower.valid = true;
        absolute_lower.lo_inf = false;
        absolute_lower.lo_p = lower;
        absolute_lower.lo_q = 1;
        ixs_interval_set_hi_pos_inf(&absolute_lower);
        break;
      }
      if (absolute_lower.valid)
        break;
    }
  }
  result = ixs_bounds_get(b, expr->u.assoc.args[0]);
  if (!result.valid)
    return absolute_lower;
  for (i = 1; i < expr->u.assoc.nargs; i++) {
    arg = ixs_bounds_get(b, expr->u.assoc.args[i]);
    if (!arg.valid)
      return absolute_lower;
    merged = ixs_interval_unknown();
    merged.valid = true;
    if (is_max) {
      interval_set_max_lower(&merged, &result, &arg);
      interval_set_max_upper(&merged, &result, &arg);
    } else {
      interval_set_min_lower(&merged, &result, &arg);
      interval_set_min_upper(&merged, &result, &arg);
    }
    result = merged;
  }
  return absolute_lower.valid ? iv_intersect(result, absolute_lower) : result;
}

static ixs_cmp_op bounds_negate_cmp_op(ixs_cmp_op op) {
  switch (op) {
  case IXS_CMP_GT:
    return IXS_CMP_LE;
  case IXS_CMP_GE:
    return IXS_CMP_LT;
  case IXS_CMP_LT:
    return IXS_CMP_GE;
  case IXS_CMP_LE:
    return IXS_CMP_GT;
  case IXS_CMP_EQ:
    return IXS_CMP_NE;
  case IXS_CMP_NE:
    return IXS_CMP_EQ;
  }
  return op;
}

static ixs_node *bounds_condition_assumption(ixs_bounds *b, ixs_node *cond,
                                             bool value,
                                             struct ixs_node_impl *storage) {
  if (!b->ctx)
    return NULL;
  memset(storage, 0, sizeof(*storage));
  storage->tag = IXS_CMP;
  storage->u.binary.rhs = b->ctx->node_zero;
  if (cond->tag == IXS_CMP) {
    storage->u.binary.lhs = cond->u.binary.lhs;
    storage->u.binary.rhs = cond->u.binary.rhs;
    storage->u.binary.cmp_op =
        value ? cond->u.binary.cmp_op
              : bounds_negate_cmp_op(cond->u.binary.cmp_op);
  } else {
    storage->u.binary.lhs = cond;
    storage->u.binary.cmp_op = value ? IXS_CMP_NE : IXS_CMP_EQ;
  }
  return storage;
}

static ixs_check_result bounds_condition_truth(ixs_bounds *b, ixs_node *cond) {
  struct ixs_node_impl cmp;
  if (ixs_node_is_known_false(cond))
    return IXS_CHECK_FALSE;
  if (ixs_node_is_known_true(cond))
    return IXS_CHECK_TRUE;
  if (!bounds_condition_assumption(b, cond, true, &cmp))
    return IXS_CHECK_UNKNOWN;
  return ixs_bounds_check(b, &cmp);
}

static bool bounds_piecewise_active(ixs_bounds *owner, ixs_bounds *remaining,
                                    ixs_node *cond, ixs_node *value,
                                    ixs_interval *result, bool *have_result) {
  ixs_arena_mark mark = ixs_arena_save(owner->scratch);
  ixs_bounds active;
  struct ixs_node_impl assumption;
  ixs_interval branch;
  bool active_ready = false;
  bool ok = false;

  memset(&active, 0, sizeof(active));
  if (!ixs_bounds_fork(&active, remaining)) {
    owner->oom = true;
    goto cleanup;
  }
  active_ready = true;
  if (!ixs_bounds_add_assumption(
          &active,
          bounds_condition_assumption(&active, cond, true, &assumption))) {
    if (active.oom)
      owner->oom = true;
    goto cleanup;
  }
  if (ixs_bounds_has_empty(&active)) {
    ok = true;
    goto cleanup;
  }
  if (ixs_bounds_check_defined(&active, value) != IXS_CHECK_TRUE)
    goto cleanup;
  branch = ixs_bounds_get(&active, value);
  if (!branch.valid)
    goto cleanup;
  if (!*have_result) {
    *result = branch;
    *have_result = true;
  } else {
    *result = iv_hull(*result, branch);
  }
  ok = true;

cleanup:
  if (active.oom)
    owner->oom = true;
  if (active_ready)
    ixs_bounds_destroy(&active);
  ixs_arena_restore(owner->scratch, mark);
  return ok;
}

static ixs_interval bounds_get_piecewise(ixs_bounds *b, ixs_node *expr) {
  ixs_interval result = ixs_interval_unknown();
  ixs_arena_mark outer_mark;
  ixs_bounds remaining;
  bool have_result = false;
  bool covered = false;
  bool failed = false;
  bool remaining_ready = false;
  uint32_t i;

  if (!b->ctx || expr->u.pw.ncases == 0 ||
      (expr->u.pw.ncases > 0 && !expr->u.pw.cases))
    return result;
  if (b->range_pw_depth == SIZE_MAX) {
    b->oom = true;
    return result;
  }
  outer_mark = ixs_arena_save(b->scratch);
  b->range_pw_depth++;
  if (!ixs_bounds_fork(&remaining, b)) {
    b->oom = true;
    failed = true;
    goto cleanup;
  }
  remaining_ready = true;

  for (i = 0; i < expr->u.pw.ncases; i++) {
    ixs_node *cond = expr->u.pw.cases[i].cond;
    ixs_node *value = expr->u.pw.cases[i].value;
    ixs_check_result truth;
    struct ixs_node_impl assumption;

    if (!cond || !value || remaining.oom) {
      failed = true;
      break;
    }
    if (ixs_bounds_has_empty(&remaining)) {
      covered = true;
      break;
    }
    if (ixs_bounds_check_defined(&remaining, cond) != IXS_CHECK_TRUE) {
      failed = true;
      break;
    }
    truth = bounds_condition_truth(&remaining, cond);
    if (truth == IXS_CHECK_FALSE)
      continue;

    if (!bounds_piecewise_active(b, &remaining, cond, value, &result,
                                 &have_result)) {
      failed = true;
      break;
    }
    if (truth == IXS_CHECK_TRUE) {
      covered = true;
      break;
    }
    if (!ixs_bounds_add_assumption(
            &remaining, bounds_condition_assumption(&remaining, cond, false,
                                                    &assumption))) {
      b->oom = true;
      failed = true;
      break;
    }
  }

  if (!failed && !covered && ixs_bounds_has_empty(&remaining))
    covered = true;
  if (!covered)
    failed = true;

cleanup:
  bounds_destroy_if_initialized(&remaining, remaining_ready);
  ixs_arena_restore(b->scratch, outer_mark);
  b->range_pw_depth--;
  if (failed || !have_result)
    return ixs_interval_unknown();
  return result;
}

static inline ixs_interval bounds_get_propagated(ixs_bounds *b,
                                                 ixs_node *expr) {
  if (!expr)
    return ixs_interval_unknown();

  switch (expr->tag) {
  case IXS_INT:
    return ixs_interval_exact(expr->u.ival, 1);
  case IXS_RAT:
    return ixs_interval_exact(expr->u.rat.p, expr->u.rat.q);
  case IXS_ADD:
    return bounds_get_add(b, expr);
  case IXS_MUL:
    return bounds_get_mul(b, expr);
  case IXS_MOD:
    return bounds_get_mod(b, expr);
  case IXS_FLOOR:
    return bounds_get_round(b, expr, false);
  case IXS_CEIL:
    return bounds_get_round(b, expr, true);
  case IXS_TRUNC:
    return bounds_get_trunc(b, expr);
  case IXS_MAX:
    return bounds_get_extrema(b, expr, true);
  case IXS_MIN:
    return bounds_get_extrema(b, expr, false);
  case IXS_AND:
    return ixs_node_is_bool_valued(expr) ? ixs_interval_range(0, 1, 1, 1)
                                         : bounds_get_and_mask(b, expr);
  case IXS_XOR:
    return bounds_get_xor(b, expr);
  case IXS_CMP:
  case IXS_NOT:
  case IXS_OR:
    return ixs_node_is_bool_valued(expr) ? ixs_interval_range(0, 1, 1, 1)
                                         : ixs_interval_unknown();
  case IXS_PIECEWISE:
    return bounds_get_piecewise(b, expr);
  default:
    return ixs_interval_unknown();
  }
}

static bool bounds_expr_may_need_canonical_alias(const ixs_node *expr) {
  if (!expr)
    return false;
  switch (expr->tag) {
  case IXS_ADD:
  case IXS_MUL:
  case IXS_MOD:
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
    return true;
  default:
    return false;
  }
}

IXS_STATIC ixs_interval bounds_get_intrinsic(ixs_bounds *b, ixs_node *expr) {
  ixs_interval iv;
  ixs_node *canon = NULL;
  ixs_var_bound *var = NULL;
  int64_t exact;
  if (!b)
    return ixs_interval_unknown();
  if (bounds_cacheable_expr(expr) && bounds_cache_lookup(b, expr, &iv))
    return iv;

  if (expr && expr->tag == IXS_SYM) {
    /* Retain the indexed symbol result through override intersection. */
    var = bounds_store_find_var(b, expr->u.name);
    iv = var ? var->iv : ixs_interval_unknown();
  } else {
    iv = bounds_get_propagated(b, expr);
  }
  if (b->nexprs && expr) {
    iv = iv_intersect(iv, bounds_store_expr_interval(b, expr));
    canon = bounds_expr_may_need_canonical_alias(expr)
                ? bounds_canonical_expr(b, expr)
                : expr;
    if (canon && canon != expr)
      iv = iv_intersect(iv, bounds_store_expr_interval(b, canon));
  }
  if (var && var->modulus > 0)
    iv = ixs_interval_intersect_congruence(iv, var->modulus, var->remainder);
  if (bounds_difference_exact_unit_value(b, expr, &exact) ||
      (canon && canon != expr &&
       bounds_difference_exact_unit_value(b, canon, &exact)))
    iv = iv_intersect(iv, ixs_interval_exact(exact, 1));
  if (bounds_cacheable_expr(expr))
    bounds_cache_store(b, expr, iv);
  return iv;
}

static ixs_interval bounds_get_without_equality(ixs_bounds *b, ixs_node *expr) {
  ixs_interval iv;
  assert(b->equality_disabled_depth != UINT_MAX);
  b->equality_disabled_depth++;
  iv = bounds_get_intrinsic(b, expr);
  b->equality_disabled_depth--;
  return iv;
}

typedef struct {
  bounds_relation_projection_bound lower;
  bounds_relation_projection_bound upper;
  bool have_valid;
  bool publish;
  bool semantic_conflict;
} bounds_equality_range_state;

static bool bounds_equality_range_collect_peer(
    ixs_bounds *b, const bounds_relation_component_entry *component_entry,
    bounds_equality_range_state *state) {
  ixs_interval peer = bounds_get_without_equality(b, component_entry->node);
  int comparison;

  if (b->oom)
    return false;
  if (bounds_query_is_tracking(b))
    bounds_relation_projection_stage_range(b, component_entry->endpoint_index,
                                           peer);
  if (!peer.valid)
    return true;
  state->have_valid = true;
  if (!peer.lo_inf) {
    if (state->lower.present &&
        !bounds_relation_projection_bound_cmp(
            peer.lo_p, peer.lo_q, component_entry->offset, state->lower.p,
            state->lower.q, state->lower.peer_offset, &comparison)) {
      bounds_query_note_invalid(b);
      return false;
    }
    if (!state->lower.present || comparison > 0) {
      state->lower.p = peer.lo_p;
      state->lower.q = peer.lo_q;
      state->lower.peer_offset = component_entry->offset;
      state->lower.present = true;
    }
  }
  if (!peer.hi_inf) {
    if (state->upper.present &&
        !bounds_relation_projection_bound_cmp(
            peer.hi_p, peer.hi_q, component_entry->offset, state->upper.p,
            state->upper.q, state->upper.peer_offset, &comparison)) {
      bounds_query_note_invalid(b);
      return false;
    }
    if (!state->upper.present || comparison < 0) {
      state->upper.p = peer.hi_p;
      state->upper.q = peer.hi_q;
      state->upper.peer_offset = component_entry->offset;
      state->upper.present = true;
    }
  }
  return true;
}

static void
bounds_equality_range_collect_peers(ixs_bounds *b,
                                    const bounds_relation_component *component,
                                    bounds_equality_range_state *state) {
  size_t i;
  for (i = 0; i < component->count; i++) {
    if (!bounds_equality_range_collect_peer(b, &component->entries[i], state)) {
      state->publish = false;
      break;
    }
  }
}

static void bounds_equality_range_validate(ixs_bounds *b,
                                           bounds_equality_range_state *state) {
  int comparison;
  if (!state->publish || !state->lower.present || !state->upper.present)
    return;
  if (!bounds_relation_projection_bound_cmp(
          state->lower.p, state->lower.q, state->lower.peer_offset,
          state->upper.p, state->upper.q, state->upper.peer_offset,
          &comparison)) {
    bounds_query_note_invalid(b);
    state->publish = false;
    return;
  }
  state->semantic_conflict = comparison > 0;
}

static ixs_interval
bounds_equality_range_publish(ixs_bounds *b,
                              const bounds_relation_component *component,
                              size_t endpoint_index, ixs_interval intrinsic,
                              const bounds_equality_range_state *state) {
  ixs_interval result = ixs_interval_unknown();
  bool tracking = bounds_query_is_tracking(b);
  size_t i;
  for (i = 0; state->publish && !b->oom && i < component->count; i++) {
    ixs_interval projected = ixs_interval_unknown();
    bool project = !state->semantic_conflict && state->have_valid;
    if (tracking) {
      projected = bounds_relation_projection_complete_range(
          b, component->entries[i].endpoint_index, component->entries[i].offset,
          &state->lower, &state->upper, project);
    } else if (project) {
      ixs_interval peer_intrinsic =
          component->entries[i].endpoint_index == endpoint_index
              ? intrinsic
              : ixs_interval_unknown();
      projected = bounds_relation_projection_apply(
          peer_intrinsic, component->entries[i].offset, &state->lower,
          &state->upper);
    }
    if (component->entries[i].endpoint_index == endpoint_index)
      result = projected;
  }
  return result;
}

/* Project peer ranges back through node == expr + offset. */
static ixs_interval bounds_project_equality_range(ixs_bounds *b, ixs_node *expr,
                                                  ixs_interval intrinsic) {
  bounds_relation_component component;
  ixs_algebra_status status;
  bounds_equality_range_state state = {{0, 1, {0, 0, false}, false},
                                       {0, 1, {0, 0, false}, false},
                                       false,
                                       true,
                                       false};
  ixs_interval cached;
  ixs_interval result;
  ixs_bounds_transport_snapshot transport =
      ixs_bounds_query_transport_snapshot(b);
  size_t endpoint_index;

  if (!ixs_relation_algebra_find_endpoint(&b->relations, expr, &endpoint_index))
    return intrinsic;
  if (bounds_query_is_tracking(b) &&
      bounds_relation_projection_lookup_range(b, endpoint_index, &cached))
    return cached;
  status = bounds_collect_relation_component(b, expr, &component);
  if (status == IXS_ALGEBRA_NO_MATCH)
    return intrinsic;
  if (status != IXS_ALGEBRA_MATCH) {
    bounds_relation_component_destroy(&component);
    return ixs_interval_unknown();
  }
  if (!bounds_publish_relation_component(b, &component)) {
    bounds_relation_component_destroy(&component);
    return ixs_interval_unknown();
  }
  bounds_equality_range_collect_peers(b, &component, &state);
  if (bounds_query_limited_since(b, transport))
    state.publish = false;
  bounds_equality_range_validate(b, &state);
  result = bounds_equality_range_publish(b, &component, endpoint_index,
                                         intrinsic, &state);
  bounds_relation_component_destroy(&component);
  return b->oom ? ixs_interval_unknown() : result;
}

static ixs_interval bounds_get_query_impl(ixs_bounds *b, ixs_node *expr) {
  ixs_interval result;
  if (!b)
    return ixs_interval_unknown();
  result = bounds_get_intrinsic(b, expr);
  if (!b->oom && ixs_relation_algebra_edge_count(&b->relations) != 0 &&
      b->equality_disabled_depth == 0)
    result = bounds_project_equality_range(b, expr, result);
  return result;
}

static ixs_interval bounds_get_tracked_one(ixs_bounds *b, ixs_node *expr) {
  bounds_query_scope scope;
  bounds_query_cache_entry *cached;
  bounds_query_cache_entry *entry;
  bounds_query_enter_result status;
  ixs_interval result;
  if (!bounds_query_should_track(b, expr))
    return bounds_get_query_impl(b, expr);
  status =
      bounds_query_begin(b, BOUNDS_QUERY_INTERVAL, expr, 0, &scope, &cached);
  if (status == BOUNDS_QUERY_ENTER_CACHED)
    return cached->result.interval;
  if (status != BOUNDS_QUERY_ENTER_STARTED)
    return ixs_interval_unknown();
  result = bounds_get_query_impl(b, expr);
  entry = bounds_query_finish(&scope, result.valid);
  if (entry->outcome == BOUNDS_QUERY_OUTCOME_VALUE)
    entry->result.interval = result;
  else
    result = ixs_interval_unknown();
  return result;
}

typedef struct {
  ixs_node *expr;
  bounds_query_scope scope;
  uint32_t next_child;
  uint32_t child_count;
  bool tracked;
  bool children_ready;
} bounds_interval_frame;

typedef struct {
  ixs_bounds *bounds;
  ixs_query_walk walk;
  ixs_interval child;
} bounds_interval_query;

static uint32_t bounds_interval_child_count(const ixs_node *expr) {
  switch (expr->tag) {
  case IXS_ADD:
    return expr->u.add.nterms + 1u;
  case IXS_MUL:
    return expr->u.mul.nfactors;
  case IXS_MOD:
    /* MOD first tries structural congruence proofs that do not need either
     * operand's interval.  Eagerly walking the operands here defeats that
     * fast path, most notably by expanding nested Piecewise values that the
     * congruence proof would otherwise avoid.  Leave MOD dependencies lazy;
     * any interval genuinely needed by the transfer is queried there. */
    return 0u;
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
    return 1u;
  case IXS_MAX:
  case IXS_MIN:
  case IXS_AND:
  case IXS_XOR:
    return expr->u.assoc.nargs;
  default:
    return 0u;
  }
}

static ixs_node *bounds_interval_child(const ixs_node *expr, uint32_t index) {
  switch (expr->tag) {
  case IXS_ADD:
    return index == 0u ? expr->u.add.coeff : expr->u.add.terms[index - 1u].term;
  case IXS_MUL:
    return expr->u.mul.factors[index].base;
  case IXS_MOD:
    return index == 0u ? expr->u.binary.lhs : expr->u.binary.rhs;
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
    return expr->u.unary.arg;
  case IXS_MAX:
  case IXS_MIN:
  case IXS_AND:
  case IXS_XOR:
    return expr->u.assoc.args[index];
  default:
    return NULL;
  }
}

static void bounds_interval_close(bounds_interval_query *query,
                                  bounds_interval_frame *frame,
                                  ixs_interval result) {
  if (frame->tracked) {
    bounds_query_cache_entry *entry =
        bounds_query_finish(&frame->scope, result.valid);
    if (entry->outcome == BOUNDS_QUERY_OUTCOME_VALUE)
      entry->result.interval = result;
    else
      result = ixs_interval_unknown();
  }
  query->child = result;
}

static ixs_query_walk_step
bounds_interval_complete(bounds_interval_query *query, ixs_interval result) {
  bounds_interval_close(query, IXS_QUERY_WALK_TOP(&query->walk), result);
  IXS_QUERY_WALK_POP(&query->walk);
  return IXS_QUERY_WALK_ADVANCED;
}

/* hot */
static void bounds_interval_abort(void *state, void *top) {
  bounds_interval_close(state, top, ixs_interval_unknown());
}

/* hot */
static ixs_query_walk_step bounds_interval_advance(void *state, void *top) {
  bounds_interval_query *query = state;
  bounds_interval_frame *frame = top;
  ixs_bounds *b = query->bounds;
  ixs_interval unknown = ixs_interval_unknown();
  if (!frame->children_ready) {
    bounds_query_cache_entry *cached = NULL;
    bounds_query_enter_result enter = bounds_query_begin(
        b, BOUNDS_QUERY_INTERVAL, frame->expr, 0, &frame->scope, &cached);
    if (enter == BOUNDS_QUERY_ENTER_CACHED)
      return bounds_interval_complete(query, cached->result.interval);
    if (enter != BOUNDS_QUERY_ENTER_STARTED)
      return bounds_interval_complete(query, unknown);
    frame->tracked = true;
    frame->children_ready = true;
    frame->child_count = bounds_interval_child_count(frame->expr);
  }
  if (frame->next_child < frame->child_count) {
    ixs_node *child = bounds_interval_child(frame->expr, frame->next_child++);
    return child ? ixs_query_walk_push(&query->walk, child)
                 : IXS_QUERY_WALK_STOP;
  }
  {
    bool old_evaluating = b->interval_evaluating;
    ixs_interval result;
    b->interval_evaluating = true;
    result = bounds_get_query_impl(b, frame->expr);
    b->interval_evaluating = old_evaluating;
    return b->oom ? IXS_QUERY_WALK_OOM
                  : bounds_interval_complete(query, result);
  }
}

/* Precompute structural children in an explicit postorder. Existing transfer
 * functions then read those child intervals through the query memo. This
 * keeps their well-tested arithmetic intact while making deep normalized DAGs
 * linear in unique nodes and independent of the C call stack. Piecewise
 * branch forks start their own owner-local postorder under branch facts. */
static ixs_interval bounds_get_interval_iterative(ixs_bounds *b,
                                                  ixs_node *expr) {
  ixs_arena_mark mark;
  bounds_interval_query query;
  ixs_query_walk_step step;
  ixs_interval unknown = ixs_interval_unknown();
  if (!b || !expr || b->oom)
    return unknown;
  if (!bounds_query_should_track(b, expr))
    return bounds_get_query_impl(b, expr);

  mark = ixs_arena_save(b->scratch);
  memset(&query, 0, sizeof(query));
  query.bounds = b;
  IXS_QUERY_WALK_INIT(&query.walk, b->scratch, &b->oom, bounds_interval_frame,
                      expr);
  step = ixs_query_walk_push(&query.walk, expr);
  if (step == IXS_QUERY_WALK_ADVANCED)
    step = ixs_query_walk_drive(&query.walk, &query, bounds_interval_advance,
                                bounds_interval_abort);
  ixs_arena_restore(b->scratch, mark);
  if (step == IXS_QUERY_WALK_ADVANCED)
    return query.child;
  b->interval_evaluating = false;
  return unknown;
}

IXS_STATIC ixs_interval bounds_get_tracked(ixs_bounds *b, ixs_node *expr) {
  if (b && b->interval_evaluating)
    return bounds_get_tracked_one(b, expr);
  return bounds_get_interval_iterative(b, expr);
}

IXS_STATIC ixs_interval ixs_bounds_get(ixs_bounds *b, ixs_node *expr) {
  return bounds_get_tracked(b, expr);
}

static bool bounds_exact_integer_difference(ixs_bounds *b, ixs_node *difference,
                                            int64_t *delta) {
  int64_t p;
  int64_t q;
  if (!b || !difference || !delta || b->oom || b->contradiction ||
      ixs_node_is_sentinel(difference))
    return false;
  if (ixs_node_is_const(difference)) {
    ixs_node_get_rat(difference, &p, &q);
    if (q == 1) {
      *delta = p;
      return true;
    }
  }
  return ixs_interval_is_point_int(ixs_bounds_get(b, difference), delta);
}

static bool bounds_interval_is_zero(ixs_interval iv) {
  return iv.valid && !iv.lo_inf && !iv.hi_inf && iv.lo_p == 0 && iv.hi_p == 0;
}

static bool bounds_has_zero_nonzero_conflict(ixs_bounds *b) {
  size_t i;
  for (i = 0; i < b->nnonzero; i++) {
    ixs_node *expr = b->nonzero[i];
    ixs_interval iv;
    if (ixs_node_is_zero(expr))
      return true;
    if (expr->tag == IXS_SYM) {
      ixs_var_bound *var = bounds_store_find_var(b, expr->u.name);
      if (var && bounds_interval_is_zero(var->iv))
        return true;
    }
    iv = bounds_store_expr_interval(b, expr);
    if (bounds_interval_is_zero(iv))
      return true;
  }
  return false;
}

static bool bounds_cache_empty_result(ixs_bounds *b, bool result) {
  b->empty_cache_valid = true;
  b->empty_cache_value = result;
  return result;
}

/* Cache hit is O(1); miss scans variables, expressions, and exclusions. */
IXS_STATIC bool ixs_bounds_has_empty(ixs_bounds *b) {
  size_t i;

  if (b->empty_cache_valid)
    return b->empty_cache_value;
  if (b->contradiction)
    return bounds_cache_empty_result(b, true);

  for (i = 0; i < b->nvars; i++) {
    bounds_store_refine_var_bits(b, &b->vars[i]);
    if (b->contradiction)
      return bounds_cache_empty_result(b, true);
    if (ixs_interval_is_empty(b->vars[i].iv))
      return bounds_cache_empty_result(b, true);
  }

  for (i = 0; i < b->nexprs; i++) {
    ixs_interval iv = b->exprs[i].iv;
    ixs_var_bound *var = NULL;
    if (!iv.valid || ixs_interval_is_empty(iv))
      return bounds_cache_empty_result(b, true);
    if (b->exprs[i].expr->tag == IXS_SYM)
      var = bounds_store_find_var(b, b->exprs[i].expr->u.name);
    if (var) {
      iv = iv_intersect(iv, var->iv);
      if (!iv.valid || ixs_interval_is_empty(iv) ||
          (var->modulus > 0 && !ixs_interval_has_congruent_integer(
                                   &iv, var->modulus, var->remainder)))
        return bounds_cache_empty_result(b, true);
    }
  }

  if (bounds_has_zero_nonzero_conflict(b))
    return bounds_cache_empty_result(b, true);

  return bounds_cache_empty_result(b, false);
}

typedef struct {
  ixs_node *dividend;
  int64_t modulus;
  int64_t remainder;
} ixs_mod_query;

static bool bounds_extract_mod_query(ixs_node *expr, ixs_mod_query *out) {
  ixs_node *mod_node;
  int64_t rem_val;

  if (!expr || !out)
    return false;

  if (expr->tag == IXS_MOD) {
    mod_node = expr;
    rem_val = 0;
  } else if (expr->tag == IXS_ADD && expr->u.add.nterms == 1 &&
             expr->u.add.terms[0].term->tag == IXS_MOD) {
    int64_t cp, cq, kp, kq;
    ixs_node_get_rat(expr->u.add.terms[0].coeff, &cp, &cq);
    ixs_node_get_rat(expr->u.add.coeff, &kp, &kq);
    if (cq != 1 || kq != 1)
      return false;
    if (cp == 1) {
      if (kp == INT64_MIN)
        return false;
      rem_val = -kp;
    } else if (cp == -1) {
      rem_val = kp;
    } else {
      return false;
    }
    mod_node = expr->u.add.terms[0].term;
  } else {
    return false;
  }

  if (mod_node->u.binary.rhs->tag != IXS_INT ||
      mod_node->u.binary.rhs->u.ival <= 0)
    return false;

  out->dividend = mod_node->u.binary.lhs;
  out->modulus = mod_node->u.binary.rhs->u.ival;
  out->remainder = rem_val;
  return true;
}

static ixs_check_result bounds_check_mod_query(ixs_bounds *b, ixs_node *cmp) {
  ixs_mod_query q;
  int64_t actual;
  bool known = false;
  bool equal;

  if (cmp->u.binary.cmp_op != IXS_CMP_EQ && cmp->u.binary.cmp_op != IXS_CMP_NE)
    return IXS_CHECK_UNKNOWN;
  if (!bounds_extract_mod_query(cmp->u.binary.lhs, &q))
    return IXS_CHECK_UNKNOWN;

  if (q.remainder < 0 || q.remainder >= q.modulus) {
    if (cmp->u.binary.cmp_op == IXS_CMP_EQ)
      return IXS_CHECK_FALSE;
    return IXS_CHECK_TRUE;
  }

  if (q.dividend->tag == IXS_INT) {
    actual = ((q.dividend->u.ival % q.modulus) + q.modulus) % q.modulus;
    known = true;
  } else if (q.dividend->tag == IXS_SYM) {
    int64_t sym_mod, sym_rem;
    if (bounds_store_get_modrem(b, q.dividend->u.name, &sym_mod, &sym_rem) &&
        sym_mod % q.modulus == 0) {
      actual = sym_rem % q.modulus;
      known = true;
    }
  }

  if (!known && q.remainder == 0 &&
      ixs_bounds_is_known_divisible(b, q.dividend, q.modulus)) {
    actual = 0;
    known = true;
  }

  if (!known)
    return IXS_CHECK_UNKNOWN;

  equal = actual == q.remainder;
  if (cmp->u.binary.cmp_op == IXS_CMP_EQ)
    return equal ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
  return equal ? IXS_CHECK_FALSE : IXS_CHECK_TRUE;
}

static ixs_check_result check_equal_result(ixs_cmp_op op, bool equal) {
  if (op == IXS_CMP_EQ)
    return equal ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
  if (op == IXS_CMP_NE)
    return equal ? IXS_CHECK_FALSE : IXS_CHECK_TRUE;
  return IXS_CHECK_UNKNOWN;
}

static ixs_check_result bounds_check_pow2_query(ixs_bounds *b, ixs_node *cmp,
                                                ixs_node *expr, int64_t value) {
  const char *name;
  struct ixs_node_impl sym_tmp;
  if (!extract_pow2_and(expr, &name))
    return IXS_CHECK_UNKNOWN;
  memset(&sym_tmp, 0, sizeof(sym_tmp));
  sym_tmp.tag = IXS_SYM;
  sym_tmp.u.name = name;
  if (!ixs_bounds_is_pow2_or_zero(b, &sym_tmp))
    return IXS_CHECK_UNKNOWN;
  return check_equal_result(cmp->u.binary.cmp_op, value == 0);
}

static ixs_check_result bounds_check_and_mask_query(ixs_bounds *b,
                                                    ixs_node *cmp,
                                                    ixs_node *expr,
                                                    int64_t value) {
  const char *name;
  int64_t mask;
  uint64_t mask_bits, value_bits, known;
  struct ixs_node_impl sym_tmp;
  ixs_bitfacts bits;
  bool equal;

  if (!extract_bitop_sym_mask(expr, IXS_AND, &name, &mask))
    return IXS_CHECK_UNKNOWN;

  /* A non-negative constant mask makes the result a finite int64 value whose
   * high bits are all zero.  Negative masks leave untracked high bits live. */
  if (mask < 0)
    return IXS_CHECK_UNKNOWN;

  mask_bits = (uint64_t)mask;
  value_bits = (uint64_t)value;
  if (value < 0 || (value_bits & ~mask_bits) != 0)
    return check_equal_result(cmp->u.binary.cmp_op, false);

  memset(&sym_tmp, 0, sizeof(sym_tmp));
  sym_tmp.tag = IXS_SYM;
  sym_tmp.hash = 0;
  sym_tmp.u.name = name;
  if (!ixs_bounds_get_bitfacts(b, &sym_tmp, &bits))
    return IXS_CHECK_UNKNOWN;

  if ((bits.known_one & mask_bits & ~value_bits) != 0 ||
      (bits.known_zero & mask_bits & value_bits) != 0)
    return check_equal_result(cmp->u.binary.cmp_op, false);

  known = (bits.known_zero | bits.known_one) & mask_bits;
  if (known != mask_bits)
    return IXS_CHECK_UNKNOWN;

  equal = (bits.known_one & mask_bits) == (value_bits & mask_bits);
  return check_equal_result(cmp->u.binary.cmp_op, equal);
}

static ixs_check_result bounds_check_bit_query(ixs_bounds *b, ixs_node *cmp) {
  ixs_node *expr;
  int64_t value;
  ixs_check_result r;

  if (cmp->u.binary.cmp_op != IXS_CMP_EQ && cmp->u.binary.cmp_op != IXS_CMP_NE)
    return IXS_CHECK_UNKNOWN;
  if (!extract_cmp_expr_const(cmp, &expr, &value))
    return IXS_CHECK_UNKNOWN;

  r = bounds_check_pow2_query(b, cmp, expr, value);
  if (r != IXS_CHECK_UNKNOWN)
    return r;

  return bounds_check_and_mask_query(b, cmp, expr, value);
}

static ixs_check_result bounds_check_zero_congruence_query(ixs_bounds *b,
                                                           ixs_node *cmp) {
  uint64_t stride;
  uint64_t residue;

  if (cmp->u.binary.cmp_op != IXS_CMP_EQ && cmp->u.binary.cmp_op != IXS_CMP_NE)
    return IXS_CHECK_UNKNOWN;
  if (!bounds_known_stride(b, cmp->u.binary.lhs, &stride) || stride <= 1u ||
      !bounds_known_residue(b, cmp->u.binary.lhs, stride, &residue) ||
      residue == 0)
    return IXS_CHECK_UNKNOWN;
  return check_equal_result(cmp->u.binary.cmp_op, false);
}

static ixs_check_result interval_check_zero(const ixs_interval *iv,
                                            ixs_cmp_op op) {
  int lo_cmp = ixs_rat_cmp(iv->lo_p, iv->lo_q, 0, 1);
  int hi_cmp = ixs_rat_cmp(iv->hi_p, iv->hi_q, 0, 1);
  switch (op) {
  case IXS_CMP_GT:
    if (lo_cmp > 0)
      return IXS_CHECK_TRUE;
    if (hi_cmp <= 0)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_GE:
    if (lo_cmp >= 0)
      return IXS_CHECK_TRUE;
    if (hi_cmp < 0)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_LT:
    if (hi_cmp < 0)
      return IXS_CHECK_TRUE;
    if (lo_cmp >= 0)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_LE:
    if (hi_cmp <= 0)
      return IXS_CHECK_TRUE;
    if (lo_cmp > 0)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_EQ:
    if (lo_cmp == 0 && hi_cmp == 0)
      return IXS_CHECK_TRUE;
    if (lo_cmp > 0 || hi_cmp < 0)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_NE:
    if (lo_cmp > 0 || hi_cmp < 0)
      return IXS_CHECK_TRUE;
    if (lo_cmp == 0 && hi_cmp == 0)
      return IXS_CHECK_FALSE;
    break;
  }
  return IXS_CHECK_UNKNOWN;
}

static bool interval_relation_input_valid(const ixs_interval *interval) {
  return interval->valid && !ixs_interval_is_empty(*interval);
}

static bool interval_upper_before_lower(const ixs_interval *lhs,
                                        const ixs_interval *rhs,
                                        bool allow_equal) {
  int comparison;

  if (lhs->hi_inf || rhs->lo_inf)
    return false;
  comparison = ixs_rat_cmp(lhs->hi_p, lhs->hi_q, rhs->lo_p, rhs->lo_q);
  return allow_equal ? comparison <= 0 : comparison < 0;
}

static bool interval_lower_after_upper(const ixs_interval *lhs,
                                       const ixs_interval *rhs,
                                       bool allow_equal) {
  int comparison;

  if (lhs->lo_inf || rhs->hi_inf)
    return false;
  comparison = ixs_rat_cmp(lhs->lo_p, lhs->lo_q, rhs->hi_p, rhs->hi_q);
  return allow_equal ? comparison >= 0 : comparison > 0;
}

static bool interval_is_singleton(const ixs_interval *interval) {
  return !interval->lo_inf && !interval->hi_inf &&
         ixs_rat_cmp(interval->lo_p, interval->lo_q, interval->hi_p,
                     interval->hi_q) == 0;
}

static bool interval_same_singleton(const ixs_interval *lhs,
                                    const ixs_interval *rhs) {
  return interval_is_singleton(lhs) && interval_is_singleton(rhs) &&
         ixs_rat_cmp(lhs->lo_p, lhs->lo_q, rhs->lo_p, rhs->lo_q) == 0;
}

static ixs_check_result interval_check_relation(const ixs_interval *lhs,
                                                const ixs_interval *rhs,
                                                ixs_cmp_op op) {
  bool lhs_before_rhs;
  bool lhs_before_or_at_rhs;
  bool lhs_after_rhs;
  bool lhs_after_or_at_rhs;
  bool same_point;

  if (!interval_relation_input_valid(lhs) ||
      !interval_relation_input_valid(rhs))
    return IXS_CHECK_UNKNOWN;

  lhs_before_rhs = interval_upper_before_lower(lhs, rhs, false);
  lhs_before_or_at_rhs = interval_upper_before_lower(lhs, rhs, true);
  lhs_after_rhs = interval_lower_after_upper(lhs, rhs, false);
  lhs_after_or_at_rhs = interval_lower_after_upper(lhs, rhs, true);
  same_point = interval_same_singleton(lhs, rhs);

  switch (op) {
  case IXS_CMP_GT:
    if (lhs_after_rhs)
      return IXS_CHECK_TRUE;
    if (lhs_before_or_at_rhs)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_GE:
    if (lhs_after_or_at_rhs)
      return IXS_CHECK_TRUE;
    if (lhs_before_rhs)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_LT:
    if (lhs_before_rhs)
      return IXS_CHECK_TRUE;
    if (lhs_after_or_at_rhs)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_LE:
    if (lhs_before_or_at_rhs)
      return IXS_CHECK_TRUE;
    if (lhs_after_rhs)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_EQ:
    if (same_point)
      return IXS_CHECK_TRUE;
    if (lhs_before_rhs || lhs_after_rhs)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_NE:
    if (lhs_before_rhs || lhs_after_rhs)
      return IXS_CHECK_TRUE;
    if (same_point)
      return IXS_CHECK_FALSE;
    break;
  }
  return IXS_CHECK_UNKNOWN;
}

static ixs_check_result bounds_check_raw(ixs_bounds *b, ixs_node *cmp) {
  ixs_interval iv;
  ixs_interval rhs_iv;
  ixs_interval truncating_remainder;
  ixs_radix_algebra_result radix_result;
  ixs_check_result interval_result;
  ixs_check_result mod_result, congruence_result, bit_result;
  ixs_algebra_status truncating_status;

  if (!cmp)
    return IXS_CHECK_UNKNOWN;

  if (ixs_bounds_has_empty(b))
    return IXS_CHECK_UNKNOWN;

  /* Smart constructors can reduce a comparison to its canonical predicate
   * constant before it reaches the query API. */
  if (cmp->tag == IXS_INT && cmp->u.ival == 1)
    return IXS_CHECK_TRUE;
  if (cmp->tag == IXS_INT && cmp->u.ival == 0)
    return IXS_CHECK_FALSE;

  if (cmp->tag != IXS_CMP)
    return IXS_CHECK_UNKNOWN;

  if (!ixs_node_is_zero(cmp->u.binary.rhs)) {
    iv = ixs_bounds_get(b, cmp->u.binary.lhs);
    rhs_iv = ixs_bounds_get(b, cmp->u.binary.rhs);
    return interval_check_relation(&iv, &rhs_iv, cmp->u.binary.cmp_op);
  }

  mod_result = bounds_check_mod_query(b, cmp);
  if (mod_result != IXS_CHECK_UNKNOWN)
    return mod_result;

  radix_result =
      ixs_radix_algebra_order(b, cmp->u.binary.lhs, cmp->u.binary.cmp_op);
  if (radix_result.oom)
    b->oom = true;
  if (radix_result.check != IXS_CHECK_UNKNOWN)
    return radix_result.check;

  congruence_result = bounds_check_zero_congruence_query(b, cmp);
  if (congruence_result != IXS_CHECK_UNKNOWN)
    return congruence_result;

  bit_result = bounds_check_bit_query(b, cmp);
  if (bit_result != IXS_CHECK_UNKNOWN)
    return bit_result;

  iv = ixs_bounds_get(b, cmp->u.binary.lhs);
  truncating_status = bounds_get_truncating_remainder_range(
      b, cmp->u.binary.lhs, /*expression_defined=*/true, &truncating_remainder);
  if (truncating_status == IXS_ALGEBRA_MATCH)
    iv = iv_intersect(iv, truncating_remainder);
  else
    bounds_note_truncating_range_status(b, truncating_status);
  if (iv.valid) {
    interval_result = interval_check_zero(&iv, cmp->u.binary.cmp_op);
    if (interval_result != IXS_CHECK_UNKNOWN)
      return interval_result;
  }
  if (cmp->u.binary.cmp_op == IXS_CMP_GE && cmp->u.binary.lhs->tag == IXS_ADD) {
    radix_result = ixs_radix_algebra_nonnegative(b, cmp->u.binary.lhs);
    if (radix_result.oom)
      b->oom = true;
    if (radix_result.check != IXS_CHECK_UNKNOWN)
      return radix_result.check;
  }
  return IXS_CHECK_UNKNOWN;
}

IXS_STATIC ixs_check_result ixs_bounds_check(ixs_bounds *b, ixs_node *cmp) {
  ixs_check_result result;
  bool query_held = false;
  if (!ixs_bounds_query_hold_begin(b, cmp, &query_held))
    return IXS_CHECK_UNKNOWN;
  if (cmp && cmp->tag == IXS_CMP &&
      ((!ixs_node_is_known_total(cmp->u.binary.lhs) &&
        ixs_bounds_check_defined(b, cmp->u.binary.lhs) != IXS_CHECK_TRUE) ||
       (!ixs_node_is_known_total(cmp->u.binary.rhs) &&
        ixs_bounds_check_defined(b, cmp->u.binary.rhs) != IXS_CHECK_TRUE))) {
    if (query_held)
      ixs_bounds_query_hold_end(b);
    return IXS_CHECK_UNKNOWN;
  }
  result = bounds_check_raw(b, cmp);
  if (query_held)
    ixs_bounds_query_hold_end(b);
  return result;
}

/* Definedness is a proof query, not an evaluator.  All expression traversal
 * uses growable work stacks.  The branch-sensitive Piecewise pass invokes a
 * structural-only subquery for its conditions and values, so C recursion is
 * statically bounded while nested Piecewise DAGs remain unbounded in size. */
#define DEFINED_BOUNDS_CACHE_MIN_CAP 32u
#define DEFINED_BOUNDS_CACHE_CAP 8192u

typedef struct {
  ixs_ctx *ctx;
  ixs_arena *arena;
  ixs_arena_mark arena_mark;
  ixs_node **active_piecewise;
  size_t active_piecewise_count;
  size_t active_piecewise_capacity;
  size_t visited;
  bool oom;
  bool limited;
  bool invalid;
} defined_state;

typedef struct {
  ixs_node *node;
  ixs_check_result result;
  bool active;
  bool complete;
} bounds_check_memo_entry;

typedef struct {
  ixs_node *node;
  ixs_node *selected_condition;
  ixs_node *selected_value;
  uint32_t next_child;
  uint32_t nchildren;
  ixs_check_result result;
  bool started;
  bool selected_piecewise_case;
} defined_frame;

typedef struct {
  defined_state *state;
  ixs_bounds *bounds;
  ixs_query_walk walk;
  ixs_query_node_memo memo;
  ixs_check_result answer;
  unsigned pw_depth;
} defined_query;

typedef struct {
  ixs_node *node;
  uint32_t next_child;
  uint32_t nchildren;
} defined_depth_frame;

typedef struct {
  defined_state *state;
  ixs_query_walk walk;
  ixs_query_node_memo memo;
  bool *shared;
  size_t visited;
} defined_depth_query;

typedef struct {
  ixs_arena_mark mark;
  ixs_ctx *old_ctx;
  ixs_bounds_cache_entry *old_cache;
  size_t old_cache_cap;
  bool active;
} defined_cache_scope;

static void defined_state_init(defined_state *state, ixs_ctx *ctx,
                               ixs_bounds *bounds) {
  memset(state, 0, sizeof(*state));
  state->ctx = ctx;
  state->arena = &bounds->query_arena;
  state->arena_mark = ixs_arena_save(state->arena);
}

static void defined_state_destroy(defined_state *state) {
  ixs_arena_restore(state->arena, state->arena_mark);
}

static bool defined_piecewise_enter(defined_state *state, ixs_node *expr) {
  size_t i;
  for (i = 0; i < state->active_piecewise_count; i++) {
    if (state->active_piecewise[i] == expr) {
      state->invalid = true;
      return false;
    }
  }
  if (state->active_piecewise_count == state->active_piecewise_capacity) {
    size_t next_capacity = state->active_piecewise_capacity
                               ? state->active_piecewise_capacity * 2u
                               : 8u;
    ixs_node **grown;
    if (next_capacity <= state->active_piecewise_capacity ||
        next_capacity > SIZE_MAX / sizeof(*grown)) {
      state->oom = true;
      return false;
    }
    grown = ixs_arena_grow(state->arena, state->active_piecewise,
                           state->active_piecewise_capacity * sizeof(*grown),
                           next_capacity * sizeof(*grown), sizeof(void *));
    if (!grown) {
      state->oom = true;
      return false;
    }
    state->active_piecewise = grown;
    state->active_piecewise_capacity = next_capacity;
  }
  state->active_piecewise[state->active_piecewise_count++] = expr;
  return true;
}

static void defined_piecewise_leave(defined_state *state) {
  assert(state->active_piecewise_count != 0);
  state->active_piecewise_count--;
}

static ixs_check_result defined_combine(ixs_check_result lhs,
                                        ixs_check_result rhs) {
  if (lhs == IXS_CHECK_FALSE || rhs == IXS_CHECK_FALSE)
    return IXS_CHECK_FALSE;
  if (lhs == IXS_CHECK_UNKNOWN || rhs == IXS_CHECK_UNKNOWN)
    return IXS_CHECK_UNKNOWN;
  return IXS_CHECK_TRUE;
}

static bool defined_cmp_op_valid(ixs_cmp_op op) {
  switch (op) {
  case IXS_CMP_GT:
  case IXS_CMP_GE:
  case IXS_CMP_LT:
  case IXS_CMP_LE:
  case IXS_CMP_EQ:
  case IXS_CMP_NE:
    return true;
  }
  return false;
}

static ixs_cmp_op defined_negate_cmp_op(ixs_cmp_op op) {
  switch (op) {
  case IXS_CMP_GT:
    return IXS_CMP_LE;
  case IXS_CMP_GE:
    return IXS_CMP_LT;
  case IXS_CMP_LT:
    return IXS_CMP_GE;
  case IXS_CMP_LE:
    return IXS_CMP_GT;
  case IXS_CMP_EQ:
    return IXS_CMP_NE;
  case IXS_CMP_NE:
    return IXS_CMP_EQ;
  }
  return op;
}

static int defined_fixed_child_count(ixs_tag tag) {
  switch (tag) {
  case IXS_INT:
  case IXS_RAT:
  case IXS_SYM:
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    return 0;
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
  case IXS_NOT:
    return 1;
  case IXS_MOD:
  case IXS_CMP:
    return 2;
  default:
    return -1;
  }
}

/* Keep this local walker independent of the public assert-based accessors.
 * It also gives malformed internal nodes the required conservative result. */
static bool defined_child_count(ixs_node *node, uint32_t *out) {
  int fixed;
  if (!node || !out)
    return false;
  fixed = defined_fixed_child_count(node->tag);
  if (fixed >= 0) {
    *out = (uint32_t)fixed;
    return true;
  }
  switch (node->tag) {
  case IXS_ADD:
    if (!node->u.add.coeff || (node->u.add.nterms > 0 && !node->u.add.terms) ||
        node->u.add.nterms > (UINT32_MAX - 1u) / 2u)
      return false;
    *out = 1u + 2u * node->u.add.nterms;
    return true;
  case IXS_MUL:
    if (!node->u.mul.coeff ||
        (node->u.mul.nfactors > 0 && !node->u.mul.factors) ||
        node->u.mul.nfactors == UINT32_MAX)
      return false;
    *out = 1u + node->u.mul.nfactors;
    return true;
  case IXS_PIECEWISE:
    if ((node->u.pw.ncases > 0 && !node->u.pw.cases) ||
        node->u.pw.ncases > UINT32_MAX / 2u)
      return false;
    *out = 2u * node->u.pw.ncases;
    return true;
  case IXS_AND:
  case IXS_OR:
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
    if (node->u.assoc.nargs < 2 || !node->u.assoc.args)
      return false;
    *out = node->u.assoc.nargs;
    return true;
  default:
    return false;
  }
}

static ixs_node *defined_child_at(ixs_node *node, uint32_t child) {
  switch (node->tag) {
  case IXS_ADD:
    if (child == 0)
      return node->u.add.coeff;
    child--;
    return (child & 1u) == 0u ? node->u.add.terms[child / 2u].coeff
                              : node->u.add.terms[child / 2u].term;
  case IXS_MUL:
    return child == 0 ? node->u.mul.coeff
                      : node->u.mul.factors[child - 1u].base;
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
    return node->u.unary.arg;
  case IXS_NOT:
    return node->u.unary_bool.arg;
  case IXS_MOD:
  case IXS_CMP:
    return child == 0 ? node->u.binary.lhs : node->u.binary.rhs;
  case IXS_PIECEWISE:
    return (child & 1u) == 0u ? node->u.pw.cases[child / 2u].value
                              : node->u.pw.cases[child / 2u].cond;
  case IXS_AND:
  case IXS_OR:
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
    return node->u.assoc.args[child];
  default:
    return NULL;
  }
}

static ixs_query_walk_step defined_depth_push(defined_depth_query *query,
                                              ixs_node *node,
                                              uint32_t nchildren) {
  bounds_check_memo_entry *entry =
      ixs_query_node_memo_get(&query->memo, node, true);
  defined_depth_frame *frame;
  ixs_query_walk_step step;
  if (!entry) {
    query->state->oom = true;
    return IXS_QUERY_WALK_OOM;
  }
  if (entry->active) {
    query->state->invalid = true;
    return IXS_QUERY_WALK_STOP;
  }
  if (entry->complete) {
    if (query->shared)
      *query->shared = true;
    return IXS_QUERY_WALK_ADVANCED;
  }
  step = ixs_query_walk_push(&query->walk, node);
  if (step != IXS_QUERY_WALK_ADVANCED)
    return step;
  frame = IXS_QUERY_WALK_TOP(&query->walk);
  frame->nchildren = nchildren;
  entry->active = true;
  query->visited++;
  return step;
}

/* hot */
static ixs_query_walk_step defined_depth_advance(void *state, void *top) {
  defined_depth_query *query = state;
  defined_depth_frame *frame = top;
  bounds_check_memo_entry *entry;
  ixs_node *child;
  uint32_t nchildren;
  if (frame->next_child < frame->nchildren) {
    child = defined_child_at(frame->node, frame->next_child++);
    if (!child || !defined_child_count(child, &nchildren)) {
      query->state->invalid = true;
      return IXS_QUERY_WALK_STOP;
    }
    return defined_depth_push(query, child, nchildren);
  }
  entry = ixs_query_node_memo_get(&query->memo, frame->node, false);
  if (!entry || !entry->active) {
    query->state->invalid = true;
    return IXS_QUERY_WALK_STOP;
  }
  entry->active = false;
  entry->complete = true;
  IXS_QUERY_WALK_POP(&query->walk);
  return IXS_QUERY_WALK_ADVANCED;
}

static bool defined_bounds_depth_safe(defined_state *state, ixs_bounds *b,
                                      ixs_node *root, bool *shared,
                                      size_t *node_visits) {
  ixs_arena_mark mark;
  defined_depth_query query;
  ixs_query_walk_step step;
  uint32_t nchildren;

  if (shared)
    *shared = false;
  if (node_visits)
    *node_visits = 0;
  if (!root || !defined_child_count(root, &nchildren)) {
    state->invalid = true;
    return false;
  }
  mark = ixs_arena_save(b->scratch);
  query.state = state;
  query.shared = shared;
  query.visited = 0;
  IXS_QUERY_NODE_MEMO_INIT(&query.memo, b->scratch, bounds_check_memo_entry,
                           node);
  IXS_QUERY_WALK_INIT_CAP(&query.walk, b->scratch, &state->oom,
                          defined_depth_frame, node, 32u);
  step = defined_depth_push(&query, root, nchildren);
  if (step == IXS_QUERY_WALK_ADVANCED)
    step =
        ixs_query_walk_drive(&query.walk, &query, defined_depth_advance, NULL);
  if (step == IXS_QUERY_WALK_ADVANCED && node_visits)
    *node_visits = query.visited;
  ixs_arena_restore(b->scratch, mark);
  return step == IXS_QUERY_WALK_ADVANCED;
}

static size_t defined_bounds_cache_capacity(size_t node_visits) {
  size_t cap = DEFINED_BOUNDS_CACHE_MIN_CAP;
  while (cap < DEFINED_BOUNDS_CACHE_CAP && node_visits > cap / 2u)
    cap *= 2u;
  return cap;
}

static bool defined_cache_scope_init(defined_cache_scope *scope,
                                     defined_state *state, ixs_bounds *b,
                                     size_t node_visits) {
  ixs_bounds_cache_entry *cache;
  size_t cache_cap = defined_bounds_cache_capacity(node_visits);
  scope->mark = ixs_arena_save(b->scratch);
  scope->old_cache = b->cache;
  scope->old_cache_cap = b->cache_cap;
  scope->active = false;
  cache =
      ixs_arena_alloc(b->scratch, cache_cap * sizeof(*cache), sizeof(void *));
  if (!cache) {
    state->oom = true;
    ixs_arena_restore(b->scratch, scope->mark);
    return false;
  }
  memset(cache, 0, cache_cap * sizeof(*cache));
  b->cache = cache;
  b->cache_cap = cache_cap;
  /* Direct overrides are enough for a proof query. Canonical aliases expand
   * recursively and can revisit a shared DAG before the interval cache sees
   * it, so disable that optional path inside this bounded scope. */
  scope->old_ctx = bounds_store_swap_active_context(b, NULL);
  scope->active = true;
  return true;
}

static void defined_cache_scope_destroy(defined_cache_scope *scope,
                                        ixs_bounds *b) {
  if (!scope->active)
    return;
  (void)bounds_store_swap_active_context(b, scope->old_ctx);
  b->cache = scope->old_cache;
  b->cache_cap = scope->old_cache_cap;
  ixs_arena_restore(b->scratch, scope->mark);
  scope->active = false;
}

static ixs_check_result defined_relation_zero(defined_state *state,
                                              ixs_bounds *b, ixs_node *expr,
                                              ixs_cmp_op op) {
  ixs_interval iv;
  ixs_check_result result;
  ixs_bitfacts bits;
  int64_t modulus, remainder;
  defined_cache_scope cache_scope;
  size_t node_visits;
  bool shared;

  if ((op == IXS_CMP_EQ || op == IXS_CMP_NE) &&
      bounds_store_contains_nonzero(b, expr))
    return op == IXS_CMP_NE ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
  if (!defined_bounds_depth_safe(state, b, expr, &shared, &node_visits) ||
      !defined_cache_scope_init(&cache_scope, state, b, node_visits))
    return IXS_CHECK_UNKNOWN;
  iv = ixs_bounds_get(b, expr);
  if (b->oom) {
    state->oom = true;
    result = IXS_CHECK_UNKNOWN;
    goto cleanup;
  }
  if (iv.valid) {
    result = interval_check_zero(&iv, op);
    if (result != IXS_CHECK_UNKNOWN)
      goto cleanup;
  }

  result = IXS_CHECK_UNKNOWN;
  if (op != IXS_CMP_EQ && op != IXS_CMP_NE)
    goto cleanup;
  if (!shared && ixs_bounds_get_bitfacts(b, expr, &bits) &&
      bits.known_one != 0) {
    result = op == IXS_CMP_NE ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
    goto cleanup;
  }
  if (b->oom) {
    state->oom = true;
    goto cleanup;
  }
  if (expr->tag == IXS_SYM &&
      bounds_store_get_modrem(b, expr->u.name, &modulus, &remainder) &&
      remainder != 0) {
    (void)modulus;
    result = op == IXS_CMP_NE ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
  }

cleanup:
  defined_cache_scope_destroy(&cache_scope, b);
  return result;
}

static ixs_check_result defined_condition_truth(defined_state *state,
                                                ixs_bounds *b, ixs_node *cond) {
  ixs_check_result result;
  defined_cache_scope cache_scope;
  size_t node_visits;
  bool shared;
  if (ixs_node_is_known_false(cond))
    return IXS_CHECK_FALSE;
  if (ixs_node_is_known_true(cond))
    return IXS_CHECK_TRUE;
  if (cond->tag == IXS_CMP) {
    if (ixs_node_is_zero(cond->u.binary.rhs)) {
      result = defined_relation_zero(state, b, cond->u.binary.lhs,
                                     cond->u.binary.cmp_op);
      if (result != IXS_CHECK_UNKNOWN || state->oom)
        return result;
    }
    if (!defined_bounds_depth_safe(state, b, cond, &shared, &node_visits))
      return IXS_CHECK_UNKNOWN;
    if (shared) {
      if (!ixs_node_is_zero(cond->u.binary.rhs))
        return IXS_CHECK_UNKNOWN;
      return defined_relation_zero(state, b, cond->u.binary.lhs,
                                   cond->u.binary.cmp_op);
    }
    if (!defined_cache_scope_init(&cache_scope, state, b, node_visits))
      return IXS_CHECK_UNKNOWN;
    result = bounds_check_raw(b, cond);
    if (b->oom)
      state->oom = true;
    defined_cache_scope_destroy(&cache_scope, b);
    return result;
  }
  return defined_relation_zero(state, b, cond, IXS_CMP_NE);
}

static ixs_node *defined_condition_assumption(defined_state *state,
                                              ixs_node *cond, bool value,
                                              struct ixs_node_impl *storage) {
  memset(storage, 0, sizeof(*storage));
  storage->tag = IXS_CMP;
  storage->u.binary.rhs = state->ctx->node_zero;
  if (cond->tag == IXS_CMP) {
    storage->u.binary.lhs = cond->u.binary.lhs;
    storage->u.binary.rhs = cond->u.binary.rhs;
    storage->u.binary.cmp_op =
        value ? cond->u.binary.cmp_op
              : defined_negate_cmp_op(cond->u.binary.cmp_op);
  } else {
    storage->u.binary.lhs = cond;
    storage->u.binary.cmp_op = value ? IXS_CMP_NE : IXS_CMP_EQ;
  }
  return storage;
}

static ixs_check_result defined_eval(defined_state *state, ixs_bounds *b,
                                     ixs_node *root, unsigned pw_depth);

static bool defined_match_shared_rounding_piecewise(ixs_node *expr,
                                                    ixs_node **condition,
                                                    ixs_node **argument) {
  ixs_node *floor_value;
  ixs_node *ceil_value;

  if (!expr || expr->tag != IXS_PIECEWISE || expr->u.pw.ncases != 2u ||
      !expr->u.pw.cases || !ixs_node_is_known_true(expr->u.pw.cases[1].cond))
    return false;
  floor_value = expr->u.pw.cases[0].value;
  ceil_value = expr->u.pw.cases[1].value;
  if (!floor_value || !ceil_value || floor_value->tag != IXS_FLOOR ||
      ceil_value->tag != IXS_CEIL ||
      floor_value->u.unary.arg != ceil_value->u.unary.arg)
    return false;
  *condition = expr->u.pw.cases[0].cond;
  *argument = floor_value->u.unary.arg;
  return *condition && *argument;
}

static void defined_partition_add(unsigned *partitions,
                                  ixs_check_result result) {
  if (result == IXS_CHECK_TRUE)
    *partitions |= 1u;
  else if (result == IXS_CHECK_FALSE)
    *partitions |= 2u;
  else
    *partitions |= 4u;
}

static ixs_check_result defined_partition_result(unsigned partitions) {
  if (partitions == 1u)
    return IXS_CHECK_TRUE;
  if (partitions == 2u)
    return IXS_CHECK_FALSE;
  return IXS_CHECK_UNKNOWN;
}

typedef enum {
  DEFINED_PW_NEXT,
  DEFINED_PW_STOP,
  DEFINED_PW_FAILED
} defined_pw_step;

static bool defined_piecewise_active(defined_state *state,
                                     ixs_bounds *remaining, ixs_node *cond,
                                     ixs_node *value, unsigned pw_depth,
                                     unsigned *partitions) {
  ixs_arena_mark mark = ixs_arena_save(remaining->scratch);
  ixs_bounds active;
  struct ixs_node_impl assumption;
  bool active_ready = false;
  bool ok = false;
  if (!ixs_bounds_fork(&active, remaining)) {
    state->oom = true;
    goto cleanup;
  }
  active_ready = true;
  if (!ixs_bounds_add_assumption(
          &active,
          defined_condition_assumption(state, cond, true, &assumption))) {
    state->oom = true;
    goto cleanup;
  }
  if (!ixs_bounds_has_empty(&active)) {
    ixs_check_result result = defined_eval(state, &active, value, pw_depth);
    defined_partition_add(partitions, result);
  }
  ok = !state->oom && !state->limited;

cleanup:
  if (active_ready)
    ixs_bounds_destroy(&active);
  ixs_arena_restore(remaining->scratch, mark);
  return ok;
}

static defined_pw_step defined_piecewise_case(defined_state *state,
                                              ixs_bounds *remaining,
                                              const ixs_pwcase *pwcase,
                                              unsigned pw_depth,
                                              unsigned *partitions) {
  ixs_node *cond = pwcase->cond;
  ixs_check_result cond_defined =
      defined_eval(state, remaining, cond, pw_depth);
  ixs_check_result truth;
  struct ixs_node_impl assumption;

  if (state->oom || state->limited)
    return DEFINED_PW_FAILED;
  if (cond_defined != IXS_CHECK_TRUE) {
    defined_partition_add(partitions, cond_defined);
    return DEFINED_PW_STOP;
  }

  truth = defined_condition_truth(state, remaining, cond);
  if (state->oom)
    return DEFINED_PW_FAILED;
  if (truth == IXS_CHECK_FALSE)
    return DEFINED_PW_NEXT;
  if (!defined_bounds_depth_safe(state, remaining, cond, NULL, NULL)) {
    defined_partition_add(partitions, IXS_CHECK_UNKNOWN);
    return DEFINED_PW_STOP;
  }
  if (!defined_piecewise_active(state, remaining, cond, pwcase->value, pw_depth,
                                partitions))
    return DEFINED_PW_FAILED;
  if (truth == IXS_CHECK_TRUE)
    return DEFINED_PW_STOP;

  if (!ixs_bounds_add_assumption(
          remaining,
          defined_condition_assumption(state, cond, false, &assumption))) {
    state->oom = true;
    return DEFINED_PW_FAILED;
  }
  return DEFINED_PW_NEXT;
}

static bool defined_piecewise_shared_result(defined_state *state, ixs_bounds *b,
                                            ixs_node *expr, unsigned pw_depth,
                                            ixs_check_result *result) {
  ixs_node *condition;
  ixs_node *argument;
  ixs_check_result condition_defined;
  ixs_check_result argument_defined;

  if (!defined_match_shared_rounding_piecewise(expr, &condition, &argument))
    return false;
  condition_defined = defined_eval(state, b, condition, pw_depth);
  if (state->oom || state->limited) {
    *result = IXS_CHECK_UNKNOWN;
    return true;
  }
  argument_defined = defined_eval(state, b, argument, pw_depth);
  if (state->oom || state->limited) {
    *result = IXS_CHECK_UNKNOWN;
    return true;
  }
  *result = defined_combine(condition_defined, argument_defined);
  return *result != IXS_CHECK_UNKNOWN;
}

static ixs_check_result defined_piecewise_partitions(defined_state *state,
                                                     ixs_bounds *b,
                                                     ixs_node *expr,
                                                     unsigned pw_depth) {
  ixs_arena_mark outer_mark;
  ixs_bounds remaining;
  unsigned partitions = 0;
  uint32_t i;
  bool stopped = false;
  bool remaining_ready = false;

  outer_mark = ixs_arena_save(b->scratch);
  if (!ixs_bounds_fork(&remaining, b)) {
    state->oom = true;
    ixs_arena_restore(b->scratch, outer_mark);
    return IXS_CHECK_UNKNOWN;
  }
  remaining_ready = true;

  for (i = 0; i < expr->u.pw.ncases; i++) {
    defined_pw_step step;

    if (remaining.oom) {
      state->oom = true;
      break;
    }
    if (ixs_bounds_has_empty(&remaining)) {
      stopped = true;
      break;
    }
    step = defined_piecewise_case(state, &remaining, &expr->u.pw.cases[i],
                                  pw_depth, &partitions);
    if (step == DEFINED_PW_STOP) {
      stopped = true;
      break;
    }
    if (step == DEFINED_PW_FAILED)
      break;
  }

  if (!state->oom && !state->limited && !stopped && !remaining.oom &&
      !ixs_bounds_has_empty(&remaining))
    defined_partition_add(&partitions, IXS_CHECK_FALSE);
  if (remaining.oom)
    state->oom = true;

  if (remaining_ready)
    ixs_bounds_destroy(&remaining);
  ixs_arena_restore(b->scratch, outer_mark);
  if (state->oom || state->limited)
    return IXS_CHECK_UNKNOWN;
  return defined_partition_result(partitions);
}

static ixs_check_result defined_piecewise(defined_state *state, ixs_bounds *b,
                                          ixs_node *expr, unsigned pw_depth) {
  ixs_check_result shared;
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  if (!defined_piecewise_enter(state, expr))
    return IXS_CHECK_UNKNOWN;
  if (defined_piecewise_shared_result(state, b, expr, pw_depth, &shared)) {
    result = shared;
    goto cleanup;
  }
  if ((expr->u.pw.ncases > 0 && !expr->u.pw.cases) ||
      expr->u.pw.ncases > UINT32_MAX / 2u) {
    state->invalid = true;
    goto cleanup;
  }
  result = expr->u.pw.ncases == 0
               ? IXS_CHECK_FALSE
               : defined_piecewise_partitions(state, b, expr, pw_depth);

cleanup:
  defined_piecewise_leave(state);
  return result;
}

static ixs_check_result defined_finalize_node(defined_state *state,
                                              ixs_bounds *b, ixs_node *node,
                                              ixs_check_result result) {
  uint32_t i;
  if (node->tag == IXS_MUL) {
    for (i = 0; i < node->u.mul.nfactors; i++) {
      ixs_check_result guard;
      if (node->u.mul.factors[i].exp == 0)
        result = defined_combine(result, IXS_CHECK_UNKNOWN);
      if (node->u.mul.factors[i].exp >= 0)
        continue;
      guard = defined_relation_zero(state, b, node->u.mul.factors[i].base,
                                    IXS_CMP_NE);
      result = defined_combine(result, guard);
    }
  } else if (node->tag == IXS_MOD) {
    ixs_check_result guard =
        defined_relation_zero(state, b, node->u.binary.rhs, IXS_CMP_GT);
    result = defined_combine(result, guard);
  } else if (node->tag == IXS_XOR || node->tag == IXS_AND ||
             node->tag == IXS_OR) {
    for (i = 0; i < node->u.assoc.nargs; i++) {
      ixs_check_result guard =
          ixs_bounds_check_integer_valued(b, node->u.assoc.args[i]);
      result = defined_combine(result, guard);
    }
  }
  return result;
}

static ixs_query_walk_step defined_complete_frame(defined_query *query,
                                                  ixs_check_result result) {
  defined_frame *frame = IXS_QUERY_WALK_TOP(&query->walk);
  bounds_check_memo_entry *entry =
      ixs_query_node_memo_get(&query->memo, frame->node, false);
  if (!entry) {
    query->state->invalid = true;
    result = IXS_CHECK_UNKNOWN;
  } else {
    entry->result = result;
    entry->active = false;
    entry->complete = true;
  }
  IXS_QUERY_WALK_POP(&query->walk);
  if (query->walk.depth == 0) {
    query->answer = result;
    return IXS_QUERY_WALK_ADVANCED;
  }
  frame = IXS_QUERY_WALK_TOP(&query->walk);
  frame->result = defined_combine(frame->result, result);
  frame->next_child++;
  return IXS_QUERY_WALK_ADVANCED;
}

static void defined_start_nested_piecewise(defined_state *state,
                                           defined_frame *frame,
                                           ixs_check_result *direct,
                                           bool *has_direct) {
  ixs_node *node = frame->node;
  uint32_t i;
  if ((node->u.pw.ncases > 0 && !node->u.pw.cases) ||
      node->u.pw.ncases > UINT32_MAX / 2u) {
    state->invalid = true;
    *has_direct = true;
    return;
  }
  for (i = 0; i < node->u.pw.ncases; i++) {
    ixs_node *cond = node->u.pw.cases[i].cond;
    if (!cond || !node->u.pw.cases[i].value) {
      state->invalid = true;
      *has_direct = true;
      return;
    }
    if (ixs_node_is_known_false(cond))
      continue;
    if (!ixs_node_is_known_true(cond)) {
      *has_direct = true;
      return;
    }
    frame->selected_condition = cond;
    frame->selected_value = node->u.pw.cases[i].value;
    frame->selected_piecewise_case = true;
    frame->nchildren = 2u;
    return;
  }
  *direct = IXS_CHECK_FALSE;
  *has_direct = true;
}

static void defined_start_frame(defined_state *state, ixs_bounds *b,
                                defined_frame *frame, unsigned pw_depth,
                                ixs_check_result *direct, bool *has_direct) {
  ixs_node *node = frame->node;
  *direct = IXS_CHECK_UNKNOWN;
  *has_direct = false;

  if (!node || !ixs_ctx_owns_node(state->ctx, node) ||
      ixs_node_is_sentinel(node)) {
    state->invalid = true;
    *has_direct = true;
    return;
  }
  if (ixs_node_is_known_total(node)) {
    *direct = IXS_CHECK_TRUE;
    *has_direct = true;
    return;
  }
  if (state->visited != SIZE_MAX)
    state->visited++;

  /* A range constrains a node only where that node is defined. It cannot skip
   * the structural walk or discharge an operation's domain guards. */

  switch (node->tag) {
  case IXS_INT:
    *direct = IXS_CHECK_TRUE;
    *has_direct = true;
    return;
  case IXS_RAT:
    *direct = node->u.rat.q > 0 ? IXS_CHECK_TRUE : IXS_CHECK_UNKNOWN;
    *has_direct = true;
    return;
  case IXS_SYM:
    *direct = node->u.name ? IXS_CHECK_TRUE : IXS_CHECK_UNKNOWN;
    *has_direct = true;
    return;
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    *has_direct = true;
    return;
  case IXS_PIECEWISE:
    if (pw_depth == 0u) {
      *direct = defined_piecewise(state, b, node, 1u);
      *has_direct = true;
      return;
    }
    /* Nested Piecewise nodes are handled on this work stack when their first
     * reachable case is statically selected.  Unknown selection is a sound
     * UNKNOWN: branch-sensitive environment reasoning is performed only by
     * the statically bounded outer Piecewise pass. */
    defined_start_nested_piecewise(state, frame, direct, has_direct);
    return;
  case IXS_CMP:
    if (!defined_cmp_op_valid(node->u.binary.cmp_op)) {
      state->invalid = true;
      *has_direct = true;
      return;
    }
    break;
  default:
    break;
  }
  if (!defined_child_count(node, &frame->nchildren)) {
    state->invalid = true;
    *has_direct = true;
  }
}

static ixs_query_walk_step defined_process_child(defined_query *query,
                                                 defined_frame *frame) {
  defined_state *state = query->state;
  ixs_node *child;
  bounds_check_memo_entry *entry;
  if (frame->next_child >= frame->nchildren)
    return IXS_QUERY_WALK_NEXT;

  if (frame->selected_piecewise_case)
    child = frame->next_child == 0u ? frame->selected_condition
                                    : frame->selected_value;
  else
    child = defined_child_at(frame->node, frame->next_child);
  if (!child) {
    state->invalid = true;
    frame->result = defined_combine(frame->result, IXS_CHECK_UNKNOWN);
    frame->next_child++;
    return IXS_QUERY_WALK_ADVANCED;
  }
  entry = ixs_query_node_memo_get(&query->memo, child, false);
  if (entry && entry->complete) {
    frame->result = defined_combine(frame->result, entry->result);
    frame->next_child++;
    return IXS_QUERY_WALK_ADVANCED;
  }
  if (entry && entry->active) {
    state->invalid = true;
    return IXS_QUERY_WALK_STOP;
  }
  if (!entry)
    entry = ixs_query_node_memo_get(&query->memo, child, true);
  if (!entry) {
    state->oom = true;
    return IXS_QUERY_WALK_OOM;
  }
  if (ixs_query_walk_push(&query->walk, child) != IXS_QUERY_WALK_ADVANCED)
    return IXS_QUERY_WALK_OOM;
  ((defined_frame *)IXS_QUERY_WALK_TOP(&query->walk))->result = IXS_CHECK_TRUE;
  entry->active = true;
  return IXS_QUERY_WALK_ADVANCED;
}

/* hot */
static ixs_query_walk_step defined_advance(void *state, void *top) {
  defined_query *query = state;
  defined_frame *frame = top;
  ixs_query_walk_step step;
  if (query->state->oom || query->state->limited || query->state->invalid)
    return IXS_QUERY_WALK_STOP;
  if (!frame->started) {
    ixs_check_result direct = IXS_CHECK_UNKNOWN;
    bool has_direct = false;
    defined_start_frame(query->state, query->bounds, frame, query->pw_depth,
                        &direct, &has_direct);
    if (query->state->limited)
      return IXS_QUERY_WALK_STOP;
    if (has_direct)
      return defined_complete_frame(query, direct);
    frame->started = true;
  }
  step = defined_process_child(query, frame);
  if (step != IXS_QUERY_WALK_NEXT)
    return step;
  frame->result = defined_finalize_node(query->state, query->bounds,
                                        frame->node, frame->result);
  return defined_complete_frame(query, frame->result);
}

static ixs_check_result defined_eval(defined_state *state, ixs_bounds *b,
                                     ixs_node *root, unsigned pw_depth) {
  ixs_arena_mark mark;
  defined_query query;
  bounds_check_memo_entry *root_entry;
  ixs_query_walk_step step;

  if (!root || state->oom || state->limited || state->invalid)
    return IXS_CHECK_UNKNOWN;
  mark = ixs_arena_save(b->scratch);
  query.state = state;
  query.bounds = b;
  query.answer = IXS_CHECK_UNKNOWN;
  query.pw_depth = pw_depth;
  IXS_QUERY_NODE_MEMO_INIT(&query.memo, b->scratch, bounds_check_memo_entry,
                           node);
  IXS_QUERY_WALK_INIT_CAP(&query.walk, b->scratch, &state->oom, defined_frame,
                          node, 32u);
  root_entry = ixs_query_node_memo_get(&query.memo, root, true);
  if (!root_entry) {
    state->oom = true;
    ixs_arena_restore(b->scratch, mark);
    return IXS_CHECK_UNKNOWN;
  }
  step = ixs_query_walk_push(&query.walk, root);
  if (step != IXS_QUERY_WALK_ADVANCED) {
    ixs_arena_restore(b->scratch, mark);
    return IXS_CHECK_UNKNOWN;
  }
  ((defined_frame *)IXS_QUERY_WALK_TOP(&query.walk))->result = IXS_CHECK_TRUE;
  root_entry->active = true;
  step = ixs_query_walk_drive(&query.walk, &query, defined_advance, NULL);
  ixs_arena_restore(b->scratch, mark);
  if (step != IXS_QUERY_WALK_ADVANCED || state->oom || state->limited ||
      state->invalid)
    return IXS_CHECK_UNKNOWN;
  return query.answer;
}

static bool bounds_defined_cache_lookup(ixs_bounds *b, ixs_node *expr,
                                        ixs_check_result *result) {
  size_t endpoint_index;
  bool without_equality;
  if (!bounds_query_is_tracking(b) || !b->query_state ||
      !ixs_relation_algebra_find_endpoint(&b->relations, expr, &endpoint_index))
    return false;
  without_equality = b->equality_disabled_depth != 0;
  return bounds_relation_projection_lookup_defined(b, endpoint_index,
                                                   without_equality, result);
}

static bool bounds_defined_cache_publish(ixs_bounds *b, ixs_node *expr,
                                         ixs_check_result result) {
  size_t endpoint_index;
  if (!bounds_query_is_tracking(b) || !b->query_state ||
      !ixs_relation_algebra_find_endpoint(&b->relations, expr, &endpoint_index))
    return true;
  if (!bounds_relation_projection_complete_defined(
          b, endpoint_index, b->equality_disabled_depth != 0, result)) {
    b->oom = true;
    return false;
  }
  return true;
}

typedef struct {
  ixs_bounds_transport_snapshot transport;
  size_t cycle_blocks;
  bool tracking;
} bounds_defined_query_snapshot;

static bounds_defined_query_snapshot
bounds_defined_query_observe(ixs_bounds *b) {
  bounds_defined_query_snapshot snapshot;
  snapshot.transport = ixs_bounds_query_transport_snapshot(b);
  snapshot.cycle_blocks = bounds_query_cycle_count(b);
  snapshot.tracking = bounds_query_is_tracking(b);
  return snapshot;
}

static bool bounds_defined_query_failed(ixs_bounds *b, defined_state *state,
                                        ixs_check_result result,
                                        bounds_defined_query_snapshot snapshot,
                                        bool *oom, bool *limited) {
  bool query_limited;
  bool query_cycle;
  bool query_invalid;
  if (state->limited && snapshot.tracking)
    bounds_query_note_limit(b);
  if (state->invalid && snapshot.tracking)
    bounds_query_note_invalid(b);
  query_limited = snapshot.tracking && result == IXS_CHECK_UNKNOWN &&
                  bounds_query_limited_since(b, snapshot.transport);
  query_cycle =
      snapshot.tracking && bounds_query_cycle_count(b) != snapshot.cycle_blocks;
  query_invalid =
      snapshot.tracking && bounds_query_invalid_since(b, snapshot.transport);
  if (oom)
    *oom = state->oom || b->oom;
  if (limited)
    *limited = state->limited || query_limited;
  defined_state_destroy(state);
  return state->oom || state->limited || state->invalid || query_limited ||
         query_cycle || query_invalid || b->oom;
}

static ixs_check_result bounds_check_defined_detail(ixs_bounds *b,
                                                    ixs_node *expr, bool *oom,
                                                    bool *limited) {
  defined_state state;
  bounds_defined_query_snapshot snapshot = bounds_defined_query_observe(b);
  ixs_check_result result;
  if (oom)
    *oom = false;
  if (limited)
    *limited = false;
  if (!b || !b->ctx || !b->scratch || !expr || b->oom ||
      ixs_bounds_has_empty(b))
    return IXS_CHECK_UNKNOWN;
  if (ixs_ctx_owns_node(b->ctx, expr) && ixs_node_is_known_total(expr))
    return IXS_CHECK_TRUE;
  if (bounds_defined_cache_lookup(b, expr, &result))
    return result;
  defined_state_init(&state, b->ctx, b);
  result = defined_eval(&state, b, expr, 0);
  if (bounds_defined_query_failed(b, &state, result, snapshot, oom, limited))
    return IXS_CHECK_UNKNOWN;
  if (!bounds_defined_cache_publish(b, expr, result)) {
    if (oom)
      *oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  return result;
}

IXS_STATIC ixs_check_result ixs_bounds_check_defined(ixs_bounds *b,
                                                     ixs_node *expr) {
  return bounds_check_defined_detail(b, expr, NULL, NULL);
}

IXS_STATIC ixs_algebra_status ixs_bounds_check_integer_domain(ixs_bounds *b,
                                                              ixs_node *expr) {
  ixs_check_result check;
  ixs_bounds_transport_snapshot snapshot =
      ixs_bounds_query_transport_snapshot(b);
  ixs_bounds_transport_status transport;
  bool oom = false, limited = false;
  check = bounds_check_defined_detail(b, expr, &oom, &limited);
  if (check == IXS_CHECK_TRUE)
    check = ixs_bounds_check_integer_valued(b, expr);
  transport = ixs_bounds_query_transport_since(b, snapshot);
  if (transport == IXS_BOUNDS_TRANSPORT_INVALID)
    return IXS_ALGEBRA_INVALID;
  if (oom || transport == IXS_BOUNDS_TRANSPORT_OOM)
    return IXS_ALGEBRA_OOM;
  if (limited || transport == IXS_BOUNDS_TRANSPORT_LIMITED)
    return IXS_ALGEBRA_LIMITED;
  return check == IXS_CHECK_TRUE ? IXS_ALGEBRA_MATCH : IXS_ALGEBRA_NO_MATCH;
}

static bool range_result_to_interval(const ixs_range_result *range,
                                     ixs_interval *out) {
  ixs_interval iv;
  if (!range || !out)
    return false;
  iv.valid = true;
  iv.lo_inf = false;
  iv.hi_inf = false;
  if (range->has_lower) {
    if (!ixs_rat_normalize(range->lower_p, range->lower_q, &iv.lo_p, &iv.lo_q))
      return false;
  } else {
    ixs_interval_set_lo_neg_inf(&iv);
  }
  if (range->has_upper) {
    if (!ixs_rat_normalize(range->upper_p, range->upper_q, &iv.hi_p, &iv.hi_q))
      return false;
  } else {
    ixs_interval_set_hi_pos_inf(&iv);
  }
  if (ixs_interval_is_empty(iv))
    return false;
  *out = iv;
  return true;
}

static void interval_to_range_result(ixs_interval iv, ixs_range_result *out) {
  out->has_lower = !iv.lo_inf;
  out->has_upper = !iv.hi_inf;
  out->lower_p = iv.lo_inf ? 0 : iv.lo_p;
  out->lower_q = iv.lo_inf ? 1 : iv.lo_q;
  out->upper_p = iv.hi_inf ? 0 : iv.hi_p;
  out->upper_q = iv.hi_inf ? 1 : iv.hi_q;
}

static bool facts_bind(ixs_facts *facts, ixs_session_binding *binding,
                       ixs_ctx **ctx) {
  if (!facts || !facts->impl || !facts->ctx || !binding || !ctx ||
      facts->epoch == 0 || facts->impl->ctx != facts->ctx ||
      facts->impl->epoch != facts->epoch)
    return false;
  *ctx = ixs_session_bind_impl(binding, facts->impl);
  bounds_store_bind(&facts->bounds, *ctx, &(*ctx)->scratch);
  return true;
}

#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
IXS_STATIC ixs_radix_algebra_result
ixs_radix_algebra_facts_probe(ixs_facts *facts, const ixs_node *expr) {
  ixs_radix_algebra_result result = {IXS_CHECK_UNKNOWN, false, false};
  ixs_session_binding binding;
  ixs_ctx *ctx;
  if (!expr || !facts_bind(facts, &binding, &ctx))
    return result;
  result = ixs_radix_algebra_nonnegative(&facts->bounds, expr);
  ixs_session_unbind(&binding);
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

static bool facts_ready(const ixs_facts *facts) {
  return facts && facts->usable && !facts->bounds.oom;
}

static void facts_poison(ixs_facts *facts) {
  if (facts)
    facts->usable = false;
}

static void facts_commit(ixs_facts *facts, ixs_bounds *candidate) {
  /* A fork's projection memo is query-local and cannot be transferred into the
   * committed bounds.  Destroy it, then reuse the destination's persistent
   * table allocation after advancing its semantic generation once. */
  assert(candidate->store_ctx != NULL);
  assert(candidate->query_tracking_depth == 0);
  assert(!candidate->query_state_owner && !candidate->query_state_borrowed);
  /* Read queries restore their temporary allocations but may retain arena
   * chunks for reuse.  A commit replaces the complete bounds object, so
   * release that old workspace before overwriting its arena owner. */
  bounds_query_reset_arena(&facts->bounds);
  bounds_query_reset_arena(candidate);
  bounds_relation_projection_commit(&facts->bounds, candidate);
  assert(candidate->query_state_arena.current == NULL &&
         candidate->query_state_arena.spare == NULL &&
         candidate->query_state_arena.inline_chunk == NULL);
  assert(candidate->query_arena.current == NULL &&
         candidate->query_arena.spare == NULL &&
         candidate->query_arena.inline_chunk == NULL);
  assert(facts->bounds.query_state_arena.current == NULL &&
         facts->bounds.query_state_arena.spare == NULL &&
         facts->bounds.query_state_arena.inline_chunk == NULL);
  assert(facts->bounds.query_arena.current == NULL &&
         facts->bounds.query_arena.spare == NULL &&
         facts->bounds.query_arena.inline_chunk == NULL);
  candidate->cache = facts->bounds.cache;
  candidate->cache_cap = facts->bounds.cache_cap;
  bounds_store_invalidate_reads(candidate);
  facts->bounds = *candidate;
}

static bool facts_node_ok(ixs_ctx *ctx, ixs_node *node) {
  return node && !ixs_node_is_sentinel(node) && ixs_ctx_owns_node(ctx, node);
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

static void bounds_add_var_fact(ixs_bounds *dst, const ixs_var_bound *src) {
  ixs_var_bound *v = bounds_store_find_var(dst, src->name);
  bool changed;
  bounds_store_invalidate_reads(dst);
  if (!v) {
    v = bounds_store_get_or_create_var(dst, src->name);
    if (!v)
      return;
    bounds_store_import_var(dst, v, src);
    bounds_store_refine_var_bits(dst, v);
    bounds_difference_propagate_symbol(dst, src->name);
    return;
  }

  changed = bounds_store_set_var_interval(dst, v, iv_intersect(v->iv, src->iv));
  if (src->modulus > 0)
    apply_modrem(dst, src->name, src->modulus, src->remainder);
  bounds_store_apply_var_known_bits(dst, v, src->bits.known_zero,
                                    src->bits.known_one);
  bounds_store_apply_pow2(dst, v, src->bits.pow2);
  if (changed)
    bounds_difference_propagate_symbol(dst, src->name);
}

static void bounds_add_var_interval(ixs_bounds *dst, const char *name,
                                    ixs_interval iv) {
  ixs_var_bound fact;
  if (!iv.valid)
    return;
  memset(&fact, 0, sizeof(fact));
  fact.name = name;
  fact.iv = iv;
  bounds_add_var_fact(dst, &fact);
}

static bool bounds_extract_integer_affine(ixs_node *expr, const char **name,
                                          int64_t *scale, int64_t *offset) {
  int64_t p, q;
  if (!expr || !name || !scale || !offset)
    return false;
  if (expr->tag == IXS_SYM) {
    *name = expr->u.name;
    *scale = 1;
    *offset = 0;
    return true;
  }
  if (expr->tag == IXS_MUL && expr->u.mul.nfactors == 1 &&
      expr->u.mul.factors[0].exp == 1 &&
      expr->u.mul.factors[0].base->tag == IXS_SYM) {
    ixs_node_get_rat(expr->u.mul.coeff, &p, &q);
    if (q != 1 || p == 0)
      return false;
    *name = expr->u.mul.factors[0].base->u.name;
    *scale = p;
    *offset = 0;
    return true;
  }
  if (expr->tag == IXS_ADD && expr->u.add.nterms == 1 &&
      expr->u.add.terms[0].term->tag == IXS_SYM) {
    ixs_node_get_rat(expr->u.add.coeff, offset, &q);
    if (q != 1)
      return false;
    ixs_node_get_rat(expr->u.add.terms[0].coeff, scale, &q);
    if (q != 1 || *scale == 0)
      return false;
    *name = expr->u.add.terms[0].term->u.name;
    return true;
  }
  return false;
}

static bool bounds_interval_contains_rational(ixs_interval iv, int64_t p,
                                              int64_t q) {
  if (!iv.valid)
    return true;
  if (!iv.lo_inf && ixs_rat_cmp(p, q, iv.lo_p, iv.lo_q) < 0)
    return false;
  if (!iv.hi_inf && ixs_rat_cmp(p, q, iv.hi_p, iv.hi_q) > 0)
    return false;
  return true;
}

static void bounds_transfer_inverse_congruence(ixs_bounds *dst,
                                               const char *name, int64_t scale,
                                               int64_t offset, int64_t modulus,
                                               int64_t residue) {
  uint64_t m, a, rhs, g, reduced, inverse, result;
  if (modulus <= 0)
    return;
  m = (uint64_t)modulus;
  a = ixs_int64_normalize_residue(scale, m);
  rhs = ixs_u64_sub_mod(ixs_int64_normalize_residue(residue, m),
                        ixs_int64_normalize_residue(offset, m), m);
  g = ixs_u64_gcd(a, m);
  if (rhs % g != 0) {
    bounds_store_mark_contradiction(dst);
    return;
  }
  reduced = m / g;
  if (reduced == 1u)
    return;
  if (!ixs_u64_mod_inverse((a / g) % reduced, reduced, &inverse)) {
    bounds_store_mark_contradiction(dst);
    return;
  }
  result = ixs_u64_mul_mod((rhs / g) % reduced, inverse, reduced);
  apply_modrem(dst, name, (int64_t)reduced, (int64_t)result);
}

static void bounds_transfer_affine_range(ixs_bounds *dst, const char *name,
                                         int64_t scale, int64_t offset,
                                         ixs_interval iv) {
  int64_t neg_offset, denominator;
  ixs_interval shifted, inverse;
  if (!iv.valid || !ixs_safe_neg(offset, &neg_offset))
    return;
  shifted = iv_add(iv, ixs_interval_exact(neg_offset, 1));
  if (scale > 0) {
    denominator = scale;
    inverse = iv_mul_const(shifted, 1, denominator);
  } else {
    if (!ixs_safe_neg(scale, &denominator))
      return;
    inverse = iv_mul_const(shifted, -1, denominator);
  }
  if (inverse.valid)
    bounds_add_var_interval(dst, name, inverse);
}

static void bounds_check_constant_var_fact(ixs_bounds *dst,
                                           const ixs_var_bound *src, int64_t p,
                                           int64_t q) {
  uint64_t value;
  if (!bounds_interval_contains_rational(src->iv, p, q))
    bounds_store_mark_contradiction(dst);
  if (src->modulus > 0 &&
      (q != 1 || ixs_int64_normalize_residue(p, (uint64_t)src->modulus) !=
                     (uint64_t)src->remainder))
    bounds_store_mark_contradiction(dst);
  if (src->bits.known_zero != 0 || src->bits.known_one != 0) {
    if (q != 1) {
      bounds_store_mark_contradiction(dst);
    } else {
      value = (uint64_t)p;
      if ((src->bits.known_zero & value) != 0 ||
          (src->bits.known_one & ~value) != 0)
        bounds_store_mark_contradiction(dst);
    }
  }
  if (src->bits.pow2 != IXS_POW2_UNKNOWN) {
    if (q != 1 ||
        (src->bits.pow2 == IXS_POW2_POSITIVE &&
         !ixs_int64_is_positive_pow2(p)) ||
        (src->bits.pow2 == IXS_POW2_OR_ZERO && p != 0 &&
         !ixs_int64_is_positive_pow2(p)))
      bounds_store_mark_contradiction(dst);
  }
}

static void bounds_transfer_range(ixs_bounds *dst, ixs_node *replacement,
                                  ixs_interval iv) {
  const char *name;
  int64_t scale, offset, p, q;
  if (!iv.valid)
    return;
  if (ixs_node_is_const(replacement)) {
    ixs_node_get_rat(replacement, &p, &q);
    if (!bounds_interval_contains_rational(iv, p, q))
      bounds_store_mark_contradiction(dst);
    return;
  }
  if (bounds_extract_integer_affine(replacement, &name, &scale, &offset))
    bounds_transfer_affine_range(dst, name, scale, offset, iv);
}

static void bounds_transfer_var_fact(ixs_bounds *dst, const ixs_var_bound *src,
                                     ixs_node *replacement) {
  const char *name;
  int64_t scale, offset, p, q;
  unsigned low_bits = 0;
  uint64_t known, modulus, mask, residue;
  ixs_var_bound renamed;
  ixs_var_bound *var;

  if (replacement->tag == IXS_SYM) {
    renamed = *src;
    renamed.name = replacement->u.name;
    bounds_add_var_fact(dst, &renamed);
    return;
  }
  if (ixs_node_is_const(replacement)) {
    ixs_node_get_rat(replacement, &p, &q);
    bounds_check_constant_var_fact(dst, src, p, q);
    return;
  }
  if (!bounds_extract_integer_affine(replacement, &name, &scale, &offset))
    return;

  bounds_transfer_affine_range(dst, name, scale, offset, src->iv);
  if (src->modulus > 0)
    bounds_transfer_inverse_congruence(dst, name, scale, offset, src->modulus,
                                       src->remainder);

  known = src->bits.known_zero | src->bits.known_one;
  while (low_bits < 62u && (known & (UINT64_C(1) << low_bits)) != 0)
    low_bits++;
  if (low_bits != 0) {
    modulus = UINT64_C(1) << low_bits;
    mask = modulus - 1u;
    residue = src->bits.known_one & mask;
    bounds_transfer_inverse_congruence(dst, name, scale, offset,
                                       (int64_t)modulus, (int64_t)residue);
  }

  if (offset == 0 && ixs_int64_is_positive_pow2(scale) &&
      src->bits.pow2 != IXS_POW2_UNKNOWN) {
    var = bounds_store_get_or_create_var(dst, name);
    bounds_store_apply_pow2(dst, var, src->bits.pow2);
  }
}

/* Build a fixed-capacity table at no more than half load. Initialization is
 * O(count); predicate processing never grows the table. */
static bool facts_predicate_set_init(ixs_arena *arena, size_t count,
                                     ixs_node ***slots, size_t *capacity) {
  size_t needed;
  *slots = NULL;
  *capacity = 0;
  if (count < 2)
    return true;
  if (count > SIZE_MAX / 2u)
    return false;
  needed = count * 2u;
  *capacity = 2u;
  while (*capacity < needed) {
    if (*capacity > SIZE_MAX / 2u)
      return false;
    *capacity *= 2u;
  }
  if (*capacity > SIZE_MAX / sizeof(**slots))
    return false;
  *slots = ixs_arena_alloc(arena, *capacity * sizeof(**slots), sizeof(void *));
  if (!*slots)
    return false;
  memset(*slots, 0, *capacity * sizeof(**slots));
  return true;
}

/* Expected O(1) at the fixed half-load bound; collisions probe linearly. */
static bool facts_predicate_seen_or_insert(ixs_node **slots, size_t capacity,
                                           ixs_node *predicate) {
  size_t index = predicate->hash & (capacity - 1u);
  while (slots[index] && slots[index] != predicate)
    index = (index + 1u) & (capacity - 1u);
  if (slots[index])
    return true;
  slots[index] = predicate;
  return false;
}

#define FACTS_CLOSURE_CACHE_CAP 32u
#define FACTS_CLOSURE_CACHE_SLOT_BYTES (3u * 1024u)
#define FACTS_CLOSURE_CACHE_RETAINED_LIMIT (128u * 1024u)
#define FACTS_CLOSURE_CACHE_SLOT_NODES                                         \
  (FACTS_CLOSURE_CACHE_SLOT_BYTES / sizeof(ixs_node *))

typedef struct {
  uint64_t hash;
  size_t n_predicates;
  size_t n_replay;
  ixs_node *nodes[FACTS_CLOSURE_CACHE_SLOT_NODES];
  bool valid;
} facts_closure_cache_entry;

typedef struct {
  facts_closure_cache_entry *entries[FACTS_CLOSURE_CACHE_CAP];
#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
  size_t lookups;
  size_t hits;
  size_t stores;
  size_t bypasses;
  size_t entry_count;
#endif
} facts_closure_cache;

typedef char facts_closure_cache_must_fit_retained_limit
    [(sizeof(facts_closure_cache) +
          FACTS_CLOSURE_CACHE_CAP * sizeof(facts_closure_cache_entry) <=
      FACTS_CLOSURE_CACHE_RETAINED_LIMIT)
         ? 1
         : -1];

typedef struct {
  ixs_node *replay[FACTS_CLOSURE_CACHE_SLOT_NODES];
  size_t n_replay;
  size_t replay_limit;
  bool overflow;
} facts_closure_capture;

typedef struct {
  facts_closure_capture capture;
  uint64_t hash;
  bool store;
} facts_closure_cache_result;

static facts_closure_cache *facts_closure_cache_get(ixs_ctx *ctx) {
  facts_closure_cache *cache;
  if (!ctx)
    return NULL;
  cache = ctx->facts_closure_cache;
  if (cache)
    return cache;
  cache = ixs_arena_alloc(&ctx->arena, sizeof(*cache), sizeof(void *));
  if (!cache)
    return NULL;
  memset(cache, 0, sizeof(*cache));
  ctx->facts_closure_cache = cache;
  return cache;
}

static uint64_t facts_closure_hash(ixs_node *const *predicates,
                                   size_t n_predicates) {
  uint64_t hash = UINT64_C(0x9e3779b97f4a7c15) ^ (uint64_t)n_predicates;
  size_t i;
  for (i = 0; i < n_predicates; i++) {
    uint64_t value = (uint64_t)(uintptr_t)predicates[i];
    hash ^= value + UINT64_C(0x9e3779b97f4a7c15) + (hash << 6) + (hash >> 2);
  }
  hash ^= hash >> 33;
  hash *= UINT64_C(0xff51afd7ed558ccd);
  hash ^= hash >> 33;
  return hash;
}

/* Lookup is O(n) in the explicit batch size and never scans context state. */
static facts_closure_cache_entry *
facts_closure_cache_lookup(ixs_ctx *ctx, ixs_node *const *predicates,
                           size_t n_predicates, uint64_t *hash_out) {
  facts_closure_cache *cache;
  facts_closure_cache_entry *entry;
  uint64_t hash;
  size_t i;
  if (n_predicates > FACTS_CLOSURE_CACHE_SLOT_NODES) {
#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
    cache = facts_closure_cache_get(ctx);
    if (cache) {
      cache->lookups++;
      cache->bypasses++;
    }
#endif
    return NULL;
  }
  hash = facts_closure_hash(predicates, n_predicates);
  *hash_out = hash;
  cache = facts_closure_cache_get(ctx);
  if (!cache)
    return NULL;
#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
  cache->lookups++;
#endif
  entry = cache->entries[(size_t)hash & (FACTS_CLOSURE_CACHE_CAP - 1u)];
  if (!entry || !entry->valid || entry->hash != hash ||
      entry->n_predicates != n_predicates)
    return NULL;
  for (i = 0; i < n_predicates; i++) {
    if (entry->nodes[i] != predicates[i])
      return NULL;
  }
#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
  cache->hits++;
#endif
  return entry;
}

#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
static void facts_closure_cache_note_bypass(ixs_ctx *ctx) {
  facts_closure_cache *cache = facts_closure_cache_get(ctx);
  if (cache)
    cache->bypasses++;
}
#endif

/* Store is O(n + r) in the exact key and replay sequence. Collisions replace
 * an entry in place, so retained cache memory cannot grow after 32 slots. */
static void facts_closure_cache_store(ixs_ctx *ctx, ixs_node *const *predicates,
                                      size_t n_predicates,
                                      const facts_closure_capture *capture,
                                      uint64_t hash) {
  facts_closure_cache *cache;
  facts_closure_cache_entry *entry;
  size_t slot;
  if (!capture || capture->overflow ||
      n_predicates > FACTS_CLOSURE_CACHE_SLOT_NODES ||
      capture->n_replay > FACTS_CLOSURE_CACHE_SLOT_NODES - n_predicates) {
#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
    facts_closure_cache_note_bypass(ctx);
#endif
    return;
  }
  cache = facts_closure_cache_get(ctx);
  if (!cache)
    return;
  slot = (size_t)hash & (FACTS_CLOSURE_CACHE_CAP - 1u);
  entry = cache->entries[slot];
  if (!entry) {
    entry = ixs_arena_alloc(&ctx->arena, sizeof(*entry), sizeof(void *));
    if (!entry)
      return;
    memset(entry, 0, sizeof(*entry));
    cache->entries[slot] = entry;
#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
    cache->entry_count++;
#endif
  }
  entry->valid = false;
  if (n_predicates)
    memcpy(entry->nodes, predicates, n_predicates * sizeof(*predicates));
  if (capture->n_replay)
    memcpy(entry->nodes + n_predicates, capture->replay,
           capture->n_replay * sizeof(*capture->replay));
  entry->hash = hash;
  entry->n_predicates = n_predicates;
  entry->n_replay = capture->n_replay;
  entry->valid = true;
#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
  cache->stores++;
#endif
}

#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
IXS_STATIC void
ixs_facts_closure_cache_stats(const ixs_ctx *ctx,
                              ixs_facts_closure_cache_stats_result *stats) {
  const facts_closure_cache *cache = ctx ? ctx->facts_closure_cache : NULL;
  if (!stats)
    return;
  memset(stats, 0, sizeof(*stats));
  stats->retained_limit = FACTS_CLOSURE_CACHE_RETAINED_LIMIT;
  stats->slot_node_capacity = FACTS_CLOSURE_CACHE_SLOT_NODES;
  if (!cache)
    return;
  stats->lookups = cache->lookups;
  stats->hits = cache->hits;
  stats->stores = cache->stores;
  stats->bypasses = cache->bypasses;
  stats->entries = cache->entry_count;
  stats->retained_bytes =
      sizeof(*cache) + cache->entry_count * sizeof(facts_closure_cache_entry);
}
#endif

static bool facts_bounds_is_empty_domain(const ixs_bounds *bounds) {
  return bounds && bounds->nvars == 0 && bounds->nexprs == 0 &&
         bounds->nmod_inverse_watchers == 0 &&
         bounds_difference_is_empty(bounds) &&
         ixs_relation_algebra_endpoint_count(&bounds->relations) == 0 &&
         ixs_relation_algebra_edge_count(&bounds->relations) == 0 &&
         ixs_relation_algebra_total_count(&bounds->relations) == 0 &&
         bounds->nnonzero == 0 && !bounds->has_modrem &&
         !bounds->contradiction && !bounds->oom;
}

static void facts_closure_capture_init(facts_closure_capture *capture,
                                       size_t n_predicates) {
  memset(capture, 0, sizeof(*capture));
  if (n_predicates > FACTS_CLOSURE_CACHE_SLOT_NODES) {
    capture->overflow = true;
    return;
  }
  capture->replay_limit = FACTS_CLOSURE_CACHE_SLOT_NODES - n_predicates;
}

static void facts_closure_capture_append(facts_closure_capture *capture,
                                         ixs_node *predicate) {
  if (!capture || capture->overflow)
    return;
  if (capture->n_replay >= capture->replay_limit) {
    capture->overflow = true;
    return;
  }
  capture->replay[capture->n_replay++] = predicate;
}

typedef struct {
  const char *name;
  size_t first_occurrence;
} facts_symbol_slot;

typedef struct {
  const char *name;
  size_t predicate;
  size_t next_for_predicate;
  size_t next_for_symbol;
} facts_symbol_occurrence;

typedef struct {
  ixs_arena arena;
  size_t n_predicates;
  bool *active;
  bool *queued;
  size_t *queue;
  size_t queue_head;
  size_t queue_tail;
  size_t queue_count;
  size_t *predicate_occurrences;
  facts_symbol_slot *symbols;
  size_t symbol_capacity;
  size_t symbol_count;
  facts_symbol_occurrence *occurrences;
  size_t occurrence_capacity;
  size_t occurrence_count;
  ixs_node **seen;
  size_t seen_capacity;
} facts_worklist;

typedef union {
  void *align;
  unsigned char bytes[IXS_ARENA_DEFAULT_SIZE];
} facts_work_storage;

static bool facts_worklist_alloc_arrays(facts_worklist *work) {
  size_t count = work->n_predicates;
  size_t i;
  if (count > SIZE_MAX / sizeof(*work->queue) ||
      count > SIZE_MAX / sizeof(*work->predicate_occurrences))
    return false;
  work->active = ixs_arena_alloc(&work->arena, count * sizeof(*work->active),
                                 sizeof(void *));
  work->queued = ixs_arena_alloc(&work->arena, count * sizeof(*work->queued),
                                 sizeof(void *));
  work->queue = ixs_arena_alloc(&work->arena, count * sizeof(*work->queue),
                                sizeof(void *));
  work->predicate_occurrences = ixs_arena_alloc(
      &work->arena, count * sizeof(*work->predicate_occurrences),
      sizeof(void *));
  if (!work->active || !work->queued || !work->queue ||
      !work->predicate_occurrences)
    return false;
  memset(work->active, 0, count * sizeof(*work->active));
  memset(work->queued, 0, count * sizeof(*work->queued));
  for (i = 0; i < count; i++)
    work->predicate_occurrences[i] = SIZE_MAX;
  return true;
}

static bool facts_worklist_init(facts_worklist *work,
                                facts_work_storage *storage,
                                size_t n_predicates) {
  memset(work, 0, sizeof(*work));
  ixs_arena_init_inline(&work->arena, storage->bytes, sizeof(storage->bytes),
                        IXS_ARENA_DEFAULT_SIZE);
  work->n_predicates = n_predicates;
  if (!facts_worklist_alloc_arrays(work) ||
      !facts_predicate_set_init(&work->arena, n_predicates, &work->seen,
                                &work->seen_capacity)) {
    ixs_arena_destroy_transient(&work->arena);
    return false;
  }
  return true;
}

static void facts_worklist_destroy(facts_worklist *work) {
  ixs_arena_destroy_transient(&work->arena);
}

static facts_symbol_slot *facts_symbol_find(facts_worklist *work,
                                            const char *name) {
  size_t index;
  if (!work->symbols)
    return NULL;
  index = ixs_hash_ptr(name) & (work->symbol_capacity - 1u);
  while (work->symbols[index].name && work->symbols[index].name != name)
    index = (index + 1u) & (work->symbol_capacity - 1u);
  return &work->symbols[index];
}

static bool facts_symbol_table_grow(facts_worklist *work) {
  size_t new_capacity =
      work->symbol_capacity ? work->symbol_capacity * 2u : FACT_WORK_INIT_CAP;
  facts_symbol_slot *symbols;
  size_t i;
  if (new_capacity <= work->symbol_capacity ||
      new_capacity > SIZE_MAX / sizeof(*symbols))
    return false;
  symbols = ixs_arena_alloc(&work->arena, new_capacity * sizeof(*symbols),
                            sizeof(void *));
  if (!symbols)
    return false;
  memset(symbols, 0, new_capacity * sizeof(*symbols));
  for (i = 0; i < work->symbol_capacity; i++) {
    if (work->symbols[i].name) {
      size_t index = ixs_hash_ptr(work->symbols[i].name) & (new_capacity - 1u);
      while (symbols[index].name)
        index = (index + 1u) & (new_capacity - 1u);
      symbols[index] = work->symbols[i];
    }
  }
  work->symbols = symbols;
  work->symbol_capacity = new_capacity;
  return true;
}

static bool facts_occurrences_grow(facts_worklist *work) {
  size_t new_capacity = work->occurrence_capacity
                            ? work->occurrence_capacity * 2u
                            : FACT_WORK_INIT_CAP;
  facts_symbol_occurrence *occurrences;
  if (new_capacity <= work->occurrence_capacity ||
      new_capacity > SIZE_MAX / sizeof(*occurrences))
    return false;
  occurrences =
      ixs_arena_grow(&work->arena, work->occurrences,
                     work->occurrence_capacity * sizeof(*work->occurrences),
                     new_capacity * sizeof(*work->occurrences), sizeof(void *));
  if (!occurrences)
    return false;
  work->occurrences = occurrences;
  work->occurrence_capacity = new_capacity;
  return true;
}

static bool facts_worklist_add_symbol(facts_worklist *work, size_t predicate,
                                      const char *name) {
  facts_symbol_slot *slot;
  facts_symbol_occurrence *occurrence;
  size_t index;
  if (!work->symbol_capacity ||
      work->symbol_count >= work->symbol_capacity / 2u) {
    if (!facts_symbol_table_grow(work))
      return false;
  }
  if (work->occurrence_count >= work->occurrence_capacity &&
      !facts_occurrences_grow(work))
    return false;
  slot = facts_symbol_find(work, name);
  if (!slot)
    return false;
  if (!slot->name) {
    slot->name = name;
    slot->first_occurrence = SIZE_MAX;
    work->symbol_count++;
  }
  index = work->occurrence_count++;
  occurrence = &work->occurrences[index];
  occurrence->name = name;
  occurrence->predicate = predicate;
  occurrence->next_for_predicate = work->predicate_occurrences[predicate];
  occurrence->next_for_symbol = slot->first_occurrence;
  work->predicate_occurrences[predicate] = index;
  slot->first_occurrence = index;
  return true;
}

static bool query_node_set_grow(ixs_arena *arena, query_node_set *set) {
  size_t new_capacity = set->capacity ? set->capacity * 2u : FACT_WORK_INIT_CAP;
  ixs_node **slots;
  size_t i;
  if (new_capacity <= set->capacity || new_capacity > SIZE_MAX / sizeof(*slots))
    return false;
  slots = ixs_arena_alloc(arena, new_capacity * sizeof(*slots), sizeof(void *));
  if (!slots)
    return false;
  memset(slots, 0, new_capacity * sizeof(*slots));
  for (i = 0; i < set->capacity; i++) {
    if (set->slots[i]) {
      size_t index = set->slots[i]->hash & (new_capacity - 1u);
      while (slots[index])
        index = (index + 1u) & (new_capacity - 1u);
      slots[index] = set->slots[i];
    }
  }
  set->slots = slots;
  set->capacity = new_capacity;
  return true;
}

IXS_STATIC bool query_node_set_insert(ixs_arena *arena, query_node_set *set,
                                      ixs_node *node, bool *inserted) {
  size_t index;
  if (!set->capacity || set->count >= set->capacity / 2u) {
    if (!query_node_set_grow(arena, set))
      return false;
  }
  index = node->hash & (set->capacity - 1u);
  while (set->slots[index] && set->slots[index] != node)
    index = (index + 1u) & (set->capacity - 1u);
  if (set->slots[index]) {
    *inserted = false;
    return true;
  }
  set->slots[index] = node;
  set->count++;
  *inserted = true;
  return true;
}

IXS_STATIC bool query_node_stack_push(ixs_arena *arena, ixs_node ***stack,
                                      size_t *count, size_t *capacity,
                                      ixs_node *node) {
  return ixs_query_node_vector_push(arena, stack, count, capacity, node,
                                    FACT_WORK_INIT_CAP);
}

static bool facts_worklist_index_predicate(facts_worklist *work,
                                           size_t predicate, ixs_node *root) {
  facts_work_storage storage;
  ixs_arena traversal;
  query_node_set visited;
  ixs_node **stack = NULL;
  size_t stack_capacity = 0;
  size_t stack_count = 0;
  bool ok = false;
  ixs_arena_init_inline(&traversal, storage.bytes, sizeof(storage.bytes),
                        IXS_ARENA_DEFAULT_SIZE);
  memset(&visited, 0, sizeof(visited));
  if (!query_node_stack_push(&traversal, &stack, &stack_count, &stack_capacity,
                             root))
    goto cleanup;
  while (stack_count > 0) {
    ixs_node *node = stack[--stack_count];
    uint32_t child_count;
    uint32_t i;
    bool inserted;
    if (!query_node_set_insert(&traversal, &visited, node, &inserted))
      goto cleanup;
    if (!inserted)
      continue;
    if (node->tag == IXS_SYM &&
        !facts_worklist_add_symbol(work, predicate, node->u.name))
      goto cleanup;
    child_count = ixs_node_nchildren(node);
    for (i = 0; i < child_count; i++) {
      if (!query_node_stack_push(&traversal, &stack, &stack_count,
                                 &stack_capacity, ixs_node_child(node, i)))
        goto cleanup;
    }
  }
  ok = true;

cleanup:
  ixs_arena_destroy_transient(&traversal);
  return ok;
}

static bool facts_worklist_enqueue(facts_worklist *work, size_t predicate) {
  if (!work->active[predicate] || work->queued[predicate])
    return true;
  if (work->queue_count >= work->n_predicates)
    return false;
  work->queue[work->queue_tail] = predicate;
  work->queue_tail = (work->queue_tail + 1u) % work->n_predicates;
  work->queue_count++;
  work->queued[predicate] = true;
  return true;
}

static bool facts_worklist_build(facts_worklist *work,
                                 ixs_node *const *predicates) {
  size_t i;
  for (i = 0; i < work->n_predicates; i++) {
    if (work->seen && facts_predicate_seen_or_insert(
                          work->seen, work->seen_capacity, predicates[i]))
      continue;
    work->active[i] = true;
    if (!facts_worklist_index_predicate(work, i, predicates[i]) ||
        !facts_worklist_enqueue(work, i))
      return false;
  }
  return true;
}

static size_t facts_worklist_pop(facts_worklist *work) {
  size_t predicate = work->queue[work->queue_head];
  work->queue_head = (work->queue_head + 1u) % work->n_predicates;
  work->queue_count--;
  work->queued[predicate] = false;
  return predicate;
}

static bool facts_worklist_enqueue_all(facts_worklist *work) {
  size_t i;
  for (i = 0; i < work->n_predicates; i++) {
    if (!facts_worklist_enqueue(work, i))
      return false;
  }
  return true;
}

static bool facts_worklist_enqueue_dependencies(facts_worklist *work,
                                                size_t predicate) {
  size_t occurrence_index = work->predicate_occurrences[predicate];
  if (occurrence_index == SIZE_MAX)
    return facts_worklist_enqueue_all(work);
  while (occurrence_index != SIZE_MAX) {
    facts_symbol_occurrence *occurrence = &work->occurrences[occurrence_index];
    facts_symbol_slot *slot = facts_symbol_find(work, occurrence->name);
    size_t dependent;
    if (!slot || !slot->name) {
      assert(slot && slot->name &&
             "group-union dependency index lost an indexed symbol");
      return false;
    }
    dependent = slot->first_occurrence;
    while (dependent != SIZE_MAX) {
      if (!facts_worklist_enqueue(work, work->occurrences[dependent].predicate))
        return false;
      dependent = work->occurrences[dependent].next_for_symbol;
    }
    occurrence_index = occurrence->next_for_predicate;
  }
  return true;
}

static ixs_bounds_build_status facts_ingest_original_predicates(
    ixs_bounds *candidate, ixs_node *const *predicates,
    const facts_worklist *work, facts_closure_capture *capture) {
  size_t i;
  for (i = 0; i < work->n_predicates; i++) {
    ixs_bounds_build_status status;
    if (!work->active[i])
      continue;
    status = bounds_assume_ingest_predicate(candidate, predicates[i]);
    if (status != IXS_BOUNDS_BUILD_OK)
      return status;
    facts_closure_capture_append(capture, predicates[i]);
  }
  return IXS_BOUNDS_BUILD_OK;
}

static ixs_bounds_build_status facts_process_predicate_worklist(
    ixs_ctx *ctx, ixs_bounds *candidate, ixs_node *const *predicates,
    facts_worklist *work, facts_closure_capture *capture) {
  while (work->queue_count > 0) {
    size_t predicate_index = facts_worklist_pop(work);
    ixs_node *predicate;
    ixs_bounds_build_status status;
    bool changed = false;
    bool limited = false;
    bool *old_observer = bounds_store_swap_change_observer(candidate, &changed);
    predicate = simp_simplify_bounds_status(ctx, predicates[predicate_index],
                                            candidate, &limited);
    if (limited) {
      (void)bounds_store_swap_change_observer(candidate, old_observer);
      return IXS_BOUNDS_BUILD_LIMIT;
    }
    if (!predicate || candidate->oom) {
      (void)bounds_store_swap_change_observer(candidate, old_observer);
      return IXS_BOUNDS_BUILD_OOM;
    }
    status = bounds_assume_ingest_predicate(candidate, predicate);
    (void)bounds_store_swap_change_observer(candidate, old_observer);
    if (status != IXS_BOUNDS_BUILD_OK)
      return status;
    if (changed)
      facts_closure_capture_append(capture, predicate);
    if (candidate->contradiction || ixs_bounds_has_empty(candidate))
      return IXS_BOUNDS_BUILD_OK;
    if (changed && !facts_worklist_enqueue_dependencies(work, predicate_index))
      return IXS_BOUNDS_BUILD_OOM;
  }
  return IXS_BOUNDS_BUILD_OK;
}

static ixs_bounds_build_status
facts_replay_predicate_closure(ixs_bounds *candidate,
                               const facts_closure_cache_entry *entry) {
  ixs_node *const *replay = entry->nodes + entry->n_predicates;
  return bounds_assume_ingest_predicates(candidate, replay, entry->n_replay);
}

static ixs_bounds_build_status
facts_ingest_predicate_closure(ixs_ctx *ctx, ixs_bounds *candidate,
                               ixs_node *const *predicates, size_t n_predicates,
                               facts_closure_cache_result *cache_result) {
  facts_closure_cache_entry *cached = NULL;
  facts_closure_capture *capture_ptr = NULL;
  facts_work_storage storage;
  facts_worklist work;
  ixs_bounds_build_status status = IXS_BOUNDS_BUILD_OOM;
  bool cacheable = cache_result && facts_bounds_is_empty_domain(candidate);

  if (cache_result)
    cache_result->store = false;
  if (cacheable) {
    cached = facts_closure_cache_lookup(ctx, predicates, n_predicates,
                                        &cache_result->hash);
    if (cached)
      return facts_replay_predicate_closure(candidate, cached);
    if (n_predicates <= FACTS_CLOSURE_CACHE_SLOT_NODES) {
      facts_closure_capture_init(&cache_result->capture, n_predicates);
      capture_ptr = &cache_result->capture;
    }
  }
  if (!facts_worklist_init(&work, &storage, n_predicates))
    return IXS_BOUNDS_BUILD_OOM;
  if (!facts_worklist_build(&work, predicates))
    goto cleanup;

  /* Preserve original expression identities before fact-conditioned
   * rewrites. */
  status = facts_ingest_original_predicates(candidate, predicates, &work,
                                            capture_ptr);
  if (status != IXS_BOUNDS_BUILD_OK || candidate->contradiction ||
      ixs_bounds_has_empty(candidate))
    goto cleanup;

  /* A rewrite cannot introduce a symbol absent from its original predicate.
   * Revisit only predicates that share a symbol with a semantic refinement. */
  status = facts_process_predicate_worklist(ctx, candidate, predicates, &work,
                                            capture_ptr);

cleanup:
  if (status == IXS_BOUNDS_BUILD_OK && cacheable && capture_ptr)
    cache_result->store = true;
  facts_worklist_destroy(&work);
  return status;
}

ixs_facts *ixs_facts_create_preds(ixs_session *s, ixs_node *const *predicates,
                                  size_t n_predicates) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds bounds;
  ixs_bounds_build_status status;
  ixs_facts *facts;
  if (!s)
    return NULL;
  ctx = ixs_session_bind(&binding, s);
  mark = ixs_arena_save(&ctx->scratch);
  status = ixs_bounds_build_ctx(&bounds, ctx, &ctx->scratch, predicates,
                                n_predicates);
  if (status != IXS_BOUNDS_BUILD_OK)
    goto failed;
  facts = ixs_arena_alloc(&ctx->arena, sizeof(*facts), sizeof(void *));
  if (!facts) {
    ixs_bounds_destroy(&bounds);
    goto failed;
  }
  memset(facts, 0, sizeof(*facts));
  facts->impl = binding.impl;
  facts->ctx = ctx;
  facts->epoch = binding.impl->epoch;
  bounds_projection_cache_reset_storage(&bounds, false);
  assert(bounds.store_ctx != NULL && bounds.query_tracking_depth == 0 &&
         !bounds.query_state_owner && !bounds.query_state_borrowed &&
         bounds.query_state_arena.current == NULL &&
         bounds.query_state_arena.spare == NULL &&
         bounds.query_state_arena.inline_chunk == NULL &&
         bounds.query_arena.current == NULL &&
         bounds.query_arena.spare == NULL &&
         bounds.query_arena.inline_chunk == NULL);
  facts->bounds = bounds;
  facts->usable = true;
  facts->session_next = binding.impl->facts_head;
  binding.impl->facts_head = facts;
  ixs_session_unbind(&binding);
  return facts;

failed:
  ixs_arena_restore(&ctx->scratch, mark);
  ixs_session_unbind(&binding);
  return NULL;
}

ixs_facts *ixs_facts_create(ixs_session *s) {
  return ixs_facts_create_preds(s, NULL, 0);
}

static ixs_bounds_build_status facts_validate_closed_predicates(
    ixs_bounds *candidate, ixs_node *const *predicates, size_t n_predicates) {
  size_t i;
  if (candidate->contradiction || ixs_bounds_has_empty(candidate))
    return IXS_BOUNDS_BUILD_OK;
  for (i = 0; i < n_predicates; i++) {
    ixs_check_result defined;
    bool oom = false;
    bool limited = false;
    bool query_held = false;
    if (!ixs_bounds_query_hold_begin(candidate, predicates[i], &query_held))
      return candidate->oom ? IXS_BOUNDS_BUILD_OOM : IXS_BOUNDS_BUILD_LIMIT;
    defined =
        bounds_check_defined_detail(candidate, predicates[i], &oom, &limited);
    if (query_held)
      ixs_bounds_query_hold_end(candidate);
    if (defined == IXS_CHECK_TRUE)
      continue;
    if (oom || candidate->oom)
      return IXS_BOUNDS_BUILD_OOM;
    if (limited)
      return IXS_BOUNDS_BUILD_LIMIT;
    return assumption_invalid(candidate, "batch does not form a closed domain");
  }
  return IXS_BOUNDS_BUILD_OK;
}

static bool facts_assume_predicates(ixs_facts *facts,
                                    ixs_node *const *predicates,
                                    size_t n_predicates, bool require_closed) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds candidate;
  ixs_bounds_build_status status;
  facts_closure_cache_result closure_cache;
  bool candidate_ready = false;
  if (!facts_bind(facts, &binding, &ctx))
    return false;
  if (!facts_ready(facts)) {
    ixs_session_unbind(&binding);
    return false;
  }
  if (n_predicates == 0) {
    ixs_session_unbind(&binding);
    return true;
  }
  if (!predicates) {
    (void)assumption_invalid(&facts->bounds, "NULL array with nonzero count");
    facts_poison(facts);
    ixs_session_unbind(&binding);
    return false;
  }
  mark = ixs_arena_save(&ctx->scratch);
  if (!ixs_bounds_fork(&candidate, &facts->bounds)) {
    ixs_arena_restore(&ctx->scratch, mark);
    facts_poison(facts);
    ixs_session_unbind(&binding);
    return false;
  }
  candidate_ready = true;
  status =
      bounds_assume_validate_predicates(&candidate, predicates, n_predicates);
  if (status == IXS_BOUNDS_BUILD_OK)
    status = facts_ingest_predicate_closure(ctx, &candidate, predicates,
                                            n_predicates, &closure_cache);
  if (status == IXS_BOUNDS_BUILD_OK && require_closed)
    status =
        facts_validate_closed_predicates(&candidate, predicates, n_predicates);
  if (status == IXS_BOUNDS_BUILD_OK) {
    if (closure_cache.store)
      facts_closure_cache_store(ctx, predicates, n_predicates,
                                &closure_cache.capture, closure_cache.hash);
    facts_commit(facts, &candidate);
  } else {
    if (candidate_ready)
      ixs_bounds_destroy(&candidate);
    ixs_arena_restore(&ctx->scratch, mark);
    facts_poison(facts);
  }
  ixs_session_unbind(&binding);
  return status == IXS_BOUNDS_BUILD_OK;
}

bool ixs_facts_assume_preds(ixs_facts *facts, ixs_node *const *predicates,
                            size_t n_predicates) {
  return facts_assume_predicates(facts, predicates, n_predicates, true);
}

bool ixs_facts_assume_pred(ixs_facts *facts, ixs_node *pred) {
  return facts_assume_predicates(facts, &pred, 1, false);
}

bool ixs_facts_assume_range(ixs_facts *facts, ixs_node *expr,
                            const ixs_range_result *range) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds candidate;
  ixs_interval iv;
  bool candidate_ready = false;
  bool ok = false;
  if (!facts_bind(facts, &binding, &ctx))
    return false;
  if (!facts_ready(facts))
    goto cleanup;
  mark = ixs_arena_save(&ctx->scratch);
  if (!facts_node_ok(ctx, expr) || !range_result_to_interval(range, &iv))
    goto failed;
  if (!ixs_bounds_fork(&candidate, &facts->bounds))
    goto failed;
  candidate_ready = true;
  ixs_bounds_add_expr(&candidate, expr, iv);
  if (candidate.oom)
    goto failed;
  facts_commit(facts, &candidate);
  ok = true;
  goto cleanup;

failed:
  if (candidate_ready)
    ixs_bounds_destroy(&candidate);
  ixs_arena_restore(&ctx->scratch, mark);
  facts_poison(facts);

cleanup:
  ixs_session_unbind(&binding);
  return ok;
}

bool ixs_facts_derive_affine(ixs_facts *facts, ixs_node *base, int64_t scale,
                             int64_t offset, ixs_node *derived) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds candidate;
  ixs_interval iv, shifted;
  bool candidate_ready = false;
  bool query_held = false;
  bool ok = false;
  if (!facts_bind(facts, &binding, &ctx))
    return false;
  if (!facts_ready(facts))
    goto cleanup;
  mark = ixs_arena_save(&ctx->scratch);
  if (!facts_node_ok(ctx, base) || !facts_node_ok(ctx, derived))
    goto failed;
  if (!ixs_bounds_fork(&candidate, &facts->bounds))
    goto failed;
  candidate_ready = true;
  if (!ixs_bounds_query_hold_begin(&candidate, base, &query_held))
    goto failed;
  iv = ixs_bounds_get(&candidate, base);
  if (candidate.oom || !iv.valid || ixs_interval_is_empty(iv))
    goto failed;
  shifted = iv_add(iv_mul_const(iv, scale, 1), ixs_interval_exact(offset, 1));
  if (!shifted.valid || ixs_interval_is_empty(shifted))
    goto failed;
  ixs_bounds_add_expr(&candidate, derived, shifted);
  if (candidate.oom)
    goto failed;
  if (query_held) {
    ixs_bounds_query_hold_end(&candidate);
    query_held = false;
  }
  facts_commit(facts, &candidate);
  ok = true;
  goto cleanup;

failed:
  if (query_held)
    ixs_bounds_query_hold_end(&candidate);
  if (candidate_ready)
    ixs_bounds_destroy(&candidate);
  ixs_arena_restore(&ctx->scratch, mark);
  facts_poison(facts);

cleanup:
  ixs_session_unbind(&binding);
  return ok;
}

bool ixs_facts_substitute(ixs_facts *dst, const ixs_facts *src,
                          ixs_node *target, ixs_node *replacement) {
  return ixs_facts_substitute_multi(dst, src, 1, &target, &replacement);
}

static bool facts_substitution_inputs_ok(const ixs_facts *dst,
                                         const ixs_facts *src, ixs_ctx *ctx,
                                         uint32_t nsubs,
                                         ixs_node *const *targets,
                                         ixs_node *const *replacements) {
  uint32_t i;
  if (!src || src->impl != dst->impl || src->ctx != ctx ||
      src->epoch != dst->epoch || !facts_ready(src) ||
      (nsubs != 0 && (!targets || !replacements)))
    return false;
  for (i = 0; i < nsubs; i++) {
    if (!facts_node_ok(ctx, targets[i]) || !facts_node_ok(ctx, replacements[i]))
      return false;
  }
  return true;
}

static bool bounds_transfer_substituted_exprs(ixs_bounds *dst,
                                              const ixs_bounds *src,
                                              ixs_ctx *ctx, uint32_t nsubs,
                                              ixs_node *const *targets,
                                              ixs_node *const *replacements) {
  size_t i;
  for (i = 0; i < src->nexprs; i++) {
    if (!src->exprs[i].iv.valid) {
      bounds_store_mark_contradiction(dst);
      continue;
    }
    ixs_node *subst =
        simp_subs_multi(ctx, src->exprs[i].expr, nsubs, targets, replacements);
    if (!subst || ixs_node_is_sentinel(subst))
      return false;
    ixs_bounds_add_expr(dst, subst, src->exprs[i].iv);
    if (subst != src->exprs[i].expr)
      bounds_transfer_range(dst, subst, src->exprs[i].iv);
    if (dst->oom)
      return false;
  }
  return true;
}

static bool bounds_transfer_substituted_equalities(
    ixs_bounds *dst, const ixs_bounds *src, ixs_ctx *ctx, uint32_t nsubs,
    ixs_node *const *targets, ixs_node *const *replacements) {
  size_t i;
  for (i = 0; i < ixs_relation_algebra_edge_slot_count(&src->relations); i++) {
    const ixs_relation_edge *edge =
        ixs_relation_algebra_edge_at_slot(&src->relations, i);
    ixs_node *lhs;
    ixs_node *rhs;
    if (!edge)
      continue;
    lhs = simp_subs_multi(ctx, ixs_relation_edge_lhs(edge), nsubs, targets,
                          replacements);
    rhs = simp_subs_multi(ctx, ixs_relation_edge_rhs(edge), nsubs, targets,
                          replacements);
    if (!lhs || !rhs || ixs_node_is_sentinel(lhs) || ixs_node_is_sentinel(rhs))
      return false;
    bounds_admit_exact_relation(dst, lhs, rhs, ixs_relation_edge_offset(edge));
    if (dst->oom)
      return false;
  }
  return true;
}

static bool bounds_transfer_substituted_vars(ixs_bounds *dst,
                                             const ixs_bounds *src,
                                             ixs_ctx *ctx, uint32_t nsubs,
                                             ixs_node *const *targets,
                                             ixs_node *const *replacements) {
  size_t i;
  for (i = 0; i < src->nvars; i++) {
    ixs_node *sym =
        ixs_node_sym(ctx, src->vars[i].name, strlen(src->vars[i].name));
    ixs_node *subst;
    if (!sym || ixs_node_is_sentinel(sym))
      return false;
    subst = simp_subs_multi(ctx, sym, nsubs, targets, replacements);
    if (!subst || ixs_node_is_sentinel(subst))
      return false;
    if (subst == sym) {
      bounds_add_var_fact(dst, &src->vars[i]);
    } else {
      ixs_bounds_add_expr(dst, subst, src->vars[i].iv);
      bounds_transfer_var_fact(dst, &src->vars[i], subst);
    }
    if (dst->oom)
      return false;
  }
  return true;
}

static bool bounds_transfer_substituted_nonzero(ixs_bounds *dst,
                                                const ixs_bounds *src,
                                                ixs_ctx *ctx, uint32_t nsubs,
                                                ixs_node *const *targets,
                                                ixs_node *const *replacements) {
  size_t i;
  for (i = 0; i < src->nnonzero; i++) {
    ixs_node *subst =
        simp_subs_multi(ctx, src->nonzero[i], nsubs, targets, replacements);
    if (!subst || ixs_node_is_sentinel(subst))
      return false;
    bounds_add_nonzero(dst, subst);
    if (dst->oom)
      return false;
  }
  return true;
}

bool ixs_facts_substitute_multi(ixs_facts *dst, const ixs_facts *src,
                                uint32_t nsubs, ixs_node *const *targets,
                                ixs_node *const *replacements) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds candidate;
  bool candidate_ready = false;
  bool ok = false;

  if (!facts_bind(dst, &binding, &ctx))
    return false;
  if (!facts_ready(dst))
    goto cleanup;
  mark = ixs_arena_save(&ctx->scratch);
  if (!facts_substitution_inputs_ok(dst, src, ctx, nsubs, targets,
                                    replacements))
    goto failed;
  if (src == dst && nsubs == 0) {
    ok = true;
    goto cleanup;
  }
  if (!ixs_bounds_fork(&candidate, &dst->bounds))
    goto failed;
  candidate_ready = true;
  if (src->bounds.contradiction)
    bounds_store_mark_contradiction(&candidate);
  if (!bounds_transfer_substituted_exprs(&candidate, &src->bounds, ctx, nsubs,
                                         targets, replacements) ||
      !bounds_transfer_substituted_equalities(&candidate, &src->bounds, ctx,
                                              nsubs, targets, replacements) ||
      !bounds_transfer_substituted_vars(&candidate, &src->bounds, ctx, nsubs,
                                        targets, replacements) ||
      !bounds_transfer_substituted_nonzero(&candidate, &src->bounds, ctx, nsubs,
                                           targets, replacements))
    goto failed;
  facts_commit(dst, &candidate);
  ok = true;
  goto cleanup;

failed:
  if (candidate_ready)
    ixs_bounds_destroy(&candidate);
  ixs_arena_restore(&ctx->scratch, mark);
  facts_poison(dst);

cleanup:
  ixs_session_unbind(&binding);
  return ok;
}

static ixs_node *
facts_simplify_truncating_remainders(ixs_ctx *ctx, ixs_bounds *bounds,
                                     ixs_node *source, ixs_node *root,
                                     ixs_fact_query_status *status);

static bool facts_simplify_preflight(ixs_facts *facts, ixs_ctx *ctx,
                                     ixs_node *expr,
                                     ixs_simplify_result *result) {
  if (!facts_ready(facts)) {
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

  if (!facts_bind(facts, &binding, &ctx))
    return result;
  if (facts_simplify_preflight(facts, ctx, expr, &result)) {
    ixs_session_unbind(&binding);
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
  ixs_session_unbind(&binding);
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

  if (!facts_bind(facts, &binding, &ctx))
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
  if (!facts_ready(facts)) {
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
  ixs_session_unbind(&binding);
  return status;
}

typedef struct {
  ixs_node *node;
  uint32_t next_child;
  ixs_check_result result;
  bool started;
} predicate_query_frame;

typedef struct {
  ixs_bounds *bounds;
  ixs_query_walk walk;
  ixs_query_node_memo memo;
  ixs_check_result answer;
} predicate_query;

static ixs_check_result check_result_not(ixs_check_result result) {
  if (result == IXS_CHECK_TRUE)
    return IXS_CHECK_FALSE;
  if (result == IXS_CHECK_FALSE)
    return IXS_CHECK_TRUE;
  return IXS_CHECK_UNKNOWN;
}

static ixs_check_result predicate_query_cmp_atom(ixs_bounds *bounds,
                                                 ixs_node *node) {
  ixs_check_result result;

  /* A reflexive equality is the public predicate encoding for totality.
   * Do not send it through arithmetic simplification: a fact-proven domain
   * failure is a FALSE proof, not an invalid query or a diagnostic. */
  if (node->u.binary.cmp_op == IXS_CMP_EQ &&
      node->u.binary.lhs == node->u.binary.rhs)
    return ixs_bounds_check_defined(bounds, node->u.binary.lhs);
  result = ixs_bounds_check_query(bounds, node);
  if (result != IXS_CHECK_UNKNOWN || !ixs_node_is_zero(node->u.binary.rhs) ||
      !bounds_store_contains_nonzero(bounds, node->u.binary.lhs))
    return result;
  if (node->u.binary.cmp_op == IXS_CMP_NE)
    return IXS_CHECK_TRUE;
  if (node->u.binary.cmp_op == IXS_CMP_EQ)
    return IXS_CHECK_FALSE;
  return result;
}

static ixs_check_result predicate_query_atom(ixs_bounds *bounds,
                                             ixs_node *node) {
  ixs_interval iv;
  int lo_cmp;
  int hi_cmp;
  if (!node)
    return IXS_CHECK_UNKNOWN;
  if (node->tag == IXS_INT)
    return node->u.ival == 0 ? IXS_CHECK_FALSE : IXS_CHECK_TRUE;
  if (node->tag == IXS_RAT)
    return node->u.rat.p == 0 ? IXS_CHECK_FALSE : IXS_CHECK_TRUE;
  if (node->tag == IXS_CMP)
    return predicate_query_cmp_atom(bounds, node);

  /* NOT accepts numeric operands.  Interval truthiness is a bounded
   * sufficient proof for those operands; a range crossing zero is unknown. */
  iv = ixs_bounds_get(bounds, node);
  if (!iv.valid || ixs_interval_is_empty(iv))
    return IXS_CHECK_UNKNOWN;
  lo_cmp = iv.lo_inf ? -1 : ixs_rat_cmp(iv.lo_p, iv.lo_q, 0, 1);
  hi_cmp = iv.hi_inf ? 1 : ixs_rat_cmp(iv.hi_p, iv.hi_q, 0, 1);
  if (!iv.lo_inf && !iv.hi_inf && lo_cmp == 0 && hi_cmp == 0)
    return IXS_CHECK_FALSE;
  if ((!iv.lo_inf && lo_cmp > 0) || (!iv.hi_inf && hi_cmp < 0))
    return IXS_CHECK_TRUE;
  return IXS_CHECK_UNKNOWN;
}

static void predicate_query_fold(predicate_query_frame *parent,
                                 ixs_check_result child) {
  if (parent->node->tag == IXS_NOT) {
    parent->result = check_result_not(child);
    return;
  }
  if (parent->node->tag == IXS_AND) {
    if (child == IXS_CHECK_FALSE)
      parent->result = IXS_CHECK_FALSE;
    else if (child == IXS_CHECK_UNKNOWN && parent->result == IXS_CHECK_TRUE)
      parent->result = IXS_CHECK_UNKNOWN;
    return;
  }
  if (parent->node->tag == IXS_OR) {
    if (child == IXS_CHECK_TRUE)
      parent->result = IXS_CHECK_TRUE;
    else if (child == IXS_CHECK_UNKNOWN && parent->result == IXS_CHECK_FALSE)
      parent->result = IXS_CHECK_UNKNOWN;
  }
}

static bool
predicate_query_short_circuited(const predicate_query_frame *frame) {
  return (frame->node->tag == IXS_AND && frame->result == IXS_CHECK_FALSE) ||
         (frame->node->tag == IXS_OR && frame->result == IXS_CHECK_TRUE);
}

/* An absorber determines a total result only when every retained operand is
 * defined and integer-valued. */
static bool predicate_query_assoc_domain_proven(ixs_bounds *bounds,
                                                ixs_node *node) {
  return ixs_bounds_check_defined(bounds, node) == IXS_CHECK_TRUE &&
         ixs_bounds_check_integer_valued(bounds, node) == IXS_CHECK_TRUE;
}

static void predicate_query_start(predicate_query_frame *frame) {
  if (frame->started)
    return;
  frame->started = true;
  if (frame->node && frame->node->tag == IXS_AND)
    frame->result = IXS_CHECK_TRUE;
  else if (frame->node && frame->node->tag == IXS_OR)
    frame->result = IXS_CHECK_FALSE;
  else
    frame->result = IXS_CHECK_UNKNOWN;
}

static ixs_node *predicate_query_next_child(predicate_query_frame *frame) {
  ixs_node *node = frame->node;

  if (node && (node->tag == IXS_AND || node->tag == IXS_OR) &&
      !predicate_query_short_circuited(frame) &&
      frame->next_child < node->u.assoc.nargs)
    return node->u.assoc.args[frame->next_child++];
  if (node && node->tag == IXS_NOT && frame->next_child == 0) {
    frame->next_child = 1;
    return node->u.unary_bool.arg;
  }
  return NULL;
}

static ixs_check_result
predicate_query_complete(ixs_bounds *bounds,
                         const predicate_query_frame *frame) {
  ixs_node *node = frame->node;
  ixs_check_result result;

  if (!node ||
      (node->tag != IXS_AND && node->tag != IXS_OR && node->tag != IXS_NOT))
    return predicate_query_atom(bounds, node);

  result = frame->result;
  if (predicate_query_short_circuited(frame) &&
      !predicate_query_assoc_domain_proven(bounds, node))
    result = IXS_CHECK_UNKNOWN;
  return result;
}

/* hot */
static ixs_query_walk_step predicate_query_advance(void *state, void *top) {
  predicate_query *query = state;
  predicate_query_frame *frame = top;
  bounds_check_memo_entry *entry;
  ixs_node *child;
  ixs_check_result completed;
  predicate_query_start(frame);
  child = predicate_query_next_child(frame);
  if (child) {
    entry = ixs_query_node_memo_get(&query->memo, child, true);
    if (!entry) {
      query->bounds->oom = true;
      return IXS_QUERY_WALK_OOM;
    }
    if (entry->active) {
      bounds_query_note_invalid(query->bounds);
      return IXS_QUERY_WALK_STOP;
    }
    if (entry->complete) {
      predicate_query_fold(frame, entry->result);
      return IXS_QUERY_WALK_ADVANCED;
    }
    if (ixs_query_walk_push(&query->walk, child) != IXS_QUERY_WALK_ADVANCED)
      return IXS_QUERY_WALK_OOM;
    entry->active = true;
    return IXS_QUERY_WALK_ADVANCED;
  }
  completed = predicate_query_complete(query->bounds, frame);
  entry = ixs_query_node_memo_get(&query->memo, frame->node, false);
  if (!entry || !entry->active) {
    bounds_query_note_invalid(query->bounds);
    return IXS_QUERY_WALK_STOP;
  }
  entry->active = false;
  entry->complete = true;
  entry->result = completed;
  IXS_QUERY_WALK_POP(&query->walk);
  if (query->walk.depth == 0)
    query->answer = completed;
  else
    predicate_query_fold(IXS_QUERY_WALK_TOP(&query->walk), completed);
  return IXS_QUERY_WALK_ADVANCED;
}

static ixs_check_result predicate_query_eval_detail(ixs_bounds *bounds,
                                                    ixs_node *predicate,
                                                    bool *limited) {
  ixs_arena *arena;
  ixs_arena_mark mark;
  predicate_query query;
  bounds_check_memo_entry *entry;
  ixs_query_walk_step step;

  if (limited)
    *limited = false;
  if (!bounds || !predicate)
    return IXS_CHECK_UNKNOWN;
  arena = &bounds->query_arena;
  mark = ixs_arena_save(arena);
  query.bounds = bounds;
  query.answer = IXS_CHECK_UNKNOWN;
  IXS_QUERY_NODE_MEMO_INIT(&query.memo, arena, bounds_check_memo_entry, node);
  IXS_QUERY_WALK_INIT_CAP(&query.walk, arena, &bounds->oom,
                          predicate_query_frame, node, 32u);
  entry = ixs_query_node_memo_get(&query.memo, predicate, true);
  if (!entry) {
    bounds->oom = true;
    ixs_arena_restore(arena, mark);
    return IXS_CHECK_UNKNOWN;
  }
  step = ixs_query_walk_push(&query.walk, predicate);
  if (step != IXS_QUERY_WALK_ADVANCED) {
    ixs_arena_restore(arena, mark);
    return IXS_CHECK_UNKNOWN;
  }
  entry->active = true;
  step =
      ixs_query_walk_drive(&query.walk, &query, predicate_query_advance, NULL);
  ixs_arena_restore(arena, mark);
  return step != IXS_QUERY_WALK_ADVANCED || bounds->oom ? IXS_CHECK_UNKNOWN
                                                        : query.answer;
}

/* Check B under a query-local A assumption.  The fork borrows the enclosing
 * query state, so a limit or transport failure invalidates the whole proof. */
static ixs_check_result predicate_query_implication_branch(ixs_bounds *bounds,
                                                           ixs_node *antecedent,
                                                           ixs_node *consequent,
                                                           bool *limited) {
  ixs_ctx *ctx;
  ixs_node *predicate_array[1];
  ixs_bounds branch;
  ixs_bounds_build_status status;
  ixs_arena_mark scratch_mark;
  ixs_arena_mark diag_mark;
  const char **saved_errors;
  size_t saved_nerrors;
  size_t saved_errors_cap;
  ixs_bounds_transport_snapshot transport;
  bool branch_ready = false;
  bool branch_limited = false;
  ixs_check_result result = IXS_CHECK_UNKNOWN;

  if (!bounds || !antecedent || !consequent ||
      (antecedent->tag != IXS_AND && antecedent->tag != IXS_CMP))
    return IXS_CHECK_UNKNOWN;

  ctx = bounds->ctx;
  transport = ixs_bounds_query_transport_snapshot(bounds);
  scratch_mark = ixs_arena_save(bounds->scratch);
  if (!ixs_bounds_fork(&branch, bounds)) {
    bounds->oom = true;
    goto cleanup;
  }
  branch_ready = true;
  predicate_array[0] = antecedent;

  /* Unsupported local assumptions are proof misses.  Their diagnostics and
   * closure are private to this branch. */
  diag_mark = ixs_arena_save(&ctx->diag);
  saved_errors = ctx->errors;
  saved_nerrors = ctx->nerrors;
  saved_errors_cap = ctx->errors_cap;
  status = bounds_assume_validate_predicate(&branch, antecedent);
  if (status == IXS_BOUNDS_BUILD_OK)
    status =
        facts_ingest_predicate_closure(ctx, &branch, predicate_array, 1u, NULL);
  ixs_arena_restore(&ctx->diag, diag_mark);
  ctx->errors = saved_errors;
  ctx->nerrors = saved_nerrors;
  ctx->errors_cap = saved_errors_cap;

  if (status == IXS_BOUNDS_BUILD_OOM || branch.oom) {
    bounds->oom = true;
    goto cleanup;
  }
  if (status == IXS_BOUNDS_BUILD_LIMIT) {
    bounds_query_note_limit(bounds);
    goto cleanup;
  }
  if (status != IXS_BOUNDS_BUILD_OK)
    goto cleanup;
  if (ixs_bounds_has_empty(&branch)) {
    result = IXS_CHECK_TRUE;
    goto cleanup;
  }
  result = predicate_query_eval_detail(&branch, consequent, &branch_limited);
  if (branch.oom) {
    bounds->oom = true;
    goto cleanup;
  }
  if (result != IXS_CHECK_TRUE)
    result = IXS_CHECK_UNKNOWN;

cleanup:
  if (branch_ready)
    ixs_bounds_destroy(&branch);
  ixs_arena_restore(bounds->scratch, scratch_mark);
  if (limited &&
      (branch_limited || bounds_query_limited_since(bounds, transport)))
    *limited = true;
  return bounds->oom ? IXS_CHECK_UNKNOWN : result;
}

/* A | B is !A => B.  Canonicalization folds NOT(CMP), so reconstruct the
 * complementary comparison when either disjunct is a comparison.  The total
 * source check preserves eager AND/OR semantics, and the branch evaluator
 * deliberately has no implication fallback of its own. */
static ixs_check_result predicate_query_implication(ixs_bounds *bounds,
                                                    ixs_node *predicate,
                                                    bool *limited) {
  unsigned pass;
  uint32_t i;

  if (!bounds || !predicate || predicate->tag != IXS_OR ||
      predicate->u.assoc.nargs != 2u ||
      !predicate_query_assoc_domain_proven(bounds, predicate))
    return IXS_CHECK_UNKNOWN;

  /* Retain explicit NOT intent before deriving a comparison complement. */
  for (pass = 0u; pass < 2u; pass++) {
    for (i = 0u; i < 2u; i++) {
      ixs_node *disjunct = predicate->u.assoc.args[i];
      ixs_node *antecedent;
      bool branch_limited = false;
      ixs_check_result result;

      if (pass == 0u && disjunct->tag == IXS_NOT) {
        antecedent = disjunct->u.unary_bool.arg;
      } else if (pass == 1u && disjunct->tag == IXS_CMP) {
        antecedent = simp_not(bounds->ctx, disjunct);
        if (!antecedent) {
          bounds->oom = true;
          return IXS_CHECK_UNKNOWN;
        }
      } else {
        continue;
      }
      result = predicate_query_implication_branch(
          bounds, antecedent, predicate->u.assoc.args[1u - i], &branch_limited);
      if (branch_limited) {
        if (limited)
          *limited = true;
        return IXS_CHECK_UNKNOWN;
      }
      if (result == IXS_CHECK_TRUE || bounds->oom)
        return result;
    }
  }
  return IXS_CHECK_UNKNOWN;
}

/* General predicate fallback budget: inspect at most 4096 expression nodes
 * and enumerate at most 64 points across at most 8 finite-range symbols. */
#define PREDICATE_FINITE_MAX_SYMBOLS 8u
#define PREDICATE_FINITE_MAX_POINTS 64u
#define PREDICATE_FINITE_MAX_NODES 4096u

typedef struct {
  ixs_node *node;
  int64_t lower;
  int64_t upper;
  int64_t current;
} predicate_finite_symbol;

static bool predicate_finite_collect_symbols(ixs_bounds *bounds,
                                             ixs_node *predicate,
                                             predicate_finite_symbol *symbols,
                                             size_t *symbol_count) {
  ixs_arena *arena = &bounds->query_arena;
  ixs_arena_mark mark = ixs_arena_save(arena);
  query_node_set visited;
  ixs_node **stack = NULL;
  size_t stack_count = 0;
  size_t stack_capacity = 0;
  size_t visited_count = 0;
  bool collected = false;

  memset(&visited, 0, sizeof(visited));
  if (!query_node_stack_push(arena, &stack, &stack_count, &stack_capacity,
                             predicate))
    goto oom;
  while (stack_count > 0) {
    ixs_node *node = stack[--stack_count];
    uint32_t child_count;
    uint32_t child;
    bool inserted;
    size_t symbol;

    if (!node || !query_node_set_insert(arena, &visited, node, &inserted))
      goto oom;
    if (!inserted)
      continue;
    if (++visited_count > PREDICATE_FINITE_MAX_NODES)
      goto cleanup;
    if (node->tag == IXS_SYM) {
      for (symbol = 0; symbol < *symbol_count; symbol++)
        if (symbols[symbol].node == node)
          break;
      if (symbol == *symbol_count) {
        if (*symbol_count == PREDICATE_FINITE_MAX_SYMBOLS)
          goto cleanup;
        memset(&symbols[*symbol_count], 0, sizeof(symbols[*symbol_count]));
        symbols[(*symbol_count)++].node = node;
      }
    }
    child_count = ixs_node_nchildren(node);
    for (child = 0; child < child_count; child++)
      if (!query_node_stack_push(arena, &stack, &stack_count, &stack_capacity,
                                 ixs_node_child(node, child)))
        goto oom;
  }
  collected = true;

cleanup:
  ixs_arena_restore(arena, mark);
  return collected;

oom:
  bounds->oom = true;
  goto cleanup;
}

static bool predicate_finite_prepare_domain(ixs_bounds *bounds,
                                            predicate_finite_symbol *symbols,
                                            size_t symbol_count,
                                            ixs_node **targets,
                                            size_t *point_count) {
  size_t symbol;

  *point_count = 1;
  for (symbol = 0; symbol < symbol_count; symbol++) {
    ixs_interval range = ixs_bounds_get(bounds, symbols[symbol].node);
    uint64_t span;
    size_t width;
    if (!range.valid || range.lo_inf || range.hi_inf || range.lo_q <= 0 ||
        range.hi_q <= 0)
      return false;
    symbols[symbol].lower = ixs_rat_ceil(range.lo_p, range.lo_q);
    symbols[symbol].upper = ixs_rat_floor(range.hi_p, range.hi_q);
    if (symbols[symbol].lower > symbols[symbol].upper)
      return false;
    span = (uint64_t)symbols[symbol].upper - (uint64_t)symbols[symbol].lower;
    if (span >= PREDICATE_FINITE_MAX_POINTS)
      return false;
    width = (size_t)span + 1u;
    if (*point_count > PREDICATE_FINITE_MAX_POINTS / width)
      return false;
    *point_count *= width;
    symbols[symbol].current = symbols[symbol].lower;
    targets[symbol] = symbols[symbol].node;
  }
  return true;
}

static ixs_check_result
predicate_finite_evaluate(ixs_bounds *bounds, ixs_node *predicate,
                          predicate_finite_symbol *symbols, size_t symbol_count,
                          ixs_node **targets, size_t point_count) {
  ixs_ctx *ctx = bounds->ctx;
  ixs_arena_mark diag_mark = ixs_arena_save(&ctx->diag);
  const char **saved_errors = ctx->errors;
  size_t saved_nerrors = ctx->nerrors;
  size_t saved_errors_cap = ctx->errors_cap;
  ixs_node *replacements[PREDICATE_FINITE_MAX_SYMBOLS];
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  size_t point;

  for (point = 0; point < point_count; point++) {
    ixs_node *evaluated;
    ixs_check_result current;
    size_t symbol;
    for (symbol = 0; symbol < symbol_count; symbol++) {
      replacements[symbol] = ixs_node_int(ctx, symbols[symbol].current);
      if (!replacements[symbol]) {
        bounds->oom = true;
        break;
      }
    }
    if (bounds->oom)
      break;
    evaluated = simp_subs_multi(ctx, predicate, (uint32_t)symbol_count, targets,
                                replacements);
    if (!evaluated || ixs_node_is_sentinel(evaluated)) {
      result = IXS_CHECK_UNKNOWN;
      if (!evaluated)
        bounds->oom = true;
      break;
    }
    if (ixs_node_is_known_true(evaluated))
      current = IXS_CHECK_TRUE;
    else if (ixs_node_is_known_false(evaluated))
      current = IXS_CHECK_FALSE;
    else {
      result = IXS_CHECK_UNKNOWN;
      break;
    }
    if (point == 0)
      result = current;
    else if (result != current) {
      result = IXS_CHECK_UNKNOWN;
      break;
    }

    for (symbol = symbol_count; symbol > 0; symbol--) {
      predicate_finite_symbol *entry = &symbols[symbol - 1u];
      if (entry->current < entry->upper) {
        entry->current++;
        break;
      }
      entry->current = entry->lower;
    }
  }
  ixs_arena_restore(&ctx->diag, diag_mark);
  ctx->errors = saved_errors;
  ctx->nerrors = saved_nerrors;
  ctx->errors_cap = saved_errors_cap;
  return bounds->oom ? IXS_CHECK_UNKNOWN : result;
}

static ixs_check_result
predicate_query_bounded_finite_domain(ixs_bounds *bounds, ixs_node *predicate) {
  predicate_finite_symbol symbols[PREDICATE_FINITE_MAX_SYMBOLS];
  ixs_node *targets[PREDICATE_FINITE_MAX_SYMBOLS];
  size_t symbol_count = 0;
  size_t point_count;

  if (!predicate_finite_collect_symbols(bounds, predicate, symbols,
                                        &symbol_count) ||
      symbol_count == 0 ||
      !predicate_finite_prepare_domain(bounds, symbols, symbol_count, targets,
                                       &point_count))
    return IXS_CHECK_UNKNOWN;

  return predicate_finite_evaluate(bounds, predicate, symbols, symbol_count,
                                   targets, point_count);
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

static uint64_t bounds_scale_stride(uint64_t stride, int64_t coefficient) {
  uint64_t magnitude = ixs_int64_magnitude(coefficient);
  if (stride == 0 || magnitude == 0)
    return 0;
  if (magnitude <= (uint64_t)INT64_MAX / stride)
    return magnitude * stride;
  return stride;
}

typedef enum {
  BOUNDS_STRIDE_INITIAL,
  BOUNDS_STRIDE_ADD,
  BOUNDS_STRIDE_LINEAR_MUL,
  BOUNDS_STRIDE_MOD,
  BOUNDS_STRIDE_PIECEWISE
} bounds_stride_stage;

typedef struct {
  ixs_node *expr;
  bounds_query_scope scope;
  uint64_t result;
  uint32_t index;
  bounds_stride_stage stage;
  bool tracked;
} bounds_stride_frame;

typedef struct {
  ixs_bounds *bounds;
  ixs_query_walk walk;
  bool child_success;
  uint64_t child_stride;
} bounds_stride_query;

static ixs_query_walk_step bounds_stride_complete(bounds_stride_query *query,
                                                  bool success,
                                                  uint64_t stride) {
  bounds_stride_frame *frame = IXS_QUERY_WALK_TOP(&query->walk);
  if (frame->tracked) {
    bounds_query_cache_entry *entry =
        bounds_query_finish(&frame->scope, success);
    if (entry->outcome == BOUNDS_QUERY_OUTCOME_VALUE)
      entry->result.stride = stride;
    else
      success = false;
  }
  IXS_QUERY_WALK_POP(&query->walk);
  query->child_success = success;
  query->child_stride = success ? stride : 0;
  return IXS_QUERY_WALK_ADVANCED;
}

/* hot */
static void bounds_stride_abort(void *state, void *raw_frame) {
  bounds_stride_frame *frame = raw_frame;
  (void)state;
  if (frame->tracked)
    (void)bounds_query_finish(&frame->scope, false);
}

static ixs_query_walk_step
bounds_stride_prepare_frame(bounds_stride_query *query,
                            bounds_stride_frame *frame) {
  ixs_node *node = frame->expr;
  if (!node || (node->properties & IXS_NODE_PROPERTY_VALID) == 0)
    return bounds_stride_complete(query, false, 0);
  if (bounds_query_should_track(query->bounds, node)) {
    bounds_query_cache_entry *cached = NULL;
    bounds_query_enter_result enter = bounds_query_begin(
        query->bounds, BOUNDS_QUERY_STRIDE, node, 0, &frame->scope, &cached);
    if (enter == BOUNDS_QUERY_ENTER_CACHED) {
      return bounds_stride_complete(query, cached->success,
                                    cached->result.stride);
    }
    if (enter != BOUNDS_QUERY_ENTER_STARTED) {
      return bounds_stride_complete(query, false, 0);
    }
    frame->tracked = true;
  }
  return IXS_QUERY_WALK_NEXT;
}

static ixs_query_walk_step bounds_stride_start_add(bounds_stride_query *query,
                                                   bounds_stride_frame *frame) {
  ixs_node *node = frame->expr;
  int64_t p;
  int64_t q;
  ixs_node_get_rat(node->u.add.coeff, &p, &q);
  (void)p;
  if (q != 1) {
    return bounds_stride_complete(query, false, 0);
  }
  frame->stage = BOUNDS_STRIDE_ADD;
  frame->result = 0;
  frame->index = 0;
  if (node->u.add.nterms == 0) {
    return bounds_stride_complete(query, true, 0);
  }
  return ixs_query_walk_push(&query->walk, node->u.add.terms[0].term);
}

static ixs_query_walk_step bounds_stride_start_mul(bounds_stride_query *query,
                                                   bounds_stride_frame *frame) {
  ixs_node *node = frame->expr;
  int64_t p;
  int64_t q;
  uint32_t i;
  ixs_node_get_rat(node->u.mul.coeff, &p, &q);
  if (q != 1) {
    return bounds_stride_complete(query, false, 0);
  }
  if (p == 0) {
    return bounds_stride_complete(query, true, 0);
  }
  if (node->u.mul.nfactors == 1 && node->u.mul.factors[0].exp == 1) {
    frame->stage = BOUNDS_STRIDE_LINEAR_MUL;
    return ixs_query_walk_push(&query->walk, node->u.mul.factors[0].base);
  }
  for (i = 0; i < node->u.mul.nfactors; i++)
    if (node->u.mul.factors[i].exp <= 0 ||
        !ixs_node_is_integer_valued(node->u.mul.factors[i].base))
      break;
  if (i != node->u.mul.nfactors) {
    return bounds_stride_complete(query, true, 1);
  } else {
    uint64_t magnitude = ixs_int64_magnitude(p);
    return bounds_stride_complete(
        query, true, magnitude <= (uint64_t)INT64_MAX ? magnitude : 1);
  }
}

static ixs_query_walk_step
bounds_stride_start_piecewise(bounds_stride_query *query,
                              bounds_stride_frame *frame) {
  ixs_node *node = frame->expr;
  if (!ixs_node_is_integer_valued(node) || !ixs_node_is_known_total(node) ||
      node->u.pw.ncases == 0 || !node->u.pw.cases)
    return bounds_stride_complete(query, false, 0);
  frame->stage = BOUNDS_STRIDE_PIECEWISE;
  frame->result = 0;
  frame->index = 0;
  return ixs_query_walk_push(&query->walk, node->u.pw.cases[0].value);
}

static ixs_query_walk_step
bounds_stride_start_frame(bounds_stride_query *query,
                          bounds_stride_frame *frame) {
  ixs_node *node = frame->expr;
  switch (node->tag) {
  case IXS_INT:
    return bounds_stride_complete(query, true, 0);
  case IXS_RAT:
    return bounds_stride_complete(query, node->u.rat.q == 1, 0);
  case IXS_SYM: {
    int64_t modulus;
    int64_t remainder;
    uint64_t result = 1;
    if (bounds_store_get_modrem(query->bounds, node->u.name, &modulus,
                                &remainder)) {
      (void)remainder;
      result = (uint64_t)modulus;
    }
    return bounds_stride_complete(query, !query->bounds->oom, result);
  }
  case IXS_ADD:
    return bounds_stride_start_add(query, frame);
  case IXS_MUL:
    return bounds_stride_start_mul(query, frame);
  case IXS_MOD:
    if (node->u.binary.rhs->tag != IXS_INT || node->u.binary.rhs->u.ival <= 0) {
      return bounds_stride_complete(query, true, 1);
    }
    frame->stage = BOUNDS_STRIDE_MOD;
    return ixs_query_walk_push(&query->walk, node->u.binary.lhs);
  case IXS_PIECEWISE:
    return bounds_stride_start_piecewise(query, frame);
  default:
    return bounds_stride_complete(query, ixs_node_is_integer_valued(node), 1);
  }
}

static ixs_query_walk_step
bounds_stride_resume_frame(bounds_stride_query *query,
                           bounds_stride_frame *frame) {
  ixs_node *node = frame->expr;
  if (!query->child_success) {
    return bounds_stride_complete(query, false, 0);
  }
  switch (frame->stage) {
  case BOUNDS_STRIDE_ADD: {
    int64_t p;
    int64_t q;
    ixs_node_get_rat(node->u.add.terms[frame->index].coeff, &p, &q);
    if (q != 1) {
      return bounds_stride_complete(query, false, 0);
    }
    frame->result =
        ixs_u64_gcd(frame->result, bounds_scale_stride(query->child_stride, p));
    frame->index++;
    if (frame->index == node->u.add.nterms) {
      return bounds_stride_complete(query, true, frame->result);
    }
    return ixs_query_walk_push(&query->walk,
                               node->u.add.terms[frame->index].term);
  }
  case BOUNDS_STRIDE_LINEAR_MUL: {
    int64_t p;
    int64_t q;
    ixs_node_get_rat(node->u.mul.coeff, &p, &q);
    (void)q;
    return bounds_stride_complete(query, true,
                                  bounds_scale_stride(query->child_stride, p));
  }
  case BOUNDS_STRIDE_MOD:
    return bounds_stride_complete(
        query, true,
        ixs_u64_gcd(query->child_stride, (uint64_t)node->u.binary.rhs->u.ival));
  case BOUNDS_STRIDE_PIECEWISE:
    frame->result = ixs_u64_gcd(frame->result, query->child_stride);
    frame->index++;
    if (frame->index == node->u.pw.ncases) {
      return bounds_stride_complete(query, true, frame->result);
    }
    return ixs_query_walk_push(&query->walk,
                               node->u.pw.cases[frame->index].value);
  case BOUNDS_STRIDE_INITIAL:
    return bounds_stride_complete(query, false, 0);
  }
  return IXS_QUERY_WALK_ADVANCED;
}

/* Iterative and memoized over the normalized expression DAG.  Each node and
 * immediate operand is processed once per query owner; there is no semantic
 * depth or visit ceiling and deep Piecewise trees do not consume C stack. */
/* hot */
static ixs_query_walk_step bounds_stride_advance(void *state, void *raw_frame) {
  bounds_stride_query *query = state;
  bounds_stride_frame *frame = raw_frame;
  ixs_query_walk_step step;
  if (frame->stage == BOUNDS_STRIDE_INITIAL) {
    step = bounds_stride_prepare_frame(query, frame);
    if (step == IXS_QUERY_WALK_NEXT)
      step = bounds_stride_start_frame(query, frame);
  } else {
    step = bounds_stride_resume_frame(query, frame);
  }
  return step;
}

static bool bounds_known_stride(ixs_bounds *bounds, ixs_node *expr,
                                uint64_t *stride) {
  bounds_stride_query query;
  if (!bounds || !expr || !stride || bounds->oom)
    return false;
  memset(&query, 0, sizeof(query));
  query.bounds = bounds;
  IXS_QUERY_WALK_INIT(&query.walk, bounds->scratch, &bounds->oom,
                      bounds_stride_frame, expr);
  if (!ixs_query_walk_run(&query.walk, expr, &query, bounds_stride_advance,
                          bounds_stride_abort))
    return false;
  if (!query.child_success)
    return false;
  *stride = query.child_stride;
  return true;
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

static bool bounds_refine_integral_interval(ixs_bounds *bounds, ixs_node *expr,
                                            bool expression_defined,
                                            ixs_interval *interval) {
  ixs_interval truncating_remainder;
  ixs_algebra_status truncating_status;
  uint64_t stride;
  uint64_t residue;
  int64_t aligned;
  bool lower_overflow = false;
  bool upper_overflow = false;

  truncating_status = bounds_get_truncating_remainder_range(
      bounds, expr, expression_defined, &truncating_remainder);
  if (truncating_status == IXS_ALGEBRA_MATCH)
    *interval = iv_intersect(*interval, truncating_remainder);
  else
    bounds_note_truncating_range_status(bounds, truncating_status);
  if (bounds->oom || !interval->valid || ixs_interval_is_empty(*interval))
    return false;
  if (!interval->lo_inf) {
    interval->lo_p = ixs_rat_ceil(interval->lo_p, interval->lo_q);
    interval->lo_q = 1;
  }
  if (!interval->hi_inf) {
    interval->hi_p = ixs_rat_floor(interval->hi_p, interval->hi_q);
    interval->hi_q = 1;
  }
  if (ixs_interval_is_empty(*interval))
    return false;
  if (!bounds_known_stride(bounds, expr, &stride) || stride <= 1u ||
      stride > (uint64_t)INT64_MAX)
    return !bounds->oom;
  if (!bounds_known_residue(bounds, expr, stride, &residue))
    return !bounds->oom;
  if (!interval->lo_inf) {
    if (ixs_integer_align_congruence_up(interval->lo_p, (int64_t)stride,
                                        (int64_t)residue, &aligned))
      interval->lo_p = aligned;
    else
      lower_overflow = true;
  }
  if (!interval->hi_inf) {
    if (ixs_integer_align_congruence_down(interval->hi_p, (int64_t)stride,
                                          (int64_t)residue, &aligned))
      interval->hi_p = aligned;
    else
      upper_overflow = true;
  }

  /* A one-sided interval can retain its untightened representable endpoint.
   * With an opposite finite side, overflow proves no value can remain. */
  if ((lower_overflow && !interval->hi_inf) ||
      (upper_overflow && !interval->lo_inf))
    return false;
  return !ixs_interval_is_empty(*interval);
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
  if (bounds_exact_integer_difference(query->bounds, difference, &delta)) {
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
  if (bounds_check_defined_detail(query->bounds, frame->lhs, &lhs_oom,
                                  &lhs_limited) != IXS_CHECK_TRUE ||
      bounds_check_defined_detail(query->bounds, frame->rhs, &rhs_oom,
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

static ixs_algebra_status bounds_get_truncating_remainder_range(
    ixs_bounds *b, ixs_node *expr, bool expression_defined, ixs_interval *out) {
  if (!b->ctx)
    return IXS_ALGEBRA_NO_MATCH;
  ixs_division_range_result result =
      ixs_division_algebra_range(b->ctx, b, expr, expr, expression_defined);
  if (result.status == IXS_ALGEBRA_MATCH)
    *out = result.range;
  return result.status;
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
  lhs_truth = predicate_query_eval_detail(state->bounds, lhs, &lhs_limited);
  rhs_truth = predicate_query_eval_detail(state->bounds, rhs, &rhs_limited);
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
  if (bounds_check_defined_detail(state->bounds, substituted_value, &value_oom,
                                  &value_limited) != IXS_CHECK_TRUE ||
      bounds_check_defined_detail(state->bounds, substituted_other, &other_oom,
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
  if (bounds_check_defined_detail(bounds, lhs, &lhs_oom, &lhs_limited) !=
          IXS_CHECK_TRUE ||
      bounds_check_defined_detail(bounds, rhs, &rhs_oom, &rhs_limited) !=
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
                                            : check_result_not(equivalent);
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
  if (bounds_check_defined_detail(bounds, lhs, &lhs_oom, &lhs_limited) !=
          IXS_CHECK_TRUE ||
      bounds_check_defined_detail(bounds, rhs, &rhs_oom, &rhs_limited) !=
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
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "predicate");
  if (!facts_ready(facts)) {
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
  result.check = predicate_query_eval_detail(&facts->bounds, predicate,
                                             &predicate_limited);
  if (!predicate_limited && result.check == IXS_CHECK_UNKNOWN)
    result.check = predicate_query_implication(&facts->bounds, predicate,
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
    result.check = predicate_query_eval_detail(&facts->bounds, simplified,
                                               &predicate_limited);
    if (!predicate_limited && result.check == IXS_CHECK_UNKNOWN)
      result.check =
          predicate_query_bounded_finite_domain(&facts->bounds, predicate);
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
  ixs_session_unbind(&binding);
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
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "equivalence");
  if (!facts_ready(facts)) {
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
  ixs_session_unbind(&binding);
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
  if (!facts_bind(facts, &scope->binding, &scope->ctx))
    return false;
  scope->facts = facts;
  scope->bound = true;
  facts_read_query_begin(&scope->read_scope, &facts->bounds, scope->ctx, query);
  if (!facts_ready(facts)) {
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
  ixs_session_unbind(&scope->binding);
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
    ixs_session_unbind(&scope->binding);
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
      bounds_check_defined_detail(&scope->facts->bounds, expr, &oom, &limited);
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
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx,
                         "constant difference");
  if (!facts_ready(facts)) {
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
  ixs_session_unbind(&binding);
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
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "check");
  if (!facts_ready(facts)) {
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
  ixs_session_unbind(&binding);
  return result;
}

static ixs_fact_check_result facts_query_check_integer_valued(ixs_facts *facts,
                                                              ixs_node *expr) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  bool query_held = false;
  ixs_fact_check_result result = {IXS_FACT_QUERY_INVALID, IXS_CHECK_UNKNOWN};
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "integer valued");
  if (!facts_ready(facts)) {
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
  ixs_session_unbind(&binding);
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
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "defined");
  if (!facts_ready(facts)) {
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
      bounds_check_defined_detail(&facts->bounds, expr, &oom, &limited);
  result.status = oom       ? IXS_FACT_QUERY_OOM
                  : limited ? IXS_FACT_QUERY_LIMITED
                            : IXS_FACT_QUERY_COMPLETE;

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.check = IXS_CHECK_UNKNOWN;
  ixs_session_unbind(&binding);
  return result;
}

static ixs_fact_check_result
facts_query_check_divisible(ixs_facts *facts, ixs_node *expr, int64_t modulus) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  bool query_held = false;
  ixs_fact_check_result result = {IXS_FACT_QUERY_INVALID, IXS_CHECK_UNKNOWN};
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "divisibility");
  if (!facts_ready(facts)) {
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
  ixs_session_unbind(&binding);
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
  if (!facts_ready(facts)) {
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
  defined = bounds_check_defined_detail(&facts->bounds, expr, &defined_oom,
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

  if (!facts_bind(facts, &binding, &ctx))
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
  ixs_session_unbind(&binding);
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
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "power of two");
  if (!facts_ready(facts)) {
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
  if (bounds_check_defined_detail(&facts->bounds, expr, &defined_oom,
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
  ixs_session_unbind(&binding);
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
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "known bits");
  if (!facts_ready(facts)) {
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

  if (bounds_check_defined_detail(&facts->bounds, expr, &defined_oom,
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
  ixs_session_unbind(&binding);
  return result;
}

static ixs_symbol_congruence_result
facts_query_get_symbol_congruence(ixs_facts *facts, ixs_node *symbol) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  ixs_symbol_congruence_result result = {IXS_FACT_QUERY_INVALID, false, 0, 0};
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "symbol congruence");
  if (!facts_ready(facts)) {
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
  ixs_session_unbind(&binding);
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
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "congruence");
  if (!facts_ready(facts)) {
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
  ixs_session_unbind(&binding);
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
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "range");
  if (!facts_ready(facts)) {
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
  if (bounds_check_defined_detail(&facts->bounds, expr, &defined_oom,
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
  ixs_session_unbind(&binding);
  return result;
}

static void facts_public_output_error(ixs_facts *facts, const char *query,
                                      const char *message) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  if (!facts_bind(facts, &binding, &ctx))
    return;
  ixs_ctx_push_error(ctx, "%s: %s", query, message);
  ixs_session_unbind(&binding);
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
