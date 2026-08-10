/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds_range.h"
#include "additive_row.h"
#include "bounds_bitfacts.h"
#include "bounds_difference.h"
#include "bounds_integer.h"
#include "bounds_query.h"
#include "bounds_relation.h"
#include "bounds_residue.h"
#include "bounds_store.h"
#include "bounds_stride.h"
#include "division_algebra.h"
#include "hash.h"
#include "query_walk.h"
#include "radix_algebra.h"
#include "rational.h"
#include "simplify.h"

#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>

#define BOUNDS_CACHE_CAP 32u

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

static bool bounds_cacheable_expr(ixs_node *expr) {
  return expr && expr->tag != IXS_INT && expr->tag != IXS_RAT &&
         expr->tag != IXS_SYM;
}

IXS_STATIC void bounds_range_init(ixs_bounds *b, bool allocate_cache) {
  b->cache = NULL;
  b->cache_cap = 0;
  b->range_pw_depth = 0;
  b->empty_cache_valid = false;
  b->empty_cache_value = false;
  b->interval_evaluating = false;
  if (!allocate_cache)
    return;
  b->cache = ixs_arena_alloc(b->scratch, BOUNDS_CACHE_CAP * sizeof(*b->cache),
                             sizeof(void *));
  if (!b->cache) {
    b->cache_cap = BOUNDS_CACHE_DISABLED;
    return;
  }
  b->cache_cap = BOUNDS_CACHE_CAP;
  memset(b->cache, 0, b->cache_cap * sizeof(*b->cache));
}

IXS_STATIC void bounds_range_inherit_fork(ixs_bounds *dst,
                                          const ixs_bounds *src) {
  dst->cache = NULL;
  dst->cache_cap = BOUNDS_CACHE_DISABLED;
  dst->range_pw_depth = src->range_pw_depth;
  dst->empty_cache_valid = false;
  dst->empty_cache_value = false;
  dst->interval_evaluating = false;
}

IXS_STATIC void bounds_range_invalidate_empty(ixs_bounds *b) {
  if (b)
    b->empty_cache_valid = false;
}

IXS_STATIC void bounds_range_invalidate_all(ixs_bounds *b) {
  bounds_range_invalidate_empty(b);
  if (b && b->cache && b->cache_cap != BOUNDS_CACHE_DISABLED)
    memset(b->cache, 0, b->cache_cap * sizeof(*b->cache));
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

IXS_STATIC ixs_algebra_status bounds_get_truncating_remainder_range(
    ixs_bounds *b, ixs_node *expr, bool expression_defined, ixs_interval *out);

IXS_STATIC void bounds_note_truncating_range_status(ixs_bounds *b,
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

    group = ixs_hash_ptr(representative) & (capacity - 1u);
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

IXS_STATIC ixs_node *
bounds_condition_assumption(ixs_bounds *b, ixs_node *cond, bool value,
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

IXS_STATIC ixs_check_result bounds_condition_truth(ixs_bounds *b,
                                                   ixs_node *cond) {
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
  if (remaining_ready)
    ixs_bounds_destroy(&remaining);
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

IXS_STATIC bool bounds_range_exact_integer_difference(ixs_bounds *b,
                                                      ixs_node *difference,
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

IXS_STATIC ixs_check_result bounds_range_check_relation(const ixs_interval *lhs,
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

IXS_STATIC ixs_check_result bounds_range_check_raw(ixs_bounds *b,
                                                   ixs_node *cmp) {
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
    return bounds_range_check_relation(&iv, &rhs_iv, cmp->u.binary.cmp_op);
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
    rhs_iv = ixs_interval_exact(0, 1);
    interval_result =
        bounds_range_check_relation(&iv, &rhs_iv, cmp->u.binary.cmp_op);
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
  result = bounds_range_check_raw(b, cmp);
  if (query_held)
    ixs_bounds_query_hold_end(b);
  return result;
}

IXS_STATIC ixs_algebra_status bounds_get_truncating_remainder_range(
    ixs_bounds *b, ixs_node *expr, bool expression_defined, ixs_interval *out) {
  ixs_division_range_result result;
  if (!b->ctx)
    return IXS_ALGEBRA_NO_MATCH;
  result =
      ixs_division_algebra_range(b->ctx, b, expr, expr, expression_defined);
  if (result.status == IXS_ALGEBRA_MATCH)
    *out = result.range;
  return result.status;
}

IXS_STATIC bool bounds_refine_integral_interval(ixs_bounds *bounds,
                                                ixs_node *expr,
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
