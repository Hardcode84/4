/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds_modular.h"
#include "bounds_bitfacts.h"
#include "bounds_defined.h"
#include "bounds_query.h"
#include "bounds_range.h"
#include "bounds_relation.h"
#include "bounds_residue.h"
#include "bounds_store.h"
#include "bounds_stride.h"
#include "division_algebra.h"
#include "expand.h"
#include "rational.h"
#include "simplify.h"
#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>

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

/* Evaluate a normalized affine row whose variable coefficients sum to zero.
 * Every term is then a weighted offset from one retained relation endpoint;
 * the anchor itself cancels. */
static ixs_algebra_status bounds_exact_additive_value(ixs_bounds *bounds,
                                                      ixs_node *expr,
                                                      int64_t *value) {
  ixs_node *anchor;
  int64_t result;
  int64_t denominator;
  int64_t coefficient_sum = 0;
  uint32_t i;
  if (expr->tag != IXS_ADD || expr->u.add.nterms == 0)
    return IXS_ALGEBRA_NO_MATCH;
  if (!ixs_node_is_const(expr->u.add.coeff))
    return IXS_ALGEBRA_NO_MATCH;
  ixs_node_get_rat(expr->u.add.coeff, &result, &denominator);
  if (denominator != 1)
    return IXS_ALGEBRA_NO_MATCH;
  anchor = expr->u.add.terms[0].term;
  for (i = 0; i < expr->u.add.nterms; i++) {
    int64_t coefficient;
    int64_t coefficient_denominator;
    int64_t delta;
    int64_t scaled;
    ixs_algebra_status status;
    if (!ixs_node_is_const(expr->u.add.terms[i].coeff))
      return IXS_ALGEBRA_NO_MATCH;
    ixs_node_get_rat(expr->u.add.terms[i].coeff, &coefficient,
                     &coefficient_denominator);
    if (coefficient_denominator != 1 ||
        !ixs_safe_add(coefficient_sum, coefficient, &coefficient_sum))
      return IXS_ALGEBRA_UNREPRESENTABLE;
    status = bounds_exact_relation_difference(bounds, expr->u.add.terms[i].term,
                                              anchor, &delta);
    if (status != IXS_ALGEBRA_MATCH)
      return status;
    if (!ixs_safe_mul(coefficient, delta, &scaled) ||
        !ixs_safe_add(result, scaled, &result))
      return IXS_ALGEBRA_UNREPRESENTABLE;
  }
  if (coefficient_sum != 0)
    return IXS_ALGEBRA_NO_MATCH;
  *value = result;
  return IXS_ALGEBRA_MATCH;
}

typedef struct {
  uint64_t magnitude;
  bool negative;
} bounds_wide_integer;

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
      (bounds_wide_integer){ixs_int64_magnitude(lhs), lhs < 0},
      (bounds_wide_integer){ixs_int64_magnitude(rhs), rhs > 0}, result);
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

/* With n == r (mod m) and m | d, every possible Mod(n,d) is r+k*m.
 * Bounding delta inside [-r,m-r) excludes both quotient boundaries. */
static bool bounds_modular_shift_window_stable(ixs_bounds *bounds,
                                               ixs_node *dividend,
                                               ixs_node *denominator,
                                               int64_t lower, int64_t upper) {
  uint64_t modulus;
  uint64_t residue;
  if (!bounds_known_stride(bounds, dividend, &modulus) || modulus <= 1u ||
      modulus > (uint64_t)INT64_MAX ||
      !bounds_known_residue(bounds, dividend, modulus, &residue) ||
      ixs_bounds_check_divisible(bounds, denominator, (int64_t)modulus) !=
          IXS_CHECK_TRUE)
    return false;
  return lower >= -(int64_t)residue && upper < (int64_t)(modulus - residue);
}

IXS_STATIC bool bounds_modular_quotient_shift_stable(ixs_bounds *bounds,
                                                     ixs_node *dividend,
                                                     ixs_node *denominator,
                                                     ixs_node *delta) {
  int64_t lower;
  int64_t upper;
  return bounds_integer_enclosure(bounds, delta, &lower, &upper) &&
         bounds_modular_shift_window_stable(bounds, dividend, denominator,
                                            lower, upper);
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
  bool normalized;
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
  difference = simp_sub(query->ctx, frame->lhs, frame->rhs);
  if (!query->normalized)
    difference = bounds_delta_simplify(query, difference);
  else if (!difference || ixs_node_is_sentinel(difference)) {
    if (!difference)
      query->bounds->oom = true;
    difference = NULL;
  }
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
        !bounds_modular_shift_window_stable(query->bounds, rhs_representative,
                                            denominator, query->child_delta,
                                            query->child_delta))
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
                                     bool allow_expand, bool normalized) {
  memset(query, 0, sizeof(*query));
  query->ctx = ctx;
  query->bounds = bounds;
  query->frames = initial_frame;
  query->capacity = 1u;
  query->normalized = normalized;
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

IXS_STATIC bool bounds_modular_exact_delta_detail(ixs_ctx *ctx,
                                                  ixs_bounds *bounds,
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
                                          lhs, rhs, allow_expand, false))
    return false;
  bounds_delta_query_run(&query);
  return bounds_delta_query_result(&query, delta, invalid, limited, oom);
}

static ixs_algebra_status bounds_exact_value_source_defined(ixs_bounds *bounds,
                                                            ixs_node *expr) {
  ixs_bounds_transport_snapshot snapshot =
      ixs_bounds_query_transport_snapshot(bounds);
  ixs_bounds_transport_status transport;
  bool defined_oom = false;
  bool defined_limited = false;
  if (bounds_defined_check_detail(bounds, expr, &defined_oom,
                                  &defined_limited) == IXS_CHECK_TRUE)
    return IXS_ALGEBRA_MATCH;
  transport = ixs_bounds_query_transport_since(bounds, snapshot);
  if (transport == IXS_BOUNDS_TRANSPORT_INVALID)
    return IXS_ALGEBRA_INVALID;
  if (defined_oom || transport == IXS_BOUNDS_TRANSPORT_OOM)
    return IXS_ALGEBRA_OOM;
  if (defined_limited || transport == IXS_BOUNDS_TRANSPORT_LIMITED)
    return IXS_ALGEBRA_LIMITED;
  return IXS_ALGEBRA_NO_MATCH;
}

static ixs_algebra_status
bounds_modular_current_transport(const ixs_bounds *bounds) {
  ixs_bounds_transport_status transport = bounds_query_state_transport(bounds);
  if (transport == IXS_BOUNDS_TRANSPORT_INVALID)
    return IXS_ALGEBRA_INVALID;
  if (transport == IXS_BOUNDS_TRANSPORT_OOM || bounds->oom)
    return IXS_ALGEBRA_OOM;
  if (transport == IXS_BOUNDS_TRANSPORT_LIMITED)
    return IXS_ALGEBRA_LIMITED;
  return IXS_ALGEBRA_NO_MATCH;
}

static ixs_algebra_status
bounds_modular_remainder_delta_equal(ixs_ctx *ctx, ixs_bounds *bounds,
                                     ixs_node *lhs, ixs_node *rhs,
                                     ixs_node *modulus) {
  ixs_node *difference;
  int64_t delta;
  bool invalid = false;
  bool limited = false;
  bool oom = false;
  if (bounds_modular_exact_delta_detail(ctx, bounds, lhs, rhs, false, &delta,
                                        &invalid, &limited, &oom)) {
    if (delta == 0 || (modulus->tag == IXS_INT && delta % modulus->u.ival == 0))
      return IXS_ALGEBRA_MATCH;
    return IXS_ALGEBRA_NO_MATCH;
  }
  if (invalid)
    return IXS_ALGEBRA_INVALID;
  if (oom)
    return IXS_ALGEBRA_OOM;
  if (limited)
    return IXS_ALGEBRA_LIMITED;
  if (modulus->tag != IXS_INT)
    return IXS_ALGEBRA_NO_MATCH;

  difference = simp_sub(ctx, lhs, rhs);
  if (!difference)
    return IXS_ALGEBRA_OOM;
  if (ixs_node_is_sentinel(difference))
    return IXS_ALGEBRA_INVALID;
  if (ixs_bounds_check_congruent(bounds, difference, modulus->u.ival, 0) ==
      IXS_CHECK_TRUE)
    return IXS_ALGEBRA_MATCH;
  return bounds_modular_current_transport(bounds);
}

IXS_STATIC ixs_algebra_status bounds_modular_remainders_equal(
    ixs_ctx *ctx, ixs_bounds *bounds, ixs_node *lhs, ixs_node *rhs) {
  ixs_node *modulus;
  ixs_interval modulus_range;
  ixs_algebra_status status;
  if (!ctx || !bounds || !lhs || !rhs || lhs->tag != IXS_MOD ||
      rhs->tag != IXS_MOD || lhs->u.binary.rhs != rhs->u.binary.rhs ||
      bounds->contradiction)
    return IXS_ALGEBRA_NO_MATCH;
  status = bounds_modular_current_transport(bounds);
  if (status != IXS_ALGEBRA_NO_MATCH)
    return status;
  status = bounds_exact_value_source_defined(bounds, lhs);
  if (status != IXS_ALGEBRA_MATCH)
    return status;
  status = bounds_exact_value_source_defined(bounds, rhs);
  if (status != IXS_ALGEBRA_MATCH)
    return status;

  modulus = lhs->u.binary.rhs;
  modulus_range = ixs_bounds_get(bounds, modulus);
  status = bounds_modular_current_transport(bounds);
  if (status != IXS_ALGEBRA_NO_MATCH)
    return status;
  if (!modulus_range.valid || modulus_range.lo_inf ||
      ixs_rat_cmp(modulus_range.lo_p, modulus_range.lo_q, 0, 1) <= 0)
    return IXS_ALGEBRA_NO_MATCH;
  return bounds_modular_remainder_delta_equal(ctx, bounds, lhs->u.binary.lhs,
                                              rhs->u.binary.lhs, modulus);
}

static ixs_algebra_status
bounds_exact_value_project_division(ixs_ctx *ctx, ixs_bounds *bounds,
                                    ixs_node *expr, ixs_node **lhs,
                                    ixs_node **rhs) {
  ixs_division_projection_result projection;
  if (!ixs_node_contains_rounding(expr))
    return IXS_ALGEBRA_NO_MATCH;
  projection = ixs_division_algebra_project(ctx, bounds, expr, expr, *rhs, *rhs,
                                            IXS_DIVISION_PROJECT_ALL);
  if (projection.status == IXS_ALGEBRA_MATCH) {
    *lhs = projection.lhs;
    *rhs = projection.rhs;
  }
  return projection.status;
}

static ixs_algebra_status
bounds_exact_value_project_bitfacts(ixs_bounds *bounds, ixs_node *expr,
                                    int64_t *value) {
  ixs_bitfacts bits;
  uint64_t raw;
  ixs_bounds_transport_status transport;
  if (!ixs_bounds_get_bitfacts(bounds, expr, &bits)) {
    transport = bounds_query_state_transport(bounds);
    if (transport == IXS_BOUNDS_TRANSPORT_INVALID)
      return IXS_ALGEBRA_INVALID;
    if (transport == IXS_BOUNDS_TRANSPORT_OOM || bounds->oom)
      return IXS_ALGEBRA_OOM;
    if (transport == IXS_BOUNDS_TRANSPORT_LIMITED)
      return IXS_ALGEBRA_LIMITED;
    return IXS_ALGEBRA_NO_MATCH;
  }
  assert((bits.known_zero & bits.known_one) == 0);
  if ((bits.known_zero | bits.known_one) != UINT64_MAX)
    return IXS_ALGEBRA_NO_MATCH;
  raw = bits.known_one;
  *value = raw <= (uint64_t)INT64_MAX ? (int64_t)raw
                                      : -1 - (int64_t)(UINT64_MAX - raw);
  return IXS_ALGEBRA_MATCH;
}

static ixs_algebra_status
bounds_exact_value_project_delta(ixs_ctx *ctx, ixs_bounds *bounds,
                                 ixs_node *lhs, ixs_node *rhs, int64_t *value) {
  bounds_delta_query query;
  bounds_delta_frame initial_frame;
  ixs_node *difference = simp_sub(ctx, lhs, rhs);
  ixs_algebra_status status;
  bool invalid = false;
  bool limited = false;
  bool oom = false;
  if (!difference)
    return IXS_ALGEBRA_OOM;
  if (ixs_node_is_sentinel(difference))
    return IXS_ALGEBRA_INVALID;
  status = bounds_exact_additive_value(bounds, difference, value);
  if (status != IXS_ALGEBRA_NO_MATCH)
    return status;
  if (!bounds_delta_query_start(&query, &initial_frame, ctx, bounds, lhs, rhs,
                                false, true))
    return bounds->oom ? IXS_ALGEBRA_OOM : IXS_ALGEBRA_NO_MATCH;
  bounds_delta_query_run(&query);
  if (bounds_delta_query_result(&query, value, &invalid, &limited, &oom))
    return IXS_ALGEBRA_MATCH;
  if (invalid)
    return IXS_ALGEBRA_INVALID;
  if (oom)
    return IXS_ALGEBRA_OOM;
  if (limited)
    return IXS_ALGEBRA_LIMITED;
  return IXS_ALGEBRA_NO_MATCH;
}

IXS_STATIC ixs_algebra_status bounds_project_exact_integer(ixs_ctx *ctx,
                                                           ixs_bounds *bounds,
                                                           ixs_node *expr,
                                                           int64_t *value) {
  ixs_node *lhs = expr;
  ixs_node *rhs = ctx ? ctx->node_zero : NULL;
  ixs_algebra_status status;
  ixs_bounds_transport_status transport;
  if (!ctx || !bounds || !expr || !value || bounds->oom ||
      bounds->contradiction)
    return bounds && bounds->oom ? IXS_ALGEBRA_OOM : IXS_ALGEBRA_NO_MATCH;
  transport = bounds_query_state_transport(bounds);
  if (transport == IXS_BOUNDS_TRANSPORT_INVALID)
    return IXS_ALGEBRA_INVALID;
  if (transport == IXS_BOUNDS_TRANSPORT_OOM)
    return IXS_ALGEBRA_OOM;
  if (transport == IXS_BOUNDS_TRANSPORT_LIMITED)
    return IXS_ALGEBRA_LIMITED;
  status = bounds_exact_value_source_defined(bounds, expr);
  if (status != IXS_ALGEBRA_MATCH)
    return status;
  if (bounds_range_exact_integer_difference(bounds, expr, value))
    return IXS_ALGEBRA_MATCH;
  status = bounds_exact_value_project_bitfacts(bounds, expr, value);
  if (status != IXS_ALGEBRA_NO_MATCH)
    return status;
  if (expr->tag != IXS_ADD)
    return IXS_ALGEBRA_NO_MATCH;
  status = bounds_exact_value_project_division(ctx, bounds, expr, &lhs, &rhs);
  if (status != IXS_ALGEBRA_MATCH && status != IXS_ALGEBRA_NO_MATCH)
    return status;
  return bounds_exact_value_project_delta(ctx, bounds, lhs, rhs, value);
}
