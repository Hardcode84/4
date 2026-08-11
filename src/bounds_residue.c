/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds_residue.h"

#include "bounds.h"
#include "bounds_bitfacts.h"
#include "bounds_difference.h"
#include "bounds_proof.h"
#include "bounds_query.h"
#include "bounds_store.h"
#include "hash.h"
#include "rational.h"

#include <assert.h>
#include <limits.h>
#include <stdint.h>
#include <string.h>

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

typedef struct bounds_residue_group {
  ixs_node *representative;
  uint64_t coefficient;
} bounds_residue_group;

/* Mod(x, k) and x have the same residue modulo every positive divisor of k.
 * Strip only literal, positive moduli and only across integer-valued operands;
 * pointer identity then gives a cheap canonical congruence representative.
 */
static ixs_node *bounds_residue_representative(bounds_proof_query *query,
                                               ixs_bounds *b, ixs_node *expr,
                                               uint64_t modulus) {
  while (expr->tag == IXS_MOD && expr->u.binary.rhs->tag == IXS_INT &&
         expr->u.binary.rhs->u.ival > 0 &&
         (uint64_t)expr->u.binary.rhs->u.ival % modulus == 0 &&
         (ixs_node_is_integer_valued(expr->u.binary.lhs) ||
          bounds_proof_integer_cached(query, b, expr->u.binary.lhs))) {
    expr = expr->u.binary.lhs;
  }
  return expr;
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

IXS_STATIC ixs_query_walk_step
bounds_proof_push_scaled_add(bounds_proof_query *query, ixs_bounds *bounds,
                             ixs_node *expr, uint64_t scale, uint64_t modulus) {
  ixs_query_walk_step step =
      bounds_proof_push_residue_task(query, bounds, expr, modulus);
  bounds_residue_frame *frame;
  if (step != IXS_QUERY_WALK_ADVANCED ||
      query->top_kind != BOUNDS_PROOF_FRAME_RESIDUE)
    return step;
  frame = &query->residue_frames[query->residue_count - 1u];
  frame->coefficient = scale;
  frame->synthetic_scaled = true;
  frame->stage = BOUNDS_RESIDUE_SCALED_ADD_START;
  return IXS_QUERY_WALK_ADVANCED;
}

static void bounds_residue_destroy_fork(bounds_proof_query *query,
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

static bool bounds_residue_close(bounds_proof_query *query,
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
  return success;
}

static ixs_query_walk_step bounds_residue_complete(bounds_proof_query *query,
                                                   bool success,
                                                   uint64_t residue) {
  bounds_residue_frame *frame;
  assert(query->top_kind == BOUNDS_PROOF_FRAME_RESIDUE);
  frame = &query->residue_frames[query->residue_count - 1u];
  success = bounds_residue_close(query, frame, success, residue);
  return bounds_proof_complete_residue(query, success, residue);
}

/* hot */
IXS_STATIC void bounds_residue_abort(bounds_proof_query *query,
                                     bounds_residue_frame *frame) {
  (void)bounds_residue_close(query, frame, false, 0);
  (void)bounds_proof_complete_residue(query, false, 0);
}

static bool bounds_residue_prepare_add(bounds_proof_query *query,
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
    if (q <= 0 || scale % (uint64_t)q != 0)
      return false;
    if (b->oom) {
      query->root->oom = true;
      return false;
    }
    coefficient =
        ixs_u64_mul_mod(ixs_int64_normalize_residue(p, frame->modulus),
                        (scale / (uint64_t)q) % frame->modulus, frame->modulus);
    if (coefficient == 0 && !frame->synthetic_scaled)
      continue;
    representative =
        bounds_residue_representative(query, b, term, frame->modulus);
    group = ixs_hash_ptr(representative) & (capacity - 1u);
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

static bool bounds_residue_add_scale(ixs_node *expr, uint64_t modulus,
                                     uint64_t *scale,
                                     uint64_t *scaled_modulus) {
  uint64_t denominator = 1u;
  uint32_t i;
  for (i = 0;; i++) {
    uint64_t divisor;
    uint64_t factor;
    int64_t p;
    int64_t q;
    ixs_node_get_rat(
        i == 0 ? expr->u.add.coeff : expr->u.add.terms[i - 1u].coeff, &p, &q);
    (void)p;
    if (q <= 0)
      return false;
    divisor = (uint64_t)q;
    factor = divisor / ixs_u64_gcd(denominator, divisor);
    if (factor != 0u && denominator > (uint64_t)INT64_MAX / factor)
      return false;
    denominator *= factor;
    if (i == expr->u.add.nterms)
      break;
  }
  if (modulus > (UINT64_C(1) << 63u) / denominator)
    return false;
  *scale = denominator;
  *scaled_modulus = modulus * denominator;
  return true;
}

static bool bounds_residue_alloc_fork(bounds_proof_query *query,
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

static bool bounds_residue_start_reachable(bounds_proof_query *query,
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
bounds_residue_track_frame(bounds_proof_query *query,
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

static ixs_query_walk_step
bounds_residue_direct_independent(bounds_proof_query *query,
                                  bounds_residue_frame *frame) {
  ixs_bounds *current = frame->bounds;
  ixs_node *node = frame->expr;
  ixs_var_bound *var = NULL;
  ixs_interval iv;
  ixs_bitfacts bits;
  int64_t exact;

  /* Public integrality would re-enter the live exact-proof stack. */
  if (!ixs_node_is_known_total(node))
    return IXS_QUERY_WALK_NEXT;
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
bounds_residue_direct_integral_tracked(bounds_proof_query *query,
                                       bounds_residue_frame *frame) {
  ixs_bounds *current = frame->bounds;
  ixs_node *node = frame->expr;
  ixs_interval iv;
  ixs_bitfacts bits;
  int64_t exact;

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
bounds_residue_direct_tracked(bounds_proof_query *query,
                              bounds_residue_frame *frame) {
  ixs_node *node = frame->expr;
  int64_t exact;

  /* Structural ADD skips recursive interval propagation, but an exact unit
   * difference is an O(1) producer invariant and retains its affine offset. */
  if (node->tag == IXS_ADD &&
      bounds_difference_exact_unit_value(frame->bounds, node, &exact)) {
    return bounds_residue_complete(
        query, true, ixs_int64_normalize_residue(exact, frame->modulus));
  }
  if (node->tag == IXS_ADD && ixs_node_is_known_total(node))
    return IXS_QUERY_WALK_NEXT;
  if ((node->tag == IXS_MUL || node->tag == IXS_MOD ||
       node->tag == IXS_PIECEWISE) &&
      ixs_node_is_integer_valued(node) && ixs_node_is_known_total(node))
    return IXS_QUERY_WALK_NEXT;
  if (!ixs_node_is_known_total(node))
    return bounds_residue_complete(query, false, 0);
  frame->stage = BOUNDS_RESIDUE_INTEGER_CHILD;
  return bounds_proof_push_exact(query, frame->bounds, node,
                                 BOUNDS_PROOF_INTEGER, 0);
}

static ixs_query_walk_step
bounds_residue_start_mul(bounds_proof_query *query,
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
  frame->result = 1u % frame->reduced_modulus;
  frame->index = 0;
  frame->stage = BOUNDS_RESIDUE_MUL_INTEGER_SCAN;
  return IXS_QUERY_WALK_ADVANCED;
}

static ixs_query_walk_step
bounds_residue_start_assoc(bounds_proof_query *query,
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
bounds_residue_start_frame(bounds_proof_query *query,
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
    if (!bounds_residue_add_scale(node, frame->modulus, &frame->reduced_modulus,
                                  &frame->result))
      return bounds_residue_complete(query, false, 0);
    if (frame->reduced_modulus != 1u) {
      frame->stage = BOUNDS_RESIDUE_ADD_SCALED_CHILD;
      return bounds_proof_push_scaled_add(
          query, frame->bounds, node, frame->reduced_modulus, frame->result);
    }
    frame->index = 0;
    frame->stage = BOUNDS_RESIDUE_ADD_INTEGER_SCAN;
    return IXS_QUERY_WALK_ADVANCED;
  case IXS_MUL:
    return bounds_residue_start_mul(query, frame);
  case IXS_MOD:
    if (node->u.binary.rhs->tag != IXS_INT || node->u.binary.rhs->u.ival <= 0 ||
        (uint64_t)node->u.binary.rhs->u.ival % frame->modulus != 0) {
      return bounds_residue_complete(query, false, 0);
    }
    frame->stage = BOUNDS_RESIDUE_MOD_CHILD;
    return bounds_proof_push_residue(query, frame->bounds, node->u.binary.lhs,
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
bounds_residue_resume_add(bounds_proof_query *query,
                          bounds_residue_frame *frame) {
  if (frame->stage == BOUNDS_RESIDUE_ADD_SCALED_CHILD) {
    uint64_t scale = frame->reduced_modulus;
    if (!query->child_success || query->child_residue % scale != 0u)
      return bounds_residue_complete(query, false, 0);
    return bounds_residue_complete(
        query, true, (query->child_residue / scale) % frame->modulus);
  }
  if (frame->stage == BOUNDS_RESIDUE_ADD_INTEGER_CHILD) {
    if (!query->child_success)
      return bounds_residue_complete(query, false, 0);
    frame->index++;
    frame->stage = BOUNDS_RESIDUE_ADD_INTEGER_SCAN;
  }
  if (frame->stage == BOUNDS_RESIDUE_ADD_INTEGER_SCAN) {
    if (frame->index < frame->expr->u.add.nterms) {
      ixs_node *term = frame->expr->u.add.terms[frame->index].term;
      if (!term)
        return IXS_QUERY_WALK_STOP;
      if (ixs_node_is_integer_valued(term) ||
          bounds_proof_integer_cached(query, frame->bounds, term)) {
        frame->index++;
        return IXS_QUERY_WALK_ADVANCED;
      }
      frame->stage = BOUNDS_RESIDUE_ADD_INTEGER_CHILD;
      return bounds_proof_push_exact(query, frame->bounds, term,
                                     BOUNDS_PROOF_INTEGER, 0);
    }
    if (!bounds_residue_prepare_add(query, frame, 1u)) {
      if (query->root->oom)
        return IXS_QUERY_WALK_OOM;
      return bounds_residue_complete(query, false, 0);
    }
  }
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
    if (!group->representative ||
        (group->coefficient == 0 && !frame->synthetic_scaled))
      continue;
    frame->coefficient = group->coefficient;
    frame->reduced_modulus =
        frame->modulus / ixs_u64_gcd(frame->coefficient, frame->modulus);
    if (frame->reduced_modulus == 1u && !frame->synthetic_scaled)
      continue;
    frame->stage = BOUNDS_RESIDUE_ADD_CHILD;
    return bounds_proof_push_residue(
        query, frame->bounds, group->representative, frame->reduced_modulus);
  }
  return bounds_residue_complete(query, true, frame->result);
}

static ixs_query_walk_step
bounds_residue_resume_mul(bounds_proof_query *query,
                          bounds_residue_frame *frame) {
  ixs_node *node = frame->expr;
  if (frame->stage == BOUNDS_RESIDUE_MUL_INTEGER_SCAN) {
    if (frame->index != 0u && !query->child_success)
      return bounds_residue_complete(query, false, 0);
    if (frame->index < node->u.mul.nfactors) {
      const ixs_mulfactor *factor = &node->u.mul.factors[frame->index++];
      if (!factor->base || factor->exp < 0)
        return factor->base ? bounds_residue_complete(query, false, 0)
                            : IXS_QUERY_WALK_STOP;
      if (ixs_node_is_integer_valued(factor->base) ||
          bounds_proof_integer_cached(query, frame->bounds, factor->base)) {
        query->child_success = true;
        return IXS_QUERY_WALK_ADVANCED;
      }
      return bounds_proof_push_exact(query, frame->bounds, factor->base,
                                     BOUNDS_PROOF_INTEGER, 0);
    }
    if (frame->reduced_modulus == 1u)
      return bounds_residue_complete(query, true, 0);
    frame->index = 0;
    frame->stage = BOUNDS_RESIDUE_MUL_SCAN;
  }
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
  if (frame->result == 0 || frame->index == node->u.mul.nfactors) {
    return bounds_residue_complete(
        query, true,
        ixs_u64_mul_mod(frame->coefficient, frame->result, frame->modulus));
  }
  if (node->u.mul.factors[frame->index].exp < 0) {
    return bounds_residue_complete(query, false, 0);
  }
  frame->stage = BOUNDS_RESIDUE_MUL_CHILD;
  return bounds_proof_push_residue(query, frame->bounds,
                                   node->u.mul.factors[frame->index].base,
                                   frame->reduced_modulus);
}

static ixs_query_walk_step
bounds_residue_resume_assoc(bounds_proof_query *query,
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
    return bounds_proof_push_residue(
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

static bool bounds_residue_add_condition(bounds_proof_query *query,
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
bounds_residue_resume_pw_total(bounds_proof_query *query,
                               bounds_residue_frame *frame) {
  ixs_node *node = frame->expr;
  if (frame->stage == BOUNDS_RESIDUE_PW_TOTAL_SCAN) {
    if (frame->index == node->u.pw.ncases) {
      return bounds_residue_complete(query, frame->have_result, frame->result);
    }
    frame->stage = BOUNDS_RESIDUE_PW_TOTAL_CHILD;
    return bounds_proof_push_residue(query, frame->bounds,
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
bounds_residue_resume_pw_reach_scan(bounds_proof_query *query,
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
  return bounds_proof_push_residue(query, frame->active, value, frame->modulus);
}

static ixs_query_walk_step
bounds_residue_resume_pw_reach_child(bounds_proof_query *query,
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
bounds_residue_resume_frame(bounds_proof_query *query,
                            bounds_residue_frame *frame) {
  switch (frame->stage) {
  case BOUNDS_RESIDUE_SCALED_ADD_START: {
    uint64_t scale = frame->coefficient;
    if (!bounds_residue_prepare_add(query, frame, scale)) {
      if (query->root->oom)
        return IXS_QUERY_WALK_OOM;
      return bounds_residue_complete(query, false, 0);
    }
    return IXS_QUERY_WALK_ADVANCED;
  }
  case BOUNDS_RESIDUE_INTEGER_CHILD: {
    ixs_query_walk_step step;
    if (!query->child_success)
      return bounds_residue_complete(query, false, 0);
    step = bounds_residue_direct_integral_tracked(query, frame);
    return step == IXS_QUERY_WALK_NEXT
               ? bounds_residue_start_frame(query, frame)
               : step;
  }
  case BOUNDS_RESIDUE_ADD_INTEGER_SCAN:
  case BOUNDS_RESIDUE_ADD_INTEGER_CHILD:
  case BOUNDS_RESIDUE_ADD_SCALED_CHILD:
  case BOUNDS_RESIDUE_ADD_SCAN:
  case BOUNDS_RESIDUE_ADD_CHILD:
    return bounds_residue_resume_add(query, frame);
  case BOUNDS_RESIDUE_MUL_INTEGER_SCAN:
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
IXS_STATIC ixs_query_walk_step
bounds_residue_advance(bounds_proof_query *query, bounds_residue_frame *frame) {
  ixs_query_walk_step step;
  query->active_bounds = frame->bounds;
  if (frame->stage != BOUNDS_RESIDUE_INITIAL)
    return bounds_residue_resume_frame(query, frame);
  step = bounds_residue_track_frame(query, frame);
  if (step == IXS_QUERY_WALK_NEXT) {
    step = query->proof_independent
               ? bounds_residue_direct_independent(query, frame)
               : bounds_residue_direct_tracked(query, frame);
  }
  if (step == IXS_QUERY_WALK_NEXT)
    step = bounds_residue_start_frame(query, frame);
  return step;
}

IXS_STATIC bool bounds_known_residue(ixs_bounds *b, ixs_node *expr,
                                     uint64_t modulus, uint64_t *out) {
  ixs_arena_mark mark;
  bounds_proof_query query;
  ixs_query_walk_step step;
  if (!b || !expr || !out || modulus == 0 || b->oom)
    return false;

  mark = ixs_arena_save(b->scratch);
  bounds_proof_query_init(&query, b, false);
  step = bounds_proof_push_residue(&query, b, expr, modulus);
  step = bounds_proof_drive(&query, step);
  if (query.child_success)
    *out = query.child_residue;
  ixs_arena_restore(b->scratch, mark);
  return step == IXS_QUERY_WALK_ADVANCED && query.child_success;
}
