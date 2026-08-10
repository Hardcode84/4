/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds_residue.h"

#include "bounds.h"
#include "bounds_bitfacts.h"
#include "bounds_difference.h"
#include "bounds_query.h"
#include "bounds_store.h"
#include "hash.h"
#include "query_walk.h"
#include "rational.h"

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

typedef struct {
  ixs_node *representative;
  uint64_t coefficient;
} bounds_residue_group;

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
    group = ixs_hash_ptr(representative) & (group_capacity - 1u);
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
  uint64_t divisor;
  uint64_t factor;
  uint64_t scaled_modulus;
  uint64_t residue;
  uint32_t i;
  int64_t p;
  int64_t q;
  bool has_rational_coefficient;

  if (!b || !expr || expr->tag != IXS_ADD || modulus <= 0)
    return false;
  denominator = 1u;
  has_rational_coefficient = false;
  for (i = 0;; i++) {
    ixs_node_get_rat(
        i == 0 ? expr->u.add.coeff : expr->u.add.terms[i - 1u].coeff, &p, &q);
    if (q <= 0)
      return false;
    has_rational_coefficient = has_rational_coefficient || q != 1;
    divisor = (uint64_t)q;
    factor = divisor / ixs_u64_gcd(denominator, divisor);
    if (factor != 0 && denominator > (uint64_t)INT64_MAX / factor)
      return false;
    denominator *= factor;
    if (i == expr->u.add.nterms)
      break;
  }
  if (!has_rational_coefficient)
    return false;
  if ((uint64_t)modulus > (uint64_t)INT64_MAX / denominator)
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
  if ((node->tag == IXS_ADD || node->tag == IXS_MOD ||
       node->tag == IXS_PIECEWISE) &&
      ixs_node_is_integer_valued(node) && ixs_node_is_known_total(node))
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
  if (step == IXS_QUERY_WALK_NEXT) {
    step = query->proof_independent
               ? bounds_residue_direct_independent(query, frame)
               : bounds_residue_direct_tracked(query, frame);
  }
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
