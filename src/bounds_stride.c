/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds_stride.h"

#include "bounds.h"
#include "bounds_query.h"
#include "bounds_store.h"
#include "query_walk.h"
#include "rational.h"

#include <stdint.h>
#include <string.h>

static uint64_t bounds_scale_stride(uint64_t stride, int64_t coefficient,
                                    uint64_t target) {
  uint64_t magnitude = ixs_int64_magnitude(coefficient);
  if (target != 0) {
    uint64_t common = ixs_u64_gcd(target, stride);
    return common * ixs_u64_gcd(target / common, magnitude);
  }
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
  BOUNDS_STRIDE_MUL,
  BOUNDS_STRIDE_MOD,
  BOUNDS_STRIDE_PIECEWISE
} bounds_stride_stage;

typedef struct {
  ixs_node *expr;
  bounds_query_scope scope;
  uint64_t result;
  uint64_t residue;
  uint32_t index;
  bounds_stride_stage stage;
  bool tracked;
} bounds_stride_frame;

typedef struct {
  ixs_bounds *bounds;
  ixs_query_walk walk;
  bool child_success;
  uint64_t child_stride;
  uint64_t child_residue;
  uint64_t target_modulus;
} bounds_stride_query;

typedef struct {
  uint64_t modulus;
  uint64_t residue;
} bounds_stride_class;

static uint64_t bounds_gcd_product(uint64_t target, uint64_t lhs,
                                   uint64_t rhs) {
  uint64_t common = ixs_u64_gcd(target, lhs);
  return common * ixs_u64_gcd(target / common, rhs);
}

static bounds_stride_class bounds_stride_class_mul(uint64_t target,
                                                   bounds_stride_class lhs,
                                                   bounds_stride_class rhs) {
  bounds_stride_class result;
  uint64_t lhs_step = bounds_gcd_product(target, lhs.modulus, rhs.residue);
  uint64_t rhs_step = bounds_gcd_product(target, rhs.modulus, lhs.residue);
  uint64_t cross_step = bounds_gcd_product(target, lhs.modulus, rhs.modulus);
  result.modulus = ixs_u64_gcd(ixs_u64_gcd(lhs_step, rhs_step), cross_step);
  result.residue =
      result.modulus <= 1u
          ? 0u
          : ixs_u64_mul_mod(lhs.residue, rhs.residue, result.modulus);
  return result;
}

static bounds_stride_class bounds_stride_class_pow(uint64_t target,
                                                   bounds_stride_class base,
                                                   uint32_t exponent) {
  bounds_stride_class result = {target, target == 1u ? 0u : 1u};
  while (exponent != 0u) {
    if ((exponent & 1u) != 0u)
      result = bounds_stride_class_mul(target, result, base);
    exponent >>= 1;
    if (exponent != 0u)
      base = bounds_stride_class_mul(target, base, base);
  }
  return result;
}

static bounds_stride_class
bounds_stride_child_class(bounds_stride_query *query) {
  bounds_stride_class result;
  result.modulus =
      query->child_stride == 0u ? query->target_modulus : query->child_stride;
  result.residue =
      result.modulus <= 1u ? 0u : query->child_residue % result.modulus;
  return result;
}

static ixs_query_walk_step bounds_stride_complete(bounds_stride_query *query,
                                                  bool success,
                                                  uint64_t stride) {
  bounds_stride_frame *frame = IXS_QUERY_WALK_TOP(&query->walk);
  uint64_t residue = frame->residue;
  if (frame->tracked) {
    bounds_query_cache_entry *entry =
        bounds_query_finish(&frame->scope, success);
    if (entry->outcome == BOUNDS_QUERY_OUTCOME_VALUE) {
      entry->result.stride.modulus = stride;
      entry->result.stride.residue = query->target_modulus == 0u || stride <= 1u
                                         ? 0u
                                         : frame->residue % stride;
    } else {
      success = false;
    }
  }
  IXS_QUERY_WALK_POP(&query->walk);
  query->child_success = success;
  query->child_stride = success ? stride : 0;
  query->child_residue = success ? residue : 0u;
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
    bounds_query_enter_result enter =
        bounds_query_begin(query->bounds, BOUNDS_QUERY_STRIDE, node,
                           query->target_modulus, &frame->scope, &cached);
    if (enter == BOUNDS_QUERY_ENTER_CACHED) {
      frame->residue = cached->result.stride.residue;
      return bounds_stride_complete(query, cached->success,
                                    cached->result.stride.modulus);
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
  if (q != 1) {
    return bounds_stride_complete(query, false, 0);
  }
  frame->stage = BOUNDS_STRIDE_ADD;
  frame->result = 0;
  frame->residue = query->target_modulus == 0u
                       ? 0u
                       : ixs_int64_normalize_residue(p, query->target_modulus);
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
    return bounds_stride_complete(
        query, true, query->target_modulus != 0 ? query->target_modulus : 0u);
  }
  if (query->target_modulus != 0u) {
    if (node->u.mul.nfactors == 0u)
      return bounds_stride_complete(query, true, query->target_modulus);
    for (i = 0; i < node->u.mul.nfactors; i++)
      if (node->u.mul.factors[i].exp <= 0 ||
          !ixs_node_is_integer_valued(node->u.mul.factors[i].base))
        return bounds_stride_complete(query, true, 1u);
    frame->stage = BOUNDS_STRIDE_MUL;
    frame->index = 0u;
    frame->result = query->target_modulus;
    frame->residue = ixs_int64_normalize_residue(p, query->target_modulus);
    return ixs_query_walk_push(&query->walk, node->u.mul.factors[0].base);
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
    if (query->target_modulus != 0u)
      frame->residue =
          ixs_int64_normalize_residue(node->u.ival, query->target_modulus);
    return bounds_stride_complete(
        query, true, query->target_modulus != 0 ? query->target_modulus : 0u);
  case IXS_RAT:
    if (query->target_modulus != 0u && node->u.rat.q == 1)
      frame->residue =
          ixs_int64_normalize_residue(node->u.rat.p, query->target_modulus);
    return bounds_stride_complete(
        query, node->u.rat.q == 1,
        query->target_modulus != 0 ? query->target_modulus : 0u);
  case IXS_SYM: {
    int64_t modulus;
    int64_t remainder = 0;
    uint64_t result = 1;
    if (bounds_store_get_modrem(query->bounds, node->u.name, &modulus,
                                &remainder)) {
      result = (uint64_t)modulus;
    }
    if (query->target_modulus != 0)
      result = ixs_u64_gcd(result, query->target_modulus);
    if (result > 1u)
      frame->residue = ixs_int64_normalize_residue(remainder, result);
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
        ixs_u64_gcd(frame->result, bounds_scale_stride(query->child_stride, p,
                                                       query->target_modulus));
    if (query->target_modulus != 0u) {
      uint64_t scaled =
          ixs_u64_mul_mod(ixs_int64_normalize_residue(p, query->target_modulus),
                          query->child_residue, query->target_modulus);
      frame->residue =
          ixs_u64_add_mod(frame->residue, scaled, query->target_modulus);
    }
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
    uint64_t stride;
    ixs_node_get_rat(node->u.mul.coeff, &p, &q);
    (void)q;
    stride = bounds_scale_stride(query->child_stride, p, query->target_modulus);
    if (query->target_modulus != 0u && stride > 1u)
      frame->residue = ixs_u64_mul_mod(ixs_int64_normalize_residue(p, stride),
                                       query->child_residue, stride);
    return bounds_stride_complete(query, true, stride);
  }
  case BOUNDS_STRIDE_MUL: {
    bounds_stride_class product = {frame->result, frame->residue};
    bounds_stride_class factor = bounds_stride_child_class(query);
    factor = bounds_stride_class_pow(
        query->target_modulus, factor,
        (uint32_t)node->u.mul.factors[frame->index].exp);
    product = bounds_stride_class_mul(query->target_modulus, product, factor);
    frame->result = product.modulus;
    frame->residue = product.residue;
    frame->index++;
    if (frame->index == node->u.mul.nfactors)
      return bounds_stride_complete(query, true, frame->result);
    return ixs_query_walk_push(&query->walk,
                               node->u.mul.factors[frame->index].base);
  }
  case BOUNDS_STRIDE_MOD:
    frame->result =
        ixs_u64_gcd(query->child_stride, (uint64_t)node->u.binary.rhs->u.ival);
    if (frame->result > 1u)
      frame->residue = query->child_residue % frame->result;
    return bounds_stride_complete(query, true, frame->result);
  case BOUNDS_STRIDE_PIECEWISE:
    if (query->target_modulus != 0u) {
      bounds_stride_class branch = bounds_stride_child_class(query);
      if (frame->index == 0u) {
        frame->result = branch.modulus;
        frame->residue = branch.residue;
      } else {
        uint64_t difference = frame->residue >= branch.residue
                                  ? frame->residue - branch.residue
                                  : branch.residue - frame->residue;
        frame->result =
            ixs_u64_gcd(ixs_u64_gcd(frame->result, branch.modulus), difference);
        frame->residue =
            frame->result <= 1u ? 0u : frame->residue % frame->result;
      }
    } else {
      frame->result = ixs_u64_gcd(frame->result, query->child_stride);
    }
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

static bool bounds_known_stride_mode(ixs_bounds *bounds, ixs_node *expr,
                                     uint64_t target_modulus, uint64_t *stride,
                                     uint64_t *residue) {
  bounds_stride_query query;
  if (!bounds || !expr || !stride || bounds->oom)
    return false;
  memset(&query, 0, sizeof(query));
  query.bounds = bounds;
  query.target_modulus = target_modulus;
  IXS_QUERY_WALK_INIT(&query.walk, bounds->scratch, &bounds->oom,
                      bounds_stride_frame, expr);
  if (!ixs_query_walk_run(&query.walk, expr, &query, bounds_stride_advance,
                          bounds_stride_abort))
    return false;
  if (!query.child_success)
    return false;
  *stride = query.child_stride;
  if (residue)
    *residue = query.child_residue;
  return true;
}

IXS_STATIC bool bounds_known_stride(ixs_bounds *bounds, ixs_node *expr,
                                    uint64_t *stride) {
  return bounds_known_stride_mode(bounds, expr, 0u, stride, NULL);
}

IXS_STATIC bool bounds_known_residue_class(ixs_bounds *bounds, ixs_node *expr,
                                           uint64_t modulus,
                                           uint64_t *class_modulus,
                                           uint64_t *class_residue) {
  uint64_t residue;
  uint64_t stride;
  if (modulus == 0u || !class_modulus || !class_residue ||
      !bounds_known_stride_mode(bounds, expr, modulus, &stride, &residue))
    return false;
  stride = stride == 0u ? modulus : ixs_u64_gcd(stride, modulus);
  if (stride <= 1u)
    return false;
  *class_modulus = stride;
  *class_residue = residue % stride;
  return true;
}
