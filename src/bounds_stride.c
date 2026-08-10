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

IXS_STATIC bool bounds_known_stride(ixs_bounds *bounds, ixs_node *expr,
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
