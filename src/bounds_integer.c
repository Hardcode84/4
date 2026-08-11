/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds_integer.h"

#include "bounds.h"
#include "bounds_proof.h"
#include "bounds_query.h"
#include "hash.h"
#include "rational.h"

#include <assert.h>
#include <limits.h>
#include <stdint.h>
#include <string.h>

static size_t bounds_exact_proof_hash(ixs_bounds *bounds, ixs_node *expr,
                                      bounds_proof_kind kind,
                                      uint64_t modulus) {
  size_t hash = ixs_hash_ptr(expr);
  hash ^= ixs_hash_ptr(bounds) + (hash << 6u) + (hash >> 2u);
  hash ^= (size_t)(uint64_t)modulus + (hash << 6u) + (hash >> 2u);
  hash ^= (size_t)kind + (hash << 6u) + (hash >> 2u);
  return hash;
}

static bool bounds_proof_memo_grow(bounds_proof_query *query) {
  size_t capacity = query->memo.capacity ? query->memo.capacity * 2u : 32u;
  bounds_proof_memo_entry *grown;
  size_t i;
  if (capacity <= query->memo.capacity || capacity > SIZE_MAX / sizeof(*grown))
    return false;
  grown = ixs_arena_alloc(query->root->scratch, capacity * sizeof(*grown),
                          sizeof(void *));
  if (!grown)
    return false;
  memset(grown, 0, capacity * sizeof(*grown));
  for (i = 0; i < query->memo.capacity; i++) {
    bounds_proof_memo_entry entry = query->memo.entries[i];
    size_t slot;
    if (!entry.expr)
      continue;
    slot =
        bounds_exact_proof_hash(entry.bounds, entry.expr,
                                (bounds_proof_kind)entry.kind, entry.modulus) &
        (capacity - 1u);
    while (grown[slot].expr)
      slot = (slot + 1u) & (capacity - 1u);
    grown[slot] = entry;
  }
  query->memo.entries = grown;
  query->memo.capacity = capacity;
  return true;
}

static bounds_proof_memo_entry *
bounds_proof_memo_get(bounds_proof_query *query, ixs_bounds *bounds,
                      ixs_node *expr, bounds_proof_kind kind, uint64_t modulus,
                      bool create) {
  size_t slot;
  if (create && (!query->memo.capacity ||
                 query->memo.count + 1u > query->memo.capacity / 2u)) {
    if (!bounds_proof_memo_grow(query))
      return NULL;
  }
  if (!query->memo.capacity)
    return NULL;
  slot = bounds_exact_proof_hash(bounds, expr, kind, modulus) &
         (query->memo.capacity - 1u);
  while (query->memo.entries[slot].expr &&
         (query->memo.entries[slot].bounds != bounds ||
          query->memo.entries[slot].expr != expr ||
          (bounds_proof_kind)query->memo.entries[slot].kind != kind ||
          query->memo.entries[slot].modulus != modulus))
    slot = (slot + 1u) & (query->memo.capacity - 1u);
  if (!query->memo.entries[slot].expr) {
    if (!create)
      return NULL;
    query->memo.entries[slot].bounds = bounds;
    query->memo.entries[slot].expr = expr;
    query->memo.entries[slot].kind = (uint8_t)kind;
    query->memo.entries[slot].modulus = modulus;
    query->memo.count++;
  }
  return &query->memo.entries[slot];
}

static bool bounds_proof_grow_exact(bounds_proof_query *query) {
  size_t capacity = query->exact_capacity * 2u;
  bounds_exact_proof_frame *grown;
  if (capacity <= query->exact_capacity || capacity > SIZE_MAX / sizeof(*grown))
    return false;
  grown = ixs_arena_grow(query->root->scratch, query->exact_frames,
                         query->exact_capacity * sizeof(*grown),
                         capacity * sizeof(*grown), sizeof(void *));
  if (!grown)
    return false;
  query->exact_frames = grown;
  query->exact_capacity = capacity;
  return true;
}

static bool bounds_proof_grow_residue(bounds_proof_query *query) {
  size_t capacity =
      query->residue_capacity ? query->residue_capacity * 2u : 16u;
  bounds_residue_frame *grown;
  if (capacity <= query->residue_capacity ||
      capacity > SIZE_MAX / sizeof(*grown))
    return false;
  grown = ixs_arena_grow(query->root->scratch, query->residue_frames,
                         query->residue_capacity * sizeof(*grown),
                         capacity * sizeof(*grown), sizeof(void *));
  if (!grown)
    return false;
  query->residue_frames = grown;
  query->residue_capacity = capacity;
  return true;
}

static void bounds_proof_restore_parent(bounds_proof_query *query,
                                        bounds_proof_frame_kind parent) {
  query->top_kind = parent;
  if (parent == BOUNDS_PROOF_FRAME_RESIDUE) {
    assert(query->residue_count != 0u);
    query->active_bounds =
        query->residue_frames[query->residue_count - 1u].bounds;
  } else if (parent == BOUNDS_PROOF_FRAME_NONE) {
    query->active_bounds = query->root;
  }
}

IXS_STATIC void bounds_proof_query_init(bounds_proof_query *query,
                                        ixs_bounds *root,
                                        bool proof_independent) {
  memset(query, 0, sizeof(*query));
  query->root = root;
  query->active_bounds = root;
  query->proof_independent = proof_independent;
  query->exact_frames = query->inline_exact;
  query->exact_capacity =
      sizeof(query->inline_exact) / sizeof(query->inline_exact[0]);
  query->memo.entries = query->inline_memo;
  query->memo.capacity =
      sizeof(query->inline_memo) / sizeof(query->inline_memo[0]);
}

IXS_STATIC ixs_query_walk_step bounds_proof_push_exact(
    bounds_proof_query *query, ixs_bounds *bounds, ixs_node *expr,
    bounds_proof_kind kind, uint64_t modulus) {
  bounds_proof_memo_entry *entry;
  bounds_exact_proof_frame *frame;
  if (!bounds || !expr || (kind == BOUNDS_PROOF_DIVISIBLE && modulus == 0u) ||
      (kind != BOUNDS_PROOF_INTEGER && kind != BOUNDS_PROOF_DIVISIBLE)) {
    return IXS_QUERY_WALK_STOP;
  }
  entry = bounds_proof_memo_get(query, bounds, expr, kind, modulus, true);
  if (!entry) {
    query->root->oom = true;
    return IXS_QUERY_WALK_OOM;
  }
  if (entry->active)
    return IXS_QUERY_WALK_STOP;
  if (entry->complete) {
    query->child_success = entry->success;
    query->child_residue = entry->residue;
    return IXS_QUERY_WALK_ADVANCED;
  }
  if (query->exact_count == query->exact_capacity &&
      !bounds_proof_grow_exact(query)) {
    query->root->oom = true;
    return IXS_QUERY_WALK_OOM;
  }
  frame = &query->exact_frames[query->exact_count++];
  memset(frame, 0, sizeof(*frame));
  frame->expr = expr;
  frame->kind = kind;
  frame->modulus = modulus;
  frame->stage = BOUNDS_EXACT_PROOF_INITIAL;
  frame->parent_kind = (uint8_t)query->top_kind;
  query->top_kind = BOUNDS_PROOF_FRAME_EXACT;
  query->active_bounds = bounds;
  query->depth++;
  if (entry)
    entry->active = true;
  return IXS_QUERY_WALK_ADVANCED;
}

static ixs_query_walk_step
bounds_proof_push_residue_mode(bounds_proof_query *query, ixs_bounds *bounds,
                               ixs_node *expr, uint64_t modulus,
                               bool memoized) {
  bounds_proof_memo_entry *entry = NULL;
  bounds_residue_frame *frame;
  if (!bounds || !expr || modulus == 0u || bounds->oom)
    return bounds && bounds->oom ? IXS_QUERY_WALK_OOM : IXS_QUERY_WALK_STOP;
  if (memoized) {
    entry = bounds_proof_memo_get(query, bounds, expr, BOUNDS_PROOF_RESIDUE,
                                  modulus, true);
    if (!entry) {
      query->root->oom = true;
      return IXS_QUERY_WALK_OOM;
    }
    if (entry->active)
      return IXS_QUERY_WALK_STOP;
    if (entry->complete) {
      query->child_success = entry->success;
      query->child_residue = entry->residue;
      return IXS_QUERY_WALK_ADVANCED;
    }
  }
  if (query->residue_count == query->residue_capacity &&
      !bounds_proof_grow_residue(query)) {
    query->root->oom = true;
    return IXS_QUERY_WALK_OOM;
  }
  frame = &query->residue_frames[query->residue_count++];
  memset(frame, 0, sizeof(*frame));
  frame->expr = expr;
  frame->bounds = bounds;
  frame->modulus = modulus;
  frame->stage = BOUNDS_RESIDUE_INITIAL;
  frame->memoized = memoized;
  frame->parent_kind = (uint8_t)query->top_kind;
  query->top_kind = BOUNDS_PROOF_FRAME_RESIDUE;
  query->active_bounds = bounds;
  query->depth++;
  if (entry)
    entry->active = true;
  return IXS_QUERY_WALK_ADVANCED;
}

IXS_STATIC ixs_query_walk_step
bounds_proof_push_residue(bounds_proof_query *query, ixs_bounds *bounds,
                          ixs_node *expr, uint64_t modulus) {
  return bounds_proof_push_residue_mode(query, bounds, expr, modulus,
                                        query->proof_independent);
}

IXS_STATIC ixs_query_walk_step
bounds_proof_push_residue_task(bounds_proof_query *query, ixs_bounds *bounds,
                               ixs_node *expr, uint64_t modulus) {
  return bounds_proof_push_residue_mode(query, bounds, expr, modulus, false);
}

IXS_STATIC bool bounds_proof_integer_cached(bounds_proof_query *query,
                                            ixs_bounds *bounds,
                                            ixs_node *expr) {
  bounds_proof_memo_entry *entry = bounds_proof_memo_get(
      query, bounds, expr, BOUNDS_PROOF_INTEGER, 0, false);
  return entry && entry->complete && entry->success;
}

IXS_STATIC ixs_query_walk_step
bounds_proof_complete_exact(bounds_proof_query *query, bool success) {
  bounds_exact_proof_frame *frame;
  bounds_proof_memo_entry *entry = NULL;
  bounds_proof_frame_kind parent;
  assert(query->top_kind == BOUNDS_PROOF_FRAME_EXACT);
  assert(query->exact_count != 0u && query->depth != 0u);
  frame = &query->exact_frames[query->exact_count - 1u];
  {
    entry = bounds_proof_memo_get(query, query->active_bounds, frame->expr,
                                  frame->kind, frame->modulus, false);
    if (!entry || !entry->active)
      return IXS_QUERY_WALK_STOP;
    entry->success = success;
    entry->residue = 0;
    entry->active = false;
    entry->complete = true;
  }
  parent = (bounds_proof_frame_kind)frame->parent_kind;
  query->exact_count--;
  query->depth--;
  bounds_proof_restore_parent(query, parent);
  query->child_success = success;
  query->child_residue = 0;
  return IXS_QUERY_WALK_ADVANCED;
}

IXS_STATIC ixs_query_walk_step bounds_proof_complete_residue(
    bounds_proof_query *query, bool success, uint64_t residue) {
  bounds_residue_frame *frame;
  bounds_proof_memo_entry *entry = NULL;
  bounds_proof_frame_kind parent;
  assert(query->top_kind == BOUNDS_PROOF_FRAME_RESIDUE);
  assert(query->residue_count != 0u && query->depth != 0u);
  frame = &query->residue_frames[query->residue_count - 1u];
  if (frame->memoized) {
    entry = bounds_proof_memo_get(query, frame->bounds, frame->expr,
                                  BOUNDS_PROOF_RESIDUE, frame->modulus, false);
    if (!entry || !entry->active)
      return IXS_QUERY_WALK_STOP;
    entry->success = success;
    entry->residue = residue;
    entry->active = false;
    entry->complete = true;
  }
  parent = (bounds_proof_frame_kind)frame->parent_kind;
  query->residue_count--;
  query->depth--;
  bounds_proof_restore_parent(query, parent);
  query->child_success = success;
  query->child_residue = residue;
  return IXS_QUERY_WALK_ADVANCED;
}

static ixs_query_walk_step bounds_exact_proof_push(bounds_proof_query *query,
                                                   ixs_node *expr,
                                                   bounds_proof_kind kind,
                                                   uint64_t modulus) {
  return bounds_proof_push_exact(query, query->active_bounds, expr, kind,
                                 modulus);
}

static bool bounds_exact_proof_rational(ixs_node *node, int64_t *p,
                                        int64_t *q) {
  if (!node || (node->tag != IXS_INT && node->tag != IXS_RAT))
    return false;
  ixs_node_get_rat(node, p, q);
  return *q > 0;
}

static ixs_query_walk_step
bounds_exact_proof_start_integer_mul(bounds_exact_proof_frame *frame) {
  ixs_node *node = frame->expr;
  int64_t p;
  int64_t q;
  int64_t divisor;
  if (!bounds_exact_proof_rational(node->u.mul.coeff, &p, &q) ||
      (node->u.mul.nfactors != 0 && !node->u.mul.factors)) {
    return IXS_QUERY_WALK_STOP;
  }
  frame->index = 0;
  if (q == 1) {
    frame->stage = BOUNDS_PROOF_INTEGER_MUL_SCAN;
    return IXS_QUERY_WALK_ADVANCED;
  }
  divisor = ixs_gcd(p, q);
  if (divisor <= 0 || q % divisor != 0) {
    return IXS_QUERY_WALK_STOP;
  }
  frame->denominator = q / divisor;
  frame->denominator_cancelled = frame->denominator == 1;
  frame->stage = BOUNDS_PROOF_INTEGER_MUL_RATIONAL_SCAN;
  return IXS_QUERY_WALK_ADVANCED;
}

static ixs_query_walk_step
bounds_exact_proof_start_integer_add(bounds_proof_query *query,
                                     bounds_exact_proof_frame *frame) {
  int64_t p;
  int64_t q;
  ixs_node *node = frame->expr;
  if (!bounds_exact_proof_rational(node->u.add.coeff, &p, &q) ||
      (node->u.add.nterms != 0 && !node->u.add.terms)) {
    return IXS_QUERY_WALK_STOP;
  }
  (void)p;
  if (q != 1) {
    frame->stage = BOUNDS_PROOF_INTEGER_ADD_RESIDUE;
    return bounds_proof_push_residue(query, query->active_bounds, node, 1u);
  }
  frame->index = 0;
  frame->stage = BOUNDS_PROOF_INTEGER_ADD_SCAN;
  return IXS_QUERY_WALK_ADVANCED;
}

static ixs_query_walk_step
bounds_exact_proof_start_integer(bounds_proof_query *query,
                                 bounds_exact_proof_frame *frame) {
  ixs_node *node = frame->expr;
  if (ixs_node_is_integer_valued(node))
    return bounds_proof_complete_exact(query, true);
  switch (node->tag) {
  case IXS_MUL:
    return bounds_exact_proof_start_integer_mul(frame);
  case IXS_ADD:
    return bounds_exact_proof_start_integer_add(query, frame);
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
    if (node->u.assoc.nargs < 2 || !node->u.assoc.args) {
      return IXS_QUERY_WALK_STOP;
    }
    frame->index = 0;
    frame->stage = BOUNDS_PROOF_INTEGER_ASSOC_SCAN;
    return IXS_QUERY_WALK_ADVANCED;
  case IXS_PIECEWISE:
    if (node->u.pw.ncases == 0 || !node->u.pw.cases) {
      return IXS_QUERY_WALK_STOP;
    }
    frame->index = 0;
    frame->stage = BOUNDS_PROOF_INTEGER_PW_SCAN;
    return IXS_QUERY_WALK_ADVANCED;
  case IXS_MOD:
    if (!node->u.binary.lhs || !node->u.binary.rhs) {
      return IXS_QUERY_WALK_STOP;
    }
    frame->stage = BOUNDS_PROOF_INTEGER_MOD_LHS;
    return bounds_exact_proof_push(query, node->u.binary.lhs,
                                   BOUNDS_PROOF_INTEGER, 0);
  default:
    return bounds_proof_complete_exact(query, false);
  }
}

static ixs_query_walk_step
bounds_exact_proof_start_divisible(bounds_proof_query *query,
                                   bounds_exact_proof_frame *frame) {
  frame->stage = BOUNDS_PROOF_DIVISIBLE_INTEGER;
  return bounds_exact_proof_push(query, frame->expr, BOUNDS_PROOF_INTEGER, 0);
}

static ixs_query_walk_step
bounds_exact_proof_resume_integer_mul(bounds_proof_query *query,
                                      bounds_exact_proof_frame *frame) {
  ixs_node *node = frame->expr;
  if (frame->stage == BOUNDS_PROOF_INTEGER_MUL_SCAN) {
    if (frame->index != 0 && !query->child_success)
      return bounds_proof_complete_exact(query, false);
    if (frame->index == node->u.mul.nfactors)
      return bounds_proof_complete_exact(query, true);
    if (!node->u.mul.factors[frame->index].base ||
        node->u.mul.factors[frame->index].exp <= 0) {
      if (!node->u.mul.factors[frame->index].base)
        return IXS_QUERY_WALK_STOP;
      return bounds_proof_complete_exact(query, false);
    }
    frame->index++;
    return bounds_exact_proof_push(query,
                                   node->u.mul.factors[frame->index - 1u].base,
                                   BOUNDS_PROOF_INTEGER, 0);
  }
  if (frame->stage == BOUNDS_PROOF_INTEGER_MUL_RATIONAL_RESIDUE) {
    ixs_node *base = node->u.mul.factors[frame->index].base;
    if (query->child_success) {
      if (query->child_residue == 0u)
        frame->denominator_cancelled = true;
      frame->index++;
      frame->stage = BOUNDS_PROOF_INTEGER_MUL_RATIONAL_SCAN;
      return IXS_QUERY_WALK_ADVANCED;
    }
    frame->stage = BOUNDS_PROOF_INTEGER_MUL_RATIONAL_INTEGER;
    return bounds_exact_proof_push(query, base, BOUNDS_PROOF_INTEGER, 0);
  }
  if (frame->stage == BOUNDS_PROOF_INTEGER_MUL_RATIONAL_INTEGER) {
    if (!query->child_success)
      return bounds_proof_complete_exact(query, false);
    frame->index++;
    frame->stage = BOUNDS_PROOF_INTEGER_MUL_RATIONAL_SCAN;
    return IXS_QUERY_WALK_ADVANCED;
  }
  if (frame->index == node->u.mul.nfactors)
    return bounds_proof_complete_exact(query, frame->denominator_cancelled);
  if (!node->u.mul.factors[frame->index].base ||
      node->u.mul.factors[frame->index].exp <= 0) {
    if (!node->u.mul.factors[frame->index].base)
      return IXS_QUERY_WALK_STOP;
    return bounds_proof_complete_exact(query, false);
  }
  if (frame->denominator_cancelled) {
    frame->stage = BOUNDS_PROOF_INTEGER_MUL_RATIONAL_INTEGER;
    return bounds_exact_proof_push(
        query, node->u.mul.factors[frame->index].base, BOUNDS_PROOF_INTEGER, 0);
  }
  frame->stage = BOUNDS_PROOF_INTEGER_MUL_RATIONAL_RESIDUE;
  return bounds_proof_push_residue(query, query->active_bounds,
                                   node->u.mul.factors[frame->index].base,
                                   frame->denominator);
}

static ixs_query_walk_step
bounds_exact_proof_resume_integer_add(bounds_proof_query *query,
                                      bounds_exact_proof_frame *frame) {
  ixs_node *node = frame->expr;
  if (frame->stage == BOUNDS_PROOF_INTEGER_ADD_RESIDUE)
    return bounds_proof_complete_exact(query, query->child_success &&
                                                  query->child_residue == 0u);
  if (frame->stage == BOUNDS_PROOF_INTEGER_ADD_INTEGER) {
    if (!query->child_success)
      return bounds_proof_complete_exact(query, false);
    frame->index++;
    frame->stage = BOUNDS_PROOF_INTEGER_ADD_SCAN;
  } else if (frame->stage == BOUNDS_PROOF_INTEGER_ADD_DIVISIBLE) {
    if (!query->child_success) {
      frame->stage = BOUNDS_PROOF_INTEGER_ADD_RESIDUE;
      return bounds_proof_push_residue(query, query->active_bounds, node, 1u);
    }
    frame->index++;
    frame->stage = BOUNDS_PROOF_INTEGER_ADD_SCAN;
  }
  if (frame->index == node->u.add.nterms)
    return bounds_proof_complete_exact(query, true);
  {
    const ixs_addterm *term = &node->u.add.terms[frame->index];
    int64_t p;
    int64_t q;
    int64_t divisor;
    if (!term->term || !bounds_exact_proof_rational(term->coeff, &p, &q)) {
      return IXS_QUERY_WALK_STOP;
    }
    if (q == 1) {
      frame->stage = BOUNDS_PROOF_INTEGER_ADD_INTEGER;
      return bounds_exact_proof_push(query, term->term, BOUNDS_PROOF_INTEGER,
                                     0);
    }
    divisor = ixs_gcd(p, q);
    if (divisor <= 0 || q % divisor != 0) {
      return IXS_QUERY_WALK_STOP;
    }
    frame->stage = BOUNDS_PROOF_INTEGER_ADD_DIVISIBLE;
    return bounds_exact_proof_push(query, term->term, BOUNDS_PROOF_DIVISIBLE,
                                   q / divisor);
  }
}

static ixs_query_walk_step
bounds_exact_proof_resume_integer_assoc(bounds_proof_query *query,
                                        bounds_exact_proof_frame *frame) {
  ixs_node *node = frame->expr;
  if (frame->index != 0 && !query->child_success)
    return bounds_proof_complete_exact(query, false);
  if (frame->index == node->u.assoc.nargs)
    return bounds_proof_complete_exact(query, true);
  if (!node->u.assoc.args[frame->index]) {
    return IXS_QUERY_WALK_STOP;
  }
  frame->index++;
  return bounds_exact_proof_push(query, node->u.assoc.args[frame->index - 1u],
                                 BOUNDS_PROOF_INTEGER, 0);
}

static ixs_query_walk_step
bounds_exact_proof_resume_integer_piecewise(bounds_proof_query *query,
                                            bounds_exact_proof_frame *frame) {
  ixs_node *node = frame->expr;
  if (frame->stage == BOUNDS_PROOF_INTEGER_PW_CHILD) {
    if (!query->child_success)
      return bounds_proof_complete_exact(query, false);
    if (frame->terminal_branch)
      return bounds_proof_complete_exact(query, true);
    frame->index++;
    frame->stage = BOUNDS_PROOF_INTEGER_PW_SCAN;
  }
  while (frame->index < node->u.pw.ncases) {
    ixs_node *cond = node->u.pw.cases[frame->index].cond;
    ixs_node *value = node->u.pw.cases[frame->index].value;
    ixs_check_result truth = IXS_CHECK_UNKNOWN;
    if (!cond || !value) {
      return IXS_QUERY_WALK_STOP;
    }
    if (ixs_node_is_known_false(cond))
      truth = IXS_CHECK_FALSE;
    else if (ixs_node_is_known_true(cond))
      truth = IXS_CHECK_TRUE;
    else if (cond->tag == IXS_CMP)
      truth = ixs_bounds_check(query->active_bounds, cond);
    if (query->active_bounds->oom)
      return IXS_QUERY_WALK_OOM;
    if (truth == IXS_CHECK_FALSE) {
      frame->index++;
      continue;
    }
    frame->reachable = true;
    frame->terminal_branch = truth == IXS_CHECK_TRUE;
    frame->stage = BOUNDS_PROOF_INTEGER_PW_CHILD;
    return bounds_exact_proof_push(query, value, BOUNDS_PROOF_INTEGER, 0);
  }
  return bounds_proof_complete_exact(query, frame->reachable);
}

static ixs_query_walk_step
bounds_exact_proof_resume_integer_mod(bounds_proof_query *query,
                                      bounds_exact_proof_frame *frame) {
  if (frame->stage == BOUNDS_PROOF_INTEGER_MOD_LHS) {
    if (!query->child_success)
      return bounds_proof_complete_exact(query, false);
    frame->stage = BOUNDS_PROOF_INTEGER_MOD_RHS;
    return bounds_exact_proof_push(query, frame->expr->u.binary.rhs,
                                   BOUNDS_PROOF_INTEGER, 0);
  }
  return bounds_proof_complete_exact(query, query->child_success);
}

static ixs_query_walk_step
bounds_exact_proof_resume_divisible(bounds_proof_query *query,
                                    bounds_exact_proof_frame *frame) {
  if (frame->stage == BOUNDS_PROOF_DIVISIBLE_INTEGER) {
    if (!query->child_success)
      return bounds_proof_complete_exact(query, false);
    frame->stage = BOUNDS_PROOF_DIVISIBLE_RESIDUE;
    return bounds_proof_push_residue(query, query->active_bounds, frame->expr,
                                     frame->modulus);
  }
  return bounds_proof_complete_exact(query, query->child_success &&
                                                query->child_residue == 0u);
}

static ixs_query_walk_step
bounds_exact_proof_resume(bounds_proof_query *query,
                          bounds_exact_proof_frame *frame) {
  switch (frame->stage) {
  case BOUNDS_PROOF_INTEGER_MUL_SCAN:
  case BOUNDS_PROOF_INTEGER_MUL_RATIONAL_SCAN:
  case BOUNDS_PROOF_INTEGER_MUL_RATIONAL_RESIDUE:
  case BOUNDS_PROOF_INTEGER_MUL_RATIONAL_INTEGER:
    return bounds_exact_proof_resume_integer_mul(query, frame);
  case BOUNDS_PROOF_INTEGER_ADD_SCAN:
  case BOUNDS_PROOF_INTEGER_ADD_INTEGER:
  case BOUNDS_PROOF_INTEGER_ADD_DIVISIBLE:
  case BOUNDS_PROOF_INTEGER_ADD_RESIDUE:
    return bounds_exact_proof_resume_integer_add(query, frame);
  case BOUNDS_PROOF_INTEGER_ASSOC_SCAN:
    return bounds_exact_proof_resume_integer_assoc(query, frame);
  case BOUNDS_PROOF_INTEGER_PW_SCAN:
  case BOUNDS_PROOF_INTEGER_PW_CHILD:
    return bounds_exact_proof_resume_integer_piecewise(query, frame);
  case BOUNDS_PROOF_INTEGER_MOD_LHS:
  case BOUNDS_PROOF_INTEGER_MOD_RHS:
    return bounds_exact_proof_resume_integer_mod(query, frame);
  case BOUNDS_PROOF_DIVISIBLE_INTEGER:
  case BOUNDS_PROOF_DIVISIBLE_RESIDUE:
    return bounds_exact_proof_resume_divisible(query, frame);
  case BOUNDS_EXACT_PROOF_INITIAL:
    break;
  }
  return IXS_QUERY_WALK_STOP;
}

/* hot */
IXS_STATIC ixs_query_walk_step bounds_exact_proof_advance(
    bounds_proof_query *query, bounds_exact_proof_frame *frame) {
  if (frame->stage == BOUNDS_EXACT_PROOF_INITIAL)
    return frame->kind == BOUNDS_PROOF_INTEGER
               ? bounds_exact_proof_start_integer(query, frame)
               : bounds_exact_proof_start_divisible(query, frame);
  return bounds_exact_proof_resume(query, frame);
}

IXS_STATIC ixs_query_walk_step bounds_proof_drive(bounds_proof_query *query,
                                                  ixs_query_walk_step step) {
  while (step == IXS_QUERY_WALK_ADVANCED && query->depth != 0u) {
    if (query->top_kind == BOUNDS_PROOF_FRAME_EXACT) {
      step = bounds_exact_proof_advance(
          query, &query->exact_frames[query->exact_count - 1u]);
    } else if (query->top_kind == BOUNDS_PROOF_FRAME_RESIDUE) {
      step = bounds_residue_advance(
          query, &query->residue_frames[query->residue_count - 1u]);
    } else {
      step = IXS_QUERY_WALK_STOP;
    }
  }
  if (step == IXS_QUERY_WALK_ADVANCED)
    return step;
  while (query->depth != 0u) {
    if (query->top_kind == BOUNDS_PROOF_FRAME_RESIDUE) {
      bounds_residue_abort(query,
                           &query->residue_frames[query->residue_count - 1u]);
    } else if (query->top_kind == BOUNDS_PROOF_FRAME_EXACT) {
      (void)bounds_proof_complete_exact(query, false);
    } else {
      break;
    }
  }
  return step;
}

/* Integer, divisibility, and residue obligations share one iterative graph.
 * Exact frames stay inline through depth 16; residue frames retain their
 * separate typed pool and allocation cutoff.  Expected work is O(V + E) over
 * distinct (bounds, node, relation, modulus) obligations. */
static bool bounds_exact_proof_eval(ixs_bounds *b, ixs_node *expr,
                                    bounds_proof_kind kind, int64_t modulus) {
  ixs_arena_mark mark;
  bounds_proof_query query;
  ixs_query_walk_step step;
  bool result = false;
  if (!b || !expr || b->oom || (kind == BOUNDS_PROOF_DIVISIBLE && modulus <= 0))
    return false;
  if (ixs_node_is_integer_valued(expr) &&
      (kind == BOUNDS_PROOF_INTEGER || modulus == 1))
    return true;
  /* Predicate and interval domains can ask an exact question while resolving
   * one Piecewise condition.  One nested evaluator preserves that precision;
   * the second re-entry is a conservative miss, making the cross-domain C
   * call depth statically at most two while each evaluator remains iterative.
   */
  if (b->exact_proof_call_depth >= 2u)
    return false;
  b->exact_proof_call_depth++;
  mark = ixs_arena_save(b->scratch);
  bounds_proof_query_init(&query, b, true);
  step = bounds_proof_push_exact(&query, b, expr, kind, (uint64_t)modulus);
  step = bounds_proof_drive(&query, step);
  if (step == IXS_QUERY_WALK_OOM || b->oom) {
    b->oom = true;
    bounds_query_note_oom(b);
  } else if (step == IXS_QUERY_WALK_STOP) {
    bounds_query_note_invalid(b);
  } else {
    result = query.child_success;
  }
  ixs_arena_restore(b->scratch, mark);
  b->exact_proof_call_depth--;
  return result;
}

IXS_STATIC bool ixs_bounds_is_known_divisible(ixs_bounds *b, ixs_node *expr,
                                              int64_t m) {
  return bounds_exact_proof_eval(b, expr, BOUNDS_PROOF_DIVISIBLE, m);
}

IXS_STATIC bool ixs_bounds_is_integer_with_divinfo(ixs_bounds *b,
                                                   ixs_node *expr) {
  return bounds_exact_proof_eval(b, expr, BOUNDS_PROOF_INTEGER, 0);
}

IXS_STATIC ixs_check_result
bounds_integer_check_without_equality(ixs_bounds *b, ixs_node *expr) {
  ixs_interval iv;
  bool proven;
  assert(b->equality_disabled_depth != UINT_MAX);
  b->equality_disabled_depth++;
  proven = ixs_bounds_is_integer_with_divinfo(b, expr);
  if (proven) {
    b->equality_disabled_depth--;
    return IXS_CHECK_TRUE;
  }
  iv = bounds_get_intrinsic(b, expr);
  b->equality_disabled_depth--;
  if (b->oom || !iv.valid || iv.lo_inf || iv.hi_inf ||
      ixs_rat_cmp(iv.lo_p, iv.lo_q, iv.hi_p, iv.hi_q) != 0)
    return IXS_CHECK_UNKNOWN;
  return iv.lo_q == 1 ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
}
