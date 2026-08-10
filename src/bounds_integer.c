/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds_integer.h"

#include "bounds.h"
#include "bounds_bitfacts.h"
#include "bounds_query.h"
#include "bounds_store.h"
#include "hash.h"
#include "query_walk.h"
#include "rational.h"

#include <assert.h>
#include <limits.h>
#include <stdint.h>
#include <string.h>

typedef enum {
  BOUNDS_EXACT_PROOF_INTEGER,
  BOUNDS_EXACT_PROOF_DIVISIBLE
} bounds_exact_proof_kind;

typedef enum {
  BOUNDS_EXACT_PROOF_INITIAL,
  BOUNDS_EXACT_PROOF_INTEGER_MUL_SCAN,
  BOUNDS_EXACT_PROOF_INTEGER_MUL_RATIONAL_SCAN,
  BOUNDS_EXACT_PROOF_INTEGER_MUL_RATIONAL_DIVISIBLE,
  BOUNDS_EXACT_PROOF_INTEGER_MUL_RATIONAL_INTEGER,
  BOUNDS_EXACT_PROOF_INTEGER_ADD_SCAN,
  BOUNDS_EXACT_PROOF_INTEGER_ADD_INTEGER,
  BOUNDS_EXACT_PROOF_INTEGER_ADD_DIVISIBLE,
  BOUNDS_EXACT_PROOF_INTEGER_ASSOC_SCAN,
  BOUNDS_EXACT_PROOF_INTEGER_PW_SCAN,
  BOUNDS_EXACT_PROOF_INTEGER_PW_CHILD,
  BOUNDS_EXACT_PROOF_INTEGER_MOD_LHS,
  BOUNDS_EXACT_PROOF_INTEGER_MOD_RHS,
  BOUNDS_EXACT_PROOF_DIVISIBLE_ADD_SCAN,
  BOUNDS_EXACT_PROOF_DIVISIBLE_ADD_CHILD,
  BOUNDS_EXACT_PROOF_DIVISIBLE_MUL_INTEGER_SCAN,
  BOUNDS_EXACT_PROOF_DIVISIBLE_MUL_FACTOR_SCAN,
  BOUNDS_EXACT_PROOF_DIVISIBLE_MUL_FACTOR_CHILD,
  BOUNDS_EXACT_PROOF_DIVISIBLE_ASSOC_SCAN
} bounds_exact_proof_stage;

typedef struct {
  ixs_node *expr;
  int64_t modulus;
  bounds_exact_proof_kind kind;
  bool result;
  bool active;
  bool complete;
} bounds_exact_proof_memo_entry;

typedef struct {
  bounds_exact_proof_memo_entry *entries;
  size_t count;
  size_t capacity;
} bounds_exact_proof_memo;

typedef struct {
  ixs_node *expr;
  int64_t modulus;
  int64_t denominator;
  uint32_t index;
  bounds_exact_proof_kind kind;
  bounds_exact_proof_stage stage;
  bool denominator_cancelled;
  bool reachable;
  bool terminal_branch;
} bounds_exact_proof_frame;

typedef struct {
  ixs_bounds *bounds;
  ixs_query_walk walk;
  bounds_exact_proof_memo memo;
  bool child_result;
  bool stack_oom;
  bounds_exact_proof_frame inline_frames[16];
  bounds_exact_proof_memo_entry inline_memo[32];
} bounds_exact_proof_query;

static size_t bounds_exact_proof_hash(ixs_node *expr,
                                      bounds_exact_proof_kind kind,
                                      int64_t modulus) {
  size_t hash = ixs_hash_ptr(expr);
  hash ^= (size_t)(uint64_t)modulus + (hash << 6u) + (hash >> 2u);
  hash ^= (size_t)kind + (hash << 6u) + (hash >> 2u);
  return hash;
}

static bool bounds_exact_proof_memo_grow(bounds_exact_proof_query *query) {
  size_t capacity = query->memo.capacity ? query->memo.capacity * 2u : 32u;
  bounds_exact_proof_memo_entry *grown;
  size_t i;
  if (capacity <= query->memo.capacity || capacity > SIZE_MAX / sizeof(*grown))
    return false;
  grown = ixs_arena_alloc(query->bounds->scratch, capacity * sizeof(*grown),
                          sizeof(void *));
  if (!grown)
    return false;
  memset(grown, 0, capacity * sizeof(*grown));
  for (i = 0; i < query->memo.capacity; i++) {
    bounds_exact_proof_memo_entry entry = query->memo.entries[i];
    size_t slot;
    if (!entry.expr)
      continue;
    slot = bounds_exact_proof_hash(entry.expr, entry.kind, entry.modulus) &
           (capacity - 1u);
    while (grown[slot].expr)
      slot = (slot + 1u) & (capacity - 1u);
    grown[slot] = entry;
  }
  query->memo.entries = grown;
  query->memo.capacity = capacity;
  return true;
}

static bounds_exact_proof_memo_entry *
bounds_exact_proof_memo_get(bounds_exact_proof_query *query, ixs_node *expr,
                            bounds_exact_proof_kind kind, int64_t modulus,
                            bool create) {
  size_t slot;
  if (create && (!query->memo.capacity ||
                 query->memo.count + 1u > query->memo.capacity / 2u)) {
    if (!bounds_exact_proof_memo_grow(query))
      return NULL;
  }
  if (!query->memo.capacity)
    return NULL;
  slot = bounds_exact_proof_hash(expr, kind, modulus) &
         (query->memo.capacity - 1u);
  while (query->memo.entries[slot].expr &&
         (query->memo.entries[slot].expr != expr ||
          query->memo.entries[slot].kind != kind ||
          query->memo.entries[slot].modulus != modulus))
    slot = (slot + 1u) & (query->memo.capacity - 1u);
  if (!query->memo.entries[slot].expr) {
    if (!create)
      return NULL;
    query->memo.entries[slot].expr = expr;
    query->memo.entries[slot].kind = kind;
    query->memo.entries[slot].modulus = modulus;
    query->memo.count++;
  }
  return &query->memo.entries[slot];
}

static ixs_query_walk_step
bounds_exact_proof_push(bounds_exact_proof_query *query, ixs_node *expr,
                        bounds_exact_proof_kind kind, int64_t modulus) {
  bounds_exact_proof_memo_entry *entry;
  bounds_exact_proof_frame *frame;
  ixs_query_walk_step step;
  if (!expr || (kind == BOUNDS_EXACT_PROOF_DIVISIBLE && modulus <= 0)) {
    return IXS_QUERY_WALK_STOP;
  }
  entry = bounds_exact_proof_memo_get(query, expr, kind, modulus, true);
  if (!entry)
    return IXS_QUERY_WALK_OOM;
  if (entry->active) {
    return IXS_QUERY_WALK_STOP;
  }
  if (entry->complete) {
    query->child_result = entry->result;
    return IXS_QUERY_WALK_ADVANCED;
  }
  step = ixs_query_walk_push(&query->walk, expr);
  if (step != IXS_QUERY_WALK_ADVANCED)
    return step;
  frame = IXS_QUERY_WALK_TOP(&query->walk);
  frame->kind = kind;
  frame->modulus = modulus;
  frame->stage = BOUNDS_EXACT_PROOF_INITIAL;
  entry->active = true;
  return IXS_QUERY_WALK_ADVANCED;
}

static ixs_query_walk_step
bounds_exact_proof_complete(bounds_exact_proof_query *query, bool result) {
  bounds_exact_proof_frame *frame = IXS_QUERY_WALK_TOP(&query->walk);
  bounds_exact_proof_memo_entry *entry = bounds_exact_proof_memo_get(
      query, frame->expr, frame->kind, frame->modulus, false);
  if (!entry || !entry->active) {
    return IXS_QUERY_WALK_STOP;
  }
  entry->result = result;
  entry->active = false;
  entry->complete = true;
  IXS_QUERY_WALK_POP(&query->walk);
  query->child_result = result;
  return IXS_QUERY_WALK_ADVANCED;
}

static bool bounds_exact_proof_rational(ixs_node *node, int64_t *p,
                                        int64_t *q) {
  if (!node || (node->tag != IXS_INT && node->tag != IXS_RAT))
    return false;
  ixs_node_get_rat(node, p, q);
  return *q > 0;
}

static ixs_query_walk_step
bounds_exact_proof_divisible_after_add(bounds_exact_proof_query *query,
                                       bounds_exact_proof_frame *frame) {
  ixs_bitfacts bits;
  uint64_t mask;
  if (ixs_int64_is_positive_pow2(frame->modulus)) {
    mask = (uint64_t)frame->modulus - 1u;
    if (ixs_bounds_get_bitfacts(query->bounds, frame->expr, &bits) &&
        (bits.known_zero & mask) == mask)
      return bounds_exact_proof_complete(query, true);
    if (query->bounds->oom)
      return IXS_QUERY_WALK_OOM;
  }
  return bounds_exact_proof_complete(query, false);
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
    frame->stage = BOUNDS_EXACT_PROOF_INTEGER_MUL_SCAN;
    return IXS_QUERY_WALK_ADVANCED;
  }
  divisor = ixs_gcd(p, q);
  if (divisor <= 0 || q % divisor != 0) {
    return IXS_QUERY_WALK_STOP;
  }
  frame->denominator = q / divisor;
  frame->denominator_cancelled = frame->denominator == 1;
  frame->stage = BOUNDS_EXACT_PROOF_INTEGER_MUL_RATIONAL_SCAN;
  return IXS_QUERY_WALK_ADVANCED;
}

static ixs_query_walk_step
bounds_exact_proof_start_integer_add(bounds_exact_proof_query *query,
                                     bounds_exact_proof_frame *frame) {
  int64_t p;
  int64_t q;
  ixs_node *node = frame->expr;
  if (!bounds_exact_proof_rational(node->u.add.coeff, &p, &q) ||
      (node->u.add.nterms != 0 && !node->u.add.terms)) {
    return IXS_QUERY_WALK_STOP;
  }
  (void)p;
  if (q != 1)
    return bounds_exact_proof_complete(
        query, bounds_add_known_divisible(query->bounds, node, 1));
  frame->index = 0;
  frame->stage = BOUNDS_EXACT_PROOF_INTEGER_ADD_SCAN;
  return IXS_QUERY_WALK_ADVANCED;
}

static ixs_query_walk_step
bounds_exact_proof_start_integer(bounds_exact_proof_query *query,
                                 bounds_exact_proof_frame *frame) {
  ixs_node *node = frame->expr;
  if (ixs_node_is_integer_valued(node))
    return bounds_exact_proof_complete(query, true);
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
    frame->stage = BOUNDS_EXACT_PROOF_INTEGER_ASSOC_SCAN;
    return IXS_QUERY_WALK_ADVANCED;
  case IXS_PIECEWISE:
    if (node->u.pw.ncases == 0 || !node->u.pw.cases) {
      return IXS_QUERY_WALK_STOP;
    }
    frame->index = 0;
    frame->stage = BOUNDS_EXACT_PROOF_INTEGER_PW_SCAN;
    return IXS_QUERY_WALK_ADVANCED;
  case IXS_MOD:
    if (!node->u.binary.lhs || !node->u.binary.rhs) {
      return IXS_QUERY_WALK_STOP;
    }
    frame->stage = BOUNDS_EXACT_PROOF_INTEGER_MOD_LHS;
    return bounds_exact_proof_push(query, node->u.binary.lhs,
                                   BOUNDS_EXACT_PROOF_INTEGER, 0);
  default:
    return bounds_exact_proof_complete(query, false);
  }
}

static ixs_query_walk_step
bounds_exact_proof_start_divisible_add(bounds_exact_proof_query *query,
                                       bounds_exact_proof_frame *frame) {
  int64_t p;
  int64_t q;
  ixs_node *node = frame->expr;
  if (!bounds_exact_proof_rational(node->u.add.coeff, &p, &q) ||
      (node->u.add.nterms != 0 && !node->u.add.terms)) {
    return IXS_QUERY_WALK_STOP;
  }
  if (q != 1) {
    if (bounds_add_known_divisible(query->bounds, node, frame->modulus))
      return bounds_exact_proof_complete(query, true);
    if (query->bounds->oom)
      return IXS_QUERY_WALK_OOM;
    return bounds_exact_proof_divisible_after_add(query, frame);
  }
  if (p % frame->modulus != 0)
    return bounds_exact_proof_divisible_after_add(query, frame);
  frame->index = 0;
  frame->stage = BOUNDS_EXACT_PROOF_DIVISIBLE_ADD_SCAN;
  return IXS_QUERY_WALK_ADVANCED;
}

static ixs_query_walk_step
bounds_exact_proof_start_divisible_mul(bounds_exact_proof_query *query,
                                       bounds_exact_proof_frame *frame) {
  ixs_node *node = frame->expr;
  if (!node->u.mul.coeff || node->u.mul.coeff->tag != IXS_INT ||
      (node->u.mul.nfactors != 0 && !node->u.mul.factors)) {
    return IXS_QUERY_WALK_STOP;
  }
  if (node->u.mul.coeff->u.ival == 0)
    return bounds_exact_proof_complete(query, true);
  frame->index = 0;
  frame->stage = BOUNDS_EXACT_PROOF_DIVISIBLE_MUL_INTEGER_SCAN;
  return IXS_QUERY_WALK_ADVANCED;
}

static ixs_query_walk_step
bounds_exact_proof_start_divisible(bounds_exact_proof_query *query,
                                   bounds_exact_proof_frame *frame) {
  ixs_node *node = frame->expr;
  ixs_bitfacts bits;
  int64_t symbol_modulus, symbol_remainder;
  uint64_t mask;
  if (frame->modulus == 1) {
    if (ixs_node_is_integer_valued(node))
      return bounds_exact_proof_complete(query, true);
    frame->stage = BOUNDS_EXACT_PROOF_DIVISIBLE_ASSOC_SCAN;
    frame->index = UINT32_MAX;
    return bounds_exact_proof_push(query, node, BOUNDS_EXACT_PROOF_INTEGER, 0);
  }
  if (node->tag == IXS_ADD)
    return bounds_exact_proof_start_divisible_add(query, frame);
  if (ixs_int64_is_positive_pow2(frame->modulus)) {
    mask = (uint64_t)frame->modulus - 1u;
    if (ixs_bounds_get_bitfacts(query->bounds, node, &bits) &&
        (bits.known_zero & mask) == mask)
      return bounds_exact_proof_complete(query, true);
    if (query->bounds->oom)
      return IXS_QUERY_WALK_OOM;
  }
  switch (node->tag) {
  case IXS_INT:
    return bounds_exact_proof_complete(query,
                                       node->u.ival % frame->modulus == 0);
  case IXS_SYM:
    if (!node->u.name) {
      return IXS_QUERY_WALK_STOP;
    }
    return bounds_exact_proof_complete(
        query, bounds_store_get_modrem(query->bounds, node->u.name,
                                       &symbol_modulus, &symbol_remainder) &&
                   symbol_modulus % frame->modulus == 0 &&
                   symbol_remainder % frame->modulus == 0);
  case IXS_MUL:
    if (node->u.mul.coeff && node->u.mul.coeff->tag == IXS_INT)
      return bounds_exact_proof_start_divisible_mul(query, frame);
    return bounds_exact_proof_complete(query, false);
  case IXS_MAX:
  case IXS_MIN:
    if (node->u.assoc.nargs == 0 || !node->u.assoc.args) {
      return IXS_QUERY_WALK_STOP;
    }
    frame->index = 0;
    frame->stage = BOUNDS_EXACT_PROOF_DIVISIBLE_ASSOC_SCAN;
    return IXS_QUERY_WALK_ADVANCED;
  default:
    return bounds_exact_proof_complete(query, false);
  }
}

static ixs_query_walk_step
bounds_exact_proof_resume_integer_mul(bounds_exact_proof_query *query,
                                      bounds_exact_proof_frame *frame) {
  ixs_node *node = frame->expr;
  if (frame->stage == BOUNDS_EXACT_PROOF_INTEGER_MUL_SCAN) {
    if (frame->index != 0 && !query->child_result)
      return bounds_exact_proof_complete(query, false);
    if (frame->index == node->u.mul.nfactors)
      return bounds_exact_proof_complete(query, true);
    if (!node->u.mul.factors[frame->index].base ||
        node->u.mul.factors[frame->index].exp <= 0) {
      if (!node->u.mul.factors[frame->index].base)
        return IXS_QUERY_WALK_STOP;
      return bounds_exact_proof_complete(query, false);
    }
    frame->index++;
    return bounds_exact_proof_push(query,
                                   node->u.mul.factors[frame->index - 1u].base,
                                   BOUNDS_EXACT_PROOF_INTEGER, 0);
  }
  if (frame->stage == BOUNDS_EXACT_PROOF_INTEGER_MUL_RATIONAL_DIVISIBLE) {
    ixs_node *base = node->u.mul.factors[frame->index].base;
    uint64_t residue = 0;
    bool known;
    if (query->child_result) {
      frame->denominator_cancelled = true;
      frame->index++;
      frame->stage = BOUNDS_EXACT_PROOF_INTEGER_MUL_RATIONAL_SCAN;
      return IXS_QUERY_WALK_ADVANCED;
    }
    known = bounds_known_residue_independent(
        query->bounds, base, (uint64_t)frame->denominator, &residue);
    if (query->bounds->oom)
      return IXS_QUERY_WALK_OOM;
    if (known) {
      if (residue == 0)
        frame->denominator_cancelled = true;
      frame->index++;
      frame->stage = BOUNDS_EXACT_PROOF_INTEGER_MUL_RATIONAL_SCAN;
      return IXS_QUERY_WALK_ADVANCED;
    }
    frame->stage = BOUNDS_EXACT_PROOF_INTEGER_MUL_RATIONAL_INTEGER;
    return bounds_exact_proof_push(query, base, BOUNDS_EXACT_PROOF_INTEGER, 0);
  }
  if (frame->stage == BOUNDS_EXACT_PROOF_INTEGER_MUL_RATIONAL_INTEGER) {
    if (!query->child_result)
      return bounds_exact_proof_complete(query, false);
    frame->index++;
    frame->stage = BOUNDS_EXACT_PROOF_INTEGER_MUL_RATIONAL_SCAN;
    return IXS_QUERY_WALK_ADVANCED;
  }
  if (frame->index == node->u.mul.nfactors)
    return bounds_exact_proof_complete(query, frame->denominator_cancelled);
  if (!node->u.mul.factors[frame->index].base ||
      node->u.mul.factors[frame->index].exp <= 0) {
    if (!node->u.mul.factors[frame->index].base)
      return IXS_QUERY_WALK_STOP;
    return bounds_exact_proof_complete(query, false);
  }
  if (frame->denominator_cancelled) {
    frame->stage = BOUNDS_EXACT_PROOF_INTEGER_MUL_RATIONAL_INTEGER;
    return bounds_exact_proof_push(query,
                                   node->u.mul.factors[frame->index].base,
                                   BOUNDS_EXACT_PROOF_INTEGER, 0);
  }
  frame->stage = BOUNDS_EXACT_PROOF_INTEGER_MUL_RATIONAL_DIVISIBLE;
  return bounds_exact_proof_push(query, node->u.mul.factors[frame->index].base,
                                 BOUNDS_EXACT_PROOF_DIVISIBLE,
                                 frame->denominator);
}

static ixs_query_walk_step
bounds_exact_proof_resume_integer_add(bounds_exact_proof_query *query,
                                      bounds_exact_proof_frame *frame) {
  ixs_node *node = frame->expr;
  if (frame->stage == BOUNDS_EXACT_PROOF_INTEGER_ADD_INTEGER) {
    if (!query->child_result)
      return bounds_exact_proof_complete(query, false);
    frame->index++;
    frame->stage = BOUNDS_EXACT_PROOF_INTEGER_ADD_SCAN;
  } else if (frame->stage == BOUNDS_EXACT_PROOF_INTEGER_ADD_DIVISIBLE) {
    if (!query->child_result)
      return bounds_exact_proof_complete(
          query, bounds_add_known_divisible(query->bounds, node, 1));
    frame->index++;
    frame->stage = BOUNDS_EXACT_PROOF_INTEGER_ADD_SCAN;
  }
  if (frame->index == node->u.add.nterms)
    return bounds_exact_proof_complete(query, true);
  {
    const ixs_addterm *term = &node->u.add.terms[frame->index];
    int64_t p;
    int64_t q;
    int64_t divisor;
    if (!term->term || !bounds_exact_proof_rational(term->coeff, &p, &q)) {
      return IXS_QUERY_WALK_STOP;
    }
    if (q == 1) {
      frame->stage = BOUNDS_EXACT_PROOF_INTEGER_ADD_INTEGER;
      return bounds_exact_proof_push(query, term->term,
                                     BOUNDS_EXACT_PROOF_INTEGER, 0);
    }
    divisor = ixs_gcd(p, q);
    if (divisor <= 0 || q % divisor != 0) {
      return IXS_QUERY_WALK_STOP;
    }
    frame->stage = BOUNDS_EXACT_PROOF_INTEGER_ADD_DIVISIBLE;
    return bounds_exact_proof_push(query, term->term,
                                   BOUNDS_EXACT_PROOF_DIVISIBLE, q / divisor);
  }
}

static ixs_query_walk_step
bounds_exact_proof_resume_integer_assoc(bounds_exact_proof_query *query,
                                        bounds_exact_proof_frame *frame) {
  ixs_node *node = frame->expr;
  if (frame->index != 0 && !query->child_result)
    return bounds_exact_proof_complete(query, false);
  if (frame->index == node->u.assoc.nargs)
    return bounds_exact_proof_complete(query, true);
  if (!node->u.assoc.args[frame->index]) {
    return IXS_QUERY_WALK_STOP;
  }
  frame->index++;
  return bounds_exact_proof_push(query, node->u.assoc.args[frame->index - 1u],
                                 BOUNDS_EXACT_PROOF_INTEGER, 0);
}

static ixs_query_walk_step
bounds_exact_proof_resume_integer_piecewise(bounds_exact_proof_query *query,
                                            bounds_exact_proof_frame *frame) {
  ixs_node *node = frame->expr;
  if (frame->stage == BOUNDS_EXACT_PROOF_INTEGER_PW_CHILD) {
    if (!query->child_result)
      return bounds_exact_proof_complete(query, false);
    if (frame->terminal_branch)
      return bounds_exact_proof_complete(query, true);
    frame->index++;
    frame->stage = BOUNDS_EXACT_PROOF_INTEGER_PW_SCAN;
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
      truth = ixs_bounds_check(query->bounds, cond);
    if (query->bounds->oom)
      return IXS_QUERY_WALK_OOM;
    if (truth == IXS_CHECK_FALSE) {
      frame->index++;
      continue;
    }
    frame->reachable = true;
    frame->terminal_branch = truth == IXS_CHECK_TRUE;
    frame->stage = BOUNDS_EXACT_PROOF_INTEGER_PW_CHILD;
    return bounds_exact_proof_push(query, value, BOUNDS_EXACT_PROOF_INTEGER, 0);
  }
  return bounds_exact_proof_complete(query, frame->reachable);
}

static ixs_query_walk_step
bounds_exact_proof_resume_integer_mod(bounds_exact_proof_query *query,
                                      bounds_exact_proof_frame *frame) {
  if (frame->stage == BOUNDS_EXACT_PROOF_INTEGER_MOD_LHS) {
    if (!query->child_result)
      return bounds_exact_proof_complete(query, false);
    frame->stage = BOUNDS_EXACT_PROOF_INTEGER_MOD_RHS;
    return bounds_exact_proof_push(query, frame->expr->u.binary.rhs,
                                   BOUNDS_EXACT_PROOF_INTEGER, 0);
  }
  return bounds_exact_proof_complete(query, query->child_result);
}

static ixs_query_walk_step
bounds_exact_proof_resume_divisible_add(bounds_exact_proof_query *query,
                                        bounds_exact_proof_frame *frame) {
  ixs_node *node = frame->expr;
  if (frame->stage == BOUNDS_EXACT_PROOF_DIVISIBLE_ADD_CHILD) {
    if (!query->child_result)
      return bounds_exact_proof_divisible_after_add(query, frame);
    frame->index++;
    frame->stage = BOUNDS_EXACT_PROOF_DIVISIBLE_ADD_SCAN;
  }
  if (frame->index == node->u.add.nterms)
    return bounds_exact_proof_complete(query, true);
  {
    const ixs_addterm *term = &node->u.add.terms[frame->index];
    int64_t p;
    int64_t q;
    int64_t divisor;
    if (!term->term || !bounds_exact_proof_rational(term->coeff, &p, &q)) {
      return IXS_QUERY_WALK_STOP;
    }
    if (q != 1) {
      if (bounds_add_known_divisible(query->bounds, node, frame->modulus))
        return bounds_exact_proof_complete(query, true);
      if (query->bounds->oom)
        return IXS_QUERY_WALK_OOM;
      return bounds_exact_proof_divisible_after_add(query, frame);
    }
    divisor = ixs_gcd(p, frame->modulus);
    if (divisor <= 0 || frame->modulus % divisor != 0) {
      return IXS_QUERY_WALK_STOP;
    }
    frame->stage = BOUNDS_EXACT_PROOF_DIVISIBLE_ADD_CHILD;
    return bounds_exact_proof_push(query, term->term,
                                   BOUNDS_EXACT_PROOF_DIVISIBLE,
                                   frame->modulus / divisor);
  }
}

static ixs_query_walk_step
bounds_exact_proof_resume_divisible_mul(bounds_exact_proof_query *query,
                                        bounds_exact_proof_frame *frame) {
  ixs_node *node = frame->expr;
  if (frame->stage == BOUNDS_EXACT_PROOF_DIVISIBLE_MUL_INTEGER_SCAN) {
    int64_t divisor;
    if (frame->index != 0 && !query->child_result)
      return bounds_exact_proof_complete(query, false);
    if (frame->index < node->u.mul.nfactors) {
      const ixs_mulfactor *factor = &node->u.mul.factors[frame->index];
      if (!factor->base || factor->exp < 0) {
        if (!factor->base)
          return IXS_QUERY_WALK_STOP;
        return bounds_exact_proof_complete(query, false);
      }
      frame->index++;
      return bounds_exact_proof_push(query, factor->base,
                                     BOUNDS_EXACT_PROOF_INTEGER, 0);
    }
    divisor = ixs_gcd(node->u.mul.coeff->u.ival, frame->modulus);
    if (divisor <= 0 || frame->modulus % divisor != 0) {
      return IXS_QUERY_WALK_STOP;
    }
    frame->denominator = frame->modulus / divisor;
    if (frame->denominator == 1)
      return bounds_exact_proof_complete(query, true);
    frame->index = 0;
    frame->stage = BOUNDS_EXACT_PROOF_DIVISIBLE_MUL_FACTOR_SCAN;
  } else if (frame->stage == BOUNDS_EXACT_PROOF_DIVISIBLE_MUL_FACTOR_CHILD) {
    if (query->child_result)
      return bounds_exact_proof_complete(query, true);
    frame->index++;
    frame->stage = BOUNDS_EXACT_PROOF_DIVISIBLE_MUL_FACTOR_SCAN;
  }
  while (frame->index < node->u.mul.nfactors &&
         node->u.mul.factors[frame->index].exp < 1)
    frame->index++;
  if (frame->index == node->u.mul.nfactors)
    return bounds_exact_proof_complete(query, false);
  frame->stage = BOUNDS_EXACT_PROOF_DIVISIBLE_MUL_FACTOR_CHILD;
  return bounds_exact_proof_push(query, node->u.mul.factors[frame->index].base,
                                 BOUNDS_EXACT_PROOF_DIVISIBLE,
                                 frame->denominator);
}

static ixs_query_walk_step
bounds_exact_proof_resume_divisible_assoc(bounds_exact_proof_query *query,
                                          bounds_exact_proof_frame *frame) {
  ixs_node *node = frame->expr;
  if (frame->index == UINT32_MAX)
    return bounds_exact_proof_complete(query, query->child_result);
  if (frame->index != 0 && !query->child_result)
    return bounds_exact_proof_complete(query, false);
  if (frame->index == node->u.assoc.nargs)
    return bounds_exact_proof_complete(query, true);
  if (!node->u.assoc.args[frame->index]) {
    return IXS_QUERY_WALK_STOP;
  }
  frame->index++;
  return bounds_exact_proof_push(query, node->u.assoc.args[frame->index - 1u],
                                 BOUNDS_EXACT_PROOF_DIVISIBLE, frame->modulus);
}

static ixs_query_walk_step
bounds_exact_proof_resume(bounds_exact_proof_query *query,
                          bounds_exact_proof_frame *frame) {
  switch (frame->stage) {
  case BOUNDS_EXACT_PROOF_INTEGER_MUL_SCAN:
  case BOUNDS_EXACT_PROOF_INTEGER_MUL_RATIONAL_SCAN:
  case BOUNDS_EXACT_PROOF_INTEGER_MUL_RATIONAL_DIVISIBLE:
  case BOUNDS_EXACT_PROOF_INTEGER_MUL_RATIONAL_INTEGER:
    return bounds_exact_proof_resume_integer_mul(query, frame);
  case BOUNDS_EXACT_PROOF_INTEGER_ADD_SCAN:
  case BOUNDS_EXACT_PROOF_INTEGER_ADD_INTEGER:
  case BOUNDS_EXACT_PROOF_INTEGER_ADD_DIVISIBLE:
    return bounds_exact_proof_resume_integer_add(query, frame);
  case BOUNDS_EXACT_PROOF_INTEGER_ASSOC_SCAN:
    return bounds_exact_proof_resume_integer_assoc(query, frame);
  case BOUNDS_EXACT_PROOF_INTEGER_PW_SCAN:
  case BOUNDS_EXACT_PROOF_INTEGER_PW_CHILD:
    return bounds_exact_proof_resume_integer_piecewise(query, frame);
  case BOUNDS_EXACT_PROOF_INTEGER_MOD_LHS:
  case BOUNDS_EXACT_PROOF_INTEGER_MOD_RHS:
    return bounds_exact_proof_resume_integer_mod(query, frame);
  case BOUNDS_EXACT_PROOF_DIVISIBLE_ADD_SCAN:
  case BOUNDS_EXACT_PROOF_DIVISIBLE_ADD_CHILD:
    return bounds_exact_proof_resume_divisible_add(query, frame);
  case BOUNDS_EXACT_PROOF_DIVISIBLE_MUL_INTEGER_SCAN:
  case BOUNDS_EXACT_PROOF_DIVISIBLE_MUL_FACTOR_SCAN:
  case BOUNDS_EXACT_PROOF_DIVISIBLE_MUL_FACTOR_CHILD:
    return bounds_exact_proof_resume_divisible_mul(query, frame);
  case BOUNDS_EXACT_PROOF_DIVISIBLE_ASSOC_SCAN:
    return bounds_exact_proof_resume_divisible_assoc(query, frame);
  case BOUNDS_EXACT_PROOF_INITIAL:
    break;
  }
  return IXS_QUERY_WALK_STOP;
}

/* hot */
static ixs_query_walk_step bounds_exact_proof_advance(void *state, void *top) {
  bounds_exact_proof_query *query = state;
  bounds_exact_proof_frame *frame = top;
  if (frame->stage == BOUNDS_EXACT_PROOF_INITIAL)
    return frame->kind == BOUNDS_EXACT_PROOF_INTEGER
               ? bounds_exact_proof_start_integer(query, frame)
               : bounds_exact_proof_start_divisible(query, frame);
  return bounds_exact_proof_resume(query, frame);
}

/* Both proof relations are one iterative dependency graph.  The common small
 * query stays in fixed local buffers; deeper stacks and larger open-addressed
 * memos grow on scratch.  Expected work is O(V + E) over distinct
 * (node, relation, modulus) obligations, and malformed cycles are rejected
 * without consuming C stack. */
static bool bounds_exact_proof_eval(ixs_bounds *b, ixs_node *expr,
                                    bounds_exact_proof_kind kind,
                                    int64_t modulus) {
  ixs_arena_mark mark;
  bounds_exact_proof_query query;
  ixs_query_walk_step step;
  bool result = false;
  if (!b || !expr || b->oom ||
      (kind == BOUNDS_EXACT_PROOF_DIVISIBLE && modulus <= 0))
    return false;
  if (ixs_node_is_integer_valued(expr) &&
      (kind == BOUNDS_EXACT_PROOF_INTEGER || modulus == 1))
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
  query.bounds = b;
  query.stack_oom = false;
  IXS_QUERY_WALK_INIT_INLINE(&query.walk, b->scratch, &query.stack_oom,
                             bounds_exact_proof_frame, expr,
                             query.inline_frames);
  query.memo.entries = query.inline_memo;
  query.memo.count = 0;
  query.memo.capacity =
      sizeof(query.inline_memo) / sizeof(query.inline_memo[0]);
  query.child_result = false;
  memset(query.inline_memo, 0, sizeof(query.inline_memo));
  step = bounds_exact_proof_push(&query, expr, kind, modulus);
  if (step == IXS_QUERY_WALK_ADVANCED)
    step = ixs_query_walk_drive(&query.walk, &query, bounds_exact_proof_advance,
                                NULL);
  if (step == IXS_QUERY_WALK_OOM || b->oom) {
    b->oom = true;
    bounds_query_note_oom(b);
  } else if (step == IXS_QUERY_WALK_STOP) {
    bounds_query_note_invalid(b);
  } else {
    result = query.child_result;
  }
  ixs_arena_restore(b->scratch, mark);
  b->exact_proof_call_depth--;
  return result;
}

IXS_STATIC bool ixs_bounds_is_known_divisible(ixs_bounds *b, ixs_node *expr,
                                              int64_t m) {
  return bounds_exact_proof_eval(b, expr, BOUNDS_EXACT_PROOF_DIVISIBLE, m);
}

IXS_STATIC bool ixs_bounds_is_integer_with_divinfo(ixs_bounds *b,
                                                   ixs_node *expr) {
  return bounds_exact_proof_eval(b, expr, BOUNDS_EXACT_PROOF_INTEGER, 0);
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
