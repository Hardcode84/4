/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds_predicate.h"
#include "bounds_assume.h"
#include "bounds_defined.h"
#include "bounds_query.h"
#include "bounds_range.h"
#include "bounds_store.h"
#include "facts_store.h"
#include "query_transaction.h"
#include "query_walk.h"
#include "simplify.h"

#include <string.h>

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

IXS_STATIC ixs_check_result bounds_predicate_not(ixs_check_result result) {
  if (result == IXS_CHECK_TRUE)
    return IXS_CHECK_FALSE;
  if (result == IXS_CHECK_FALSE)
    return IXS_CHECK_TRUE;
  return IXS_CHECK_UNKNOWN;
}

static ixs_check_result predicate_cmp_atom(ixs_bounds *bounds, ixs_node *cmp) {
  ixs_check_result result;
  /* Reflexive equality is an exact poison refinement. */
  if (cmp->u.binary.cmp_op == IXS_CMP_EQ &&
      cmp->u.binary.lhs == cmp->u.binary.rhs)
    return IXS_CHECK_TRUE;
  result = ixs_bounds_check(bounds, cmp);
  if (result == IXS_CHECK_UNKNOWN)
    result = bounds_range_check_relation_refined(bounds, cmp);
  if (result != IXS_CHECK_UNKNOWN || !ixs_node_is_zero(cmp->u.binary.rhs) ||
      (cmp->u.binary.cmp_op != IXS_CMP_EQ &&
       cmp->u.binary.cmp_op != IXS_CMP_NE) ||
      !bounds_store_contains_nonzero(bounds, cmp->u.binary.lhs))
    return result;
  return cmp->u.binary.cmp_op == IXS_CMP_NE ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
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
    return predicate_cmp_atom(bounds, node);

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
    parent->result = bounds_predicate_not(child);
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

  if (!node ||
      (node->tag != IXS_AND && node->tag != IXS_OR && node->tag != IXS_NOT))
    return predicate_query_atom(bounds, node);

  return frame->result;
}

/* hot */
static ixs_query_walk_step predicate_query_advance(void *state, void *top) {
  predicate_query *query = state;
  predicate_query_frame *frame = top;
  ixs_query_check_memo_entry *entry;
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

IXS_STATIC ixs_check_result bounds_predicate_eval(ixs_bounds *bounds,
                                                  ixs_node *predicate,
                                                  bool *limited) {
  ixs_arena *arena;
  ixs_arena_mark mark;
  predicate_query query;
  ixs_query_check_memo_entry *entry;
  ixs_query_walk_step step;

  if (limited)
    *limited = false;
  if (!bounds || !predicate)
    return IXS_CHECK_UNKNOWN;
  arena = &bounds->query_arena;
  mark = ixs_arena_save(arena);
  query.bounds = bounds;
  query.answer = IXS_CHECK_UNKNOWN;
  IXS_QUERY_NODE_MEMO_INIT(&query.memo, arena, ixs_query_check_memo_entry,
                           node);
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
  ixs_query_transaction transaction;
  ixs_node *replacements[PREDICATE_FINITE_MAX_SYMBOLS];
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  bool have_defined_point = false;
  size_t point;

  ixs_query_transaction_begin(&transaction, ctx, NULL, NULL);
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
    if (!evaluated) {
      bounds->oom = true;
      break;
    }
    if (ixs_node_is_sentinel(evaluated))
      goto next_point;
    if (ixs_node_is_known_true(evaluated))
      current = IXS_CHECK_TRUE;
    else if (ixs_node_is_known_false(evaluated))
      current = IXS_CHECK_FALSE;
    else {
      result = IXS_CHECK_UNKNOWN;
      break;
    }
    if (!have_defined_point) {
      result = current;
      have_defined_point = true;
    } else if (result != current) {
      result = IXS_CHECK_UNKNOWN;
      break;
    }

  next_point:
    for (symbol = symbol_count; symbol > 0; symbol--) {
      predicate_finite_symbol *entry = &symbols[symbol - 1u];
      if (entry->current < entry->upper) {
        entry->current++;
        break;
      }
      entry->current = entry->lower;
    }
  }
  (void)ixs_query_transaction_finish(&transaction, false);
  return bounds->oom ? IXS_CHECK_UNKNOWN : result;
}

IXS_STATIC ixs_check_result bounds_predicate_bounded_finite_domain(
    ixs_bounds *bounds, ixs_node *predicate) {
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
/* Check B under a query-local A assumption.  The fork borrows the enclosing
 * query state, so a limit or transport failure invalidates the whole proof. */
static ixs_check_result predicate_query_implication_branch(ixs_bounds *bounds,
                                                           ixs_node *antecedent,
                                                           ixs_node *consequent,
                                                           bool *limited) {
  ixs_ctx *ctx;
  ixs_bounds branch;
  ixs_bounds_build_status status;
  ixs_query_transaction transaction;
  ixs_query_transaction assumption;
  ixs_bounds_transport_snapshot transport;
  bool branch_ready = false;
  bool branch_limited = false;
  ixs_check_result result = IXS_CHECK_UNKNOWN;

  if (!bounds || !antecedent || !consequent ||
      (antecedent->tag != IXS_AND && antecedent->tag != IXS_CMP))
    return IXS_CHECK_UNKNOWN;

  ctx = bounds->ctx;
  ixs_query_transaction_begin(&transaction, NULL, bounds, bounds->scratch);
  transport = transaction.transport;
  if (!ixs_bounds_fork(&branch, bounds)) {
    bounds->oom = true;
    goto cleanup;
  }
  branch_ready = true;
  /* Unsupported local assumptions are proof misses.  Their diagnostics and
   * closure are private to this branch. */
  ixs_query_transaction_begin(&assumption, ctx, NULL, NULL);
  status = bounds_assume_validate_predicate(&branch, antecedent);
  if (status == IXS_BOUNDS_BUILD_OK)
    status = facts_store_ingest_predicate_branch(ctx, &branch, antecedent);
  (void)ixs_query_transaction_finish(&assumption, false);

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
  result = bounds_predicate_eval(&branch, consequent, &branch_limited);
  if (branch.oom) {
    bounds->oom = true;
    goto cleanup;
  }
  if (result != IXS_CHECK_TRUE)
    result = IXS_CHECK_UNKNOWN;

cleanup:
  if (branch_ready)
    ixs_bounds_destroy(&branch);
  (void)ixs_query_transaction_finish(&transaction, false);
  if (limited &&
      (branch_limited || bounds_query_limited_since(bounds, transport)))
    *limited = true;
  return bounds->oom ? IXS_CHECK_UNKNOWN : result;
}

/* A | B is !A => B. Canonicalization folds NOT(CMP), so reconstruct the
 * complementary comparison when either disjunct is a comparison. The branch
 * evaluator deliberately has no implication fallback of its own. */
IXS_STATIC ixs_check_result bounds_predicate_implication(ixs_bounds *bounds,
                                                         ixs_node *predicate,
                                                         bool *limited) {
  unsigned pass;
  uint32_t i;

  if (!bounds || !predicate || predicate->tag != IXS_OR ||
      predicate->u.assoc.nargs != 2u)
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
