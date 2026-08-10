/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds_query.h"
#include <assert.h>
#include <string.h>

#define BOUNDS_QUERY_ACTIVE_INIT_CAP 16u
#define BOUNDS_QUERY_CACHE_INIT_CAP 256u

struct ixs_bounds_query_state {
  ixs_arena *arena;
  bounds_query_key *active;
  bounds_query_cache_entry *cache;
  size_t active_count;
  size_t active_capacity;
  size_t cache_count;
  size_t cache_capacity;
  size_t nesting;
  size_t visits;
  size_t stride_visits;
  size_t cache_hits;
  size_t cycle_blocks;
  size_t limit_blocks;
  size_t invalid_blocks;
  bounds_query_outcome transport_outcome;
  uint64_t generation;
  uint64_t next_owner;
};

static bool bounds_query_key_equal(bounds_query_key lhs, bounds_query_key rhs) {
  return lhs.kind == rhs.kind && lhs.owner == rhs.owner &&
         lhs.expr == rhs.expr && lhs.argument == rhs.argument &&
         lhs.equality_disabled == rhs.equality_disabled;
}

static void bounds_query_reset(ixs_bounds_query_state *state) {
  assert(state->active_count == 0);
  state->active_count = 0;
  state->visits = 0;
  state->stride_visits = 0;
  state->cache_hits = 0;
  state->cycle_blocks = 0;
  state->limit_blocks = 0;
  state->invalid_blocks = 0;
  state->transport_outcome = BOUNDS_QUERY_OUTCOME_PENDING;
  state->cache_count = 0;
  state->generation++;
  if (state->generation == 0) {
    if (state->cache)
      memset(state->cache, 0, state->cache_capacity * sizeof(*state->cache));
    state->generation = 1;
  }
}

static unsigned bounds_query_transport_rank(bounds_query_outcome outcome) {
  switch (outcome) {
  case BOUNDS_QUERY_OUTCOME_LIMITED:
    return 1u;
  case BOUNDS_QUERY_OUTCOME_OOM:
    return 2u;
  case BOUNDS_QUERY_OUTCOME_INVALID:
    return 3u;
  default:
    return 0u;
  }
}

static void bounds_query_note_transport_state(ixs_bounds_query_state *state,
                                              bounds_query_outcome outcome) {
  if (state && bounds_query_transport_rank(outcome) >
                   bounds_query_transport_rank(state->transport_outcome))
    state->transport_outcome = outcome;
}

IXS_STATIC void bounds_query_note_oom(ixs_bounds *b) {
  bounds_query_note_transport_state(b ? b->query_state : NULL,
                                    BOUNDS_QUERY_OUTCOME_OOM);
}

IXS_STATIC void bounds_query_note_limit(ixs_bounds *b) {
  ixs_bounds_query_state *state = b ? b->query_state : NULL;
  if (!state)
    return;
  if (state->limit_blocks != SIZE_MAX)
    state->limit_blocks++;
  bounds_query_note_transport_state(state, BOUNDS_QUERY_OUTCOME_LIMITED);
}

IXS_STATIC void bounds_query_note_invalid(ixs_bounds *b) {
  ixs_bounds_query_state *state = b ? b->query_state : NULL;
  if (!state)
    return;
  if (state->invalid_blocks != SIZE_MAX)
    state->invalid_blocks++;
  bounds_query_note_transport_state(state, BOUNDS_QUERY_OUTCOME_INVALID);
}

IXS_STATIC bool
bounds_query_limited_since(const ixs_bounds *bounds,
                           ixs_bounds_transport_snapshot before) {
  return bounds && bounds->query_state &&
         (bounds->query_state->generation != before.generation
              ? bounds->query_state->limit_blocks != 0
              : before.limit_blocks == SIZE_MAX ||
                    bounds->query_state->limit_blocks != before.limit_blocks);
}

IXS_STATIC bool
bounds_query_invalid_since(const ixs_bounds *bounds,
                           ixs_bounds_transport_snapshot before) {
  return bounds && bounds->query_state &&
         (bounds->query_state->generation != before.generation
              ? bounds->query_state->invalid_blocks != 0
              : before.invalid_blocks == SIZE_MAX ||
                    bounds->query_state->invalid_blocks !=
                        before.invalid_blocks);
}

static void bounds_query_counter_increment(size_t *counter) {
  if (*counter != SIZE_MAX)
    (*counter)++;
}

static uint64_t bounds_query_new_owner(ixs_bounds_query_state *state) {
  /* A generation admits only finitely many visits/nested holds, so owner reuse
   * within one generation would require more than 2^64 bounded operations.
   * Generation wrap separately clears every memo slot in bounds_query_reset. */
  state->next_owner++;
  if (state->next_owner == 0)
    state->next_owner++;
  return state->next_owner;
}

IXS_STATIC void bounds_query_init(ixs_bounds *b) {
  assert(b != NULL);
  ixs_arena_init(&b->query_state_arena, IXS_ARENA_DEFAULT_SIZE);
  ixs_arena_init(&b->query_arena, IXS_ARENA_DEFAULT_SIZE);
  b->query_state = NULL;
  b->query_owner = 0;
  b->query_tracking_depth = 0;
  b->query_state_owner = false;
  b->query_state_borrowed = false;
}

IXS_STATIC void bounds_query_destroy(ixs_bounds *b) {
  if (!b)
    return;
  assert(b->query_tracking_depth == 0);
  assert(!b->query_state_borrowed ||
         (b->query_state && b->query_state->nesting != 0));
  assert(!b->query_state_owner ||
         (b->query_state && b->query_state->arena == &b->query_state_arena &&
          b->query_state->nesting == 0 && b->query_state->active_count == 0));
  ixs_arena_destroy_transient(&b->query_arena);
  /* One state plus geometric active/cache growth is bounded by the largest
   * single query, not by retained context or query count. */
  ixs_arena_destroy_transient(&b->query_state_arena);
  b->query_state = NULL;
  b->query_owner = 0;
  b->query_tracking_depth = 0;
  b->query_state_owner = false;
  b->query_state_borrowed = false;
}

static bool bounds_query_ensure(ixs_bounds *b) {
  ixs_bounds_query_state *state;
  ixs_arena *arena;
  if (!b || b->oom)
    return false;
  if (b->query_state)
    return true;
  if (b->store_ctx && b->store_ctx->bounds_query_state) {
    state = b->store_ctx->bounds_query_state;
  } else if (b->store_ctx) {
    state =
        ixs_arena_alloc(&b->store_ctx->arena, sizeof(*state), sizeof(void *));
  } else {
    state =
        ixs_arena_alloc(&b->query_state_arena, sizeof(*state), sizeof(void *));
  }
  if (!state) {
    b->oom = true;
    return false;
  }
  if (!b->store_ctx || !b->store_ctx->bounds_query_state) {
    memset(state, 0, sizeof(*state));
    arena = b->store_ctx ? &b->store_ctx->arena : &b->query_state_arena;
    state->arena = arena;
    state->next_owner = 1;
    if (b->store_ctx)
      b->store_ctx->bounds_query_state = state;
  } else {
    (void)bounds_query_new_owner(state);
  }
  b->query_state = state;
  b->query_owner = state->next_owner;
  b->query_state_owner = !b->store_ctx;
  b->query_state_borrowed = false;
  return true;
}

IXS_STATIC void bounds_query_refresh_owner(ixs_bounds *b) {
  if (!b || !b->query_state)
    return;
  b->query_owner = bounds_query_new_owner(b->query_state);
}

IXS_STATIC void
bounds_query_owner_scope_begin(ixs_bounds *b, bounds_query_owner_scope *scope) {
  assert(b != NULL && scope != NULL);
  scope->owner = b->query_owner;
  scope->active = true;
  bounds_query_refresh_owner(b);
}

IXS_STATIC void bounds_query_owner_scope_end(ixs_bounds *b,
                                             bounds_query_owner_scope *scope) {
  assert(b != NULL && scope != NULL && scope->active);
  b->query_owner = scope->owner;
  scope->active = false;
}

IXS_STATIC bool bounds_query_is_tracking(const ixs_bounds *b) {
  return b && (b->query_tracking_depth != 0 || b->query_state_borrowed);
}

IXS_STATIC void bounds_query_inherit_fork(ixs_bounds *dst,
                                          const ixs_bounds *src) {
  assert(dst != NULL && src != NULL && dst->scratch == src->scratch);
  assert(!bounds_query_is_tracking(src) ||
         (src->query_state && src->query_state->nesting != 0));
  dst->query_state = bounds_query_is_tracking(src) ? src->query_state : NULL;
  dst->query_tracking_depth = 0;
  dst->query_state_owner = false;
  dst->query_state_borrowed = dst->query_state != NULL;
  dst->query_owner =
      dst->query_state ? bounds_query_new_owner(dst->query_state) : 0;
}

IXS_STATIC size_t bounds_query_cycle_count(const ixs_bounds *b) {
  return b && b->query_state ? b->query_state->cycle_blocks : 0;
}

IXS_STATIC ixs_bounds_transport_status
bounds_query_state_transport(const ixs_bounds *b) {
  bounds_query_outcome outcome = b && b->query_state
                                     ? b->query_state->transport_outcome
                                     : BOUNDS_QUERY_OUTCOME_PENDING;
  switch (outcome) {
  case BOUNDS_QUERY_OUTCOME_LIMITED:
    return IXS_BOUNDS_TRANSPORT_LIMITED;
  case BOUNDS_QUERY_OUTCOME_OOM:
    return IXS_BOUNDS_TRANSPORT_OOM;
  case BOUNDS_QUERY_OUTCOME_INVALID:
    return IXS_BOUNDS_TRANSPORT_INVALID;
  default:
    return IXS_BOUNDS_TRANSPORT_CLEAN;
  }
}

static ixs_bounds_transport_status
bounds_query_transport_status(const ixs_bounds *b) {
  bounds_query_outcome outcome =
      b && bounds_query_is_tracking(b) && b->query_state
          ? b->query_state->transport_outcome
          : BOUNDS_QUERY_OUTCOME_PENDING;
  if (!b || b->contradiction || outcome == BOUNDS_QUERY_OUTCOME_INVALID)
    return IXS_BOUNDS_TRANSPORT_INVALID;
  if (b->oom || outcome == BOUNDS_QUERY_OUTCOME_OOM)
    return IXS_BOUNDS_TRANSPORT_OOM;
  if (outcome == BOUNDS_QUERY_OUTCOME_LIMITED)
    return IXS_BOUNDS_TRANSPORT_LIMITED;
  return IXS_BOUNDS_TRANSPORT_CLEAN;
}

IXS_STATIC bool ixs_bounds_query_transport_clean(const ixs_bounds *b) {
  return bounds_query_transport_status(b) == IXS_BOUNDS_TRANSPORT_CLEAN;
}

IXS_STATIC ixs_bounds_transport_snapshot
ixs_bounds_query_transport_snapshot(const ixs_bounds *b) {
  ixs_bounds_transport_snapshot result;
  result.limit_blocks = b && b->query_state ? b->query_state->limit_blocks : 0;
  result.invalid_blocks =
      b && b->query_state ? b->query_state->invalid_blocks : 0;
  result.generation = b && b->query_state ? b->query_state->generation : 0;
  result.oom = b && b->oom;
  result.inherited = bounds_query_transport_status(b);
  return result;
}

IXS_STATIC ixs_bounds_transport_status ixs_bounds_query_transport_since(
    const ixs_bounds *b, ixs_bounds_transport_snapshot snapshot) {
  bool new_generation =
      b && b->query_state && b->query_state->generation != snapshot.generation;
  if (!b || b->contradiction ||
      snapshot.inherited == IXS_BOUNDS_TRANSPORT_INVALID ||
      (b->query_state && (new_generation ? b->query_state->invalid_blocks != 0
                                         : b->query_state->invalid_blocks !=
                                               snapshot.invalid_blocks)))
    return IXS_BOUNDS_TRANSPORT_INVALID;
  if ((!snapshot.oom && b->oom) ||
      snapshot.inherited == IXS_BOUNDS_TRANSPORT_OOM)
    return IXS_BOUNDS_TRANSPORT_OOM;
  if (snapshot.inherited == IXS_BOUNDS_TRANSPORT_LIMITED ||
      (b->query_state && (new_generation ? b->query_state->limit_blocks != 0
                                         : b->query_state->limit_blocks !=
                                               snapshot.limit_blocks)))
    return IXS_BOUNDS_TRANSPORT_LIMITED;
  return IXS_BOUNDS_TRANSPORT_CLEAN;
}

static bool bounds_query_root_needs_tracking(const ixs_bounds *b,
                                             const ixs_node *root) {
  return b && (bounds_query_is_tracking(b) ||
               ixs_node_contains_nested_piecewise(root) ||
               ixs_relation_algebra_edge_count(&b->relations) != 0);
}

IXS_STATIC const ixs_node *bounds_query_select_root(const ixs_bounds *b,
                                                    ixs_node *const *nodes,
                                                    size_t nnodes) {
  size_t i;
  if (!nodes || nnodes == 0)
    return NULL;
  if (bounds_query_is_tracking(b) ||
      (b && ixs_relation_algebra_edge_count(&b->relations) != 0))
    return nodes[0];
  for (i = 0; i < nnodes; i++) {
    if (ixs_node_contains_nested_piecewise(nodes[i]))
      return nodes[i];
  }
  return nodes[0];
}

static bool bounds_query_start_hold(ixs_bounds *b,
                                    ixs_bounds_query_state *state,
                                    bool *entered) {
  if (state->nesting == SIZE_MAX || b->query_tracking_depth == SIZE_MAX) {
    b->oom = true;
    return false;
  }
  state->nesting++;
  b->query_tracking_depth++;
  *entered = true;
  return true;
}

IXS_STATIC bool ixs_bounds_query_hold_begin(ixs_bounds *b, const ixs_node *root,
                                            bool *entered) {
  ixs_bounds_query_state *state;
  assert(entered != NULL);
  *entered = false;
  if (!bounds_query_root_needs_tracking(b, root))
    return true;
  if (!bounds_query_ensure(b))
    return false;
  state = b->query_state;
  if (state->nesting == 0)
    bounds_query_reset(state);
  return bounds_query_start_hold(b, state, entered);
}

IXS_STATIC bool bounds_query_force_hold_begin(ixs_bounds *b, bool *entered) {
  ixs_bounds_query_state *state;
  assert(entered != NULL);
  *entered = false;
  if (!bounds_query_ensure(b))
    return false;
  state = b->query_state;
  if (state->nesting == 0)
    bounds_query_reset(state);
  return bounds_query_start_hold(b, state, entered);
}

IXS_STATIC void ixs_bounds_query_hold_end(ixs_bounds *b) {
  ixs_bounds_query_state *state;
  assert(b != NULL && b->query_tracking_depth != 0);
  state = b->query_state;
  assert(state != NULL && state->nesting != 0);
  b->query_tracking_depth--;
  state->nesting--;
}

static bool bounds_query_grow_active(ixs_bounds *b,
                                     ixs_bounds_query_state *state) {
  bounds_query_key *grown;
  size_t capacity;
  size_t old_bytes;
  size_t new_bytes;

  if (state->active_count < state->active_capacity)
    return true;
  capacity = state->active_capacity ? state->active_capacity * 2u
                                    : BOUNDS_QUERY_ACTIVE_INIT_CAP;
  if (capacity < state->active_capacity ||
      state->active_capacity > SIZE_MAX / sizeof(*state->active) ||
      capacity > SIZE_MAX / sizeof(*state->active)) {
    b->oom = true;
    return false;
  }
  old_bytes = state->active_capacity * sizeof(*state->active);
  new_bytes = capacity * sizeof(*state->active);
  grown = ixs_arena_grow(state->arena, state->active, old_bytes, new_bytes,
                         sizeof(void *));
  if (!grown) {
    b->oom = true;
    return false;
  }
  state->active = grown;
  state->active_capacity = capacity;
  return true;
}

static size_t bounds_query_key_hash(bounds_query_key key) {
  uint64_t mixed = key.owner ^ key.argument ^ ((uint64_t)key.kind << 56);
  if (key.equality_disabled)
    mixed ^= UINT64_C(0x9e3779b97f4a7c15);
  mixed ^= (uint64_t)((uintptr_t)key.expr >> 3);
  mixed ^= mixed >> 33;
  mixed *= UINT64_C(0xff51afd7ed558ccd);
  mixed ^= mixed >> 33;
  return (size_t)mixed;
}

static bounds_query_cache_entry *
bounds_query_cache_find(ixs_bounds_query_state *state, bounds_query_key key,
                        bool *found) {
  size_t slot;
  if (!state->cache_capacity) {
    *found = false;
    return NULL;
  }
  slot = bounds_query_key_hash(key) & (state->cache_capacity - 1u);
  while (state->cache[slot].generation == state->generation) {
    if (bounds_query_key_equal(state->cache[slot].key, key)) {
      *found = true;
      return &state->cache[slot];
    }
    slot = (slot + 1u) & (state->cache_capacity - 1u);
  }
  *found = false;
  return &state->cache[slot];
}

static bool bounds_query_grow_cache(ixs_bounds *b,
                                    ixs_bounds_query_state *state) {
  bounds_query_cache_entry *grown;
  size_t capacity;
  size_t bytes;
  size_t i;

  capacity = state->cache_capacity ? state->cache_capacity * 2u
                                   : BOUNDS_QUERY_CACHE_INIT_CAP;
  if (capacity < state->cache_capacity ||
      capacity > SIZE_MAX / sizeof(*state->cache)) {
    b->oom = true;
    return false;
  }
  bytes = capacity * sizeof(*state->cache);
  grown = ixs_arena_alloc(state->arena, bytes, sizeof(void *));
  if (!grown) {
    b->oom = true;
    return false;
  }
  memset(grown, 0, bytes);
  for (i = 0; i < state->cache_capacity; i++) {
    bounds_query_cache_entry entry = state->cache[i];
    size_t slot;
    if (entry.generation != state->generation)
      continue;
    slot = bounds_query_key_hash(entry.key) & (capacity - 1u);
    while (grown[slot].generation == state->generation)
      slot = (slot + 1u) & (capacity - 1u);
    grown[slot] = entry;
  }
  state->cache = grown;
  state->cache_capacity = capacity;
  return true;
}

static bool bounds_query_prepare_cache_insert(ixs_bounds *b,
                                              ixs_bounds_query_state *state) {
  if (!state->cache_capacity ||
      state->cache_count + 1u >
          state->cache_capacity - state->cache_capacity / 4u)
    return bounds_query_grow_cache(b, state);
  return true;
}

IXS_STATIC bounds_query_enter_result bounds_query_begin(
    ixs_bounds *b, bounds_query_kind kind, ixs_node *expr, uint64_t argument,
    bounds_query_scope *scope, bounds_query_cache_entry **cached) {
  ixs_bounds_query_state *state;
  bounds_query_key key;
  bounds_query_cache_entry *entry;
  bool found;

  memset(scope, 0, sizeof(*scope));
  *cached = NULL;
  if (!b || !expr || (expr->properties & IXS_NODE_PROPERTY_VALID) == 0) {
    if (b)
      bounds_query_note_invalid(b);
    return BOUNDS_QUERY_ENTER_INVALID;
  }
  if (!bounds_query_ensure(b)) {
    bounds_query_note_oom(b);
    return BOUNDS_QUERY_ENTER_OOM;
  }
  state = b->query_state;
  if (state->nesting == 0)
    bounds_query_reset(state);
  if (b->oom)
    bounds_query_note_oom(b);
  switch (state->transport_outcome) {
  case BOUNDS_QUERY_OUTCOME_LIMITED:
    return BOUNDS_QUERY_ENTER_LIMIT;
  case BOUNDS_QUERY_OUTCOME_INVALID:
    return BOUNDS_QUERY_ENTER_INVALID;
  case BOUNDS_QUERY_OUTCOME_OOM:
    return BOUNDS_QUERY_ENTER_OOM;
  default:
    break;
  }
  key.kind = kind;
  key.owner = b->query_owner;
  key.expr = expr;
  key.argument = argument;
  key.equality_disabled = b->equality_disabled_depth != 0;
  entry = bounds_query_cache_find(state, key, &found);
  if (found) {
    /* STARTED entries remain incomplete until their LIFO scope finishes, so
     * an incomplete current-generation entry is exactly an active cycle.
     * This keeps the hot-path recursion guard expected O(1); the active vector
     * exists only for finish-order assertions and diagnostics. */
    if (!entry->complete) {
      bounds_query_counter_increment(&state->cycle_blocks);
      return BOUNDS_QUERY_ENTER_CYCLE;
    }
    if (entry->outcome == BOUNDS_QUERY_OUTCOME_VALUE ||
        entry->outcome == BOUNDS_QUERY_OUTCOME_NO_FACT) {
      bounds_query_counter_increment(&state->cache_hits);
      *cached = entry;
      return BOUNDS_QUERY_ENTER_CACHED;
    }
  }
  if (state->nesting == SIZE_MAX || state->visits == SIZE_MAX) {
    b->oom = true;
    bounds_query_note_oom(b);
    return BOUNDS_QUERY_ENTER_OOM;
  }
  state->visits++;
  if (kind == BOUNDS_QUERY_STRIDE)
    state->stride_visits++;
  if (!bounds_query_grow_active(b, state)) {
    bounds_query_note_oom(b);
    return BOUNDS_QUERY_ENTER_OOM;
  }
  if (!found) {
    if (!bounds_query_prepare_cache_insert(b, state)) {
      bounds_query_note_oom(b);
      return BOUNDS_QUERY_ENTER_OOM;
    }
    entry = bounds_query_cache_find(state, key, &found);
    assert(!found);
    state->cache_count++;
  }
  memset(entry, 0, sizeof(*entry));
  entry->key = key;
  entry->generation = state->generation;
  entry->outcome = BOUNDS_QUERY_OUTCOME_PENDING;
  state->active[state->active_count++] = key;
  state->nesting++;
  scope->bounds = b;
  scope->state = state;
  scope->key = key;
  scope->active = true;
  return BOUNDS_QUERY_ENTER_STARTED;
}

IXS_STATIC bounds_query_cache_entry *
bounds_query_finish(bounds_query_scope *scope, bool success) {
  ixs_bounds_query_state *state;
  bounds_query_cache_entry *entry;
  bool found;
  assert(scope != NULL && scope->active && scope->state != NULL &&
         scope->bounds != NULL);
  state = scope->state;
  assert(state->active_count != 0 && state->nesting != 0 &&
         bounds_query_key_equal(state->active[state->active_count - 1u],
                                scope->key));
  entry = bounds_query_cache_find(state, scope->key, &found);
  assert(found && entry && !entry->complete);
  if (scope->bounds->oom)
    bounds_query_note_oom(scope->bounds);
  entry->complete = true;
  entry->outcome =
      state->transport_outcome == BOUNDS_QUERY_OUTCOME_PENDING
          ? success ? BOUNDS_QUERY_OUTCOME_VALUE : BOUNDS_QUERY_OUTCOME_NO_FACT
          : state->transport_outcome;
  entry->success = entry->outcome == BOUNDS_QUERY_OUTCOME_VALUE;
  state->active_count--;
  state->nesting--;
  scope->active = false;
  return entry;
}

#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
IXS_STATIC void ixs_bounds_query_stats(const ixs_bounds *b, size_t *visits,
                                       size_t *stride_visits,
                                       size_t *cache_hits, size_t *cycle_blocks,
                                       size_t *limit_blocks,
                                       size_t *active_count, size_t *nesting) {
  const ixs_bounds_query_state *state = b ? b->query_state : NULL;
  if (visits)
    *visits = state ? state->visits : 0;
  if (stride_visits)
    *stride_visits = state ? state->stride_visits : 0;
  if (cache_hits)
    *cache_hits = state ? state->cache_hits : 0;
  if (cycle_blocks)
    *cycle_blocks = state ? state->cycle_blocks : 0;
  if (limit_blocks)
    *limit_blocks = state ? state->limit_blocks : 0;
  if (active_count)
    *active_count = state ? state->active_count : 0;
  if (nesting)
    *nesting = state ? state->nesting : 0;
}

IXS_STATIC bool ixs_bounds_query_cycle_probe(ixs_bounds *b, ixs_node *expr) {
  bounds_query_scope outer;
  bounds_query_scope reentered;
  bounds_query_cache_entry *cached;
  bounds_query_enter_result outer_status;
  bounds_query_enter_result reentered_status;
  bool held = false;

  if (!b || !expr || !ixs_bounds_query_hold_begin(b, expr, &held))
    return false;
  outer_status =
      bounds_query_begin(b, BOUNDS_QUERY_INTERVAL, expr, 0, &outer, &cached);
  if (outer_status != BOUNDS_QUERY_ENTER_STARTED)
    goto cleanup;
  reentered_status = bounds_query_begin(b, BOUNDS_QUERY_INTERVAL, expr, 0,
                                        &reentered, &cached);
  (void)bounds_query_finish(&outer, false);
  if (held)
    ixs_bounds_query_hold_end(b);
  return reentered_status == BOUNDS_QUERY_ENTER_CYCLE;

cleanup:
  if (held)
    ixs_bounds_query_hold_end(b);
  return false;
}

IXS_STATIC bool
ixs_bounds_query_transport_probe(ixs_bounds *b, ixs_node *expr,
                                 ixs_bounds_test_transport injected,
                                 ixs_bounds_test_transport *observed) {
  struct ixs_node_impl invalid_node;
  bounds_query_scope outer;
  bounds_query_scope invalid_scope;
  bounds_query_cache_entry *cached = NULL;
  bounds_query_cache_entry *entry = NULL;
  bounds_query_enter_result enter;
  bool held = false;
  bool result = false;

  if (!b || !expr || !observed ||
      !ixs_bounds_query_hold_begin(b, expr, &held) || !held)
    return false;
  enter =
      bounds_query_begin(b, BOUNDS_QUERY_INTERVAL, expr, 0, &outer, &cached);
  if (enter != BOUNDS_QUERY_ENTER_STARTED)
    goto cleanup;

  switch (injected) {
  case IXS_BOUNDS_TEST_TRANSPORT_VALUE:
    break;
  case IXS_BOUNDS_TEST_TRANSPORT_LIMITED:
    bounds_query_note_limit(b);
    break;
  case IXS_BOUNDS_TEST_TRANSPORT_INVALID:
    memset(&invalid_node, 0, sizeof(invalid_node));
    invalid_node.tag = IXS_SYM;
    enter = bounds_query_begin(b, BOUNDS_QUERY_INTERVAL, &invalid_node, 0,
                               &invalid_scope, &cached);
    if (enter != BOUNDS_QUERY_ENTER_INVALID)
      goto cleanup;
    break;
  default:
    goto cleanup;
  }

  entry = bounds_query_finish(&outer, true);
  switch (entry->outcome) {
  case BOUNDS_QUERY_OUTCOME_VALUE:
    *observed = IXS_BOUNDS_TEST_TRANSPORT_VALUE;
    break;
  case BOUNDS_QUERY_OUTCOME_LIMITED:
    *observed = IXS_BOUNDS_TEST_TRANSPORT_LIMITED;
    break;
  case BOUNDS_QUERY_OUTCOME_INVALID:
    *observed = IXS_BOUNDS_TEST_TRANSPORT_INVALID;
    break;
  default:
    goto cleanup;
  }
  result = true;

cleanup:
  if (outer.active)
    (void)bounds_query_finish(&outer, false);
  if (held)
    ixs_bounds_query_hold_end(b);
  return result;
}
#endif

IXS_STATIC bool bounds_query_should_track(const ixs_bounds *b,
                                          const ixs_node *expr) {
  return bounds_query_is_tracking(b) && expr &&
         (expr->properties & IXS_NODE_PROPERTY_VALID) != 0;
}

IXS_STATIC void bounds_query_reset_arena(ixs_bounds *b) {
  assert(b != NULL);
  assert(b->query_tracking_depth == 0);
  assert(!b->query_state_owner && !b->query_state_borrowed);
  ixs_arena_destroy_transient(&b->query_arena);
  ixs_arena_init(&b->query_arena, IXS_ARENA_DEFAULT_SIZE);
}
