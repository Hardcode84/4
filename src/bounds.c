/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds.h"
#include "expand.h"
#include "simplify.h"
#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>

/* Transport detail is intentionally private.  The public fact-query API keeps
 * its original value/out-parameter contracts and reports transport failures
 * through the owning session's diagnostics. */
typedef enum {
  IXS_FACT_QUERY_COMPLETE,
  IXS_FACT_QUERY_LIMITED,
  IXS_FACT_QUERY_INVALID,
  IXS_FACT_QUERY_OOM
} ixs_fact_query_status;

typedef struct {
  ixs_fact_query_status status;
  ixs_check_result check;
} ixs_fact_check_result;

typedef struct {
  ixs_fact_query_status status;
  const ixs_node *value;
} ixs_simplify_result;

typedef struct {
  ixs_fact_query_status status;
  bool available;
  int64_t difference;
} ixs_constant_difference_result;

typedef struct {
  ixs_fact_query_status status;
  ixs_pow2_fact fact;
} ixs_pow2_query_result;

typedef struct {
  ixs_fact_query_status status;
  ixs_known_bits bits;
} ixs_known_bits_query_result;

typedef struct {
  ixs_fact_query_status status;
  bool available;
  ixs_range_result range;
} ixs_range_query_result;

typedef struct {
  ixs_fact_query_status status;
  bool available;
  int64_t modulus;
  int64_t residue;
} ixs_symbol_congruence_result;

typedef struct {
  ixs_fact_query_status status;
  bool available;
  const ixs_node *coefficient;
  const ixs_node *residual;
} ixs_affine_decomposition_result;

typedef struct {
  ixs_fact_query_status status;
  bool available;
  const ixs_node *difference;
} ixs_finite_difference_result;

typedef struct {
  ixs_fact_query_status status;
  bool available;
  const ixs_node *residual;
  int64_t constant;
} ixs_additive_constant_result;

#define BOUNDS_INIT_CAP 16
#define BOUNDS_VAR_INDEX_INIT_CAP 8u
#define BOUNDS_EXPR_INDEX_INIT_CAP 8u
#define BOUNDS_DIFFERENCE_INDEX_INIT_CAP 8u
#define BOUNDS_EXACT_INDEX_INIT_CAP 8u
#define BOUNDS_EQUALITY_ENDPOINT_INDEX_INIT_CAP 8u
#define BOUNDS_EQUALITY_INDEX_INIT_CAP 8u
#define BOUNDS_EQUALITY_WALK_INIT_CAP 16u
#define BOUNDS_EQUALITY_PROJECTION_CACHE_INIT_CAP 64u
#define BOUNDS_CACHE_CAP 32u
#define BOUNDS_CACHE_DISABLED ((size_t)-1)
#define FACT_WORK_INIT_CAP 64u
#define BOUNDS_QUERY_ACTIVE_INIT_CAP 16u
#define BOUNDS_QUERY_CACHE_INIT_CAP 256u

/* lhs - rhs <= offset, equivalently the directed edge rhs -> lhs. Edge
 * objects are immutable after publication. Variable indices remain valid
 * across append-only table growth and transactional forks. */
struct ixs_difference_constraint {
  ixs_node *lhs;
  ixs_node *rhs;
  ixs_difference_constraint *next_lhs;
  ixs_difference_constraint *next_rhs;
  size_t lhs_var;
  size_t rhs_var;
  int64_t offset;
};

/* Immutable exact relation lhs == rhs + offset. Endpoint indices survive
 * append-only growth and order-preserving bounds forks. */
struct ixs_equality_edge {
  ixs_node *lhs;
  ixs_node *rhs;
  ixs_equality_edge *next_lhs;
  ixs_equality_edge *next_rhs;
  size_t lhs_endpoint;
  size_t rhs_endpoint;
  int64_t offset;
};

typedef ixs_wide_offset bounds_wide_offset;

typedef struct {
  ixs_node *node;
  size_t endpoint_index;
  /* Exact node - component-root offset. Signed magnitude preserves the
   * transient +2^63 reverse of an INT64_MIN edge. */
  bounds_wide_offset offset;
} bounds_equality_walk_entry;

typedef struct {
  size_t endpoint_plus_one;
  size_t entry_plus_one;
} bounds_equality_seen_entry;

typedef struct {
  ixs_arena_mark mark;
  bounds_equality_walk_entry *entries;
  bounds_equality_seen_entry *seen;
  size_t count;
  size_t capacity;
  size_t seen_count;
  size_t seen_capacity;
  bool initialized;
} bounds_equality_walk;

typedef enum {
  BOUNDS_EQUALITY_WALK_NONE,
  BOUNDS_EQUALITY_WALK_VALID,
  BOUNDS_EQUALITY_WALK_UNREPRESENTABLE,
  BOUNDS_EQUALITY_WALK_LIMITED,
  BOUNDS_EQUALITY_WALK_CONFLICT,
  BOUNDS_EQUALITY_WALK_INVALID,
  BOUNDS_EQUALITY_WALK_OOM
} bounds_equality_walk_status;

typedef struct {
  ixs_arena_mark mark;
  size_t *queue;
  size_t epoch;
  size_t capacity;
  size_t head;
  size_t tail;
  size_t count;
} difference_worklist;

typedef enum {
  BOUNDS_EQUALITY_RECORD_INSERTED,
  BOUNDS_EQUALITY_RECORD_MATCHED,
  BOUNDS_EQUALITY_RECORD_CONFLICT,
  BOUNDS_EQUALITY_RECORD_INVALID,
  BOUNDS_EQUALITY_RECORD_OOM
} bounds_equality_record_status;

typedef enum {
  BOUNDS_EQUALITY_UNION_MERGED,
  BOUNDS_EQUALITY_UNION_MATCHED,
  BOUNDS_EQUALITY_UNION_CONFLICT,
  BOUNDS_EQUALITY_UNION_INVALID
} bounds_equality_union_status;

typedef enum {
  BOUNDS_QUERY_EMPTY,
  BOUNDS_QUERY_INTERVAL,
  BOUNDS_QUERY_BITFACTS,
  BOUNDS_QUERY_RESIDUE,
  BOUNDS_QUERY_STRIDE
} bounds_query_kind;

/* VALUE and NO_FACT are semantic outcomes.  LIMITED, INVALID, and OOM are
 * transport failures: once observed they poison the whole current query
 * generation, so no parent can publish or reuse a partial semantic miss. */
typedef enum {
  BOUNDS_QUERY_OUTCOME_PENDING,
  BOUNDS_QUERY_OUTCOME_VALUE,
  BOUNDS_QUERY_OUTCOME_NO_FACT,
  BOUNDS_QUERY_OUTCOME_CYCLE,
  BOUNDS_QUERY_OUTCOME_LIMITED,
  BOUNDS_QUERY_OUTCOME_INVALID,
  BOUNDS_QUERY_OUTCOME_OOM
} bounds_query_outcome;

typedef struct {
  bounds_query_kind kind;
  uint64_t owner;
  ixs_node *expr;
  uint64_t argument;
  bool equality_disabled;
} bounds_query_key;

typedef struct {
  bounds_query_key key;
  uint64_t generation;
  bounds_query_outcome outcome;
  bool complete;
  bool success;
  union {
    ixs_interval interval;
    ixs_bitfacts bitfacts;
    uint64_t residue;
    uint64_t stride;
  } result;
} bounds_query_cache_entry;

typedef struct {
  size_t endpoint_index;
  size_t defined_component;
  bounds_wide_offset defined_offset;
  ixs_interval range;
  ixs_check_result integer;
  ixs_check_result defined_with_equality;
  ixs_check_result defined_without_equality;
  bool range_complete;
  bool integer_complete;
  bool defined_component_complete;
  bool defined_with_equality_complete;
  bool defined_without_equality_complete;
  bool occupied;
} bounds_equality_projection_cache_entry;

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
  size_t range_pw_case_visits;
  size_t range_pw_limit_blocks;
  size_t cache_hits;
  size_t cycle_blocks;
  size_t limit_blocks;
  size_t invalid_blocks;
  size_t equality_walks;
  size_t equality_endpoint_visits;
  size_t equality_edge_visits;
  size_t equality_defined_checks;
  size_t equality_intrinsic_evaluations;
  bool range_pw_budget_armed;
  bounds_query_outcome transport_outcome;
  uint64_t generation;
  uint64_t next_owner;
};

typedef enum {
  BOUNDS_QUERY_ENTER_STARTED,
  BOUNDS_QUERY_ENTER_CACHED,
  BOUNDS_QUERY_ENTER_CYCLE,
  BOUNDS_QUERY_ENTER_LIMIT,
  BOUNDS_QUERY_ENTER_INVALID,
  BOUNDS_QUERY_ENTER_OOM
} bounds_query_enter_result;

typedef struct {
  ixs_bounds *bounds;
  ixs_bounds_query_state *state;
  bounds_query_key key;
  bool active;
} bounds_query_scope;

static void bounds_propagate_difference_bounds(ixs_bounds *b, const char *first,
                                               const char *second);
static void bounds_add_exact_relation(ixs_bounds *b, ixs_node *lhs,
                                      ixs_node *rhs, int64_t offset);
static ixs_interval bounds_get_intrinsic(ixs_bounds *b, ixs_node *expr);
static ixs_interval bounds_get_tracked(ixs_bounds *b, ixs_node *expr);
static bool bounds_get_bitfacts_tracked(ixs_bounds *b, ixs_node *expr,
                                        ixs_bitfacts *out);
static ixs_node *bounds_condition_assumption(ixs_bounds *b, ixs_node *cond,
                                             bool value,
                                             struct ixs_node_impl *storage);
static ixs_check_result bounds_condition_truth(ixs_bounds *b, ixs_node *cond);
static bool bounds_known_stride(ixs_bounds *bounds, ixs_node *expr,
                                uint64_t *stride);
static ixs_check_result bounds_check_defined_without_equality(ixs_bounds *b,
                                                              ixs_node *expr,
                                                              bool *oom,
                                                              bool *limited);
static ixs_check_result bounds_check_defined_detail(ixs_bounds *b,
                                                    ixs_node *expr, bool *oom,
                                                    bool *limited);
static bool bounds_find_equality_endpoint(const ixs_bounds *b,
                                          const ixs_node *expr,
                                          size_t *endpoint_index);
static bounds_equality_walk_status
bounds_collect_equality_component(ixs_bounds *b, ixs_node *expr,
                                  bounds_equality_walk *walk,
                                  bool require_defined);
static bounds_equality_walk_status
bounds_relation_offset(ixs_bounds *b, ixs_node *lhs, ixs_node *rhs,
                       bounds_wide_offset *offset, bool require_defined);
static bounds_wide_offset bounds_wide_offset_from_int64(int64_t value);
static bounds_wide_offset bounds_wide_offset_negate(bounds_wide_offset value);
static bool bounds_wide_offset_add(bounds_wide_offset a, bounds_wide_offset b,
                                   bounds_wide_offset *result);
static bool bounds_wide_offset_equal(bounds_wide_offset a,
                                     bounds_wide_offset b);
static bounds_equality_union_status
bounds_union_equality_endpoints(ixs_bounds *b, size_t lhs_endpoint,
                                size_t rhs_endpoint, int64_t offset);
static bounds_equality_walk_status
bounds_exact_relation_difference(ixs_bounds *b, ixs_node *lhs, ixs_node *rhs,
                                 int64_t *delta);
static bool bounds_exact_symbol_difference(ixs_bounds *b, ixs_node *lhs,
                                           ixs_node *rhs, int64_t *delta);

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
  state->range_pw_case_visits = 0;
  state->range_pw_limit_blocks = 0;
  state->cache_hits = 0;
  state->cycle_blocks = 0;
  state->limit_blocks = 0;
  state->invalid_blocks = 0;
  state->equality_walks = 0;
  state->equality_endpoint_visits = 0;
  state->equality_edge_visits = 0;
  state->equality_defined_checks = 0;
  state->equality_intrinsic_evaluations = 0;
  state->range_pw_budget_armed = false;
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

static void bounds_query_note_transport(ixs_bounds_query_state *state,
                                        bounds_query_outcome outcome) {
  if (state && bounds_query_transport_rank(outcome) >
                   bounds_query_transport_rank(state->transport_outcome))
    state->transport_outcome = outcome;
}

static void bounds_query_note_limit(ixs_bounds_query_state *state) {
  if (!state)
    return;
  if (state->limit_blocks != SIZE_MAX)
    state->limit_blocks++;
  bounds_query_note_transport(state, BOUNDS_QUERY_OUTCOME_LIMITED);
}

static void bounds_query_note_invalid(ixs_bounds_query_state *state) {
  if (!state)
    return;
  if (state->invalid_blocks != SIZE_MAX)
    state->invalid_blocks++;
  bounds_query_note_transport(state, BOUNDS_QUERY_OUTCOME_INVALID);
}

static bool bounds_query_limited_since(const ixs_bounds *bounds,
                                       size_t limit_blocks) {
  return bounds && bounds->query_state &&
         (limit_blocks == SIZE_MAX ||
          bounds->query_state->limit_blocks != limit_blocks);
}

static bool bounds_query_invalid_since(const ixs_bounds *bounds,
                                       size_t invalid_blocks) {
  return bounds && bounds->query_state &&
         (invalid_blocks == SIZE_MAX ||
          bounds->query_state->invalid_blocks != invalid_blocks);
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
    state = ixs_arena_alloc(&b->query_arena, sizeof(*state), sizeof(void *));
  }
  if (!state) {
    b->oom = true;
    return false;
  }
  if (!b->store_ctx || !b->store_ctx->bounds_query_state) {
    memset(state, 0, sizeof(*state));
    arena = b->store_ctx ? &b->store_ctx->arena : &b->query_arena;
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

static void bounds_query_refresh_owner(ixs_bounds *b) {
  if (!b || !b->query_state)
    return;
  b->query_owner = bounds_query_new_owner(b->query_state);
}

static bool bounds_query_is_tracking(const ixs_bounds *b) {
  return b && (b->query_tracking_depth != 0 || b->query_state_borrowed);
}

static bool bounds_query_root_needs_tracking(const ixs_bounds *b,
                                             const ixs_node *root) {
  return b && (bounds_query_is_tracking(b) ||
               ixs_node_contains_nested_piecewise(root) || b->nequalities != 0);
}

static const ixs_node *bounds_query_select_root(const ixs_bounds *b,
                                                ixs_node *const *nodes,
                                                size_t nnodes) {
  size_t i;
  if (!nodes || nnodes == 0)
    return NULL;
  if (bounds_query_is_tracking(b))
    return nodes[0];
  if (b && b->nequalities != 0)
    return nodes[0];
  for (i = 0; i < nnodes; i++) {
    size_t endpoint_index;
    if (ixs_node_contains_nested_piecewise(nodes[i]) ||
        (b && b->nequalities != 0 &&
         bounds_find_equality_endpoint(b, nodes[i], &endpoint_index)))
      return nodes[i];
  }
  return nodes[0];
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
  if (state->nesting == 0) {
    bounds_query_reset(state);
    state->range_pw_budget_armed = ixs_node_contains_nested_piecewise(root);
  } else if (ixs_node_contains_nested_piecewise(root)) {
    state->range_pw_budget_armed = true;
  }
  if (state->nesting == SIZE_MAX || b->query_tracking_depth == SIZE_MAX) {
    b->oom = true;
    return false;
  }
  state->nesting++;
  b->query_tracking_depth++;
  *entered = true;
  return true;
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

static size_t bounds_equality_projection_cache_hash(size_t endpoint_index) {
  uint64_t mixed = (uint64_t)endpoint_index;
  mixed ^= mixed >> 33;
  mixed *= UINT64_C(0xff51afd7ed558ccd);
  mixed ^= mixed >> 33;
  return (size_t)mixed;
}

static bounds_equality_projection_cache_entry *
bounds_equality_projection_cache_find(ixs_bounds *b, size_t endpoint_index,
                                      bool *found) {
  bounds_equality_projection_cache_entry *cache =
      (bounds_equality_projection_cache_entry *)b->equality_projection_cache;
  size_t slot;
  if (!b->equality_projection_cache_capacity) {
    *found = false;
    return NULL;
  }
  slot = bounds_equality_projection_cache_hash(endpoint_index) &
         (b->equality_projection_cache_capacity - 1u);
  while (cache[slot].occupied) {
    bounds_equality_projection_cache_entry *entry = &cache[slot];
    if (entry->endpoint_index == endpoint_index) {
      *found = true;
      return entry;
    }
    slot = (slot + 1u) & (b->equality_projection_cache_capacity - 1u);
  }
  *found = false;
  return &cache[slot];
}

static bool bounds_equality_projection_cache_grow(ixs_bounds *b) {
  bounds_equality_projection_cache_entry *grown;
  bounds_equality_projection_cache_entry *cache =
      (bounds_equality_projection_cache_entry *)b->equality_projection_cache;
  ixs_arena *arena;
  size_t capacity = b->equality_projection_cache_capacity
                        ? b->equality_projection_cache_capacity * 2u
                        : BOUNDS_EQUALITY_PROJECTION_CACHE_INIT_CAP;
  size_t bytes;
  size_t i;
  if (capacity < b->equality_projection_cache_capacity ||
      capacity > SIZE_MAX / sizeof(*grown)) {
    b->oom = true;
    return false;
  }
  bytes = capacity * sizeof(*grown);
  arena = b->equality_projection_cache_transient ? &b->query_arena
          : b->store_ctx                         ? &b->store_ctx->arena
                                                 : &b->query_arena;
  grown = ixs_arena_alloc(arena, bytes, sizeof(void *));
  if (!grown) {
    b->oom = true;
    return false;
  }
  memset(grown, 0, bytes);
  for (i = 0; i < b->equality_projection_cache_capacity; i++) {
    bounds_equality_projection_cache_entry entry = cache[i];
    size_t slot;
    if (!entry.occupied)
      continue;
    slot = bounds_equality_projection_cache_hash(entry.endpoint_index) &
           (capacity - 1u);
    while (grown[slot].occupied)
      slot = (slot + 1u) & (capacity - 1u);
    grown[slot] = entry;
  }
  b->equality_projection_cache = grown;
  b->equality_projection_cache_capacity = capacity;
  return true;
}

static bounds_equality_projection_cache_entry *
bounds_equality_projection_cache_get(ixs_bounds *b, size_t endpoint_index,
                                     bool create) {
  bounds_equality_projection_cache_entry *entry;
  bool found;
  if (!bounds_query_is_tracking(b) || !b->query_state)
    return NULL;
  entry = bounds_equality_projection_cache_find(b, endpoint_index, &found);
  if (found || !create)
    return found ? entry : NULL;
  if (!b->equality_projection_cache_capacity ||
      b->equality_projection_cache_count + 1u >
          b->equality_projection_cache_capacity -
              b->equality_projection_cache_capacity / 4u) {
    if (!bounds_equality_projection_cache_grow(b))
      return NULL;
    entry = bounds_equality_projection_cache_find(b, endpoint_index, &found);
    assert(!found);
  }
  if (!entry) {
    b->oom = true;
    return NULL;
  }
  memset(entry, 0, sizeof(*entry));
  entry->endpoint_index = endpoint_index;
  entry->occupied = true;
  b->equality_projection_cache_count++;
  return entry;
}

static bool bounds_equality_projection_cache_reserve(ixs_bounds *b,
                                                     size_t additional) {
  size_t needed;
  if (!bounds_query_is_tracking(b))
    return true;
  if (!b->query_state ||
      additional > SIZE_MAX - b->equality_projection_cache_count) {
    b->oom = true;
    return false;
  }
  needed = b->equality_projection_cache_count + additional;
  while (!b->equality_projection_cache_capacity ||
         needed > b->equality_projection_cache_capacity -
                      b->equality_projection_cache_capacity / 4u) {
    if (!bounds_equality_projection_cache_grow(b))
      return false;
  }
  return true;
}

static bounds_query_enter_result
bounds_query_begin(ixs_bounds *b, bounds_query_kind kind, ixs_node *expr,
                   uint64_t argument, bounds_query_scope *scope,
                   bounds_query_cache_entry **cached) {
  ixs_bounds_query_state *state;
  bounds_query_key key;
  bounds_query_cache_entry *entry;
  bool found;

  memset(scope, 0, sizeof(*scope));
  *cached = NULL;
  if (!b || !expr || (expr->properties & IXS_NODE_PROPERTY_VALID) == 0) {
    if (b)
      bounds_query_note_invalid(b->query_state);
    return BOUNDS_QUERY_ENTER_INVALID;
  }
  if (!bounds_query_ensure(b)) {
    bounds_query_note_transport(b->query_state, BOUNDS_QUERY_OUTCOME_OOM);
    return BOUNDS_QUERY_ENTER_OOM;
  }
  state = b->query_state;
  if (state->nesting == 0)
    bounds_query_reset(state);
  if (b->oom)
    bounds_query_note_transport(state, BOUNDS_QUERY_OUTCOME_OOM);
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
    bounds_query_note_transport(state, BOUNDS_QUERY_OUTCOME_OOM);
    return BOUNDS_QUERY_ENTER_OOM;
  }
  state->visits++;
  if (kind == BOUNDS_QUERY_STRIDE)
    state->stride_visits++;
  if (!bounds_query_grow_active(b, state)) {
    bounds_query_note_transport(state, BOUNDS_QUERY_OUTCOME_OOM);
    return BOUNDS_QUERY_ENTER_OOM;
  }
  if (!found) {
    if (!bounds_query_prepare_cache_insert(b, state)) {
      bounds_query_note_transport(state, BOUNDS_QUERY_OUTCOME_OOM);
      return BOUNDS_QUERY_ENTER_OOM;
    }
    entry = bounds_query_cache_find(state, key, &found);
    assert(!found);
    if (found) {
      bounds_query_note_invalid(state);
      return BOUNDS_QUERY_ENTER_INVALID;
    }
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

static bounds_query_cache_entry *bounds_query_finish(bounds_query_scope *scope,
                                                     bool success) {
  ixs_bounds_query_state *state;
  bounds_query_cache_entry *entry;
  bool found;
  if (!scope || !scope->active)
    return NULL;
  state = scope->state;
  assert(state->active_count != 0 &&
         bounds_query_key_equal(state->active[state->active_count - 1u],
                                scope->key));
  entry = bounds_query_cache_find(state, scope->key, &found);
  assert(found && entry && !entry->complete);
  if (scope->bounds->oom)
    bounds_query_note_transport(state, BOUNDS_QUERY_OUTCOME_OOM);
  entry->complete = true;
  entry->outcome =
      state->transport_outcome == BOUNDS_QUERY_OUTCOME_PENDING
          ? success ? BOUNDS_QUERY_OUTCOME_VALUE : BOUNDS_QUERY_OUTCOME_NO_FACT
          : state->transport_outcome;
  entry->success = entry->outcome == BOUNDS_QUERY_OUTCOME_VALUE;
  if (state->active_count != 0)
    state->active_count--;
  if (state->nesting != 0)
    state->nesting--;
  scope->active = false;
  return entry;
}

#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
IXS_STATIC void ixs_bounds_query_stats(const ixs_bounds *b, size_t *visits,
                                       size_t *stride_visits,
                                       size_t *range_pw_case_visits,
                                       size_t *range_pw_limit_blocks,
                                       size_t *cache_hits, size_t *cycle_blocks,
                                       size_t *limit_blocks,
                                       size_t *active_count, size_t *nesting) {
  const ixs_bounds_query_state *state = b ? b->query_state : NULL;
  if (visits)
    *visits = state ? state->visits : 0;
  if (stride_visits)
    *stride_visits = state ? state->stride_visits : 0;
  if (range_pw_case_visits)
    *range_pw_case_visits = state ? state->range_pw_case_visits : 0;
  if (range_pw_limit_blocks)
    *range_pw_limit_blocks = state ? state->range_pw_limit_blocks : 0;
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
    bounds_query_note_limit(b->query_state);
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
  if (!entry || !entry->complete)
    goto cleanup;
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

static bool bounds_query_should_track(const ixs_bounds *b,
                                      const ixs_node *expr) {
  return bounds_query_is_tracking(b) && expr &&
         (expr->properties & IXS_NODE_PROPERTY_VALID) != 0;
}

static bool bounds_query_take_range_visit(ixs_bounds *b,
                                          const ixs_node *piecewise) {
  ixs_bounds_query_state *state;
  if (!bounds_query_is_tracking(b) || !b->query_state)
    return true;
  state = b->query_state;
  if (ixs_node_contains_nested_piecewise(piecewise))
    state->range_pw_budget_armed = true;
  if (!state->range_pw_budget_armed)
    return true;
  bounds_query_counter_increment(&state->range_pw_case_visits);
  return true;
}

static void bounds_empty_cache_invalidate(ixs_bounds *b) {
  if (b)
    b->empty_cache_valid = false;
}

static void bounds_mark_semantic_changed(ixs_bounds *b) {
  if (b && b->semantic_changed)
    *b->semantic_changed = true;
}

static void bounds_mark_contradiction(ixs_bounds *b) {
  if (!b->contradiction)
    bounds_mark_semantic_changed(b);
  b->contradiction = true;
  bounds_empty_cache_invalidate(b);
}

static bool bounds_intervals_equal(ixs_interval a, ixs_interval b) {
  return a.lo_p == b.lo_p && a.lo_q == b.lo_q && a.hi_p == b.hi_p &&
         a.hi_q == b.hi_q && a.lo_inf == b.lo_inf && a.hi_inf == b.hi_inf &&
         a.valid == b.valid;
}

static void bounds_cache_clear(ixs_bounds *b) {
  bounds_equality_projection_cache_entry *projection_cache;
  bounds_empty_cache_invalidate(b);
  bounds_query_refresh_owner(b);
  if (b && b->cache && b->cache_cap != BOUNDS_CACHE_DISABLED)
    memset(b->cache, 0, b->cache_cap * sizeof(*b->cache));
  if (!b)
    return;
  projection_cache =
      (bounds_equality_projection_cache_entry *)b->equality_projection_cache;
  if (projection_cache)
    memset(projection_cache, 0,
           b->equality_projection_cache_capacity * sizeof(*projection_cache));
  b->equality_projection_cache_count = 0;
}

static void bounds_cache_alloc(ixs_bounds *b) {
  if (!b || b->cache_cap == BOUNDS_CACHE_DISABLED)
    return;
  if (b->cache)
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

IXS_STATIC bool ixs_bounds_init(ixs_bounds *b, ixs_arena *scratch) {
  ixs_arena_init(&b->query_arena, IXS_ARENA_DEFAULT_SIZE);
  b->ctx = NULL;
  b->store_ctx = NULL;
  b->scratch = scratch;
  b->nvars = 0;
  b->cap = BOUNDS_INIT_CAP;
  b->vars = ixs_arena_alloc(scratch, BOUNDS_INIT_CAP * sizeof(*b->vars),
                            sizeof(void *));
  b->var_index = NULL;
  b->var_index_cap = 0;
  b->nexprs = 0;
  b->expr_cap = 0;
  b->exprs = NULL;
  b->expr_index = NULL;
  b->expr_index_cap = 0;
  b->mod_inverse_heads = NULL;
  b->mod_inverse_head_cap = 0;
  b->mod_inverse_watchers = NULL;
  b->nmod_inverse_watchers = 0;
  b->mod_inverse_watcher_cap = 0;
  b->mod_inverse_watch_visits = 0;
  b->difference_index = NULL;
  b->difference_vars = NULL;
  b->ndifferences = 0;
  b->ndifference_vars = 0;
  b->difference_index_cap = 0;
  b->difference_var_cap = 0;
  b->difference_epoch = 0;
  b->exact_vars = NULL;
  b->exact_index = NULL;
  b->nexact_vars = 0;
  b->exact_var_cap = 0;
  b->exact_index_cap = 0;
  b->equality_endpoints = NULL;
  b->equality_endpoint_index = NULL;
  b->nequality_endpoints = 0;
  b->equality_endpoint_cap = 0;
  b->equality_endpoint_index_cap = 0;
  b->equality_index = NULL;
  b->nequalities = 0;
  b->equality_index_cap = 0;
  b->nonzero = NULL;
  b->nnonzero = 0;
  b->nonzero_cap = 0;
  b->cache = NULL;
  b->cache_cap = 0;
  b->range_pw_depth = 0;
  b->has_modrem = false;
  b->contradiction = false;
  b->empty_cache_valid = false;
  b->empty_cache_value = false;
  b->oom = false;
  b->query_state = NULL;
  b->query_owner = 0;
  b->equality_projection_cache = NULL;
  b->equality_projection_cache_count = 0;
  b->equality_projection_cache_capacity = 0;
  b->mod_inverse_heads = NULL;
  b->mod_inverse_head_cap = 0;
  b->mod_inverse_watchers = NULL;
  b->nmod_inverse_watchers = 0;
  b->mod_inverse_watcher_cap = 0;
  b->mod_inverse_watch_visits = 0;
  b->query_tracking_depth = 0;
  b->equality_disabled_depth = 0;
  b->predicate_equivalence_depth = 0;
  b->exact_proof_call_depth = 0;
  b->interval_evaluating = false;
  b->query_state_owner = false;
  b->query_state_borrowed = false;
  b->equality_projection_cache_transient = true;
  b->semantic_changed = NULL;
  if (b->vars)
    bounds_cache_alloc(b);
  return b->vars != NULL;
}

IXS_STATIC bool ixs_bounds_init_ctx(ixs_bounds *b, ixs_ctx *ctx,
                                    ixs_arena *scratch) {
  if (!ixs_bounds_init(b, scratch))
    return false;
  b->ctx = ctx;
  b->store_ctx = ctx;
  return true;
}

static void bounds_projection_cache_reset_storage(ixs_bounds *b,
                                                  bool transient) {
  assert(b != NULL);
  assert(b->query_tracking_depth == 0);
  assert(!b->query_state_owner && !b->query_state_borrowed);
  ixs_arena_destroy_transient(&b->query_arena);
  ixs_arena_init(&b->query_arena, IXS_ARENA_DEFAULT_SIZE);
  b->equality_projection_cache = NULL;
  b->equality_projection_cache_count = 0;
  b->equality_projection_cache_capacity = 0;
  b->equality_projection_cache_transient = transient;
}

/* Context-owned query state lives in the context arena.  Contextless state
 * lives in this bounds object's dedicated arena, so scratch restores cannot
 * invalidate growable recursion and memo buffers. */
IXS_STATIC void ixs_bounds_destroy(ixs_bounds *b) {
  if (!b)
    return;
  assert(b->query_tracking_depth == 0);
  assert(!b->query_state_borrowed ||
         (b->query_state && b->query_state->nesting != 0));
  assert(!b->query_state_owner ||
         (b->query_state && b->query_state->arena == &b->query_arena &&
          b->query_state->nesting == 0 && b->query_state->active_count == 0));
  ixs_arena_destroy_transient(&b->query_arena);
  b->query_state = NULL;
  b->query_owner = 0;
  b->equality_projection_cache = NULL;
  b->equality_projection_cache_count = 0;
  b->equality_projection_cache_capacity = 0;
  b->query_tracking_depth = 0;
  b->equality_disabled_depth = 0;
  b->predicate_equivalence_depth = 0;
  b->exact_proof_call_depth = 0;
  b->query_state_owner = false;
  b->query_state_borrowed = false;
  b->equality_projection_cache_transient = false;
}

static void bounds_destroy_if_initialized(ixs_bounds *b, bool initialized) {
  if (initialized)
    ixs_bounds_destroy(b);
}

static bool bounds_fork_index_state(ixs_bounds *dst, const ixs_bounds *src) {
  if (src->nvars) {
    if (!src->var_index || !src->var_index_cap ||
        src->var_index_cap > SIZE_MAX / sizeof(*dst->var_index))
      return false;
    dst->var_index = ixs_arena_alloc(
        dst->scratch, src->var_index_cap * sizeof(*dst->var_index),
        sizeof(void *));
    if (!dst->var_index)
      return false;
    memcpy(dst->var_index, src->var_index,
           src->var_index_cap * sizeof(*src->var_index));
  }
  if (src->difference_index_cap) {
    if (!src->difference_index ||
        src->difference_index_cap > SIZE_MAX / sizeof(*dst->difference_index))
      return false;
    dst->difference_index = ixs_arena_alloc(dst->scratch,
                                            src->difference_index_cap *
                                                sizeof(*dst->difference_index),
                                            sizeof(void *));
    if (!dst->difference_index)
      return false;
    memcpy(dst->difference_index, src->difference_index,
           src->difference_index_cap * sizeof(*src->difference_index));
  }
  if (src->difference_var_cap) {
    if (!src->difference_vars ||
        src->difference_var_cap > SIZE_MAX / sizeof(*dst->difference_vars))
      return false;
    dst->difference_vars = ixs_arena_alloc(
        dst->scratch, src->difference_var_cap * sizeof(*dst->difference_vars),
        sizeof(void *));
    if (!dst->difference_vars)
      return false;
    memcpy(dst->difference_vars, src->difference_vars,
           src->difference_var_cap * sizeof(*src->difference_vars));
  }
  return true;
}

static bool bounds_fork_mod_inverse_state(ixs_bounds *dst,
                                          const ixs_bounds *src) {
  if (src->mod_inverse_head_cap) {
    if (!src->mod_inverse_heads ||
        src->mod_inverse_head_cap > SIZE_MAX / sizeof(*dst->mod_inverse_heads))
      return false;
    dst->mod_inverse_heads = ixs_arena_alloc(
        dst->scratch,
        src->mod_inverse_head_cap * sizeof(*dst->mod_inverse_heads),
        sizeof(void *));
    if (!dst->mod_inverse_heads)
      return false;
    memcpy(dst->mod_inverse_heads, src->mod_inverse_heads,
           src->mod_inverse_head_cap * sizeof(*src->mod_inverse_heads));
  }
  if (src->nmod_inverse_watchers) {
    if (!src->mod_inverse_watchers ||
        src->nmod_inverse_watchers >
            SIZE_MAX / sizeof(*dst->mod_inverse_watchers))
      return false;
    dst->mod_inverse_watchers = ixs_arena_alloc(
        dst->scratch,
        src->nmod_inverse_watchers * sizeof(*dst->mod_inverse_watchers),
        sizeof(void *));
    if (!dst->mod_inverse_watchers)
      return false;
    memcpy(dst->mod_inverse_watchers, src->mod_inverse_watchers,
           src->nmod_inverse_watchers * sizeof(*src->mod_inverse_watchers));
  }
  return true;
}

static bool bounds_fork_exact_state(ixs_bounds *dst, const ixs_bounds *src) {
  if (src->exact_var_cap) {
    if (!src->exact_vars ||
        src->exact_var_cap > SIZE_MAX / sizeof(*dst->exact_vars))
      return false;
    dst->exact_vars = ixs_arena_alloc(
        dst->scratch, src->exact_var_cap * sizeof(*dst->exact_vars),
        sizeof(void *));
    if (!dst->exact_vars)
      return false;
    memcpy(dst->exact_vars, src->exact_vars,
           src->exact_var_cap * sizeof(*src->exact_vars));
  }
  if (src->exact_index_cap) {
    if (!src->exact_index ||
        src->exact_index_cap > SIZE_MAX / sizeof(*dst->exact_index))
      return false;
    dst->exact_index = ixs_arena_alloc(
        dst->scratch, src->exact_index_cap * sizeof(*dst->exact_index),
        sizeof(void *));
    if (!dst->exact_index)
      return false;
    memcpy(dst->exact_index, src->exact_index,
           src->exact_index_cap * sizeof(*src->exact_index));
  }
  return true;
}

static bool bounds_fork_equality_state(ixs_bounds *dst, const ixs_bounds *src) {
  size_t i;
  if (src->equality_endpoint_cap) {
    if (!src->equality_endpoints ||
        src->equality_endpoint_cap >
            SIZE_MAX / sizeof(*dst->equality_endpoints))
      return false;
    dst->equality_endpoints = ixs_arena_alloc(
        dst->scratch,
        src->equality_endpoint_cap * sizeof(*dst->equality_endpoints),
        sizeof(void *));
    if (!dst->equality_endpoints)
      return false;
    memcpy(dst->equality_endpoints, src->equality_endpoints,
           src->equality_endpoint_cap * sizeof(*src->equality_endpoints));
    for (i = 0; i < src->nequality_endpoints; i++)
      dst->equality_endpoints[i].edges = NULL;
  }
  if (src->equality_endpoint_index_cap) {
    if (!src->equality_endpoint_index ||
        src->equality_endpoint_index_cap >
            SIZE_MAX / sizeof(*dst->equality_endpoint_index))
      return false;
    dst->equality_endpoint_index =
        ixs_arena_alloc(dst->scratch,
                        src->equality_endpoint_index_cap *
                            sizeof(*dst->equality_endpoint_index),
                        sizeof(void *));
    if (!dst->equality_endpoint_index)
      return false;
    memcpy(dst->equality_endpoint_index, src->equality_endpoint_index,
           src->equality_endpoint_index_cap *
               sizeof(*src->equality_endpoint_index));
  }
  if (src->equality_index_cap) {
    if (!src->equality_index ||
        src->equality_index_cap > SIZE_MAX / sizeof(*dst->equality_index))
      return false;
    dst->equality_index = ixs_arena_alloc(
        dst->scratch, src->equality_index_cap * sizeof(*dst->equality_index),
        sizeof(void *));
    if (!dst->equality_index)
      return false;
    memset(dst->equality_index, 0,
           src->equality_index_cap * sizeof(*dst->equality_index));
    for (i = 0; i < src->equality_index_cap; i++) {
      const ixs_equality_edge *source_edge = src->equality_index[i];
      ixs_equality_edge *edge;
      if (!source_edge)
        continue;
      if (source_edge->lhs_endpoint >= src->nequality_endpoints ||
          source_edge->rhs_endpoint >= src->nequality_endpoints)
        return false;
      edge = ixs_arena_alloc(dst->scratch, sizeof(*edge), sizeof(void *));
      if (!edge)
        return false;
      *edge = *source_edge;
      edge->next_lhs = dst->equality_endpoints[edge->lhs_endpoint].edges;
      edge->next_rhs = dst->equality_endpoints[edge->rhs_endpoint].edges;
      dst->equality_endpoints[edge->lhs_endpoint].edges = edge;
      dst->equality_endpoints[edge->rhs_endpoint].edges = edge;
      dst->equality_index[i] = edge;
    }
  }
  return true;
}

static bool bounds_fork_expr_state(ixs_bounds *dst, const ixs_bounds *src) {
  if (!src->nexprs)
    return true;
  dst->exprs = ixs_arena_alloc(
      dst->scratch, dst->expr_cap * sizeof(*dst->exprs), sizeof(void *));
  if (!dst->exprs)
    return false;
  memcpy(dst->exprs, src->exprs, src->nexprs * sizeof(*src->exprs));
  if (!src->expr_index || !src->expr_index_cap ||
      src->expr_index_cap > SIZE_MAX / sizeof(*dst->expr_index))
    return false;
  dst->expr_index = ixs_arena_alloc(
      dst->scratch, dst->expr_index_cap * sizeof(*dst->expr_index),
      sizeof(void *));
  if (!dst->expr_index)
    return false;
  memcpy(dst->expr_index, src->expr_index,
         src->expr_index_cap * sizeof(*src->expr_index));
  return true;
}

static void bounds_query_assign_fork_owner(ixs_bounds *dst) {
  if (!dst->query_state) {
    dst->query_owner = 0;
    return;
  }
  dst->query_owner = bounds_query_new_owner(dst->query_state);
}

IXS_STATIC bool ixs_bounds_fork(ixs_bounds *dst, const ixs_bounds *src) {
  if (!dst || !src || src->oom)
    return false;
  ixs_arena_init(&dst->query_arena, IXS_ARENA_DEFAULT_SIZE);
  dst->ctx = src->ctx;
  dst->store_ctx = src->store_ctx;
  dst->scratch = src->scratch;
  dst->nvars = src->nvars;
  dst->cap = src->nvars ? src->nvars : 1;
  dst->vars = ixs_arena_alloc(dst->scratch, dst->cap * sizeof(*dst->vars),
                              sizeof(void *));
  if (!dst->vars)
    goto failed;
  if (src->nvars)
    memcpy(dst->vars, src->vars, src->nvars * sizeof(*src->vars));
  dst->var_index = NULL;
  dst->var_index_cap = src->nvars ? src->var_index_cap : 0;
  dst->nexprs = src->nexprs;
  dst->expr_cap = src->nexprs ? src->nexprs : 0;
  dst->exprs = NULL;
  dst->expr_index = NULL;
  dst->expr_index_cap = src->nexprs ? src->expr_index_cap : 0;
  dst->mod_inverse_heads = NULL;
  dst->mod_inverse_head_cap = src->mod_inverse_head_cap;
  dst->mod_inverse_watchers = NULL;
  dst->nmod_inverse_watchers = src->nmod_inverse_watchers;
  dst->mod_inverse_watcher_cap = src->nmod_inverse_watchers;
  dst->mod_inverse_watch_visits = 0;
  dst->difference_index = NULL;
  dst->difference_vars = NULL;
  dst->ndifferences = src->ndifferences;
  dst->ndifference_vars = src->ndifference_vars;
  dst->difference_index_cap = src->difference_index_cap;
  dst->difference_var_cap = src->difference_var_cap;
  dst->difference_epoch = src->difference_epoch;
  dst->exact_vars = NULL;
  dst->exact_index = NULL;
  dst->nexact_vars = src->nexact_vars;
  dst->exact_var_cap = src->exact_var_cap;
  dst->exact_index_cap = src->exact_index_cap;
  dst->equality_endpoints = NULL;
  dst->equality_endpoint_index = NULL;
  dst->nequality_endpoints = src->nequality_endpoints;
  dst->equality_endpoint_cap = src->equality_endpoint_cap;
  dst->equality_endpoint_index_cap = src->equality_endpoint_index_cap;
  dst->equality_index = NULL;
  dst->nequalities = src->nequalities;
  dst->equality_index_cap = src->equality_index_cap;
  dst->nnonzero = src->nnonzero;
  dst->nonzero_cap = src->nnonzero;
  dst->nonzero = NULL;
  dst->cache = NULL;
  dst->cache_cap = BOUNDS_CACHE_DISABLED;
  dst->range_pw_depth = src->range_pw_depth;
  dst->has_modrem = src->has_modrem;
  dst->contradiction = src->contradiction;
  dst->empty_cache_valid = false;
  dst->empty_cache_value = false;
  dst->oom = false;
  /* A fork allocated from the source scratch cannot outlive that scratch.
   * While a source hold is active, the same lifetime rule also keeps the
   * source-owned query arena alive, so borrowing its guard/budget is safe.
   * Outside an active hold the fork starts with no state and lazily acquires
   * context-owned state or its own dedicated arena. */
  assert(dst->scratch == src->scratch);
  assert(!bounds_query_is_tracking(src) ||
         (src->query_state && src->query_state->nesting != 0));
  dst->query_state = bounds_query_is_tracking(src) ? src->query_state : NULL;
  dst->equality_projection_cache = NULL;
  dst->equality_projection_cache_count = 0;
  dst->equality_projection_cache_capacity = 0;
  dst->query_tracking_depth = 0;
  dst->equality_disabled_depth = src->equality_disabled_depth;
  /* A fork made by a nested query remains inside the source predicate probe;
   * inheriting the guard prevents the fork from reopening the same cycle. */
  dst->predicate_equivalence_depth = src->predicate_equivalence_depth;
  dst->exact_proof_call_depth = src->exact_proof_call_depth;
  dst->interval_evaluating = false;
  dst->query_state_owner = false;
  dst->query_state_borrowed = dst->query_state != NULL;
  dst->equality_projection_cache_transient = true;
  if (dst->query_state)
    bounds_query_assign_fork_owner(dst);
  else
    dst->query_owner = 0;
  dst->semantic_changed = NULL;
  if (!bounds_fork_index_state(dst, src) ||
      !bounds_fork_mod_inverse_state(dst, src) ||
      !bounds_fork_exact_state(dst, src) ||
      !bounds_fork_equality_state(dst, src) ||
      !bounds_fork_expr_state(dst, src))
    goto failed;
  if (src->nnonzero) {
    dst->nonzero = ixs_arena_alloc(
        dst->scratch, dst->nonzero_cap * sizeof(*dst->nonzero), sizeof(void *));
    if (!dst->nonzero)
      goto failed;
    memcpy(dst->nonzero, src->nonzero, src->nnonzero * sizeof(*src->nonzero));
  }
  return true;

failed:
  ixs_arena_destroy_transient(&dst->query_arena);
  return false;
}

static size_t bounds_hash_ptr(const void *ptr) {
  uint64_t x = (uint64_t)(uintptr_t)ptr;
  x ^= x >> 33;
  x *= UINT64_C(0xff51afd7ed558ccd);
  x ^= x >> 33;
  return (size_t)x;
}

static size_t bounds_var_index_slot(const size_t *index, size_t capacity,
                                    const ixs_var_bound *vars,
                                    const char *name) {
  size_t slot = bounds_hash_ptr(name) & (capacity - 1u);
  while (index[slot] && vars[index[slot] - 1u].name != name)
    slot = (slot + 1u) & (capacity - 1u);
  return slot;
}

/* Variable lookup is expected O(1); growth rehashes at 75% load. */
static bool bounds_prepare_var_index(ixs_bounds *b, size_t count,
                                     size_t **prepared,
                                     size_t *prepared_capacity) {
  size_t capacity = b->var_index_cap;
  size_t *index;
  size_t i;

  if (capacity && count <= capacity - capacity / 4u) {
    *prepared = b->var_index;
    *prepared_capacity = capacity;
    return true;
  }
  if (!capacity)
    capacity = BOUNDS_VAR_INDEX_INIT_CAP;
  while (count > capacity - capacity / 4u) {
    if (capacity > SIZE_MAX / 2u)
      return false;
    capacity *= 2u;
  }
  if (capacity > SIZE_MAX / sizeof(*index))
    return false;
  index =
      ixs_arena_alloc(b->scratch, capacity * sizeof(*index), sizeof(void *));
  if (!index)
    return false;
  memset(index, 0, capacity * sizeof(*index));
  for (i = 0; i < b->nvars; i++) {
    size_t slot =
        bounds_var_index_slot(index, capacity, b->vars, b->vars[i].name);
    index[slot] = i + 1u;
  }
  *prepared = index;
  *prepared_capacity = capacity;
  return true;
}

static ixs_var_bound *find_var(ixs_bounds *b, const char *name) {
  size_t slot;
  if (!b || !b->vars || !name || b->nvars == 0)
    return NULL;
  if (!b->var_index || !b->var_index_cap) {
    b->oom = true;
    return NULL;
  }
  slot = bounds_var_index_slot(b->var_index, b->var_index_cap, b->vars, name);
  return b->var_index[slot] ? &b->vars[b->var_index[slot] - 1u] : NULL;
}

static bool get_or_create_var_index(ixs_bounds *b, const char *name,
                                    size_t *index) {
  ixs_var_bound *v = find_var(b, name);
  size_t *prepared_index;
  size_t prepared_index_cap;
  size_t slot;
  if (v) {
    *index = (size_t)(v - b->vars);
    return true;
  }
  if (!b->vars || b->oom || b->nvars == SIZE_MAX ||
      !bounds_prepare_var_index(b, b->nvars + 1u, &prepared_index,
                                &prepared_index_cap)) {
    b->oom = true;
    return false;
  }
  if (b->nvars >= b->cap) {
    ixs_var_bound *grown;
    size_t new_cap;
    if (b->cap > SIZE_MAX / 2u || b->cap * 2u > SIZE_MAX / sizeof(*b->vars)) {
      b->oom = true;
      return false;
    }
    new_cap = b->cap * 2u;
    grown = ixs_arena_grow(b->scratch, b->vars, b->cap * sizeof(*b->vars),
                           new_cap * sizeof(*b->vars), sizeof(void *));
    if (!grown) {
      b->oom = true;
      return false;
    }
    b->vars = grown;
    b->cap = new_cap;
  }
  bounds_empty_cache_invalidate(b);
  *index = b->nvars;
  v = &b->vars[*index];
  v->name = name;
  v->iv.valid = true;
  v->iv.lo_inf = false;
  v->iv.hi_inf = false;
  ixs_interval_set_lo_neg_inf(&v->iv);
  ixs_interval_set_hi_pos_inf(&v->iv);
  v->modulus = 0;
  v->remainder = 0;
  v->bits.known_zero = 0;
  v->bits.known_one = 0;
  v->bits.pow2 = IXS_POW2_UNKNOWN;
  b->var_index = prepared_index;
  b->var_index_cap = prepared_index_cap;
  slot = bounds_var_index_slot(b->var_index, b->var_index_cap, b->vars, name);
  b->var_index[slot] = *index + 1u;
  b->nvars++;
  bounds_mark_semantic_changed(b);
  return true;
}

static ixs_var_bound *get_or_create_var(ixs_bounds *b, const char *name) {
  size_t index;
  if (!get_or_create_var_index(b, name, &index))
    return NULL;
  return &b->vars[index];
}

static void bitfacts_unknown(ixs_bitfacts *bits) {
  bits->known_zero = 0;
  bits->known_one = 0;
  bits->pow2 = IXS_POW2_UNKNOWN;
}

static unsigned bit_popcount64(uint64_t v) {
  unsigned n = 0;
  while (v) {
    n += (unsigned)(v & 1u);
    v >>= 1;
  }
  return n;
}

static bool uint64_is_pow2(uint64_t v) { return v != 0 && (v & (v - 1u)) == 0; }

static bool int64_is_positive_pow2(int64_t v) {
  return v > 0 && uint64_is_pow2((uint64_t)v);
}

static bool int64_modulus_is_pow2(int64_t v) {
  return v > 0 && uint64_is_pow2((uint64_t)v);
}

static unsigned bit_ctz64(uint64_t v) {
  unsigned n = 0;
  while (v != 0 && (v & 1u) == 0) {
    n++;
    v >>= 1;
  }
  return n;
}

static uint64_t low_mask(unsigned nbits) {
  if (nbits >= 64u)
    return ~(uint64_t)0;
  return (((uint64_t)1) << nbits) - 1u;
}

static uint64_t value_span_mask(uint64_t hi) {
  uint64_t mask = 0;
  while (hi) {
    mask = (mask << 1) | 1u;
    hi >>= 1;
  }
  return mask;
}

static bool bitfacts_conflict(const ixs_bitfacts *bits) {
  if ((bits->known_zero & bits->known_one) != 0)
    return true;
  if ((bits->pow2 == IXS_POW2_OR_ZERO || bits->pow2 == IXS_POW2_POSITIVE) &&
      bit_popcount64(bits->known_one) > 1)
    return true;
  return false;
}

static bool interval_lower_at_least(const ixs_interval *iv, int64_t p,
                                    int64_t q) {
  return iv->valid && !iv->lo_inf && ixs_rat_cmp(iv->lo_p, iv->lo_q, p, q) >= 0;
}

static bool interval_upper_less_than(const ixs_interval *iv, int64_t p,
                                     int64_t q) {
  return iv->valid && !iv->hi_inf && ixs_rat_cmp(iv->hi_p, iv->hi_q, p, q) < 0;
}

static bool interval_exact_int(const ixs_interval *iv, int64_t *value) {
  if (!iv->valid || iv->lo_inf || iv->hi_inf || iv->lo_q != 1 ||
      iv->hi_q != 1 || iv->lo_p != iv->hi_p)
    return false;
  *value = iv->lo_p;
  return true;
}

static int64_t integer_congruence_residue(int64_t value, int64_t modulus) {
  int64_t residue = value % modulus;
  return residue < 0 ? residue + modulus : residue;
}

static bool integer_align_congruence_up(int64_t value, int64_t modulus,
                                        int64_t remainder, int64_t *out) {
  int64_t current, delta;
  if (modulus <= 0 || remainder < 0 || remainder >= modulus || !out)
    return false;
  current = integer_congruence_residue(value, modulus);
  delta = remainder >= current ? remainder - current
                               : modulus - (current - remainder);
  return ixs_safe_add(value, delta, out);
}

static bool integer_align_congruence_down(int64_t value, int64_t modulus,
                                          int64_t remainder, int64_t *out) {
  int64_t current, delta;
  if (modulus <= 0 || remainder < 0 || remainder >= modulus || !out)
    return false;
  current = integer_congruence_residue(value, modulus);
  delta = current >= remainder ? current - remainder
                               : modulus - (remainder - current);
  return ixs_safe_sub(value, delta, out);
}

static ixs_interval interval_intersect_congruence(ixs_interval iv,
                                                  int64_t modulus,
                                                  int64_t remainder) {
  int64_t aligned;
  if (!iv.valid || modulus <= 0)
    return iv;
  if (!iv.lo_inf && integer_align_congruence_up(ixs_rat_ceil(iv.lo_p, iv.lo_q),
                                                modulus, remainder, &aligned)) {
    iv.lo_p = aligned;
    iv.lo_q = 1;
  }
  if (!iv.hi_inf &&
      integer_align_congruence_down(ixs_rat_floor(iv.hi_p, iv.hi_q), modulus,
                                    remainder, &aligned)) {
    iv.hi_p = aligned;
    iv.hi_q = 1;
  }
  return iv;
}

static bool interval_has_congruent_integer(const ixs_interval *iv,
                                           int64_t modulus, int64_t remainder) {
  int64_t lo, hi, first;
  if (!iv->valid || iv->lo_inf || iv->hi_inf || modulus <= 0)
    return true;
  lo = ixs_rat_ceil(iv->lo_p, iv->lo_q);
  hi = ixs_rat_floor(iv->hi_p, iv->hi_q);
  if (lo > hi)
    return false;
  return integer_align_congruence_up(lo, modulus, remainder, &first) &&
         first <= hi;
}

static void refine_var_bit_consistency(ixs_bounds *b, ixs_var_bound *v) {
  int64_t exact;
  if (!v)
    return;
  bounds_empty_cache_invalidate(b);
  if (v->bits.pow2 == IXS_POW2_OR_ZERO &&
      interval_lower_at_least(&v->iv, 1, 1)) {
    v->bits.pow2 = IXS_POW2_POSITIVE;
    bounds_mark_semantic_changed(b);
  }
  if ((v->bits.pow2 == IXS_POW2_OR_ZERO &&
       interval_upper_less_than(&v->iv, 0, 1)) ||
      (v->bits.pow2 == IXS_POW2_POSITIVE &&
       interval_upper_less_than(&v->iv, 1, 1)))
    bounds_mark_contradiction(b);
  if (interval_exact_int(&v->iv, &exact)) {
    uint64_t u = (uint64_t)exact;
    if ((v->bits.known_zero & u) != 0 || (v->bits.known_one & ~u) != 0)
      bounds_mark_contradiction(b);
    if ((v->bits.pow2 == IXS_POW2_OR_ZERO ||
         v->bits.pow2 == IXS_POW2_POSITIVE) &&
        exact != 0 && !int64_is_positive_pow2(exact))
      bounds_mark_contradiction(b);
    if (v->bits.pow2 == IXS_POW2_POSITIVE && exact == 0)
      bounds_mark_contradiction(b);
  }
  if (v->modulus > 0 &&
      !interval_has_congruent_integer(&v->iv, v->modulus, v->remainder))
    bounds_mark_contradiction(b);
  if (bitfacts_conflict(&v->bits))
    bounds_mark_contradiction(b);
}

static void apply_var_known_bits(ixs_bounds *b, ixs_var_bound *v,
                                 uint64_t known_zero, uint64_t known_one) {
  uint64_t old_zero;
  uint64_t old_one;
  if (!v)
    return;
  old_zero = v->bits.known_zero;
  old_one = v->bits.known_one;
  v->bits.known_zero |= known_zero;
  v->bits.known_one |= known_one;
  if (old_zero != v->bits.known_zero || old_one != v->bits.known_one)
    bounds_mark_semantic_changed(b);
  refine_var_bit_consistency(b, v);
}

static void apply_known_bits(ixs_bounds *b, const char *name,
                             uint64_t known_zero, uint64_t known_one) {
  ixs_var_bound *v = get_or_create_var(b, name);
  apply_var_known_bits(b, v, known_zero, known_one);
}

static void apply_pow2_fact(ixs_bounds *b, ixs_var_bound *v,
                            ixs_pow2_fact pow2) {
  if (!v)
    return;
  if (pow2 == IXS_POW2_POSITIVE) {
    if (v->bits.pow2 == IXS_POW2_UNKNOWN || v->bits.pow2 == IXS_POW2_OR_ZERO) {
      v->bits.pow2 = IXS_POW2_POSITIVE;
      bounds_mark_semantic_changed(b);
    }
  } else if (pow2 == IXS_POW2_OR_ZERO && v->bits.pow2 == IXS_POW2_UNKNOWN) {
    v->bits.pow2 = IXS_POW2_OR_ZERO;
    bounds_mark_semantic_changed(b);
  }
  refine_var_bit_consistency(b, v);
}

static void apply_exact_int_bits(ixs_bounds *b, ixs_var_bound *v, int64_t val) {
  uint64_t u = (uint64_t)val;
  if (!v)
    return;
  apply_var_known_bits(b, v, ~u, u);
  if (val == 0) {
    if (v->bits.pow2 == IXS_POW2_POSITIVE)
      bounds_mark_contradiction(b);
    else if (v->bits.pow2 != IXS_POW2_OR_ZERO) {
      v->bits.pow2 = IXS_POW2_OR_ZERO;
      bounds_mark_semantic_changed(b);
    }
  } else if (int64_is_positive_pow2(val)) {
    if (v->bits.pow2 != IXS_POW2_POSITIVE) {
      v->bits.pow2 = IXS_POW2_POSITIVE;
      bounds_mark_semantic_changed(b);
    }
  } else if (v->bits.pow2 == IXS_POW2_OR_ZERO ||
             v->bits.pow2 == IXS_POW2_POSITIVE) {
    bounds_mark_contradiction(b);
  }
  refine_var_bit_consistency(b, v);
}

static void apply_congruence_known_bits(ixs_bounds *b, ixs_var_bound *v) {
  uint64_t mask, rem;
  if (!v || !int64_modulus_is_pow2(v->modulus))
    return;
  mask = (uint64_t)v->modulus - 1u;
  rem = (uint64_t)v->remainder & mask;
  apply_var_known_bits(b, v, (~rem) & mask, rem & mask);
}

static uint64_t bounds_normalize_residue(int64_t value, uint64_t modulus);
static uint64_t bounds_mul_mod(uint64_t a, uint64_t b, uint64_t modulus);
static bool bounds_mod_inverse(uint64_t value, uint64_t modulus,
                               uint64_t *inverse);

/* Record sym == rem (mod m).  Merges with existing info via CRT.
 * Overflowing constraints are silently ignored.  Direct contradictions are
 * recorded on the bounds object so query APIs can decline concrete answers. */
static void apply_modrem(ixs_bounds *b, const char *name, int64_t m,
                         int64_t rem) {
  ixs_var_bound *v;
  int64_t g, new_mod, old_mod, step, m_div_g, difference;
  uint64_t inverse, k, merged;
  bool changed = false;
  if (m <= 0)
    return;
  bounds_empty_cache_invalidate(b);
  rem = (int64_t)bounds_normalize_residue(rem, (uint64_t)m);
  v = get_or_create_var(b, name);
  if (!v)
    return;
  b->has_modrem = true;
  if (v->modulus == 0) {
    v->modulus = m;
    v->remainder = rem;
    bounds_mark_semantic_changed(b);
    apply_congruence_known_bits(b, v);
    bounds_propagate_difference_bounds(b, name, NULL);
    return;
  }
  old_mod = v->modulus;
  g = ixs_gcd(old_mod, m);
  difference = rem - v->remainder;
  if (bounds_normalize_residue(difference, (uint64_t)g) != 0) {
    bounds_mark_contradiction(b);
    return;
  }
  if (old_mod > INT64_MAX / (m / g))
    return;
  new_mod = old_mod / g * m;
  /* Solve old_mod/g * k == (rem - old_remainder)/g (mod m/g).
   * Keep the modular arithmetic bounded so large public moduli do not turn
   * this merge into either an overflow or a linear scan. */
  step = old_mod / g;
  m_div_g = m / g;
  if (m_div_g == 1) {
    k = 0;
  } else {
    uint64_t target =
        bounds_normalize_residue(difference / g, (uint64_t)m_div_g);
    if (!bounds_mod_inverse((uint64_t)step, (uint64_t)m_div_g, &inverse))
      return;
    k = bounds_mul_mod(target, inverse, (uint64_t)m_div_g);
  }
  merged = bounds_mul_mod((uint64_t)old_mod, k, (uint64_t)new_mod);
  merged += (uint64_t)v->remainder;
  rem = (int64_t)(merged % (uint64_t)new_mod);
  if (v->modulus != new_mod || v->remainder != rem) {
    v->modulus = new_mod;
    v->remainder = rem;
    bounds_mark_semantic_changed(b);
    changed = true;
  }
  apply_congruence_known_bits(b, v);
  if (changed)
    bounds_propagate_difference_bounds(b, name, NULL);
}

/* Recognize Mod(sym, M) == R as a modular congruence.
 *
 * Depends on the CMP normalizer in simp_cmp (cmp_normalize_to_zero):
 * "Mod(sym,M) == R" is rewritten to "(Mod(sym,M) - R) == 0", producing an
 * ADD node.  We must handle both the direct form (R == 0, no normalization)
 * and the normalized ADD form (R != 0). */
static void extract_modrem(ixs_bounds *b, ixs_node *a) {
  ixs_node *mod_node;
  int64_t rem_val;

  if (a->tag != IXS_CMP || a->u.binary.cmp_op != IXS_CMP_EQ)
    return;

  ixs_node *lhs = a->u.binary.lhs;
  ixs_node *rhs = a->u.binary.rhs;

  /* Direct: Mod(sym, M) == 0 */
  if (lhs->tag == IXS_MOD && ixs_node_is_zero(rhs)) {
    mod_node = lhs;
    rem_val = 0;
  } else if (rhs->tag == IXS_MOD && ixs_node_is_zero(lhs)) {
    mod_node = rhs;
    rem_val = 0;
  }
  /* Normalized: ADD(k, c*Mod(sym, M)) == 0, where c = +/-1 and k is integer.
   * c=1:  Mod(sym,M) == -k;   c=-1: Mod(sym,M) == k. */
  else if (ixs_node_is_zero(rhs) && lhs->tag == IXS_ADD &&
           lhs->u.add.nterms == 1 && lhs->u.add.terms[0].term->tag == IXS_MOD) {
    int64_t cp, cq, kp, kq;
    ixs_node_get_rat(lhs->u.add.terms[0].coeff, &cp, &cq);
    ixs_node_get_rat(lhs->u.add.coeff, &kp, &kq);
    if (cq != 1 || kq != 1)
      return;
    if (cp == 1) {
      if (kp == INT64_MIN)
        return;
      rem_val = -kp;
    } else if (cp == -1) {
      rem_val = kp;
    } else {
      return;
    }
    mod_node = lhs->u.add.terms[0].term;
  } else {
    return;
  }

  /* Validate Mod operands and record the congruence. */
  {
    ixs_node *dividend = mod_node->u.binary.lhs;
    ixs_node *modulus = mod_node->u.binary.rhs;
    if (dividend->tag != IXS_SYM || modulus->tag != IXS_INT ||
        modulus->u.ival <= 0)
      return;
    rem_val =
        (int64_t)bounds_normalize_residue(rem_val, (uint64_t)modulus->u.ival);
    apply_modrem(b, dividend->u.name, modulus->u.ival, rem_val);
  }
}

static ixs_cmp_op flip_cmp(ixs_cmp_op op) {
  switch (op) {
  case IXS_CMP_GE:
    return IXS_CMP_LE;
  case IXS_CMP_GT:
    return IXS_CMP_LT;
  case IXS_CMP_LE:
    return IXS_CMP_GE;
  case IXS_CMP_LT:
    return IXS_CMP_GT;
  default:
    return op;
  }
}

static ixs_interval interval_from_integer_zero_cmp(ixs_cmp_op op) {
  ixs_interval iv = ixs_interval_unknown();
  iv.lo_inf = false;
  iv.hi_inf = false;
  switch (op) {
  case IXS_CMP_GT:
    iv.valid = true;
    iv.lo_p = 1;
    iv.lo_q = 1;
    ixs_interval_set_hi_pos_inf(&iv);
    break;
  case IXS_CMP_GE:
    iv.valid = true;
    iv.lo_p = 0;
    iv.lo_q = 1;
    ixs_interval_set_hi_pos_inf(&iv);
    break;
  case IXS_CMP_LT:
    iv.valid = true;
    ixs_interval_set_lo_neg_inf(&iv);
    iv.hi_p = -1;
    iv.hi_q = 1;
    break;
  case IXS_CMP_LE:
    iv.valid = true;
    ixs_interval_set_lo_neg_inf(&iv);
    iv.hi_p = 0;
    iv.hi_q = 1;
    break;
  case IXS_CMP_EQ:
    iv = ixs_interval_exact(0, 1);
    break;
  case IXS_CMP_NE:
    break;
  }
  return iv;
}

static ixs_interval interval_from_sym_cmp_const(ixs_cmp_op op, int64_t cp,
                                                int64_t cq) {
  ixs_interval iv = ixs_interval_unknown();
  iv.lo_inf = false;
  iv.hi_inf = false;
  switch (op) {
  case IXS_CMP_GE:
    iv.valid = true;
    iv.lo_p = cp;
    iv.lo_q = cq;
    ixs_interval_set_hi_pos_inf(&iv);
    break;
  case IXS_CMP_GT: {
    int64_t lo;
    if (!ixs_safe_add(ixs_rat_floor(cp, cq), 1, &lo))
      break;
    iv.valid = true;
    iv.lo_p = lo;
    iv.lo_q = 1;
    ixs_interval_set_hi_pos_inf(&iv);
    break;
  }
  case IXS_CMP_LE:
    iv.valid = true;
    ixs_interval_set_lo_neg_inf(&iv);
    iv.hi_p = cp;
    iv.hi_q = cq;
    break;
  case IXS_CMP_LT: {
    int64_t hi;
    if (!ixs_safe_sub(ixs_rat_ceil(cp, cq), 1, &hi))
      break;
    iv.valid = true;
    ixs_interval_set_lo_neg_inf(&iv);
    iv.hi_p = hi;
    iv.hi_q = 1;
    break;
  }
  case IXS_CMP_EQ:
    iv = ixs_interval_exact(cp, cq);
    break;
  case IXS_CMP_NE:
    break;
  }
  return iv;
}

/* Cache hits are expected O(1); a miss rebuilds the n immediate ADD terms. */
static ixs_node *bounds_expr_without_add_const(ixs_bounds *b, ixs_node *expr) {
  ixs_node *cached;
  ixs_node *result;
  uint32_t i;
  if (!b || !b->ctx || !expr || expr->tag != IXS_ADD ||
      ixs_node_is_zero(expr->u.add.coeff) || expr->u.add.nterms == 0)
    return NULL;

  cached = ixs_node_transform_cache_lookup(
      b->ctx, expr, IXS_NODE_TRANSFORM_ADD_WITHOUT_CONST);
  if (cached)
    return cached;

  result = b->ctx->node_zero;
  for (i = 0; i < expr->u.add.nterms; i++) {
    ixs_node *term = expr->u.add.terms[i].term;
    ixs_node *coeff = expr->u.add.terms[i].coeff;
    ixs_node *scaled =
        ixs_node_is_one(coeff) ? term : simp_mul(b->ctx, coeff, term);
    if (!scaled) {
      b->oom = true;
      return NULL;
    }
    result = simp_add(b->ctx, result, scaled);
    if (!result) {
      b->oom = true;
      return NULL;
    }
  }
  ixs_node_transform_cache_store(b->ctx, expr,
                                 IXS_NODE_TRANSFORM_ADD_WITHOUT_CONST, result);
  return result;
}

/*
 * Write an ADD as offset + scale * primitive, using its first canonical term
 * coefficient as scale. The transform cache makes repeated range queries
 * O(1); a miss is linear only in the immediate ADD terms.
 */
static bool bounds_get_proportional_primitive(
    ixs_bounds *b, ixs_node *expr, ixs_node **primitive, int64_t *scale_p,
    int64_t *scale_q, int64_t *offset_p, int64_t *offset_q) {
  ixs_node *normalized;
  ixs_addterm *terms;
  ixs_arena_mark mark;
  size_t term_bytes;
  uint32_t i;
  /* Context-free proof scopes intentionally disable canonical alias creation.
   */
  if (!b->ctx)
    return false;

  if (expr->tag == IXS_MUL && expr->u.mul.nfactors == 1u &&
      expr->u.mul.factors[0].exp == 1) {
    ixs_node_get_rat(expr->u.mul.coeff, scale_p, scale_q);
    if (*scale_p == 0)
      return false;
    *primitive = expr->u.mul.factors[0].base;
    *offset_p = 0;
    *offset_q = 1;
    return true;
  }

  if (expr->tag != IXS_ADD || expr->u.add.nterms == 0)
    return false;
  ixs_node_get_rat(expr->u.add.terms[0].coeff, scale_p, scale_q);
  ixs_node_get_rat(expr->u.add.coeff, offset_p, offset_q);
  if (*scale_p == 0)
    return false;

  normalized = ixs_node_transform_cache_lookup(
      b->ctx, expr, IXS_NODE_TRANSFORM_PROPORTIONAL_PRIMITIVE);
  if (!normalized) {
    mark = ixs_arena_save(b->scratch);
    term_bytes = (size_t)expr->u.add.nterms * sizeof(*terms);
    if (term_bytes / sizeof(*terms) != expr->u.add.nterms) {
      b->oom = true;
      ixs_arena_restore(b->scratch, mark);
      return false;
    }
    terms = ixs_arena_alloc(b->scratch, term_bytes, sizeof(void *));
    if (!terms) {
      b->oom = true;
      ixs_arena_restore(b->scratch, mark);
      return false;
    }
    for (i = 0; i < expr->u.add.nterms; i++) {
      int64_t coeff_p, coeff_q, normalized_p, normalized_q;
      ixs_node_get_rat(expr->u.add.terms[i].coeff, &coeff_p, &coeff_q);
      if (!ixs_rat_div(coeff_p, coeff_q, *scale_p, *scale_q, &normalized_p,
                       &normalized_q)) {
        ixs_arena_restore(b->scratch, mark);
        return false;
      }
      terms[i].term = expr->u.add.terms[i].term;
      terms[i].coeff = ixs_node_rat(b->ctx, normalized_p, normalized_q);
      if (!terms[i].coeff) {
        b->oom = true;
        ixs_arena_restore(b->scratch, mark);
        return false;
      }
    }
    /* Dividing by the first coefficient makes this coefficient exactly one. */
    normalized = expr->u.add.nterms == 1
                     ? terms[0].term
                     : ixs_node_add(b->ctx, b->ctx->node_zero,
                                    expr->u.add.nterms, terms);
    ixs_arena_restore(b->scratch, mark);
    if (!normalized) {
      b->oom = true;
      return false;
    }
    if (ixs_node_is_sentinel(normalized))
      return false;
    ixs_node_transform_cache_store(
        b->ctx, expr, IXS_NODE_TRANSFORM_PROPORTIONAL_PRIMITIVE, normalized);
  }
  *primitive = normalized;
  return true;
}

static ixs_interval bounds_apply_affine(ixs_interval iv, int64_t scale_p,
                                        int64_t scale_q, int64_t offset_p,
                                        int64_t offset_q) {
  return iv_add(iv_mul_const(iv, scale_p, scale_q),
                ixs_interval_exact(offset_p, offset_q));
}

static ixs_interval bounds_invert_affine(ixs_interval iv, int64_t scale_p,
                                         int64_t scale_q, int64_t offset_p,
                                         int64_t offset_q) {
  int64_t neg_p, neg_q, inverse_p, inverse_q;
  if (!ixs_rat_neg(offset_p, offset_q, &neg_p, &neg_q) ||
      !ixs_rat_div(1, 1, scale_p, scale_q, &inverse_p, &inverse_q))
    return ixs_interval_unknown();
  return iv_mul_const(iv_add(iv, ixs_interval_exact(neg_p, neg_q)), inverse_p,
                      inverse_q);
}

static void add_shifted_add_range(ixs_bounds *b, ixs_node *expr,
                                  ixs_interval iv) {
  ixs_node *base;
  int64_t cp, cq, np, nq;
  ixs_interval offset, shifted;

  base = bounds_expr_without_add_const(b, expr);
  if (!base || base == expr)
    return;
  ixs_node_get_rat(expr->u.add.coeff, &cp, &cq);
  if (!ixs_rat_neg(cp, cq, &np, &nq))
    return;
  offset = ixs_interval_exact(np, nq);
  shifted = iv_add(iv, offset);
  if (shifted.valid)
    ixs_bounds_add_expr(b, base, shifted);
}

static void add_expr_integer_zero_cmp(ixs_bounds *b, ixs_node *expr,
                                      ixs_cmp_op op) {
  ixs_interval iv;
  if (!ixs_node_is_integer_valued(expr))
    return;
  iv = interval_from_integer_zero_cmp(op);
  if (!iv.valid)
    return;
  ixs_bounds_add_expr(b, expr, iv);
  add_shifted_add_range(b, expr, iv);
}

/*
 * Apply "sym op const" bound to the variable's interval.
 */
static void apply_sym_cmp_const(ixs_bounds *b, const char *name, ixs_cmp_op op,
                                int64_t cp, int64_t cq) {
  ixs_var_bound *v = get_or_create_var(b, name);
  ixs_interval old;
  bool changed;
  if (!v)
    return;
  old = v->iv;
  switch (op) {
  case IXS_CMP_GE:
    if (v->iv.lo_inf || ixs_rat_cmp(cp, cq, v->iv.lo_p, v->iv.lo_q) > 0) {
      v->iv.lo_p = cp;
      v->iv.lo_q = cq;
      v->iv.lo_inf = false;
    }
    break;
  case IXS_CMP_GT: {
    int64_t lo;
    if (!ixs_safe_add(ixs_rat_floor(cp, cq), 1, &lo))
      break;
    if (v->iv.lo_inf || ixs_rat_cmp(lo, 1, v->iv.lo_p, v->iv.lo_q) > 0) {
      v->iv.lo_p = lo;
      v->iv.lo_q = 1;
      v->iv.lo_inf = false;
    }
    break;
  }
  case IXS_CMP_LE:
    if (v->iv.hi_inf || ixs_rat_cmp(cp, cq, v->iv.hi_p, v->iv.hi_q) < 0) {
      v->iv.hi_p = cp;
      v->iv.hi_q = cq;
      v->iv.hi_inf = false;
    }
    break;
  case IXS_CMP_LT: {
    int64_t hi;
    if (!ixs_safe_sub(ixs_rat_ceil(cp, cq), 1, &hi))
      break;
    if (v->iv.hi_inf || ixs_rat_cmp(hi, 1, v->iv.hi_p, v->iv.hi_q) < 0) {
      v->iv.hi_p = hi;
      v->iv.hi_q = 1;
      v->iv.hi_inf = false;
    }
    break;
  }
  case IXS_CMP_EQ:
    v->iv.lo_p = cp;
    v->iv.lo_q = cq;
    v->iv.hi_p = cp;
    v->iv.hi_q = cq;
    v->iv.lo_inf = false;
    v->iv.hi_inf = false;
    if (cq == 1)
      apply_exact_int_bits(b, v, cp);
    break;
  case IXS_CMP_NE:
    break;
  }
  changed = !bounds_intervals_equal(old, v->iv);
  if (changed)
    bounds_mark_semantic_changed(b);
  refine_var_bit_consistency(b, v);
  if (changed)
    bounds_propagate_difference_bounds(b, name, NULL);
}

static bool node_get_int_const(ixs_node *n, int64_t *out) {
  if (!n || !out)
    return false;
  if (n->tag == IXS_INT) {
    *out = n->u.ival;
    return true;
  }
  if (n->tag == IXS_RAT && n->u.rat.q == 1) {
    *out = n->u.rat.p;
    return true;
  }
  return false;
}

static bool node_coeff_is(ixs_node *n, int64_t value) {
  int64_t p, q;
  if (!n)
    return false;
  ixs_node_get_rat(n, &p, &q);
  return p == value && q == 1;
}

static bool extract_add_term_eq_const(ixs_node *n, ixs_node **expr,
                                      int64_t *value) {
  int64_t kp, kq, cp, cq;
  if (!n || n->tag != IXS_ADD || n->u.add.nterms != 1)
    return false;
  ixs_node_get_rat(n->u.add.coeff, &kp, &kq);
  ixs_node_get_rat(n->u.add.terms[0].coeff, &cp, &cq);
  if (kq != 1 || cq != 1)
    return false;
  if (cp == 1) {
    if (kp == INT64_MIN)
      return false;
    *value = -kp;
  } else if (cp == -1) {
    *value = kp;
  } else {
    return false;
  }
  *expr = n->u.add.terms[0].term;
  return true;
}

/* Recover "expr == integer" from either direct comparisons or the normalized
 * ADD(k, +/-expr) == 0 form produced by cmp_normalize_to_zero. */
static bool extract_cmp_expr_const(ixs_node *cmp, ixs_node **expr,
                                   int64_t *value) {
  int64_t c;
  if (!cmp || cmp->tag != IXS_CMP || !expr || !value)
    return false;

  if (ixs_node_is_zero(cmp->u.binary.rhs) &&
      extract_add_term_eq_const(cmp->u.binary.lhs, expr, value))
    return true;
  if (ixs_node_is_zero(cmp->u.binary.lhs) &&
      extract_add_term_eq_const(cmp->u.binary.rhs, expr, value))
    return true;

  if (node_get_int_const(cmp->u.binary.rhs, &c) &&
      !ixs_node_is_const(cmp->u.binary.lhs)) {
    *expr = cmp->u.binary.lhs;
    *value = c;
    return true;
  }
  if (node_get_int_const(cmp->u.binary.lhs, &c) &&
      !ixs_node_is_const(cmp->u.binary.rhs)) {
    *expr = cmp->u.binary.rhs;
    *value = c;
    return true;
  }

  return false;
}

static bool extract_add_node_equality(ixs_node *n, ixs_node **a, ixs_node **b) {
  int64_t kp, kq;
  const ixs_addterm *t0, *t1;
  if (!n || n->tag != IXS_ADD || n->u.add.nterms != 2)
    return false;
  ixs_node_get_rat(n->u.add.coeff, &kp, &kq);
  if (kp != 0 || kq != 1)
    return false;
  t0 = &n->u.add.terms[0];
  t1 = &n->u.add.terms[1];
  if (node_coeff_is(t0->coeff, 1) && node_coeff_is(t1->coeff, -1)) {
    *a = t0->term;
    *b = t1->term;
    return true;
  }
  if (node_coeff_is(t0->coeff, -1) && node_coeff_is(t1->coeff, 1)) {
    *a = t0->term;
    *b = t1->term;
    return true;
  }
  return false;
}

static bool extract_cmp_node_equality(ixs_node *cmp, ixs_node **a,
                                      ixs_node **b) {
  if (!cmp || cmp->tag != IXS_CMP || cmp->u.binary.cmp_op != IXS_CMP_EQ)
    return false;
  if (ixs_node_is_zero(cmp->u.binary.rhs))
    return extract_add_node_equality(cmp->u.binary.lhs, a, b);
  if (ixs_node_is_zero(cmp->u.binary.lhs))
    return extract_add_node_equality(cmp->u.binary.rhs, a, b);
  if (!ixs_node_is_const(cmp->u.binary.lhs) &&
      !ixs_node_is_const(cmp->u.binary.rhs)) {
    *a = cmp->u.binary.lhs;
    *b = cmp->u.binary.rhs;
    return true;
  }
  return false;
}

static ixs_node *bounds_cmp_exact_residual(ixs_bounds *b, ixs_node *cmp) {
  ixs_node *difference;
  ixs_arena_mark diag_mark;
  const char **saved_errors;
  size_t saved_nerrors;
  size_t saved_errors_cap;

  if (ixs_node_is_zero(cmp->u.binary.rhs))
    return cmp->u.binary.lhs;
  if (ixs_node_is_zero(cmp->u.binary.lhs))
    return cmp->u.binary.rhs;

  /* Failure to represent an optional residual is a missed relation, not a
   * diagnostic on an otherwise valid comparison. */
  diag_mark = ixs_arena_save(&b->ctx->diag);
  saved_errors = b->ctx->errors;
  saved_nerrors = b->ctx->nerrors;
  saved_errors_cap = b->ctx->errors_cap;
  difference = simp_sub(b->ctx, cmp->u.binary.lhs, cmp->u.binary.rhs);
  if (!difference) {
    b->oom = true;
    return NULL;
  }
  if (!ixs_node_is_sentinel(difference))
    return difference;
  ixs_arena_restore(&b->ctx->diag, diag_mark);
  b->ctx->errors = saved_errors;
  b->ctx->nerrors = saved_nerrors;
  b->ctx->errors_cap = saved_errors_cap;
  return NULL;
}

/* The source residual is already a canonical ADD: its terms are unique and
 * sorted by node key. Stable sign partitioning preserves both properties, so
 * build each side in one hash-consing pass. */
static ixs_node *bounds_build_exact_relation_side(ixs_bounds *b,
                                                  ixs_addterm *terms,
                                                  uint32_t nterms) {
  ixs_node *result;
  if (nterms == 0)
    return b->ctx->node_zero;
  if (nterms == 1) {
    if (ixs_node_is_one(terms[0].coeff))
      return terms[0].term;
    result = simp_mul(b->ctx, terms[0].coeff, terms[0].term);
  } else {
    result = ixs_node_add(b->ctx, b->ctx->node_zero, nterms, terms);
  }
  if (!result) {
    b->oom = true;
    return NULL;
  }
  return ixs_node_is_sentinel(result) ? NULL : result;
}

static bool bounds_partition_exact_relation(ixs_bounds *b, ixs_node *difference,
                                            ixs_node **positive,
                                            ixs_node **negative) {
  ixs_arena_mark mark = ixs_arena_save(b->scratch);
  ixs_addterm *terms;
  ixs_addterm *positive_terms;
  ixs_addterm *negative_terms;
  size_t bytes;
  uint32_t positive_count = 0;
  uint32_t negative_count = 0;
  uint32_t i;
  bool ok = false;

  bytes = (size_t)difference->u.add.nterms * sizeof(*terms);
  if (bytes / sizeof(*terms) != difference->u.add.nterms ||
      bytes > SIZE_MAX / 2u) {
    b->oom = true;
    ixs_arena_restore(b->scratch, mark);
    return false;
  }
  bytes *= 2u;
  terms = ixs_arena_alloc(b->scratch, bytes, sizeof(void *));
  if (!terms) {
    b->oom = true;
    ixs_arena_restore(b->scratch, mark);
    return false;
  }
  positive_terms = terms;
  negative_terms = terms + difference->u.add.nterms;

  for (i = 0; i < difference->u.add.nterms; i++) {
    ixs_node *coefficient = difference->u.add.terms[i].coeff;
    int64_t coefficient_p;
    int64_t coefficient_q;
    int sign;

    ixs_node_get_rat(coefficient, &coefficient_p, &coefficient_q);
    sign = ixs_rat_cmp(coefficient_p, coefficient_q, 0, 1);
    if (sign > 0) {
      positive_terms[positive_count++] = difference->u.add.terms[i];
      continue;
    }
    if (sign == 0)
      continue;
    if (!ixs_rat_neg(coefficient_p, coefficient_q, &coefficient_p,
                     &coefficient_q))
      goto cleanup;
    coefficient = ixs_node_rat(b->ctx, coefficient_p, coefficient_q);
    if (!coefficient) {
      b->oom = true;
      goto cleanup;
    }
    negative_terms[negative_count].term = difference->u.add.terms[i].term;
    negative_terms[negative_count++].coeff = coefficient;
  }

  *positive =
      bounds_build_exact_relation_side(b, positive_terms, positive_count);
  *negative =
      bounds_build_exact_relation_side(b, negative_terms, negative_count);
  ok = *positive && *negative;

cleanup:
  ixs_arena_restore(b->scratch, mark);
  return ok;
}

/* Split an exact comparison residual
 *
 *   constant + positive - negative == 0
 *
 * into the arbitrary-expression relation positive == negative + offset.
 * Query-time use is guarded by independent endpoint-definedness proofs. */
static bool bounds_extract_cmp_exact_relation(ixs_bounds *b, ixs_node *cmp,
                                              ixs_node **lhs, ixs_node **rhs,
                                              int64_t *offset) {
  ixs_node *difference;
  ixs_node *positive;
  ixs_node *negative;
  int64_t constant;
  int64_t constant_q;

  if (!b || !b->ctx || !cmp || cmp->tag != IXS_CMP ||
      cmp->u.binary.cmp_op != IXS_CMP_EQ || !lhs || !rhs || !offset)
    return false;

  difference = bounds_cmp_exact_residual(b, cmp);
  if (!difference)
    return false;
  if (difference->tag != IXS_ADD || difference->u.add.nterms < 2u)
    return false;
  ixs_node_get_rat(difference->u.add.coeff, &constant, &constant_q);
  if (constant_q != 1)
    return false;
  if (!bounds_partition_exact_relation(b, difference, &positive, &negative))
    return false;
  if (ixs_node_is_zero(positive) || ixs_node_is_zero(negative))
    return false;
  if (constant == INT64_MIN) {
    /* positive == negative + 2^63 is not representable in this orientation.
     * Store the reverse relation, whose offset is INT64_MIN. */
    *lhs = negative;
    *rhs = positive;
    *offset = INT64_MIN;
  } else {
    *lhs = positive;
    *rhs = negative;
    *offset = -constant;
  }
  return true;
}

static bool sym_name_matches(ixs_node *n, const char *name) {
  return n && n->tag == IXS_SYM && n->u.name == name;
}

static bool node_is_sym_minus_one(ixs_node *n, const char *name) {
  int64_t kp, kq, cp, cq;
  if (!n || n->tag != IXS_ADD || n->u.add.nterms != 1 ||
      !sym_name_matches(n->u.add.terms[0].term, name))
    return false;
  ixs_node_get_rat(n->u.add.coeff, &kp, &kq);
  ixs_node_get_rat(n->u.add.terms[0].coeff, &cp, &cq);
  return kp == -1 && kq == 1 && cp == 1 && cq == 1;
}

static bool extract_pow2_and(ixs_node *expr, const char **name) {
  ixs_node *a, *b;
  if (!expr || expr->tag != IXS_AND || expr->u.assoc.nargs != 2 || !name)
    return false;
  a = expr->u.assoc.args[0];
  b = expr->u.assoc.args[1];
  if (a->tag == IXS_SYM && node_is_sym_minus_one(b, a->u.name)) {
    *name = a->u.name;
    return true;
  }
  if (b->tag == IXS_SYM && node_is_sym_minus_one(a, b->u.name)) {
    *name = b->u.name;
    return true;
  }
  return false;
}

static bool extract_bitop_sym_mask(ixs_node *expr, ixs_tag tag,
                                   const char **name, int64_t *mask) {
  ixs_node *a, *b;
  if (!expr || expr->tag != tag || expr->u.assoc.nargs != 2 || !name || !mask)
    return false;
  a = expr->u.assoc.args[0];
  b = expr->u.assoc.args[1];
  if (a->tag == IXS_SYM && node_get_int_const(b, mask)) {
    *name = a->u.name;
    return true;
  }
  if (b->tag == IXS_SYM && node_get_int_const(a, mask)) {
    *name = b->u.name;
    return true;
  }
  return false;
}

static void apply_pow2_or_zero(ixs_bounds *b, const char *name) {
  ixs_var_bound *v = get_or_create_var(b, name);
  if (!v)
    return;
  if (v->bits.pow2 == IXS_POW2_UNKNOWN) {
    v->bits.pow2 = IXS_POW2_OR_ZERO;
    bounds_mark_semantic_changed(b);
  }
  refine_var_bit_consistency(b, v);
  apply_sym_cmp_const(b, name, IXS_CMP_GE, 0, 1);
}

static void extract_bitfacts_from_const_eq(ixs_bounds *b, ixs_node *expr,
                                           int64_t value) {
  const char *name;
  int64_t mask;
  uint64_t mask_bits, value_bits;

  if (extract_pow2_and(expr, &name)) {
    if (value == 0)
      apply_pow2_or_zero(b, name);
    return;
  }

  if (extract_bitop_sym_mask(expr, IXS_AND, &name, &mask)) {
    mask_bits = (uint64_t)mask;
    value_bits = (uint64_t)value;
    if ((value_bits & ~mask_bits) != 0) {
      bounds_mark_contradiction(b);
      return;
    }
    apply_known_bits(b, name, (~value_bits) & mask_bits,
                     value_bits & mask_bits);
    return;
  }

  if (extract_bitop_sym_mask(expr, IXS_OR, &name, &mask)) {
    mask_bits = (uint64_t)mask;
    value_bits = (uint64_t)value;
    if ((value_bits & mask_bits) != mask_bits) {
      bounds_mark_contradiction(b);
      return;
    }
    apply_known_bits(b, name, ~value_bits, value_bits & ~mask_bits);
  }
}

static void extract_bitfacts_from_node_eq(ixs_bounds *b, ixs_node *a,
                                          ixs_node *other) {
  const char *name;
  int64_t mask;
  uint64_t mask_bits;

  if (other->tag != IXS_SYM)
    return;
  if (extract_bitop_sym_mask(a, IXS_OR, &name, &mask) &&
      name == other->u.name) {
    apply_known_bits(b, name, 0, (uint64_t)mask);
    return;
  }
  if (extract_bitop_sym_mask(a, IXS_AND, &name, &mask) &&
      name == other->u.name) {
    mask_bits = (uint64_t)mask;
    apply_known_bits(b, name, ~mask_bits, 0);
  }
}

static void extract_bitfacts(ixs_bounds *b, ixs_node *a) {
  ixs_node *expr, *lhs, *rhs;
  int64_t value;
  if (a->tag != IXS_CMP || a->u.binary.cmp_op != IXS_CMP_EQ)
    return;

  if (extract_cmp_expr_const(a, &expr, &value))
    extract_bitfacts_from_const_eq(b, expr, value);

  if (extract_cmp_node_equality(a, &lhs, &rhs)) {
    extract_bitfacts_from_node_eq(b, lhs, rhs);
    extract_bitfacts_from_node_eq(b, rhs, lhs);
  }
}

static ixs_node *bounds_simplify_fact_free(ixs_ctx *ctx, ixs_node *expr) {
  return simp_simplify_bounds(ctx, expr, NULL);
}

static ixs_node *bounds_canonical_expr(ixs_bounds *b, ixs_node *expr) {
  ixs_node *cached, *canonical, *expanded;
  ixs_arena_mark diag_mark;
  const char **saved_errors;
  size_t saved_nerrors, saved_errors_cap;
  if (!b || !b->ctx || !expr || ixs_node_is_sentinel(expr))
    return expr;
  if (expr->tag == IXS_INT || expr->tag == IXS_RAT || expr->tag == IXS_SYM)
    return expr;

  cached = ixs_node_transform_cache_lookup(b->ctx, expr,
                                           IXS_NODE_TRANSFORM_BOUNDS_CANONICAL);
  if (cached)
    return cached;

  /* Alias diagnostics must not leak into otherwise valid range queries. */
  diag_mark = ixs_arena_save(&b->ctx->diag);
  saved_errors = b->ctx->errors;
  saved_nerrors = b->ctx->nerrors;
  saved_errors_cap = b->ctx->errors_cap;
  expanded = expand_impl(b->ctx, expr);
  canonical = expanded && !ixs_node_is_sentinel(expanded)
                  ? bounds_simplify_fact_free(b->ctx, expanded)
                  : expanded;
  ixs_arena_restore(&b->ctx->diag, diag_mark);
  b->ctx->errors = saved_errors;
  b->ctx->nerrors = saved_nerrors;
  b->ctx->errors_cap = saved_errors_cap;

  if (!expanded) {
    b->oom = true;
    return expr;
  }
  if (ixs_node_is_sentinel(expanded))
    return expr;
  if (!canonical) {
    b->oom = true;
    return expr;
  }
  if (ixs_node_is_sentinel(canonical))
    return expanded;
  ixs_node_transform_cache_store(
      b->ctx, expr, IXS_NODE_TRANSFORM_BOUNDS_CANONICAL, canonical);
  return canonical;
}

/* Pointer hashing and bounded linear probing keep range lookup expected O(1).
 */
static size_t bounds_expr_hash_ptr(const ixs_node *expr) {
  return bounds_hash_ptr(expr);
}

static size_t bounds_expr_index_slot(const size_t *index, size_t capacity,
                                     const ixs_expr_bound *exprs,
                                     const ixs_node *expr) {
  size_t slot = bounds_expr_hash_ptr(expr) & (capacity - 1u);
  while (index[slot] && exprs[index[slot] - 1u].expr != expr)
    slot = (slot + 1u) & (capacity - 1u);
  return slot;
}

static ixs_interval bounds_get_expr_overrides(ixs_bounds *b, ixs_node *expr) {
  size_t slot;
  if (!b || !expr || !b->expr_index || !b->expr_index_cap)
    return ixs_interval_unknown();
  slot =
      bounds_expr_index_slot(b->expr_index, b->expr_index_cap, b->exprs, expr);
  if (!b->expr_index[slot])
    return ixs_interval_unknown();
  return b->exprs[b->expr_index[slot] - 1u].iv;
}

/*
 * Rebuilds only at 75% load. Growth is amortized O(1), and publication stays
 * with the caller so a later dense-array allocation cannot split the index.
 */
static bool bounds_prepare_expr_index(ixs_bounds *b, size_t count,
                                      size_t **prepared,
                                      size_t *prepared_capacity) {
  size_t capacity = b->expr_index_cap;
  size_t *index;
  size_t i;

  if (capacity && count <= capacity - capacity / 4u) {
    *prepared = b->expr_index;
    *prepared_capacity = capacity;
    return true;
  }
  if (!capacity)
    capacity = BOUNDS_EXPR_INDEX_INIT_CAP;
  while (count > capacity - capacity / 4u) {
    if (capacity > SIZE_MAX / 2u)
      return false;
    capacity *= 2u;
  }
  if (capacity > SIZE_MAX / sizeof(*index))
    return false;
  index =
      ixs_arena_alloc(b->scratch, capacity * sizeof(*index), sizeof(void *));
  if (!index)
    return false;
  memset(index, 0, capacity * sizeof(*index));
  for (i = 0; i < b->nexprs; i++) {
    size_t slot =
        bounds_expr_index_slot(index, capacity, b->exprs, b->exprs[i].expr);
    index[slot] = i + 1u;
  }
  *prepared = index;
  *prepared_capacity = capacity;
  return true;
}

static bool bounds_prepare_mod_inverse_heads(ixs_bounds *b, size_t count) {
  size_t capacity = b->mod_inverse_head_cap;
  size_t *grown;
  if (count <= capacity)
    return true;
  if (!capacity)
    capacity = BOUNDS_VAR_INDEX_INIT_CAP;
  while (capacity < count) {
    if (capacity > SIZE_MAX / 2u)
      return false;
    capacity *= 2u;
  }
  if (b->mod_inverse_head_cap > SIZE_MAX / sizeof(*grown) ||
      capacity > SIZE_MAX / sizeof(*grown))
    return false;
  grown =
      ixs_arena_grow(b->scratch, b->mod_inverse_heads,
                     b->mod_inverse_head_cap * sizeof(*b->mod_inverse_heads),
                     capacity * sizeof(*b->mod_inverse_heads), sizeof(void *));
  if (!grown)
    return false;
  memset(grown + b->mod_inverse_head_cap, 0,
         (capacity - b->mod_inverse_head_cap) * sizeof(*grown));
  b->mod_inverse_heads = grown;
  b->mod_inverse_head_cap = capacity;
  return true;
}

static bool bounds_grow_mod_inverse_watchers(ixs_bounds *b) {
  size_t capacity = b->mod_inverse_watcher_cap ? b->mod_inverse_watcher_cap * 2u
                                               : BOUNDS_EXPR_INDEX_INIT_CAP;
  ixs_mod_inverse_watcher *grown;
  if (capacity <= b->mod_inverse_watcher_cap ||
      b->mod_inverse_watcher_cap > SIZE_MAX / sizeof(*grown) ||
      capacity > SIZE_MAX / sizeof(*grown))
    return false;
  grown = ixs_arena_grow(
      b->scratch, b->mod_inverse_watchers,
      b->mod_inverse_watcher_cap * sizeof(*b->mod_inverse_watchers),
      capacity * sizeof(*b->mod_inverse_watchers), sizeof(void *));
  if (!grown)
    return false;
  b->mod_inverse_watchers = grown;
  b->mod_inverse_watcher_cap = capacity;
  return true;
}

static bool bounds_register_mod_inverse_watcher(ixs_bounds *b,
                                                size_t expr_index) {
  ixs_node *expr;
  size_t var_index;
  ixs_mod_inverse_watcher *watcher;
  if (expr_index >= b->nexprs)
    return false;
  expr = b->exprs[expr_index].expr;
  if (expr->tag != IXS_MOD || expr->u.binary.lhs->tag != IXS_SYM ||
      expr->u.binary.rhs->tag != IXS_INT || expr->u.binary.rhs->u.ival <= 0)
    return true;
  if (!get_or_create_var_index(b, expr->u.binary.lhs->u.name, &var_index) ||
      !bounds_prepare_mod_inverse_heads(b, b->nvars) ||
      (b->nmod_inverse_watchers >= b->mod_inverse_watcher_cap &&
       !bounds_grow_mod_inverse_watchers(b)))
    return false;
  watcher = &b->mod_inverse_watchers[b->nmod_inverse_watchers];
  watcher->expr_index = expr_index;
  watcher->next = b->mod_inverse_heads[var_index];
  b->mod_inverse_heads[var_index] = b->nmod_inverse_watchers + 1u;
  b->nmod_inverse_watchers++;
  return true;
}

static void bounds_add_expr_raw(ixs_bounds *b, ixs_node *expr,
                                ixs_interval iv) {
  ixs_expr_bound *exprs;
  size_t *index;
  size_t expr_capacity;
  size_t index_capacity;
  size_t slot;

  if (!b || !expr || !iv.valid || b->oom)
    return;

  if (b->expr_index_cap) {
    slot = bounds_expr_index_slot(b->expr_index, b->expr_index_cap, b->exprs,
                                  expr);
    if (b->expr_index[slot]) {
      ixs_expr_bound *bound = &b->exprs[b->expr_index[slot] - 1u];
      if (bound->iv.valid) {
        ixs_interval refined = iv_intersect(bound->iv, iv);
        if (!bounds_intervals_equal(bound->iv, refined)) {
          bound->iv = refined;
          bounds_mark_semantic_changed(b);
        }
      }
      bounds_cache_clear(b);
      return;
    }
  }

  if (b->nexprs == SIZE_MAX ||
      !bounds_prepare_expr_index(b, b->nexprs + 1u, &index, &index_capacity)) {
    b->oom = true;
    return;
  }

  exprs = b->exprs;
  expr_capacity = b->expr_cap;
  if (b->nexprs >= expr_capacity) {
    if (expr_capacity > SIZE_MAX / 2u) {
      b->oom = true;
      return;
    }
    expr_capacity = expr_capacity ? expr_capacity * 2u : 4u;
    if (expr_capacity > SIZE_MAX / sizeof(*exprs)) {
      b->oom = true;
      return;
    }
    exprs = ixs_arena_alloc(b->scratch, expr_capacity * sizeof(*exprs),
                            sizeof(void *));
    if (!exprs) {
      b->oom = true;
      return;
    }
    if (b->nexprs)
      memcpy(exprs, b->exprs, b->nexprs * sizeof(*exprs));
  }

  b->exprs = exprs;
  b->expr_cap = expr_capacity;
  b->expr_index = index;
  b->expr_index_cap = index_capacity;
  slot =
      bounds_expr_index_slot(b->expr_index, b->expr_index_cap, b->exprs, expr);
  b->exprs[b->nexprs].expr = expr;
  b->exprs[b->nexprs].iv = iv;
  b->expr_index[slot] = b->nexprs + 1u;
  b->nexprs++;
  if (!bounds_register_mod_inverse_watcher(b, b->nexprs - 1u)) {
    b->oom = true;
    return;
  }
  bounds_mark_semantic_changed(b);
  bounds_cache_clear(b);
}

static size_t
bounds_equality_endpoint_slot(const size_t *index, size_t capacity,
                              const ixs_equality_endpoint *endpoints,
                              const ixs_node *expr) {
  size_t slot = bounds_expr_hash_ptr(expr) & (capacity - 1u);
  while (index[slot] && endpoints[index[slot] - 1u].expr != expr)
    slot = (slot + 1u) & (capacity - 1u);
  return slot;
}

static bool bounds_find_equality_endpoint(const ixs_bounds *b,
                                          const ixs_node *expr,
                                          size_t *endpoint_index) {
  size_t slot;
  if (!b || !expr || !endpoint_index || !b->equality_endpoint_index ||
      !b->equality_endpoint_index_cap)
    return false;
  slot = bounds_equality_endpoint_slot(b->equality_endpoint_index,
                                       b->equality_endpoint_index_cap,
                                       b->equality_endpoints, expr);
  if (!b->equality_endpoint_index[slot])
    return false;
  *endpoint_index = b->equality_endpoint_index[slot] - 1u;
  return true;
}

/* Endpoint lookup is expected O(1); growth rehashes at 75% load. */
static bool bounds_prepare_equality_endpoint_index(ixs_bounds *b, size_t count,
                                                   size_t **prepared,
                                                   size_t *prepared_capacity) {
  size_t capacity = b->equality_endpoint_index_cap;
  size_t *index;
  size_t i;

  if (capacity && count <= capacity - capacity / 4u) {
    *prepared = b->equality_endpoint_index;
    *prepared_capacity = capacity;
    return true;
  }
  if (!capacity)
    capacity = BOUNDS_EQUALITY_ENDPOINT_INDEX_INIT_CAP;
  while (count > capacity - capacity / 4u) {
    if (capacity > SIZE_MAX / 2u)
      return false;
    capacity *= 2u;
  }
  if (capacity > SIZE_MAX / sizeof(*index))
    return false;
  index =
      ixs_arena_alloc(b->scratch, capacity * sizeof(*index), sizeof(void *));
  if (!index)
    return false;
  memset(index, 0, capacity * sizeof(*index));
  for (i = 0; i < b->nequality_endpoints; i++) {
    size_t slot = bounds_equality_endpoint_slot(
        index, capacity, b->equality_endpoints, b->equality_endpoints[i].expr);
    index[slot] = i + 1u;
  }
  *prepared = index;
  *prepared_capacity = capacity;
  return true;
}

static bool bounds_get_or_create_equality_endpoint(ixs_bounds *b,
                                                   ixs_node *expr,
                                                   size_t *endpoint_index) {
  ixs_equality_endpoint *endpoints;
  size_t *index;
  size_t endpoint_capacity;
  size_t index_capacity;
  size_t slot;

  if (bounds_find_equality_endpoint(b, expr, endpoint_index))
    return true;
  if (b->nequality_endpoints == SIZE_MAX ||
      !bounds_prepare_equality_endpoint_index(b, b->nequality_endpoints + 1u,
                                              &index, &index_capacity))
    return false;

  endpoints = b->equality_endpoints;
  endpoint_capacity = b->equality_endpoint_cap;
  if (b->nequality_endpoints >= endpoint_capacity) {
    if (endpoint_capacity > SIZE_MAX / 2u)
      return false;
    endpoint_capacity = endpoint_capacity ? endpoint_capacity * 2u : 4u;
    if (endpoint_capacity > SIZE_MAX / sizeof(*endpoints))
      return false;
    endpoints = ixs_arena_alloc(
        b->scratch, endpoint_capacity * sizeof(*endpoints), sizeof(void *));
    if (!endpoints)
      return false;
    if (b->nequality_endpoints)
      memcpy(endpoints, b->equality_endpoints,
             b->nequality_endpoints * sizeof(*endpoints));
  }

  b->equality_endpoints = endpoints;
  b->equality_endpoint_cap = endpoint_capacity;
  b->equality_endpoint_index = index;
  b->equality_endpoint_index_cap = index_capacity;
  slot = bounds_equality_endpoint_slot(b->equality_endpoint_index,
                                       b->equality_endpoint_index_cap,
                                       b->equality_endpoints, expr);
  b->equality_endpoints[b->nequality_endpoints].expr = expr;
  b->equality_endpoints[b->nequality_endpoints].edges = NULL;
  b->equality_endpoints[b->nequality_endpoints].parent = b->nequality_endpoints;
  b->equality_endpoints[b->nequality_endpoints].rank = 0;
  b->equality_endpoints[b->nequality_endpoints].offset =
      bounds_wide_offset_from_int64(0);
  b->equality_endpoint_index[slot] = b->nequality_endpoints + 1u;
  *endpoint_index = b->nequality_endpoints;
  b->nequality_endpoints++;
  return true;
}

static size_t bounds_equality_hash(ixs_node *lhs, ixs_node *rhs,
                                   int64_t offset) {
  uint64_t x = (uint64_t)bounds_expr_hash_ptr(lhs);
  x ^= (uint64_t)bounds_expr_hash_ptr(rhs) + UINT64_C(0x9e3779b97f4a7c15) +
       (x << 6) + (x >> 2);
  x ^= (uint64_t)offset + UINT64_C(0x9e3779b97f4a7c15) + (x << 6) + (x >> 2);
  x ^= x >> 33;
  x *= UINT64_C(0xff51afd7ed558ccd);
  x ^= x >> 33;
  return (size_t)x;
}

static size_t bounds_equality_index_slot(ixs_equality_edge *const *index,
                                         size_t capacity, ixs_node *lhs,
                                         ixs_node *rhs, int64_t offset) {
  size_t slot = bounds_equality_hash(lhs, rhs, offset) & (capacity - 1u);
  while (index[slot] && (index[slot]->lhs != lhs || index[slot]->rhs != rhs ||
                         index[slot]->offset != offset))
    slot = (slot + 1u) & (capacity - 1u);
  return slot;
}

/* Exact-relation edge lookup is expected O(1); growth rehashes at 75%. */
static bool bounds_prepare_equality_index(ixs_bounds *b, size_t count,
                                          ixs_equality_edge ***prepared,
                                          size_t *prepared_capacity) {
  size_t capacity = b->equality_index_cap;
  ixs_equality_edge **index;
  size_t i;

  if (capacity && count <= capacity - capacity / 4u) {
    *prepared = b->equality_index;
    *prepared_capacity = capacity;
    return true;
  }
  if (!capacity)
    capacity = BOUNDS_EQUALITY_INDEX_INIT_CAP;
  while (count > capacity - capacity / 4u) {
    if (capacity > SIZE_MAX / 2u)
      return false;
    capacity *= 2u;
  }
  if (capacity > SIZE_MAX / sizeof(*index))
    return false;
  index =
      ixs_arena_alloc(b->scratch, capacity * sizeof(*index), sizeof(void *));
  if (!index)
    return false;
  memset(index, 0, capacity * sizeof(*index));
  for (i = 0; i < b->equality_index_cap; i++) {
    ixs_equality_edge *edge = b->equality_index[i];
    size_t slot;
    if (!edge)
      continue;
    slot = bounds_equality_index_slot(index, capacity, edge->lhs, edge->rhs,
                                      edge->offset);
    index[slot] = edge;
  }
  *prepared = index;
  *prepared_capacity = capacity;
  return true;
}

static bool bounds_has_exact_relation(const ixs_bounds *b, ixs_node *lhs,
                                      ixs_node *rhs, int64_t offset) {
  int64_t reverse_offset;
  size_t slot;
  if (!b->equality_index || !b->equality_index_cap)
    return false;
  slot = bounds_equality_index_slot(b->equality_index, b->equality_index_cap,
                                    lhs, rhs, offset);
  if (b->equality_index[slot])
    return true;
  if (!ixs_safe_neg(offset, &reverse_offset))
    return false;
  slot = bounds_equality_index_slot(b->equality_index, b->equality_index_cap,
                                    rhs, lhs, reverse_offset);
  return b->equality_index[slot] != NULL;
}

static void bounds_add_exact_relation(ixs_bounds *b, ixs_node *lhs,
                                      ixs_node *rhs, int64_t offset) {
  ixs_equality_edge **index;
  ixs_equality_edge *edge;
  bounds_equality_union_status union_status;
  size_t lhs_endpoint;
  size_t rhs_endpoint;
  size_t index_capacity;
  size_t slot;

  if (!b || !lhs || !rhs || b->oom || b->contradiction)
    return;
  if (lhs == rhs) {
    if (offset != 0)
      bounds_mark_contradiction(b);
    return;
  }
  if (bounds_has_exact_relation(b, lhs, rhs, offset))
    return;
  if (b->nequalities == SIZE_MAX) {
    b->oom = true;
    return;
  }
  if (!bounds_get_or_create_equality_endpoint(b, lhs, &lhs_endpoint) ||
      !bounds_get_or_create_equality_endpoint(b, rhs, &rhs_endpoint)) {
    b->oom = true;
    return;
  }
  union_status =
      bounds_union_equality_endpoints(b, lhs_endpoint, rhs_endpoint, offset);
  if (union_status == BOUNDS_EQUALITY_UNION_CONFLICT) {
    bounds_mark_contradiction(b);
    return;
  }
  if (union_status == BOUNDS_EQUALITY_UNION_INVALID) {
    assert(!"invalid exact-relation component topology");
    return;
  }
  if (!bounds_prepare_equality_index(b, b->nequalities + 1u, &index,
                                     &index_capacity)) {
    b->oom = true;
    return;
  }
  edge = ixs_arena_alloc(b->scratch, sizeof(*edge), sizeof(void *));
  if (!edge) {
    b->oom = true;
    return;
  }
  edge->lhs = lhs;
  edge->rhs = rhs;
  edge->lhs_endpoint = lhs_endpoint;
  edge->rhs_endpoint = rhs_endpoint;
  edge->offset = offset;
  edge->next_lhs = b->equality_endpoints[lhs_endpoint].edges;
  edge->next_rhs = b->equality_endpoints[rhs_endpoint].edges;
  b->equality_endpoints[lhs_endpoint].edges = edge;
  b->equality_endpoints[rhs_endpoint].edges = edge;
  b->equality_index = index;
  b->equality_index_cap = index_capacity;
  slot = bounds_equality_index_slot(index, index_capacity, lhs, rhs, offset);
  index[slot] = edge;
  b->nequalities++;
  bounds_mark_semantic_changed(b);
  bounds_cache_clear(b);
}

static uint64_t bounds_int64_magnitude(int64_t value) {
  if (value >= 0)
    return (uint64_t)value;
  return (uint64_t)(-(value + 1)) + 1u;
}

static bounds_wide_offset bounds_wide_offset_from_int64(int64_t value) {
  bounds_wide_offset result;
  result.lo = bounds_int64_magnitude(value);
  result.hi = 0;
  result.negative = value < 0;
  return result;
}

static bounds_wide_offset bounds_wide_offset_negate(bounds_wide_offset value) {
  if (value.lo != 0 || value.hi != 0)
    value.negative = !value.negative;
  return value;
}

static int bounds_wide_offset_magnitude_cmp(bounds_wide_offset a,
                                            bounds_wide_offset b) {
  if (a.hi != b.hi)
    return a.hi < b.hi ? -1 : 1;
  if (a.lo != b.lo)
    return a.lo < b.lo ? -1 : 1;
  return 0;
}

static bool bounds_wide_offset_add_magnitudes(bounds_wide_offset a,
                                              bounds_wide_offset b,
                                              bounds_wide_offset *result) {
  uint64_t hi;
  uint64_t lo = a.lo + b.lo;
  bool carry = lo < a.lo;
  hi = a.hi + b.hi;
  if (hi < a.hi || (carry && hi == UINT64_MAX))
    return false;
  result->lo = lo;
  result->hi = hi + (carry ? 1u : 0u);
  return true;
}

static void bounds_wide_offset_subtract_magnitudes(bounds_wide_offset larger,
                                                   bounds_wide_offset smaller,
                                                   bounds_wide_offset *result) {
  bool borrow = larger.lo < smaller.lo;
  result->lo = larger.lo - smaller.lo;
  result->hi = larger.hi - smaller.hi - (borrow ? 1u : 0u);
}

static bool bounds_wide_offset_add(bounds_wide_offset a, bounds_wide_offset b,
                                   bounds_wide_offset *result) {
  int magnitude_cmp;
  if (a.negative == b.negative) {
    if (!bounds_wide_offset_add_magnitudes(a, b, result))
      return false;
    result->negative = a.negative;
  } else {
    magnitude_cmp = bounds_wide_offset_magnitude_cmp(a, b);
    if (magnitude_cmp >= 0) {
      bounds_wide_offset_subtract_magnitudes(a, b, result);
      result->negative = a.negative;
    } else {
      bounds_wide_offset_subtract_magnitudes(b, a, result);
      result->negative = b.negative;
    }
  }
  if (result->lo == 0 && result->hi == 0)
    result->negative = false;
  return true;
}

static bool bounds_wide_offset_equal(bounds_wide_offset a,
                                     bounds_wide_offset b) {
  return a.lo == b.lo && a.hi == b.hi && a.negative == b.negative;
}

static bool bounds_equality_root_offset(const ixs_bounds *b,
                                        size_t endpoint_index,
                                        size_t *root_index,
                                        bounds_wide_offset *offset) {
  bounds_wide_offset total = {0, 0, false};
  size_t current = endpoint_index;
  size_t hops = 0;
  if (!b || !root_index || !offset || endpoint_index >= b->nequality_endpoints)
    return false;
  while (b->equality_endpoints[current].parent != current) {
    size_t parent = b->equality_endpoints[current].parent;
    if (parent >= b->nequality_endpoints || hops++ >= b->nequality_endpoints ||
        !bounds_wide_offset_add(total, b->equality_endpoints[current].offset,
                                &total))
      return false;
    current = parent;
  }
  *root_index = current;
  *offset = total;
  return true;
}

static bounds_equality_union_status
bounds_union_equality_endpoints(ixs_bounds *b, size_t lhs_endpoint,
                                size_t rhs_endpoint, int64_t offset) {
  bounds_wide_offset lhs_offset;
  bounds_wide_offset rhs_offset;
  bounds_wide_offset requested = bounds_wide_offset_from_int64(offset);
  bounds_wide_offset implied;
  bounds_wide_offset root_delta;
  size_t lhs_root;
  size_t rhs_root;
  size_t lhs_rank;
  size_t rhs_rank;
  if (!bounds_equality_root_offset(b, lhs_endpoint, &lhs_root, &lhs_offset) ||
      !bounds_equality_root_offset(b, rhs_endpoint, &rhs_root, &rhs_offset))
    return BOUNDS_EQUALITY_UNION_INVALID;
  if (lhs_root == rhs_root) {
    if (!bounds_wide_offset_add(
            lhs_offset, bounds_wide_offset_negate(rhs_offset), &implied))
      return BOUNDS_EQUALITY_UNION_INVALID;
    return bounds_wide_offset_equal(implied, requested)
               ? BOUNDS_EQUALITY_UNION_MATCHED
               : BOUNDS_EQUALITY_UNION_CONFLICT;
  }

  /* lhs = lhs_root + lhs_offset and rhs = rhs_root + rhs_offset, so
   * lhs_root - rhs_root = rhs_offset + requested - lhs_offset. */
  if (!bounds_wide_offset_add(rhs_offset, requested, &root_delta) ||
      !bounds_wide_offset_add(root_delta, bounds_wide_offset_negate(lhs_offset),
                              &root_delta))
    return BOUNDS_EQUALITY_UNION_INVALID;
  lhs_rank = b->equality_endpoints[lhs_root].rank;
  rhs_rank = b->equality_endpoints[rhs_root].rank;
  if (lhs_rank < rhs_rank) {
    b->equality_endpoints[lhs_root].parent = rhs_root;
    b->equality_endpoints[lhs_root].offset = root_delta;
  } else {
    if (lhs_rank == rhs_rank && lhs_rank == SIZE_MAX)
      return BOUNDS_EQUALITY_UNION_INVALID;
    b->equality_endpoints[rhs_root].parent = lhs_root;
    b->equality_endpoints[rhs_root].offset =
        bounds_wide_offset_negate(root_delta);
    if (lhs_rank == rhs_rank)
      b->equality_endpoints[lhs_root].rank++;
  }
  return BOUNDS_EQUALITY_UNION_MERGED;
}

static bool bounds_wide_offset_to_int64(bounds_wide_offset value,
                                        int64_t *result) {
  uint64_t negative_limit = (uint64_t)INT64_MAX + 1u;
  if (value.hi != 0)
    return false;
  if (!value.negative) {
    if (value.lo > (uint64_t)INT64_MAX)
      return false;
    *result = (int64_t)value.lo;
    return true;
  }
  if (value.lo > negative_limit)
    return false;
  if (value.lo == negative_limit) {
    *result = INT64_MIN;
    return true;
  }
  *result = -(int64_t)value.lo;
  return true;
}

static void bounds_u64_mul_wide(uint64_t lhs, uint64_t rhs, uint64_t *lo,
                                uint64_t *hi) {
  const uint64_t mask = UINT64_C(0xffffffff);
  uint64_t lhs_lo = lhs & mask;
  uint64_t lhs_hi = lhs >> 32;
  uint64_t rhs_lo = rhs & mask;
  uint64_t rhs_hi = rhs >> 32;
  uint64_t p0 = lhs_lo * rhs_lo;
  uint64_t p1 = lhs_lo * rhs_hi;
  uint64_t p2 = lhs_hi * rhs_lo;
  uint64_t p3 = lhs_hi * rhs_hi;
  uint64_t middle = (p0 >> 32) + (p1 & mask) + (p2 & mask);
  *lo = (p0 & mask) | (middle << 32);
  *hi = p3 + (p1 >> 32) + (p2 >> 32) + (middle >> 32);
}

/* Add an integer offset to p/q without first narrowing the offset. A
 * two-limb offset cannot cancel back into int64 once its high limb is set,
 * because |p| is at most 2^63 and q is positive. */
static bool bounds_wide_offset_add_rational(bounds_wide_offset offset,
                                            int64_t p, int64_t q,
                                            int64_t *result_p) {
  bounds_wide_offset scaled;
  bounds_wide_offset sum;
  if (q <= 0 || offset.hi != 0)
    return false;
  bounds_u64_mul_wide(offset.lo, (uint64_t)q, &scaled.lo, &scaled.hi);
  scaled.negative = offset.negative;
  if (!bounds_wide_offset_add(scaled, bounds_wide_offset_from_int64(p), &sum))
    return false;
  return bounds_wide_offset_to_int64(sum, result_p);
}

/* Projection bounds remain attached to their original peer.  Comparing them
 * in component coordinates must not first narrow the component-coordinate
 * value: a peer offset at an int64 boundary can cancel only when the result is
 * translated directly to the endpoint being queried.  Floor-splitting p/q
 * leaves a signed integer plus a nonnegative proper fraction.  Three limbs are
 * sufficient for a two-limb graph offset plus one int64 quotient. */
typedef struct {
  uint64_t lo;
  uint64_t mid;
  uint64_t hi;
  bool negative;
} bounds_projection_integer;

typedef struct {
  int64_t p;
  int64_t q;
  bounds_wide_offset peer_offset;
  bool present;
} bounds_projection_bound;

static int
bounds_projection_integer_magnitude_cmp(bounds_projection_integer lhs,
                                        bounds_projection_integer rhs) {
  if (lhs.hi != rhs.hi)
    return lhs.hi < rhs.hi ? -1 : 1;
  if (lhs.mid != rhs.mid)
    return lhs.mid < rhs.mid ? -1 : 1;
  if (lhs.lo != rhs.lo)
    return lhs.lo < rhs.lo ? -1 : 1;
  return 0;
}

static void bounds_projection_integer_subtract_magnitudes(
    bounds_projection_integer larger, bounds_projection_integer smaller,
    bounds_projection_integer *result) {
  bool borrow_lo = larger.lo < smaller.lo;
  uint64_t mid_subtrahend = smaller.mid + (borrow_lo ? 1u : 0u);
  bool mid_subtrahend_overflow = mid_subtrahend < smaller.mid;
  bool borrow_mid = mid_subtrahend_overflow || larger.mid < mid_subtrahend;
  result->lo = larger.lo - smaller.lo;
  result->mid = larger.mid - mid_subtrahend;
  result->hi = larger.hi - smaller.hi - (borrow_mid ? 1u : 0u);
}

static void bounds_projection_integer_add(bounds_projection_integer lhs,
                                          bounds_projection_integer rhs,
                                          bounds_projection_integer *result) {
  int magnitude_cmp;
  if (lhs.negative == rhs.negative) {
    bool carry_lo;
    bool carry_mid;
    result->lo = lhs.lo + rhs.lo;
    carry_lo = result->lo < lhs.lo;
    result->mid = lhs.mid + rhs.mid;
    carry_mid = result->mid < lhs.mid;
    if (carry_lo) {
      uint64_t old_mid = result->mid;
      result->mid++;
      if (result->mid < old_mid)
        carry_mid = true;
    }
    result->hi = lhs.hi + rhs.hi + (carry_mid ? 1u : 0u);
    result->negative = lhs.negative;
  } else {
    magnitude_cmp = bounds_projection_integer_magnitude_cmp(lhs, rhs);
    if (magnitude_cmp >= 0) {
      bounds_projection_integer_subtract_magnitudes(lhs, rhs, result);
      result->negative = lhs.negative;
    } else {
      bounds_projection_integer_subtract_magnitudes(rhs, lhs, result);
      result->negative = rhs.negative;
    }
  }
  if (result->lo == 0 && result->mid == 0 && result->hi == 0)
    result->negative = false;
}

static int bounds_projection_integer_cmp(bounds_projection_integer lhs,
                                         bounds_projection_integer rhs) {
  int magnitude_cmp;
  if (lhs.negative != rhs.negative)
    return lhs.negative ? -1 : 1;
  magnitude_cmp = bounds_projection_integer_magnitude_cmp(lhs, rhs);
  return lhs.negative ? -magnitude_cmp : magnitude_cmp;
}

static bool bounds_projection_coordinate(int64_t p, int64_t q,
                                         bounds_wide_offset peer_offset,
                                         bounds_projection_integer *integer,
                                         uint64_t *remainder) {
  bounds_projection_integer quotient = {0, 0, 0, false};
  bounds_projection_integer offset = {0, 0, 0, false};
  uint64_t magnitude;
  uint64_t denominator;
  uint64_t quotient_magnitude;
  uint64_t truncated_remainder;
  if (q <= 0)
    return false;
  denominator = (uint64_t)q;
  magnitude = bounds_int64_magnitude(p);
  quotient_magnitude = magnitude / denominator;
  truncated_remainder = magnitude % denominator;
  if (p < 0 && truncated_remainder != 0) {
    quotient_magnitude++;
    *remainder = denominator - truncated_remainder;
  } else {
    *remainder = truncated_remainder;
  }
  quotient.lo = quotient_magnitude;
  quotient.negative = p < 0 && quotient_magnitude != 0;
  offset.lo = peer_offset.lo;
  offset.mid = peer_offset.hi;
  offset.negative =
      !peer_offset.negative && (peer_offset.lo != 0 || peer_offset.hi != 0);
  if (peer_offset.negative)
    offset.negative = false;
  bounds_projection_integer_add(quotient, offset, integer);
  return true;
}

static bool bounds_projection_bound_cmp(int64_t lhs_p, int64_t lhs_q,
                                        bounds_wide_offset lhs_offset,
                                        int64_t rhs_p, int64_t rhs_q,
                                        bounds_wide_offset rhs_offset,
                                        int *result) {
  bounds_projection_integer lhs_integer;
  bounds_projection_integer rhs_integer;
  uint64_t lhs_remainder;
  uint64_t rhs_remainder;
  uint64_t lhs_product_lo;
  uint64_t lhs_product_hi;
  uint64_t rhs_product_lo;
  uint64_t rhs_product_hi;
  int integer_cmp;
  if (!bounds_projection_coordinate(lhs_p, lhs_q, lhs_offset, &lhs_integer,
                                    &lhs_remainder) ||
      !bounds_projection_coordinate(rhs_p, rhs_q, rhs_offset, &rhs_integer,
                                    &rhs_remainder))
    return false;
  integer_cmp = bounds_projection_integer_cmp(lhs_integer, rhs_integer);
  if (integer_cmp != 0) {
    *result = integer_cmp;
    return true;
  }
  bounds_u64_mul_wide(lhs_remainder, (uint64_t)rhs_q, &lhs_product_lo,
                      &lhs_product_hi);
  bounds_u64_mul_wide(rhs_remainder, (uint64_t)lhs_q, &rhs_product_lo,
                      &rhs_product_hi);
  if (lhs_product_hi != rhs_product_hi)
    *result = lhs_product_hi < rhs_product_hi ? -1 : 1;
  else if (lhs_product_lo != rhs_product_lo)
    *result = lhs_product_lo < rhs_product_lo ? -1 : 1;
  else
    *result = 0;
  return true;
}

static bool bounds_projection_delta(bounds_wide_offset endpoint_offset,
                                    bounds_wide_offset peer_offset,
                                    bounds_wide_offset *delta) {
  return bounds_wide_offset_add(endpoint_offset,
                                bounds_wide_offset_negate(peer_offset), delta);
}

static ixs_interval bounds_projection_unbounded_interval(void) {
  ixs_interval result = ixs_interval_exact(0, 1);
  ixs_interval_set_lo_neg_inf(&result);
  ixs_interval_set_hi_pos_inf(&result);
  return result;
}

static ixs_interval
bounds_projection_apply(ixs_interval intrinsic,
                        bounds_wide_offset endpoint_offset,
                        const bounds_projection_bound *lower,
                        const bounds_projection_bound *upper) {
  ixs_interval result =
      intrinsic.valid ? intrinsic : bounds_projection_unbounded_interval();
  bounds_wide_offset delta;
  int64_t shifted;
  if (lower->present) {
    if (!bounds_projection_delta(endpoint_offset, lower->peer_offset, &delta) ||
        !bounds_wide_offset_add_rational(delta, lower->p, lower->q, &shifted))
      return ixs_interval_unknown();
    if (result.lo_inf ||
        ixs_rat_cmp(shifted, lower->q, result.lo_p, result.lo_q) > 0) {
      result.lo_inf = false;
      result.lo_p = shifted;
      result.lo_q = lower->q;
    }
  }
  if (upper->present) {
    if (!bounds_projection_delta(endpoint_offset, upper->peer_offset, &delta) ||
        !bounds_wide_offset_add_rational(delta, upper->p, upper->q, &shifted))
      return ixs_interval_unknown();
    if (result.hi_inf ||
        ixs_rat_cmp(shifted, upper->q, result.hi_p, result.hi_q) < 0) {
      result.hi_inf = false;
      result.hi_p = shifted;
      result.hi_q = upper->q;
    }
  }
  return ixs_interval_is_empty(result) ? ixs_interval_unknown() : result;
}

static ixs_check_result bounds_check_defined_without_equality(ixs_bounds *b,
                                                              ixs_node *expr,
                                                              bool *oom,
                                                              bool *limited) {
  ixs_check_result result;
  assert(b->equality_disabled_depth != UINT_MAX);
  b->equality_disabled_depth++;
  result = bounds_check_defined_detail(b, expr, oom, limited);
  b->equality_disabled_depth--;
  return result;
}

static bool bounds_equality_walk_init(ixs_bounds *b,
                                      bounds_equality_walk *walk) {
  memset(walk, 0, sizeof(*walk));
  walk->mark = ixs_arena_save(b->scratch);
  walk->initialized = true;
  return true;
}

static void bounds_equality_walk_destroy(ixs_bounds *b,
                                         bounds_equality_walk *walk) {
  if (walk && walk->initialized) {
    ixs_arena_restore(b->scratch, walk->mark);
    walk->initialized = false;
  }
}

static bool bounds_equality_walk_grow(ixs_bounds *b,
                                      bounds_equality_walk *walk) {
  bounds_equality_walk_entry *entries;
  size_t capacity;
  size_t old_bytes;
  size_t new_bytes;
  if (walk->count < walk->capacity)
    return true;
  capacity = walk->capacity ? walk->capacity : BOUNDS_EQUALITY_WALK_INIT_CAP;
  if (walk->capacity) {
    if (capacity > SIZE_MAX / 2u)
      goto failed;
    capacity *= 2u;
  }
  if (capacity > b->nequality_endpoints)
    capacity = b->nequality_endpoints;
  if (capacity <= walk->capacity ||
      walk->capacity > SIZE_MAX / sizeof(*walk->entries) ||
      capacity > SIZE_MAX / sizeof(*walk->entries))
    goto failed;
  old_bytes = walk->capacity * sizeof(*walk->entries);
  new_bytes = capacity * sizeof(*walk->entries);
  if (walk->entries) {
    entries = ixs_arena_grow(b->scratch, walk->entries, old_bytes, new_bytes,
                             sizeof(void *));
  } else {
    entries = ixs_arena_alloc(b->scratch, new_bytes, sizeof(void *));
  }
  if (!entries)
    goto failed;
  walk->entries = entries;
  walk->capacity = capacity;
  return true;

failed:
  b->oom = true;
  return false;
}

static size_t bounds_equality_seen_hash(size_t endpoint_index) {
  uint64_t x = (uint64_t)endpoint_index + UINT64_C(0x9e3779b97f4a7c15);
  x ^= x >> 33;
  x *= UINT64_C(0xff51afd7ed558ccd);
  x ^= x >> 33;
  return (size_t)x;
}

static size_t bounds_equality_seen_slot(const bounds_equality_seen_entry *seen,
                                        size_t capacity,
                                        size_t endpoint_index) {
  size_t endpoint_plus_one = endpoint_index + 1u;
  size_t slot = bounds_equality_seen_hash(endpoint_index) & (capacity - 1u);
  while (seen[slot].endpoint_plus_one &&
         seen[slot].endpoint_plus_one != endpoint_plus_one)
    slot = (slot + 1u) & (capacity - 1u);
  return slot;
}

static bool bounds_equality_walk_find(const bounds_equality_walk *walk,
                                      size_t endpoint_index,
                                      size_t *entry_index) {
  size_t slot;
  if (!walk->seen_capacity)
    return false;
  slot = bounds_equality_seen_slot(walk->seen, walk->seen_capacity,
                                   endpoint_index);
  if (!walk->seen[slot].endpoint_plus_one)
    return false;
  if (!walk->seen[slot].entry_plus_one)
    return false;
  *entry_index = walk->seen[slot].entry_plus_one - 1u;
  return true;
}

static bool bounds_equality_walk_prepare_seen(ixs_bounds *b,
                                              bounds_equality_walk *walk) {
  bounds_equality_seen_entry *seen;
  size_t capacity = walk->seen_capacity;
  size_t bytes;
  size_t i;

  if (capacity && walk->seen_count < capacity - capacity / 4u)
    return true;
  if (!capacity)
    capacity = BOUNDS_EQUALITY_WALK_INIT_CAP;
  else {
    if (capacity > SIZE_MAX / 2u)
      goto failed;
    capacity *= 2u;
  }
  if (capacity > SIZE_MAX / sizeof(*seen))
    goto failed;
  bytes = capacity * sizeof(*seen);
  seen = ixs_arena_alloc(b->scratch, bytes, sizeof(void *));
  if (!seen)
    goto failed;
  memset(seen, 0, bytes);
  for (i = 0; i < walk->seen_capacity; i++) {
    size_t endpoint_index;
    size_t slot;
    if (!walk->seen[i].endpoint_plus_one)
      continue;
    endpoint_index = walk->seen[i].endpoint_plus_one - 1u;
    slot = bounds_equality_seen_slot(seen, capacity, endpoint_index);
    seen[slot] = walk->seen[i];
  }
  walk->seen = seen;
  walk->seen_capacity = capacity;
  return true;

failed:
  b->oom = true;
  return false;
}

static bounds_equality_record_status
bounds_equality_walk_record(ixs_bounds *b, bounds_equality_walk *walk,
                            size_t endpoint_index, bounds_wide_offset offset) {
  size_t entry_index;
  size_t slot;
  if (endpoint_index >= b->nequality_endpoints)
    return BOUNDS_EQUALITY_RECORD_INVALID;
  if (bounds_equality_walk_find(walk, endpoint_index, &entry_index)) {
    if (entry_index >= walk->count)
      return BOUNDS_EQUALITY_RECORD_INVALID;
    return bounds_wide_offset_equal(walk->entries[entry_index].offset, offset)
               ? BOUNDS_EQUALITY_RECORD_MATCHED
               : BOUNDS_EQUALITY_RECORD_CONFLICT;
  }
  if (!bounds_equality_walk_grow(b, walk) ||
      !bounds_equality_walk_prepare_seen(b, walk))
    return BOUNDS_EQUALITY_RECORD_OOM;
  walk->entries[walk->count].node = b->equality_endpoints[endpoint_index].expr;
  walk->entries[walk->count].endpoint_index = endpoint_index;
  walk->entries[walk->count].offset = offset;
  slot = bounds_equality_seen_slot(walk->seen, walk->seen_capacity,
                                   endpoint_index);
  if (walk->seen[slot].endpoint_plus_one)
    return BOUNDS_EQUALITY_RECORD_INVALID;
  walk->seen[slot].endpoint_plus_one = endpoint_index + 1u;
  walk->seen[slot].entry_plus_one = walk->count + 1u;
  walk->seen_count++;
  walk->count++;
  return BOUNDS_EQUALITY_RECORD_INSERTED;
}

static bool bounds_equality_edge_neighbor(size_t endpoint_index,
                                          ixs_equality_edge *edge,
                                          size_t *neighbor_endpoint,
                                          bounds_wide_offset *step,
                                          ixs_equality_edge **next) {
  if (edge->lhs_endpoint == endpoint_index) {
    *neighbor_endpoint = edge->rhs_endpoint;
    *step =
        bounds_wide_offset_negate(bounds_wide_offset_from_int64(edge->offset));
    *next = edge->next_lhs;
    return true;
  }
  if (edge->rhs_endpoint == endpoint_index) {
    *neighbor_endpoint = edge->lhs_endpoint;
    *step = bounds_wide_offset_from_int64(edge->offset);
    *next = edge->next_rhs;
    return true;
  }
  return false;
}

static bounds_equality_walk_status
bounds_equality_require_defined(ixs_bounds *b, ixs_node *expr) {
  bool defined_oom = false;
  bool defined_limited = false;
  if (bounds_check_defined_without_equality(b, expr, &defined_oom,
                                            &defined_limited) == IXS_CHECK_TRUE)
    return BOUNDS_EQUALITY_WALK_VALID;
  if (defined_oom)
    return BOUNDS_EQUALITY_WALK_OOM;
  if (!defined_limited)
    return BOUNDS_EQUALITY_WALK_NONE;
  if (bounds_query_is_tracking(b))
    bounds_query_note_limit(b->query_state);
  return BOUNDS_EQUALITY_WALK_LIMITED;
}

static bounds_equality_walk_status
bounds_equality_walk_edge(ixs_bounds *b, bounds_equality_walk *walk,
                          const bounds_equality_walk_entry *current,
                          ixs_equality_edge **edge_ptr, bool require_defined,
                          ixs_bounds_query_state *query_state) {
  ixs_equality_edge *next;
  ixs_node *neighbor;
  size_t neighbor_endpoint;
  size_t neighbor_entry;
  bounds_wide_offset step;
  bounds_wide_offset neighbor_offset;
  bounds_equality_record_status record_status;
  bounds_equality_walk_status defined_status;

  if (query_state)
    bounds_query_counter_increment(&query_state->equality_edge_visits);
  if (!bounds_equality_edge_neighbor(current->endpoint_index, *edge_ptr,
                                     &neighbor_endpoint, &step, &next) ||
      neighbor_endpoint >= b->nequality_endpoints)
    return BOUNDS_EQUALITY_WALK_INVALID;
  *edge_ptr = next;
  neighbor = b->equality_endpoints[neighbor_endpoint].expr;
  if (!neighbor)
    return BOUNDS_EQUALITY_WALK_INVALID;
  if (!bounds_equality_walk_find(walk, neighbor_endpoint, &neighbor_entry) &&
      require_defined) {
    defined_status = bounds_equality_require_defined(b, neighbor);
    if (defined_status != BOUNDS_EQUALITY_WALK_VALID)
      return defined_status;
  }
  if (!bounds_wide_offset_add(current->offset, step, &neighbor_offset)) {
    bounds_query_note_invalid(b->query_state);
    return BOUNDS_EQUALITY_WALK_INVALID;
  }
  record_status =
      bounds_equality_walk_record(b, walk, neighbor_endpoint, neighbor_offset);
  if (record_status == BOUNDS_EQUALITY_RECORD_OOM)
    return BOUNDS_EQUALITY_WALK_OOM;
  if (record_status == BOUNDS_EQUALITY_RECORD_CONFLICT) {
    bounds_query_note_invalid(b->query_state);
    return BOUNDS_EQUALITY_WALK_INVALID;
  }
  if (record_status == BOUNDS_EQUALITY_RECORD_INVALID)
    return BOUNDS_EQUALITY_WALK_INVALID;
  return BOUNDS_EQUALITY_WALK_VALID;
}

/* Collect the independently defined component incident to expr. Traversal is
 * nonrecursive and grows with the component; there is no semantic walk cap. */
static bounds_equality_walk_status
bounds_collect_equality_component(ixs_bounds *b, ixs_node *expr,
                                  bounds_equality_walk *walk,
                                  bool require_defined) {
  ixs_bounds_query_state *query_state = NULL;
  size_t head = 0;
  size_t root_endpoint;
  bounds_equality_record_status record_status;
  bounds_equality_walk_status status;
  bounds_wide_offset zero = {0, 0, false};

  memset(walk, 0, sizeof(*walk));
  if (!b || !expr || !b->nequalities ||
      !bounds_find_equality_endpoint(b, expr, &root_endpoint))
    return BOUNDS_EQUALITY_WALK_NONE;
  if (bounds_query_is_tracking(b)) {
    query_state = b->query_state;
    bounds_query_counter_increment(&query_state->equality_walks);
  }
  if (require_defined) {
    status = bounds_equality_require_defined(b, expr);
    if (status != BOUNDS_EQUALITY_WALK_VALID)
      return status;
  }
  if (!bounds_equality_walk_init(b, walk))
    return BOUNDS_EQUALITY_WALK_OOM;
  record_status = bounds_equality_walk_record(b, walk, root_endpoint, zero);
  if (record_status == BOUNDS_EQUALITY_RECORD_OOM)
    return BOUNDS_EQUALITY_WALK_OOM;
  if (record_status == BOUNDS_EQUALITY_RECORD_CONFLICT ||
      record_status == BOUNDS_EQUALITY_RECORD_INVALID)
    return BOUNDS_EQUALITY_WALK_INVALID;

  while (head < walk->count) {
    bounds_equality_walk_entry current = walk->entries[head++];
    ixs_equality_edge *edge =
        b->equality_endpoints[current.endpoint_index].edges;
    if (query_state)
      bounds_query_counter_increment(&query_state->equality_endpoint_visits);
    while (edge) {
      status = bounds_equality_walk_edge(b, walk, &current, &edge,
                                         require_defined, query_state);
      if (status == BOUNDS_EQUALITY_WALK_NONE)
        continue;
      if (status != BOUNDS_EQUALITY_WALK_VALID)
        return status;
    }
  }
  return BOUNDS_EQUALITY_WALK_VALID;
}

static bool
bounds_publish_defined_equality_component(ixs_bounds *b,
                                          const bounds_equality_walk *walk) {
  size_t component;
  size_t i;
  if (!bounds_query_is_tracking(b) || !walk || walk->count == 0)
    return true;
  if (!bounds_equality_projection_cache_reserve(b, walk->count))
    return false;
  component = walk->entries[0].endpoint_index;
  for (i = 0; i < walk->count; i++) {
    bounds_equality_projection_cache_entry *entry =
        bounds_equality_projection_cache_get(b, walk->entries[i].endpoint_index,
                                             true);
    assert(entry != NULL);
    entry->defined_component = component;
    entry->defined_offset = walk->entries[i].offset;
    entry->defined_component_complete = true;
  }
  return true;
}

static bounds_equality_walk_status
bounds_relation_offset(ixs_bounds *b, ixs_node *lhs, ixs_node *rhs,
                       bounds_wide_offset *offset, bool require_defined) {
  bounds_equality_walk walk;
  bounds_equality_walk_status status;
  bounds_equality_projection_cache_entry *lhs_cached;
  bounds_equality_projection_cache_entry *rhs_cached;
  size_t lhs_endpoint;
  size_t rhs_endpoint;
  size_t entry_index;
  if (!b || !lhs || !rhs || !offset || b->oom || b->contradiction)
    return BOUNDS_EQUALITY_WALK_NONE;
  if (lhs == rhs) {
    *offset = bounds_wide_offset_from_int64(0);
    return BOUNDS_EQUALITY_WALK_VALID;
  }
  if (!bounds_find_equality_endpoint(b, lhs, &lhs_endpoint))
    return BOUNDS_EQUALITY_WALK_NONE;
  if (require_defined && bounds_query_is_tracking(b) &&
      bounds_find_equality_endpoint(b, rhs, &rhs_endpoint)) {
    rhs_cached = bounds_equality_projection_cache_get(b, rhs_endpoint, false);
    if (!rhs_cached || !rhs_cached->defined_component_complete) {
      status =
          bounds_collect_equality_component(b, rhs, &walk, require_defined);
      if (status != BOUNDS_EQUALITY_WALK_VALID) {
        bounds_equality_walk_destroy(b, &walk);
        return status;
      }
      if (!bounds_publish_defined_equality_component(b, &walk)) {
        bounds_equality_walk_destroy(b, &walk);
        return BOUNDS_EQUALITY_WALK_OOM;
      }
      bounds_equality_walk_destroy(b, &walk);
      rhs_cached = bounds_equality_projection_cache_get(b, rhs_endpoint, false);
    }
    lhs_cached = bounds_equality_projection_cache_get(b, lhs_endpoint, false);
    if (!lhs_cached || !rhs_cached || !lhs_cached->defined_component_complete ||
        lhs_cached->defined_component != rhs_cached->defined_component)
      return BOUNDS_EQUALITY_WALK_NONE;
    if (!bounds_wide_offset_add(
            lhs_cached->defined_offset,
            bounds_wide_offset_negate(rhs_cached->defined_offset), offset)) {
      bounds_query_note_invalid(b->query_state);
      return BOUNDS_EQUALITY_WALK_INVALID;
    }
    return BOUNDS_EQUALITY_WALK_VALID;
  }
  status = bounds_collect_equality_component(b, rhs, &walk, require_defined);
  if (status != BOUNDS_EQUALITY_WALK_VALID) {
    bounds_equality_walk_destroy(b, &walk);
    return status;
  }
  if (!bounds_equality_walk_find(&walk, lhs_endpoint, &entry_index)) {
    bounds_equality_walk_destroy(b, &walk);
    return BOUNDS_EQUALITY_WALK_NONE;
  }
  if (entry_index >= walk.count) {
    bounds_equality_walk_destroy(b, &walk);
    return BOUNDS_EQUALITY_WALK_INVALID;
  }
  *offset = walk.entries[entry_index].offset;
  bounds_equality_walk_destroy(b, &walk);
  return BOUNDS_EQUALITY_WALK_VALID;
}

static bounds_equality_walk_status
bounds_exact_relation_difference(ixs_bounds *b, ixs_node *lhs, ixs_node *rhs,
                                 int64_t *delta) {
  bounds_equality_walk_status status;
  bounds_wide_offset offset;
  if (!b || !lhs || !rhs || !delta || b->oom || b->contradiction)
    return BOUNDS_EQUALITY_WALK_NONE;
  /* Preserve the weighted symbol forest as the hot path. */
  if (bounds_exact_symbol_difference(b, lhs, rhs, delta))
    return BOUNDS_EQUALITY_WALK_VALID;
  status = bounds_relation_offset(b, lhs, rhs, &offset, true);
  if (status != BOUNDS_EQUALITY_WALK_VALID)
    return status;
  if (!bounds_wide_offset_to_int64(offset, delta))
    return BOUNDS_EQUALITY_WALK_UNREPRESENTABLE;
  return BOUNDS_EQUALITY_WALK_VALID;
}

static size_t bounds_difference_hash(ixs_node *lhs, ixs_node *rhs,
                                     int64_t offset) {
  uint64_t x = (uint64_t)bounds_expr_hash_ptr(lhs);
  x ^= (uint64_t)bounds_expr_hash_ptr(rhs) + UINT64_C(0x9e3779b97f4a7c15) +
       (x << 6) + (x >> 2);
  x ^= (uint64_t)offset + UINT64_C(0x9e3779b97f4a7c15) + (x << 6) + (x >> 2);
  x ^= x >> 33;
  x *= UINT64_C(0xff51afd7ed558ccd);
  x ^= x >> 33;
  return (size_t)x;
}

/* Exact-edge lookup is expected O(1); growth rehashes at 75% load. */
static size_t
bounds_difference_index_slot(ixs_difference_constraint *const *index,
                             size_t capacity, ixs_node *lhs, ixs_node *rhs,
                             int64_t offset) {
  size_t slot = bounds_difference_hash(lhs, rhs, offset) & (capacity - 1u);
  while (index[slot] && (index[slot]->lhs != lhs || index[slot]->rhs != rhs ||
                         index[slot]->offset != offset))
    slot = (slot + 1u) & (capacity - 1u);
  return slot;
}

static bool
bounds_prepare_difference_index(ixs_bounds *b, size_t count,
                                ixs_difference_constraint ***prepared,
                                size_t *prepared_capacity) {
  size_t capacity = b->difference_index_cap;
  ixs_difference_constraint **index;
  size_t i;

  if (capacity && count <= capacity - capacity / 4u) {
    *prepared = b->difference_index;
    *prepared_capacity = capacity;
    return true;
  }
  if (!capacity)
    capacity = BOUNDS_DIFFERENCE_INDEX_INIT_CAP;
  while (count > capacity - capacity / 4u) {
    if (capacity > SIZE_MAX / 2u)
      return false;
    capacity *= 2u;
  }
  if (capacity > SIZE_MAX / sizeof(*index))
    return false;
  index =
      ixs_arena_alloc(b->scratch, capacity * sizeof(*index), sizeof(void *));
  if (!index)
    return false;
  memset(index, 0, capacity * sizeof(*index));
  for (i = 0; i < b->difference_index_cap; i++) {
    ixs_difference_constraint *edge = b->difference_index[i];
    size_t slot;
    if (!edge)
      continue;
    slot = bounds_difference_index_slot(index, capacity, edge->lhs, edge->rhs,
                                        edge->offset);
    index[slot] = edge;
  }
  *prepared = index;
  *prepared_capacity = capacity;
  return true;
}

/* Relation metadata is absent from non-relational fact sets. Geometric growth
 * keeps appending graph variables amortized O(1) while stable var indices keep
 * the parallel table independent of var-array relocation. */
static bool bounds_prepare_difference_vars(ixs_bounds *b, size_t count) {
  ixs_difference_var *vars;
  size_t capacity = b->difference_var_cap;
  size_t old_bytes;
  size_t new_bytes;

  if (count <= capacity)
    return true;
  if (!capacity)
    capacity = 1u;
  while (capacity < count) {
    if (capacity > SIZE_MAX / 2u)
      return false;
    capacity *= 2u;
  }
  if (b->difference_var_cap > SIZE_MAX / sizeof(*vars) ||
      capacity > SIZE_MAX / sizeof(*vars))
    return false;
  old_bytes = b->difference_var_cap * sizeof(*vars);
  new_bytes = capacity * sizeof(*vars);
  vars = ixs_arena_grow(b->scratch, b->difference_vars, old_bytes, new_bytes,
                        sizeof(void *));
  if (!vars)
    return false;
  memset(vars + b->difference_var_cap, 0,
         (capacity - b->difference_var_cap) * sizeof(*vars));
  b->difference_vars = vars;
  b->difference_var_cap = capacity;
  return true;
}

static size_t bounds_exact_hash(size_t var_index) {
  uint64_t x = (uint64_t)var_index + UINT64_C(0x9e3779b97f4a7c15);
  x ^= x >> 33;
  x *= UINT64_C(0xff51afd7ed558ccd);
  x ^= x >> 33;
  return (size_t)x;
}

static size_t bounds_exact_index_slot(const size_t *index, size_t capacity,
                                      const ixs_exact_var *vars,
                                      size_t var_index) {
  size_t slot = bounds_exact_hash(var_index) & (capacity - 1u);
  while (index[slot] && vars[index[slot] - 1u].var_index != var_index)
    slot = (slot + 1u) & (capacity - 1u);
  return slot;
}

static bool bounds_exact_lookup(const ixs_bounds *b, size_t var_index,
                                size_t *exact_index) {
  size_t slot;
  if (!b->exact_index || !b->exact_index_cap)
    return false;
  slot = bounds_exact_index_slot(b->exact_index, b->exact_index_cap,
                                 b->exact_vars, var_index);
  if (!b->exact_index[slot])
    return false;
  *exact_index = b->exact_index[slot] - 1u;
  return true;
}

/* Exact-index growth is amortized O(1) and touches only exact participants. */
static bool bounds_prepare_exact_index(ixs_bounds *b, size_t count,
                                       size_t **prepared,
                                       size_t *prepared_capacity) {
  size_t capacity = b->exact_index_cap;
  size_t *index;
  size_t i;

  if (capacity && count <= capacity - capacity / 4u) {
    *prepared = b->exact_index;
    *prepared_capacity = capacity;
    return true;
  }
  if (!capacity)
    capacity = BOUNDS_EXACT_INDEX_INIT_CAP;
  while (count > capacity - capacity / 4u) {
    if (capacity > SIZE_MAX / 2u)
      return false;
    capacity *= 2u;
  }
  if (capacity > SIZE_MAX / sizeof(*index))
    return false;
  index =
      ixs_arena_alloc(b->scratch, capacity * sizeof(*index), sizeof(void *));
  if (!index)
    return false;
  memset(index, 0, capacity * sizeof(*index));
  for (i = 0; i < b->nexact_vars; i++) {
    size_t slot = bounds_exact_index_slot(index, capacity, b->exact_vars,
                                          b->exact_vars[i].var_index);
    index[slot] = i + 1u;
  }
  *prepared = index;
  *prepared_capacity = capacity;
  return true;
}

static bool bounds_prepare_exact_vars(ixs_bounds *b, size_t count,
                                      ixs_exact_var **prepared,
                                      size_t *prepared_capacity) {
  ixs_exact_var *vars;
  size_t capacity = b->exact_var_cap;
  size_t old_bytes;
  size_t new_bytes;

  if (count <= capacity) {
    *prepared = b->exact_vars;
    *prepared_capacity = capacity;
    return true;
  }
  if (!capacity)
    capacity = 2u;
  while (capacity < count) {
    if (capacity > SIZE_MAX / 2u)
      return false;
    capacity *= 2u;
  }
  if (b->exact_var_cap > SIZE_MAX / sizeof(*vars) ||
      capacity > SIZE_MAX / sizeof(*vars))
    return false;
  old_bytes = b->exact_var_cap * sizeof(*vars);
  new_bytes = capacity * sizeof(*vars);
  vars = ixs_arena_grow(b->scratch, b->exact_vars, old_bytes, new_bytes,
                        sizeof(void *));
  if (!vars)
    return false;
  memset(vars + b->exact_var_cap, 0,
         (capacity - b->exact_var_cap) * sizeof(*vars));
  *prepared = vars;
  *prepared_capacity = capacity;
  return true;
}

static void bounds_exact_init_var(ixs_bounds *b, size_t var_index,
                                  size_t *exact_index) {
  size_t slot;
  size_t id = b->nexact_vars++;
  b->exact_vars[id].var_index = var_index;
  b->exact_vars[id].parent = id;
  b->exact_vars[id].size = 1u;
  b->exact_vars[id].offset = 0;
  slot = bounds_exact_index_slot(b->exact_index, b->exact_index_cap,
                                 b->exact_vars, var_index);
  b->exact_index[slot] = id + 1u;
  *exact_index = id;
}

static bool bounds_prepare_exact_pair(ixs_bounds *b, size_t lhs_var,
                                      size_t rhs_var, size_t *lhs_exact,
                                      size_t *rhs_exact) {
  ixs_exact_var *vars;
  size_t *index;
  size_t var_capacity;
  size_t index_capacity;
  size_t missing = 0;
  bool have_lhs = bounds_exact_lookup(b, lhs_var, lhs_exact);
  bool have_rhs = bounds_exact_lookup(b, rhs_var, rhs_exact);

  if (!have_lhs)
    missing++;
  if (!have_rhs)
    missing++;
  if (b->nexact_vars > SIZE_MAX - missing ||
      !bounds_prepare_exact_index(b, b->nexact_vars + missing, &index,
                                  &index_capacity) ||
      !bounds_prepare_exact_vars(b, b->nexact_vars + missing, &vars,
                                 &var_capacity))
    return false;

  b->exact_vars = vars;
  b->exact_var_cap = var_capacity;
  b->exact_index = index;
  b->exact_index_cap = index_capacity;
  if (!have_lhs)
    bounds_exact_init_var(b, lhs_var, lhs_exact);
  if (!have_rhs)
    bounds_exact_init_var(b, rhs_var, rhs_exact);
  return true;
}

/* Weighted parent links use value(node) - value(parent). Union by size and
 * path compression make representable exact queries amortized inverse-Ackermann
 * in the number of exact participants, independent of inequality fan-out. */
static bool bounds_exact_find(ixs_bounds *b, size_t id, size_t *root,
                              int64_t *offset) {
  size_t current = id;
  int64_t total = 0;

  while (b->exact_vars[current].parent != current) {
    if (!ixs_safe_add(total, b->exact_vars[current].offset, &total))
      return false;
    current = b->exact_vars[current].parent;
  }
  *root = current;
  *offset = total;

  current = id;
  while (b->exact_vars[current].parent != current) {
    size_t parent = b->exact_vars[current].parent;
    int64_t edge = b->exact_vars[current].offset;
    int64_t remaining;
    if (!ixs_safe_sub(total, edge, &remaining))
      break;
    b->exact_vars[current].parent = *root;
    b->exact_vars[current].offset = total;
    current = parent;
    total = remaining;
  }
  return true;
}

/* Record lhs - rhs == offset. Overflow leaves the exact forest unchanged;
 * the complete directed graph still owns and validates both inequalities. */
static bool bounds_union_exact(ixs_bounds *b, size_t lhs_var, size_t rhs_var,
                               int64_t offset) {
  size_t lhs_exact;
  size_t rhs_exact;
  size_t lhs_root;
  size_t rhs_root;
  int64_t lhs_offset;
  int64_t rhs_offset;
  int64_t root_offset;
  int64_t reverse_offset;

  if (!bounds_prepare_exact_pair(b, lhs_var, rhs_var, &lhs_exact, &rhs_exact)) {
    b->oom = true;
    return false;
  }
  if (!bounds_exact_find(b, lhs_exact, &lhs_root, &lhs_offset) ||
      !bounds_exact_find(b, rhs_exact, &rhs_root, &rhs_offset))
    return true;
  if (lhs_root == rhs_root) {
    int64_t existing;
    if (ixs_safe_sub(lhs_offset, rhs_offset, &existing) && existing != offset)
      bounds_mark_contradiction(b);
    return true;
  }
  if (!ixs_safe_sub(offset, lhs_offset, &root_offset) ||
      !ixs_safe_add(root_offset, rhs_offset, &root_offset))
    return true;

  if (b->exact_vars[lhs_root].size <= b->exact_vars[rhs_root].size) {
    b->exact_vars[lhs_root].parent = rhs_root;
    b->exact_vars[lhs_root].offset = root_offset;
    b->exact_vars[rhs_root].size += b->exact_vars[lhs_root].size;
  } else {
    if (!ixs_safe_neg(root_offset, &reverse_offset))
      return true;
    b->exact_vars[rhs_root].parent = lhs_root;
    b->exact_vars[rhs_root].offset = reverse_offset;
    b->exact_vars[lhs_root].size += b->exact_vars[rhs_root].size;
  }
  bounds_mark_semantic_changed(b);
  bounds_cache_clear(b);
  return true;
}

static bool bounds_exact_symbol_difference(ixs_bounds *b, ixs_node *lhs,
                                           ixs_node *rhs, int64_t *delta) {
  ixs_var_bound *lhs_var;
  ixs_var_bound *rhs_var;
  size_t lhs_exact;
  size_t rhs_exact;
  size_t lhs_root;
  size_t rhs_root;
  int64_t lhs_offset;
  int64_t rhs_offset;

  if (!b || !lhs || !rhs || !delta || b->oom || b->contradiction ||
      lhs->tag != IXS_SYM || rhs->tag != IXS_SYM)
    return false;
  if (lhs == rhs) {
    *delta = 0;
    return true;
  }
  lhs_var = find_var(b, lhs->u.name);
  rhs_var = find_var(b, rhs->u.name);
  if (!lhs_var || !rhs_var ||
      !bounds_exact_lookup(b, (size_t)(lhs_var - b->vars), &lhs_exact) ||
      !bounds_exact_lookup(b, (size_t)(rhs_var - b->vars), &rhs_exact) ||
      !bounds_exact_find(b, lhs_exact, &lhs_root, &lhs_offset) ||
      !bounds_exact_find(b, rhs_exact, &rhs_root, &rhs_offset) ||
      lhs_root != rhs_root)
    return false;
  return ixs_safe_sub(lhs_offset, rhs_offset, delta);
}

static bool bounds_difference_worklist_init(ixs_bounds *b,
                                            difference_worklist *work) {
  size_t count = b->ndifference_vars;
  memset(work, 0, sizeof(*work));
  work->mark = ixs_arena_save(b->scratch);
  work->capacity = count;
  if (count == 0)
    return true;
  if (b->difference_epoch == SIZE_MAX ||
      count > SIZE_MAX / sizeof(*work->queue)) {
    b->oom = true;
    return false;
  }
  work->epoch = ++b->difference_epoch;
  work->queue =
      ixs_arena_alloc(b->scratch, count * sizeof(*work->queue), sizeof(void *));
  if (!work->queue) {
    ixs_arena_restore(b->scratch, work->mark);
    b->oom = true;
    return false;
  }
  return true;
}

static void bounds_difference_worklist_destroy(ixs_bounds *b,
                                               difference_worklist *work) {
  ixs_arena_restore(b->scratch, work->mark);
}

static bool bounds_difference_var_active(const ixs_bounds *b,
                                         size_t var_index) {
  const ixs_difference_var *var;
  if (var_index >= b->nvars || var_index >= b->difference_var_cap)
    return false;
  var = &b->difference_vars[var_index];
  return var->incoming || var->outgoing;
}

static bool bounds_difference_enqueue(ixs_bounds *b, difference_worklist *work,
                                      size_t var_index) {
  ixs_difference_var *var;
  if (var_index >= b->nvars)
    return false;
  if (!bounds_difference_var_active(b, var_index))
    return true;
  var = &b->difference_vars[var_index];
  if (var->queue_epoch == work->epoch)
    return true;
  if (work->count >= work->capacity)
    return false;
  work->queue[work->tail] = var_index;
  work->tail = (work->tail + 1u) % work->capacity;
  work->count++;
  var->queue_epoch = work->epoch;
  return true;
}

static size_t bounds_difference_pop(ixs_bounds *b, difference_worklist *work) {
  size_t var_index = work->queue[work->head];
  work->head = (work->head + 1u) % work->capacity;
  work->count--;
  b->difference_vars[var_index].queue_epoch = 0;
  return var_index;
}

/* Existing potentials satisfy every published edge. Adding one edge can only
 * invalidate paths containing that edge. A strictly improving path of nvars
 * edges repeats a vertex, so its repeated segment is a negative cycle. The
 * work is proportional to the affected directed component and has no semantic
 * iteration cap. */
static bool bounds_validate_difference_edge(ixs_bounds *b, size_t lhs_var,
                                            size_t rhs_var, int64_t offset) {
  difference_worklist work;
  int64_t candidate;

  if (!ixs_safe_add(b->difference_vars[rhs_var].potential, offset,
                    &candidate)) {
    b->oom = true;
    return false;
  }
  if (b->difference_vars[lhs_var].potential <= candidate)
    return true;
  if (!bounds_difference_worklist_init(b, &work))
    return false;

  b->difference_vars[lhs_var].potential = candidate;
  b->difference_vars[lhs_var].hops = 1u;
  if (!bounds_difference_enqueue(b, &work, lhs_var)) {
    b->oom = true;
    bounds_difference_worklist_destroy(b, &work);
    return false;
  }

  while (work.count && !b->contradiction && !b->oom) {
    size_t source = bounds_difference_pop(b, &work);
    ixs_difference_constraint *edge = b->difference_vars[source].outgoing;
    while (edge) {
      size_t target = edge->lhs_var;
      if (!ixs_safe_add(b->difference_vars[source].potential, edge->offset,
                        &candidate)) {
        b->oom = true;
        break;
      }
      if (b->difference_vars[target].potential > candidate) {
        if (b->difference_vars[source].hops >= b->ndifference_vars - 1u) {
          bounds_mark_contradiction(b);
          break;
        }
        b->difference_vars[target].potential = candidate;
        b->difference_vars[target].hops = b->difference_vars[source].hops + 1u;
        if (!bounds_difference_enqueue(b, &work, target)) {
          b->oom = true;
          break;
        }
      }
      edge = edge->next_rhs;
    }
  }
  bounds_difference_worklist_destroy(b, &work);
  return !b->oom;
}

static bool bounds_refine_var_upper(ixs_bounds *b, ixs_var_bound *v,
                                    int64_t upper) {
  if (!v ||
      (!v->iv.hi_inf && ixs_rat_cmp(upper, 1, v->iv.hi_p, v->iv.hi_q) >= 0))
    return false;
  v->iv.hi_p = upper;
  v->iv.hi_q = 1;
  v->iv.hi_inf = false;
  bounds_mark_semantic_changed(b);
  bounds_cache_clear(b);
  refine_var_bit_consistency(b, v);
  return true;
}

static bool bounds_refine_var_lower(ixs_bounds *b, ixs_var_bound *v,
                                    int64_t lower) {
  if (!v ||
      (!v->iv.lo_inf && ixs_rat_cmp(lower, 1, v->iv.lo_p, v->iv.lo_q) <= 0))
    return false;
  v->iv.lo_p = lower;
  v->iv.lo_q = 1;
  v->iv.lo_inf = false;
  bounds_mark_semantic_changed(b);
  bounds_cache_clear(b);
  refine_var_bit_consistency(b, v);
  return true;
}

static ixs_interval bounds_get_difference_symbol(ixs_bounds *b,
                                                 ixs_var_bound *var,
                                                 ixs_node *symbol) {
  ixs_interval iv = var->iv;
  if (b->nexprs) {
    ixs_node *canon;
    iv = iv_intersect(iv, bounds_get_expr_overrides(b, symbol));
    canon = bounds_canonical_expr(b, symbol);
    if (canon && canon != symbol)
      iv = iv_intersect(iv, bounds_get_expr_overrides(b, canon));
  }
  if (var->modulus > 0)
    iv = interval_intersect_congruence(iv, var->modulus, var->remainder);
  return iv;
}

static bool bounds_propagate_difference_upper(ixs_bounds *b,
                                              difference_worklist *work,
                                              size_t var_index) {
  ixs_difference_constraint *edge = b->difference_vars[var_index].outgoing;
  ixs_var_bound *var = &b->vars[var_index];
  ixs_interval iv;
  int64_t endpoint;
  int64_t derived;
  if (!edge)
    return true;
  iv = bounds_get_difference_symbol(b, var, edge->rhs);
  if (!iv.valid || iv.hi_inf)
    return !b->oom;
  endpoint = ixs_rat_floor(iv.hi_p, iv.hi_q);
  while (edge && !b->contradiction) {
    if (ixs_safe_add(endpoint, edge->offset, &derived) &&
        bounds_refine_var_upper(b, &b->vars[edge->lhs_var], derived) &&
        !bounds_difference_enqueue(b, work, edge->lhs_var)) {
      b->oom = true;
      return false;
    }
    edge = edge->next_rhs;
  }
  return !b->oom;
}

static bool bounds_propagate_difference_lower(ixs_bounds *b,
                                              difference_worklist *work,
                                              size_t var_index) {
  ixs_difference_constraint *edge = b->difference_vars[var_index].incoming;
  ixs_var_bound *var = &b->vars[var_index];
  ixs_interval iv;
  int64_t endpoint;
  int64_t derived;
  if (!edge)
    return true;
  iv = bounds_get_difference_symbol(b, var, edge->lhs);
  if (!iv.valid || iv.lo_inf)
    return !b->oom;
  endpoint = ixs_rat_ceil(iv.lo_p, iv.lo_q);
  while (edge && !b->contradiction) {
    if (ixs_safe_sub(endpoint, edge->offset, &derived) &&
        bounds_refine_var_lower(b, &b->vars[edge->rhs_var], derived) &&
        !bounds_difference_enqueue(b, work, edge->rhs_var)) {
      b->oom = true;
      return false;
    }
    edge = edge->next_lhs;
  }
  return !b->oom;
}

/* Existing edges are already closed. An insertion needs an endpoint worklist
 * only when the new edge itself can tighten one of its endpoints. */
static bool
bounds_difference_edge_can_refine(ixs_bounds *b,
                                  const ixs_difference_constraint *edge) {
  ixs_interval iv;
  int64_t endpoint;
  int64_t derived;

  iv = bounds_get_difference_symbol(b, &b->vars[edge->rhs_var], edge->rhs);
  if (iv.valid && !iv.hi_inf) {
    endpoint = ixs_rat_floor(iv.hi_p, iv.hi_q);
    if (ixs_safe_add(endpoint, edge->offset, &derived) &&
        (b->vars[edge->lhs_var].iv.hi_inf ||
         ixs_rat_cmp(derived, 1, b->vars[edge->lhs_var].iv.hi_p,
                     b->vars[edge->lhs_var].iv.hi_q) < 0))
      return true;
  }

  iv = bounds_get_difference_symbol(b, &b->vars[edge->lhs_var], edge->lhs);
  if (!iv.valid || iv.lo_inf)
    return false;
  endpoint = ixs_rat_ceil(iv.lo_p, iv.lo_q);
  return ixs_safe_sub(endpoint, edge->offset, &derived) &&
         (b->vars[edge->rhs_var].iv.lo_inf ||
          ixs_rat_cmp(derived, 1, b->vars[edge->rhs_var].iv.lo_p,
                      b->vars[edge->rhs_var].iv.lo_q) > 0);
}

static bool bounds_propagate_difference_indices(ixs_bounds *b, size_t first,
                                                size_t second,
                                                bool have_second) {
  difference_worklist work;
  bool first_active;
  bool second_active;

  if (!b || b->oom || b->contradiction || b->ndifferences == 0)
    return true;
  first_active = bounds_difference_var_active(b, first);
  second_active =
      have_second && second != first && bounds_difference_var_active(b, second);
  if (!first_active && !second_active)
    return true;
  if (!bounds_difference_worklist_init(b, &work))
    return false;
  if ((first_active && !bounds_difference_enqueue(b, &work, first)) ||
      (second_active && !bounds_difference_enqueue(b, &work, second))) {
    b->oom = true;
    bounds_difference_worklist_destroy(b, &work);
    return false;
  }

  /* Each strict interval refinement schedules only its adjacent variable.
   * With a feasible graph, closure is finite and costs the successful
   * relaxations plus the incident edges they inspect. */
  while (work.count && !b->oom && !b->contradiction) {
    size_t var_index = bounds_difference_pop(b, &work);
    if (!bounds_propagate_difference_upper(b, &work, var_index) ||
        b->contradiction ||
        !bounds_propagate_difference_lower(b, &work, var_index))
      break;
  }
  bounds_difference_worklist_destroy(b, &work);
  return !b->oom;
}

static void bounds_propagate_difference_bounds(ixs_bounds *b, const char *first,
                                               const char *second) {
  ixs_var_bound *first_var;
  ixs_var_bound *second_var = NULL;
  size_t first_index;
  size_t second_index = 0;
  if (!b || b->oom || !first || b->ndifferences == 0)
    return;
  first_var = find_var(b, first);
  if (!first_var)
    return;
  first_index = (size_t)(first_var - b->vars);
  if (second && second != first) {
    second_var = find_var(b, second);
    if (second_var)
      second_index = (size_t)(second_var - b->vars);
  }
  (void)bounds_propagate_difference_indices(b, first_index, second_index,
                                            second_var != NULL);
}

static bool bounds_register_exact_reverse(
    ixs_bounds *b, ixs_difference_constraint *const *index,
    size_t index_capacity, ixs_node *lhs, ixs_node *rhs, size_t lhs_var,
    size_t rhs_var, int64_t offset) {
  int64_t reverse_offset;
  size_t slot;
  if (!ixs_safe_neg(offset, &reverse_offset))
    return true;
  slot = bounds_difference_index_slot(index, index_capacity, rhs, lhs,
                                      reverse_offset);
  if (!index[slot])
    return true;
  if (!bounds_union_exact(b, lhs_var, rhs_var, offset))
    return false;
  bounds_add_exact_relation(b, lhs, rhs, offset);
  return !b->oom;
}

static void bounds_add_difference_constraint(ixs_bounds *b, ixs_node *lhs,
                                             ixs_node *rhs, int64_t offset) {
  ixs_difference_constraint **index;
  ixs_difference_constraint *edge;
  size_t lhs_var;
  size_t rhs_var;
  size_t index_capacity;
  size_t new_vertices;
  size_t slot;

  if (!b || !lhs || !rhs || lhs == rhs || lhs->tag != IXS_SYM ||
      rhs->tag != IXS_SYM || b->oom || b->contradiction)
    return;
  if (b->difference_index_cap) {
    slot = bounds_difference_index_slot(
        b->difference_index, b->difference_index_cap, lhs, rhs, offset);
    if (b->difference_index[slot])
      return;
  }
  if (!get_or_create_var_index(b, lhs->u.name, &lhs_var) ||
      !get_or_create_var_index(b, rhs->u.name, &rhs_var) ||
      b->ndifferences == SIZE_MAX ||
      !bounds_prepare_difference_vars(b, b->nvars) ||
      !bounds_prepare_difference_index(b, b->ndifferences + 1u, &index,
                                       &index_capacity)) {
    b->oom = true;
    return;
  }
  new_vertices = (!b->difference_vars[lhs_var].incoming &&
                  !b->difference_vars[lhs_var].outgoing) +
                 (!b->difference_vars[rhs_var].incoming &&
                  !b->difference_vars[rhs_var].outgoing);
  if (b->ndifference_vars > SIZE_MAX - new_vertices) {
    b->oom = true;
    return;
  }
  edge = ixs_arena_alloc(b->scratch, sizeof(*edge), sizeof(void *));
  if (!edge) {
    b->oom = true;
    return;
  }
  edge->lhs = lhs;
  edge->rhs = rhs;
  edge->next_lhs = b->difference_vars[lhs_var].incoming;
  edge->next_rhs = b->difference_vars[rhs_var].outgoing;
  edge->lhs_var = lhs_var;
  edge->rhs_var = rhs_var;
  edge->offset = offset;
  b->difference_vars[lhs_var].incoming = edge;
  b->difference_vars[rhs_var].outgoing = edge;
  b->difference_index = index;
  b->difference_index_cap = index_capacity;
  slot = bounds_difference_index_slot(index, index_capacity, lhs, rhs, offset);
  index[slot] = edge;
  b->ndifferences++;
  b->ndifference_vars += new_vertices;
  bounds_mark_semantic_changed(b);
  bounds_cache_clear(b);
  if (!bounds_validate_difference_edge(b, lhs_var, rhs_var, offset) ||
      b->contradiction)
    return;
  if (!bounds_register_exact_reverse(b, index, index_capacity, lhs, rhs,
                                     lhs_var, rhs_var, offset) ||
      b->contradiction)
    return;
  if (bounds_difference_edge_can_refine(b, edge))
    (void)bounds_propagate_difference_indices(b, lhs_var, rhs_var, true);
}

static bool bounds_extract_unit_difference(ixs_node *expr, ixs_node **lhs,
                                           ixs_node **rhs, int64_t *constant) {
  uint32_t i;
  int64_t p;
  int64_t q;
  if (!expr || !lhs || !rhs || !constant || expr->tag != IXS_ADD ||
      expr->u.add.nterms != 2u)
    return false;
  ixs_node_get_rat(expr->u.add.coeff, &p, &q);
  if (q != 1)
    return false;
  *constant = p;
  *lhs = NULL;
  *rhs = NULL;
  for (i = 0; i < 2u; i++) {
    ixs_node *term = expr->u.add.terms[i].term;
    ixs_node_get_rat(expr->u.add.terms[i].coeff, &p, &q);
    if (term->tag != IXS_SYM || q != 1 || (p != 1 && p != -1))
      return false;
    if (p == 1) {
      if (*lhs)
        return false;
      *lhs = term;
    } else {
      if (*rhs)
        return false;
      *rhs = term;
    }
  }
  return *lhs && *rhs && *lhs != *rhs;
}

static bool bounds_exact_unit_difference_value(ixs_bounds *b, ixs_node *expr,
                                               int64_t *value) {
  ixs_node *lhs;
  ixs_node *rhs;
  int64_t constant;
  int64_t difference;
  return bounds_extract_unit_difference(expr, &lhs, &rhs, &constant) &&
         bounds_exact_symbol_difference(b, lhs, rhs, &difference) &&
         ixs_safe_add(constant, difference, value);
}

static void bounds_add_difference_range(ixs_bounds *b, ixs_node *expr,
                                        ixs_interval iv) {
  ixs_node *lhs;
  ixs_node *rhs;
  int64_t constant;
  int64_t endpoint;
  int64_t offset;
  if (!iv.valid || !bounds_extract_unit_difference(expr, &lhs, &rhs, &constant))
    return;
  if (!iv.hi_inf) {
    endpoint = ixs_rat_floor(iv.hi_p, iv.hi_q);
    if (ixs_safe_sub(endpoint, constant, &offset))
      bounds_add_difference_constraint(b, lhs, rhs, offset);
  }
  if (!b->oom && !b->contradiction && !iv.lo_inf) {
    endpoint = ixs_rat_ceil(iv.lo_p, iv.lo_q);
    if (ixs_safe_sub(constant, endpoint, &offset))
      bounds_add_difference_constraint(b, rhs, lhs, offset);
  }
}

static void bounds_add_proportional_range(ixs_bounds *b, ixs_node *expr,
                                          ixs_interval iv) {
  ixs_node *primitive, *canonical;
  ixs_interval primitive_iv;
  int64_t scale_p, scale_q, offset_p, offset_q;
  if (!bounds_get_proportional_primitive(b, expr, &primitive, &scale_p,
                                         &scale_q, &offset_p, &offset_q) ||
      (primitive == expr && scale_p == 1 && scale_q == 1 && offset_p == 0))
    return;
  primitive_iv = bounds_invert_affine(iv, scale_p, scale_q, offset_p, offset_q);
  if (!primitive_iv.valid)
    return;
  bounds_add_expr_raw(b, primitive, primitive_iv);
  if (b->oom)
    return;
  canonical = bounds_canonical_expr(b, primitive);
  if (canonical && canonical != primitive)
    bounds_add_expr_raw(b, canonical, primitive_iv);
}

typedef struct {
  ixs_node *symbol;
  ixs_var_bound *var;
  int64_t modulus;
  int64_t lower;
  int64_t upper;
  int64_t residue_lower;
  int64_t residue_upper;
} bounds_mod_lift_domain;

static bool bounds_prepare_mod_lift_domain(ixs_bounds *b, ixs_node *mod,
                                           ixs_interval residue,
                                           bounds_mod_lift_domain *domain) {
  if (!b || !mod || mod->tag != IXS_MOD || mod->u.binary.lhs->tag != IXS_SYM ||
      mod->u.binary.rhs->tag != IXS_INT || mod->u.binary.rhs->u.ival <= 0 ||
      !residue.valid || residue.lo_inf || residue.hi_inf)
    return false;
  domain->symbol = mod->u.binary.lhs;
  domain->modulus = mod->u.binary.rhs->u.ival;
  domain->var = find_var(b, domain->symbol->u.name);
  if (!domain->var || !domain->var->iv.valid || domain->var->iv.lo_inf ||
      domain->var->iv.hi_inf)
    return false;
  domain->lower = ixs_rat_ceil(domain->var->iv.lo_p, domain->var->iv.lo_q);
  domain->upper = ixs_rat_floor(domain->var->iv.hi_p, domain->var->iv.hi_q);
  if (domain->lower > domain->upper || domain->lower <= -domain->modulus ||
      domain->upper >= domain->modulus)
    return false;
  domain->residue_lower = ixs_rat_ceil(residue.lo_p, residue.lo_q);
  domain->residue_upper = ixs_rat_floor(residue.hi_p, residue.hi_q);
  if (domain->residue_lower < 0)
    domain->residue_lower = 0;
  if (domain->residue_upper >= domain->modulus)
    domain->residue_upper = domain->modulus - 1;
  return domain->residue_lower <= domain->residue_upper;
}

/* Invert a residue interval only when a raw integer symbol is known to occupy
 * one lift on either side of zero.  Within (-m,m), Mod(x,m) can come only from
 * x itself or x+m; if exactly one lift misses the stored residue interval, the
 * other lift safely narrows x. */
static bool bounds_refine_symbol_from_mod_range(ixs_bounds *b, ixs_node *mod,
                                                ixs_interval residue) {
  bounds_mod_lift_domain domain;
  ixs_interval original;
  ixs_interval lifted;
  ixs_interval refined;
  int64_t negative_lower;
  int64_t negative_upper;
  int64_t positive_lower;
  int64_t positive_upper;
  bool negative_possible;
  bool positive_possible;

  if (!bounds_prepare_mod_lift_domain(b, mod, residue, &domain))
    return false;

  negative_lower = domain.lower;
  negative_upper = domain.upper < -1 ? domain.upper : -1;
  negative_possible = negative_lower <= negative_upper &&
                      negative_lower + domain.modulus <= domain.residue_upper &&
                      negative_upper + domain.modulus >= domain.residue_lower;
  positive_lower = domain.lower > 0 ? domain.lower : 0;
  positive_upper = domain.upper;
  positive_possible = positive_lower <= positive_upper &&
                      positive_lower <= domain.residue_upper &&
                      positive_upper >= domain.residue_lower;
  if (negative_possible == positive_possible)
    return false;

  if (positive_possible) {
    if (positive_lower < domain.residue_lower)
      positive_lower = domain.residue_lower;
    if (positive_upper > domain.residue_upper)
      positive_upper = domain.residue_upper;
    lifted = ixs_interval_range(positive_lower, 1, positive_upper, 1);
  } else {
    negative_lower = domain.residue_lower - domain.modulus;
    negative_upper = domain.residue_upper - domain.modulus;
    if (negative_lower < domain.lower)
      negative_lower = domain.lower;
    if (negative_upper > domain.upper)
      negative_upper = domain.upper;
    lifted = ixs_interval_range(negative_lower, 1, negative_upper, 1);
  }
  original = domain.var->iv;
  refined = iv_intersect(original, lifted);
  if (!refined.valid || ixs_interval_is_empty(refined) ||
      bounds_intervals_equal(original, refined))
    return false;
  domain.var->iv = refined;
  bounds_mark_semantic_changed(b);
  refine_var_bit_consistency(b, domain.var);
  bounds_add_expr_raw(b, domain.symbol, refined);
  if (!b->oom)
    bounds_propagate_difference_bounds(b, domain.symbol->u.name, NULL);
  return !b->oom;
}

typedef struct {
  size_t watcher_index;
  int64_t modulus;
} bounds_mod_inverse_incident;

static int bounds_mod_inverse_incident_compare(const void *lhs,
                                               const void *rhs) {
  const bounds_mod_inverse_incident *a = lhs;
  const bounds_mod_inverse_incident *b = rhs;
  if (a->modulus > b->modulus)
    return -1;
  if (a->modulus < b->modulus)
    return 1;
  return a->watcher_index < b->watcher_index
             ? -1
             : a->watcher_index != b->watcher_index;
}

/* A crossing interval can change only by selecting one wholly negative or
 * nonnegative lift, which fixes its sign.  Once the sign is fixed, descending
 * modulus order is a topological order: a larger modulus can enable a smaller
 * one, never the reverse.  Thus one crossing scan plus one sorted pass reaches
 * the same fixed point in O(k log k) for k incident watchers. */
static bool bounds_mod_inverse_sign_fixed(ixs_bounds *b,
                                          const char *symbol_name) {
  ixs_var_bound *var = find_var(b, symbol_name);
  if (!var || !var->iv.valid || var->iv.lo_inf || var->iv.hi_inf)
    return false;
  return ixs_rat_cmp(var->iv.hi_p, var->iv.hi_q, 0, 1) < 0 ||
         ixs_rat_cmp(var->iv.lo_p, var->iv.lo_q, 0, 1) >= 0;
}

static bool bounds_visit_mod_inverse_watcher(ixs_bounds *b,
                                             size_t watcher_index) {
  ixs_mod_inverse_watcher *watcher;
  ixs_expr_bound *bound;
  assert(watcher_index < b->nmod_inverse_watchers);
  watcher = &b->mod_inverse_watchers[watcher_index];
  assert(watcher->expr_index < b->nexprs);
  bound = &b->exprs[watcher->expr_index];
  if (b->mod_inverse_watch_visits != SIZE_MAX)
    b->mod_inverse_watch_visits++;
  return bounds_refine_symbol_from_mod_range(b, bound->expr, bound->iv);
}

static bool
bounds_refine_mod_inverse_sign(ixs_bounds *b, const char *symbol_name,
                               const bounds_mod_inverse_incident *incident,
                               size_t incident_count) {
  size_t i;

  if (bounds_mod_inverse_sign_fixed(b, symbol_name))
    return true;
  for (i = 0; i < incident_count && !b->oom && !b->contradiction; i++) {
    if (bounds_visit_mod_inverse_watcher(b, incident[i].watcher_index))
      break;
  }
  return bounds_mod_inverse_sign_fixed(b, symbol_name);
}

static void bounds_refine_mod_inverse_symbol(ixs_bounds *b, ixs_node *symbol) {
  ixs_var_bound *var;
  size_t var_index;
  size_t watcher_link;
  size_t incident_count = 0;
  bounds_mod_inverse_incident *incident;
  ixs_arena_mark work_mark;
  size_t i;

  if (!b || !symbol || symbol->tag != IXS_SYM || b->oom)
    return;
  var = find_var(b, symbol->u.name);
  if (!var || !var->iv.valid || var->iv.lo_inf || var->iv.hi_inf ||
      !b->mod_inverse_heads)
    return;
  var_index = (size_t)(var - b->vars);
  if (var_index >= b->mod_inverse_head_cap)
    return;
  watcher_link = b->mod_inverse_heads[var_index];
  while (watcher_link) {
    size_t watcher_index = watcher_link - 1u;
    assert(watcher_index < b->nmod_inverse_watchers);
    incident_count++;
    assert(incident_count <= b->nmod_inverse_watchers);
    watcher_link = b->mod_inverse_watchers[watcher_index].next;
  }
  if (!incident_count)
    return;
  if (incident_count > SIZE_MAX / sizeof(*incident)) {
    b->oom = true;
    return;
  }
  work_mark = ixs_arena_save(&b->query_arena);
  incident = ixs_arena_alloc(
      &b->query_arena, incident_count * sizeof(*incident), sizeof(void *));
  if (!incident) {
    ixs_arena_restore(&b->query_arena, work_mark);
    b->oom = true;
    return;
  }
  watcher_link = b->mod_inverse_heads[var_index];
  for (i = 0; i < incident_count; i++) {
    size_t watcher_index = watcher_link - 1u;
    ixs_mod_inverse_watcher *watcher = &b->mod_inverse_watchers[watcher_index];
    ixs_node *mod;
    assert(watcher->expr_index < b->nexprs);
    mod = b->exprs[watcher->expr_index].expr;
    assert(mod->tag == IXS_MOD && mod->u.binary.rhs->tag == IXS_INT &&
           mod->u.binary.rhs->u.ival > 0);
    incident[i].watcher_index = watcher_index;
    incident[i].modulus = mod->u.binary.rhs->u.ival;
    watcher_link = b->mod_inverse_watchers[watcher_index].next;
  }
  if (!bounds_refine_mod_inverse_sign(b, symbol->u.name, incident,
                                      incident_count)) {
    ixs_arena_restore(&b->query_arena, work_mark);
    return;
  }
  qsort(incident, incident_count, sizeof(*incident),
        bounds_mod_inverse_incident_compare);
  for (i = 0; i < incident_count && !b->oom && !b->contradiction; i++)
    (void)bounds_visit_mod_inverse_watcher(b, incident[i].watcher_index);
  ixs_arena_restore(&b->query_arena, work_mark);
}

static void bounds_refine_mod_inverse_for_expr(ixs_bounds *b, ixs_node *expr) {
  if (!b || !expr || b->oom)
    return;
  if (expr->tag == IXS_MOD && expr->u.binary.lhs->tag == IXS_SYM) {
    bounds_refine_mod_inverse_symbol(b, expr->u.binary.lhs);
    return;
  }
  if (expr->tag == IXS_SYM)
    bounds_refine_mod_inverse_symbol(b, expr);
}

static bool bounds_lift_floor_symbol_range(ixs_node *round,
                                           ixs_interval quotient,
                                           ixs_node **symbol,
                                           ixs_interval *lifted) {
  ixs_node *argument;
  int64_t coefficient_p;
  int64_t denominator;
  int64_t quotient_lower;
  int64_t quotient_upper;
  int64_t upper_successor;
  int64_t lower;
  int64_t upper;

  if (!round || round->tag != IXS_FLOOR || !quotient.valid || quotient.lo_inf ||
      quotient.hi_inf)
    return false;
  argument = round->u.unary.arg;
  if (argument->tag != IXS_MUL || argument->u.mul.nfactors != 1u ||
      argument->u.mul.factors[0].exp != 1 ||
      argument->u.mul.factors[0].base->tag != IXS_SYM)
    return false;
  ixs_node_get_rat(argument->u.mul.coeff, &coefficient_p, &denominator);
  if (coefficient_p != 1 || denominator <= 0)
    return false;
  *symbol = argument->u.mul.factors[0].base;
  if (!ixs_node_is_integer_valued(*symbol))
    return false;
  quotient_lower = ixs_rat_ceil(quotient.lo_p, quotient.lo_q);
  quotient_upper = ixs_rat_floor(quotient.hi_p, quotient.hi_q);
  if (quotient_lower > quotient_upper ||
      !ixs_safe_mul(quotient_lower, denominator, &lower) ||
      !ixs_safe_add(quotient_upper, 1, &upper_successor) ||
      !ixs_safe_mul(upper_successor, denominator, &upper) ||
      !ixs_safe_sub(upper, 1, &upper))
    return false;
  *lifted = ixs_interval_range(lower, 1, upper, 1);
  return true;
}

/* A finite range for floor(x/d), with raw integer x and positive literal d,
 * maps back to the exact inclusive integer band for x. */
static void bounds_refine_symbol_from_floor_range(ixs_bounds *b,
                                                  ixs_node *round,
                                                  ixs_interval quotient) {
  ixs_node *symbol;
  ixs_var_bound *var;
  ixs_interval original;
  ixs_interval lifted;
  ixs_interval refined;

  if (!b || !bounds_lift_floor_symbol_range(round, quotient, &symbol, &lifted))
    return;
  var = get_or_create_var(b, symbol->u.name);
  if (!var)
    return;
  original = var->iv;
  refined = iv_intersect(original, lifted);
  if (!refined.valid || ixs_interval_is_empty(refined) ||
      bounds_intervals_equal(original, refined))
    return;
  var->iv = refined;
  bounds_mark_semantic_changed(b);
  refine_var_bit_consistency(b, var);
  bounds_add_expr_raw(b, symbol, refined);
  if (!b->oom)
    bounds_propagate_difference_bounds(b, symbol->u.name, NULL);
  if (!b->oom && !b->contradiction)
    bounds_refine_mod_inverse_symbol(b, symbol);
}

static void bounds_sync_raw_symbol_range(ixs_bounds *b, ixs_node *symbol) {
  ixs_var_bound *var;
  ixs_interval stored;
  ixs_interval refined;
  if (!b || !symbol || symbol->tag != IXS_SYM || b->oom)
    return;
  stored = bounds_get_expr_overrides(b, symbol);
  if (!stored.valid)
    return;
  var = get_or_create_var(b, symbol->u.name);
  if (!var)
    return;
  refined = iv_intersect(var->iv, stored);
  if (bounds_intervals_equal(var->iv, refined))
    return;
  var->iv = refined;
  bounds_mark_semantic_changed(b);
  bounds_cache_clear(b);
  refine_var_bit_consistency(b, var);
}

static bool bounds_propagate_added_expr_ranges(ixs_bounds *b, ixs_node *expr,
                                               ixs_node *canon, ixs_interval iv,
                                               size_t first_expr,
                                               size_t added_expr_end) {
  size_t i;

  for (i = first_expr; i < added_expr_end; i++)
    if (b->exprs[i].expr->tag == IXS_SYM)
      bounds_sync_raw_symbol_range(b, b->exprs[i].expr);
  if (expr->tag == IXS_SYM)
    bounds_sync_raw_symbol_range(b, expr);
  if (canon && canon != expr && canon->tag == IXS_SYM)
    bounds_sync_raw_symbol_range(b, canon);
  if (b->oom || b->contradiction)
    return false;
  bounds_add_difference_range(b, expr, iv);
  if (canon && canon != expr)
    bounds_add_difference_range(b, canon, iv);
  if (b->oom || b->contradiction)
    return false;
  if (expr->tag == IXS_SYM)
    bounds_propagate_difference_bounds(b, expr->u.name, NULL);
  if (canon && canon != expr && canon->tag == IXS_SYM)
    bounds_propagate_difference_bounds(b, canon->u.name, NULL);
  return !b->oom && !b->contradiction;
}

IXS_STATIC void ixs_bounds_add_expr(ixs_bounds *b, ixs_node *expr,
                                    ixs_interval iv) {
  ixs_node *canon = NULL;
  size_t first_expr = b ? b->nexprs : 0u;
  size_t added_expr_end;
  size_t i;
  bounds_add_expr_raw(b, expr, iv);
  if (b->oom)
    return;
  bounds_add_proportional_range(b, expr, iv);
  if (b->oom)
    return;
  canon = bounds_canonical_expr(b, expr);
  if (canon && canon != expr) {
    bounds_add_expr_raw(b, canon, iv);
    if (!b->oom)
      bounds_add_proportional_range(b, canon, iv);
  }
  if (b->oom || b->contradiction)
    return;
  added_expr_end = b->nexprs;
  if (!bounds_propagate_added_expr_ranges(b, expr, canon, iv, first_expr,
                                          added_expr_end))
    return;
  for (i = first_expr; i < added_expr_end; i++)
    bounds_refine_mod_inverse_for_expr(b, b->exprs[i].expr);
  bounds_refine_mod_inverse_for_expr(b, expr);
  if (canon && canon != expr)
    bounds_refine_mod_inverse_for_expr(b, canon);
  if (b->oom || b->contradiction)
    return;
  if (expr->tag == IXS_FLOOR)
    bounds_refine_symbol_from_floor_range(b, expr,
                                          bounds_get_expr_overrides(b, expr));
  if (canon && canon != expr && canon->tag == IXS_FLOOR)
    bounds_refine_symbol_from_floor_range(b, canon,
                                          bounds_get_expr_overrides(b, canon));
}

static bool bounds_is_known_nonzero(const ixs_bounds *b, const ixs_node *expr) {
  size_t i;
  if (!b || !expr)
    return false;
  for (i = 0; i < b->nnonzero; i++) {
    if (b->nonzero[i] == expr)
      return true;
  }
  return false;
}

static bool bounds_add_nonzero_one(ixs_bounds *b, ixs_node *expr) {
  ixs_node **grown;
  size_t new_cap;
  if (!b || !expr || b->oom || bounds_is_known_nonzero(b, expr))
    return false;
  bounds_empty_cache_invalidate(b);
  if (b->nnonzero < b->nonzero_cap) {
    b->nonzero[b->nnonzero++] = expr;
    bounds_mark_semantic_changed(b);
    return true;
  }
  new_cap = b->nonzero_cap ? b->nonzero_cap * 2u : 4u;
  if (new_cap < b->nonzero_cap || new_cap > SIZE_MAX / sizeof(*b->nonzero)) {
    b->oom = true;
    return false;
  }
  grown = ixs_arena_alloc(b->scratch, new_cap * sizeof(*grown), sizeof(void *));
  if (!grown) {
    b->oom = true;
    return false;
  }
  if (b->nnonzero)
    memcpy(grown, b->nonzero, b->nnonzero * sizeof(*grown));
  b->nonzero = grown;
  b->nonzero_cap = new_cap;
  b->nonzero[b->nnonzero++] = expr;
  bounds_mark_semantic_changed(b);
  return true;
}

static void bounds_add_nonzero_product_bases(ixs_bounds *b, ixs_node *expr) {
  uint32_t i;
  if (!b || !expr || b->oom || expr->tag != IXS_MUL)
    return;
  for (i = 0; i < expr->u.mul.nfactors; i++) {
    const ixs_mulfactor *factor = &expr->u.mul.factors[i];
    ixs_node *canonical;
    if (factor->exp <= 0)
      continue;
    bounds_add_nonzero_one(b, factor->base);
    if (b->oom)
      return;
    canonical = bounds_canonical_expr(b, factor->base);
    if (canonical && canonical != factor->base &&
        !ixs_node_is_sentinel(canonical))
      bounds_add_nonzero_one(b, canonical);
    if (b->oom)
      return;
  }
}

static void bounds_add_nonzero(ixs_bounds *b, ixs_node *expr) {
  ixs_node *canonical;
  if (!b || !expr || b->oom)
    return;
  bounds_add_nonzero_one(b, expr);
  if (b->oom || (expr->tag != IXS_MUL && expr->tag != IXS_PIECEWISE))
    return;

  canonical = bounds_canonical_expr(b, expr);
  if (b->oom)
    return;
  if (canonical && canonical != expr && !ixs_node_is_sentinel(canonical))
    bounds_add_nonzero_one(b, canonical);
  if (b->oom)
    return;

  bounds_add_nonzero_product_bases(b, expr);
  if (canonical && canonical != expr && !ixs_node_is_sentinel(canonical))
    bounds_add_nonzero_product_bases(b, canonical);
}

/*
 * Extract interval bounds and modular congruence from a comparison.
 * Patterns: sym >= 0, sym < N, Mod(sym, M) == R, etc.
 */
static bool bounds_add_sym_cmp_const(ixs_bounds *b, ixs_node *lhs,
                                     ixs_node *rhs, ixs_cmp_op op) {
  ixs_node *sym;
  ixs_node *constant;
  ixs_cmp_op effective_op;
  ixs_interval sym_iv;
  int64_t p;
  int64_t q;

  if (lhs->tag == IXS_SYM && ixs_node_is_const(rhs)) {
    sym = lhs;
    constant = rhs;
    effective_op = op;
  } else if (rhs->tag == IXS_SYM && ixs_node_is_const(lhs)) {
    sym = rhs;
    constant = lhs;
    effective_op = flip_cmp(op);
  } else {
    return false;
  }

  ixs_node_get_rat(constant, &p, &q);
  apply_sym_cmp_const(b, sym->u.name, effective_op, p, q);
  sym_iv = interval_from_sym_cmp_const(effective_op, p, q);
  if (sym_iv.valid)
    ixs_bounds_add_expr(b, sym, sym_iv);
  return true;
}

static bool bounds_add_affine_zero_cmp(ixs_bounds *b, ixs_node *lhs,
                                       ixs_node *rhs, ixs_cmp_op op) {
  ixs_node *sym;
  ixs_cmp_op effective_op;
  ixs_interval sym_iv;
  int64_t tp;
  int64_t tq;
  int64_t kp;
  int64_t kq;
  int64_t np;
  int64_t nq;
  int64_t raw_p;
  int64_t raw_q;
  int64_t p;
  int64_t q;

  if (!ixs_node_is_zero(rhs) || lhs->tag != IXS_ADD || lhs->u.add.nterms != 1 ||
      lhs->u.add.terms[0].term->tag != IXS_SYM)
    return false;

  sym = lhs->u.add.terms[0].term;
  ixs_node_get_rat(lhs->u.add.terms[0].coeff, &tp, &tq);
  ixs_node_get_rat(lhs->u.add.coeff, &kp, &kq);

  /* tp/tq * sym + kp/kq OP 0, so divide -kp/kq by tp/tq. */
  if (tp == 0 || !ixs_rat_neg(kp, kq, &np, &nq) ||
      !ixs_rat_mul(np, nq, tq, tp, &raw_p, &raw_q) ||
      !ixs_rat_normalize(raw_p, raw_q, &p, &q))
    return true;

  effective_op = (ixs_rat_cmp(tp, tq, 0, 1) < 0) ? flip_cmp(op) : op;
  apply_sym_cmp_const(b, sym->u.name, effective_op, p, q);
  sym_iv = interval_from_sym_cmp_const(effective_op, p, q);
  if (sym_iv.valid)
    ixs_bounds_add_expr(b, sym, sym_iv);
  return true;
}

static void bounds_add_assumption_impl(ixs_bounds *b, ixs_node *a) {
  ixs_node *equality_lhs;
  ixs_node *equality_rhs;
  int64_t equality_offset;
  ixs_node *lhs;
  ixs_node *rhs;
  ixs_cmp_op op;

  if (a->tag != IXS_CMP)
    return;
  bounds_cache_clear(b);

  extract_modrem(b, a);
  extract_bitfacts(b, a);

  lhs = a->u.binary.lhs;
  rhs = a->u.binary.rhs;
  op = a->u.binary.cmp_op;

  if (op == IXS_CMP_EQ) {
    if (bounds_extract_cmp_exact_relation(b, a, &equality_lhs, &equality_rhs,
                                          &equality_offset))
      bounds_add_exact_relation(b, equality_lhs, equality_rhs, equality_offset);
    else if (!b->oom &&
             extract_cmp_node_equality(a, &equality_lhs, &equality_rhs))
      bounds_add_exact_relation(b, equality_lhs, equality_rhs, 0);
    if (b->oom || b->contradiction)
      return;
  }

  if (op == IXS_CMP_NE) {
    if (ixs_node_is_zero(rhs))
      bounds_add_nonzero(b, lhs);
    else if (ixs_node_is_zero(lhs))
      bounds_add_nonzero(b, rhs);
  }

  if (bounds_add_sym_cmp_const(b, lhs, rhs, op))
    return;

  if (bounds_add_affine_zero_cmp(b, lhs, rhs, op))
    return;

  /* Fallback: expr op 0 for non-symbol lhs. Store as expression bound. */
  if (ixs_node_is_zero(rhs)) {
    add_expr_integer_zero_cmp(b, lhs, op);
  } else if (ixs_bounds_check_defined(b, lhs) == IXS_CHECK_TRUE &&
             ixs_bounds_check_defined(b, rhs) == IXS_CHECK_TRUE) {
    ixs_node *difference = simp_sub(b->ctx, lhs, rhs);
    if (!difference) {
      b->oom = true;
      return;
    }
    if (!ixs_node_is_sentinel(difference))
      add_expr_integer_zero_cmp(b, difference, op);
  }
}

IXS_STATIC bool ixs_bounds_add_assumption(ixs_bounds *b, ixs_node *a) {
  if (!b || !a || b->oom)
    return false;
  bounds_add_assumption_impl(b, a);
  return !b->oom;
}

/* GCD of a positive modulus and a conservative dividend step.  Computing the
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

static void bitfacts_apply_exact(ixs_bitfacts *bits, int64_t val) {
  uint64_t u = (uint64_t)val;
  bits->known_zero |= ~u;
  bits->known_one |= u;
  if (val == 0)
    bits->pow2 = IXS_POW2_OR_ZERO;
  else if (int64_is_positive_pow2(val))
    bits->pow2 = IXS_POW2_POSITIVE;
}

static void bitfacts_apply_interval(ixs_bitfacts *bits,
                                    const ixs_interval *iv) {
  int64_t exact;
  if (interval_exact_int(iv, &exact)) {
    bitfacts_apply_exact(bits, exact);
    return;
  }
  if (!iv->valid || iv->lo_inf || iv->hi_inf || iv->hi_q != 1 || iv->hi_p < 0 ||
      !interval_lower_at_least(iv, 0, 1))
    return;
  bits->known_zero |= ~value_span_mask((uint64_t)iv->hi_p);
}

static bool bitfacts_low_value(const ixs_bitfacts *bits, unsigned nbits,
                               uint64_t *value) {
  uint64_t mask = low_mask(nbits);
  if (((bits->known_zero | bits->known_one) & mask) != mask)
    return false;
  *value = bits->known_one & mask;
  return true;
}

static void bitfacts_set_low_value(ixs_bitfacts *bits, unsigned nbits,
                                   uint64_t value) {
  uint64_t mask = low_mask(nbits);
  bits->known_one |= value & mask;
  bits->known_zero |= (~value) & mask;
}

static void bitfacts_apply_modrem(ixs_bitfacts *bits, int64_t modulus,
                                  int64_t remainder) {
  uint64_t mask, rem;
  if (!int64_modulus_is_pow2(modulus))
    return;
  mask = (uint64_t)modulus - 1u;
  rem = (uint64_t)remainder & mask;
  bits->known_zero |= (~rem) & mask;
  bits->known_one |= rem & mask;
}

static bool bounds_get_symbol_bitfacts(ixs_bounds *b, const char *name,
                                       ixs_bitfacts *out) {
  int64_t exact;
  ixs_var_bound *v = find_var(b, name);
  if (v) {
    out->known_zero |= v->bits.known_zero;
    out->known_one |= v->bits.known_one;
    if (v->bits.pow2 == IXS_POW2_POSITIVE ||
        (v->bits.pow2 == IXS_POW2_OR_ZERO && out->pow2 == IXS_POW2_UNKNOWN))
      out->pow2 = v->bits.pow2;
    bitfacts_apply_modrem(out, v->modulus, v->remainder);
    if (interval_exact_int(&v->iv, &exact))
      bitfacts_apply_exact(out, exact);
    if (out->pow2 == IXS_POW2_OR_ZERO && interval_lower_at_least(&v->iv, 1, 1))
      out->pow2 = IXS_POW2_POSITIVE;
  }
  return true;
}

static void bitfacts_apply_and(ixs_bitfacts *out, const ixs_bitfacts *a,
                               const ixs_bitfacts *b) {
  out->known_one = a->known_one & b->known_one;
  out->known_zero = a->known_zero | b->known_zero;
  out->pow2 = IXS_POW2_UNKNOWN;
}

static void bitfacts_apply_or(ixs_bitfacts *out, const ixs_bitfacts *a,
                              const ixs_bitfacts *b) {
  out->known_one = a->known_one | b->known_one;
  out->known_zero = a->known_zero & b->known_zero;
  out->pow2 = IXS_POW2_UNKNOWN;
}

static void bitfacts_apply_xor(ixs_bitfacts *out, const ixs_bitfacts *a,
                               const ixs_bitfacts *b) {
  out->known_one =
      (a->known_one & b->known_zero) | (a->known_zero & b->known_one);
  out->known_zero =
      (a->known_zero & b->known_zero) | (a->known_one & b->known_one);
  out->pow2 = IXS_POW2_UNKNOWN;
}

typedef struct {
  ixs_bitfacts bits;
  bool success;
} bounds_bitfacts_child;

static bool bitfacts_scale_nonnegative_pow2_known(
    ixs_bounds *b, ixs_node *term, int64_t coeff,
    const bounds_bitfacts_child *child, ixs_bitfacts *out) {
  ixs_interval iv;
  uint64_t scale;
  unsigned shift;

  if (!child->success || !int64_is_positive_pow2(coeff) ||
      !ixs_node_is_integer_valued(term))
    return false;

  iv = bounds_get_tracked(b, term);
  scale = (uint64_t)coeff;
  if (!interval_lower_at_least(&iv, 0, 1) || iv.hi_inf || iv.hi_q != 1 ||
      iv.hi_p < 0 || (uint64_t)iv.hi_p > (uint64_t)INT64_MAX / scale)
    return false;

  shift = bit_ctz64(scale);
  bitfacts_unknown(out);
  out->known_zero = (child->bits.known_zero << shift) | low_mask(shift);
  out->known_one = child->bits.known_one << shift;
  return true;
}

/* One linear pass over normalized addends. Pairwise-disjoint possible-one
 * masks prove that integer addition cannot carry between addends. */
static void
bitfacts_apply_carry_free_add_known(ixs_bounds *b, ixs_node *expr,
                                    const bounds_bitfacts_child *children,
                                    ixs_bitfacts *out) {
  ixs_bitfacts addend;
  uint64_t known_one, possible;
  int64_t cp, cq;
  uint32_t i;

  ixs_node_get_rat(expr->u.add.coeff, &cp, &cq);
  if (cq != 1 || cp < 0)
    return;

  bitfacts_unknown(&addend);
  bitfacts_apply_exact(&addend, cp);
  possible = ~addend.known_zero;
  known_one = addend.known_one;

  for (i = 0; i < expr->u.add.nterms; i++) {
    uint64_t term_possible;
    int64_t tp, tq;

    ixs_node_get_rat(expr->u.add.terms[i].coeff, &tp, &tq);
    if (tq != 1 || !bitfacts_scale_nonnegative_pow2_known(
                       b, expr->u.add.terms[i].term, tp, &children[i], &addend))
      return;

    term_possible = ~addend.known_zero;
    if ((possible & term_possible) != 0)
      return;
    possible |= term_possible;
    known_one |= addend.known_one;
  }

  out->known_zero |= ~possible;
  out->known_one |= known_one;
}

static void bitfacts_apply_add_known(ixs_bounds *b, ixs_node *expr,
                                     const bounds_bitfacts_child *children,
                                     ixs_bitfacts *out) {
  unsigned nbits;
  int64_t cp, cq;

  ixs_node_get_rat(expr->u.add.coeff, &cp, &cq);
  if (cq != 1)
    return;

  bitfacts_apply_carry_free_add_known(b, expr, children, out);

  for (nbits = 1; nbits <= 64u; nbits++) {
    uint64_t mask = low_mask(nbits);
    uint64_t sum = (uint64_t)cp & mask;
    uint32_t i;
    bool known = true;

    for (i = 0; i < expr->u.add.nterms; i++) {
      uint64_t term_value;
      int64_t tp, tq;

      ixs_node_get_rat(expr->u.add.terms[i].coeff, &tp, &tq);
      if (tq != 1 || !children[i].success ||
          !bitfacts_low_value(&children[i].bits, nbits, &term_value)) {
        known = false;
        break;
      }
      sum = (sum + (((uint64_t)tp * term_value) & mask)) & mask;
    }

    if (!known)
      break;
    bitfacts_set_low_value(out, nbits, sum);
    if (nbits == 64u)
      break;
  }
}

static void bitfacts_apply_mul_known(ixs_node *expr,
                                     const bounds_bitfacts_child *child,
                                     ixs_bitfacts *out) {
  uint64_t coeff;
  unsigned shift, i;

  if (expr->u.mul.coeff->tag != IXS_INT || expr->u.mul.coeff->u.ival <= 0 ||
      expr->u.mul.nfactors != 1 || expr->u.mul.factors[0].exp != 1 ||
      !ixs_node_is_integer_valued(expr))
    return;

  coeff = (uint64_t)expr->u.mul.coeff->u.ival;
  if (!uint64_is_pow2(coeff) || !child->success)
    return;

  shift = bit_ctz64(coeff);
  out->known_zero |= low_mask(shift);
  for (i = shift; i < 64u; i++) {
    uint64_t src = ((uint64_t)1) << (i - shift);
    uint64_t dst = ((uint64_t)1) << i;
    if (child->bits.known_zero & src)
      out->known_zero |= dst;
    if (child->bits.known_one & src)
      out->known_one |= dst;
  }
}

static bool extract_pow2_dividend(ixs_node *expr, ixs_node **dividend,
                                  uint64_t *denom) {
  int64_t cp, cq;
  if (!expr || expr->tag != IXS_MUL || expr->u.mul.nfactors != 1 ||
      expr->u.mul.factors[0].exp != 1)
    return false;
  ixs_node_get_rat(expr->u.mul.coeff, &cp, &cq);
  if (cp != 1 || cq <= 0 || !int64_modulus_is_pow2(cq))
    return false;
  *dividend = expr->u.mul.factors[0].base;
  *denom = (uint64_t)cq;
  return true;
}

static void bitfacts_apply_floor_div_known(ixs_bounds *b, ixs_node *dividend,
                                           uint64_t denom,
                                           const bounds_bitfacts_child *child,
                                           ixs_bitfacts *out) {
  ixs_interval iv;
  unsigned shift, i;

  iv = bounds_get_tracked(b, dividend);
  if (!child->success || !interval_lower_at_least(&iv, 0, 1))
    return;

  shift = bit_ctz64(denom);
  for (i = 0; i + shift < 64u; i++) {
    uint64_t src = ((uint64_t)1) << (i + shift);
    uint64_t dst = ((uint64_t)1) << i;
    if (child->bits.known_zero & src)
      out->known_zero |= dst;
    if (child->bits.known_one & src)
      out->known_one |= dst;
  }
}

static void bitfacts_apply_mod_known(ixs_node *expr,
                                     const bounds_bitfacts_child *child,
                                     ixs_bitfacts *out) {
  uint64_t mask;
  int64_t modulus;

  if (expr->u.binary.rhs->tag != IXS_INT ||
      !int64_modulus_is_pow2(expr->u.binary.rhs->u.ival) ||
      !ixs_node_is_integer_valued(expr->u.binary.lhs))
    return;

  modulus = expr->u.binary.rhs->u.ival;
  mask = (uint64_t)modulus - 1u;
  out->known_zero |= ~mask;
  if (child->success) {
    out->known_zero |= child->bits.known_zero & mask;
    out->known_one |= child->bits.known_one & mask;
  }
}

static bool bitfacts_apply_assoc_known(ixs_node *expr,
                                       const bounds_bitfacts_child *children,
                                       ixs_bitfacts *out) {
  ixs_bitfacts result, arg, next;
  uint32_t i;
  if (expr->u.assoc.nargs == 0 || !expr->u.assoc.args)
    return false;
  if (!children[0].success)
    return false;
  result = children[0].bits;
  for (i = 1; i < expr->u.assoc.nargs; i++) {
    if (!children[i].success)
      return false;
    arg = children[i].bits;
    if (expr->tag == IXS_AND)
      bitfacts_apply_and(&next, &result, &arg);
    else if (expr->tag == IXS_OR)
      bitfacts_apply_or(&next, &result, &arg);
    else
      bitfacts_apply_xor(&next, &result, &arg);
    result = next;
  }
  *out = result;
  return true;
}

static inline bool bitfacts_apply_bool_value(ixs_bitfacts *out) {
  out->known_zero = ~(uint64_t)1;
  out->known_one = 0;
  return true;
}

typedef enum {
  BOUNDS_BITFACTS_INITIAL,
  BOUNDS_BITFACTS_ADD,
  BOUNDS_BITFACTS_MUL,
  BOUNDS_BITFACTS_FLOOR,
  BOUNDS_BITFACTS_MOD,
  BOUNDS_BITFACTS_ASSOC
} bounds_bitfacts_stage;

typedef struct {
  ixs_node *expr;
  ixs_node *child_expr;
  bounds_query_scope scope;
  bounds_bitfacts_child *children;
  ixs_bitfacts bits;
  uint64_t argument;
  uint32_t index;
  uint32_t child_count;
  bounds_bitfacts_stage stage;
  bool tracked;
} bounds_bitfacts_frame;

typedef struct {
  ixs_bounds *bounds;
  bounds_bitfacts_frame *frames;
  size_t depth;
  size_t capacity;
  bounds_bitfacts_child child;
} bounds_bitfacts_query;

static bool bounds_bitfacts_push(bounds_bitfacts_query *query, ixs_node *expr) {
  bounds_bitfacts_frame *grown;
  size_t capacity;
  size_t old_bytes;
  size_t new_bytes;
  if (query->depth == query->capacity) {
    capacity = query->capacity ? query->capacity * 2u : 16u;
    if (capacity < query->capacity ||
        capacity > SIZE_MAX / sizeof(*query->frames)) {
      query->bounds->oom = true;
      return false;
    }
    old_bytes = query->capacity * sizeof(*query->frames);
    new_bytes = capacity * sizeof(*query->frames);
    grown = ixs_arena_grow(query->bounds->scratch, query->frames, old_bytes,
                           new_bytes, sizeof(void *));
    if (!grown) {
      query->bounds->oom = true;
      return false;
    }
    query->frames = grown;
    query->capacity = capacity;
  }
  memset(&query->frames[query->depth], 0, sizeof(*query->frames));
  query->frames[query->depth++].expr = expr;
  return true;
}

static bool bounds_bitfacts_alloc_children(bounds_bitfacts_query *query,
                                           bounds_bitfacts_frame *frame,
                                           uint32_t count) {
  size_t bytes;
  if (count == 0)
    return false;
  bytes = (size_t)count * sizeof(*frame->children);
  frame->children =
      ixs_arena_alloc(query->bounds->scratch, bytes, sizeof(void *));
  if (!frame->children) {
    query->bounds->oom = true;
    return false;
  }
  memset(frame->children, 0, bytes);
  frame->child_count = count;
  return true;
}

static void bounds_bitfacts_complete(bounds_bitfacts_query *query, bool success,
                                     ixs_bitfacts bits) {
  bounds_bitfacts_frame *frame = &query->frames[query->depth - 1u];
  if (frame->tracked) {
    bounds_query_cache_entry *entry =
        bounds_query_finish(&frame->scope, success);
    if (entry && entry->outcome == BOUNDS_QUERY_OUTCOME_VALUE)
      entry->result.bitfacts = bits;
    else
      success = false;
  }
  query->depth--;
  query->child.success = success;
  query->child.bits = bits;
}

static void bounds_bitfacts_unwind(bounds_bitfacts_query *query) {
  ixs_bitfacts unknown;
  bitfacts_unknown(&unknown);
  while (query->depth != 0)
    bounds_bitfacts_complete(query, false, unknown);
}

typedef enum {
  BOUNDS_BITFACTS_STEP_ADVANCED,
  BOUNDS_BITFACTS_STEP_UNHANDLED,
  BOUNDS_BITFACTS_STEP_OOM
} bounds_bitfacts_step;

static bounds_bitfacts_step
bounds_bitfacts_prepare_frame(bounds_bitfacts_query *query,
                              bounds_bitfacts_frame *frame,
                              ixs_bitfacts unknown) {
  ixs_bounds *b = query->bounds;
  ixs_node *node = frame->expr;
  ixs_interval iv;

  /* Stack-local synthetic symbols are valid read-only operands but are not
   * memoized because bounds_query_should_track requires VALID. */
  if (!node) {
    bounds_bitfacts_complete(query, false, unknown);
    return BOUNDS_BITFACTS_STEP_ADVANCED;
  }
  if (bounds_query_should_track(b, node)) {
    bounds_query_cache_entry *cached = NULL;
    bounds_query_enter_result enter = bounds_query_begin(
        b, BOUNDS_QUERY_BITFACTS, node, 0, &frame->scope, &cached);
    if (enter == BOUNDS_QUERY_ENTER_CACHED) {
      bounds_bitfacts_complete(query, cached->success, cached->result.bitfacts);
      return BOUNDS_BITFACTS_STEP_ADVANCED;
    }
    if (enter != BOUNDS_QUERY_ENTER_STARTED) {
      bounds_bitfacts_complete(query, false, unknown);
      return BOUNDS_BITFACTS_STEP_ADVANCED;
    }
    frame->tracked = true;
  }
  bitfacts_unknown(&frame->bits);
  iv = bounds_get_tracked(b, node);
  bitfacts_apply_interval(&frame->bits, &iv);
  return b->oom ? BOUNDS_BITFACTS_STEP_OOM : BOUNDS_BITFACTS_STEP_UNHANDLED;
}

static bounds_bitfacts_step
bounds_bitfacts_start_scalar(bounds_bitfacts_query *query,
                             bounds_bitfacts_frame *frame) {
  ixs_node *node = frame->expr;
  switch (node->tag) {
  case IXS_INT:
    bitfacts_apply_exact(&frame->bits, node->u.ival);
    bounds_bitfacts_complete(query, true, frame->bits);
    return BOUNDS_BITFACTS_STEP_ADVANCED;
  case IXS_RAT:
    if (node->u.rat.q == 1)
      bitfacts_apply_exact(&frame->bits, node->u.rat.p);
    bounds_bitfacts_complete(query, node->u.rat.q == 1, frame->bits);
    return BOUNDS_BITFACTS_STEP_ADVANCED;
  case IXS_SYM:
    bounds_get_symbol_bitfacts(query->bounds, node->u.name, &frame->bits);
    bounds_bitfacts_complete(query, true, frame->bits);
    return BOUNDS_BITFACTS_STEP_ADVANCED;
  case IXS_CMP:
  case IXS_NOT:
    bitfacts_apply_bool_value(&frame->bits);
    bounds_bitfacts_complete(query, true, frame->bits);
    return BOUNDS_BITFACTS_STEP_ADVANCED;
  case IXS_CEIL:
  case IXS_TRUNC:
  case IXS_PIECEWISE:
  case IXS_MAX:
  case IXS_MIN:
    bounds_bitfacts_complete(query, ixs_node_is_integer_valued(node),
                             frame->bits);
    return BOUNDS_BITFACTS_STEP_ADVANCED;
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    bounds_bitfacts_complete(query, false, frame->bits);
    return BOUNDS_BITFACTS_STEP_ADVANCED;
  default:
    return BOUNDS_BITFACTS_STEP_UNHANDLED;
  }
}

static bounds_bitfacts_step
bounds_bitfacts_start_assoc(bounds_bitfacts_query *query,
                            bounds_bitfacts_frame *frame) {
  ixs_node *node = frame->expr;
  if (!node->u.assoc.args || node->u.assoc.nargs == 0) {
    bounds_bitfacts_complete(query, false, frame->bits);
    return BOUNDS_BITFACTS_STEP_ADVANCED;
  }
  if (!bounds_bitfacts_alloc_children(query, frame, node->u.assoc.nargs))
    return BOUNDS_BITFACTS_STEP_OOM;
  frame->stage = BOUNDS_BITFACTS_ASSOC;
  return bounds_bitfacts_push(query, node->u.assoc.args[0])
             ? BOUNDS_BITFACTS_STEP_ADVANCED
             : BOUNDS_BITFACTS_STEP_OOM;
}

static bounds_bitfacts_step
bounds_bitfacts_start_composite(bounds_bitfacts_query *query,
                                bounds_bitfacts_frame *frame) {
  ixs_node *node = frame->expr;
  switch (node->tag) {
  case IXS_ADD:
    if (node->u.add.nterms == 0) {
      bitfacts_apply_add_known(query->bounds, node, NULL, &frame->bits);
      bounds_bitfacts_complete(query, true, frame->bits);
      return BOUNDS_BITFACTS_STEP_ADVANCED;
    }
    if (!bounds_bitfacts_alloc_children(query, frame, node->u.add.nterms))
      return BOUNDS_BITFACTS_STEP_OOM;
    frame->stage = BOUNDS_BITFACTS_ADD;
    return bounds_bitfacts_push(query, node->u.add.terms[0].term)
               ? BOUNDS_BITFACTS_STEP_ADVANCED
               : BOUNDS_BITFACTS_STEP_OOM;
  case IXS_MUL:
    if (node->u.mul.coeff->tag != IXS_INT || node->u.mul.coeff->u.ival <= 0 ||
        node->u.mul.nfactors != 1 || node->u.mul.factors[0].exp != 1 ||
        !ixs_node_is_integer_valued(node) ||
        !uint64_is_pow2((uint64_t)node->u.mul.coeff->u.ival)) {
      bounds_bitfacts_complete(query, true, frame->bits);
      return BOUNDS_BITFACTS_STEP_ADVANCED;
    }
    frame->stage = BOUNDS_BITFACTS_MUL;
    return bounds_bitfacts_push(query, node->u.mul.factors[0].base)
               ? BOUNDS_BITFACTS_STEP_ADVANCED
               : BOUNDS_BITFACTS_STEP_OOM;
  case IXS_FLOOR:
    if (!extract_pow2_dividend(node->u.unary.arg, &frame->child_expr,
                               &frame->argument)) {
      bounds_bitfacts_complete(query, true, frame->bits);
      return BOUNDS_BITFACTS_STEP_ADVANCED;
    }
    frame->stage = BOUNDS_BITFACTS_FLOOR;
    return bounds_bitfacts_push(query, frame->child_expr)
               ? BOUNDS_BITFACTS_STEP_ADVANCED
               : BOUNDS_BITFACTS_STEP_OOM;
  case IXS_MOD:
    if (node->u.binary.rhs->tag != IXS_INT ||
        !int64_modulus_is_pow2(node->u.binary.rhs->u.ival) ||
        !ixs_node_is_integer_valued(node->u.binary.lhs)) {
      bounds_bitfacts_complete(query, true, frame->bits);
      return BOUNDS_BITFACTS_STEP_ADVANCED;
    }
    frame->stage = BOUNDS_BITFACTS_MOD;
    return bounds_bitfacts_push(query, node->u.binary.lhs)
               ? BOUNDS_BITFACTS_STEP_ADVANCED
               : BOUNDS_BITFACTS_STEP_OOM;
  case IXS_AND:
  case IXS_OR:
  case IXS_XOR:
    return bounds_bitfacts_start_assoc(query, frame);
  default:
    bounds_bitfacts_complete(query, false, frame->bits);
    return BOUNDS_BITFACTS_STEP_ADVANCED;
  }
}

static bounds_bitfacts_step
bounds_bitfacts_resume_frame(bounds_bitfacts_query *query,
                             bounds_bitfacts_frame *frame) {
  ixs_node *node = frame->expr;
  switch (frame->stage) {
  case BOUNDS_BITFACTS_ADD:
  case BOUNDS_BITFACTS_ASSOC:
    frame->children[frame->index++] = query->child;
    if (frame->index < frame->child_count) {
      ixs_node *child = frame->stage == BOUNDS_BITFACTS_ADD
                            ? node->u.add.terms[frame->index].term
                            : node->u.assoc.args[frame->index];
      return bounds_bitfacts_push(query, child) ? BOUNDS_BITFACTS_STEP_ADVANCED
                                                : BOUNDS_BITFACTS_STEP_OOM;
    }
    if (frame->stage == BOUNDS_BITFACTS_ADD) {
      bitfacts_apply_add_known(query->bounds, node, frame->children,
                               &frame->bits);
      bounds_bitfacts_complete(query, true, frame->bits);
    } else {
      bool success =
          bitfacts_apply_assoc_known(node, frame->children, &frame->bits);
      bounds_bitfacts_complete(query, success, frame->bits);
    }
    return BOUNDS_BITFACTS_STEP_ADVANCED;
  case BOUNDS_BITFACTS_MUL:
    bitfacts_apply_mul_known(node, &query->child, &frame->bits);
    bounds_bitfacts_complete(query, true, frame->bits);
    return BOUNDS_BITFACTS_STEP_ADVANCED;
  case BOUNDS_BITFACTS_FLOOR:
    bitfacts_apply_floor_div_known(query->bounds, frame->child_expr,
                                   frame->argument, &query->child,
                                   &frame->bits);
    bounds_bitfacts_complete(query, true, frame->bits);
    return BOUNDS_BITFACTS_STEP_ADVANCED;
  case BOUNDS_BITFACTS_MOD:
    bitfacts_apply_mod_known(node, &query->child, &frame->bits);
    bounds_bitfacts_complete(query, true, frame->bits);
    return BOUNDS_BITFACTS_STEP_ADVANCED;
  case BOUNDS_BITFACTS_INITIAL:
    bounds_bitfacts_complete(query, false, frame->bits);
    return BOUNDS_BITFACTS_STEP_ADVANCED;
  }
  return BOUNDS_BITFACTS_STEP_ADVANCED;
}

static bool bounds_get_bitfacts_iterative(ixs_bounds *b, ixs_node *expr,
                                          ixs_bitfacts *out) {
  ixs_arena_mark mark;
  bounds_bitfacts_query query;
  ixs_bitfacts unknown;
  bitfacts_unknown(&unknown);
  if (!b || !expr || !out || b->oom)
    return false;
  mark = ixs_arena_save(b->scratch);
  memset(&query, 0, sizeof(query));
  query.bounds = b;
  if (!bounds_bitfacts_push(&query, expr))
    goto failed;

  while (query.depth != 0) {
    bounds_bitfacts_frame *frame = &query.frames[query.depth - 1u];
    bounds_bitfacts_step step;
    if (frame->stage == BOUNDS_BITFACTS_INITIAL) {
      step = bounds_bitfacts_prepare_frame(&query, frame, unknown);
      if (step == BOUNDS_BITFACTS_STEP_OOM)
        goto failed;
      if (step == BOUNDS_BITFACTS_STEP_ADVANCED)
        continue;
      step = bounds_bitfacts_start_scalar(&query, frame);
      if (step == BOUNDS_BITFACTS_STEP_UNHANDLED)
        step = bounds_bitfacts_start_composite(&query, frame);
    } else {
      step = bounds_bitfacts_resume_frame(&query, frame);
    }
    if (step == BOUNDS_BITFACTS_STEP_OOM)
      goto failed;
  }

  *out = query.child.bits;
  ixs_arena_restore(b->scratch, mark);
  return query.child.success;

failed:
  bounds_bitfacts_unwind(&query);
  bitfacts_unknown(out);
  ixs_arena_restore(b->scratch, mark);
  return false;
}

static bool bounds_get_bitfacts_tracked(ixs_bounds *b, ixs_node *expr,
                                        ixs_bitfacts *out) {
  return bounds_get_bitfacts_iterative(b, expr, out);
}

IXS_STATIC bool ixs_bounds_get_bitfacts(ixs_bounds *b, ixs_node *expr,
                                        ixs_bitfacts *out) {
  return bounds_get_bitfacts_iterative(b, expr, out);
}

IXS_STATIC bool ixs_bounds_is_pow2_positive(ixs_bounds *b, ixs_node *expr) {
  ixs_bitfacts bits;
  if (!ixs_bounds_get_bitfacts(b, expr, &bits))
    return false;
  return bits.pow2 == IXS_POW2_POSITIVE;
}

IXS_STATIC bool ixs_bounds_is_pow2_or_zero(ixs_bounds *b, ixs_node *expr) {
  ixs_bitfacts bits;
  if (!ixs_bounds_get_bitfacts(b, expr, &bits))
    return false;
  return bits.pow2 == IXS_POW2_OR_ZERO || ixs_bounds_is_pow2_positive(b, expr);
}

static inline bool bounds_symbol_divisible(ixs_bounds *b, const char *name,
                                           int64_t m) {
  int64_t sym_mod, sym_rem;
  if (!ixs_bounds_get_modrem(b, name, &sym_mod, &sym_rem))
    return false;
  return sym_mod % m == 0 && sym_rem % m == 0;
}

static bool bounds_add_known_divisible(ixs_bounds *b, ixs_node *expr,
                                       int64_t modulus);
static bool bounds_known_residue(ixs_bounds *b, ixs_node *expr,
                                 uint64_t modulus, uint64_t *out);
static bool bounds_known_residue_independent(ixs_bounds *b, ixs_node *expr,
                                             uint64_t modulus, uint64_t *out);

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
  bounds_exact_proof_frame *frames;
  size_t depth;
  size_t capacity;
  bounds_exact_proof_memo memo;
  bool child_result;
  bool invalid;
  bounds_exact_proof_frame inline_frames[16];
  bounds_exact_proof_memo_entry inline_memo[32];
} bounds_exact_proof_query;

typedef enum {
  BOUNDS_EXACT_PROOF_STEP_ADVANCED,
  BOUNDS_EXACT_PROOF_STEP_OOM,
  BOUNDS_EXACT_PROOF_STEP_INVALID
} bounds_exact_proof_step;

static size_t bounds_exact_proof_hash(ixs_node *expr,
                                      bounds_exact_proof_kind kind,
                                      int64_t modulus) {
  size_t hash = bounds_expr_hash_ptr(expr);
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

static bool bounds_exact_proof_stack_grow(bounds_exact_proof_query *query) {
  size_t capacity = query->capacity ? query->capacity * 2u : 32u;
  size_t old_bytes;
  size_t new_bytes;
  bounds_exact_proof_frame *grown;
  if (capacity <= query->capacity ||
      capacity > SIZE_MAX / sizeof(*query->frames))
    return false;
  old_bytes = query->capacity * sizeof(*query->frames);
  new_bytes = capacity * sizeof(*query->frames);
  grown = ixs_arena_grow(query->bounds->scratch, query->frames, old_bytes,
                         new_bytes, sizeof(void *));
  if (!grown)
    return false;
  query->frames = grown;
  query->capacity = capacity;
  return true;
}

static bounds_exact_proof_step
bounds_exact_proof_push(bounds_exact_proof_query *query, ixs_node *expr,
                        bounds_exact_proof_kind kind, int64_t modulus) {
  bounds_exact_proof_memo_entry *entry;
  bounds_exact_proof_frame *frame;
  if (!expr || (kind == BOUNDS_EXACT_PROOF_DIVISIBLE && modulus <= 0)) {
    query->invalid = true;
    return BOUNDS_EXACT_PROOF_STEP_INVALID;
  }
  entry = bounds_exact_proof_memo_get(query, expr, kind, modulus, true);
  if (!entry)
    return BOUNDS_EXACT_PROOF_STEP_OOM;
  if (entry->active) {
    query->invalid = true;
    return BOUNDS_EXACT_PROOF_STEP_INVALID;
  }
  if (entry->complete) {
    query->child_result = entry->result;
    return BOUNDS_EXACT_PROOF_STEP_ADVANCED;
  }
  if (query->depth == query->capacity && !bounds_exact_proof_stack_grow(query))
    return BOUNDS_EXACT_PROOF_STEP_OOM;
  frame = &query->frames[query->depth++];
  memset(frame, 0, sizeof(*frame));
  frame->expr = expr;
  frame->kind = kind;
  frame->modulus = modulus;
  frame->stage = BOUNDS_EXACT_PROOF_INITIAL;
  entry->active = true;
  return BOUNDS_EXACT_PROOF_STEP_ADVANCED;
}

static bounds_exact_proof_step
bounds_exact_proof_complete(bounds_exact_proof_query *query, bool result) {
  bounds_exact_proof_frame *frame = &query->frames[query->depth - 1u];
  bounds_exact_proof_memo_entry *entry = bounds_exact_proof_memo_get(
      query, frame->expr, frame->kind, frame->modulus, false);
  if (!entry || !entry->active) {
    query->invalid = true;
    return BOUNDS_EXACT_PROOF_STEP_INVALID;
  }
  entry->result = result;
  entry->active = false;
  entry->complete = true;
  query->depth--;
  query->child_result = result;
  return BOUNDS_EXACT_PROOF_STEP_ADVANCED;
}

static bool bounds_exact_proof_rational(ixs_node *node, int64_t *p,
                                        int64_t *q) {
  if (!node || (node->tag != IXS_INT && node->tag != IXS_RAT))
    return false;
  ixs_node_get_rat(node, p, q);
  return *q > 0;
}

static bounds_exact_proof_step
bounds_exact_proof_divisible_after_add(bounds_exact_proof_query *query,
                                       bounds_exact_proof_frame *frame) {
  ixs_bitfacts bits;
  uint64_t mask;
  if (int64_modulus_is_pow2(frame->modulus)) {
    mask = (uint64_t)frame->modulus - 1u;
    if (ixs_bounds_get_bitfacts(query->bounds, frame->expr, &bits) &&
        (bits.known_zero & mask) == mask)
      return bounds_exact_proof_complete(query, true);
    if (query->bounds->oom)
      return BOUNDS_EXACT_PROOF_STEP_OOM;
  }
  return bounds_exact_proof_complete(query, false);
}

static bounds_exact_proof_step
bounds_exact_proof_start_integer_mul(bounds_exact_proof_query *query,
                                     bounds_exact_proof_frame *frame) {
  ixs_node *node = frame->expr;
  int64_t p;
  int64_t q;
  int64_t divisor;
  if (!bounds_exact_proof_rational(node->u.mul.coeff, &p, &q) ||
      (node->u.mul.nfactors != 0 && !node->u.mul.factors)) {
    query->invalid = true;
    return BOUNDS_EXACT_PROOF_STEP_INVALID;
  }
  frame->index = 0;
  if (q == 1) {
    frame->stage = BOUNDS_EXACT_PROOF_INTEGER_MUL_SCAN;
    return BOUNDS_EXACT_PROOF_STEP_ADVANCED;
  }
  divisor = ixs_gcd(p, q);
  if (divisor <= 0 || q % divisor != 0) {
    query->invalid = true;
    return BOUNDS_EXACT_PROOF_STEP_INVALID;
  }
  frame->denominator = q / divisor;
  frame->denominator_cancelled = frame->denominator == 1;
  frame->stage = BOUNDS_EXACT_PROOF_INTEGER_MUL_RATIONAL_SCAN;
  return BOUNDS_EXACT_PROOF_STEP_ADVANCED;
}

static bounds_exact_proof_step
bounds_exact_proof_start_integer_add(bounds_exact_proof_query *query,
                                     bounds_exact_proof_frame *frame) {
  int64_t p;
  int64_t q;
  ixs_node *node = frame->expr;
  if (!bounds_exact_proof_rational(node->u.add.coeff, &p, &q) ||
      (node->u.add.nterms != 0 && !node->u.add.terms)) {
    query->invalid = true;
    return BOUNDS_EXACT_PROOF_STEP_INVALID;
  }
  (void)p;
  if (q != 1)
    return bounds_exact_proof_complete(
        query, bounds_add_known_divisible(query->bounds, node, 1));
  frame->index = 0;
  frame->stage = BOUNDS_EXACT_PROOF_INTEGER_ADD_SCAN;
  return BOUNDS_EXACT_PROOF_STEP_ADVANCED;
}

static bounds_exact_proof_step
bounds_exact_proof_start_integer(bounds_exact_proof_query *query,
                                 bounds_exact_proof_frame *frame) {
  ixs_node *node = frame->expr;
  if (ixs_node_is_integer_valued(node))
    return bounds_exact_proof_complete(query, true);
  switch (node->tag) {
  case IXS_MUL:
    return bounds_exact_proof_start_integer_mul(query, frame);
  case IXS_ADD:
    return bounds_exact_proof_start_integer_add(query, frame);
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
    if (node->u.assoc.nargs < 2 || !node->u.assoc.args) {
      query->invalid = true;
      return BOUNDS_EXACT_PROOF_STEP_INVALID;
    }
    frame->index = 0;
    frame->stage = BOUNDS_EXACT_PROOF_INTEGER_ASSOC_SCAN;
    return BOUNDS_EXACT_PROOF_STEP_ADVANCED;
  case IXS_PIECEWISE:
    if (node->u.pw.ncases == 0 || !node->u.pw.cases) {
      query->invalid = true;
      return BOUNDS_EXACT_PROOF_STEP_INVALID;
    }
    frame->index = 0;
    frame->stage = BOUNDS_EXACT_PROOF_INTEGER_PW_SCAN;
    return BOUNDS_EXACT_PROOF_STEP_ADVANCED;
  case IXS_MOD:
    if (!node->u.binary.lhs || !node->u.binary.rhs) {
      query->invalid = true;
      return BOUNDS_EXACT_PROOF_STEP_INVALID;
    }
    frame->stage = BOUNDS_EXACT_PROOF_INTEGER_MOD_LHS;
    return bounds_exact_proof_push(query, node->u.binary.lhs,
                                   BOUNDS_EXACT_PROOF_INTEGER, 0);
  default:
    return bounds_exact_proof_complete(query, false);
  }
}

static bounds_exact_proof_step
bounds_exact_proof_start_divisible_add(bounds_exact_proof_query *query,
                                       bounds_exact_proof_frame *frame) {
  int64_t p;
  int64_t q;
  ixs_node *node = frame->expr;
  if (!bounds_exact_proof_rational(node->u.add.coeff, &p, &q) ||
      (node->u.add.nterms != 0 && !node->u.add.terms)) {
    query->invalid = true;
    return BOUNDS_EXACT_PROOF_STEP_INVALID;
  }
  if (q != 1) {
    if (bounds_add_known_divisible(query->bounds, node, frame->modulus))
      return bounds_exact_proof_complete(query, true);
    if (query->bounds->oom)
      return BOUNDS_EXACT_PROOF_STEP_OOM;
    return bounds_exact_proof_divisible_after_add(query, frame);
  }
  if (p % frame->modulus != 0)
    return bounds_exact_proof_divisible_after_add(query, frame);
  frame->index = 0;
  frame->stage = BOUNDS_EXACT_PROOF_DIVISIBLE_ADD_SCAN;
  return BOUNDS_EXACT_PROOF_STEP_ADVANCED;
}

static bounds_exact_proof_step
bounds_exact_proof_start_divisible_mul(bounds_exact_proof_query *query,
                                       bounds_exact_proof_frame *frame) {
  ixs_node *node = frame->expr;
  if (!node->u.mul.coeff || node->u.mul.coeff->tag != IXS_INT ||
      (node->u.mul.nfactors != 0 && !node->u.mul.factors)) {
    query->invalid = true;
    return BOUNDS_EXACT_PROOF_STEP_INVALID;
  }
  if (node->u.mul.coeff->u.ival == 0)
    return bounds_exact_proof_complete(query, true);
  frame->index = 0;
  frame->stage = BOUNDS_EXACT_PROOF_DIVISIBLE_MUL_INTEGER_SCAN;
  return BOUNDS_EXACT_PROOF_STEP_ADVANCED;
}

static bounds_exact_proof_step
bounds_exact_proof_start_divisible(bounds_exact_proof_query *query,
                                   bounds_exact_proof_frame *frame) {
  ixs_node *node = frame->expr;
  ixs_bitfacts bits;
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
  if (int64_modulus_is_pow2(frame->modulus)) {
    mask = (uint64_t)frame->modulus - 1u;
    if (ixs_bounds_get_bitfacts(query->bounds, node, &bits) &&
        (bits.known_zero & mask) == mask)
      return bounds_exact_proof_complete(query, true);
    if (query->bounds->oom)
      return BOUNDS_EXACT_PROOF_STEP_OOM;
  }
  switch (node->tag) {
  case IXS_INT:
    return bounds_exact_proof_complete(query,
                                       node->u.ival % frame->modulus == 0);
  case IXS_SYM:
    if (!node->u.name) {
      query->invalid = true;
      return BOUNDS_EXACT_PROOF_STEP_INVALID;
    }
    return bounds_exact_proof_complete(
        query,
        bounds_symbol_divisible(query->bounds, node->u.name, frame->modulus));
  case IXS_MUL:
    if (node->u.mul.coeff && node->u.mul.coeff->tag == IXS_INT)
      return bounds_exact_proof_start_divisible_mul(query, frame);
    return bounds_exact_proof_complete(query, false);
  case IXS_MAX:
  case IXS_MIN:
    if (node->u.assoc.nargs == 0 || !node->u.assoc.args) {
      query->invalid = true;
      return BOUNDS_EXACT_PROOF_STEP_INVALID;
    }
    frame->index = 0;
    frame->stage = BOUNDS_EXACT_PROOF_DIVISIBLE_ASSOC_SCAN;
    return BOUNDS_EXACT_PROOF_STEP_ADVANCED;
  default:
    return bounds_exact_proof_complete(query, false);
  }
}

static bounds_exact_proof_step
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
        query->invalid = true;
      return query->invalid ? BOUNDS_EXACT_PROOF_STEP_INVALID
                            : bounds_exact_proof_complete(query, false);
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
      return BOUNDS_EXACT_PROOF_STEP_ADVANCED;
    }
    known = bounds_known_residue_independent(
        query->bounds, base, (uint64_t)frame->denominator, &residue);
    if (query->bounds->oom)
      return BOUNDS_EXACT_PROOF_STEP_OOM;
    if (known) {
      if (residue == 0)
        frame->denominator_cancelled = true;
      frame->index++;
      frame->stage = BOUNDS_EXACT_PROOF_INTEGER_MUL_RATIONAL_SCAN;
      return BOUNDS_EXACT_PROOF_STEP_ADVANCED;
    }
    frame->stage = BOUNDS_EXACT_PROOF_INTEGER_MUL_RATIONAL_INTEGER;
    return bounds_exact_proof_push(query, base, BOUNDS_EXACT_PROOF_INTEGER, 0);
  }
  if (frame->stage == BOUNDS_EXACT_PROOF_INTEGER_MUL_RATIONAL_INTEGER) {
    if (!query->child_result)
      return bounds_exact_proof_complete(query, false);
    frame->index++;
    frame->stage = BOUNDS_EXACT_PROOF_INTEGER_MUL_RATIONAL_SCAN;
    return BOUNDS_EXACT_PROOF_STEP_ADVANCED;
  }
  if (frame->index == node->u.mul.nfactors)
    return bounds_exact_proof_complete(query, frame->denominator_cancelled);
  if (!node->u.mul.factors[frame->index].base ||
      node->u.mul.factors[frame->index].exp <= 0) {
    if (!node->u.mul.factors[frame->index].base)
      query->invalid = true;
    return query->invalid ? BOUNDS_EXACT_PROOF_STEP_INVALID
                          : bounds_exact_proof_complete(query, false);
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

static bounds_exact_proof_step
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
      query->invalid = true;
      return BOUNDS_EXACT_PROOF_STEP_INVALID;
    }
    if (q == 1) {
      frame->stage = BOUNDS_EXACT_PROOF_INTEGER_ADD_INTEGER;
      return bounds_exact_proof_push(query, term->term,
                                     BOUNDS_EXACT_PROOF_INTEGER, 0);
    }
    divisor = ixs_gcd(p, q);
    if (divisor <= 0 || q % divisor != 0) {
      query->invalid = true;
      return BOUNDS_EXACT_PROOF_STEP_INVALID;
    }
    frame->stage = BOUNDS_EXACT_PROOF_INTEGER_ADD_DIVISIBLE;
    return bounds_exact_proof_push(query, term->term,
                                   BOUNDS_EXACT_PROOF_DIVISIBLE, q / divisor);
  }
}

static bounds_exact_proof_step
bounds_exact_proof_resume_integer_assoc(bounds_exact_proof_query *query,
                                        bounds_exact_proof_frame *frame) {
  ixs_node *node = frame->expr;
  if (frame->index != 0 && !query->child_result)
    return bounds_exact_proof_complete(query, false);
  if (frame->index == node->u.assoc.nargs)
    return bounds_exact_proof_complete(query, true);
  if (!node->u.assoc.args[frame->index]) {
    query->invalid = true;
    return BOUNDS_EXACT_PROOF_STEP_INVALID;
  }
  frame->index++;
  return bounds_exact_proof_push(query, node->u.assoc.args[frame->index - 1u],
                                 BOUNDS_EXACT_PROOF_INTEGER, 0);
}

static bounds_exact_proof_step
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
      query->invalid = true;
      return BOUNDS_EXACT_PROOF_STEP_INVALID;
    }
    if (ixs_node_is_known_false(cond))
      truth = IXS_CHECK_FALSE;
    else if (ixs_node_is_known_true(cond))
      truth = IXS_CHECK_TRUE;
    else if (cond->tag == IXS_CMP)
      truth = ixs_bounds_check(query->bounds, cond);
    if (query->bounds->oom)
      return BOUNDS_EXACT_PROOF_STEP_OOM;
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

static bounds_exact_proof_step
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

static bounds_exact_proof_step
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
      query->invalid = true;
      return BOUNDS_EXACT_PROOF_STEP_INVALID;
    }
    if (q != 1) {
      if (bounds_add_known_divisible(query->bounds, node, frame->modulus))
        return bounds_exact_proof_complete(query, true);
      if (query->bounds->oom)
        return BOUNDS_EXACT_PROOF_STEP_OOM;
      return bounds_exact_proof_divisible_after_add(query, frame);
    }
    divisor = ixs_gcd(p, frame->modulus);
    if (divisor <= 0 || frame->modulus % divisor != 0) {
      query->invalid = true;
      return BOUNDS_EXACT_PROOF_STEP_INVALID;
    }
    frame->stage = BOUNDS_EXACT_PROOF_DIVISIBLE_ADD_CHILD;
    return bounds_exact_proof_push(query, term->term,
                                   BOUNDS_EXACT_PROOF_DIVISIBLE,
                                   frame->modulus / divisor);
  }
}

static bounds_exact_proof_step
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
          query->invalid = true;
        return query->invalid ? BOUNDS_EXACT_PROOF_STEP_INVALID
                              : bounds_exact_proof_complete(query, false);
      }
      frame->index++;
      return bounds_exact_proof_push(query, factor->base,
                                     BOUNDS_EXACT_PROOF_INTEGER, 0);
    }
    divisor = ixs_gcd(node->u.mul.coeff->u.ival, frame->modulus);
    if (divisor <= 0 || frame->modulus % divisor != 0) {
      query->invalid = true;
      return BOUNDS_EXACT_PROOF_STEP_INVALID;
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

static bounds_exact_proof_step
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
    query->invalid = true;
    return BOUNDS_EXACT_PROOF_STEP_INVALID;
  }
  frame->index++;
  return bounds_exact_proof_push(query, node->u.assoc.args[frame->index - 1u],
                                 BOUNDS_EXACT_PROOF_DIVISIBLE, frame->modulus);
}

static bounds_exact_proof_step
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
  query->invalid = true;
  return BOUNDS_EXACT_PROOF_STEP_INVALID;
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
  bounds_exact_proof_step step;
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
  query.frames = query.inline_frames;
  query.depth = 0;
  query.capacity = sizeof(query.inline_frames) / sizeof(query.inline_frames[0]);
  query.memo.entries = query.inline_memo;
  query.memo.count = 0;
  query.memo.capacity =
      sizeof(query.inline_memo) / sizeof(query.inline_memo[0]);
  query.child_result = false;
  query.invalid = false;
  memset(query.inline_memo, 0, sizeof(query.inline_memo));
  step = bounds_exact_proof_push(&query, expr, kind, modulus);
  while (step == BOUNDS_EXACT_PROOF_STEP_ADVANCED && query.depth != 0) {
    bounds_exact_proof_frame *frame = &query.frames[query.depth - 1u];
    if (frame->stage == BOUNDS_EXACT_PROOF_INITIAL) {
      step = frame->kind == BOUNDS_EXACT_PROOF_INTEGER
                 ? bounds_exact_proof_start_integer(&query, frame)
                 : bounds_exact_proof_start_divisible(&query, frame);
    } else {
      step = bounds_exact_proof_resume(&query, frame);
    }
  }
  if (step == BOUNDS_EXACT_PROOF_STEP_OOM || b->oom) {
    b->oom = true;
    bounds_query_note_transport(b->query_state, BOUNDS_QUERY_OUTCOME_OOM);
  } else if (step == BOUNDS_EXACT_PROOF_STEP_INVALID || query.invalid) {
    bounds_query_note_invalid(b->query_state);
  } else if (query.depth == 0) {
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

static bool bounds_interval_point_rational(ixs_interval iv, int64_t *p,
                                           int64_t *q) {
  if (!iv.valid || iv.lo_inf || iv.hi_inf ||
      ixs_rat_cmp(iv.lo_p, iv.lo_q, iv.hi_p, iv.hi_q) != 0)
    return false;
  if (p)
    *p = iv.lo_p;
  if (q)
    *q = iv.lo_q;
  return true;
}

static ixs_check_result
bounds_check_integer_valued_without_equality(ixs_bounds *b, ixs_node *expr) {
  ixs_interval iv;
  int64_t p;
  int64_t q;
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
  if (b->oom || !bounds_interval_point_rational(iv, &p, &q))
    return IXS_CHECK_UNKNOWN;
  (void)p;
  return q == 1 ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
}

static ixs_check_result bounds_project_equality_integer(ixs_bounds *b,
                                                        ixs_node *expr) {
  bounds_equality_walk walk;
  bounds_equality_walk_status status;
  bounds_equality_projection_cache_entry *cached;
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  size_t endpoint_index;
  size_t limit_blocks = b->query_state ? b->query_state->limit_blocks : 0u;
  size_t i;

  if (!bounds_find_equality_endpoint(b, expr, &endpoint_index))
    return bounds_check_integer_valued_without_equality(b, expr);
  cached = bounds_equality_projection_cache_get(b, endpoint_index, false);
  if (cached && cached->integer_complete)
    return cached->integer;
  status = bounds_collect_equality_component(b, expr, &walk, true);
  if (status == BOUNDS_EQUALITY_WALK_NONE)
    return bounds_check_integer_valued_without_equality(b, expr);
  if (status != BOUNDS_EQUALITY_WALK_VALID) {
    if (status == BOUNDS_EQUALITY_WALK_INVALID)
      bounds_query_note_invalid(b->query_state);
    bounds_equality_walk_destroy(b, &walk);
    return IXS_CHECK_UNKNOWN;
  }
  if (!bounds_publish_defined_equality_component(b, &walk)) {
    bounds_equality_walk_destroy(b, &walk);
    return IXS_CHECK_UNKNOWN;
  }
  for (i = 0; i < walk.count; i++) {
    ixs_check_result current =
        bounds_check_integer_valued_without_equality(b, walk.entries[i].node);
    if (bounds_query_is_tracking(b))
      bounds_query_counter_increment(
          &b->query_state->equality_intrinsic_evaluations);
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
  if (bounds_query_limited_since(b, limit_blocks)) {
    result = IXS_CHECK_UNKNOWN;
  } else if (!b->oom) {
    for (i = 0; i < walk.count; i++) {
      bounds_equality_projection_cache_entry *entry =
          bounds_equality_projection_cache_get(
              b, walk.entries[i].endpoint_index, true);
      if (!entry) {
        assert(!bounds_query_is_tracking(b));
        continue;
      }
      entry->integer = result;
      entry->integer_complete = true;
    }
  }
  bounds_equality_walk_destroy(b, &walk);
  if (b->oom)
    return IXS_CHECK_UNKNOWN;
  cached = bounds_equality_projection_cache_get(b, endpoint_index, false);
  return cached && cached->integer_complete ? cached->integer : result;
}

IXS_STATIC ixs_check_result ixs_bounds_check_integer_valued(ixs_bounds *b,
                                                            ixs_node *expr) {
  if (!b || !expr || b->oom || ixs_bounds_has_empty(b))
    return IXS_CHECK_UNKNOWN;
  if (b->equality_disabled_depth != 0 || !b->nequalities)
    return bounds_check_integer_valued_without_equality(b, expr);
  return bounds_project_equality_integer(b, expr);
}

static bool bounds_int64_divisible_by_u64(int64_t value, uint64_t modulus) {
  return bounds_int64_magnitude(value) % modulus == 0;
}

static uint64_t bounds_normalize_residue(int64_t value, uint64_t modulus) {
  uint64_t magnitude;
  uint64_t remainder;
  if (value >= 0)
    return (uint64_t)value % modulus;
  magnitude = bounds_int64_magnitude(value);
  remainder = magnitude % modulus;
  return remainder == 0 ? 0 : modulus - remainder;
}

static uint64_t bounds_u64_gcd(uint64_t a, uint64_t b) {
  while (b != 0) {
    uint64_t next = a % b;
    a = b;
    b = next;
  }
  return a;
}

static uint64_t bounds_add_mod(uint64_t a, uint64_t b, uint64_t modulus) {
  return (a + b) % modulus;
}

/* modulus is at most 2^63, so doubling two normalized operands cannot
 * overflow uint64_t.  This keeps modular multiplication portable C99. */
static uint64_t bounds_mul_mod(uint64_t a, uint64_t b, uint64_t modulus) {
  uint64_t result = 0;
  a %= modulus;
  while (b != 0) {
    if ((b & 1u) != 0)
      result = bounds_add_mod(result, a, modulus);
    b >>= 1;
    if (b != 0)
      a = bounds_add_mod(a, a, modulus);
  }
  return result;
}

static uint64_t bounds_sub_mod(uint64_t a, uint64_t b, uint64_t modulus) {
  a %= modulus;
  b %= modulus;
  return a >= b ? a - b : modulus - (b - a);
}

/* Extended Euclid with coefficients kept as residues.  This avoids signed
 * coefficient overflow while retaining portable C99 arithmetic. */
static bool bounds_mod_inverse(uint64_t value, uint64_t modulus,
                               uint64_t *inverse) {
  uint64_t r, new_r, t, new_t;
  if (!inverse || modulus <= 1u)
    return false;
  r = modulus;
  new_r = value % modulus;
  t = 0;
  new_t = 1u;
  while (new_r != 0) {
    uint64_t quotient = r / new_r;
    uint64_t next_r = r % new_r;
    uint64_t product = bounds_mul_mod(quotient, new_t, modulus);
    uint64_t next_t = bounds_sub_mod(t, product, modulus);
    r = new_r;
    new_r = next_r;
    t = new_t;
    new_t = next_t;
  }
  if (r != 1u)
    return false;
  *inverse = t;
  return true;
}

static uint64_t bounds_pow_mod(uint64_t base, int32_t exponent,
                               uint64_t modulus) {
  uint64_t result = 1u % modulus;
  while (exponent > 0) {
    if ((exponent & 1) != 0)
      result = bounds_mul_mod(result, base, modulus);
    exponent >>= 1;
    if (exponent != 0)
      base = bounds_mul_mod(base, base, modulus);
  }
  return result;
}

static bool bounds_known_residue(ixs_bounds *b, ixs_node *expr,
                                 uint64_t modulus, uint64_t *out);

typedef struct {
  ixs_node *representative;
  uint64_t coefficient;
} bounds_residue_group;

static size_t bounds_residue_group_hash(const ixs_node *node) {
  uint64_t mixed = (uint64_t)((uintptr_t)node >> 3);
  mixed ^= mixed >> 33;
  mixed *= UINT64_C(0xff51afd7ed558ccd);
  mixed ^= mixed >> 33;
  return (size_t)mixed;
}

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

static bool bounds_add_denominator_lcm(ixs_node *expr, uint64_t *out) {
  uint64_t denominator = 1u;
  uint32_t i;
  int64_t p;
  int64_t q;

  ixs_node_get_rat(expr->u.add.coeff, &p, &q);
  (void)p;
  for (i = 0;; i++) {
    uint64_t factor;
    uint64_t divisor;
    if (q <= 0)
      return false;
    divisor = (uint64_t)q;
    factor = divisor / bounds_u64_gcd(denominator, divisor);
    if (factor != 0 && denominator > (uint64_t)INT64_MAX / factor)
      return false;
    denominator *= factor;
    if (i == expr->u.add.nterms)
      break;
    ixs_node_get_rat(expr->u.add.terms[i].coeff, &p, &q);
  }
  *out = denominator;
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
    coefficient = bounds_mul_mod(bounds_normalize_residue(p, modulus),
                                 (scale / (uint64_t)q) % modulus, modulus);
    if (coefficient == 0)
      continue;
    representative =
        bounds_residue_representative(b, term, modulus, proof_independent);
    group = bounds_residue_group_hash(representative) & (group_capacity - 1u);
    while (groups[group].representative &&
           groups[group].representative != representative)
      group = (group + 1u) & (group_capacity - 1u);
    if (!groups[group].representative) {
      groups[group].representative = representative;
      (*ngroups)++;
    }
    groups[group].coefficient =
        bounds_add_mod(groups[group].coefficient, coefficient, modulus);
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
    reduced = modulus / bounds_u64_gcd(coefficient, modulus);
    if (reduced == 1u)
      continue;
    if (!(proof_independent
              ? bounds_known_residue_independent(b, groups[i].representative,
                                                 reduced, &residue)
              : bounds_known_residue(b, groups[i].representative, reduced,
                                     &residue)))
      return false;
    *result = bounds_add_mod(
        *result, bounds_mul_mod(coefficient, residue, modulus), modulus);
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
  result = bounds_mul_mod(bounds_normalize_residue(p, modulus),
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

static bool bounds_add_known_divisible(ixs_bounds *b, ixs_node *expr,
                                       int64_t modulus) {
  uint64_t denominator;
  uint64_t scaled_modulus;
  uint64_t residue;
  uint32_t i;
  int64_t p;
  int64_t q;
  bool has_rational_coefficient;

  if (!b || !expr || expr->tag != IXS_ADD || modulus <= 0)
    return false;
  ixs_node_get_rat(expr->u.add.coeff, &p, &q);
  (void)p;
  has_rational_coefficient = q != 1;
  for (i = 0; !has_rational_coefficient && i < expr->u.add.nterms; i++) {
    ixs_node_get_rat(expr->u.add.terms[i].coeff, &p, &q);
    has_rational_coefficient = q != 1;
  }
  if (!has_rational_coefficient)
    return false;
  if (!bounds_add_denominator_lcm(expr, &denominator) ||
      (uint64_t)modulus > (uint64_t)INT64_MAX / denominator)
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
      !ixs_bounds_get_modrem(b, expr->u.name, &stored_modulus,
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
  ixs_bounds *bounds;
  ixs_node *expr;
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
  bounds_residue_frame *frames;
  size_t depth;
  size_t capacity;
  uint64_t child_residue;
  bool child_success;
  bool proof_independent;
} bounds_residue_query;

static bool bounds_residue_push(bounds_residue_query *query, ixs_bounds *b,
                                ixs_node *expr, uint64_t modulus) {
  bounds_residue_frame *grown;
  size_t capacity;
  size_t old_bytes;
  size_t new_bytes;
  if (!b || !expr || modulus == 0 || b->oom)
    return false;
  if (query->depth == query->capacity) {
    capacity = query->capacity ? query->capacity * 2u : 16u;
    if (capacity < query->capacity ||
        capacity > SIZE_MAX / sizeof(*query->frames)) {
      query->root->oom = true;
      return false;
    }
    old_bytes = query->capacity * sizeof(*query->frames);
    new_bytes = capacity * sizeof(*query->frames);
    grown = ixs_arena_grow(query->root->scratch, query->frames, old_bytes,
                           new_bytes, sizeof(void *));
    if (!grown) {
      query->root->oom = true;
      return false;
    }
    query->frames = grown;
    query->capacity = capacity;
  }
  memset(&query->frames[query->depth], 0, sizeof(*query->frames));
  query->frames[query->depth].bounds = b;
  query->frames[query->depth].expr = expr;
  query->frames[query->depth].modulus = modulus;
  query->frames[query->depth].stage = BOUNDS_RESIDUE_INITIAL;
  query->depth++;
  return true;
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

static void bounds_residue_complete(bounds_residue_query *query, bool success,
                                    uint64_t residue) {
  bounds_residue_frame *frame = &query->frames[query->depth - 1u];
  bounds_residue_destroy_fork(query, frame, true);
  bounds_residue_destroy_fork(query, frame, false);
  if (frame->tracked) {
    bounds_query_cache_entry *entry =
        bounds_query_finish(&frame->scope, success);
    if (entry && entry->outcome == BOUNDS_QUERY_OUTCOME_VALUE)
      entry->result.residue = residue;
    else
      success = false;
  }
  query->depth--;
  query->child_success = success;
  query->child_residue = residue;
}

static void bounds_residue_unwind(bounds_residue_query *query) {
  while (query->depth != 0)
    bounds_residue_complete(query, false, 0);
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
      bounds_mul_mod(bounds_normalize_residue(p, frame->modulus),
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
        bounds_mul_mod(bounds_normalize_residue(p, frame->modulus),
                       (scale / (uint64_t)q) % frame->modulus, frame->modulus);
    if (coefficient == 0)
      continue;
    representative = bounds_residue_representative(b, term, frame->modulus,
                                                   query->proof_independent);
    group = bounds_residue_group_hash(representative) & (capacity - 1u);
    while (frame->groups[group].representative &&
           frame->groups[group].representative != representative)
      group = (group + 1u) & (capacity - 1u);
    frame->groups[group].representative = representative;
    frame->groups[group].coefficient = bounds_add_mod(
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

typedef enum {
  BOUNDS_RESIDUE_STEP_ADVANCED,
  BOUNDS_RESIDUE_STEP_READY,
  BOUNDS_RESIDUE_STEP_OOM
} bounds_residue_step;

static bounds_residue_step
bounds_residue_track_frame(bounds_residue_query *query,
                           bounds_residue_frame *frame) {
  bounds_query_cache_entry *cached = NULL;
  bounds_query_enter_result enter;
  if (!bounds_query_should_track(frame->bounds, frame->expr))
    return BOUNDS_RESIDUE_STEP_READY;
  enter = bounds_query_begin(frame->bounds, BOUNDS_QUERY_RESIDUE, frame->expr,
                             frame->modulus, &frame->scope, &cached);
  if (enter == BOUNDS_QUERY_ENTER_CACHED) {
    bounds_residue_complete(query, cached->success,
                            cached->success ? cached->result.residue : 0);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  if (enter != BOUNDS_QUERY_ENTER_STARTED) {
    bounds_residue_complete(query, false, 0);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  frame->tracked = true;
  return BOUNDS_RESIDUE_STEP_READY;
}

static bool bounds_residue_structural_first(const ixs_node *node) {
  return (node->tag == IXS_ADD || node->tag == IXS_MOD ||
          node->tag == IXS_PIECEWISE) &&
         ixs_node_is_integer_valued(node) && ixs_node_is_known_total(node);
}

static bounds_residue_step
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
    bounds_residue_complete(query, false, 0);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  if (node->tag == IXS_ADD &&
      bounds_exact_unit_difference_value(current, node, &exact)) {
    bounds_residue_complete(query, true,
                            bounds_normalize_residue(exact, frame->modulus));
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  if (ixs_node_is_integer_valued(node) && frame->modulus == 1u) {
    bounds_residue_complete(query, true, 0);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  iv = bounds_get_expr_overrides(current, node);
  if (node->tag == IXS_SYM)
    var = find_var(current, node->u.name);
  if (var)
    iv = iv.valid ? iv_intersect(iv, var->iv) : var->iv;
  if (ixs_interval_is_point_int(iv, &exact)) {
    bounds_residue_complete(query, true,
                            bounds_normalize_residue(exact, frame->modulus));
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  if (ixs_node_is_integer_valued(node) && uint64_is_pow2(frame->modulus) &&
      bounds_get_bitfacts_tracked(current, node, &bits)) {
    uint64_t mask = frame->modulus - 1u;
    if (((bits.known_zero | bits.known_one) & mask) == mask) {
      bounds_residue_complete(query, true, bits.known_one & mask);
      return BOUNDS_RESIDUE_STEP_ADVANCED;
    }
  }
  if (current->oom) {
    query->root->oom = true;
    return BOUNDS_RESIDUE_STEP_OOM;
  }
  return BOUNDS_RESIDUE_STEP_READY;
}

static bounds_residue_step
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
      bounds_exact_unit_difference_value(current, node, &exact)) {
    bounds_residue_complete(query, true,
                            bounds_normalize_residue(exact, frame->modulus));
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  if (bounds_residue_structural_first(node))
    return BOUNDS_RESIDUE_STEP_READY;
  if (ixs_bounds_check_integer_valued(current, node) != IXS_CHECK_TRUE ||
      !ixs_node_is_known_total(node)) {
    if (current->oom)
      query->root->oom = true;
    if (query->root->oom)
      return BOUNDS_RESIDUE_STEP_OOM;
    bounds_residue_complete(query, false, 0);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  if (frame->modulus == 1u) {
    bounds_residue_complete(query, true, 0);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  iv = bounds_get_tracked(current, node);
  if (current->oom) {
    query->root->oom = true;
    return BOUNDS_RESIDUE_STEP_OOM;
  }
  if (ixs_interval_is_point_int(iv, &exact)) {
    bounds_residue_complete(query, true,
                            bounds_normalize_residue(exact, frame->modulus));
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  if (uint64_is_pow2(frame->modulus) &&
      bounds_get_bitfacts_tracked(current, node, &bits)) {
    uint64_t mask = frame->modulus - 1u;
    if (((bits.known_zero | bits.known_one) & mask) == mask) {
      bounds_residue_complete(query, true, bits.known_one & mask);
      return BOUNDS_RESIDUE_STEP_ADVANCED;
    }
  }
  if (current->oom) {
    query->root->oom = true;
    return BOUNDS_RESIDUE_STEP_OOM;
  }
  return BOUNDS_RESIDUE_STEP_READY;
}

static bounds_residue_step
bounds_residue_direct_fact(bounds_residue_query *query,
                           bounds_residue_frame *frame) {
  if (query->proof_independent)
    return bounds_residue_direct_independent(query, frame);
  return bounds_residue_direct_tracked(query, frame);
}

static bounds_residue_step
bounds_residue_start_mul(bounds_residue_query *query,
                         bounds_residue_frame *frame) {
  ixs_node *node = frame->expr;
  int64_t p;
  int64_t q;
  ixs_node_get_rat(node->u.mul.coeff, &p, &q);
  if (q != 1) {
    bounds_residue_complete(query, false, 0);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  frame->coefficient = bounds_normalize_residue(p, frame->modulus);
  frame->reduced_modulus =
      frame->modulus / bounds_u64_gcd(frame->coefficient, frame->modulus);
  if (frame->reduced_modulus == 1u) {
    bounds_residue_complete(query, true, 0);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  frame->result = 1u % frame->reduced_modulus;
  frame->index = 0;
  frame->stage = BOUNDS_RESIDUE_MUL_SCAN;
  return BOUNDS_RESIDUE_STEP_ADVANCED;
}

static bounds_residue_step
bounds_residue_start_assoc(bounds_residue_query *query,
                           bounds_residue_frame *frame, bool bitwise) {
  ixs_node *node = frame->expr;
  if ((bitwise && !uint64_is_pow2(frame->modulus)) ||
      node->u.assoc.nargs == 0 || !node->u.assoc.args) {
    bounds_residue_complete(query, false, 0);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  frame->index = 0;
  frame->have_result = false;
  frame->stage = BOUNDS_RESIDUE_ASSOC_SCAN;
  return BOUNDS_RESIDUE_STEP_ADVANCED;
}

static bounds_residue_step
bounds_residue_start_frame(bounds_residue_query *query,
                           bounds_residue_frame *frame) {
  ixs_node *node = frame->expr;
  switch (node->tag) {
  case IXS_INT:
    bounds_residue_complete(
        query, true, bounds_normalize_residue(node->u.ival, frame->modulus));
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  case IXS_RAT:
    bounds_residue_complete(
        query, node->u.rat.q == 1,
        node->u.rat.q == 1
            ? bounds_normalize_residue(node->u.rat.p, frame->modulus)
            : 0);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  case IXS_SYM: {
    uint64_t residue = 0;
    bool success = bounds_known_symbol_residue(frame->bounds, node,
                                               frame->modulus, &residue);
    bounds_residue_complete(query, success, residue);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  case IXS_ADD:
    if (!bounds_residue_prepare_add(query, frame, 1u)) {
      if (query->root->oom)
        return BOUNDS_RESIDUE_STEP_OOM;
      bounds_residue_complete(query, false, 0);
    }
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  case IXS_MUL:
    return bounds_residue_start_mul(query, frame);
  case IXS_MOD:
    if (node->u.binary.rhs->tag != IXS_INT || node->u.binary.rhs->u.ival <= 0 ||
        (uint64_t)node->u.binary.rhs->u.ival % frame->modulus != 0) {
      bounds_residue_complete(query, false, 0);
      return BOUNDS_RESIDUE_STEP_ADVANCED;
    }
    frame->stage = BOUNDS_RESIDUE_MOD_CHILD;
    return bounds_residue_push(query, frame->bounds, node->u.binary.lhs,
                               frame->modulus)
               ? BOUNDS_RESIDUE_STEP_ADVANCED
               : BOUNDS_RESIDUE_STEP_OOM;
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
    return bounds_residue_start_assoc(query, frame, true);
  case IXS_MAX:
  case IXS_MIN:
    return bounds_residue_start_assoc(query, frame, false);
  case IXS_PIECEWISE:
    if (!frame->bounds->ctx || node->u.pw.ncases == 0 || !node->u.pw.cases) {
      bounds_residue_complete(query, false, 0);
      return BOUNDS_RESIDUE_STEP_ADVANCED;
    }
    frame->index = 0;
    frame->have_result = false;
    frame->stage = BOUNDS_RESIDUE_PW_TOTAL_SCAN;
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  default:
    bounds_residue_complete(query, false, 0);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
}

static bounds_residue_step
bounds_residue_resume_add(bounds_residue_query *query,
                          bounds_residue_frame *frame) {
  if (frame->stage == BOUNDS_RESIDUE_ADD_CHILD) {
    if (!query->child_success) {
      bounds_residue_complete(query, false, 0);
      return BOUNDS_RESIDUE_STEP_ADVANCED;
    }
    frame->result =
        bounds_add_mod(frame->result,
                       bounds_mul_mod(frame->coefficient, query->child_residue,
                                      frame->modulus),
                       frame->modulus);
    frame->stage = BOUNDS_RESIDUE_ADD_SCAN;
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  while (frame->group_index < frame->group_capacity) {
    bounds_residue_group *group = &frame->groups[frame->group_index++];
    if (!group->representative || group->coefficient == 0)
      continue;
    frame->coefficient = group->coefficient;
    frame->reduced_modulus =
        frame->modulus / bounds_u64_gcd(frame->coefficient, frame->modulus);
    if (frame->reduced_modulus == 1u)
      continue;
    frame->stage = BOUNDS_RESIDUE_ADD_CHILD;
    return bounds_residue_push(query, frame->bounds, group->representative,
                               frame->reduced_modulus)
               ? BOUNDS_RESIDUE_STEP_ADVANCED
               : BOUNDS_RESIDUE_STEP_OOM;
  }
  bounds_residue_complete(query, true, frame->result);
  return BOUNDS_RESIDUE_STEP_ADVANCED;
}

static bounds_residue_step
bounds_residue_resume_mul(bounds_residue_query *query,
                          bounds_residue_frame *frame) {
  ixs_node *node = frame->expr;
  if (frame->stage == BOUNDS_RESIDUE_MUL_CHILD) {
    if (!query->child_success) {
      bounds_residue_complete(query, false, 0);
      return BOUNDS_RESIDUE_STEP_ADVANCED;
    }
    frame->result =
        bounds_mul_mod(frame->result,
                       bounds_pow_mod(query->child_residue,
                                      node->u.mul.factors[frame->index].exp,
                                      frame->reduced_modulus),
                       frame->reduced_modulus);
    frame->index++;
    frame->stage = BOUNDS_RESIDUE_MUL_SCAN;
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  /* Ordinary residue queries have already proved every factor integral and
   * may stop after a zero product.  Independent exact-proof queries have no
   * such callback: visit the remaining factors so a divisible integer factor
   * cannot hide a rational one. */
  if ((!query->proof_independent && frame->result == 0) ||
      frame->index == node->u.mul.nfactors) {
    bounds_residue_complete(
        query, true,
        bounds_mul_mod(frame->coefficient, frame->result, frame->modulus));
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  if (node->u.mul.factors[frame->index].exp < 0) {
    bounds_residue_complete(query, false, 0);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  frame->stage = BOUNDS_RESIDUE_MUL_CHILD;
  return bounds_residue_push(query, frame->bounds,
                             node->u.mul.factors[frame->index].base,
                             frame->reduced_modulus)
             ? BOUNDS_RESIDUE_STEP_ADVANCED
             : BOUNDS_RESIDUE_STEP_OOM;
}

static bounds_residue_step
bounds_residue_resume_assoc(bounds_residue_query *query,
                            bounds_residue_frame *frame) {
  ixs_node *node = frame->expr;
  if (frame->stage == BOUNDS_RESIDUE_ASSOC_SCAN) {
    if (frame->index == node->u.assoc.nargs) {
      uint64_t result = frame->result;
      if (node->tag == IXS_XOR || node->tag == IXS_AND || node->tag == IXS_OR)
        result &= frame->modulus - 1u;
      bounds_residue_complete(query, frame->have_result, result);
      return BOUNDS_RESIDUE_STEP_ADVANCED;
    }
    frame->stage = BOUNDS_RESIDUE_ASSOC_CHILD;
    return bounds_residue_push(query, frame->bounds,
                               node->u.assoc.args[frame->index], frame->modulus)
               ? BOUNDS_RESIDUE_STEP_ADVANCED
               : BOUNDS_RESIDUE_STEP_OOM;
  }
  if (!query->child_success) {
    bounds_residue_complete(query, false, 0);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
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
    bounds_residue_complete(query, false, 0);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  frame->index++;
  frame->stage = BOUNDS_RESIDUE_ASSOC_SCAN;
  return BOUNDS_RESIDUE_STEP_ADVANCED;
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

static bounds_residue_step
bounds_residue_resume_pw_total(bounds_residue_query *query,
                               bounds_residue_frame *frame) {
  ixs_node *node = frame->expr;
  if (frame->stage == BOUNDS_RESIDUE_PW_TOTAL_SCAN) {
    if (frame->index == node->u.pw.ncases) {
      bounds_residue_complete(query, frame->have_result, frame->result);
      return BOUNDS_RESIDUE_STEP_ADVANCED;
    }
    frame->stage = BOUNDS_RESIDUE_PW_TOTAL_CHILD;
    return bounds_residue_push(query, frame->bounds,
                               node->u.pw.cases[frame->index].value,
                               frame->modulus)
               ? BOUNDS_RESIDUE_STEP_ADVANCED
               : BOUNDS_RESIDUE_STEP_OOM;
  }
  if (!query->child_success ||
      !bounds_residue_merge(query->child_residue, &frame->result,
                            &frame->have_result)) {
    if (query->root->oom)
      return BOUNDS_RESIDUE_STEP_OOM;
    if (query->proof_independent) {
      bounds_residue_complete(query, false, 0);
      return BOUNDS_RESIDUE_STEP_ADVANCED;
    }
    if (!bounds_residue_start_reachable(query, frame)) {
      if (query->root->oom)
        return BOUNDS_RESIDUE_STEP_OOM;
      bounds_residue_complete(query, false, 0);
    }
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  frame->index++;
  frame->stage = BOUNDS_RESIDUE_PW_TOTAL_SCAN;
  return BOUNDS_RESIDUE_STEP_ADVANCED;
}

static bounds_residue_step
bounds_residue_resume_pw_reach_scan(bounds_residue_query *query,
                                    bounds_residue_frame *frame) {
  ixs_node *node = frame->expr;
  ixs_node *cond;
  ixs_node *value;
  ixs_check_result truth;
  if (frame->remaining->oom) {
    query->root->oom = true;
    return BOUNDS_RESIDUE_STEP_OOM;
  }
  if (ixs_bounds_has_empty(frame->remaining)) {
    frame->covered = true;
    bounds_residue_complete(query, frame->have_result, frame->result);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  if (frame->index == node->u.pw.ncases) {
    bounds_residue_complete(query, frame->covered && frame->have_result,
                            frame->result);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  cond = node->u.pw.cases[frame->index].cond;
  value = node->u.pw.cases[frame->index].value;
  if (!cond || !value ||
      ixs_bounds_check_defined(frame->remaining, cond) != IXS_CHECK_TRUE) {
    if (frame->remaining->oom)
      query->root->oom = true;
    if (query->root->oom)
      return BOUNDS_RESIDUE_STEP_OOM;
    bounds_residue_complete(query, false, 0);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  truth = bounds_condition_truth(frame->remaining, cond);
  if (truth == IXS_CHECK_FALSE) {
    frame->index++;
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  if (!bounds_residue_alloc_fork(query, frame, frame->remaining, true))
    return BOUNDS_RESIDUE_STEP_OOM;
  if (!bounds_residue_add_condition(query, frame->active, cond, true)) {
    if (query->root->oom)
      return BOUNDS_RESIDUE_STEP_OOM;
    bounds_residue_complete(query, false, 0);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  if (ixs_bounds_has_empty(frame->active)) {
    bounds_residue_destroy_fork(query, frame, true);
    if (truth == IXS_CHECK_TRUE) {
      frame->covered = true;
      bounds_residue_complete(query, frame->have_result, frame->result);
      return BOUNDS_RESIDUE_STEP_ADVANCED;
    }
    if (!bounds_residue_add_condition(query, frame->remaining, cond, false)) {
      if (query->root->oom)
        return BOUNDS_RESIDUE_STEP_OOM;
      bounds_residue_complete(query, false, 0);
      return BOUNDS_RESIDUE_STEP_ADVANCED;
    }
    frame->index++;
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  if (ixs_bounds_check_defined(frame->active, value) != IXS_CHECK_TRUE) {
    if (frame->active->oom)
      query->root->oom = true;
    if (query->root->oom)
      return BOUNDS_RESIDUE_STEP_OOM;
    bounds_residue_complete(query, false, 0);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  frame->branch_truth = truth;
  frame->stage = BOUNDS_RESIDUE_PW_REACH_CHILD;
  return bounds_residue_push(query, frame->active, value, frame->modulus)
             ? BOUNDS_RESIDUE_STEP_ADVANCED
             : BOUNDS_RESIDUE_STEP_OOM;
}

static bounds_residue_step
bounds_residue_resume_pw_reach_child(bounds_residue_query *query,
                                     bounds_residue_frame *frame) {
  ixs_node *cond = frame->expr->u.pw.cases[frame->index].cond;
  if (!query->child_success ||
      !bounds_residue_merge(query->child_residue, &frame->result,
                            &frame->have_result)) {
    bounds_residue_complete(query, false, 0);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  bounds_residue_destroy_fork(query, frame, true);
  if (frame->branch_truth == IXS_CHECK_TRUE) {
    frame->covered = true;
    bounds_residue_complete(query, true, frame->result);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  if (!bounds_residue_add_condition(query, frame->remaining, cond, false)) {
    if (query->root->oom)
      return BOUNDS_RESIDUE_STEP_OOM;
    bounds_residue_complete(query, false, 0);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  frame->index++;
  frame->stage = BOUNDS_RESIDUE_PW_REACH_SCAN;
  return BOUNDS_RESIDUE_STEP_ADVANCED;
}

static bounds_residue_step
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
    bounds_residue_complete(query, query->child_success,
                            query->child_success ? query->child_residue : 0);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
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
    bounds_residue_complete(query, false, 0);
    return BOUNDS_RESIDUE_STEP_ADVANCED;
  }
  return BOUNDS_RESIDUE_STEP_ADVANCED;
}

static bool bounds_known_residue_mode(ixs_bounds *b, ixs_node *expr,
                                      uint64_t modulus, uint64_t *out,
                                      bool proof_independent) {
  ixs_arena_mark mark;
  bounds_residue_query query;
  if (!b || !expr || !out || modulus == 0 || b->oom)
    return false;

  mark = ixs_arena_save(b->scratch);
  memset(&query, 0, sizeof(query));
  query.root = b;
  query.proof_independent = proof_independent;
  if (!bounds_residue_push(&query, b, expr, modulus))
    goto failed;

  while (query.depth != 0) {
    bounds_residue_frame *frame = &query.frames[query.depth - 1u];
    bounds_residue_step step;

    if (frame->stage == BOUNDS_RESIDUE_INITIAL) {
      step = bounds_residue_track_frame(&query, frame);
      if (step == BOUNDS_RESIDUE_STEP_READY)
        step = bounds_residue_direct_fact(&query, frame);
      if (step == BOUNDS_RESIDUE_STEP_READY)
        step = bounds_residue_start_frame(&query, frame);
    } else {
      step = bounds_residue_resume_frame(&query, frame);
    }
    if (step == BOUNDS_RESIDUE_STEP_OOM)
      goto failed;
  }

  if (query.child_success)
    *out = query.child_residue;
  ixs_arena_restore(b->scratch, mark);
  return query.child_success;

failed:
  bounds_residue_unwind(&query);
  ixs_arena_restore(b->scratch, mark);
  return false;
}

static bool bounds_known_residue(ixs_bounds *b, ixs_node *expr,
                                 uint64_t modulus, uint64_t *out) {
  return bounds_known_residue_mode(b, expr, modulus, out, false);
}

static bool bounds_known_residue_independent(ixs_bounds *b, ixs_node *expr,
                                             uint64_t modulus, uint64_t *out) {
  return bounds_known_residue_mode(b, expr, modulus, out, true);
}

#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
IXS_STATIC bool ixs_bounds_known_residue_probe(ixs_bounds *b, ixs_node *expr,
                                               uint64_t modulus,
                                               uint64_t *residue) {
  return bounds_known_residue(b, expr, modulus, residue);
}
#endif

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

  magnitude = bounds_int64_magnitude(modulus);
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
  magnitude = bounds_int64_magnitude(modulus);
  expected = bounds_normalize_residue(residue, magnitude);
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
    if (!interval_lower_at_least(&arg_iv, 0, 1))
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

  span = value_span_mask((uint64_t)max_hi);
  possible = span;
  required = 0;
  have_bits =
      bounds_get_bitfacts_tracked(b, expr->u.assoc.args[0], &result_bits);
  for (i = 1; have_bits && i < expr->u.assoc.nargs; i++) {
    if (!bounds_get_bitfacts_tracked(b, expr->u.assoc.args[i], &arg_bits)) {
      have_bits = false;
      break;
    }
    bitfacts_apply_xor(&next_bits, &result_bits, &arg_bits);
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

static ixs_interval bounds_get_proportional_range(ixs_bounds *b,
                                                  ixs_node *expr) {
  ixs_node *primitive, *canonical;
  ixs_interval primitive_iv;
  int64_t scale_p, scale_q, offset_p, offset_q;
  if (!bounds_get_proportional_primitive(b, expr, &primitive, &scale_p,
                                         &scale_q, &offset_p, &offset_q) ||
      (primitive == expr && scale_p == 1 && scale_q == 1 && offset_p == 0))
    return ixs_interval_unknown();
  primitive_iv = bounds_get_expr_overrides(b, primitive);
  canonical = bounds_canonical_expr(b, primitive);
  if (canonical && canonical != primitive)
    primitive_iv =
        iv_intersect(primitive_iv, bounds_get_expr_overrides(b, canonical));
  if (!primitive_iv.valid)
    return ixs_interval_unknown();
  return bounds_apply_affine(primitive_iv, scale_p, scale_q, offset_p,
                             offset_q);
}

typedef enum {
  BOUNDS_TRUNCATING_RANGE_NO_MATCH,
  BOUNDS_TRUNCATING_RANGE_MATCH,
  BOUNDS_TRUNCATING_RANGE_LIMITED,
  BOUNDS_TRUNCATING_RANGE_INVALID,
  BOUNDS_TRUNCATING_RANGE_OOM
} bounds_truncating_range_status;

static bounds_truncating_range_status bounds_get_truncating_remainder_range(
    ixs_bounds *b, ixs_node *expr, bool expression_defined, ixs_interval *out);

static void
bounds_note_truncating_range_status(ixs_bounds *b,
                                    bounds_truncating_range_status status) {
  if (status == BOUNDS_TRUNCATING_RANGE_OOM)
    b->oom = true;
  else if (status == BOUNDS_TRUNCATING_RANGE_INVALID)
    bounds_query_note_invalid(b->query_state);
  else if (status == BOUNDS_TRUNCATING_RANGE_LIMITED)
    bounds_query_note_limit(b->query_state);
}

static inline ixs_interval bounds_get_add(ixs_bounds *b, ixs_node *expr) {
  uint32_t i;
  ixs_interval result = ixs_bounds_get(b, expr->u.add.coeff);
  for (i = 0; i < expr->u.add.nterms; i++) {
    int64_t cp, cq;
    ixs_interval ti = ixs_bounds_get(b, expr->u.add.terms[i].term);
    ixs_interval scaled;
    ixs_node_get_rat(expr->u.add.terms[i].coeff, &cp, &cq);
    scaled = iv_mul_const(ti, cp, cq);
    result = iv_add(result, scaled);
  }
  if (!b->oom && b->nexprs != 0)
    result = iv_intersect(result, bounds_get_proportional_range(b, expr));
  if (!b->oom && b->nexprs != 0 && !ixs_node_is_zero(expr->u.add.coeff)) {
    ixs_node *base = bounds_expr_without_add_const(b, expr);
    if (base && base != expr) {
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
      !ixs_bounds_get_modrem(b, symbol->u.name, &known_modulus,
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
  residue = bounds_normalize_residue(first, (uint64_t)modulus);
  g = bounds_u64_gcd(step, (uint64_t)modulus);
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
  common = bounds_u64_gcd(stride, (uint64_t)modulus);
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
  if (interval_exact_int(&pi, &exact_lhs))
    return ixs_interval_exact(
        (int64_t)bounds_normalize_residue(exact_lhs, (uint64_t)modulus), 1);
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

  if (interval_exact_int(&mi, &exact_m) && exact_m > 0)
    return bounds_get_positive_mod(b, lhs, exact_m);

  if (ixs_node_is_integer_valued(lhs) && ixs_node_is_integer_valued(m) &&
      interval_lower_at_least(&mi, 1, 1)) {
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
    if (interval_lower_at_least(&li, 0, 1) && !li.hi_inf &&
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
            (bounds_is_known_nonzero(b, expr->u.assoc.args[i]) ||
             bounds_is_known_nonzero(b, expr->u.assoc.args[j])) &&
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

static ixs_node *bounds_condition_assumption(ixs_bounds *b, ixs_node *cond,
                                             bool value,
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

static ixs_check_result bounds_condition_truth(ixs_bounds *b, ixs_node *cond) {
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
    if (!bounds_query_take_range_visit(b, expr)) {
      failed = true;
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
  bounds_destroy_if_initialized(&remaining, remaining_ready);
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

static ixs_interval bounds_get_intrinsic(ixs_bounds *b, ixs_node *expr) {
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
    var = find_var(b, expr->u.name);
    iv = var ? var->iv : ixs_interval_unknown();
  } else {
    iv = bounds_get_propagated(b, expr);
  }
  if (b->nexprs && expr) {
    iv = iv_intersect(iv, bounds_get_expr_overrides(b, expr));
    canon = bounds_expr_may_need_canonical_alias(expr)
                ? bounds_canonical_expr(b, expr)
                : expr;
    if (canon && canon != expr)
      iv = iv_intersect(iv, bounds_get_expr_overrides(b, canon));
  }
  if (var && var->modulus > 0)
    iv = interval_intersect_congruence(iv, var->modulus, var->remainder);
  if (bounds_exact_unit_difference_value(b, expr, &exact) ||
      (canon && canon != expr &&
       bounds_exact_unit_difference_value(b, canon, &exact)))
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
  bounds_projection_bound lower;
  bounds_projection_bound upper;
  bool have_valid;
  bool publish;
  bool semantic_conflict;
} bounds_equality_range_state;

static bool
bounds_equality_range_collect_peer(ixs_bounds *b,
                                   const bounds_equality_walk_entry *walk_entry,
                                   bounds_equality_range_state *state) {
  ixs_interval peer = bounds_get_without_equality(b, walk_entry->node);
  bounds_equality_projection_cache_entry *entry;
  int comparison;

  if (bounds_query_is_tracking(b))
    bounds_query_counter_increment(
        &b->query_state->equality_intrinsic_evaluations);
  if (b->oom)
    return false;
  entry =
      bounds_equality_projection_cache_get(b, walk_entry->endpoint_index, true);
  if (bounds_query_is_tracking(b) && !entry)
    return false;
  if (entry)
    entry->range = peer;
  if (!peer.valid)
    return true;
  state->have_valid = true;
  if (!peer.lo_inf) {
    if (state->lower.present &&
        !bounds_projection_bound_cmp(peer.lo_p, peer.lo_q, walk_entry->offset,
                                     state->lower.p, state->lower.q,
                                     state->lower.peer_offset, &comparison)) {
      bounds_query_note_invalid(b->query_state);
      return false;
    }
    if (!state->lower.present || comparison > 0) {
      state->lower.p = peer.lo_p;
      state->lower.q = peer.lo_q;
      state->lower.peer_offset = walk_entry->offset;
      state->lower.present = true;
    }
  }
  if (!peer.hi_inf) {
    if (state->upper.present &&
        !bounds_projection_bound_cmp(peer.hi_p, peer.hi_q, walk_entry->offset,
                                     state->upper.p, state->upper.q,
                                     state->upper.peer_offset, &comparison)) {
      bounds_query_note_invalid(b->query_state);
      return false;
    }
    if (!state->upper.present || comparison < 0) {
      state->upper.p = peer.hi_p;
      state->upper.q = peer.hi_q;
      state->upper.peer_offset = walk_entry->offset;
      state->upper.present = true;
    }
  }
  return true;
}

static void
bounds_equality_range_collect_peers(ixs_bounds *b,
                                    const bounds_equality_walk *walk,
                                    bounds_equality_range_state *state) {
  size_t i;
  for (i = 0; i < walk->count; i++) {
    if (!bounds_equality_range_collect_peer(b, &walk->entries[i], state)) {
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
  if (!bounds_projection_bound_cmp(state->lower.p, state->lower.q,
                                   state->lower.peer_offset, state->upper.p,
                                   state->upper.q, state->upper.peer_offset,
                                   &comparison)) {
    bounds_query_note_invalid(b->query_state);
    state->publish = false;
    return;
  }
  state->semantic_conflict = comparison > 0;
}

static ixs_interval
bounds_equality_range_publish(ixs_bounds *b, const bounds_equality_walk *walk,
                              size_t endpoint_index, ixs_interval intrinsic,
                              const bounds_equality_range_state *state) {
  ixs_interval result = ixs_interval_unknown();
  size_t i;
  for (i = 0; state->publish && !b->oom && i < walk->count; i++) {
    bounds_equality_projection_cache_entry *entry =
        bounds_equality_projection_cache_get(b, walk->entries[i].endpoint_index,
                                             true);
    ixs_interval projected = ixs_interval_unknown();
    if (bounds_query_is_tracking(b) && !entry)
      break;
    if (!state->semantic_conflict && state->have_valid) {
      ixs_interval peer_intrinsic =
          entry ? entry->range
                : (walk->entries[i].endpoint_index == endpoint_index
                       ? intrinsic
                       : ixs_interval_unknown());
      projected =
          bounds_projection_apply(peer_intrinsic, walk->entries[i].offset,
                                  &state->lower, &state->upper);
    }
    if (entry) {
      entry->range = projected;
      entry->range_complete = true;
    }
    if (walk->entries[i].endpoint_index == endpoint_index)
      result = projected;
  }
  return result;
}

/* Project peer ranges back through node == expr + offset. */
static ixs_interval bounds_project_equality_range(ixs_bounds *b, ixs_node *expr,
                                                  ixs_interval intrinsic) {
  bounds_equality_walk walk;
  bounds_equality_walk_status status;
  bounds_equality_projection_cache_entry *cached;
  bounds_equality_range_state state = {{0, 1, {0, 0, false}, false},
                                       {0, 1, {0, 0, false}, false},
                                       false,
                                       true,
                                       false};
  ixs_interval result;
  size_t endpoint_index;
  size_t limit_blocks = b->query_state ? b->query_state->limit_blocks : 0u;

  if (!bounds_find_equality_endpoint(b, expr, &endpoint_index))
    return intrinsic;
  cached = bounds_equality_projection_cache_get(b, endpoint_index, false);
  if (cached && cached->range_complete)
    return cached->range;
  status = bounds_collect_equality_component(b, expr, &walk, true);
  if (status == BOUNDS_EQUALITY_WALK_NONE)
    return intrinsic;
  if (status != BOUNDS_EQUALITY_WALK_VALID) {
    if (status == BOUNDS_EQUALITY_WALK_INVALID)
      bounds_query_note_invalid(b->query_state);
    bounds_equality_walk_destroy(b, &walk);
    return ixs_interval_unknown();
  }
  if (!bounds_publish_defined_equality_component(b, &walk)) {
    bounds_equality_walk_destroy(b, &walk);
    return ixs_interval_unknown();
  }
  bounds_equality_range_collect_peers(b, &walk, &state);
  if (bounds_query_limited_since(b, limit_blocks))
    state.publish = false;
  bounds_equality_range_validate(b, &state);
  result = bounds_equality_range_publish(b, &walk, endpoint_index, intrinsic,
                                         &state);
  bounds_equality_walk_destroy(b, &walk);
  return b->oom ? ixs_interval_unknown() : result;
}

static ixs_interval bounds_get_query_impl(ixs_bounds *b, ixs_node *expr) {
  ixs_interval result;
  if (!b)
    return ixs_interval_unknown();
  result = bounds_get_intrinsic(b, expr);
  if (!b->oom && b->nequalities && b->equality_disabled_depth == 0)
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
  if (entry && entry->outcome == BOUNDS_QUERY_OUTCOME_VALUE)
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
  bounds_interval_frame *frames;
  size_t depth;
  size_t capacity;
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

static bool bounds_interval_push(bounds_interval_query *query, ixs_node *expr) {
  bounds_interval_frame *grown;
  size_t capacity;
  size_t old_bytes;
  size_t new_bytes;
  if (query->depth == query->capacity) {
    capacity = query->capacity ? query->capacity * 2u : 16u;
    if (capacity < query->capacity ||
        capacity > SIZE_MAX / sizeof(*query->frames)) {
      query->bounds->oom = true;
      return false;
    }
    old_bytes = query->capacity * sizeof(*query->frames);
    new_bytes = capacity * sizeof(*query->frames);
    grown = ixs_arena_grow(query->bounds->scratch, query->frames, old_bytes,
                           new_bytes, sizeof(void *));
    if (!grown) {
      query->bounds->oom = true;
      return false;
    }
    query->frames = grown;
    query->capacity = capacity;
  }
  memset(&query->frames[query->depth], 0, sizeof(*query->frames));
  query->frames[query->depth++].expr = expr;
  return true;
}

static void bounds_interval_complete(bounds_interval_query *query,
                                     ixs_interval result) {
  bounds_interval_frame *frame = &query->frames[query->depth - 1u];
  if (frame->tracked) {
    bounds_query_cache_entry *entry =
        bounds_query_finish(&frame->scope, result.valid);
    if (entry && entry->outcome == BOUNDS_QUERY_OUTCOME_VALUE)
      entry->result.interval = result;
    else
      result = ixs_interval_unknown();
  }
  query->depth--;
  query->child = result;
}

static void bounds_interval_unwind(bounds_interval_query *query) {
  ixs_interval unknown = ixs_interval_unknown();
  while (query->depth != 0)
    bounds_interval_complete(query, unknown);
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
  ixs_interval unknown = ixs_interval_unknown();
  if (!b || !expr || b->oom)
    return unknown;
  if (!bounds_query_should_track(b, expr))
    return bounds_get_query_impl(b, expr);

  mark = ixs_arena_save(b->scratch);
  memset(&query, 0, sizeof(query));
  query.bounds = b;
  if (!bounds_interval_push(&query, expr))
    goto failed;

  while (query.depth != 0) {
    bounds_interval_frame *frame = &query.frames[query.depth - 1u];
    if (!frame->children_ready) {
      bounds_query_cache_entry *cached = NULL;
      bounds_query_enter_result enter = bounds_query_begin(
          b, BOUNDS_QUERY_INTERVAL, frame->expr, 0, &frame->scope, &cached);
      if (enter == BOUNDS_QUERY_ENTER_CACHED) {
        bounds_interval_complete(&query, cached->result.interval);
        continue;
      }
      if (enter != BOUNDS_QUERY_ENTER_STARTED) {
        bounds_interval_complete(&query, unknown);
        continue;
      }
      frame->tracked = true;
      frame->children_ready = true;
      frame->child_count = bounds_interval_child_count(frame->expr);
    }
    if (frame->next_child < frame->child_count) {
      ixs_node *child = bounds_interval_child(frame->expr, frame->next_child++);
      if (!child || !bounds_interval_push(&query, child))
        goto failed;
      continue;
    }
    {
      bool old_evaluating = b->interval_evaluating;
      ixs_interval result;
      b->interval_evaluating = true;
      result = bounds_get_query_impl(b, frame->expr);
      b->interval_evaluating = old_evaluating;
      if (b->oom)
        goto failed;
      bounds_interval_complete(&query, result);
    }
  }

  ixs_arena_restore(b->scratch, mark);
  return query.child;

failed:
  b->interval_evaluating = false;
  bounds_interval_unwind(&query);
  ixs_arena_restore(b->scratch, mark);
  return unknown;
}

static ixs_interval bounds_get_tracked(ixs_bounds *b, ixs_node *expr) {
  if (b && b->interval_evaluating)
    return bounds_get_tracked_one(b, expr);
  return bounds_get_interval_iterative(b, expr);
}

IXS_STATIC ixs_interval ixs_bounds_get(ixs_bounds *b, ixs_node *expr) {
  return bounds_get_tracked(b, expr);
}

static bool bounds_exact_integer_difference(ixs_bounds *b, ixs_node *difference,
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
      ixs_var_bound *var = find_var(b, expr->u.name);
      if (var && bounds_interval_is_zero(var->iv))
        return true;
    }
    iv = bounds_get_expr_overrides(b, expr);
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
    refine_var_bit_consistency(b, &b->vars[i]);
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
      var = find_var(b, b->exprs[i].expr->u.name);
    if (var) {
      iv = iv_intersect(iv, var->iv);
      if (!iv.valid || ixs_interval_is_empty(iv) ||
          (var->modulus > 0 &&
           !interval_has_congruent_integer(&iv, var->modulus, var->remainder)))
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
    if (ixs_bounds_get_modrem(b, q.dividend->u.name, &sym_mod, &sym_rem) &&
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

/* Recognize +/- (x - Mod(x,m)).  For integer x >= 0 and positive m this is
 * +/- m*floor(x/m), so its sign follows directly without losing correlation
 * between x and its remainder to independent interval arithmetic. */
typedef struct {
  ixs_node *mod;
  ixs_node *dividend;
  int64_t mod_coefficient;
} bounds_mod_quotient_match;

static bool bounds_extract_mod_quotient(ixs_node *expr,
                                        bounds_mod_quotient_match *match) {
  int64_t constant_p;
  int64_t constant_q;
  int64_t dividend_coefficient = 0;
  uint32_t i;

  memset(match, 0, sizeof(*match));
  if (expr->tag != IXS_ADD || expr->u.add.nterms != 2u)
    return false;
  ixs_node_get_rat(expr->u.add.coeff, &constant_p, &constant_q);
  if (constant_p != 0 || constant_q != 1)
    return false;
  for (i = 0; i < 2u; i++) {
    ixs_node *term = expr->u.add.terms[i].term;
    int64_t p;
    int64_t q;
    ixs_node_get_rat(expr->u.add.terms[i].coeff, &p, &q);
    if (q != 1)
      return false;
    if (term->tag == IXS_MOD) {
      if (match->mod)
        return false;
      match->mod = term;
      match->mod_coefficient = p;
    } else {
      if (match->dividend)
        return false;
      match->dividend = term;
      dividend_coefficient = p;
    }
  }
  return match->mod && match->dividend &&
         match->mod->u.binary.lhs == match->dividend &&
         ((match->mod_coefficient == -1 && dividend_coefficient == 1) ||
          (match->mod_coefficient == 1 && dividend_coefficient == -1));
}

static bool bounds_mod_quotient_domain(ixs_bounds *b,
                                       const bounds_mod_quotient_match *match) {
  ixs_interval dividend_range;
  ixs_interval modulus_range;

  if (ixs_bounds_check_integer_valued(b, match->dividend) != IXS_CHECK_TRUE)
    return false;
  modulus_range = ixs_bounds_get(b, match->mod->u.binary.rhs);
  dividend_range = ixs_bounds_get(b, match->dividend);
  return interval_lower_at_least(&modulus_range, 1, 1) &&
         interval_lower_at_least(&dividend_range, 0, 1);
}

static ixs_check_result bounds_check_mod_quotient_order(ixs_bounds *b,
                                                        ixs_node *cmp) {
  bounds_mod_quotient_match match;

  if (!cmp || cmp->tag != IXS_CMP || !ixs_node_is_zero(cmp->u.binary.rhs))
    return IXS_CHECK_UNKNOWN;
  if (!bounds_extract_mod_quotient(cmp->u.binary.lhs, &match) ||
      !bounds_mod_quotient_domain(b, &match))
    return IXS_CHECK_UNKNOWN;

  if (match.mod_coefficient == -1) {
    if (cmp->u.binary.cmp_op == IXS_CMP_GE)
      return IXS_CHECK_TRUE;
    if (cmp->u.binary.cmp_op == IXS_CMP_LT)
      return IXS_CHECK_FALSE;
  } else {
    if (cmp->u.binary.cmp_op == IXS_CMP_LE)
      return IXS_CHECK_TRUE;
    if (cmp->u.binary.cmp_op == IXS_CMP_GT)
      return IXS_CHECK_FALSE;
  }
  return IXS_CHECK_UNKNOWN;
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

static ixs_check_result interval_check_zero(const ixs_interval *iv,
                                            ixs_cmp_op op) {
  int lo_cmp = ixs_rat_cmp(iv->lo_p, iv->lo_q, 0, 1);
  int hi_cmp = ixs_rat_cmp(iv->hi_p, iv->hi_q, 0, 1);
  switch (op) {
  case IXS_CMP_GT:
    if (lo_cmp > 0)
      return IXS_CHECK_TRUE;
    if (hi_cmp <= 0)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_GE:
    if (lo_cmp >= 0)
      return IXS_CHECK_TRUE;
    if (hi_cmp < 0)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_LT:
    if (hi_cmp < 0)
      return IXS_CHECK_TRUE;
    if (lo_cmp >= 0)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_LE:
    if (hi_cmp <= 0)
      return IXS_CHECK_TRUE;
    if (lo_cmp > 0)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_EQ:
    if (lo_cmp == 0 && hi_cmp == 0)
      return IXS_CHECK_TRUE;
    if (lo_cmp > 0 || hi_cmp < 0)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_NE:
    if (lo_cmp > 0 || hi_cmp < 0)
      return IXS_CHECK_TRUE;
    if (lo_cmp == 0 && hi_cmp == 0)
      return IXS_CHECK_FALSE;
    break;
  }
  return IXS_CHECK_UNKNOWN;
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

static ixs_check_result interval_check_relation(const ixs_interval *lhs,
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

static ixs_check_result bounds_check_raw(ixs_bounds *b, ixs_node *cmp) {
  ixs_interval iv;
  ixs_interval rhs_iv;
  ixs_interval truncating_remainder;
  ixs_check_result mod_result, quotient_result, congruence_result, bit_result;
  bounds_truncating_range_status truncating_status;

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
    return interval_check_relation(&iv, &rhs_iv, cmp->u.binary.cmp_op);
  }

  mod_result = bounds_check_mod_query(b, cmp);
  if (mod_result != IXS_CHECK_UNKNOWN)
    return mod_result;

  quotient_result = bounds_check_mod_quotient_order(b, cmp);
  if (quotient_result != IXS_CHECK_UNKNOWN)
    return quotient_result;

  congruence_result = bounds_check_zero_congruence_query(b, cmp);
  if (congruence_result != IXS_CHECK_UNKNOWN)
    return congruence_result;

  bit_result = bounds_check_bit_query(b, cmp);
  if (bit_result != IXS_CHECK_UNKNOWN)
    return bit_result;

  iv = ixs_bounds_get(b, cmp->u.binary.lhs);
  truncating_status = bounds_get_truncating_remainder_range(
      b, cmp->u.binary.lhs, /*expression_defined=*/true, &truncating_remainder);
  if (truncating_status == BOUNDS_TRUNCATING_RANGE_MATCH)
    iv = iv_intersect(iv, truncating_remainder);
  else
    bounds_note_truncating_range_status(b, truncating_status);
  if (!iv.valid)
    return IXS_CHECK_UNKNOWN;

  return interval_check_zero(&iv, cmp->u.binary.cmp_op);
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
  result = bounds_check_raw(b, cmp);
  if (query_held)
    ixs_bounds_query_hold_end(b);
  return result;
}

/* Definedness is a proof query, not an evaluator.  All expression traversal
 * uses growable work stacks.  The branch-sensitive Piecewise pass invokes a
 * structural-only subquery for its conditions and values, so C recursion is
 * statically bounded while nested Piecewise DAGs remain unbounded in size. */
#define DEFINED_BOUNDS_CACHE_MIN_CAP 32u
#define DEFINED_BOUNDS_CACHE_CAP 8192u

typedef struct {
  ixs_ctx *ctx;
  ixs_arena *arena;
  ixs_arena_mark arena_mark;
  ixs_node **active_piecewise;
  size_t active_piecewise_count;
  size_t active_piecewise_capacity;
  size_t visited;
  bool oom;
  bool limited;
  bool invalid;
} defined_state;

typedef struct {
  ixs_node *node;
  ixs_check_result result;
  bool active;
  bool complete;
} defined_memo_entry;

typedef struct {
  defined_memo_entry *entries;
  size_t count;
  size_t capacity;
} defined_memo;

typedef struct {
  ixs_node *node;
  ixs_node *selected_condition;
  ixs_node *selected_value;
  uint32_t next_child;
  uint32_t nchildren;
  ixs_check_result result;
  bool started;
  bool selected_piecewise_case;
} defined_frame;

typedef struct {
  ixs_node *node;
  uint32_t next_child;
  uint32_t nchildren;
} defined_depth_frame;

typedef struct {
  ixs_node *node;
  bool active;
  bool complete;
} defined_depth_entry;

typedef struct {
  defined_depth_entry *entries;
  size_t count;
  size_t capacity;
} defined_depth_memo;

typedef struct {
  ixs_arena_mark mark;
  ixs_ctx *old_ctx;
  ixs_bounds_cache_entry *old_cache;
  size_t old_cache_cap;
  bool active;
} defined_cache_scope;

static void defined_state_init(defined_state *state, ixs_ctx *ctx,
                               ixs_bounds *bounds) {
  memset(state, 0, sizeof(*state));
  state->ctx = ctx;
  state->arena = &bounds->query_arena;
  state->arena_mark = ixs_arena_save(state->arena);
}

static void defined_state_destroy(defined_state *state) {
  ixs_arena_restore(state->arena, state->arena_mark);
}

static bool defined_piecewise_enter(defined_state *state, ixs_node *expr) {
  size_t i;
  for (i = 0; i < state->active_piecewise_count; i++) {
    if (state->active_piecewise[i] == expr) {
      state->invalid = true;
      return false;
    }
  }
  if (state->active_piecewise_count == state->active_piecewise_capacity) {
    size_t next_capacity = state->active_piecewise_capacity
                               ? state->active_piecewise_capacity * 2u
                               : 8u;
    ixs_node **grown;
    if (next_capacity <= state->active_piecewise_capacity ||
        next_capacity > SIZE_MAX / sizeof(*grown)) {
      state->oom = true;
      return false;
    }
    grown = ixs_arena_grow(state->arena, state->active_piecewise,
                           state->active_piecewise_capacity * sizeof(*grown),
                           next_capacity * sizeof(*grown), sizeof(void *));
    if (!grown) {
      state->oom = true;
      return false;
    }
    state->active_piecewise = grown;
    state->active_piecewise_capacity = next_capacity;
  }
  state->active_piecewise[state->active_piecewise_count++] = expr;
  return true;
}

static void defined_piecewise_leave(defined_state *state) {
  assert(state->active_piecewise_count != 0);
  state->active_piecewise_count--;
}

static ixs_check_result defined_combine(ixs_check_result lhs,
                                        ixs_check_result rhs) {
  if (lhs == IXS_CHECK_FALSE || rhs == IXS_CHECK_FALSE)
    return IXS_CHECK_FALSE;
  if (lhs == IXS_CHECK_UNKNOWN || rhs == IXS_CHECK_UNKNOWN)
    return IXS_CHECK_UNKNOWN;
  return IXS_CHECK_TRUE;
}

static bool defined_cmp_op_valid(ixs_cmp_op op) {
  switch (op) {
  case IXS_CMP_GT:
  case IXS_CMP_GE:
  case IXS_CMP_LT:
  case IXS_CMP_LE:
  case IXS_CMP_EQ:
  case IXS_CMP_NE:
    return true;
  }
  return false;
}

static ixs_cmp_op defined_negate_cmp_op(ixs_cmp_op op) {
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

static int defined_fixed_child_count(ixs_tag tag) {
  switch (tag) {
  case IXS_INT:
  case IXS_RAT:
  case IXS_SYM:
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    return 0;
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
  case IXS_NOT:
    return 1;
  case IXS_MOD:
  case IXS_CMP:
    return 2;
  default:
    return -1;
  }
}

/* Keep this local walker independent of the public assert-based accessors.
 * It also gives malformed internal nodes the required conservative result. */
static bool defined_child_count(ixs_node *node, uint32_t *out) {
  int fixed;
  if (!node || !out)
    return false;
  fixed = defined_fixed_child_count(node->tag);
  if (fixed >= 0) {
    *out = (uint32_t)fixed;
    return true;
  }
  switch (node->tag) {
  case IXS_ADD:
    if (!node->u.add.coeff || (node->u.add.nterms > 0 && !node->u.add.terms) ||
        node->u.add.nterms > (UINT32_MAX - 1u) / 2u)
      return false;
    *out = 1u + 2u * node->u.add.nterms;
    return true;
  case IXS_MUL:
    if (!node->u.mul.coeff ||
        (node->u.mul.nfactors > 0 && !node->u.mul.factors) ||
        node->u.mul.nfactors == UINT32_MAX)
      return false;
    *out = 1u + node->u.mul.nfactors;
    return true;
  case IXS_PIECEWISE:
    if ((node->u.pw.ncases > 0 && !node->u.pw.cases) ||
        node->u.pw.ncases > UINT32_MAX / 2u)
      return false;
    *out = 2u * node->u.pw.ncases;
    return true;
  case IXS_AND:
  case IXS_OR:
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
    if (node->u.assoc.nargs < 2 || !node->u.assoc.args)
      return false;
    *out = node->u.assoc.nargs;
    return true;
  default:
    return false;
  }
}

static ixs_node *defined_child_at(ixs_node *node, uint32_t child) {
  switch (node->tag) {
  case IXS_ADD:
    if (child == 0)
      return node->u.add.coeff;
    child--;
    return (child & 1u) == 0u ? node->u.add.terms[child / 2u].coeff
                              : node->u.add.terms[child / 2u].term;
  case IXS_MUL:
    return child == 0 ? node->u.mul.coeff
                      : node->u.mul.factors[child - 1u].base;
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
    return node->u.unary.arg;
  case IXS_NOT:
    return node->u.unary_bool.arg;
  case IXS_MOD:
  case IXS_CMP:
    return child == 0 ? node->u.binary.lhs : node->u.binary.rhs;
  case IXS_PIECEWISE:
    return (child & 1u) == 0u ? node->u.pw.cases[child / 2u].value
                              : node->u.pw.cases[child / 2u].cond;
  case IXS_AND:
  case IXS_OR:
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
    return node->u.assoc.args[child];
  default:
    return NULL;
  }
}

static bool defined_depth_memo_grow(ixs_arena *arena,
                                    defined_depth_memo *memo) {
  size_t next_capacity = memo->capacity ? memo->capacity * 2u : 32u;
  defined_depth_entry *grown;
  size_t i;
  if (next_capacity <= memo->capacity ||
      next_capacity > SIZE_MAX / sizeof(*grown))
    return false;
  grown =
      ixs_arena_alloc(arena, next_capacity * sizeof(*grown), sizeof(void *));
  if (!grown)
    return false;
  memset(grown, 0, next_capacity * sizeof(*grown));
  for (i = 0; i < memo->capacity; i++) {
    defined_depth_entry entry = memo->entries[i];
    size_t index;
    if (!entry.node)
      continue;
    index = entry.node->hash & (next_capacity - 1u);
    while (grown[index].node)
      index = (index + 1u) & (next_capacity - 1u);
    grown[index] = entry;
  }
  memo->entries = grown;
  memo->capacity = next_capacity;
  return true;
}

static defined_depth_entry *defined_depth_memo_get(ixs_arena *arena,
                                                   defined_depth_memo *memo,
                                                   ixs_node *node,
                                                   bool create) {
  size_t index;
  if (create && (!memo->capacity || memo->count + 1u > memo->capacity / 2u)) {
    if (!defined_depth_memo_grow(arena, memo))
      return NULL;
  }
  if (!memo->capacity)
    return NULL;
  index = node->hash & (memo->capacity - 1u);
  while (memo->entries[index].node && memo->entries[index].node != node)
    index = (index + 1u) & (memo->capacity - 1u);
  if (!memo->entries[index].node) {
    if (!create)
      return NULL;
    memo->entries[index].node = node;
    memo->count++;
  }
  return &memo->entries[index];
}

static bool defined_depth_stack_push(ixs_arena *arena,
                                     defined_depth_frame **stack, size_t *depth,
                                     size_t *capacity, ixs_node *node,
                                     uint32_t nchildren) {
  if (*depth == *capacity) {
    size_t next_capacity = *capacity ? *capacity * 2u : 32u;
    defined_depth_frame *grown;
    if (next_capacity <= *capacity || next_capacity > SIZE_MAX / sizeof(*grown))
      return false;
    grown = ixs_arena_grow(arena, *stack, *capacity * sizeof(*grown),
                           next_capacity * sizeof(*grown), sizeof(void *));
    if (!grown)
      return false;
    *stack = grown;
    *capacity = next_capacity;
  }
  (*stack)[*depth].node = node;
  (*stack)[*depth].next_child = 0;
  (*stack)[*depth].nchildren = nchildren;
  (*depth)++;
  return true;
}

static bool defined_bounds_depth_safe(defined_state *state, ixs_bounds *b,
                                      ixs_node *root, bool *shared,
                                      size_t *node_visits) {
  defined_depth_frame *stack = NULL;
  ixs_arena_mark mark;
  defined_depth_memo memo;
  defined_depth_entry *entry;
  size_t depth = 0;
  size_t stack_capacity = 0;
  size_t visited = 0;
  uint32_t nchildren;
  bool safe = false;

  if (shared)
    *shared = false;
  if (node_visits)
    *node_visits = 0;
  if (!root || !defined_child_count(root, &nchildren)) {
    state->invalid = true;
    return false;
  }
  mark = ixs_arena_save(b->scratch);
  memset(&memo, 0, sizeof(memo));
  entry = defined_depth_memo_get(b->scratch, &memo, root, true);
  if (!entry || !defined_depth_stack_push(b->scratch, &stack, &depth,
                                          &stack_capacity, root, nchildren)) {
    state->oom = true;
    ixs_arena_restore(b->scratch, mark);
    return false;
  }
  entry->active = true;
  visited = 1;

  while (depth > 0) {
    defined_depth_frame *frame = &stack[depth - 1];
    ixs_node *child;
    if (frame->next_child >= frame->nchildren) {
      entry = defined_depth_memo_get(b->scratch, &memo, frame->node, false);
      assert(entry != NULL && entry->active);
      entry->active = false;
      entry->complete = true;
      depth--;
      continue;
    }
    child = defined_child_at(frame->node, frame->next_child++);
    if (!child || !defined_child_count(child, &nchildren)) {
      state->invalid = true;
      goto cleanup;
    }
    entry = defined_depth_memo_get(b->scratch, &memo, child, true);
    if (!entry) {
      state->oom = true;
      goto cleanup;
    }
    if (entry->active) {
      state->invalid = true;
      goto cleanup;
    }
    if (entry->complete) {
      if (shared)
        *shared = true;
      continue;
    }
    entry->active = true;
    if (!defined_depth_stack_push(b->scratch, &stack, &depth, &stack_capacity,
                                  child, nchildren)) {
      state->oom = true;
      goto cleanup;
    }
    visited++;
  }
  safe = true;
  if (node_visits)
    *node_visits = visited;

cleanup:
  ixs_arena_restore(b->scratch, mark);
  return safe;
}

static size_t defined_bounds_cache_capacity(size_t node_visits) {
  size_t cap = DEFINED_BOUNDS_CACHE_MIN_CAP;
  while (cap < DEFINED_BOUNDS_CACHE_CAP && node_visits > cap / 2u)
    cap *= 2u;
  return cap;
}

static bool defined_cache_scope_init(defined_cache_scope *scope,
                                     defined_state *state, ixs_bounds *b,
                                     size_t node_visits) {
  ixs_bounds_cache_entry *cache;
  size_t cache_cap = defined_bounds_cache_capacity(node_visits);
  scope->mark = ixs_arena_save(b->scratch);
  scope->old_ctx = b->ctx;
  scope->old_cache = b->cache;
  scope->old_cache_cap = b->cache_cap;
  scope->active = false;
  cache =
      ixs_arena_alloc(b->scratch, cache_cap * sizeof(*cache), sizeof(void *));
  if (!cache) {
    state->oom = true;
    ixs_arena_restore(b->scratch, scope->mark);
    return false;
  }
  memset(cache, 0, cache_cap * sizeof(*cache));
  b->cache = cache;
  b->cache_cap = cache_cap;
  /* Direct overrides are enough for a proof query. Canonical aliases expand
   * recursively and can revisit a shared DAG before the interval cache sees
   * it, so disable that optional path inside this bounded scope. */
  b->ctx = NULL;
  scope->active = true;
  return true;
}

static void defined_cache_scope_destroy(defined_cache_scope *scope,
                                        ixs_bounds *b) {
  if (!scope->active)
    return;
  b->ctx = scope->old_ctx;
  b->cache = scope->old_cache;
  b->cache_cap = scope->old_cache_cap;
  ixs_arena_restore(b->scratch, scope->mark);
  scope->active = false;
}

static ixs_check_result defined_relation_zero(defined_state *state,
                                              ixs_bounds *b, ixs_node *expr,
                                              ixs_cmp_op op) {
  ixs_interval iv;
  ixs_check_result result;
  ixs_bitfacts bits;
  int64_t modulus, remainder;
  defined_cache_scope cache_scope;
  size_t node_visits;
  bool shared;

  if ((op == IXS_CMP_EQ || op == IXS_CMP_NE) &&
      bounds_is_known_nonzero(b, expr))
    return op == IXS_CMP_NE ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
  if (!defined_bounds_depth_safe(state, b, expr, &shared, &node_visits) ||
      !defined_cache_scope_init(&cache_scope, state, b, node_visits))
    return IXS_CHECK_UNKNOWN;
  iv = ixs_bounds_get(b, expr);
  if (b->oom) {
    state->oom = true;
    result = IXS_CHECK_UNKNOWN;
    goto cleanup;
  }
  if (iv.valid) {
    result = interval_check_zero(&iv, op);
    if (result != IXS_CHECK_UNKNOWN)
      goto cleanup;
  }

  result = IXS_CHECK_UNKNOWN;
  if (op != IXS_CMP_EQ && op != IXS_CMP_NE)
    goto cleanup;
  if (!shared && ixs_bounds_get_bitfacts(b, expr, &bits) &&
      bits.known_one != 0) {
    result = op == IXS_CMP_NE ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
    goto cleanup;
  }
  if (b->oom) {
    state->oom = true;
    goto cleanup;
  }
  if (expr->tag == IXS_SYM &&
      ixs_bounds_get_modrem(b, expr->u.name, &modulus, &remainder) &&
      remainder != 0) {
    (void)modulus;
    result = op == IXS_CMP_NE ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
  }

cleanup:
  defined_cache_scope_destroy(&cache_scope, b);
  return result;
}

static ixs_check_result defined_condition_truth(defined_state *state,
                                                ixs_bounds *b, ixs_node *cond) {
  ixs_check_result result;
  defined_cache_scope cache_scope;
  size_t node_visits;
  bool shared;
  if (ixs_node_is_known_false(cond))
    return IXS_CHECK_FALSE;
  if (ixs_node_is_known_true(cond))
    return IXS_CHECK_TRUE;
  if (cond->tag == IXS_CMP) {
    if (ixs_node_is_zero(cond->u.binary.rhs)) {
      result = defined_relation_zero(state, b, cond->u.binary.lhs,
                                     cond->u.binary.cmp_op);
      if (result != IXS_CHECK_UNKNOWN || state->oom)
        return result;
    }
    if (!defined_bounds_depth_safe(state, b, cond, &shared, &node_visits))
      return IXS_CHECK_UNKNOWN;
    if (shared) {
      if (!ixs_node_is_zero(cond->u.binary.rhs))
        return IXS_CHECK_UNKNOWN;
      return defined_relation_zero(state, b, cond->u.binary.lhs,
                                   cond->u.binary.cmp_op);
    }
    if (!defined_cache_scope_init(&cache_scope, state, b, node_visits))
      return IXS_CHECK_UNKNOWN;
    result = bounds_check_raw(b, cond);
    if (b->oom)
      state->oom = true;
    defined_cache_scope_destroy(&cache_scope, b);
    return result;
  }
  return defined_relation_zero(state, b, cond, IXS_CMP_NE);
}

static ixs_node *defined_condition_assumption(defined_state *state,
                                              ixs_node *cond, bool value,
                                              struct ixs_node_impl *storage) {
  memset(storage, 0, sizeof(*storage));
  storage->tag = IXS_CMP;
  storage->u.binary.rhs = state->ctx->node_zero;
  if (cond->tag == IXS_CMP) {
    storage->u.binary.lhs = cond->u.binary.lhs;
    storage->u.binary.rhs = cond->u.binary.rhs;
    storage->u.binary.cmp_op =
        value ? cond->u.binary.cmp_op
              : defined_negate_cmp_op(cond->u.binary.cmp_op);
  } else {
    storage->u.binary.lhs = cond;
    storage->u.binary.cmp_op = value ? IXS_CMP_NE : IXS_CMP_EQ;
  }
  return storage;
}

static bool defined_memo_grow(ixs_arena *arena, defined_memo *memo) {
  size_t next_capacity = memo->capacity ? memo->capacity * 2u : 32u;
  defined_memo_entry *grown;
  size_t i;
  if (next_capacity <= memo->capacity ||
      next_capacity > SIZE_MAX / sizeof(*grown))
    return false;
  grown =
      ixs_arena_alloc(arena, next_capacity * sizeof(*grown), sizeof(void *));
  if (!grown)
    return false;
  memset(grown, 0, next_capacity * sizeof(*grown));
  for (i = 0; i < memo->capacity; i++) {
    defined_memo_entry entry = memo->entries[i];
    size_t index;
    if (!entry.node)
      continue;
    index = entry.node->hash & (next_capacity - 1u);
    while (grown[index].node)
      index = (index + 1u) & (next_capacity - 1u);
    grown[index] = entry;
  }
  memo->entries = grown;
  memo->capacity = next_capacity;
  return true;
}

static defined_memo_entry *defined_memo_get(ixs_arena *arena,
                                            defined_memo *memo, ixs_node *node,
                                            bool create) {
  size_t index;
  if (create && (!memo->capacity || memo->count + 1u > memo->capacity / 2u)) {
    if (!defined_memo_grow(arena, memo))
      return NULL;
  }
  if (!memo->capacity)
    return NULL;
  index = node->hash & (memo->capacity - 1u);
  while (memo->entries[index].node && memo->entries[index].node != node)
    index = (index + 1u) & (memo->capacity - 1u);
  if (!memo->entries[index].node) {
    if (!create)
      return NULL;
    memo->entries[index].node = node;
    memo->count++;
  }
  return &memo->entries[index];
}

static bool defined_stack_push(ixs_arena *arena, defined_frame **stack,
                               size_t *depth, size_t *capacity,
                               ixs_node *node) {
  if (*depth == *capacity) {
    size_t next_capacity = *capacity ? *capacity * 2u : 32u;
    defined_frame *grown;
    if (next_capacity <= *capacity || next_capacity > SIZE_MAX / sizeof(*grown))
      return false;
    grown = ixs_arena_grow(arena, *stack, *capacity * sizeof(*grown),
                           next_capacity * sizeof(*grown), sizeof(void *));
    if (!grown)
      return false;
    *stack = grown;
    *capacity = next_capacity;
  }
  (*stack)[*depth].node = node;
  (*stack)[*depth].selected_condition = NULL;
  (*stack)[*depth].selected_value = NULL;
  (*stack)[*depth].next_child = 0;
  (*stack)[*depth].nchildren = 0;
  (*stack)[*depth].result = IXS_CHECK_TRUE;
  (*stack)[*depth].started = false;
  (*stack)[*depth].selected_piecewise_case = false;
  (*depth)++;
  return true;
}

static ixs_check_result defined_eval(defined_state *state, ixs_bounds *b,
                                     ixs_node *root, unsigned pw_depth);

static bool defined_match_shared_rounding_piecewise(ixs_node *expr,
                                                    ixs_node **condition,
                                                    ixs_node **argument) {
  ixs_node *floor_value;
  ixs_node *ceil_value;

  if (!expr || expr->tag != IXS_PIECEWISE || expr->u.pw.ncases != 2u ||
      !expr->u.pw.cases || !ixs_node_is_known_true(expr->u.pw.cases[1].cond))
    return false;
  floor_value = expr->u.pw.cases[0].value;
  ceil_value = expr->u.pw.cases[1].value;
  if (!floor_value || !ceil_value || floor_value->tag != IXS_FLOOR ||
      ceil_value->tag != IXS_CEIL ||
      floor_value->u.unary.arg != ceil_value->u.unary.arg)
    return false;
  *condition = expr->u.pw.cases[0].cond;
  *argument = floor_value->u.unary.arg;
  return *condition && *argument;
}

static void defined_partition_add(unsigned *partitions,
                                  ixs_check_result result) {
  if (result == IXS_CHECK_TRUE)
    *partitions |= 1u;
  else if (result == IXS_CHECK_FALSE)
    *partitions |= 2u;
  else
    *partitions |= 4u;
}

static ixs_check_result defined_partition_result(unsigned partitions) {
  if (partitions == 1u)
    return IXS_CHECK_TRUE;
  if (partitions == 2u)
    return IXS_CHECK_FALSE;
  return IXS_CHECK_UNKNOWN;
}

typedef enum {
  DEFINED_PW_NEXT,
  DEFINED_PW_STOP,
  DEFINED_PW_FAILED
} defined_pw_step;

static bool defined_piecewise_active(defined_state *state,
                                     ixs_bounds *remaining, ixs_node *cond,
                                     ixs_node *value, unsigned pw_depth,
                                     unsigned *partitions) {
  ixs_arena_mark mark = ixs_arena_save(remaining->scratch);
  ixs_bounds active;
  struct ixs_node_impl assumption;
  bool active_ready = false;
  bool ok = false;
  if (!ixs_bounds_fork(&active, remaining)) {
    state->oom = true;
    goto cleanup;
  }
  active_ready = true;
  if (!ixs_bounds_add_assumption(
          &active,
          defined_condition_assumption(state, cond, true, &assumption))) {
    state->oom = true;
    goto cleanup;
  }
  if (!ixs_bounds_has_empty(&active)) {
    ixs_check_result result = defined_eval(state, &active, value, pw_depth);
    defined_partition_add(partitions, result);
  }
  ok = !state->oom && !state->limited;

cleanup:
  if (active_ready)
    ixs_bounds_destroy(&active);
  ixs_arena_restore(remaining->scratch, mark);
  return ok;
}

static defined_pw_step defined_piecewise_case(defined_state *state,
                                              ixs_bounds *remaining,
                                              const ixs_pwcase *pwcase,
                                              unsigned pw_depth,
                                              unsigned *partitions) {
  ixs_node *cond = pwcase->cond;
  ixs_check_result cond_defined =
      defined_eval(state, remaining, cond, pw_depth);
  ixs_check_result truth;
  struct ixs_node_impl assumption;

  if (state->oom || state->limited)
    return DEFINED_PW_FAILED;
  if (cond_defined != IXS_CHECK_TRUE) {
    defined_partition_add(partitions, cond_defined);
    return DEFINED_PW_STOP;
  }

  truth = defined_condition_truth(state, remaining, cond);
  if (state->oom)
    return DEFINED_PW_FAILED;
  if (truth == IXS_CHECK_FALSE)
    return DEFINED_PW_NEXT;
  if (!defined_bounds_depth_safe(state, remaining, cond, NULL, NULL)) {
    defined_partition_add(partitions, IXS_CHECK_UNKNOWN);
    return DEFINED_PW_STOP;
  }
  if (!defined_piecewise_active(state, remaining, cond, pwcase->value, pw_depth,
                                partitions))
    return DEFINED_PW_FAILED;
  if (truth == IXS_CHECK_TRUE)
    return DEFINED_PW_STOP;

  if (!ixs_bounds_add_assumption(
          remaining,
          defined_condition_assumption(state, cond, false, &assumption))) {
    state->oom = true;
    return DEFINED_PW_FAILED;
  }
  return DEFINED_PW_NEXT;
}

static bool defined_piecewise_shared_result(defined_state *state, ixs_bounds *b,
                                            ixs_node *expr, unsigned pw_depth,
                                            ixs_check_result *result) {
  ixs_node *condition;
  ixs_node *argument;
  ixs_check_result condition_defined;
  ixs_check_result argument_defined;

  if (!defined_match_shared_rounding_piecewise(expr, &condition, &argument))
    return false;
  condition_defined = defined_eval(state, b, condition, pw_depth);
  if (state->oom || state->limited) {
    *result = IXS_CHECK_UNKNOWN;
    return true;
  }
  argument_defined = defined_eval(state, b, argument, pw_depth);
  if (state->oom || state->limited) {
    *result = IXS_CHECK_UNKNOWN;
    return true;
  }
  *result = defined_combine(condition_defined, argument_defined);
  return *result != IXS_CHECK_UNKNOWN;
}

static ixs_check_result defined_piecewise_partitions(defined_state *state,
                                                     ixs_bounds *b,
                                                     ixs_node *expr,
                                                     unsigned pw_depth) {
  ixs_arena_mark outer_mark;
  ixs_bounds remaining;
  unsigned partitions = 0;
  uint32_t i;
  bool stopped = false;
  bool remaining_ready = false;

  outer_mark = ixs_arena_save(b->scratch);
  if (!ixs_bounds_fork(&remaining, b)) {
    state->oom = true;
    ixs_arena_restore(b->scratch, outer_mark);
    return IXS_CHECK_UNKNOWN;
  }
  remaining_ready = true;

  for (i = 0; i < expr->u.pw.ncases; i++) {
    defined_pw_step step;

    if (remaining.oom) {
      state->oom = true;
      break;
    }
    if (ixs_bounds_has_empty(&remaining)) {
      stopped = true;
      break;
    }
    step = defined_piecewise_case(state, &remaining, &expr->u.pw.cases[i],
                                  pw_depth, &partitions);
    if (step == DEFINED_PW_STOP) {
      stopped = true;
      break;
    }
    if (step == DEFINED_PW_FAILED)
      break;
  }

  if (!state->oom && !state->limited && !stopped && !remaining.oom &&
      !ixs_bounds_has_empty(&remaining))
    defined_partition_add(&partitions, IXS_CHECK_FALSE);
  if (remaining.oom)
    state->oom = true;

  if (remaining_ready)
    ixs_bounds_destroy(&remaining);
  ixs_arena_restore(b->scratch, outer_mark);
  if (state->oom || state->limited)
    return IXS_CHECK_UNKNOWN;
  return defined_partition_result(partitions);
}

static ixs_check_result defined_piecewise(defined_state *state, ixs_bounds *b,
                                          ixs_node *expr, unsigned pw_depth) {
  ixs_check_result shared;
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  if (!defined_piecewise_enter(state, expr))
    return IXS_CHECK_UNKNOWN;
  if (defined_piecewise_shared_result(state, b, expr, pw_depth, &shared)) {
    result = shared;
    goto cleanup;
  }
  if ((expr->u.pw.ncases > 0 && !expr->u.pw.cases) ||
      expr->u.pw.ncases > UINT32_MAX / 2u) {
    state->invalid = true;
    goto cleanup;
  }
  result = expr->u.pw.ncases == 0
               ? IXS_CHECK_FALSE
               : defined_piecewise_partitions(state, b, expr, pw_depth);

cleanup:
  defined_piecewise_leave(state);
  return result;
}

static ixs_check_result defined_finalize_node(defined_state *state,
                                              ixs_bounds *b, ixs_node *node,
                                              ixs_check_result result) {
  uint32_t i;
  if (node->tag == IXS_MUL) {
    for (i = 0; i < node->u.mul.nfactors; i++) {
      ixs_check_result guard;
      if (node->u.mul.factors[i].exp == 0)
        result = defined_combine(result, IXS_CHECK_UNKNOWN);
      if (node->u.mul.factors[i].exp >= 0)
        continue;
      guard = defined_relation_zero(state, b, node->u.mul.factors[i].base,
                                    IXS_CMP_NE);
      result = defined_combine(result, guard);
    }
  } else if (node->tag == IXS_MOD) {
    ixs_check_result guard =
        defined_relation_zero(state, b, node->u.binary.rhs, IXS_CMP_GT);
    result = defined_combine(result, guard);
  } else if (node->tag == IXS_XOR || node->tag == IXS_AND ||
             node->tag == IXS_OR) {
    for (i = 0; i < node->u.assoc.nargs; i++) {
      ixs_check_result guard =
          ixs_bounds_check_integer_valued(b, node->u.assoc.args[i]);
      result = defined_combine(result, guard);
    }
  }
  return result;
}

static bool defined_complete_frame(defined_state *state, ixs_bounds *b,
                                   defined_memo *memo, defined_frame *stack,
                                   size_t *depth, ixs_check_result result,
                                   ixs_check_result *answer) {
  defined_frame *frame = &stack[*depth - 1u];
  defined_memo_entry *entry =
      defined_memo_get(b->scratch, memo, frame->node, false);
  if (!entry) {
    state->invalid = true;
    result = IXS_CHECK_UNKNOWN;
  } else {
    entry->result = result;
    entry->active = false;
    entry->complete = true;
  }
  (*depth)--;
  if (*depth == 0) {
    *answer = result;
    return true;
  }
  frame = &stack[*depth - 1u];
  frame->result = defined_combine(frame->result, result);
  frame->next_child++;
  return false;
}

static void defined_start_nested_piecewise(defined_state *state,
                                           defined_frame *frame,
                                           ixs_check_result *direct,
                                           bool *has_direct) {
  ixs_node *node = frame->node;
  uint32_t i;
  if ((node->u.pw.ncases > 0 && !node->u.pw.cases) ||
      node->u.pw.ncases > UINT32_MAX / 2u) {
    state->invalid = true;
    *has_direct = true;
    return;
  }
  for (i = 0; i < node->u.pw.ncases; i++) {
    ixs_node *cond = node->u.pw.cases[i].cond;
    if (!cond || !node->u.pw.cases[i].value) {
      state->invalid = true;
      *has_direct = true;
      return;
    }
    if (ixs_node_is_known_false(cond))
      continue;
    if (!ixs_node_is_known_true(cond)) {
      *has_direct = true;
      return;
    }
    frame->selected_condition = cond;
    frame->selected_value = node->u.pw.cases[i].value;
    frame->selected_piecewise_case = true;
    frame->nchildren = 2u;
    return;
  }
  *direct = IXS_CHECK_FALSE;
  *has_direct = true;
}

static void defined_start_frame(defined_state *state, ixs_bounds *b,
                                defined_frame *frame, unsigned pw_depth,
                                ixs_check_result *direct, bool *has_direct) {
  ixs_node *node = frame->node;
  *direct = IXS_CHECK_UNKNOWN;
  *has_direct = false;

  if (!node || !ixs_ctx_owns_node(state->ctx, node) ||
      ixs_node_is_sentinel(node)) {
    state->invalid = true;
    *has_direct = true;
    return;
  }
  if (ixs_node_is_known_total(node)) {
    *direct = IXS_CHECK_TRUE;
    *has_direct = true;
    return;
  }
  if (state->visited != SIZE_MAX)
    state->visited++;

  /* A range constrains a node only where that node is defined. It cannot skip
   * the structural walk or discharge an operation's domain guards. */

  switch (node->tag) {
  case IXS_INT:
    *direct = IXS_CHECK_TRUE;
    *has_direct = true;
    return;
  case IXS_RAT:
    *direct = node->u.rat.q > 0 ? IXS_CHECK_TRUE : IXS_CHECK_UNKNOWN;
    *has_direct = true;
    return;
  case IXS_SYM:
    *direct = node->u.name ? IXS_CHECK_TRUE : IXS_CHECK_UNKNOWN;
    *has_direct = true;
    return;
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    *has_direct = true;
    return;
  case IXS_PIECEWISE:
    if (pw_depth == 0u) {
      *direct = defined_piecewise(state, b, node, 1u);
      *has_direct = true;
      return;
    }
    /* Nested Piecewise nodes are handled on this work stack when their first
     * reachable case is statically selected.  Unknown selection is a sound
     * UNKNOWN: branch-sensitive environment reasoning is performed only by
     * the statically bounded outer Piecewise pass. */
    defined_start_nested_piecewise(state, frame, direct, has_direct);
    return;
  case IXS_CMP:
    if (!defined_cmp_op_valid(node->u.binary.cmp_op)) {
      state->invalid = true;
      *has_direct = true;
      return;
    }
    break;
  default:
    break;
  }
  if (!defined_child_count(node, &frame->nchildren)) {
    state->invalid = true;
    *has_direct = true;
  }
}

static bool defined_process_child(defined_state *state, ixs_bounds *b,
                                  defined_memo *memo, defined_frame **stack,
                                  size_t *depth, size_t *capacity) {
  defined_frame *frame = &(*stack)[*depth - 1u];
  ixs_node *child;
  defined_memo_entry *entry;
  if (frame->next_child >= frame->nchildren)
    return false;

  if (frame->selected_piecewise_case)
    child = frame->next_child == 0u ? frame->selected_condition
                                    : frame->selected_value;
  else
    child = defined_child_at(frame->node, frame->next_child);
  if (!child) {
    state->invalid = true;
    frame->result = defined_combine(frame->result, IXS_CHECK_UNKNOWN);
    frame->next_child++;
    return true;
  }
  entry = defined_memo_get(b->scratch, memo, child, false);
  if (entry && entry->complete) {
    frame->result = defined_combine(frame->result, entry->result);
    frame->next_child++;
    return true;
  }
  if (entry && entry->active) {
    state->invalid = true;
    return true;
  }
  if (!entry)
    entry = defined_memo_get(b->scratch, memo, child, true);
  if (!entry ||
      !defined_stack_push(b->scratch, stack, depth, capacity, child)) {
    state->oom = true;
    return true;
  }
  entry->active = true;
  return true;
}

static ixs_check_result defined_eval(defined_state *state, ixs_bounds *b,
                                     ixs_node *root, unsigned pw_depth) {
  ixs_arena_mark mark;
  defined_memo memo;
  defined_memo_entry *root_entry;
  defined_frame *stack = NULL;
  size_t depth = 0;
  size_t capacity = 0;
  ixs_check_result answer = IXS_CHECK_UNKNOWN;

  if (!root || state->oom || state->limited || state->invalid)
    return IXS_CHECK_UNKNOWN;
  mark = ixs_arena_save(b->scratch);
  memset(&memo, 0, sizeof(memo));
  root_entry = defined_memo_get(b->scratch, &memo, root, true);
  if (!root_entry ||
      !defined_stack_push(b->scratch, &stack, &depth, &capacity, root)) {
    state->oom = true;
    ixs_arena_restore(b->scratch, mark);
    return IXS_CHECK_UNKNOWN;
  }
  root_entry->active = true;

  while (depth > 0 && !state->oom && !state->limited && !state->invalid) {
    defined_frame *frame = &stack[depth - 1u];
    ixs_node *node = frame->node;

    if (!frame->started) {
      ixs_check_result direct = IXS_CHECK_UNKNOWN;
      bool has_direct = false;
      defined_start_frame(state, b, frame, pw_depth, &direct, &has_direct);
      if (state->limited)
        break;
      if (has_direct) {
        if (defined_complete_frame(state, b, &memo, stack, &depth, direct,
                                   &answer))
          break;
        continue;
      }
      frame->started = true;
    }

    if (defined_process_child(state, b, &memo, &stack, &depth, &capacity))
      continue;

    frame->result = defined_finalize_node(state, b, node, frame->result);
    if (defined_complete_frame(state, b, &memo, stack, &depth, frame->result,
                               &answer))
      break;
  }

  ixs_arena_restore(b->scratch, mark);
  if (state->oom || state->limited || state->invalid)
    return IXS_CHECK_UNKNOWN;
  return answer;
}

static bool bounds_defined_cache_lookup(ixs_bounds *b, ixs_node *expr,
                                        ixs_check_result *result) {
  bounds_equality_projection_cache_entry *entry;
  size_t endpoint_index;
  bool without_equality;
  if (!bounds_query_is_tracking(b) || !b->query_state ||
      !bounds_find_equality_endpoint(b, expr, &endpoint_index))
    return false;
  entry = bounds_equality_projection_cache_get(b, endpoint_index, false);
  if (!entry)
    return false;
  without_equality = b->equality_disabled_depth != 0;
  if (without_equality && entry->defined_without_equality_complete) {
    *result = entry->defined_without_equality;
    return true;
  }
  if (!without_equality && entry->defined_with_equality_complete) {
    *result = entry->defined_with_equality;
    return true;
  }
  return false;
}

static bool bounds_defined_cache_publish(ixs_bounds *b, ixs_node *expr,
                                         ixs_check_result result) {
  bounds_equality_projection_cache_entry *entry;
  size_t endpoint_index;
  if (!bounds_query_is_tracking(b) || !b->query_state ||
      !bounds_find_equality_endpoint(b, expr, &endpoint_index))
    return true;
  entry = bounds_equality_projection_cache_get(b, endpoint_index, true);
  if (!entry)
    return false;
  if (b->equality_disabled_depth != 0) {
    entry->defined_without_equality = result;
    entry->defined_without_equality_complete = true;
  } else {
    entry->defined_with_equality = result;
    entry->defined_with_equality_complete = true;
  }
  return true;
}

typedef struct {
  size_t limit_blocks;
  size_t cycle_blocks;
  size_t invalid_blocks;
  bool tracking;
} bounds_defined_query_snapshot;

static bounds_defined_query_snapshot
bounds_defined_query_observe(ixs_bounds *b) {
  bounds_defined_query_snapshot snapshot;
  snapshot.limit_blocks =
      b && b->query_state ? b->query_state->limit_blocks : 0u;
  snapshot.cycle_blocks =
      b && b->query_state ? b->query_state->cycle_blocks : 0u;
  snapshot.invalid_blocks =
      b && b->query_state ? b->query_state->invalid_blocks : 0u;
  snapshot.tracking = bounds_query_is_tracking(b);
  return snapshot;
}

static bool bounds_defined_query_failed(ixs_bounds *b, defined_state *state,
                                        ixs_check_result result,
                                        bounds_defined_query_snapshot snapshot,
                                        bool *oom, bool *limited) {
  bool query_limited;
  bool query_cycle;
  bool query_invalid;
  if (state->limited && snapshot.tracking)
    bounds_query_note_limit(b->query_state);
  if (state->invalid && snapshot.tracking)
    bounds_query_note_invalid(b->query_state);
  query_limited = snapshot.tracking && result == IXS_CHECK_UNKNOWN &&
                  bounds_query_limited_since(b, snapshot.limit_blocks);
  query_cycle = snapshot.tracking && b->query_state &&
                b->query_state->cycle_blocks != snapshot.cycle_blocks;
  query_invalid = snapshot.tracking && b->query_state &&
                  b->query_state->invalid_blocks != snapshot.invalid_blocks;
  if (oom)
    *oom = state->oom || b->oom;
  if (limited)
    *limited = state->limited || query_limited;
  defined_state_destroy(state);
  return state->oom || state->limited || state->invalid || query_limited ||
         query_cycle || query_invalid || b->oom;
}

static ixs_check_result bounds_check_defined_detail(ixs_bounds *b,
                                                    ixs_node *expr, bool *oom,
                                                    bool *limited) {
  defined_state state;
  bounds_defined_query_snapshot snapshot = bounds_defined_query_observe(b);
  ixs_check_result result;
  size_t endpoint_index;
  if (oom)
    *oom = false;
  if (limited)
    *limited = false;
  if (!b || !b->ctx || !b->scratch || !expr || b->oom ||
      ixs_bounds_has_empty(b))
    return IXS_CHECK_UNKNOWN;
  if (ixs_ctx_owns_node(b->ctx, expr) && ixs_node_is_known_total(expr))
    return IXS_CHECK_TRUE;
  if (bounds_defined_cache_lookup(b, expr, &result))
    return result;
  if (snapshot.tracking && b->query_state &&
      bounds_find_equality_endpoint(b, expr, &endpoint_index))
    bounds_query_counter_increment(&b->query_state->equality_defined_checks);
  defined_state_init(&state, b->ctx, b);
  result = defined_eval(&state, b, expr, 0);
  if (bounds_defined_query_failed(b, &state, result, snapshot, oom, limited))
    return IXS_CHECK_UNKNOWN;
  if (!bounds_defined_cache_publish(b, expr, result)) {
    if (oom)
      *oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  return result;
}

static ixs_check_result bounds_check_defined_status(ixs_bounds *b,
                                                    ixs_node *expr, bool *oom) {
  return bounds_check_defined_detail(b, expr, oom, NULL);
}

IXS_STATIC ixs_check_result ixs_bounds_check_defined(ixs_bounds *b,
                                                     ixs_node *expr) {
  return bounds_check_defined_status(b, expr, NULL);
}

static ixs_bounds_build_status assumption_invalid(ixs_bounds *b,
                                                  const char *message) {
  if (b && b->ctx)
    ixs_ctx_push_error(b->ctx, "assumptions: %s", message);
  return IXS_BOUNDS_BUILD_INVALID;
}

static bool assumption_cmp_op_valid(ixs_cmp_op op) {
  switch (op) {
  case IXS_CMP_GT:
  case IXS_CMP_GE:
  case IXS_CMP_LT:
  case IXS_CMP_LE:
  case IXS_CMP_EQ:
  case IXS_CMP_NE:
    return true;
  }
  return false;
}

static void bounds_ingest_validated_leaf(ixs_bounds *b, ixs_node *pred,
                                         bool ingest) {
  if (!ingest)
    return;
  if (pred == b->ctx->node_false) {
    bounds_mark_contradiction(b);
    bounds_cache_clear(b);
    return;
  }
  (void)ixs_bounds_add_assumption(b, pred);
}

typedef struct {
  ixs_node *node;
  uint32_t next_child;
  uint32_t nchildren;
  bool started;
} assumption_predicate_frame;

static bool assumption_predicate_stack_push(ixs_arena *arena,
                                            assumption_predicate_frame **stack,
                                            size_t *depth, size_t *capacity,
                                            ixs_node *node) {
  assumption_predicate_frame *frame;
  if (*depth == *capacity) {
    size_t next_capacity = *capacity ? *capacity * 2u : 32u;
    assumption_predicate_frame *grown;
    if (next_capacity <= *capacity || next_capacity > SIZE_MAX / sizeof(*grown))
      return false;
    grown = ixs_arena_grow(arena, *stack, *capacity * sizeof(*grown),
                           next_capacity * sizeof(*grown), sizeof(void *));
    if (!grown)
      return false;
    *stack = grown;
    *capacity = next_capacity;
  }
  frame = &(*stack)[(*depth)++];
  memset(frame, 0, sizeof(*frame));
  frame->node = node;
  return true;
}

static bool assumption_predicate_leaf_push(ixs_arena *arena, ixs_node ***leaves,
                                           size_t *count, size_t *capacity,
                                           ixs_node *leaf) {
  if (*count == *capacity) {
    size_t next_capacity = *capacity ? *capacity * 2u : 32u;
    ixs_node **grown;
    if (next_capacity <= *capacity || next_capacity > SIZE_MAX / sizeof(*grown))
      return false;
    grown = ixs_arena_grow(arena, *leaves, *capacity * sizeof(*grown),
                           next_capacity * sizeof(*grown), sizeof(void *));
    if (!grown)
      return false;
    *leaves = grown;
    *capacity = next_capacity;
  }
  (*leaves)[(*count)++] = leaf;
  return true;
}

static ixs_bounds_build_status bounds_validate_cmp_leaf(ixs_bounds *b,
                                                        ixs_node *cmp) {
  ixs_node *lhs = cmp->u.binary.lhs;
  ixs_node *rhs = cmp->u.binary.rhs;
  if (!lhs || !rhs || !assumption_cmp_op_valid(cmp->u.binary.cmp_op))
    return assumption_invalid(b, "malformed CMP predicate");
  if (!ixs_ctx_owns_node(b->ctx, lhs) || !ixs_ctx_owns_node(b->ctx, rhs))
    return assumption_invalid(b, "CMP child belongs to a different context");
  if (ixs_node_is_sentinel(lhs) || ixs_node_is_sentinel(rhs))
    return assumption_invalid(b, "sentinel CMP children are not accepted");
  return IXS_BOUNDS_BUILD_OK;
}

static ixs_bounds_build_status bounds_start_predicate_frame(
    ixs_bounds *b, ixs_arena *traversal, assumption_predicate_frame *frame,
    ixs_node ***leaves, size_t *leaf_count, size_t *leaf_capacity) {
  ixs_node *cur = frame->node;
  ixs_bounds_build_status status;
  frame->started = true;
  if (!cur)
    return assumption_invalid(b, "NULL predicate child");
  if (!ixs_ctx_owns_node(b->ctx, cur))
    return assumption_invalid(b, "predicate belongs to a different context");
  if (ixs_node_is_sentinel(cur))
    return assumption_invalid(b, "sentinel predicates are not accepted");
  if (cur == b->ctx->node_true) {
    frame->nchildren = 0u;
    return IXS_BOUNDS_BUILD_OK;
  }
  if (cur == b->ctx->node_false) {
    frame->nchildren = 0u;
  } else if (cur->tag == IXS_CMP) {
    status = bounds_validate_cmp_leaf(b, cur);
    if (status != IXS_BOUNDS_BUILD_OK)
      return status;
    frame->nchildren = 0u;
  } else if (cur->tag == IXS_AND) {
    if (cur->u.assoc.nargs < 2 || !cur->u.assoc.args)
      return assumption_invalid(b, "malformed AND predicate");
    frame->nchildren = cur->u.assoc.nargs;
    return IXS_BOUNDS_BUILD_OK;
  } else if (cur->tag == IXS_OR) {
    return assumption_invalid(b, "OR predicates are not supported");
  } else if (cur->tag == IXS_NOT) {
    return assumption_invalid(b, "NOT predicates are not supported");
  } else {
    return assumption_invalid(
        b, "expected a CMP, AND, or boolean constant predicate");
  }
  return assumption_predicate_leaf_push(traversal, leaves, leaf_count,
                                        leaf_capacity, cur)
             ? IXS_BOUNDS_BUILD_OK
             : IXS_BOUNDS_BUILD_OOM;
}

static ixs_bounds_build_status
bounds_process_predicate(ixs_bounds *b, ixs_node *pred, bool ingest) {
  ixs_arena traversal;
  assumption_predicate_frame *stack = NULL;
  defined_depth_memo memo;
  ixs_node **leaves = NULL;
  size_t depth = 0;
  size_t stack_capacity = 0;
  size_t leaf_count = 0;
  size_t leaf_capacity = 0;
  size_t i;
  ixs_bounds_build_status status = IXS_BOUNDS_BUILD_OK;

  if (!pred)
    return assumption_invalid(b, "NULL predicate");
  ixs_arena_init(&traversal, IXS_ARENA_DEFAULT_SIZE);
  memset(&memo, 0, sizeof(memo));
  {
    defined_depth_entry *entry =
        defined_depth_memo_get(&traversal, &memo, pred, true);
    if (!entry || !assumption_predicate_stack_push(&traversal, &stack, &depth,
                                                   &stack_capacity, pred)) {
      status = IXS_BOUNDS_BUILD_OOM;
      goto cleanup;
    }
    entry->active = true;
  }

  while (depth > 0) {
    assumption_predicate_frame *frame = &stack[depth - 1u];
    ixs_node *cur = frame->node;
    defined_depth_entry *entry;

    if (!frame->started) {
      status = bounds_start_predicate_frame(b, &traversal, frame, &leaves,
                                            &leaf_count, &leaf_capacity);
      if (status != IXS_BOUNDS_BUILD_OK)
        goto cleanup;
    }

    if (frame->next_child < frame->nchildren) {
      ixs_node *child = cur->u.assoc.args[frame->next_child++];
      entry =
          child ? defined_depth_memo_get(&traversal, &memo, child, true) : NULL;
      if (!child) {
        status = assumption_invalid(b, "NULL predicate child");
        goto cleanup;
      }
      if (!entry) {
        status = IXS_BOUNDS_BUILD_OOM;
        goto cleanup;
      }
      if (entry->active) {
        status = assumption_invalid(b, "cyclic predicate tree");
        goto cleanup;
      }
      if (entry->complete)
        continue;
      entry->active = true;
      if (!assumption_predicate_stack_push(&traversal, &stack, &depth,
                                           &stack_capacity, child)) {
        status = IXS_BOUNDS_BUILD_OOM;
        goto cleanup;
      }
      continue;
    }

    entry = defined_depth_memo_get(&traversal, &memo, cur, false);
    if (!entry || !entry->active) {
      status = assumption_invalid(b, "invalid predicate traversal state");
      goto cleanup;
    }
    entry->active = false;
    entry->complete = true;
    depth--;
  }

  for (i = 0; ingest && i < leaf_count; i++) {
    bounds_ingest_validated_leaf(b, leaves[i], true);
    if (b->oom) {
      status = IXS_BOUNDS_BUILD_OOM;
      break;
    }
  }

cleanup:
  ixs_arena_destroy_transient(&traversal);
  return status;
}

static ixs_bounds_build_status bounds_validate_predicate(ixs_bounds *b,
                                                         ixs_node *pred) {
  return bounds_process_predicate(b, pred, false);
}

static ixs_bounds_build_status bounds_ingest_predicate(ixs_bounds *b,
                                                       ixs_node *pred) {
  ixs_bounds_build_status status;
  bool query_held = false;
  /* One published predicate owns the complete proof scope used while its CMP
   * leaves are ingested.  Synthetic branch assumptions are added below an
   * already-active Piecewise scope and therefore do not enter here. */
  if (!ixs_bounds_query_hold_begin(b, pred, &query_held))
    return b && b->oom ? IXS_BOUNDS_BUILD_OOM : IXS_BOUNDS_BUILD_LIMIT;
  status = bounds_process_predicate(b, pred, true);
  if (query_held)
    ixs_bounds_query_hold_end(b);
  return status;
}

static ixs_bounds_build_status
bounds_validate_predicates(ixs_bounds *b, ixs_node *const *predicates,
                           size_t n_predicates) {
  size_t i;
  ixs_bounds_build_status status;

  if (n_predicates > 0 && !predicates)
    return assumption_invalid(b, "NULL array with nonzero count");
  for (i = 0; i < n_predicates; i++) {
    status = bounds_validate_predicate(b, predicates[i]);
    if (status != IXS_BOUNDS_BUILD_OK)
      return status;
  }
  return IXS_BOUNDS_BUILD_OK;
}

static ixs_bounds_build_status
bounds_ingest_predicates(ixs_bounds *b, ixs_node *const *predicates,
                         size_t n_predicates) {
  size_t i;
  ixs_bounds_build_status status;

  if (n_predicates > 0 && !predicates)
    return assumption_invalid(b, "NULL array with nonzero count");
  for (i = 0; i < n_predicates; i++) {
    status = bounds_ingest_predicate(b, predicates[i]);
    if (status != IXS_BOUNDS_BUILD_OK)
      return status;
  }
  return IXS_BOUNDS_BUILD_OK;
}

IXS_STATIC ixs_bounds_build_status
ixs_bounds_build_ctx(ixs_bounds *b, ixs_ctx *ctx, ixs_arena *scratch,
                     ixs_node *const *assumptions, size_t n_assumptions) {
  ixs_bounds_build_status status;
  if (n_assumptions > 0 && !assumptions) {
    ixs_ctx_push_error(ctx, "assumptions: NULL array with nonzero count");
    return IXS_BOUNDS_BUILD_INVALID;
  }
  if (!ixs_bounds_init_ctx(b, ctx, scratch))
    return IXS_BOUNDS_BUILD_OOM;
  status = bounds_ingest_predicates(b, assumptions, n_assumptions);
  if (status != IXS_BOUNDS_BUILD_OK)
    ixs_bounds_destroy(b);
  return status;
}

static bool range_result_to_interval(const ixs_range_result *range,
                                     ixs_interval *out) {
  ixs_interval iv;
  if (!range || !out)
    return false;
  iv.valid = true;
  iv.lo_inf = false;
  iv.hi_inf = false;
  if (range->has_lower) {
    if (!ixs_rat_normalize(range->lower_p, range->lower_q, &iv.lo_p, &iv.lo_q))
      return false;
  } else {
    ixs_interval_set_lo_neg_inf(&iv);
  }
  if (range->has_upper) {
    if (!ixs_rat_normalize(range->upper_p, range->upper_q, &iv.hi_p, &iv.hi_q))
      return false;
  } else {
    ixs_interval_set_hi_pos_inf(&iv);
  }
  if (ixs_interval_is_empty(iv))
    return false;
  *out = iv;
  return true;
}

static void interval_to_range_result(ixs_interval iv, ixs_range_result *out) {
  out->has_lower = !iv.lo_inf;
  out->has_upper = !iv.hi_inf;
  out->lower_p = iv.lo_inf ? 0 : iv.lo_p;
  out->lower_q = iv.lo_inf ? 1 : iv.lo_q;
  out->upper_p = iv.hi_inf ? 0 : iv.hi_p;
  out->upper_q = iv.hi_inf ? 1 : iv.hi_q;
}

static bool facts_bind(ixs_facts *facts, ixs_session_binding *binding,
                       ixs_ctx **ctx) {
  if (!facts || !facts->impl || !facts->ctx || !binding || !ctx ||
      facts->epoch == 0 || facts->impl->ctx != facts->ctx ||
      facts->impl->epoch != facts->epoch)
    return false;
  *ctx = ixs_session_bind_impl(binding, facts->impl);
  facts->bounds.ctx = *ctx;
  facts->bounds.store_ctx = *ctx;
  facts->bounds.scratch = &(*ctx)->scratch;
  return true;
}

typedef struct {
  ixs_bounds *bounds;
  ixs_ctx *ctx;
  const char *query;
  ixs_bounds_query_state *query_state;
  uint64_t generation;
  size_t limit_blocks;
  size_t invalid_blocks;
  size_t nerrors;
  bool old_oom;
  bool tracking_entered;
  bool tracking_limited;
  bool active;
} facts_read_query_scope;

static void facts_read_query_begin(facts_read_query_scope *scope,
                                   ixs_bounds *bounds, ixs_ctx *ctx,
                                   const char *query) {
  memset(scope, 0, sizeof(*scope));
  scope->bounds = bounds;
  scope->ctx = ctx;
  scope->query = query;
  scope->old_oom = bounds->oom;
  if (bounds_query_ensure(bounds)) {
    ixs_bounds_query_state *state = bounds->query_state;
    if (state->nesting == 0)
      bounds_query_reset(state);
    if (state->nesting == SIZE_MAX ||
        bounds->query_tracking_depth == SIZE_MAX) {
      bounds->oom = true;
    } else {
      state->nesting++;
      bounds->query_tracking_depth++;
      scope->tracking_entered = true;
    }
  }
  scope->query_state = bounds->query_state;
  scope->generation =
      bounds->query_state ? bounds->query_state->generation : 0u;
  scope->limit_blocks =
      bounds->query_state ? bounds->query_state->limit_blocks : 0u;
  scope->invalid_blocks =
      bounds->query_state ? bounds->query_state->invalid_blocks : 0u;
  scope->nerrors = ctx ? ctx->nerrors : 0u;
  scope->active = true;
}

typedef struct {
  bool new_oom;
  bool limited;
  bool invalid;
} facts_read_query_observation;

static facts_read_query_observation
facts_read_query_observe(facts_read_query_scope *scope) {
  facts_read_query_observation result = {false, false, false};
  bounds_query_outcome transport = BOUNDS_QUERY_OUTCOME_PENDING;
  size_t limit_baseline;
  size_t invalid_baseline;
  if (scope->bounds->query_state) {
    if (scope->tracking_entered && scope->query_state &&
        (scope->bounds->query_state != scope->query_state ||
         scope->bounds->query_state->generation != scope->generation))
      transport = BOUNDS_QUERY_OUTCOME_INVALID;
    else
      transport = scope->bounds->query_state->transport_outcome;
  }
  result.new_oom = !scope->old_oom && scope->bounds->oom;
  if (scope->bounds->query_state != scope->query_state ||
      (scope->bounds->query_state &&
       scope->bounds->query_state->generation != scope->generation)) {
    limit_baseline = 0u;
    invalid_baseline = 0u;
  } else {
    limit_baseline = scope->limit_blocks;
    invalid_baseline = scope->invalid_blocks;
  }
  result.limited = bounds_query_limited_since(scope->bounds, limit_baseline);
  result.invalid = bounds_query_invalid_since(scope->bounds, invalid_baseline);
  if (transport == BOUNDS_QUERY_OUTCOME_LIMITED)
    result.limited = true;
  else if (transport == BOUNDS_QUERY_OUTCOME_INVALID)
    result.invalid = true;
  else if (transport == BOUNDS_QUERY_OUTCOME_OOM)
    result.new_oom = true;
  return result;
}

static ixs_fact_query_status
facts_read_query_finish(facts_read_query_scope *scope,
                        ixs_fact_query_status status) {
  facts_read_query_observation observed;
  if (!scope || !scope->active)
    return status;
  observed = facts_read_query_observe(scope);
  if (observed.invalid)
    status = IXS_FACT_QUERY_INVALID;
  else if (observed.new_oom || scope->old_oom)
    status = IXS_FACT_QUERY_OOM;
  else if ((observed.limited || scope->tracking_limited) &&
           status == IXS_FACT_QUERY_COMPLETE)
    status = IXS_FACT_QUERY_LIMITED;
  if (observed.new_oom || observed.limited || scope->tracking_limited ||
      observed.invalid || status != IXS_FACT_QUERY_COMPLETE)
    bounds_cache_clear(scope->bounds);
  scope->bounds->oom = scope->old_oom;
  if (scope->ctx && scope->ctx->nerrors == scope->nerrors) {
    if (status == IXS_FACT_QUERY_OOM)
      ixs_ctx_push_error(scope->ctx, "%s: out of memory", scope->query);
    else if (status == IXS_FACT_QUERY_INVALID)
      ixs_ctx_push_error(scope->ctx, "%s: invalid internal relation state",
                         scope->query);
    else if (status == IXS_FACT_QUERY_LIMITED)
      ixs_ctx_push_error(scope->ctx, "%s: resource limit exceeded",
                         scope->query);
  }
  if (scope->tracking_entered)
    ixs_bounds_query_hold_end(scope->bounds);
  scope->active = false;
  return status;
}

static bool facts_ready(const ixs_facts *facts) {
  return facts && facts->usable && !facts->bounds.oom;
}

static void facts_poison(ixs_facts *facts) {
  if (facts)
    facts->usable = false;
}

static void facts_commit(ixs_facts *facts, ixs_bounds *candidate) {
  void *projection_cache = facts->bounds.equality_projection_cache;
  size_t projection_capacity = facts->bounds.equality_projection_cache_capacity;
  /* A fork's projection memo is query-local and cannot be transferred into the
   * committed bounds.  Destroy it, then reuse the destination's persistent
   * table allocation after clearing its semantic contents. */
  assert(candidate->store_ctx != NULL);
  assert(candidate->query_tracking_depth == 0);
  assert(!candidate->query_state_owner && !candidate->query_state_borrowed);
  /* Read queries restore their temporary allocations but may retain arena
   * chunks for reuse.  A commit replaces the complete bounds object, so
   * release that old workspace before overwriting its arena owner. */
  bounds_projection_cache_reset_storage(&facts->bounds, false);
  bounds_projection_cache_reset_storage(candidate, false);
  assert(candidate->query_arena.current == NULL &&
         candidate->query_arena.spare == NULL &&
         candidate->query_arena.inline_chunk == NULL);
  assert(facts->bounds.query_arena.current == NULL &&
         facts->bounds.query_arena.spare == NULL &&
         facts->bounds.query_arena.inline_chunk == NULL);
  candidate->cache = facts->bounds.cache;
  candidate->cache_cap = facts->bounds.cache_cap;
  candidate->equality_projection_cache = projection_cache;
  candidate->equality_projection_cache_count = 0;
  candidate->equality_projection_cache_capacity = projection_capacity;
  bounds_cache_clear(candidate);
  facts->bounds = *candidate;
}

static bool facts_node_ok(ixs_ctx *ctx, ixs_node *node) {
  return node && !ixs_node_is_sentinel(node) && ixs_ctx_owns_node(ctx, node);
}

static bool facts_query_node_ok(ixs_ctx *ctx, ixs_node *node,
                                const char *query) {
  if (!node) {
    ixs_ctx_push_error(ctx, "%s: NULL expression", query);
    return false;
  }
  if (ixs_node_is_sentinel(node)) {
    ixs_ctx_push_error(ctx, "%s: sentinel expression is not accepted", query);
    return false;
  }
  if (!ixs_ctx_owns_node(ctx, node)) {
    ixs_ctx_push_error(ctx, "%s: expression belongs to a different context",
                       query);
    return false;
  }
  return true;
}

static void bounds_add_var_fact(ixs_bounds *dst, const ixs_var_bound *src) {
  ixs_var_bound *v = find_var(dst, src->name);
  ixs_interval old;
  bool changed;
  bounds_cache_clear(dst);
  if (!v) {
    v = get_or_create_var(dst, src->name);
    if (!v)
      return;
    *v = *src;
    if (src->modulus > 0)
      dst->has_modrem = true;
    refine_var_bit_consistency(dst, v);
    bounds_propagate_difference_bounds(dst, src->name, NULL);
    return;
  }

  old = v->iv;
  v->iv = iv_intersect(v->iv, src->iv);
  changed = !bounds_intervals_equal(old, v->iv);
  if (changed)
    bounds_mark_semantic_changed(dst);
  if (src->modulus > 0)
    apply_modrem(dst, src->name, src->modulus, src->remainder);
  apply_var_known_bits(dst, v, src->bits.known_zero, src->bits.known_one);
  apply_pow2_fact(dst, v, src->bits.pow2);
  if (changed)
    bounds_propagate_difference_bounds(dst, src->name, NULL);
}

static void bounds_add_var_interval(ixs_bounds *dst, const char *name,
                                    ixs_interval iv) {
  ixs_var_bound fact;
  if (!iv.valid)
    return;
  memset(&fact, 0, sizeof(fact));
  fact.name = name;
  fact.iv = iv;
  bounds_add_var_fact(dst, &fact);
}

static bool bounds_extract_integer_affine(ixs_node *expr, const char **name,
                                          int64_t *scale, int64_t *offset) {
  int64_t p, q;
  if (!expr || !name || !scale || !offset)
    return false;
  if (expr->tag == IXS_SYM) {
    *name = expr->u.name;
    *scale = 1;
    *offset = 0;
    return true;
  }
  if (expr->tag == IXS_MUL && expr->u.mul.nfactors == 1 &&
      expr->u.mul.factors[0].exp == 1 &&
      expr->u.mul.factors[0].base->tag == IXS_SYM) {
    ixs_node_get_rat(expr->u.mul.coeff, &p, &q);
    if (q != 1 || p == 0)
      return false;
    *name = expr->u.mul.factors[0].base->u.name;
    *scale = p;
    *offset = 0;
    return true;
  }
  if (expr->tag == IXS_ADD && expr->u.add.nterms == 1 &&
      expr->u.add.terms[0].term->tag == IXS_SYM) {
    ixs_node_get_rat(expr->u.add.coeff, offset, &q);
    if (q != 1)
      return false;
    ixs_node_get_rat(expr->u.add.terms[0].coeff, scale, &q);
    if (q != 1 || *scale == 0)
      return false;
    *name = expr->u.add.terms[0].term->u.name;
    return true;
  }
  return false;
}

static bool bounds_interval_contains_rational(ixs_interval iv, int64_t p,
                                              int64_t q) {
  if (!iv.valid)
    return true;
  if (!iv.lo_inf && ixs_rat_cmp(p, q, iv.lo_p, iv.lo_q) < 0)
    return false;
  if (!iv.hi_inf && ixs_rat_cmp(p, q, iv.hi_p, iv.hi_q) > 0)
    return false;
  return true;
}

static void bounds_transfer_inverse_congruence(ixs_bounds *dst,
                                               const char *name, int64_t scale,
                                               int64_t offset, int64_t modulus,
                                               int64_t residue) {
  uint64_t m, a, rhs, g, reduced, inverse, result;
  if (modulus <= 0)
    return;
  m = (uint64_t)modulus;
  a = bounds_normalize_residue(scale, m);
  rhs = bounds_sub_mod(bounds_normalize_residue(residue, m),
                       bounds_normalize_residue(offset, m), m);
  g = bounds_u64_gcd(a, m);
  if (rhs % g != 0) {
    bounds_mark_contradiction(dst);
    return;
  }
  reduced = m / g;
  if (reduced == 1u)
    return;
  if (!bounds_mod_inverse((a / g) % reduced, reduced, &inverse)) {
    bounds_mark_contradiction(dst);
    return;
  }
  result = bounds_mul_mod((rhs / g) % reduced, inverse, reduced);
  apply_modrem(dst, name, (int64_t)reduced, (int64_t)result);
}

static void bounds_transfer_affine_range(ixs_bounds *dst, const char *name,
                                         int64_t scale, int64_t offset,
                                         ixs_interval iv) {
  int64_t neg_offset, denominator;
  ixs_interval shifted, inverse;
  if (!iv.valid || !ixs_safe_neg(offset, &neg_offset))
    return;
  shifted = iv_add(iv, ixs_interval_exact(neg_offset, 1));
  if (scale > 0) {
    denominator = scale;
    inverse = iv_mul_const(shifted, 1, denominator);
  } else {
    if (!ixs_safe_neg(scale, &denominator))
      return;
    inverse = iv_mul_const(shifted, -1, denominator);
  }
  if (inverse.valid)
    bounds_add_var_interval(dst, name, inverse);
}

static void bounds_check_constant_var_fact(ixs_bounds *dst,
                                           const ixs_var_bound *src, int64_t p,
                                           int64_t q) {
  uint64_t value;
  if (!bounds_interval_contains_rational(src->iv, p, q))
    bounds_mark_contradiction(dst);
  if (src->modulus > 0 &&
      (q != 1 || bounds_normalize_residue(p, (uint64_t)src->modulus) !=
                     (uint64_t)src->remainder))
    bounds_mark_contradiction(dst);
  if (src->bits.known_zero != 0 || src->bits.known_one != 0) {
    if (q != 1) {
      bounds_mark_contradiction(dst);
    } else {
      value = (uint64_t)p;
      if ((src->bits.known_zero & value) != 0 ||
          (src->bits.known_one & ~value) != 0)
        bounds_mark_contradiction(dst);
    }
  }
  if (src->bits.pow2 != IXS_POW2_UNKNOWN) {
    if (q != 1 ||
        (src->bits.pow2 == IXS_POW2_POSITIVE && !int64_is_positive_pow2(p)) ||
        (src->bits.pow2 == IXS_POW2_OR_ZERO && p != 0 &&
         !int64_is_positive_pow2(p)))
      bounds_mark_contradiction(dst);
  }
}

static void bounds_transfer_range(ixs_bounds *dst, ixs_node *replacement,
                                  ixs_interval iv) {
  const char *name;
  int64_t scale, offset, p, q;
  if (!iv.valid)
    return;
  if (ixs_node_is_const(replacement)) {
    ixs_node_get_rat(replacement, &p, &q);
    if (!bounds_interval_contains_rational(iv, p, q))
      bounds_mark_contradiction(dst);
    return;
  }
  if (bounds_extract_integer_affine(replacement, &name, &scale, &offset))
    bounds_transfer_affine_range(dst, name, scale, offset, iv);
}

static void bounds_transfer_var_fact(ixs_bounds *dst, const ixs_var_bound *src,
                                     ixs_node *replacement) {
  const char *name;
  int64_t scale, offset, p, q;
  unsigned low_bits = 0;
  uint64_t known, modulus, mask, residue;
  ixs_var_bound renamed;
  ixs_var_bound *var;

  if (replacement->tag == IXS_SYM) {
    renamed = *src;
    renamed.name = replacement->u.name;
    bounds_add_var_fact(dst, &renamed);
    return;
  }
  if (ixs_node_is_const(replacement)) {
    ixs_node_get_rat(replacement, &p, &q);
    bounds_check_constant_var_fact(dst, src, p, q);
    return;
  }
  if (!bounds_extract_integer_affine(replacement, &name, &scale, &offset))
    return;

  bounds_transfer_affine_range(dst, name, scale, offset, src->iv);
  if (src->modulus > 0)
    bounds_transfer_inverse_congruence(dst, name, scale, offset, src->modulus,
                                       src->remainder);

  known = src->bits.known_zero | src->bits.known_one;
  while (low_bits < 62u && (known & (UINT64_C(1) << low_bits)) != 0)
    low_bits++;
  if (low_bits != 0) {
    modulus = UINT64_C(1) << low_bits;
    mask = modulus - 1u;
    residue = src->bits.known_one & mask;
    bounds_transfer_inverse_congruence(dst, name, scale, offset,
                                       (int64_t)modulus, (int64_t)residue);
  }

  if (offset == 0 && int64_is_positive_pow2(scale) &&
      src->bits.pow2 != IXS_POW2_UNKNOWN) {
    var = get_or_create_var(dst, name);
    apply_pow2_fact(dst, var, src->bits.pow2);
  }
}

/* Build a fixed-capacity table at no more than half load. Initialization is
 * O(count); predicate processing never grows the table. */
static bool facts_predicate_set_init(ixs_arena *arena, size_t count,
                                     ixs_node ***slots, size_t *capacity) {
  size_t needed;
  *slots = NULL;
  *capacity = 0;
  if (count < 2)
    return true;
  if (count > SIZE_MAX / 2u)
    return false;
  needed = count * 2u;
  *capacity = 2u;
  while (*capacity < needed) {
    if (*capacity > SIZE_MAX / 2u)
      return false;
    *capacity *= 2u;
  }
  if (*capacity > SIZE_MAX / sizeof(**slots))
    return false;
  *slots = ixs_arena_alloc(arena, *capacity * sizeof(**slots), sizeof(void *));
  if (!*slots)
    return false;
  memset(*slots, 0, *capacity * sizeof(**slots));
  return true;
}

/* Expected O(1) at the fixed half-load bound; collisions probe linearly. */
static bool facts_predicate_seen_or_insert(ixs_node **slots, size_t capacity,
                                           ixs_node *predicate) {
  size_t index = predicate->hash & (capacity - 1u);
  while (slots[index] && slots[index] != predicate)
    index = (index + 1u) & (capacity - 1u);
  if (slots[index])
    return true;
  slots[index] = predicate;
  return false;
}

typedef struct {
  const char *name;
  size_t first_occurrence;
} facts_symbol_slot;

typedef struct {
  const char *name;
  size_t predicate;
  size_t next_for_predicate;
  size_t next_for_symbol;
} facts_symbol_occurrence;

typedef struct {
  ixs_arena arena;
  size_t n_predicates;
  bool *active;
  bool *queued;
  size_t *queue;
  size_t queue_head;
  size_t queue_tail;
  size_t queue_count;
  size_t *predicate_occurrences;
  facts_symbol_slot *symbols;
  size_t symbol_capacity;
  size_t symbol_count;
  facts_symbol_occurrence *occurrences;
  size_t occurrence_capacity;
  size_t occurrence_count;
  ixs_node **seen;
  size_t seen_capacity;
} facts_worklist;

typedef struct {
  ixs_node **slots;
  size_t capacity;
  size_t count;
} query_node_set;

typedef union {
  void *align;
  unsigned char bytes[IXS_ARENA_DEFAULT_SIZE];
} facts_work_storage;

static bool facts_worklist_alloc_arrays(facts_worklist *work) {
  size_t count = work->n_predicates;
  size_t i;
  if (count > SIZE_MAX / sizeof(*work->queue) ||
      count > SIZE_MAX / sizeof(*work->predicate_occurrences))
    return false;
  work->active = ixs_arena_alloc(&work->arena, count * sizeof(*work->active),
                                 sizeof(void *));
  work->queued = ixs_arena_alloc(&work->arena, count * sizeof(*work->queued),
                                 sizeof(void *));
  work->queue = ixs_arena_alloc(&work->arena, count * sizeof(*work->queue),
                                sizeof(void *));
  work->predicate_occurrences = ixs_arena_alloc(
      &work->arena, count * sizeof(*work->predicate_occurrences),
      sizeof(void *));
  if (!work->active || !work->queued || !work->queue ||
      !work->predicate_occurrences)
    return false;
  memset(work->active, 0, count * sizeof(*work->active));
  memset(work->queued, 0, count * sizeof(*work->queued));
  for (i = 0; i < count; i++)
    work->predicate_occurrences[i] = SIZE_MAX;
  return true;
}

static bool facts_worklist_init(facts_worklist *work,
                                facts_work_storage *storage,
                                size_t n_predicates) {
  memset(work, 0, sizeof(*work));
  ixs_arena_init_inline(&work->arena, storage->bytes, sizeof(storage->bytes),
                        IXS_ARENA_DEFAULT_SIZE);
  work->n_predicates = n_predicates;
  if (!facts_worklist_alloc_arrays(work) ||
      !facts_predicate_set_init(&work->arena, n_predicates, &work->seen,
                                &work->seen_capacity)) {
    ixs_arena_destroy_transient(&work->arena);
    return false;
  }
  return true;
}

static void facts_worklist_destroy(facts_worklist *work) {
  ixs_arena_destroy_transient(&work->arena);
}

static facts_symbol_slot *facts_symbol_find(facts_worklist *work,
                                            const char *name) {
  size_t index;
  if (!work->symbols)
    return NULL;
  index = bounds_hash_ptr(name) & (work->symbol_capacity - 1u);
  while (work->symbols[index].name && work->symbols[index].name != name)
    index = (index + 1u) & (work->symbol_capacity - 1u);
  return &work->symbols[index];
}

static bool facts_symbol_table_grow(facts_worklist *work) {
  size_t new_capacity =
      work->symbol_capacity ? work->symbol_capacity * 2u : FACT_WORK_INIT_CAP;
  facts_symbol_slot *symbols;
  size_t i;
  if (new_capacity <= work->symbol_capacity ||
      new_capacity > SIZE_MAX / sizeof(*symbols))
    return false;
  symbols = ixs_arena_alloc(&work->arena, new_capacity * sizeof(*symbols),
                            sizeof(void *));
  if (!symbols)
    return false;
  memset(symbols, 0, new_capacity * sizeof(*symbols));
  for (i = 0; i < work->symbol_capacity; i++) {
    if (work->symbols[i].name) {
      size_t index =
          bounds_hash_ptr(work->symbols[i].name) & (new_capacity - 1u);
      while (symbols[index].name)
        index = (index + 1u) & (new_capacity - 1u);
      symbols[index] = work->symbols[i];
    }
  }
  work->symbols = symbols;
  work->symbol_capacity = new_capacity;
  return true;
}

static bool facts_occurrences_grow(facts_worklist *work) {
  size_t new_capacity = work->occurrence_capacity
                            ? work->occurrence_capacity * 2u
                            : FACT_WORK_INIT_CAP;
  facts_symbol_occurrence *occurrences;
  if (new_capacity <= work->occurrence_capacity ||
      new_capacity > SIZE_MAX / sizeof(*occurrences))
    return false;
  occurrences =
      ixs_arena_grow(&work->arena, work->occurrences,
                     work->occurrence_capacity * sizeof(*work->occurrences),
                     new_capacity * sizeof(*work->occurrences), sizeof(void *));
  if (!occurrences)
    return false;
  work->occurrences = occurrences;
  work->occurrence_capacity = new_capacity;
  return true;
}

static bool facts_worklist_add_symbol(facts_worklist *work, size_t predicate,
                                      const char *name) {
  facts_symbol_slot *slot;
  facts_symbol_occurrence *occurrence;
  size_t index;
  if (!work->symbol_capacity ||
      work->symbol_count >= work->symbol_capacity / 2u) {
    if (!facts_symbol_table_grow(work))
      return false;
  }
  if (work->occurrence_count >= work->occurrence_capacity &&
      !facts_occurrences_grow(work))
    return false;
  slot = facts_symbol_find(work, name);
  if (!slot)
    return false;
  if (!slot->name) {
    slot->name = name;
    slot->first_occurrence = SIZE_MAX;
    work->symbol_count++;
  }
  index = work->occurrence_count++;
  occurrence = &work->occurrences[index];
  occurrence->name = name;
  occurrence->predicate = predicate;
  occurrence->next_for_predicate = work->predicate_occurrences[predicate];
  occurrence->next_for_symbol = slot->first_occurrence;
  work->predicate_occurrences[predicate] = index;
  slot->first_occurrence = index;
  return true;
}

static bool query_node_set_grow(ixs_arena *arena, query_node_set *set) {
  size_t new_capacity = set->capacity ? set->capacity * 2u : FACT_WORK_INIT_CAP;
  ixs_node **slots;
  size_t i;
  if (new_capacity <= set->capacity || new_capacity > SIZE_MAX / sizeof(*slots))
    return false;
  slots = ixs_arena_alloc(arena, new_capacity * sizeof(*slots), sizeof(void *));
  if (!slots)
    return false;
  memset(slots, 0, new_capacity * sizeof(*slots));
  for (i = 0; i < set->capacity; i++) {
    if (set->slots[i]) {
      size_t index = set->slots[i]->hash & (new_capacity - 1u);
      while (slots[index])
        index = (index + 1u) & (new_capacity - 1u);
      slots[index] = set->slots[i];
    }
  }
  set->slots = slots;
  set->capacity = new_capacity;
  return true;
}

static bool query_node_set_insert(ixs_arena *arena, query_node_set *set,
                                  ixs_node *node, bool *inserted) {
  size_t index;
  if (!set->capacity || set->count >= set->capacity / 2u) {
    if (!query_node_set_grow(arena, set))
      return false;
  }
  index = node->hash & (set->capacity - 1u);
  while (set->slots[index] && set->slots[index] != node)
    index = (index + 1u) & (set->capacity - 1u);
  if (set->slots[index]) {
    *inserted = false;
    return true;
  }
  set->slots[index] = node;
  set->count++;
  *inserted = true;
  return true;
}

static bool query_node_stack_push(ixs_arena *arena, ixs_node ***stack,
                                  size_t *count, size_t *capacity,
                                  ixs_node *node) {
  if (*count >= *capacity) {
    size_t new_capacity = *capacity ? *capacity * 2u : FACT_WORK_INIT_CAP;
    ixs_node **grown;
    if (new_capacity <= *capacity || new_capacity > SIZE_MAX / sizeof(**stack))
      return false;
    grown = ixs_arena_grow(arena, *stack, *capacity * sizeof(**stack),
                           new_capacity * sizeof(**stack), sizeof(void *));
    if (!grown)
      return false;
    *stack = grown;
    *capacity = new_capacity;
  }
  (*stack)[(*count)++] = node;
  return true;
}

static bool facts_worklist_index_predicate(facts_worklist *work,
                                           size_t predicate, ixs_node *root) {
  facts_work_storage storage;
  ixs_arena traversal;
  query_node_set visited;
  ixs_node **stack = NULL;
  size_t stack_capacity = 0;
  size_t stack_count = 0;
  bool ok = false;
  ixs_arena_init_inline(&traversal, storage.bytes, sizeof(storage.bytes),
                        IXS_ARENA_DEFAULT_SIZE);
  memset(&visited, 0, sizeof(visited));
  if (!query_node_stack_push(&traversal, &stack, &stack_count, &stack_capacity,
                             root))
    goto cleanup;
  while (stack_count > 0) {
    ixs_node *node = stack[--stack_count];
    uint32_t child_count;
    uint32_t i;
    bool inserted;
    if (!query_node_set_insert(&traversal, &visited, node, &inserted))
      goto cleanup;
    if (!inserted)
      continue;
    if (node->tag == IXS_SYM &&
        !facts_worklist_add_symbol(work, predicate, node->u.name))
      goto cleanup;
    child_count = ixs_node_nchildren(node);
    for (i = 0; i < child_count; i++) {
      if (!query_node_stack_push(&traversal, &stack, &stack_count,
                                 &stack_capacity, ixs_node_child(node, i)))
        goto cleanup;
    }
  }
  ok = true;

cleanup:
  ixs_arena_destroy_transient(&traversal);
  return ok;
}

static bool facts_worklist_enqueue(facts_worklist *work, size_t predicate) {
  if (!work->active[predicate] || work->queued[predicate])
    return true;
  if (work->queue_count >= work->n_predicates)
    return false;
  work->queue[work->queue_tail] = predicate;
  work->queue_tail = (work->queue_tail + 1u) % work->n_predicates;
  work->queue_count++;
  work->queued[predicate] = true;
  return true;
}

static bool facts_worklist_build(facts_worklist *work,
                                 ixs_node *const *predicates) {
  size_t i;
  for (i = 0; i < work->n_predicates; i++) {
    if (work->seen && facts_predicate_seen_or_insert(
                          work->seen, work->seen_capacity, predicates[i]))
      continue;
    work->active[i] = true;
    if (!facts_worklist_index_predicate(work, i, predicates[i]) ||
        !facts_worklist_enqueue(work, i))
      return false;
  }
  return true;
}

static size_t facts_worklist_pop(facts_worklist *work) {
  size_t predicate = work->queue[work->queue_head];
  work->queue_head = (work->queue_head + 1u) % work->n_predicates;
  work->queue_count--;
  work->queued[predicate] = false;
  return predicate;
}

static bool facts_worklist_enqueue_all(facts_worklist *work) {
  size_t i;
  for (i = 0; i < work->n_predicates; i++) {
    if (!facts_worklist_enqueue(work, i))
      return false;
  }
  return true;
}

static bool facts_worklist_enqueue_dependencies(facts_worklist *work,
                                                size_t predicate) {
  size_t occurrence_index = work->predicate_occurrences[predicate];
  if (occurrence_index == SIZE_MAX)
    return facts_worklist_enqueue_all(work);
  while (occurrence_index != SIZE_MAX) {
    facts_symbol_occurrence *occurrence = &work->occurrences[occurrence_index];
    facts_symbol_slot *slot = facts_symbol_find(work, occurrence->name);
    size_t dependent;
    if (!slot || !slot->name) {
      assert(slot && slot->name &&
             "group-union dependency index lost an indexed symbol");
      return false;
    }
    dependent = slot->first_occurrence;
    while (dependent != SIZE_MAX) {
      if (!facts_worklist_enqueue(work, work->occurrences[dependent].predicate))
        return false;
      dependent = work->occurrences[dependent].next_for_symbol;
    }
    occurrence_index = occurrence->next_for_predicate;
  }
  return true;
}

static ixs_bounds_build_status
facts_ingest_original_predicates(ixs_bounds *candidate,
                                 ixs_node *const *predicates,
                                 const facts_worklist *work) {
  size_t i;
  for (i = 0; i < work->n_predicates; i++) {
    ixs_bounds_build_status status;
    if (!work->active[i])
      continue;
    status = bounds_ingest_predicate(candidate, predicates[i]);
    if (status != IXS_BOUNDS_BUILD_OK)
      return status;
  }
  return IXS_BOUNDS_BUILD_OK;
}

static ixs_bounds_build_status
facts_process_predicate_worklist(ixs_ctx *ctx, ixs_bounds *candidate,
                                 ixs_node *const *predicates,
                                 facts_worklist *work) {
  while (work->queue_count > 0) {
    size_t predicate_index = facts_worklist_pop(work);
    ixs_node *predicate;
    ixs_bounds_build_status status;
    bool changed = false;
    bool limited = false;
    candidate->semantic_changed = &changed;
    predicate = simp_simplify_bounds_status(ctx, predicates[predicate_index],
                                            candidate, &limited);
    if (limited) {
      candidate->semantic_changed = NULL;
      return IXS_BOUNDS_BUILD_LIMIT;
    }
    if (!predicate || candidate->oom) {
      candidate->semantic_changed = NULL;
      return IXS_BOUNDS_BUILD_OOM;
    }
    status = bounds_ingest_predicate(candidate, predicate);
    candidate->semantic_changed = NULL;
    if (status != IXS_BOUNDS_BUILD_OK)
      return status;
    if (candidate->contradiction || ixs_bounds_has_empty(candidate))
      return IXS_BOUNDS_BUILD_OK;
    if (changed && !facts_worklist_enqueue_dependencies(work, predicate_index))
      return IXS_BOUNDS_BUILD_OOM;
  }
  return IXS_BOUNDS_BUILD_OK;
}

static ixs_bounds_build_status
facts_ingest_predicate_closure(ixs_ctx *ctx, ixs_bounds *candidate,
                               ixs_node *const *predicates,
                               size_t n_predicates) {
  facts_work_storage storage;
  facts_worklist work;
  ixs_bounds_build_status status = IXS_BOUNDS_BUILD_OOM;
  if (!facts_worklist_init(&work, &storage, n_predicates))
    return IXS_BOUNDS_BUILD_OOM;
  if (!facts_worklist_build(&work, predicates))
    goto cleanup;

  /* Preserve original expression identities before fact-conditioned
   * rewrites. */
  status = facts_ingest_original_predicates(candidate, predicates, &work);
  if (status != IXS_BOUNDS_BUILD_OK || candidate->contradiction ||
      ixs_bounds_has_empty(candidate))
    goto cleanup;

  /* A rewrite cannot introduce a symbol absent from its original predicate.
   * Revisit only predicates that share a symbol with a semantic refinement. */
  status = facts_process_predicate_worklist(ctx, candidate, predicates, &work);

cleanup:
  candidate->semantic_changed = NULL;
  facts_worklist_destroy(&work);
  return status;
}

ixs_facts *ixs_facts_create_preds(ixs_session *s, ixs_node *const *predicates,
                                  size_t n_predicates) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds bounds;
  ixs_bounds_build_status status;
  ixs_facts *facts;
  if (!s)
    return NULL;
  ctx = ixs_session_bind(&binding, s);
  mark = ixs_arena_save(&ctx->scratch);
  status = ixs_bounds_build_ctx(&bounds, ctx, &ctx->scratch, predicates,
                                n_predicates);
  if (status != IXS_BOUNDS_BUILD_OK)
    goto failed;
  facts = ixs_arena_alloc(&ctx->arena, sizeof(*facts), sizeof(void *));
  if (!facts) {
    ixs_bounds_destroy(&bounds);
    goto failed;
  }
  memset(facts, 0, sizeof(*facts));
  facts->impl = binding.impl;
  facts->ctx = ctx;
  facts->epoch = binding.impl->epoch;
  bounds_projection_cache_reset_storage(&bounds, false);
  assert(bounds.store_ctx != NULL && bounds.query_tracking_depth == 0 &&
         !bounds.query_state_owner && !bounds.query_state_borrowed &&
         bounds.query_arena.current == NULL &&
         bounds.query_arena.spare == NULL &&
         bounds.query_arena.inline_chunk == NULL);
  facts->bounds = bounds;
  facts->usable = true;
  facts->session_next = binding.impl->facts_head;
  binding.impl->facts_head = facts;
  ixs_session_unbind(&binding);
  return facts;

failed:
  ixs_arena_restore(&ctx->scratch, mark);
  ixs_session_unbind(&binding);
  return NULL;
}

ixs_facts *ixs_facts_create(ixs_session *s) {
  return ixs_facts_create_preds(s, NULL, 0);
}

static ixs_bounds_build_status facts_validate_closed_predicates(
    ixs_bounds *candidate, ixs_node *const *predicates, size_t n_predicates) {
  size_t i;
  if (candidate->contradiction || ixs_bounds_has_empty(candidate))
    return IXS_BOUNDS_BUILD_OK;
  for (i = 0; i < n_predicates; i++) {
    ixs_check_result defined;
    bool oom = false;
    bool limited = false;
    bool query_held = false;
    if (!ixs_bounds_query_hold_begin(candidate, predicates[i], &query_held))
      return candidate->oom ? IXS_BOUNDS_BUILD_OOM : IXS_BOUNDS_BUILD_LIMIT;
    defined =
        bounds_check_defined_detail(candidate, predicates[i], &oom, &limited);
    if (query_held)
      ixs_bounds_query_hold_end(candidate);
    if (defined == IXS_CHECK_TRUE)
      continue;
    if (oom || candidate->oom)
      return IXS_BOUNDS_BUILD_OOM;
    if (limited)
      return IXS_BOUNDS_BUILD_LIMIT;
    return assumption_invalid(candidate, "batch does not form a closed domain");
  }
  return IXS_BOUNDS_BUILD_OK;
}

static bool facts_assume_predicates(ixs_facts *facts,
                                    ixs_node *const *predicates,
                                    size_t n_predicates, bool require_closed) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds candidate;
  ixs_bounds_build_status status;
  bool candidate_ready = false;
  if (!facts_bind(facts, &binding, &ctx))
    return false;
  if (!facts_ready(facts)) {
    ixs_session_unbind(&binding);
    return false;
  }
  if (n_predicates == 0) {
    ixs_session_unbind(&binding);
    return true;
  }
  if (!predicates) {
    (void)assumption_invalid(&facts->bounds, "NULL array with nonzero count");
    facts_poison(facts);
    ixs_session_unbind(&binding);
    return false;
  }
  mark = ixs_arena_save(&ctx->scratch);
  if (!ixs_bounds_fork(&candidate, &facts->bounds)) {
    ixs_arena_restore(&ctx->scratch, mark);
    facts_poison(facts);
    ixs_session_unbind(&binding);
    return false;
  }
  candidate_ready = true;
  status = bounds_validate_predicates(&candidate, predicates, n_predicates);
  if (status == IXS_BOUNDS_BUILD_OK)
    status = facts_ingest_predicate_closure(ctx, &candidate, predicates,
                                            n_predicates);
  if (status == IXS_BOUNDS_BUILD_OK && require_closed)
    status =
        facts_validate_closed_predicates(&candidate, predicates, n_predicates);
  if (status == IXS_BOUNDS_BUILD_OK) {
    facts_commit(facts, &candidate);
  } else {
    if (candidate_ready)
      ixs_bounds_destroy(&candidate);
    ixs_arena_restore(&ctx->scratch, mark);
    facts_poison(facts);
  }
  ixs_session_unbind(&binding);
  return status == IXS_BOUNDS_BUILD_OK;
}

bool ixs_facts_assume_preds(ixs_facts *facts, ixs_node *const *predicates,
                            size_t n_predicates) {
  return facts_assume_predicates(facts, predicates, n_predicates, true);
}

bool ixs_facts_assume_pred(ixs_facts *facts, ixs_node *pred) {
  return facts_assume_predicates(facts, &pred, 1, false);
}

bool ixs_facts_assume_range(ixs_facts *facts, ixs_node *expr,
                            const ixs_range_result *range) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds candidate;
  ixs_interval iv;
  bool candidate_ready = false;
  bool ok = false;
  if (!facts_bind(facts, &binding, &ctx))
    return false;
  if (!facts_ready(facts))
    goto cleanup;
  mark = ixs_arena_save(&ctx->scratch);
  if (!facts_node_ok(ctx, expr) || !range_result_to_interval(range, &iv))
    goto failed;
  if (!ixs_bounds_fork(&candidate, &facts->bounds))
    goto failed;
  candidate_ready = true;
  ixs_bounds_add_expr(&candidate, expr, iv);
  if (candidate.oom)
    goto failed;
  facts_commit(facts, &candidate);
  ok = true;
  goto cleanup;

failed:
  if (candidate_ready)
    ixs_bounds_destroy(&candidate);
  ixs_arena_restore(&ctx->scratch, mark);
  facts_poison(facts);

cleanup:
  ixs_session_unbind(&binding);
  return ok;
}

bool ixs_facts_derive_affine(ixs_facts *facts, ixs_node *base, int64_t scale,
                             int64_t offset, ixs_node *derived) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds candidate;
  ixs_interval iv, shifted;
  bool candidate_ready = false;
  bool query_held = false;
  bool ok = false;
  if (!facts_bind(facts, &binding, &ctx))
    return false;
  if (!facts_ready(facts))
    goto cleanup;
  mark = ixs_arena_save(&ctx->scratch);
  if (!facts_node_ok(ctx, base) || !facts_node_ok(ctx, derived))
    goto failed;
  if (!ixs_bounds_fork(&candidate, &facts->bounds))
    goto failed;
  candidate_ready = true;
  if (!ixs_bounds_query_hold_begin(&candidate, base, &query_held))
    goto failed;
  iv = ixs_bounds_get(&candidate, base);
  if (candidate.oom || !iv.valid || ixs_interval_is_empty(iv))
    goto failed;
  shifted = iv_add(iv_mul_const(iv, scale, 1), ixs_interval_exact(offset, 1));
  if (!shifted.valid || ixs_interval_is_empty(shifted))
    goto failed;
  ixs_bounds_add_expr(&candidate, derived, shifted);
  if (candidate.oom)
    goto failed;
  if (query_held) {
    ixs_bounds_query_hold_end(&candidate);
    query_held = false;
  }
  facts_commit(facts, &candidate);
  ok = true;
  goto cleanup;

failed:
  if (query_held)
    ixs_bounds_query_hold_end(&candidate);
  if (candidate_ready)
    ixs_bounds_destroy(&candidate);
  ixs_arena_restore(&ctx->scratch, mark);
  facts_poison(facts);

cleanup:
  ixs_session_unbind(&binding);
  return ok;
}

bool ixs_facts_substitute(ixs_facts *dst, const ixs_facts *src,
                          ixs_node *target, ixs_node *replacement) {
  return ixs_facts_substitute_multi(dst, src, 1, &target, &replacement);
}

static bool facts_substitution_inputs_ok(const ixs_facts *dst,
                                         const ixs_facts *src, ixs_ctx *ctx,
                                         uint32_t nsubs,
                                         ixs_node *const *targets,
                                         ixs_node *const *replacements) {
  uint32_t i;
  if (!src || src->impl != dst->impl || src->ctx != ctx ||
      src->epoch != dst->epoch || !facts_ready(src) ||
      (nsubs != 0 && (!targets || !replacements)))
    return false;
  for (i = 0; i < nsubs; i++) {
    if (!facts_node_ok(ctx, targets[i]) || !facts_node_ok(ctx, replacements[i]))
      return false;
  }
  return true;
}

static bool bounds_transfer_substituted_exprs(ixs_bounds *dst,
                                              const ixs_bounds *src,
                                              ixs_ctx *ctx, uint32_t nsubs,
                                              ixs_node *const *targets,
                                              ixs_node *const *replacements) {
  size_t i;
  for (i = 0; i < src->nexprs; i++) {
    if (!src->exprs[i].iv.valid) {
      bounds_mark_contradiction(dst);
      continue;
    }
    ixs_node *subst =
        simp_subs_multi(ctx, src->exprs[i].expr, nsubs, targets, replacements);
    if (!subst || ixs_node_is_sentinel(subst))
      return false;
    ixs_bounds_add_expr(dst, subst, src->exprs[i].iv);
    if (subst != src->exprs[i].expr)
      bounds_transfer_range(dst, subst, src->exprs[i].iv);
    if (dst->oom)
      return false;
  }
  return true;
}

static bool bounds_transfer_substituted_equalities(
    ixs_bounds *dst, const ixs_bounds *src, ixs_ctx *ctx, uint32_t nsubs,
    ixs_node *const *targets, ixs_node *const *replacements) {
  size_t i;
  for (i = 0; i < src->equality_index_cap; i++) {
    ixs_equality_edge *edge = src->equality_index[i];
    ixs_node *lhs;
    ixs_node *rhs;
    if (!edge)
      continue;
    lhs = simp_subs_multi(ctx, edge->lhs, nsubs, targets, replacements);
    rhs = simp_subs_multi(ctx, edge->rhs, nsubs, targets, replacements);
    if (!lhs || !rhs || ixs_node_is_sentinel(lhs) || ixs_node_is_sentinel(rhs))
      return false;
    bounds_add_exact_relation(dst, lhs, rhs, edge->offset);
    if (dst->oom)
      return false;
  }
  return true;
}

static bool bounds_transfer_substituted_vars(ixs_bounds *dst,
                                             const ixs_bounds *src,
                                             ixs_ctx *ctx, uint32_t nsubs,
                                             ixs_node *const *targets,
                                             ixs_node *const *replacements) {
  size_t i;
  for (i = 0; i < src->nvars; i++) {
    ixs_node *sym =
        ixs_node_sym(ctx, src->vars[i].name, strlen(src->vars[i].name));
    ixs_node *subst;
    if (!sym || ixs_node_is_sentinel(sym))
      return false;
    subst = simp_subs_multi(ctx, sym, nsubs, targets, replacements);
    if (!subst || ixs_node_is_sentinel(subst))
      return false;
    if (subst == sym) {
      bounds_add_var_fact(dst, &src->vars[i]);
    } else {
      ixs_bounds_add_expr(dst, subst, src->vars[i].iv);
      bounds_transfer_var_fact(dst, &src->vars[i], subst);
    }
    if (dst->oom)
      return false;
  }
  return true;
}

static bool bounds_transfer_substituted_nonzero(ixs_bounds *dst,
                                                const ixs_bounds *src,
                                                ixs_ctx *ctx, uint32_t nsubs,
                                                ixs_node *const *targets,
                                                ixs_node *const *replacements) {
  size_t i;
  for (i = 0; i < src->nnonzero; i++) {
    ixs_node *subst =
        simp_subs_multi(ctx, src->nonzero[i], nsubs, targets, replacements);
    if (!subst || ixs_node_is_sentinel(subst))
      return false;
    bounds_add_nonzero(dst, subst);
    if (dst->oom)
      return false;
  }
  return true;
}

bool ixs_facts_substitute_multi(ixs_facts *dst, const ixs_facts *src,
                                uint32_t nsubs, ixs_node *const *targets,
                                ixs_node *const *replacements) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds candidate;
  bool candidate_ready = false;
  bool ok = false;

  if (!facts_bind(dst, &binding, &ctx))
    return false;
  if (!facts_ready(dst))
    goto cleanup;
  mark = ixs_arena_save(&ctx->scratch);
  if (!facts_substitution_inputs_ok(dst, src, ctx, nsubs, targets,
                                    replacements))
    goto failed;
  if (src == dst && nsubs == 0) {
    ok = true;
    goto cleanup;
  }
  if (!ixs_bounds_fork(&candidate, &dst->bounds))
    goto failed;
  candidate_ready = true;
  if (src->bounds.contradiction)
    bounds_mark_contradiction(&candidate);
  if (!bounds_transfer_substituted_exprs(&candidate, &src->bounds, ctx, nsubs,
                                         targets, replacements) ||
      !bounds_transfer_substituted_equalities(&candidate, &src->bounds, ctx,
                                              nsubs, targets, replacements) ||
      !bounds_transfer_substituted_vars(&candidate, &src->bounds, ctx, nsubs,
                                        targets, replacements) ||
      !bounds_transfer_substituted_nonzero(&candidate, &src->bounds, ctx, nsubs,
                                           targets, replacements))
    goto failed;
  facts_commit(dst, &candidate);
  ok = true;
  goto cleanup;

failed:
  if (candidate_ready)
    ixs_bounds_destroy(&candidate);
  ixs_arena_restore(&ctx->scratch, mark);
  facts_poison(dst);

cleanup:
  ixs_session_unbind(&binding);
  return ok;
}

static ixs_node *
facts_simplify_truncating_remainders(ixs_ctx *ctx, ixs_bounds *bounds,
                                     ixs_node *expr,
                                     ixs_fact_query_status *status);

static bool facts_simplify_preflight(ixs_facts *facts, ixs_ctx *ctx,
                                     ixs_node *expr,
                                     ixs_simplify_result *result) {
  if (!facts_ready(facts)) {
    ixs_ctx_push_error(ctx, "facts: fact set is unusable");
    result->status = IXS_FACT_QUERY_COMPLETE;
    result->value = ctx->sentinel_error;
    return true;
  }
  if (!expr) {
    result->status = IXS_FACT_QUERY_COMPLETE;
    return true;
  }
  if (!ixs_ctx_owns_node(ctx, expr)) {
    ixs_ctx_push_error(ctx, "facts: expression belongs to a different context");
    result->status = IXS_FACT_QUERY_COMPLETE;
    result->value = ctx->sentinel_error;
    return true;
  }
  if (ixs_node_is_sentinel(expr)) {
    result->status = IXS_FACT_QUERY_COMPLETE;
    result->value = expr;
    return true;
  }
  return false;
}

static ixs_simplify_result facts_query_simplify(ixs_facts *facts,
                                                ixs_node *expr) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_arena_mark mark;
  ixs_ctx *ctx;
  ixs_node *value = NULL;
  ixs_simplify_result result = {IXS_FACT_QUERY_INVALID, NULL};
  bool old_oom;
  bool limited = false;
  bool query_held = false;

  if (!facts_bind(facts, &binding, &ctx))
    return result;
  if (facts_simplify_preflight(facts, ctx, expr, &result)) {
    ixs_session_unbind(&binding);
    return result;
  }
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "simplify");
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    result.value = expr;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(&facts->bounds, expr, &query_held)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_LIMITED;
    goto cleanup;
  }

  mark = ixs_arena_save(&ctx->scratch);
  old_oom = facts->bounds.oom;
  value = simp_simplify_bounds_status(ctx, expr, &facts->bounds, &limited);
  result.status = IXS_FACT_QUERY_COMPLETE;
  if (!limited && value && !ixs_node_is_sentinel(value) &&
      ixs_node_contains_rounding(value) && ixs_node_contains_piecewise(value))
    value = facts_simplify_truncating_remainders(ctx, &facts->bounds, value,
                                                 &result.status);
  if (!limited && result.status == IXS_FACT_QUERY_COMPLETE && value &&
      !ixs_node_is_sentinel(value))
    value = simp_normalize_rational_carrier(ctx, &facts->bounds, value);
  if (limited) {
    result.status = IXS_FACT_QUERY_LIMITED;
  } else if (result.status != IXS_FACT_QUERY_COMPLETE) {
    value = NULL;
  } else if (!value || (!old_oom && facts->bounds.oom)) {
    result.status = IXS_FACT_QUERY_OOM;
    bounds_cache_clear(&facts->bounds);
  } else if (ixs_node_is_sentinel(value)) {
    result.status = IXS_FACT_QUERY_INVALID;
  } else {
    result.status = IXS_FACT_QUERY_COMPLETE;
    result.value = value;
  }
  facts->bounds.oom = old_oom;
  ixs_arena_restore(&ctx->scratch, mark);

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.value = NULL;
  ixs_session_unbind(&binding);
  return result;
}

static bool facts_simplify_batch_remainders(ixs_ctx *ctx, ixs_bounds *bounds,
                                            ixs_node **exprs, size_t n,
                                            ixs_fact_query_status *status) {
  size_t i;
  for (i = 0; i < n; i++) {
    bool query_held = false;
    ixs_fact_query_status item_status = IXS_FACT_QUERY_COMPLETE;
    if (!exprs[i] || ixs_node_is_sentinel(exprs[i]) ||
        !ixs_node_contains_rounding(exprs[i]) ||
        !ixs_node_contains_piecewise(exprs[i]))
      continue;
    if (!ixs_bounds_query_hold_begin(bounds, exprs[i], &query_held)) {
      if (bounds->oom)
        return false;
      continue;
    }
    exprs[i] = facts_simplify_truncating_remainders(ctx, bounds, exprs[i],
                                                    &item_status);
    if (query_held)
      ixs_bounds_query_hold_end(bounds);
    if (item_status != IXS_FACT_QUERY_COMPLETE) {
      *status = item_status;
      return false;
    }
    if (!exprs[i])
      return false;
  }
  return true;
}

static ixs_fact_query_status
facts_query_simplify_batch(ixs_facts *facts, ixs_node **exprs, size_t n) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_arena_mark mark;
  ixs_ctx *ctx;
  ixs_node **originals = NULL;
  bool ok;
  bool old_oom;
  bool scratch_saved = false;
  size_t i;
  ixs_fact_query_status status = IXS_FACT_QUERY_INVALID;

  if (!facts_bind(facts, &binding, &ctx))
    return status;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "simplify batch");
  if (n > 0 && !exprs) {
    ixs_ctx_push_error(ctx, "simplify batch: NULL batch with nonzero count");
    goto cleanup;
  }
  if (!facts_ready(facts)) {
    status = facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "simplify batch: fact set is unusable");
    goto cleanup;
  }
  for (i = 0; i < n; i++) {
    if (!facts_query_node_ok(ctx, exprs[i], "simplify batch"))
      goto cleanup;
  }
  if (ixs_bounds_has_empty(&facts->bounds)) {
    status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }

  mark = ixs_arena_save(&ctx->scratch);
  scratch_saved = true;
  if (n > 0) {
    originals =
        ixs_arena_alloc(&ctx->scratch, n * sizeof(*originals), sizeof(void *));
    if (!originals) {
      status = IXS_FACT_QUERY_OOM;
      goto cleanup;
    }
    memcpy(originals, exprs, n * sizeof(*originals));
  }
  old_oom = facts->bounds.oom;
  ok = simp_simplify_batch_bounds(ctx, exprs, n, &facts->bounds);
  if (ok)
    ok =
        facts_simplify_batch_remainders(ctx, &facts->bounds, exprs, n, &status);
  if (ok) {
    for (i = 0; i < n; i++) {
      exprs[i] = simp_normalize_rational_carrier(ctx, &facts->bounds, exprs[i]);
      if (!exprs[i]) {
        ok = false;
        break;
      }
    }
  }
  if (!ok || (!old_oom && facts->bounds.oom)) {
    if (status == IXS_FACT_QUERY_COMPLETE)
      status =
          bounds_query_limited_since(&facts->bounds, read_scope.limit_blocks)
              ? IXS_FACT_QUERY_LIMITED
              : IXS_FACT_QUERY_OOM;
    bounds_cache_clear(&facts->bounds);
  } else {
    status = IXS_FACT_QUERY_COMPLETE;
    for (i = 0; i < n; i++) {
      if (ixs_node_is_sentinel(exprs[i])) {
        status = IXS_FACT_QUERY_INVALID;
        break;
      }
    }
  }
  facts->bounds.oom = old_oom;

cleanup:
  status = facts_read_query_finish(&read_scope, status);
  if (status != IXS_FACT_QUERY_COMPLETE && originals)
    memcpy(exprs, originals, n * sizeof(*originals));
  if (scratch_saved)
    ixs_arena_restore(&ctx->scratch, mark);
  ixs_session_unbind(&binding);
  return status;
}

typedef struct {
  ixs_node *node;
  uint32_t next_child;
  ixs_check_result result;
  bool started;
} predicate_query_frame;

typedef struct {
  ixs_node *node;
  ixs_check_result result;
  bool active;
  bool complete;
} predicate_query_memo_entry;

typedef struct {
  predicate_query_memo_entry *entries;
  size_t count;
  size_t capacity;
} predicate_query_memo;

static bool predicate_query_memo_grow(ixs_arena *arena,
                                      predicate_query_memo *memo) {
  size_t next_capacity = memo->capacity ? memo->capacity * 2u : 32u;
  predicate_query_memo_entry *grown;
  size_t i;
  if (next_capacity <= memo->capacity ||
      next_capacity > SIZE_MAX / sizeof(*grown))
    return false;
  grown =
      ixs_arena_alloc(arena, next_capacity * sizeof(*grown), sizeof(void *));
  if (!grown)
    return false;
  memset(grown, 0, next_capacity * sizeof(*grown));
  for (i = 0; i < memo->capacity; i++) {
    predicate_query_memo_entry entry = memo->entries[i];
    size_t index;
    if (!entry.node)
      continue;
    index = entry.node->hash & (next_capacity - 1u);
    while (grown[index].node)
      index = (index + 1u) & (next_capacity - 1u);
    grown[index] = entry;
  }
  memo->entries = grown;
  memo->capacity = next_capacity;
  return true;
}

static predicate_query_memo_entry *
predicate_query_memo_get(ixs_arena *arena, predicate_query_memo *memo,
                         ixs_node *node, bool create) {
  size_t index;
  if (create && (!memo->capacity || memo->count + 1u > memo->capacity / 2u)) {
    if (!predicate_query_memo_grow(arena, memo))
      return NULL;
  }
  if (!memo->capacity)
    return NULL;
  index = node->hash & (memo->capacity - 1u);
  while (memo->entries[index].node && memo->entries[index].node != node)
    index = (index + 1u) & (memo->capacity - 1u);
  if (!memo->entries[index].node) {
    if (!create)
      return NULL;
    memo->entries[index].node = node;
    memo->count++;
  }
  return &memo->entries[index];
}

static bool predicate_query_stack_push(ixs_arena *arena,
                                       predicate_query_frame **stack,
                                       size_t *depth, size_t *capacity,
                                       ixs_node *node) {
  if (*depth == *capacity) {
    size_t next_capacity = *capacity ? *capacity * 2u : 32u;
    predicate_query_frame *grown;
    if (next_capacity <= *capacity || next_capacity > SIZE_MAX / sizeof(*grown))
      return false;
    grown = ixs_arena_grow(arena, *stack, *capacity * sizeof(*grown),
                           next_capacity * sizeof(*grown), sizeof(void *));
    if (!grown)
      return false;
    *stack = grown;
    *capacity = next_capacity;
  }
  memset(&(*stack)[*depth], 0, sizeof(**stack));
  (*stack)[*depth].node = node;
  (*depth)++;
  return true;
}

static ixs_check_result check_result_not(ixs_check_result result) {
  if (result == IXS_CHECK_TRUE)
    return IXS_CHECK_FALSE;
  if (result == IXS_CHECK_FALSE)
    return IXS_CHECK_TRUE;
  return IXS_CHECK_UNKNOWN;
}

static ixs_check_result predicate_query_cmp_atom(ixs_bounds *bounds,
                                                 ixs_node *node) {
  ixs_check_result result;

  /* A reflexive equality is the public predicate encoding for totality.
   * Do not send it through arithmetic simplification: a fact-proven domain
   * failure is a FALSE proof, not an invalid query or a diagnostic. */
  if (node->u.binary.cmp_op == IXS_CMP_EQ &&
      node->u.binary.lhs == node->u.binary.rhs)
    return ixs_bounds_check_defined(bounds, node->u.binary.lhs);
  result = ixs_bounds_check_query(bounds, node);
  if (result != IXS_CHECK_UNKNOWN || !ixs_node_is_zero(node->u.binary.rhs) ||
      !bounds_is_known_nonzero(bounds, node->u.binary.lhs))
    return result;
  if (node->u.binary.cmp_op == IXS_CMP_NE)
    return IXS_CHECK_TRUE;
  if (node->u.binary.cmp_op == IXS_CMP_EQ)
    return IXS_CHECK_FALSE;
  return result;
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
    return predicate_query_cmp_atom(bounds, node);

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
    parent->result = check_result_not(child);
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

/* An absorber determines a total result only when every retained operand is
 * defined and integer-valued. */
static bool predicate_query_assoc_domain_proven(ixs_bounds *bounds,
                                                ixs_node *node) {
  return ixs_bounds_check_defined(bounds, node) == IXS_CHECK_TRUE &&
         ixs_bounds_check_integer_valued(bounds, node) == IXS_CHECK_TRUE;
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
  ixs_check_result result;

  if (!node ||
      (node->tag != IXS_AND && node->tag != IXS_OR && node->tag != IXS_NOT))
    return predicate_query_atom(bounds, node);

  result = frame->result;
  if (predicate_query_short_circuited(frame) &&
      !predicate_query_assoc_domain_proven(bounds, node))
    result = IXS_CHECK_UNKNOWN;
  return result;
}

static ixs_check_result predicate_query_eval_detail(ixs_bounds *bounds,
                                                    ixs_node *predicate,
                                                    bool *limited) {
  ixs_arena *arena;
  ixs_arena_mark mark;
  predicate_query_frame *stack = NULL;
  predicate_query_memo memo = {0};
  predicate_query_memo_entry *entry;
  size_t depth = 0;
  size_t capacity = 0;
  ixs_check_result answer = IXS_CHECK_UNKNOWN;

  if (limited)
    *limited = false;
  if (!bounds || !predicate)
    return IXS_CHECK_UNKNOWN;
  arena = &bounds->query_arena;
  mark = ixs_arena_save(arena);
  entry = predicate_query_memo_get(arena, &memo, predicate, true);
  if (!entry || !predicate_query_stack_push(arena, &stack, &depth, &capacity,
                                            predicate)) {
    bounds->oom = true;
    goto cleanup;
  }
  entry->active = true;
  while (depth > 0) {
    predicate_query_frame *frame = &stack[depth - 1u];
    ixs_node *child = NULL;
    ixs_check_result completed;

    predicate_query_start(frame);
    child = predicate_query_next_child(frame);

    if (child) {
      entry = predicate_query_memo_get(arena, &memo, child, true);
      if (!entry) {
        bounds->oom = true;
        goto cleanup;
      }
      if (entry->active) {
        bounds_query_note_invalid(bounds->query_state);
        goto cleanup;
      }
      if (entry->complete) {
        predicate_query_fold(frame, entry->result);
        continue;
      }
      if (!predicate_query_stack_push(arena, &stack, &depth, &capacity,
                                      child)) {
        bounds->oom = true;
        goto cleanup;
      }
      entry->active = true;
      continue;
    }

    completed = predicate_query_complete(bounds, frame);
    entry = predicate_query_memo_get(arena, &memo, frame->node, false);
    if (!entry || !entry->active) {
      bounds_query_note_invalid(bounds->query_state);
      goto cleanup;
    }
    entry->active = false;
    entry->complete = true;
    entry->result = completed;
    depth--;
    if (depth == 0) {
      answer = completed;
      break;
    }
    predicate_query_fold(&stack[depth - 1u], completed);
  }

cleanup:
  ixs_arena_restore(arena, mark);
  return bounds->oom ? IXS_CHECK_UNKNOWN : answer;
}

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
  ixs_arena_mark diag_mark = ixs_arena_save(&ctx->diag);
  const char **saved_errors = ctx->errors;
  size_t saved_nerrors = ctx->nerrors;
  size_t saved_errors_cap = ctx->errors_cap;
  ixs_node *replacements[PREDICATE_FINITE_MAX_SYMBOLS];
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  size_t point;

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
    if (!evaluated || ixs_node_is_sentinel(evaluated)) {
      result = IXS_CHECK_UNKNOWN;
      if (!evaluated)
        bounds->oom = true;
      break;
    }
    if (ixs_node_is_known_true(evaluated))
      current = IXS_CHECK_TRUE;
    else if (ixs_node_is_known_false(evaluated))
      current = IXS_CHECK_FALSE;
    else {
      result = IXS_CHECK_UNKNOWN;
      break;
    }
    if (point == 0)
      result = current;
    else if (result != current) {
      result = IXS_CHECK_UNKNOWN;
      break;
    }

    for (symbol = symbol_count; symbol > 0; symbol--) {
      predicate_finite_symbol *entry = &symbols[symbol - 1u];
      if (entry->current < entry->upper) {
        entry->current++;
        break;
      }
      entry->current = entry->lower;
    }
  }
  ixs_arena_restore(&ctx->diag, diag_mark);
  ctx->errors = saved_errors;
  ctx->nerrors = saved_nerrors;
  ctx->errors_cap = saved_errors_cap;
  return bounds->oom ? IXS_CHECK_UNKNOWN : result;
}

static ixs_check_result
predicate_query_finite_domain(ixs_bounds *bounds, ixs_node *predicate,
                              size_t *remaining_points) {
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

  if (remaining_points) {
    if (point_count > *remaining_points)
      return IXS_CHECK_UNKNOWN;
    *remaining_points -= point_count;
  }
  return predicate_finite_evaluate(bounds, predicate, symbols, symbol_count,
                                   targets, point_count);
}

typedef struct {
  ixs_node *lhs;
  ixs_node *rhs;
  ixs_check_result result;
  bool active;
  bool complete;
} equivalence_memo_entry;

typedef struct {
  ixs_ctx *ctx;
  ixs_bounds *bounds;
  ixs_arena_mark memo_mark;
  equivalence_memo_entry *memo;
  size_t memo_count;
  size_t memo_capacity;
  size_t visited;
  unsigned bounded_subproof_depth;
  bool limited;
  bool invalid;
  bool oom;
  bool arithmetic_unrepresentable;
} equivalence_state;

/* Algebraic bridge rules may nest only through this fixed allowance. */
#define EQUIVALENCE_BOUNDED_SUBPROOF_DEPTH 4u

static size_t equivalence_pair_hash(ixs_node *lhs, ixs_node *rhs) {
  uintptr_t left = (uintptr_t)lhs;
  uintptr_t right = (uintptr_t)rhs;
  left >>= 3u;
  right >>= 3u;
  return (size_t)(left ^ (right + (left << 6u) + (left >> 2u)));
}

static bool equivalence_memo_grow(equivalence_state *state) {
  size_t next_capacity = state->memo_capacity ? state->memo_capacity * 2u : 32u;
  equivalence_memo_entry *grown;
  size_t i;
  if (next_capacity <= state->memo_capacity ||
      next_capacity > SIZE_MAX / sizeof(*grown))
    return false;
  grown = ixs_arena_alloc(&state->bounds->query_arena,
                          next_capacity * sizeof(*grown), sizeof(void *));
  if (!grown)
    return false;
  memset(grown, 0, next_capacity * sizeof(*grown));
  for (i = 0; i < state->memo_capacity; i++) {
    equivalence_memo_entry entry = state->memo[i];
    size_t index;
    if (!entry.lhs)
      continue;
    index = equivalence_pair_hash(entry.lhs, entry.rhs) & (next_capacity - 1u);
    while (grown[index].lhs)
      index = (index + 1u) & (next_capacity - 1u);
    grown[index] = entry;
  }
  state->memo = grown;
  state->memo_capacity = next_capacity;
  return true;
}

static equivalence_memo_entry *equivalence_memo_get(equivalence_state *state,
                                                    ixs_node *lhs,
                                                    ixs_node *rhs,
                                                    bool create) {
  size_t index;
  if (create && (!state->memo_capacity ||
                 state->memo_count + 1u > state->memo_capacity / 2u)) {
    if (!equivalence_memo_grow(state))
      return NULL;
  }
  if (!state->memo_capacity)
    return NULL;
  index = equivalence_pair_hash(lhs, rhs) & (state->memo_capacity - 1u);
  while (state->memo[index].lhs &&
         (state->memo[index].lhs != lhs || state->memo[index].rhs != rhs))
    index = (index + 1u) & (state->memo_capacity - 1u);
  if (!state->memo[index].lhs) {
    if (!create)
      return NULL;
    state->memo[index].lhs = lhs;
    state->memo[index].rhs = rhs;
    state->memo[index].result = IXS_CHECK_UNKNOWN;
    state->memo_count++;
  }
  return &state->memo[index];
}

static void equivalence_state_init(equivalence_state *state, ixs_ctx *ctx,
                                   ixs_bounds *bounds) {
  memset(state, 0, sizeof(*state));
  state->ctx = ctx;
  state->bounds = bounds;
  state->memo_mark = ixs_arena_save(&bounds->query_arena);
}

static void equivalence_state_destroy(equivalence_state *state) {
  ixs_arena_restore(&state->bounds->query_arena, state->memo_mark);
}

typedef struct {
  ixs_node *dividend;
  int64_t modulus;
  int64_t term_coeff;
  int64_t offset_p;
  int64_t offset_q;
  ixs_cmp_op op;
} equivalence_mod_cmp;

static ixs_check_result equivalence_core(equivalence_state *state,
                                         ixs_node *lhs, ixs_node *rhs,
                                         unsigned depth);
static ixs_check_result equivalence_core_impl(equivalence_state *state,
                                              ixs_node *lhs, ixs_node *rhs,
                                              unsigned depth);
static bool bounds_constant_delta_query(ixs_ctx *ctx, ixs_bounds *bounds,
                                        ixs_node *lhs, ixs_node *rhs,
                                        bool allow_expand, int64_t *delta);

static ixs_check_result equivalence_bounded_core(equivalence_state *state,
                                                 ixs_node *lhs, ixs_node *rhs,
                                                 unsigned depth) {
  ixs_check_result result;
  if (state->bounded_subproof_depth >= EQUIVALENCE_BOUNDED_SUBPROOF_DEPTH)
    return IXS_CHECK_UNKNOWN;
  state->bounded_subproof_depth++;
  result = equivalence_core(state, lhs, rhs, depth);
  state->bounded_subproof_depth--;
  return result;
}

/* Optional algebraic proof rules must not turn a valid query into a session
 * diagnostic merely because an intermediate rational cannot be represented.
 * Build their small linear intermediates directly from canonical nodes:
 * overflow is a rule miss and allocation failure remains OOM. */
typedef enum {
  EQUIVALENCE_BUILD_OK,
  EQUIVALENCE_BUILD_NO_MATCH,
  EQUIVALENCE_BUILD_OOM
} equivalence_build_status;

static ixs_node *equivalence_build_const(ixs_ctx *ctx, int64_t p, int64_t q) {
  return q == 1 ? ixs_node_int(ctx, p) : ixs_node_rat(ctx, p, q);
}

static equivalence_build_status
equivalence_build_scale_rat(equivalence_state *state, ixs_node *expr,
                            int64_t scale_p, int64_t scale_q,
                            ixs_node **result) {
  ixs_node *coefficient;
  bool unrepresentable = false;

  *result = NULL;
  if (!expr || ixs_node_is_sentinel(expr) || scale_q <= 0)
    return EQUIVALENCE_BUILD_NO_MATCH;
  coefficient = equivalence_build_const(state->ctx, scale_p, scale_q);
  if (!coefficient)
    return EQUIVALENCE_BUILD_OOM;
  *result = simp_try_mul(state->ctx, coefficient, expr, &unrepresentable);
  if (unrepresentable) {
    state->arithmetic_unrepresentable = true;
    return EQUIVALENCE_BUILD_NO_MATCH;
  }
  return *result ? EQUIVALENCE_BUILD_OK : EQUIVALENCE_BUILD_OOM;
}

static equivalence_build_status
equivalence_build_scale(equivalence_state *state, ixs_node *coefficient,
                        ixs_node *expr, ixs_node **result) {
  bool unrepresentable = false;
  if (!coefficient || !ixs_node_is_const(coefficient))
    return EQUIVALENCE_BUILD_NO_MATCH;
  *result = simp_try_mul(state->ctx, coefficient, expr, &unrepresentable);
  if (unrepresentable) {
    state->arithmetic_unrepresentable = true;
    return EQUIVALENCE_BUILD_NO_MATCH;
  }
  return *result ? EQUIVALENCE_BUILD_OK : EQUIVALENCE_BUILD_OOM;
}

static equivalence_build_status equivalence_build_add(equivalence_state *state,
                                                      ixs_node *lhs,
                                                      ixs_node *rhs,
                                                      ixs_node **result) {
  bool unrepresentable = false;
  *result = simp_try_add(state->ctx, lhs, rhs, &unrepresentable);
  if (unrepresentable) {
    state->arithmetic_unrepresentable = true;
    return EQUIVALENCE_BUILD_NO_MATCH;
  }
  if (!*result) {
    state->oom = true;
    return EQUIVALENCE_BUILD_OOM;
  }
  return EQUIVALENCE_BUILD_OK;
}

static equivalence_build_status equivalence_build_neg(equivalence_state *state,
                                                      ixs_node *expr,
                                                      ixs_node **result) {
  equivalence_build_status status =
      equivalence_build_scale_rat(state, expr, -1, 1, result);
  if (status == EQUIVALENCE_BUILD_OOM)
    state->oom = true;
  return status;
}

static equivalence_build_status equivalence_build_sub(equivalence_state *state,
                                                      ixs_node *lhs,
                                                      ixs_node *rhs,
                                                      ixs_node **result) {
  ixs_node *negative;
  equivalence_build_status status =
      equivalence_build_neg(state, rhs, &negative);
  if (status != EQUIVALENCE_BUILD_OK)
    return status;
  return equivalence_build_add(state, lhs, negative, result);
}

static equivalence_build_status
equivalence_build_div_const(equivalence_state *state, ixs_node *expr,
                            ixs_node *divisor, ixs_node **result) {
  bool unrepresentable = false;
  if (!expr || !divisor)
    return EQUIVALENCE_BUILD_NO_MATCH;
  *result = simp_try_div(state->ctx, expr, divisor, &unrepresentable);
  if (unrepresentable) {
    state->arithmetic_unrepresentable = true;
    return EQUIVALENCE_BUILD_NO_MATCH;
  }
  if (!*result) {
    state->oom = true;
    return EQUIVALENCE_BUILD_OOM;
  }
  if (ixs_node_is_sentinel(*result))
    return EQUIVALENCE_BUILD_NO_MATCH;
  return EQUIVALENCE_BUILD_OK;
}

static ixs_check_result equivalence_difference(equivalence_state *state,
                                               ixs_node *lhs, ixs_node *rhs) {
  struct ixs_node_impl nonzero;
  ixs_node *difference;
  ixs_check_result nonzero_result;
  int64_t delta;
  bool proved;
  if (equivalence_build_sub(state, lhs, rhs, &difference) !=
      EQUIVALENCE_BUILD_OK)
    return IXS_CHECK_UNKNOWN;
  proved = bounds_constant_delta_query(state->ctx, state->bounds, lhs, rhs,
                                       false, &delta);
  if (state->bounds->oom) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (proved)
    return delta == 0 ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;

  /* A variable difference need not be constant to prove that the two
   * expressions never agree.  Reuse the ordinary range, bit, and congruence
   * query for the canonical difference instead of teaching equivalence those
   * domains again. */
  if (ixs_node_is_sentinel(difference))
    return IXS_CHECK_UNKNOWN;
  memset(&nonzero, 0, sizeof(nonzero));
  nonzero.tag = IXS_CMP;
  nonzero.u.binary.lhs = difference;
  nonzero.u.binary.rhs = state->ctx->node_zero;
  nonzero.u.binary.cmp_op = IXS_CMP_NE;
  nonzero_result = ixs_bounds_check(state->bounds, &nonzero);
  if (state->bounds->oom) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (nonzero_result == IXS_CHECK_TRUE)
    return IXS_CHECK_FALSE;

  /* Integer equality is also bitwise equality.  Canonical xor cancels shared
   * subexpressions that an arithmetic difference deliberately preserves. */
  if (ixs_bounds_check_integer_valued(state->bounds, lhs) == IXS_CHECK_TRUE &&
      ixs_bounds_check_integer_valued(state->bounds, rhs) == IXS_CHECK_TRUE) {
    ixs_node *bit_difference = simp_xor(state->ctx, lhs, rhs);
    if (!bit_difference) {
      state->oom = true;
      return IXS_CHECK_UNKNOWN;
    }
    if (!ixs_node_is_sentinel(bit_difference)) {
      if (ixs_node_is_zero(bit_difference))
        return IXS_CHECK_TRUE;
      nonzero.u.binary.lhs = bit_difference;
      nonzero_result = ixs_bounds_check(state->bounds, &nonzero);
      if (state->bounds->oom) {
        state->oom = true;
        return IXS_CHECK_UNKNOWN;
      }
      if (nonzero_result == IXS_CHECK_TRUE)
        return IXS_CHECK_FALSE;
    }
  }
  return IXS_CHECK_UNKNOWN;
}

static bool equivalence_integer_delta(equivalence_state *state, ixs_node *lhs,
                                      ixs_node *rhs, int64_t *delta) {
  bool proved = bounds_constant_delta_query(state->ctx, state->bounds, lhs, rhs,
                                            true, delta);
  if (state->bounds->oom)
    state->oom = true;
  return proved && !state->oom;
}

static uint64_t bounds_scale_stride(uint64_t stride, int64_t coefficient) {
  uint64_t magnitude = bounds_int64_magnitude(coefficient);
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
  bounds_stride_frame *frames;
  size_t depth;
  size_t capacity;
  bool child_success;
  uint64_t child_stride;
} bounds_stride_query;

static bool bounds_stride_push(bounds_stride_query *query, ixs_node *expr) {
  bounds_stride_frame *grown;
  size_t capacity;
  size_t old_bytes;
  size_t new_bytes;
  if (query->depth < query->capacity) {
    memset(&query->frames[query->depth], 0, sizeof(*query->frames));
    query->frames[query->depth++].expr = expr;
    return true;
  }
  capacity = query->capacity ? query->capacity * 2u : 16u;
  if (capacity < query->capacity ||
      capacity > SIZE_MAX / sizeof(*query->frames)) {
    query->bounds->oom = true;
    return false;
  }
  old_bytes = query->capacity * sizeof(*query->frames);
  new_bytes = capacity * sizeof(*query->frames);
  grown = ixs_arena_grow(query->bounds->scratch, query->frames, old_bytes,
                         new_bytes, sizeof(void *));
  if (!grown) {
    query->bounds->oom = true;
    return false;
  }
  query->frames = grown;
  query->capacity = capacity;
  memset(&query->frames[query->depth], 0, sizeof(*query->frames));
  query->frames[query->depth++].expr = expr;
  return true;
}

static void bounds_stride_complete(bounds_stride_query *query, bool success,
                                   uint64_t stride) {
  bounds_stride_frame *frame = &query->frames[query->depth - 1u];
  if (frame->tracked) {
    bounds_query_cache_entry *entry =
        bounds_query_finish(&frame->scope, success);
    if (entry && entry->outcome == BOUNDS_QUERY_OUTCOME_VALUE)
      entry->result.stride = stride;
    else
      success = false;
  }
  query->depth--;
  query->child_success = success;
  query->child_stride = success ? stride : 0;
}

static void bounds_stride_unwind(bounds_stride_query *query) {
  while (query->depth != 0)
    bounds_stride_complete(query, false, 0);
}

typedef enum {
  BOUNDS_STRIDE_STEP_ADVANCED,
  BOUNDS_STRIDE_STEP_READY,
  BOUNDS_STRIDE_STEP_OOM
} bounds_stride_step;

static bounds_stride_step
bounds_stride_prepare_frame(bounds_stride_query *query,
                            bounds_stride_frame *frame) {
  ixs_node *node = frame->expr;
  if (!node || (node->properties & IXS_NODE_PROPERTY_VALID) == 0) {
    bounds_stride_complete(query, false, 0);
    return BOUNDS_STRIDE_STEP_ADVANCED;
  }
  if (bounds_query_should_track(query->bounds, node)) {
    bounds_query_cache_entry *cached = NULL;
    bounds_query_enter_result enter = bounds_query_begin(
        query->bounds, BOUNDS_QUERY_STRIDE, node, 0, &frame->scope, &cached);
    if (enter == BOUNDS_QUERY_ENTER_CACHED) {
      bounds_stride_complete(query, cached->success, cached->result.stride);
      return BOUNDS_STRIDE_STEP_ADVANCED;
    }
    if (enter != BOUNDS_QUERY_ENTER_STARTED) {
      bounds_stride_complete(query, false, 0);
      return BOUNDS_STRIDE_STEP_ADVANCED;
    }
    frame->tracked = true;
  }
  return BOUNDS_STRIDE_STEP_READY;
}

static bounds_stride_step bounds_stride_start_add(bounds_stride_query *query,
                                                  bounds_stride_frame *frame) {
  ixs_node *node = frame->expr;
  int64_t p;
  int64_t q;
  ixs_node_get_rat(node->u.add.coeff, &p, &q);
  (void)p;
  if (q != 1) {
    bounds_stride_complete(query, false, 0);
    return BOUNDS_STRIDE_STEP_ADVANCED;
  }
  frame->stage = BOUNDS_STRIDE_ADD;
  frame->result = 0;
  frame->index = 0;
  if (node->u.add.nterms == 0) {
    bounds_stride_complete(query, true, 0);
    return BOUNDS_STRIDE_STEP_ADVANCED;
  }
  return bounds_stride_push(query, node->u.add.terms[0].term)
             ? BOUNDS_STRIDE_STEP_ADVANCED
             : BOUNDS_STRIDE_STEP_OOM;
}

static bounds_stride_step bounds_stride_start_mul(bounds_stride_query *query,
                                                  bounds_stride_frame *frame) {
  ixs_node *node = frame->expr;
  int64_t p;
  int64_t q;
  uint32_t i;
  ixs_node_get_rat(node->u.mul.coeff, &p, &q);
  if (q != 1) {
    bounds_stride_complete(query, false, 0);
    return BOUNDS_STRIDE_STEP_ADVANCED;
  }
  if (p == 0) {
    bounds_stride_complete(query, true, 0);
    return BOUNDS_STRIDE_STEP_ADVANCED;
  }
  if (node->u.mul.nfactors == 1 && node->u.mul.factors[0].exp == 1) {
    frame->stage = BOUNDS_STRIDE_LINEAR_MUL;
    return bounds_stride_push(query, node->u.mul.factors[0].base)
               ? BOUNDS_STRIDE_STEP_ADVANCED
               : BOUNDS_STRIDE_STEP_OOM;
  }
  for (i = 0; i < node->u.mul.nfactors; i++)
    if (node->u.mul.factors[i].exp <= 0 ||
        !ixs_node_is_integer_valued(node->u.mul.factors[i].base))
      break;
  if (i != node->u.mul.nfactors) {
    bounds_stride_complete(query, true, 1);
  } else {
    uint64_t magnitude = bounds_int64_magnitude(p);
    bounds_stride_complete(query, true,
                           magnitude <= (uint64_t)INT64_MAX ? magnitude : 1);
  }
  return BOUNDS_STRIDE_STEP_ADVANCED;
}

static bounds_stride_step
bounds_stride_start_piecewise(bounds_stride_query *query,
                              bounds_stride_frame *frame) {
  ixs_node *node = frame->expr;
  if (!ixs_node_is_integer_valued(node) || !ixs_node_is_known_total(node) ||
      node->u.pw.ncases == 0 || !node->u.pw.cases) {
    bounds_stride_complete(query, false, 0);
    return BOUNDS_STRIDE_STEP_ADVANCED;
  }
  frame->stage = BOUNDS_STRIDE_PIECEWISE;
  frame->result = 0;
  frame->index = 0;
  return bounds_stride_push(query, node->u.pw.cases[0].value)
             ? BOUNDS_STRIDE_STEP_ADVANCED
             : BOUNDS_STRIDE_STEP_OOM;
}

static bounds_stride_step
bounds_stride_start_frame(bounds_stride_query *query,
                          bounds_stride_frame *frame) {
  ixs_node *node = frame->expr;
  switch (node->tag) {
  case IXS_INT:
    bounds_stride_complete(query, true, 0);
    return BOUNDS_STRIDE_STEP_ADVANCED;
  case IXS_RAT:
    bounds_stride_complete(query, node->u.rat.q == 1, 0);
    return BOUNDS_STRIDE_STEP_ADVANCED;
  case IXS_SYM: {
    int64_t modulus;
    int64_t remainder;
    uint64_t result = 1;
    if (ixs_bounds_get_modrem(query->bounds, node->u.name, &modulus,
                              &remainder)) {
      (void)remainder;
      result = (uint64_t)modulus;
    }
    bounds_stride_complete(query, !query->bounds->oom, result);
    return BOUNDS_STRIDE_STEP_ADVANCED;
  }
  case IXS_ADD:
    return bounds_stride_start_add(query, frame);
  case IXS_MUL:
    return bounds_stride_start_mul(query, frame);
  case IXS_MOD:
    if (node->u.binary.rhs->tag != IXS_INT || node->u.binary.rhs->u.ival <= 0) {
      bounds_stride_complete(query, true, 1);
      return BOUNDS_STRIDE_STEP_ADVANCED;
    }
    frame->stage = BOUNDS_STRIDE_MOD;
    return bounds_stride_push(query, node->u.binary.lhs)
               ? BOUNDS_STRIDE_STEP_ADVANCED
               : BOUNDS_STRIDE_STEP_OOM;
  case IXS_PIECEWISE:
    return bounds_stride_start_piecewise(query, frame);
  default:
    bounds_stride_complete(query, ixs_node_is_integer_valued(node), 1);
    return BOUNDS_STRIDE_STEP_ADVANCED;
  }
}

static bounds_stride_step
bounds_stride_resume_frame(bounds_stride_query *query,
                           bounds_stride_frame *frame) {
  ixs_node *node = frame->expr;
  if (!query->child_success) {
    bounds_stride_complete(query, false, 0);
    return BOUNDS_STRIDE_STEP_ADVANCED;
  }
  switch (frame->stage) {
  case BOUNDS_STRIDE_ADD: {
    int64_t p;
    int64_t q;
    ixs_node_get_rat(node->u.add.terms[frame->index].coeff, &p, &q);
    if (q != 1) {
      bounds_stride_complete(query, false, 0);
      return BOUNDS_STRIDE_STEP_ADVANCED;
    }
    frame->result = bounds_u64_gcd(frame->result,
                                   bounds_scale_stride(query->child_stride, p));
    frame->index++;
    if (frame->index == node->u.add.nterms) {
      bounds_stride_complete(query, true, frame->result);
      return BOUNDS_STRIDE_STEP_ADVANCED;
    }
    return bounds_stride_push(query, node->u.add.terms[frame->index].term)
               ? BOUNDS_STRIDE_STEP_ADVANCED
               : BOUNDS_STRIDE_STEP_OOM;
  }
  case BOUNDS_STRIDE_LINEAR_MUL: {
    int64_t p;
    int64_t q;
    ixs_node_get_rat(node->u.mul.coeff, &p, &q);
    (void)q;
    bounds_stride_complete(query, true,
                           bounds_scale_stride(query->child_stride, p));
    return BOUNDS_STRIDE_STEP_ADVANCED;
  }
  case BOUNDS_STRIDE_MOD:
    bounds_stride_complete(
        query, true,
        bounds_u64_gcd(query->child_stride,
                       (uint64_t)node->u.binary.rhs->u.ival));
    return BOUNDS_STRIDE_STEP_ADVANCED;
  case BOUNDS_STRIDE_PIECEWISE:
    frame->result = bounds_u64_gcd(frame->result, query->child_stride);
    frame->index++;
    if (frame->index == node->u.pw.ncases) {
      bounds_stride_complete(query, true, frame->result);
      return BOUNDS_STRIDE_STEP_ADVANCED;
    }
    return bounds_stride_push(query, node->u.pw.cases[frame->index].value)
               ? BOUNDS_STRIDE_STEP_ADVANCED
               : BOUNDS_STRIDE_STEP_OOM;
  case BOUNDS_STRIDE_INITIAL:
    bounds_stride_complete(query, false, 0);
    return BOUNDS_STRIDE_STEP_ADVANCED;
  }
  return BOUNDS_STRIDE_STEP_ADVANCED;
}

/* Iterative and memoized over the normalized expression DAG.  Each node and
 * immediate operand is processed once per query owner; there is no semantic
 * depth or visit ceiling and deep Piecewise trees do not consume C stack. */
static bool bounds_known_stride(ixs_bounds *bounds, ixs_node *expr,
                                uint64_t *stride) {
  ixs_arena_mark mark;
  bounds_stride_query query;
  if (!bounds || !expr || !stride || bounds->oom)
    return false;

  mark = ixs_arena_save(bounds->scratch);
  memset(&query, 0, sizeof(query));
  query.bounds = bounds;
  if (!bounds_stride_push(&query, expr))
    goto failed;

  while (query.depth != 0) {
    bounds_stride_frame *frame = &query.frames[query.depth - 1u];
    bounds_stride_step step;

    if (frame->stage == BOUNDS_STRIDE_INITIAL) {
      step = bounds_stride_prepare_frame(&query, frame);
      if (step == BOUNDS_STRIDE_STEP_READY)
        step = bounds_stride_start_frame(&query, frame);
    } else {
      step = bounds_stride_resume_frame(&query, frame);
    }
    if (step == BOUNDS_STRIDE_STEP_OOM)
      goto failed;
  }

  if (!query.child_success)
    goto failed;
  *stride = query.child_stride;
  ixs_arena_restore(bounds->scratch, mark);
  return true;

failed:
  bounds_stride_unwind(&query);
  ixs_arena_restore(bounds->scratch, mark);
  return false;
}

typedef struct {
  uint64_t magnitude;
  bool negative;
} bounds_wide_integer;

static bounds_wide_integer bounds_wide_integer_from_int64(int64_t value) {
  bounds_wide_integer result;
  result.magnitude = bounds_int64_magnitude(value);
  result.negative = value < 0;
  return result;
}

static bounds_wide_integer
bounds_wide_integer_negate(bounds_wide_integer value) {
  if (value.magnitude != 0)
    value.negative = !value.negative;
  return value;
}

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
      bounds_wide_integer_from_int64(lhs),
      bounds_wide_integer_negate(bounds_wide_integer_from_int64(rhs)), result);
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

static bool bounds_refine_integral_interval(ixs_bounds *bounds, ixs_node *expr,
                                            bool expression_defined,
                                            ixs_interval *interval) {
  ixs_interval truncating_remainder;
  bounds_truncating_range_status truncating_status;
  uint64_t stride;
  uint64_t residue;
  int64_t aligned;
  bool lower_overflow = false;
  bool upper_overflow = false;

  truncating_status = bounds_get_truncating_remainder_range(
      bounds, expr, expression_defined, &truncating_remainder);
  if (truncating_status == BOUNDS_TRUNCATING_RANGE_MATCH)
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
    if (integer_align_congruence_up(interval->lo_p, (int64_t)stride,
                                    (int64_t)residue, &aligned))
      interval->lo_p = aligned;
    else
      lower_overflow = true;
  }
  if (!interval->hi_inf) {
    if (integer_align_congruence_down(interval->hi_p, (int64_t)stride,
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
      (uint64_t)integer_congruence_residue(representative_delta, modulus);
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

static bool bounds_residue_shift_in_range(uint64_t residue, uint64_t modulus,
                                          int64_t shift) {
  uint64_t magnitude;
  if (shift >= 0) {
    uint64_t positive = (uint64_t)shift;
    return positive < modulus && residue < modulus - positive;
  }
  magnitude = bounds_int64_magnitude(shift);
  return magnitude <= residue;
}

/* If the dividend and positive divisor share a stride class, a shift which
 * stays within one stride bucket cannot cross a divisor boundary. */
static bool bounds_mod_shift_by_congruence(ixs_bounds *bounds,
                                           ixs_node *dividend,
                                           ixs_node *denominator,
                                           int64_t shift) {
  uint64_t modulus;
  uint64_t residue;
  if (!bounds_known_stride(bounds, dividend, &modulus) || modulus <= 1u ||
      modulus > (uint64_t)INT64_MAX ||
      !bounds_known_residue(bounds, dividend, modulus, &residue) ||
      ixs_bounds_check_divisible(bounds, denominator, (int64_t)modulus) !=
          IXS_CHECK_TRUE)
    return false;
  return bounds_residue_shift_in_range(residue, modulus, shift);
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
  if (bounds_exact_integer_difference(query->bounds, difference, &delta)) {
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
  bounds_equality_walk_status relation_status;
  int64_t relation_delta;
  ixs_node *difference;
  bool lhs_oom = false;
  bool rhs_oom = false;
  bool lhs_limited = false;
  bool rhs_limited = false;
  if (bounds_check_defined_detail(query->bounds, frame->lhs, &lhs_oom,
                                  &lhs_limited) != IXS_CHECK_TRUE ||
      bounds_check_defined_detail(query->bounds, frame->rhs, &rhs_oom,
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
  if (relation_status == BOUNDS_EQUALITY_WALK_VALID) {
    bounds_delta_complete(query, true, relation_delta);
    return;
  }
  if (relation_status == BOUNDS_EQUALITY_WALK_OOM) {
    query->oom = true;
    return;
  }
  if (relation_status == BOUNDS_EQUALITY_WALK_LIMITED) {
    query->limited = true;
    return;
  }
  if (relation_status == BOUNDS_EQUALITY_WALK_CONFLICT) {
    bounds_mark_contradiction(query->bounds);
    bounds_delta_complete(query, false, 0);
    return;
  }
  if (relation_status == BOUNDS_EQUALITY_WALK_INVALID) {
    query->invalid = true;
    bounds_delta_complete(query, false, 0);
    return;
  }
  difference = bounds_delta_simplify(
      query, simp_sub(query->ctx, frame->lhs, frame->rhs));
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
        !bounds_mod_shift_by_congruence(query->bounds, rhs_representative,
                                        denominator, query->child_delta))
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
                                     bool allow_expand) {
  memset(query, 0, sizeof(*query));
  query->ctx = ctx;
  query->bounds = bounds;
  query->frames = initial_frame;
  query->capacity = 1u;
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

static bool bounds_constant_delta_query_detail(ixs_ctx *ctx, ixs_bounds *bounds,
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
                                          lhs, rhs, allow_expand))
    return false;
  bounds_delta_query_run(&query);
  return bounds_delta_query_result(&query, delta, invalid, limited, oom);
}

static bool bounds_constant_delta_query(ixs_ctx *ctx, ixs_bounds *bounds,
                                        ixs_node *lhs, ixs_node *rhs,
                                        bool allow_expand, int64_t *delta) {
  return bounds_constant_delta_query_detail(ctx, bounds, lhs, rhs, allow_expand,
                                            delta, NULL, NULL, NULL);
}

static bool equivalence_no_reachable_integer(equivalence_state *state,
                                             ixs_node *expr, int64_t lo,
                                             int64_t hi) {
  ixs_interval region;
  ixs_interval known;
  uint64_t stride;
  uint64_t residue;
  if (lo > hi)
    return true;
  region = ixs_interval_range(lo, 1, hi, 1);
  known = ixs_bounds_get(state->bounds, expr);
  if (state->bounds->oom) {
    state->oom = true;
    return false;
  }
  if (known.valid) {
    region = iv_intersect(region, known);
    if (!region.valid)
      return true;
  }
  if (!bounds_known_stride(state->bounds, expr, &stride) || stride <= 1u ||
      stride > (uint64_t)INT64_MAX ||
      !bounds_known_residue(state->bounds, expr, stride, &residue)) {
    if (state->bounds->oom)
      state->oom = true;
    return false;
  }
  return !interval_has_congruent_integer(&region, (int64_t)stride,
                                         (int64_t)residue);
}

static bool equivalence_ordered_cut(ixs_cmp_op op, bool *lower,
                                    int64_t *threshold) {
  switch (op) {
  case IXS_CMP_LT:
    *lower = false;
    *threshold = -1;
    return true;
  case IXS_CMP_LE:
    *lower = false;
    *threshold = 0;
    return true;
  case IXS_CMP_GT:
    *lower = true;
    *threshold = 1;
    return true;
  case IXS_CMP_GE:
    *lower = true;
    *threshold = 0;
    return true;
  default:
    return false;
  }
}

typedef struct {
  int64_t *slots;
  size_t capacity;
  size_t count;
} equivalence_modulus_set;

static size_t equivalence_modulus_hash(int64_t modulus) {
  uint64_t x = (uint64_t)modulus;
  x ^= x >> 33;
  x *= UINT64_C(0xff51afd7ed558ccd);
  x ^= x >> 33;
  return (size_t)x;
}

/* Rehashing is amortized O(1), and storage grows only with distinct moduli in
 * the two queried expression DAGs. */
static bool equivalence_modulus_set_grow(ixs_arena *arena,
                                         equivalence_modulus_set *set) {
  size_t new_capacity = set->capacity ? set->capacity * 2u : 8u;
  int64_t *slots;
  size_t i;
  if (new_capacity <= set->capacity || new_capacity > SIZE_MAX / sizeof(*slots))
    return false;
  slots = ixs_arena_alloc(arena, new_capacity * sizeof(*slots), sizeof(void *));
  if (!slots)
    return false;
  memset(slots, 0, new_capacity * sizeof(*slots));
  for (i = 0; i < set->capacity; i++) {
    if (set->slots[i] != 0) {
      size_t index =
          equivalence_modulus_hash(set->slots[i]) & (new_capacity - 1u);
      while (slots[index] != 0)
        index = (index + 1u) & (new_capacity - 1u);
      slots[index] = set->slots[i];
    }
  }
  set->slots = slots;
  set->capacity = new_capacity;
  return true;
}

static bool equivalence_modulus_set_insert(ixs_arena *arena,
                                           equivalence_modulus_set *set,
                                           int64_t modulus) {
  size_t index;
  if (modulus <= 1)
    return true;
  if (!set->capacity || set->count >= set->capacity / 2u) {
    if (!equivalence_modulus_set_grow(arena, set))
      return false;
  }
  index = equivalence_modulus_hash(modulus) & (set->capacity - 1u);
  while (set->slots[index] != 0 && set->slots[index] != modulus)
    index = (index + 1u) & (set->capacity - 1u);
  if (set->slots[index] == modulus)
    return true;
  set->slots[index] = modulus;
  set->count++;
  return true;
}

/* Discover congruence candidates by visiting each node in the two queried
 * residual DAGs once. Growable query-local storage avoids semantic depth,
 * visit, and candidate-count cutoffs without scanning unrelated context state.
 */
static bool equivalence_collect_congruences(equivalence_state *state,
                                            ixs_node *lhs, ixs_node *rhs,
                                            equivalence_modulus_set *moduli) {
  query_node_set visited;
  ixs_node **stack = NULL;
  size_t stack_capacity = 0;
  size_t stack_count = 0;

  memset(&visited, 0, sizeof(visited));
  if (!query_node_stack_push(&state->ctx->scratch, &stack, &stack_count,
                             &stack_capacity, lhs) ||
      !query_node_stack_push(&state->ctx->scratch, &stack, &stack_count,
                             &stack_capacity, rhs))
    goto oom;
  while (stack_count > 0) {
    ixs_node *node = stack[--stack_count];
    uint32_t child_count;
    uint32_t i;
    bool inserted;
    if (!query_node_set_insert(&state->ctx->scratch, &visited, node, &inserted))
      goto oom;
    if (!inserted)
      continue;
    if (node->tag == IXS_SYM) {
      int64_t modulus;
      int64_t remainder;
      bool known = ixs_bounds_get_modrem(state->bounds, node->u.name, &modulus,
                                         &remainder);
      if (state->bounds->oom)
        goto oom;
      if (known && !equivalence_modulus_set_insert(&state->ctx->scratch, moduli,
                                                   modulus))
        goto oom;
      (void)remainder;
    }
    child_count = ixs_node_nchildren(node);
    for (i = 0; i < child_count; i++) {
      if (!query_node_stack_push(&state->ctx->scratch, &stack, &stack_count,
                                 &stack_capacity, ixs_node_child(node, i)))
        goto oom;
    }
  }
  return true;

oom:
  state->oom = true;
  return false;
}

static ixs_node *equivalence_build_rounded_ordered(equivalence_state *state,
                                                   ixs_node *cmp,
                                                   int64_t divisor) {
  ixs_node *scale = ixs_node_int(state->ctx, divisor);
  ixs_node *quotient;
  ixs_node *rounded;
  if (!scale)
    return NULL;
  quotient = simp_div(state->ctx, cmp->u.binary.lhs, scale);
  if (!quotient)
    return NULL;
  switch (cmp->u.binary.cmp_op) {
  case IXS_CMP_LT:
  case IXS_CMP_GE:
    rounded = simp_floor(state->ctx, quotient);
    break;
  case IXS_CMP_LE:
  case IXS_CMP_GT:
    rounded = simp_ceil(state->ctx, quotient);
    break;
  default:
    return cmp;
  }
  if (!rounded)
    return NULL;
  return simp_cmp(state->ctx, rounded, cmp->u.binary.cmp_op,
                  state->ctx->node_zero);
}

static ixs_check_result
equivalence_ordered_congruence_forms(equivalence_state *state, ixs_node *lhs,
                                     ixs_node *rhs) {
  ixs_arena_mark mark = ixs_arena_save(&state->ctx->scratch);
  equivalence_modulus_set moduli;
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  size_t i;

  memset(&moduli, 0, sizeof(moduli));
  if (state->oom || state->limited ||
      !equivalence_collect_congruences(state, lhs->u.binary.lhs,
                                       rhs->u.binary.lhs, &moduli))
    goto cleanup;
  for (i = 0; i < moduli.capacity; i++) {
    ixs_node *normalized[2];
    if (moduli.slots[i] == 0)
      continue;
    normalized[0] =
        equivalence_build_rounded_ordered(state, lhs, moduli.slots[i]);
    normalized[1] =
        equivalence_build_rounded_ordered(state, rhs, moduli.slots[i]);
    if (!normalized[0] || !normalized[1] ||
        !simp_simplify_batch_bounds(state->ctx, normalized, 2, state->bounds) ||
        state->bounds->oom) {
      state->oom = true;
      goto cleanup;
    }
    if (!ixs_node_is_sentinel(normalized[0]) &&
        !ixs_node_is_sentinel(normalized[1]) &&
        normalized[0] == normalized[1]) {
      result = IXS_CHECK_TRUE;
      goto cleanup;
    }
  }

cleanup:
  ixs_arena_restore(&state->ctx->scratch, mark);
  return result;
}

static ixs_check_result
equivalence_ordered_comparisons(equivalence_state *state, ixs_node *lhs,
                                ixs_node *rhs) {
  bool left_lower, right_lower;
  int64_t left_threshold, right_threshold, delta, mapped_threshold;
  int64_t lo, hi;
  if (!lhs || !rhs || lhs->tag != IXS_CMP || rhs->tag != IXS_CMP ||
      !ixs_node_is_zero(lhs->u.binary.rhs) ||
      !ixs_node_is_zero(rhs->u.binary.rhs) ||
      !equivalence_ordered_cut(lhs->u.binary.cmp_op, &left_lower,
                               &left_threshold) ||
      !equivalence_ordered_cut(rhs->u.binary.cmp_op, &right_lower,
                               &right_threshold) ||
      left_lower != right_lower ||
      ixs_bounds_check_integer_valued(state->bounds, lhs->u.binary.lhs) !=
          IXS_CHECK_TRUE ||
      ixs_bounds_check_integer_valued(state->bounds, rhs->u.binary.lhs) !=
          IXS_CHECK_TRUE)
    return IXS_CHECK_UNKNOWN;
  if (equivalence_integer_delta(state, lhs->u.binary.lhs, rhs->u.binary.lhs,
                                &delta) &&
      ixs_safe_add(right_threshold, delta, &mapped_threshold)) {
    bool cut_valid;
    if (left_threshold == mapped_threshold)
      return IXS_CHECK_TRUE;
    lo = left_threshold < mapped_threshold ? left_threshold : mapped_threshold;
    hi = left_threshold < mapped_threshold ? mapped_threshold : left_threshold;
    cut_valid =
        left_lower ? ixs_safe_sub(hi, 1, &hi) : ixs_safe_add(lo, 1, &lo);
    if (cut_valid &&
        equivalence_no_reachable_integer(state, lhs->u.binary.lhs, lo, hi))
      return IXS_CHECK_TRUE;
  }
  return equivalence_ordered_congruence_forms(state, lhs, rhs);
}

static bool equivalence_extract_mod_sum(ixs_node *expr, ixs_node **dividend,
                                        ixs_node **denominator,
                                        int64_t *offset) {
  ixs_node *mod;
  int64_t cp, cq, kp, kq;
  if (expr->tag == IXS_MOD) {
    mod = expr;
    *offset = 0;
  } else if (expr->tag == IXS_ADD && expr->u.add.nterms == 1u &&
             expr->u.add.terms[0].term->tag == IXS_MOD) {
    ixs_node_get_rat(expr->u.add.terms[0].coeff, &cp, &cq);
    ixs_node_get_rat(expr->u.add.coeff, &kp, &kq);
    if (cp != 1 || cq != 1 || kq != 1)
      return false;
    mod = expr->u.add.terms[0].term;
    *offset = kp;
  } else {
    return false;
  }
  *dividend = mod->u.binary.lhs;
  *denominator = mod->u.binary.rhs;
  return true;
}

static bool equivalence_proves_zero_cmp(equivalence_state *state, ixs_node *lhs,
                                        ixs_cmp_op op) {
  struct ixs_node_impl cmp;
  bool result;
  memset(&cmp, 0, sizeof(cmp));
  cmp.tag = IXS_CMP;
  cmp.u.binary.lhs = lhs;
  cmp.u.binary.rhs = state->ctx->node_zero;
  cmp.u.binary.cmp_op = op;
  result = ixs_bounds_check(state->bounds, &cmp) == IXS_CHECK_TRUE;
  if (state->bounds->oom)
    state->oom = true;
  return result;
}

static bool equivalence_mod_sum_in_range(equivalence_state *state,
                                         ixs_node *sum, ixs_node *denominator) {
  ixs_node *upper;
  if (!equivalence_proves_zero_cmp(state, denominator, IXS_CMP_GT))
    return false;
  upper = simp_sub(state->ctx, sum, denominator);
  if (!upper) {
    state->oom = true;
    return false;
  }
  if (ixs_node_is_sentinel(upper))
    return false;
  return equivalence_proves_zero_cmp(state, sum, IXS_CMP_GE) &&
         equivalence_proves_zero_cmp(state, upper, IXS_CMP_LT);
}

static bool equivalence_mod_shift_by_congruence(equivalence_state *state,
                                                ixs_node *dividend,
                                                ixs_node *denominator,
                                                int64_t shift) {
  if (!equivalence_proves_zero_cmp(state, denominator, IXS_CMP_GT) ||
      !bounds_mod_shift_by_congruence(state->bounds, dividend, denominator,
                                      shift)) {
    if (state->bounds->oom)
      state->oom = true;
    return false;
  }
  return true;
}

static ixs_check_result
equivalence_mod_shift_direction(equivalence_state *state, ixs_node *shifted,
                                ixs_node *sum) {
  ixs_node *shifted_dividend;
  ixs_node *shifted_denominator;
  ixs_node *base_dividend;
  ixs_node *base_denominator;
  int64_t sum_offset;
  int64_t dividend_shift;
  if (shifted->tag != IXS_MOD ||
      !equivalence_extract_mod_sum(shifted, &shifted_dividend,
                                   &shifted_denominator, &dividend_shift) ||
      dividend_shift != 0 ||
      !equivalence_extract_mod_sum(sum, &base_dividend, &base_denominator,
                                   &sum_offset) ||
      shifted_denominator != base_denominator ||
      !equivalence_integer_delta(state, shifted_dividend, base_dividend,
                                 &dividend_shift) ||
      dividend_shift != sum_offset ||
      ixs_bounds_check_integer_valued(state->bounds, base_dividend) !=
          IXS_CHECK_TRUE ||
      ixs_bounds_check_integer_valued(state->bounds, base_denominator) !=
          IXS_CHECK_TRUE)
    return IXS_CHECK_UNKNOWN;
  if (equivalence_mod_sum_in_range(state, sum, base_denominator) ||
      equivalence_mod_shift_by_congruence(state, base_dividend,
                                          base_denominator, sum_offset))
    return IXS_CHECK_TRUE;
  return IXS_CHECK_UNKNOWN;
}

static ixs_check_result equivalence_mod_shifts(equivalence_state *state,
                                               ixs_node *lhs, ixs_node *rhs) {
  ixs_check_result result = equivalence_mod_shift_direction(state, lhs, rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  return equivalence_mod_shift_direction(state, rhs, lhs);
}

static bool equivalence_extract_positive_scaled_mod(equivalence_state *state,
                                                    ixs_node *expr,
                                                    int64_t *scale,
                                                    ixs_node **mod,
                                                    ixs_node **residual) {
  int64_t p;
  int64_t q;
  ixs_node *scaled;
  uint32_t i;

  *residual = state->ctx->node_zero;
  if (expr->tag == IXS_MUL && expr->u.mul.nfactors == 1u &&
      expr->u.mul.factors[0].exp == 1 &&
      expr->u.mul.factors[0].base->tag == IXS_MOD) {
    ixs_node_get_rat(expr->u.mul.coeff, &p, &q);
    if (q != 1 || p <= 1)
      return false;
    *scale = p;
    *mod = expr->u.mul.factors[0].base;
    return true;
  }
  if (expr->tag != IXS_ADD)
    return false;
  *mod = NULL;
  for (i = 0; i < expr->u.add.nterms; i++) {
    if (expr->u.add.terms[i].term->tag != IXS_MOD)
      continue;
    ixs_node_get_rat(expr->u.add.terms[i].coeff, &p, &q);
    if (q != 1 || p <= 1 || *mod)
      return false;
    *scale = p;
    *mod = expr->u.add.terms[i].term;
  }
  if (!*mod)
    return false;
  if (equivalence_build_scale_rat(state, *mod, *scale, 1, &scaled) !=
          EQUIVALENCE_BUILD_OK ||
      equivalence_build_sub(state, expr, scaled, residual) !=
          EQUIVALENCE_BUILD_OK)
    return false;
  return !ixs_node_is_sentinel(scaled) && !ixs_node_is_sentinel(*residual);
}

static bool equivalence_accumulate_scaled_part(equivalence_state *state,
                                               ixs_node **sum,
                                               ixs_node *coefficient,
                                               ixs_node *term) {
  ixs_node *part = coefficient;
  ixs_node *next;
  if ((term && equivalence_build_scale(state, coefficient, term, &part) !=
                   EQUIVALENCE_BUILD_OK) ||
      equivalence_build_add(state, *sum, part, &next) != EQUIVALENCE_BUILD_OK)
    return false;
  if (ixs_node_is_sentinel(part) || ixs_node_is_sentinel(next))
    return false;
  *sum = next;
  return true;
}

/* Split a canonical sum into terms whose integer coefficients contain scale
 * and the remaining residue.  This is deliberately structural: a residual
 * that merely happens to agree at sampled points cannot be manufactured. */
static bool equivalence_partition_scaled_sum(equivalence_state *state,
                                             ixs_node *expr, int64_t scale,
                                             ixs_node **quotient,
                                             ixs_node **residual) {
  int64_t p;
  int64_t q;
  int64_t scaled_p;
  int64_t residual_p;
  uint32_t i;

  if (expr->tag != IXS_ADD)
    return false;
  *quotient = state->ctx->node_zero;
  *residual = state->ctx->node_zero;
  ixs_node_get_rat(expr->u.add.coeff, &p, &q);
  if (q == 1) {
    scaled_p = p / scale;
    residual_p = p % scale;
    if (residual_p < 0) {
      residual_p += scale;
      scaled_p--;
    }
    if (scaled_p != 0 &&
        !equivalence_accumulate_scaled_part(
            state, quotient, ixs_node_int(state->ctx, scaled_p), NULL))
      return false;
    if (residual_p != 0 &&
        !equivalence_accumulate_scaled_part(
            state, residual, ixs_node_int(state->ctx, residual_p), NULL))
      return false;
  } else if (!equivalence_accumulate_scaled_part(state, residual,
                                                 expr->u.add.coeff, NULL)) {
    return false;
  }
  for (i = 0; i < expr->u.add.nterms; i++) {
    ixs_node *coefficient = expr->u.add.terms[i].coeff;
    ixs_node *term = expr->u.add.terms[i].term;
    ixs_node_get_rat(coefficient, &p, &q);
    if (q == 1) {
      scaled_p = p / scale;
      residual_p = p % scale;
      if (residual_p < 0) {
        residual_p += scale;
        scaled_p--;
      }
      if (scaled_p != 0 &&
          !equivalence_accumulate_scaled_part(
              state, quotient, ixs_node_int(state->ctx, scaled_p), term))
        return false;
      if (residual_p != 0 &&
          !equivalence_accumulate_scaled_part(
              state, residual, ixs_node_int(state->ctx, residual_p), term))
        return false;
    } else if (!equivalence_accumulate_scaled_part(state, residual, coefficient,
                                                   term)) {
      return false;
    }
  }
  return true;
}

/* Prove g*Mod(a,m) == Mod(b,d) by projecting the latter through the exact
 * positive integer scale g when b/g and d/g are integer-valued. */
static ixs_check_result
equivalence_scaled_mod_direction(equivalence_state *state, ixs_node *scaled,
                                 ixs_node *wrapped, unsigned depth) {
  int64_t scale;
  ixs_node *inner;
  ixs_node *scale_node;
  ixs_node *dividend;
  ixs_node *denominator;
  ixs_node *projected;
  ixs_node *residual;
  ixs_node *wrapped_residual;
  if (!equivalence_extract_positive_scaled_mod(state, scaled, &scale, &inner,
                                               &residual) ||
      wrapped->tag != IXS_MOD ||
      !equivalence_proves_zero_cmp(state, wrapped->u.binary.rhs, IXS_CMP_GT))
    return IXS_CHECK_UNKNOWN;
  scale_node = ixs_node_int(state->ctx, scale);
  if (!scale_node) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (ixs_node_is_zero(residual)) {
    if (equivalence_build_div_const(state, wrapped->u.binary.lhs, scale_node,
                                    &dividend) != EQUIVALENCE_BUILD_OK)
      return IXS_CHECK_UNKNOWN;
  } else {
    ixs_check_result shared;
    if (ixs_bounds_check_integer_valued(state->bounds, residual) !=
            IXS_CHECK_TRUE ||
        !equivalence_mod_sum_in_range(state, residual, scale_node) ||
        !equivalence_partition_scaled_sum(state, wrapped->u.binary.lhs, scale,
                                          &dividend, &wrapped_residual) ||
        ixs_bounds_check_integer_valued(state->bounds, wrapped_residual) !=
            IXS_CHECK_TRUE) {
      if (state->bounds->oom)
        state->oom = true;
      return IXS_CHECK_UNKNOWN;
    }
    shared = residual == wrapped_residual
                 ? IXS_CHECK_TRUE
                 : equivalence_bounded_core(state, residual, wrapped_residual,
                                            depth + 1u);
    if (shared != IXS_CHECK_TRUE)
      return IXS_CHECK_UNKNOWN;
  }
  denominator = NULL;
  if (scale_node &&
      equivalence_build_div_const(state, wrapped->u.binary.rhs, scale_node,
                                  &denominator) != EQUIVALENCE_BUILD_OK)
    return IXS_CHECK_UNKNOWN;
  if (!scale_node || !dividend || !denominator) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (ixs_node_is_sentinel(dividend) || ixs_node_is_sentinel(denominator) ||
      ixs_bounds_check_integer_valued(state->bounds, dividend) !=
          IXS_CHECK_TRUE ||
      ixs_bounds_check_integer_valued(state->bounds, denominator) !=
          IXS_CHECK_TRUE)
    return IXS_CHECK_UNKNOWN;
  projected = simp_mod(state->ctx, dividend, denominator);
  if (!projected) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (ixs_node_is_sentinel(projected))
    return IXS_CHECK_UNKNOWN;
  return equivalence_bounded_core(state, inner, projected, depth + 1u);
}

static ixs_check_result equivalence_scaled_mods(equivalence_state *state,
                                                ixs_node *lhs, ixs_node *rhs,
                                                unsigned depth) {
  ixs_check_result result =
      equivalence_scaled_mod_direction(state, lhs, rhs, depth);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  return equivalence_scaled_mod_direction(state, rhs, lhs, depth);
}

static bool equivalence_extract_linear_mod(ixs_node *difference, ixs_node **mod,
                                           ixs_node **coefficient) {
  uint32_t i;

  *mod = NULL;
  *coefficient = NULL;
  if (difference->tag == IXS_MOD) {
    *mod = difference;
    return true;
  }
  if (difference->tag == IXS_MUL && difference->u.mul.nfactors == 1u &&
      difference->u.mul.factors[0].exp == 1 &&
      difference->u.mul.factors[0].base->tag == IXS_MOD) {
    *mod = difference->u.mul.factors[0].base;
    *coefficient = difference->u.mul.coeff;
    return true;
  }
  if (difference->tag != IXS_ADD)
    return false;
  for (i = 0; i < difference->u.add.nterms; i++) {
    if (difference->u.add.terms[i].term->tag != IXS_MOD)
      continue;
    if (*mod)
      return false;
    *mod = difference->u.add.terms[i].term;
    *coefficient = difference->u.add.terms[i].coeff;
  }
  return *mod != NULL;
}

static ixs_check_result equivalence_isolate_unit_mod(equivalence_state *state,
                                                     ixs_node *difference,
                                                     unsigned depth) {
  ixs_node *mod = NULL;
  ixs_node *coefficient = NULL;
  ixs_node *mod_term;
  ixs_node *rest;
  ixs_node *candidate;
  int64_t sign = 0;
  uint32_t i;

  if (difference->tag != IXS_ADD)
    return IXS_CHECK_UNKNOWN;
  for (i = 0; i < difference->u.add.nterms; i++) {
    ixs_node *term = difference->u.add.terms[i].term;
    ixs_node *term_coefficient = difference->u.add.terms[i].coeff;
    int64_t p;
    int64_t q;

    if (term->tag != IXS_MOD)
      continue;
    ixs_node_get_rat(term_coefficient, &p, &q);
    if (q != 1 || (p != 1 && p != -1))
      continue;
    if (mod)
      return IXS_CHECK_UNKNOWN;
    mod = term;
    coefficient = term_coefficient;
    sign = p;
  }
  if (!mod)
    return IXS_CHECK_UNKNOWN;
  if (equivalence_build_scale(state, coefficient, mod, &mod_term) !=
          EQUIVALENCE_BUILD_OK ||
      equivalence_build_sub(state, difference, mod_term, &rest) !=
          EQUIVALENCE_BUILD_OK)
    return IXS_CHECK_UNKNOWN;
  candidate = rest;
  if (sign == 1 &&
      equivalence_build_neg(state, rest, &candidate) != EQUIVALENCE_BUILD_OK)
    return IXS_CHECK_UNKNOWN;
  if (ixs_node_is_sentinel(mod_term) || ixs_node_is_sentinel(rest) ||
      ixs_node_is_sentinel(candidate) ||
      ixs_bounds_check_defined(state->bounds, candidate) != IXS_CHECK_TRUE ||
      ixs_bounds_check_defined(state->bounds, mod) != IXS_CHECK_TRUE) {
    if (state->bounds->oom)
      state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  return equivalence_bounded_core(state, candidate, mod, depth + 1u);
}

static ixs_node *equivalence_simplified_difference(equivalence_state *state,
                                                   ixs_node *lhs,
                                                   ixs_node *rhs) {
  ixs_node *difference;
  ixs_node *expanded;
  bool limited = false;

  if (equivalence_build_sub(state, lhs, rhs, &difference) !=
      EQUIVALENCE_BUILD_OK)
    return NULL;
  expanded = expand_impl(state->ctx, difference);
  if (!expanded) {
    state->oom = true;
    return NULL;
  }
  if (ixs_node_is_sentinel(difference) || ixs_node_is_sentinel(expanded))
    return NULL;
  difference = simp_simplify_bounds_status(state->ctx, expanded, state->bounds,
                                           &limited);
  if (limited) {
    state->limited = true;
    return NULL;
  }
  if (!difference) {
    state->oom = true;
    return NULL;
  }
  return ixs_node_is_sentinel(difference) ? NULL : difference;
}

/* For a positive integer m, c*Mod(x,m)+rest == 0 iff
 * floor(x/m) == (c*x+rest)/(c*m).  Solve only this linear identity and hand
 * the quotient equality back to the ordinary fact-backed equivalence engine.
 * This is structural proof composition, not finite-domain evaluation. */
static ixs_check_result
equivalence_mod_quotient_identity(equivalence_state *state, ixs_node *lhs,
                                  ixs_node *rhs, unsigned depth) {
  ixs_node *difference;
  ixs_node *mod;
  ixs_node *coefficient;
  ixs_node *mod_term;
  ixs_node *rest;
  ixs_node *scaled_dividend;
  ixs_node *numerator;
  ixs_node *denominator;
  ixs_node *quotient_arg;
  ixs_node *quotient;
  ixs_node *required;
  int64_t coefficient_p;
  int64_t coefficient_q;
  int64_t denominator_p;
  int64_t denominator_q;

  if (depth != 0u)
    return IXS_CHECK_UNKNOWN;
  difference = equivalence_simplified_difference(state, lhs, rhs);
  if (!difference)
    return IXS_CHECK_UNKNOWN;
  if (equivalence_isolate_unit_mod(state, difference, depth) == IXS_CHECK_TRUE)
    return IXS_CHECK_TRUE;
  if (!equivalence_extract_linear_mod(difference, &mod, &coefficient) ||
      mod->u.binary.rhs->tag != IXS_INT || mod->u.binary.rhs->u.ival <= 0 ||
      ixs_bounds_check_defined(state->bounds, mod) != IXS_CHECK_TRUE ||
      ixs_bounds_check_integer_valued(state->bounds, mod->u.binary.lhs) !=
          IXS_CHECK_TRUE) {
    if (state->bounds->oom)
      state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (!coefficient)
    coefficient = state->ctx->node_one;
  ixs_node_get_rat(coefficient, &coefficient_p, &coefficient_q);
  if (!ixs_rat_mul(coefficient_p, coefficient_q, mod->u.binary.rhs->u.ival, 1,
                   &denominator_p, &denominator_q))
    return IXS_CHECK_UNKNOWN;
  if (equivalence_build_scale(state, coefficient, mod, &mod_term) !=
          EQUIVALENCE_BUILD_OK ||
      equivalence_build_sub(state, difference, mod_term, &rest) !=
          EQUIVALENCE_BUILD_OK ||
      equivalence_build_scale(state, coefficient, mod->u.binary.lhs,
                              &scaled_dividend) != EQUIVALENCE_BUILD_OK ||
      equivalence_build_add(state, rest, scaled_dividend, &numerator) !=
          EQUIVALENCE_BUILD_OK)
    return IXS_CHECK_UNKNOWN;
  denominator =
      equivalence_build_const(state->ctx, denominator_p, denominator_q);
  if (!denominator) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (equivalence_build_div_const(state, numerator, denominator, &required) !=
          EQUIVALENCE_BUILD_OK ||
      equivalence_build_div_const(state, mod->u.binary.lhs, mod->u.binary.rhs,
                                  &quotient_arg) != EQUIVALENCE_BUILD_OK)
    return IXS_CHECK_UNKNOWN;
  quotient = simp_floor(state->ctx, quotient_arg);
  if (!quotient) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (ixs_node_is_sentinel(rest) || ixs_node_is_sentinel(required) ||
      ixs_node_is_sentinel(quotient))
    return IXS_CHECK_UNKNOWN;
  return equivalence_core(state, quotient, required, depth + 1u);
}

typedef struct {
  ixs_node *target;
  ixs_node *replacement;
} equivalence_substitution;

typedef struct {
  equivalence_substitution *items;
  size_t count;
  size_t capacity;
} equivalence_substitutions;

static bool
equivalence_substitutions_push(ixs_arena *arena,
                               equivalence_substitutions *substitutions,
                               ixs_node *target, ixs_node *replacement) {
  if (substitutions->count >= substitutions->capacity) {
    size_t new_capacity = substitutions->capacity ? substitutions->capacity * 2u
                                                  : FACT_WORK_INIT_CAP;
    equivalence_substitution *grown;
    if (new_capacity <= substitutions->capacity ||
        new_capacity > SIZE_MAX / sizeof(*substitutions->items))
      return false;
    grown = ixs_arena_grow(
        arena, substitutions->items,
        substitutions->capacity * sizeof(*substitutions->items),
        new_capacity * sizeof(*substitutions->items), sizeof(void *));
    if (!grown)
      return false;
    substitutions->items = grown;
    substitutions->capacity = new_capacity;
  }
  substitutions->items[substitutions->count].target = target;
  substitutions->items[substitutions->count].replacement = replacement;
  substitutions->count++;
  return true;
}

static bool query_node_set_contains(const query_node_set *set, ixs_node *node) {
  size_t index;
  if (!set->capacity)
    return false;
  index = node->hash & (set->capacity - 1u);
  while (set->slots[index] && set->slots[index] != node)
    index = (index + 1u) & (set->capacity - 1u);
  return set->slots[index] != NULL;
}

static bool equivalence_remainder_domain_proven(equivalence_state *state,
                                                ixs_node *node) {
  bool proven = ixs_bounds_check_defined(state->bounds, node) == IXS_CHECK_TRUE;
  if (state->bounds->oom)
    state->oom = true;
  return proven;
}

static bool equivalence_remainder_integer_proven(equivalence_state *state,
                                                 ixs_node *node) {
  bool proven =
      ixs_bounds_check_integer_valued(state->bounds, node) == IXS_CHECK_TRUE;
  if (state->bounds->oom)
    state->oom = true;
  return proven;
}

static bool equivalence_build_same_sign(equivalence_state *state,
                                        ixs_node *numerator,
                                        ixs_node *denominator,
                                        ixs_node **same_sign) {
  ixs_node *numerator_nonnegative =
      simp_cmp(state->ctx, numerator, IXS_CMP_GE, state->ctx->node_zero);
  ixs_node *numerator_nonpositive =
      simp_cmp(state->ctx, numerator, IXS_CMP_LE, state->ctx->node_zero);
  ixs_node *denominator_positive =
      simp_cmp(state->ctx, denominator, IXS_CMP_GT, state->ctx->node_zero);
  ixs_node *denominator_negative =
      simp_cmp(state->ctx, denominator, IXS_CMP_LT, state->ctx->node_zero);
  ixs_node *both_nonnegative;
  ixs_node *both_nonpositive;
  if (!numerator_nonnegative || !numerator_nonpositive ||
      !denominator_positive || !denominator_negative) {
    state->oom = true;
    return false;
  }
  if (ixs_node_is_sentinel(numerator_nonnegative) ||
      ixs_node_is_sentinel(numerator_nonpositive) ||
      ixs_node_is_sentinel(denominator_positive) ||
      ixs_node_is_sentinel(denominator_negative))
    return false;
  both_nonnegative =
      simp_and(state->ctx, numerator_nonnegative, denominator_positive);
  both_nonpositive =
      simp_and(state->ctx, numerator_nonpositive, denominator_negative);
  if (!both_nonnegative || !both_nonpositive) {
    state->oom = true;
    return false;
  }
  if (ixs_node_is_sentinel(both_nonnegative) ||
      ixs_node_is_sentinel(both_nonpositive))
    return false;
  *same_sign = simp_or(state->ctx, both_nonnegative, both_nonpositive);
  if (!*same_sign) {
    state->oom = true;
    return false;
  }
  return !ixs_node_is_sentinel(*same_sign);
}

static bool equivalence_split_affine_round(equivalence_state *state,
                                           ixs_node *value, ixs_tag tag,
                                           ixs_node **argument,
                                           ixs_node **residual) {
  ixs_node *round = NULL;
  uint32_t i;
  if (value->tag == tag) {
    *argument = value->u.unary.arg;
    *residual = state->ctx->node_zero;
    return true;
  }
  if (value->tag != IXS_ADD)
    return false;
  for (i = 0; i < value->u.add.nterms; i++) {
    ixs_node *term = value->u.add.terms[i].term;
    int64_t p;
    int64_t q;
    ixs_node_get_rat(value->u.add.terms[i].coeff, &p, &q);
    if (term->tag != tag || p != 1 || q != 1)
      continue;
    if (round)
      return false;
    round = term;
  }
  if (!round)
    return false;
  *argument = round->u.unary.arg;
  if (equivalence_build_sub(state, value, round, residual) !=
      EQUIVALENCE_BUILD_OK)
    return false;
  return !ixs_node_is_sentinel(*residual);
}

static bool equivalence_match_piecewise_truncating_round(
    equivalence_state *state, ixs_node *node, unsigned depth,
    ixs_node **quotient, bool *matched) {
  ixs_node *floor_argument;
  ixs_node *floor_residual;
  ixs_node *ceil_argument;
  ixs_node *ceil_residual;
  ixs_node *same_sign;
  ixs_node *numerator;
  ixs_node *denominator;
  ixs_node *argument;
  ixs_quotient_parts_status quotient_status;
  ixs_check_result guard_equivalent;
  /* Guard matching is an optional proof refinement. Restrict it to the outer
   * equivalence query so the one nested subproof below is a static C recursion
   * boundary rather than a function of expression depth. */
  if (depth != 0u || node->u.pw.ncases != 2u ||
      !ixs_node_is_known_true(node->u.pw.cases[1].cond))
    return true;
  if (!equivalence_split_affine_round(state, node->u.pw.cases[0].value,
                                      IXS_FLOOR, &floor_argument,
                                      &floor_residual) ||
      !equivalence_split_affine_round(state, node->u.pw.cases[1].value,
                                      IXS_CEIL, &ceil_argument, &ceil_residual))
    return !state->oom;
  if (floor_argument != ceil_argument || floor_residual != ceil_residual ||
      !equivalence_remainder_domain_proven(state, floor_residual) ||
      !equivalence_remainder_integer_proven(state, floor_residual))
    return true;
  if (equivalence_build_add(state, floor_argument, floor_residual, &argument) !=
          EQUIVALENCE_BUILD_OK ||
      ixs_node_is_sentinel(argument))
    return true;
  quotient_status = simp_decompose_exact_quotient(state->ctx, argument,
                                                  &numerator, &denominator);
  if (quotient_status == IXS_QUOTIENT_PARTS_OOM) {
    state->oom = true;
    return false;
  }
  if (quotient_status != IXS_QUOTIENT_PARTS_MATCH ||
      !equivalence_build_same_sign(state, numerator, denominator, &same_sign))
    return !state->oom;
  if (!equivalence_remainder_domain_proven(state, node->u.pw.cases[0].cond) ||
      !equivalence_remainder_domain_proven(state, same_sign))
    return !state->oom;
  guard_equivalent =
      equivalence_core(state, node->u.pw.cases[0].cond, same_sign, depth + 1u);
  if (guard_equivalent != IXS_CHECK_TRUE)
    return true;
  *quotient = argument;
  *matched = true;
  return true;
}

static bool equivalence_match_truncating_round(equivalence_state *state,
                                               ixs_node *node, unsigned depth,
                                               ixs_node **quotient,
                                               bool *matched) {
  ixs_node *argument;
  *matched = false;
  if (node->tag == IXS_TRUNC) {
    *quotient = node->u.unary.arg;
    *matched = true;
    return true;
  }
  if (node->tag == IXS_FLOOR || node->tag == IXS_CEIL) {
    argument = node->u.unary.arg;
    if ((node->tag == IXS_FLOOR &&
         !equivalence_proves_zero_cmp(state, argument, IXS_CMP_GE)) ||
        (node->tag == IXS_CEIL &&
         !equivalence_proves_zero_cmp(state, argument, IXS_CMP_LE)))
      return true;
    *quotient = argument;
    *matched = true;
    return true;
  }
  if (node->tag == IXS_PIECEWISE)
    return equivalence_match_piecewise_truncating_round(state, node, depth,
                                                        quotient, matched);
  return true;
}

static bool equivalence_truncating_parts_proven(equivalence_state *state,
                                                ixs_node *node,
                                                ixs_node *quotient,
                                                ixs_node *numerator,
                                                ixs_node *denominator) {
  return equivalence_remainder_domain_proven(state, node) &&
         equivalence_remainder_domain_proven(state, quotient) &&
         equivalence_remainder_domain_proven(state, numerator) &&
         equivalence_remainder_domain_proven(state, denominator) &&
         equivalence_remainder_integer_proven(state, numerator) &&
         equivalence_remainder_integer_proven(state, denominator);
}

static bool equivalence_build_nonnegative_remainder(equivalence_state *state,
                                                    ixs_node *numerator,
                                                    ixs_node *denominator,
                                                    bool denominator_positive,
                                                    bool denominator_negative,
                                                    ixs_node **remainder) {
  ixs_node *negative_denominator;
  ixs_node *absolute_denominator;

  if (denominator_positive) {
    *remainder = simp_mod(state->ctx, numerator, denominator);
  } else {
    if (equivalence_build_neg(state, denominator, &negative_denominator) !=
            EQUIVALENCE_BUILD_OK ||
        ixs_node_is_sentinel(negative_denominator))
      return false;
    if (denominator_negative) {
      *remainder = simp_mod(state->ctx, numerator, negative_denominator);
    } else {
      absolute_denominator =
          simp_max(state->ctx, denominator, negative_denominator);
      if (!absolute_denominator) {
        state->oom = true;
        return false;
      }
      if (ixs_node_is_sentinel(absolute_denominator))
        return false;
      *remainder = simp_mod(state->ctx, numerator, absolute_denominator);
    }
  }
  if (!*remainder) {
    state->oom = true;
    return false;
  }
  return !ixs_node_is_sentinel(*remainder) &&
         equivalence_remainder_domain_proven(state, *remainder) &&
         equivalence_remainder_integer_proven(state, *remainder);
}

static bool equivalence_build_signed_remainder(equivalence_state *state,
                                               ixs_node *numerator,
                                               ixs_node *denominator,
                                               ixs_node **remainder) {
  ixs_node *numerator_nonnegative_cmp;
  ixs_node *positive_modulo;
  ixs_node *negative_numerator;
  ixs_node *negative_modulo;
  ixs_node *negative_remainder;
  ixs_node *values[2];
  ixs_node *conditions[2];
  bool numerator_nonnegative =
      equivalence_proves_zero_cmp(state, numerator, IXS_CMP_GE);
  bool numerator_nonpositive;
  bool denominator_positive;
  bool denominator_negative;

  numerator_nonpositive =
      !numerator_nonnegative &&
      equivalence_proves_zero_cmp(state, numerator, IXS_CMP_LE);
  denominator_positive =
      equivalence_proves_zero_cmp(state, denominator, IXS_CMP_GT);
  denominator_negative =
      !denominator_positive &&
      equivalence_proves_zero_cmp(state, denominator, IXS_CMP_LT);

  if (numerator_nonnegative) {
    if (!equivalence_build_nonnegative_remainder(
            state, numerator, denominator, denominator_positive,
            denominator_negative, remainder))
      return false;
  } else {
    if (equivalence_build_neg(state, numerator, &negative_numerator) !=
            EQUIVALENCE_BUILD_OK ||
        ixs_node_is_sentinel(negative_numerator))
      return false;
    if (!equivalence_build_nonnegative_remainder(
            state, negative_numerator, denominator, denominator_positive,
            denominator_negative, &negative_modulo))
      return false;
    if (equivalence_build_neg(state, negative_modulo, &negative_remainder) !=
            EQUIVALENCE_BUILD_OK ||
        ixs_node_is_sentinel(negative_remainder))
      return false;
    if (numerator_nonpositive) {
      *remainder = negative_remainder;
    } else {
      if (!equivalence_build_nonnegative_remainder(
              state, numerator, denominator, denominator_positive,
              denominator_negative, &positive_modulo))
        return false;
      numerator_nonnegative_cmp =
          simp_cmp(state->ctx, numerator, IXS_CMP_GE, state->ctx->node_zero);
      if (!positive_modulo || !numerator_nonnegative_cmp) {
        state->oom = true;
        return false;
      }
      if (ixs_node_is_sentinel(positive_modulo) ||
          ixs_node_is_sentinel(numerator_nonnegative_cmp))
        return false;
      values[0] = positive_modulo;
      values[1] = negative_remainder;
      conditions[0] = numerator_nonnegative_cmp;
      conditions[1] = state->ctx->node_true;
      *remainder = simp_pw(state->ctx, 2u, values, conditions);
    }
  }
  if (!*remainder) {
    state->oom = true;
    return false;
  }
  if (ixs_node_is_sentinel(*remainder))
    return false;
  return equivalence_remainder_domain_proven(state, *remainder) &&
         equivalence_remainder_integer_proven(state, *remainder);
}

static bool equivalence_build_truncating_replacement(equivalence_state *state,
                                                     ixs_node *node,
                                                     unsigned depth,
                                                     ixs_node **replacement,
                                                     bool *matched) {
  ixs_node *quotient;
  ixs_node *numerator;
  ixs_node *denominator;
  ixs_node *remainder;
  ixs_node *difference;
  ixs_quotient_parts_status quotient_status;

  *replacement = NULL;
  if (!equivalence_match_truncating_round(state, node, depth, &quotient,
                                          matched) ||
      !*matched)
    return !state->oom;
  quotient_status = simp_decompose_exact_quotient(state->ctx, quotient,
                                                  &numerator, &denominator);
  if (quotient_status == IXS_QUOTIENT_PARTS_OOM) {
    state->oom = true;
    return false;
  }
  if (quotient_status != IXS_QUOTIENT_PARTS_MATCH ||
      !equivalence_truncating_parts_proven(state, node, quotient, numerator,
                                           denominator) ||
      !equivalence_build_signed_remainder(state, numerator, denominator,
                                          &remainder)) {
    *matched = false;
    return !state->oom;
  }
  /* q = trunc(N/D), R = N - D*q, hence q = (N - R)/D. */
  if (equivalence_build_sub(state, numerator, remainder, &difference) !=
          EQUIVALENCE_BUILD_OK ||
      ixs_node_is_sentinel(difference)) {
    *matched = false;
    return !state->oom;
  }
  if (equivalence_build_div_const(state, difference, denominator,
                                  replacement) != EQUIVALENCE_BUILD_OK ||
      ixs_node_is_sentinel(*replacement) ||
      !equivalence_remainder_domain_proven(state, *replacement)) {
    *replacement = NULL;
    *matched = false;
    return !state->oom;
  }
  return true;
}

/* A matched replacement becomes an outer-selection candidate and therefore
 * hides its children. An unmatched Piecewise is also opaque by contract;
 * unmatched scalar rounding nodes remain traversable. */
static bool equivalence_collect_truncating_candidate(
    equivalence_state *state, ixs_node *node, unsigned depth,
    bool piecewise_only, equivalence_substitutions *substitutions,
    bool *descend) {
  ixs_arena *arena = &state->ctx->scratch;
  ixs_node *replacement;
  bool candidate =
      node->tag == IXS_PIECEWISE ||
      (!piecewise_only && (node->tag == IXS_FLOOR || node->tag == IXS_CEIL ||
                           node->tag == IXS_TRUNC));
  bool matched;

  *descend = true;
  if (!candidate)
    return true;
  if (!equivalence_build_truncating_replacement(state, node, depth,
                                                &replacement, &matched))
    return false;
  if (matched) {
    if (!equivalence_substitutions_push(arena, substitutions, node,
                                        replacement)) {
      state->oom = true;
      return false;
    }
    *descend = false;
    return true;
  }
  *descend = node->tag != IXS_PIECEWISE;
  return true;
}

/* Candidate discovery visits each rounding-bearing node in the two query DAGs
 * once. Piecewise children are opaque to discovery even when malformed. */
static bool equivalence_collect_truncating_substitutions(
    equivalence_state *state, ixs_node *lhs, ixs_node *rhs, unsigned depth,
    bool piecewise_only, equivalence_substitutions *substitutions) {
  ixs_arena *arena = &state->ctx->scratch;
  query_node_set visited;
  ixs_node **stack = NULL;
  size_t stack_count = 0;
  size_t stack_capacity = 0;

  memset(&visited, 0, sizeof(visited));
  if ((ixs_node_contains_rounding(rhs) &&
       !query_node_stack_push(arena, &stack, &stack_count, &stack_capacity,
                              rhs)) ||
      (ixs_node_contains_rounding(lhs) &&
       !query_node_stack_push(arena, &stack, &stack_count, &stack_capacity,
                              lhs)))
    goto oom;
  while (stack_count > 0) {
    ixs_node *node = stack[--stack_count];
    uint32_t nchildren;
    uint32_t i;
    bool descend;
    bool inserted;
    if (!ixs_node_contains_rounding(node))
      continue;
    if (!query_node_set_insert(arena, &visited, node, &inserted))
      goto oom;
    if (!inserted)
      continue;
    if (state->visited != SIZE_MAX)
      state->visited++;
    if (!equivalence_collect_truncating_candidate(
            state, node, depth, piecewise_only, substitutions, &descend))
      return false;
    if (!descend)
      continue;
    if (!defined_child_count(node, &nchildren))
      return false;
    for (i = nchildren; i > 0; i--)
      if (!query_node_stack_push(arena, &stack, &stack_count, &stack_capacity,
                                 defined_child_at(node, i - 1u)))
        goto oom;
  }
  return true;

oom:
  state->oom = true;
  return false;
}

/* Mark every candidate reachable below another candidate in one multi-source
 * traversal. Shared sub-DAGs are visited once, so selection is O(N + C)
 * expected for N descendant nodes and C candidates instead of O(C^2 * N). */
static bool equivalence_select_outermost_substitutions(
    equivalence_state *state, equivalence_substitutions *substitutions) {
  ixs_arena *arena = &state->ctx->scratch;
  query_node_set candidates;
  query_node_set descendants;
  query_node_set excluded;
  ixs_node **stack = NULL;
  size_t stack_count = 0;
  size_t stack_capacity = 0;
  size_t output = 0;
  size_t i;

  memset(&candidates, 0, sizeof(candidates));
  memset(&descendants, 0, sizeof(descendants));
  memset(&excluded, 0, sizeof(excluded));
  for (i = 0; i < substitutions->count; i++) {
    ixs_node *target = substitutions->items[i].target;
    uint32_t nchildren;
    uint32_t child;
    bool inserted;
    if (!query_node_set_insert(arena, &candidates, target, &inserted))
      goto oom;
    if (!inserted)
      continue;
    if (!defined_child_count(target, &nchildren))
      return false;
    /* Seed children, not candidate roots. Expression DAGs are acyclic, so a
     * source cannot reach and exclude itself; only an enclosing match can. */
    for (child = nchildren; child > 0; child--)
      if (!query_node_stack_push(arena, &stack, &stack_count, &stack_capacity,
                                 defined_child_at(target, child - 1u)))
        goto oom;
  }

  while (stack_count > 0) {
    ixs_node *node = stack[--stack_count];
    uint32_t nchildren;
    uint32_t child;
    bool inserted;
    if (!query_node_set_insert(arena, &descendants, node, &inserted))
      goto oom;
    if (!inserted)
      continue;
    if (query_node_set_contains(&candidates, node) &&
        !query_node_set_insert(arena, &excluded, node, &inserted))
      goto oom;
    if (!defined_child_count(node, &nchildren))
      return false;
    for (child = nchildren; child > 0; child--)
      if (!query_node_stack_push(arena, &stack, &stack_count, &stack_capacity,
                                 defined_child_at(node, child - 1u)))
        goto oom;
  }

  for (i = 0; i < substitutions->count; i++) {
    if (query_node_set_contains(&excluded, substitutions->items[i].target))
      continue;
    if (output != i)
      substitutions->items[output] = substitutions->items[i];
    output++;
  }
  substitutions->count = output;
  return true;

oom:
  state->oom = true;
  return false;
}

static bool
equivalence_apply_substitutions(equivalence_state *state, ixs_node *root,
                                const equivalence_substitutions *substitutions,
                                ixs_node **result) {
  ixs_node **targets;
  ixs_node **replacements;
  size_t count = substitutions->count;
  size_t i;
  if (count == 0) {
    *result = root;
    return true;
  }
  if (count > UINT32_MAX || count > SIZE_MAX / sizeof(*targets)) {
    state->oom = true;
    return false;
  }
  targets = ixs_arena_alloc(&state->ctx->scratch, count * sizeof(*targets),
                            sizeof(void *));
  replacements = ixs_arena_alloc(&state->ctx->scratch,
                                 count * sizeof(*replacements), sizeof(void *));
  if (!targets || !replacements) {
    state->oom = true;
    return false;
  }
  for (i = 0; i < count; i++) {
    targets[i] = substitutions->items[i].target;
    replacements[i] = substitutions->items[i].replacement;
  }
  *result =
      simp_subs_multi(state->ctx, root, (uint32_t)count, targets, replacements);
  if (!*result) {
    state->oom = true;
    return false;
  }
  return !ixs_node_is_sentinel(*result);
}

/* Semantic projection is private to proof queries. It does not change the
 * caller's expression or expose truncation relations as an API. Modular
 * arithmetic remains in the generic constant-delta proof. */
static bool equivalence_project_truncating_rounds(
    equivalence_state *state, ixs_node *lhs, ixs_node *rhs, unsigned depth,
    bool piecewise_only, ixs_node **projected_lhs, ixs_node **projected_rhs) {
  ixs_arena_mark mark;
  equivalence_substitutions substitutions;
  ixs_node *nodes[2] = {lhs, rhs};
  bool projected = false;

  *projected_lhs = lhs;
  *projected_rhs = rhs;
  if (!ixs_node_contains_rounding(lhs) && !ixs_node_contains_rounding(rhs))
    return false;
  mark = ixs_arena_save(&state->ctx->scratch);
  memset(&substitutions, 0, sizeof(substitutions));
  if (!equivalence_collect_truncating_substitutions(
          state, lhs, rhs, depth, piecewise_only, &substitutions) ||
      substitutions.count == 0 ||
      !equivalence_select_outermost_substitutions(state, &substitutions) ||
      substitutions.count == 0 ||
      !equivalence_apply_substitutions(state, lhs, &substitutions, &nodes[0]) ||
      !equivalence_apply_substitutions(state, rhs, &substitutions, &nodes[1]))
    goto cleanup;
  *projected_lhs = nodes[0];
  *projected_rhs = nodes[1];
  projected = true;

cleanup:
  ixs_arena_restore(&state->ctx->scratch, mark);
  return projected;
}

static bool bounds_truncating_round_quotient(ixs_node *round,
                                             ixs_node **quotient) {
  if (round->tag == IXS_TRUNC) {
    *quotient = round->u.unary.arg;
    return true;
  }
  if (round->tag != IXS_PIECEWISE || round->u.pw.ncases != 2u ||
      !ixs_node_is_known_true(round->u.pw.cases[1].cond) ||
      round->u.pw.cases[0].value->tag != IXS_FLOOR ||
      round->u.pw.cases[1].value->tag != IXS_CEIL)
    return false;
  *quotient = round->u.pw.cases[0].value->u.unary.arg;
  return round->u.pw.cases[1].value->u.unary.arg == *quotient;
}

static bounds_truncating_range_status
bounds_truncating_round_proven(ixs_bounds *b, ixs_node *round,
                               ixs_node *quotient, ixs_node *numerator,
                               ixs_node *denominator, bool expression_defined) {
  equivalence_state state;
  ixs_node *same_sign;
  bool proven = false;
  size_t limit_blocks = b->query_state ? b->query_state->limit_blocks : 0u;
  size_t invalid_blocks = b->query_state ? b->query_state->invalid_blocks : 0u;
  bounds_truncating_range_status status;

  equivalence_state_init(&state, b->ctx, b);
  if (round->tag != IXS_TRUNC &&
      (!equivalence_build_same_sign(&state, numerator, denominator,
                                    &same_sign) ||
       state.invalid || state.oom || same_sign != round->u.pw.cases[0].cond))
    goto cleanup;
  if (ixs_bounds_check_integer_valued(b, numerator) != IXS_CHECK_TRUE ||
      ixs_bounds_check_integer_valued(b, denominator) != IXS_CHECK_TRUE)
    goto cleanup;
  proven = expression_defined ||
           (ixs_bounds_check_defined(b, numerator) == IXS_CHECK_TRUE &&
            ixs_bounds_check_defined(b, denominator) == IXS_CHECK_TRUE &&
            ixs_bounds_check_defined(b, quotient) == IXS_CHECK_TRUE);

cleanup:
  if (state.oom || b->oom)
    status = BOUNDS_TRUNCATING_RANGE_OOM;
  else if (state.invalid || bounds_query_invalid_since(b, invalid_blocks))
    status = BOUNDS_TRUNCATING_RANGE_INVALID;
  else if (state.limited || bounds_query_limited_since(b, limit_blocks))
    status = BOUNDS_TRUNCATING_RANGE_LIMITED;
  else
    status = proven ? BOUNDS_TRUNCATING_RANGE_MATCH
                    : BOUNDS_TRUNCATING_RANGE_NO_MATCH;
  equivalence_state_destroy(&state);
  return status;
}

static bounds_truncating_range_status
bounds_truncating_remainder_shift(ixs_bounds *b, ixs_node *expr,
                                  ixs_node *round, ixs_node *numerator,
                                  ixs_node *denominator, int64_t *shift_p) {
  ixs_node *product = simp_mul(b->ctx, denominator, round);
  ixs_node *remainder = product ? simp_sub(b->ctx, numerator, product) : NULL;
  ixs_node *shift = remainder ? simp_sub(b->ctx, expr, remainder) : NULL;
  int64_t shift_q;

  if (!product || !remainder || !shift)
    return BOUNDS_TRUNCATING_RANGE_OOM;
  if (ixs_node_is_sentinel(product) || ixs_node_is_sentinel(remainder) ||
      ixs_node_is_sentinel(shift))
    return BOUNDS_TRUNCATING_RANGE_INVALID;
  if (!ixs_node_is_const(shift))
    return BOUNDS_TRUNCATING_RANGE_NO_MATCH;
  ixs_node_get_rat(shift, shift_p, &shift_q);
  return shift_q == 1 ? BOUNDS_TRUNCATING_RANGE_MATCH
                      : BOUNDS_TRUNCATING_RANGE_NO_MATCH;
}

static bounds_truncating_range_status
bounds_truncating_denominator_radius(ixs_bounds *b, ixs_node *denominator,
                                     uint64_t *radius) {
  size_t limit_blocks = b->query_state ? b->query_state->limit_blocks : 0u;
  size_t invalid_blocks = b->query_state ? b->query_state->invalid_blocks : 0u;
  ixs_interval range = ixs_bounds_get(b, denominator);
  int64_t lo;
  int64_t hi;
  uint64_t magnitude;

  if (b->oom)
    return BOUNDS_TRUNCATING_RANGE_OOM;
  if (bounds_query_invalid_since(b, invalid_blocks))
    return BOUNDS_TRUNCATING_RANGE_INVALID;
  if (bounds_query_limited_since(b, limit_blocks))
    return BOUNDS_TRUNCATING_RANGE_LIMITED;
  if (!range.valid || range.lo_inf || range.hi_inf)
    return BOUNDS_TRUNCATING_RANGE_NO_MATCH;
  lo = ixs_rat_ceil(range.lo_p, range.lo_q);
  hi = ixs_rat_floor(range.hi_p, range.hi_q);
  if (lo > hi)
    return BOUNDS_TRUNCATING_RANGE_NO_MATCH;
  magnitude = bounds_int64_magnitude(lo);
  if (bounds_int64_magnitude(hi) > magnitude)
    magnitude = bounds_int64_magnitude(hi);
  if (magnitude == 0)
    return BOUNDS_TRUNCATING_RANGE_NO_MATCH;
  *radius = magnitude - 1u;
  return *radius <= (uint64_t)INT64_MAX ? BOUNDS_TRUNCATING_RANGE_MATCH
                                        : BOUNDS_TRUNCATING_RANGE_NO_MATCH;
}

static bounds_truncating_range_status
bounds_try_truncating_remainder_range(ixs_bounds *b, ixs_node *expr,
                                      ixs_node *round, bool expression_defined,
                                      ixs_interval *out) {
  ixs_node *quotient;
  ixs_node *numerator;
  ixs_node *denominator;
  ixs_interval remainder_range;
  ixs_interval shift_range;
  int64_t shift_p;
  uint64_t radius;
  ixs_quotient_parts_status quotient_status;
  bounds_truncating_range_status status;

  if (!bounds_truncating_round_quotient(round, &quotient))
    return BOUNDS_TRUNCATING_RANGE_NO_MATCH;
  quotient_status =
      simp_decompose_exact_quotient(b->ctx, quotient, &numerator, &denominator);
  if (quotient_status == IXS_QUOTIENT_PARTS_OOM)
    return BOUNDS_TRUNCATING_RANGE_OOM;
  if (quotient_status != IXS_QUOTIENT_PARTS_MATCH)
    return BOUNDS_TRUNCATING_RANGE_NO_MATCH;
  status = bounds_truncating_round_proven(b, round, quotient, numerator,
                                          denominator, expression_defined);
  if (status != BOUNDS_TRUNCATING_RANGE_MATCH)
    return status;
  status = bounds_truncating_remainder_shift(b, expr, round, numerator,
                                             denominator, &shift_p);
  if (status != BOUNDS_TRUNCATING_RANGE_MATCH)
    return status;
  status = bounds_truncating_denominator_radius(b, denominator, &radius);
  if (status != BOUNDS_TRUNCATING_RANGE_MATCH)
    return status;

  remainder_range = ixs_interval_range(-(int64_t)radius, 1, (int64_t)radius, 1);
  shift_range = ixs_interval_exact(shift_p, 1);
  remainder_range = iv_add(remainder_range, shift_range);
  if (!remainder_range.valid)
    return BOUNDS_TRUNCATING_RANGE_NO_MATCH;
  *out = remainder_range;
  return BOUNDS_TRUNCATING_RANGE_MATCH;
}

/* Recognize only the immediate canonical R = N - D * trunc(N / D) shape.
 * Do not walk the numerator DAG: this is on the hot interval path and may be
 * queried independently for every generated packet.  The existing intrinsic
 * range cache owns the result for the original ADD node. */
static bounds_truncating_range_status bounds_get_truncating_remainder_range(
    ixs_bounds *b, ixs_node *expr, bool expression_defined, ixs_interval *out) {
  uint32_t i;
  bounds_truncating_range_status status;

  if (!b || !b->ctx || !expr || expr->tag != IXS_ADD || !out ||
      !ixs_node_contains_rounding(expr))
    return BOUNDS_TRUNCATING_RANGE_NO_MATCH;

  for (i = 0; i < expr->u.add.nterms; i++) {
    ixs_node *term = expr->u.add.terms[i].term;
    uint32_t factor;
    if (term->tag == IXS_PIECEWISE || term->tag == IXS_TRUNC) {
      status = bounds_try_truncating_remainder_range(b, expr, term,
                                                     expression_defined, out);
      if (status != BOUNDS_TRUNCATING_RANGE_NO_MATCH)
        return status;
    }
    if (term->tag != IXS_MUL)
      continue;
    for (factor = 0; factor < term->u.mul.nfactors; factor++) {
      const ixs_mulfactor *candidate = &term->u.mul.factors[factor];
      if (candidate->exp == 1 && (candidate->base->tag == IXS_PIECEWISE ||
                                  candidate->base->tag == IXS_TRUNC)) {
        status = bounds_try_truncating_remainder_range(b, expr, candidate->base,
                                                       expression_defined, out);
        if (status != BOUNDS_TRUNCATING_RANGE_NO_MATCH)
          return status;
      }
    }
  }
  return BOUNDS_TRUNCATING_RANGE_NO_MATCH;
}

typedef struct {
  size_t nodes;
  size_t rounds;
} facts_truncating_cost;

static bool facts_measure_truncating_cost(ixs_ctx *ctx, ixs_node *root,
                                          facts_truncating_cost *cost,
                                          ixs_fact_query_status *status) {
  ixs_arena_mark mark = ixs_arena_save(&ctx->scratch);
  query_node_set visited;
  ixs_node **stack = NULL;
  size_t nstack = 0;
  size_t stack_capacity = 0;
  bool ok = false;

  cost->nodes = 0;
  cost->rounds = 0;
  memset(&visited, 0, sizeof(visited));
  if (!root) {
    *status = IXS_FACT_QUERY_INVALID;
    goto cleanup;
  }
  if (!query_node_stack_push(&ctx->scratch, &stack, &nstack, &stack_capacity,
                             root)) {
    *status = IXS_FACT_QUERY_OOM;
    goto cleanup;
  }
  while (nstack > 0) {
    ixs_node *node = stack[--nstack];
    uint32_t nchildren;
    uint32_t i;
    bool inserted;
    if (!node ||
        !query_node_set_insert(&ctx->scratch, &visited, node, &inserted)) {
      *status = node ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
      goto cleanup;
    }
    if (!inserted)
      continue;
    if (!defined_child_count(node, &nchildren)) {
      *status = IXS_FACT_QUERY_INVALID;
      goto cleanup;
    }
    if (cost->nodes != SIZE_MAX)
      cost->nodes++;
    if (node->tag == IXS_FLOOR || node->tag == IXS_CEIL ||
        node->tag == IXS_TRUNC) {
      if (cost->rounds != SIZE_MAX)
        cost->rounds++;
    }
    for (i = 0; i < nchildren; i++) {
      if (!query_node_stack_push(&ctx->scratch, &stack, &nstack,
                                 &stack_capacity, defined_child_at(node, i))) {
        *status = IXS_FACT_QUERY_OOM;
        goto cleanup;
      }
    }
  }
  ok = true;

cleanup:
  ixs_arena_restore(&ctx->scratch, mark);
  return ok;
}

static ixs_node *
facts_simplify_truncating_remainders(ixs_ctx *ctx, ixs_bounds *bounds,
                                     ixs_node *expr,
                                     ixs_fact_query_status *status) {
  equivalence_state state;
  facts_truncating_cost original_cost;
  facts_truncating_cost candidate_cost;
  ixs_node *projected;
  ixs_node *unused;
  ixs_node *candidate;
  ixs_node *result = NULL;
  bool simplify_limited = false;

  *status = IXS_FACT_QUERY_COMPLETE;

  equivalence_state_init(&state, ctx, bounds);
  if (!equivalence_project_truncating_rounds(&state, expr, ctx->node_zero, 0,
                                             true, &projected, &unused)) {
    if (state.oom)
      *status = IXS_FACT_QUERY_OOM;
    else if (state.invalid)
      *status = IXS_FACT_QUERY_INVALID;
    else if (state.limited)
      *status = IXS_FACT_QUERY_LIMITED;
    result = *status == IXS_FACT_QUERY_COMPLETE ? expr : NULL;
    goto cleanup;
  }
  if (state.oom) {
    *status = IXS_FACT_QUERY_OOM;
    goto cleanup;
  }
  if (state.invalid) {
    *status = IXS_FACT_QUERY_INVALID;
    goto cleanup;
  }
  if (state.limited) {
    *status = IXS_FACT_QUERY_LIMITED;
    goto cleanup;
  }
  if (projected == expr) {
    result = expr;
    goto cleanup;
  }
  candidate =
      simp_simplify_bounds_status(ctx, projected, bounds, &simplify_limited);
  if (simplify_limited) {
    *status = IXS_FACT_QUERY_LIMITED;
    goto cleanup;
  }
  if (!candidate) {
    *status = IXS_FACT_QUERY_OOM;
    goto cleanup;
  }
  if (ixs_node_is_sentinel(candidate)) {
    *status = IXS_FACT_QUERY_INVALID;
    goto cleanup;
  }
  if (candidate == expr) {
    result = expr;
    goto cleanup;
  }
  if (!facts_measure_truncating_cost(ctx, expr, &original_cost, status) ||
      !facts_measure_truncating_cost(ctx, candidate, &candidate_cost, status))
    goto cleanup;
  if (candidate_cost.rounds >= original_cost.rounds ||
      candidate_cost.nodes >= original_cost.nodes) {
    result = expr;
    goto cleanup;
  }
  result = candidate;

cleanup:
  equivalence_state_destroy(&state);
  return result;
}

static bool equivalence_extract_mod_cmp(ixs_node *cmp,
                                        equivalence_mod_cmp *out) {
  ixs_node *residual;
  ixs_node *mod;
  int64_t cp;
  int64_t cq;
  if (!cmp || !out || cmp->tag != IXS_CMP ||
      !ixs_node_is_zero(cmp->u.binary.rhs))
    return false;
  residual = cmp->u.binary.lhs;
  out->offset_p = 0;
  out->offset_q = 1;
  out->term_coeff = 1;
  if (residual->tag == IXS_MOD) {
    mod = residual;
  } else if (residual->tag == IXS_ADD && residual->u.add.nterms == 1 &&
             residual->u.add.terms[0].term->tag == IXS_MOD) {
    ixs_node_get_rat(residual->u.add.terms[0].coeff, &cp, &cq);
    if (cq != 1 || (cp != 1 && cp != -1))
      return false;
    out->term_coeff = cp;
    ixs_node_get_rat(residual->u.add.coeff, &out->offset_p, &out->offset_q);
    mod = residual->u.add.terms[0].term;
  } else {
    return false;
  }
  if (mod->u.binary.rhs->tag != IXS_INT || mod->u.binary.rhs->u.ival <= 0)
    return false;
  out->dividend = mod->u.binary.lhs;
  out->modulus = mod->u.binary.rhs->u.ival;
  out->op = cmp->u.binary.cmp_op;
  return true;
}

static ixs_check_result equivalence_mod_comparisons(equivalence_state *state,
                                                    ixs_node *lhs,
                                                    ixs_node *rhs) {
  equivalence_mod_cmp left;
  equivalence_mod_cmp right;
  ixs_node *delta;
  ixs_check_result congruent;
  if (!equivalence_extract_mod_cmp(lhs, &left) ||
      !equivalence_extract_mod_cmp(rhs, &right))
    return IXS_CHECK_UNKNOWN;
  if (left.modulus != right.modulus || left.term_coeff != right.term_coeff ||
      left.offset_p != right.offset_p || left.offset_q != right.offset_q ||
      left.op != right.op)
    return IXS_CHECK_UNKNOWN;
  delta = simp_sub(state->ctx, left.dividend, right.dividend);
  if (!delta) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (ixs_node_is_sentinel(delta))
    return IXS_CHECK_UNKNOWN;
  congruent = ixs_bounds_check_congruent(state->bounds, delta, left.modulus, 0);
  return congruent == IXS_CHECK_TRUE ? IXS_CHECK_TRUE : IXS_CHECK_UNKNOWN;
}

static bool equivalence_flatten_logic(equivalence_state *state, ixs_node *root,
                                      ixs_tag tag, ixs_node ***terms,
                                      size_t *nterms, size_t *terms_capacity) {
  query_node_set visited;
  ixs_node **stack = NULL;
  size_t stack_capacity = 0;
  size_t nstack = 0;

  memset(&visited, 0, sizeof(visited));
  *nterms = 0;
  if (!query_node_stack_push(&state->ctx->scratch, &stack, &nstack,
                             &stack_capacity, root))
    goto oom;
  while (nstack > 0) {
    ixs_node *node = stack[--nstack];
    bool inserted;
    if (!query_node_set_insert(&state->ctx->scratch, &visited, node, &inserted))
      goto oom;
    /* AND and OR are idempotent, so sharing and repeated operands may be
     * visited once.  This also makes malformed cyclic nodes terminate. */
    if (!inserted)
      continue;
    if (node->tag == tag && ixs_node_is_bool_valued(node)) {
      uint32_t i;
      for (i = 0; i < node->u.assoc.nargs; i++) {
        if (!query_node_stack_push(&state->ctx->scratch, &stack, &nstack,
                                   &stack_capacity, node->u.assoc.args[i]))
          goto oom;
      }
    } else {
      if (!query_node_stack_push(&state->ctx->scratch, terms, nterms,
                                 terms_capacity, node))
        goto oom;
    }
  }
  return true;

oom:
  state->oom = true;
  return false;
}

static ixs_check_result equivalence_match_logic(equivalence_state *state,
                                                ixs_node *lhs, ixs_node *rhs,
                                                unsigned depth) {
  ixs_arena_mark mark = ixs_arena_save(&state->ctx->scratch);
  ixs_node **left_terms = NULL;
  ixs_node **right_terms = NULL;
  unsigned char *left_matched;
  unsigned char *right_matched;
  size_t left_capacity = 0;
  size_t right_capacity = 0;
  size_t nleft;
  size_t nright;
  size_t i;
  size_t j;
  ixs_check_result result = IXS_CHECK_UNKNOWN;

  if (!equivalence_flatten_logic(state, lhs, lhs->tag, &left_terms, &nleft,
                                 &left_capacity) ||
      !equivalence_flatten_logic(state, rhs, rhs->tag, &right_terms, &nright,
                                 &right_capacity) ||
      nleft != nright)
    goto cleanup;
  left_matched = ixs_arena_alloc(&state->ctx->scratch, nleft, 1);
  right_matched = ixs_arena_alloc(&state->ctx->scratch, nright, 1);
  if ((!left_matched || !right_matched) && nleft != 0) {
    state->oom = true;
    goto cleanup;
  }
  if (nleft != 0) {
    memset(left_matched, 0, nleft);
    memset(right_matched, 0, nright);
  }

  /* Exact terms first.  This makes matching deterministic and avoids proof
   * work on the common reordered-tree case. */
  for (i = 0; i < nleft; i++) {
    for (j = 0; j < nright; j++) {
      if (!right_matched[j] && left_terms[i] == right_terms[j]) {
        left_matched[i] = 1;
        right_matched[j] = 1;
        break;
      }
    }
  }
  for (i = 0; i < nleft; i++) {
    if (left_matched[i])
      continue;
    /* Nested associative matching is a conservative optional refinement.
     * Only the outer match starts subproofs, statically bounding C recursion;
     * each subproof still has unbounded growable traversal of its DAG. */
    if (depth != 0u)
      goto cleanup;
    for (j = 0; j < nright; j++) {
      if (!right_matched[j] &&
          equivalence_core(state, left_terms[i], right_terms[j], depth + 1u) ==
              IXS_CHECK_TRUE) {
        left_matched[i] = 1;
        right_matched[j] = 1;
        break;
      }
    }
    if (!left_matched[i])
      goto cleanup;
  }
  result = IXS_CHECK_TRUE;

cleanup:
  ixs_arena_restore(&state->ctx->scratch, mark);
  return result;
}

static ixs_check_result equivalence_predicate_shapes(equivalence_state *state,
                                                     ixs_node *lhs,
                                                     ixs_node *rhs,
                                                     unsigned depth) {
  if (lhs->tag == rhs->tag && (lhs->tag == IXS_AND || lhs->tag == IXS_OR))
    return equivalence_match_logic(state, lhs, rhs, depth);
  if (lhs->tag == IXS_NOT && rhs->tag == IXS_NOT) {
    if (depth != 0u)
      return IXS_CHECK_UNKNOWN;
    do {
      lhs = lhs->u.unary_bool.arg;
      rhs = rhs->u.unary_bool.arg;
    } while (lhs && rhs && lhs->tag == IXS_NOT && rhs->tag == IXS_NOT);
    return equivalence_core(state, lhs, rhs, depth + 1u);
  }
  if (lhs->tag == IXS_CMP && rhs->tag == IXS_CMP) {
    ixs_check_result result = equivalence_mod_comparisons(state, lhs, rhs);
    if (result != IXS_CHECK_UNKNOWN)
      return result;
    return equivalence_ordered_comparisons(state, lhs, rhs);
  }
  return IXS_CHECK_UNKNOWN;
}

static bool equivalence_extract_mod_partition(ixs_node *expr, ixs_node **base,
                                              int64_t *modulus) {
  ixs_node *mod = NULL;
  int64_t constant_p;
  int64_t constant_q;
  uint32_t i;

  *base = NULL;
  if (!expr || expr->tag != IXS_ADD || expr->u.add.nterms != 2u)
    return false;
  ixs_node_get_rat(expr->u.add.coeff, &constant_p, &constant_q);
  if (constant_p != 0 || constant_q != 1)
    return false;
  for (i = 0; i < expr->u.add.nterms; i++) {
    ixs_node *term = expr->u.add.terms[i].term;
    int64_t coefficient_p;
    int64_t coefficient_q;
    ixs_node_get_rat(expr->u.add.terms[i].coeff, &coefficient_p,
                     &coefficient_q);
    if (coefficient_q != 1)
      return false;
    if (term->tag == IXS_MOD && coefficient_p == -1) {
      if (mod)
        return false;
      mod = term;
    } else if (coefficient_p == 1) {
      if (*base)
        return false;
      *base = term;
    } else {
      return false;
    }
  }
  if (!mod || !*base || mod->u.binary.lhs != *base ||
      mod->u.binary.rhs->tag != IXS_INT || mod->u.binary.rhs->u.ival <= 0)
    return false;
  *modulus = mod->u.binary.rhs->u.ival;
  return true;
}

/* Removing a Euclidean residue modulo M rounds an integer down to an M
 * boundary.  When M divides the positive floor divisor D, that operation
 * cannot cross a D boundary, so floor(x/D) is unchanged. */
static ixs_check_result equivalence_floor_mod_partition_direction(
    equivalence_state *state, ixs_node *direct, ixs_node *partitioned) {
  ixs_node *direct_numerator;
  ixs_node *direct_denominator;
  ixs_node *partitioned_numerator;
  ixs_node *partitioned_denominator;
  ixs_node *base;
  ixs_quotient_parts_status direct_status;
  ixs_quotient_parts_status partitioned_status;
  int64_t direct_p;
  int64_t direct_q;
  int64_t partitioned_p;
  int64_t partitioned_q;
  int64_t modulus;

  if (!direct || !partitioned || direct->tag != IXS_FLOOR ||
      partitioned->tag != IXS_FLOOR)
    return IXS_CHECK_UNKNOWN;
  direct_status = simp_decompose_exact_quotient(
      state->ctx, direct->u.unary.arg, &direct_numerator, &direct_denominator);
  partitioned_status = simp_decompose_exact_quotient(
      state->ctx, partitioned->u.unary.arg, &partitioned_numerator,
      &partitioned_denominator);
  if (direct_status == IXS_QUOTIENT_PARTS_OOM ||
      partitioned_status == IXS_QUOTIENT_PARTS_OOM) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (direct_status != IXS_QUOTIENT_PARTS_MATCH ||
      partitioned_status != IXS_QUOTIENT_PARTS_MATCH ||
      !ixs_node_is_const(direct_denominator) ||
      !ixs_node_is_const(partitioned_denominator) ||
      !equivalence_extract_mod_partition(partitioned_numerator, &base,
                                         &modulus) ||
      base != direct_numerator)
    return IXS_CHECK_UNKNOWN;
  ixs_node_get_rat(direct_denominator, &direct_p, &direct_q);
  ixs_node_get_rat(partitioned_denominator, &partitioned_p, &partitioned_q);
  if (direct_q != 1 || partitioned_q != 1 || direct_p <= 0 ||
      direct_p != partitioned_p || direct_p % modulus != 0 ||
      ixs_bounds_check_integer_valued(state->bounds, base) != IXS_CHECK_TRUE)
    return IXS_CHECK_UNKNOWN;
  return IXS_CHECK_TRUE;
}

static ixs_check_result
equivalence_floor_mod_partition(equivalence_state *state, ixs_node *lhs,
                                ixs_node *rhs) {
  ixs_check_result result =
      equivalence_floor_mod_partition_direction(state, lhs, rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  return equivalence_floor_mod_partition_direction(state, rhs, lhs);
}

static ixs_check_result equivalence_expanded(equivalence_state *state,
                                             ixs_node *lhs, ixs_node *rhs,
                                             unsigned depth) {
  ixs_node *expanded_lhs = expand_impl(state->ctx, lhs);
  ixs_node *expanded_rhs = expand_impl(state->ctx, rhs);
  ixs_check_result result;
  bool lhs_limited = false;
  bool rhs_limited = false;
  if (!expanded_lhs || !expanded_rhs) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (ixs_node_is_sentinel(expanded_lhs) ||
      ixs_node_is_sentinel(expanded_rhs)) {
    bounds_query_note_invalid(state->bounds->query_state);
    return IXS_CHECK_UNKNOWN;
  }
  expanded_lhs = simp_simplify_bounds_status(state->ctx, expanded_lhs,
                                             state->bounds, &lhs_limited);
  expanded_rhs = simp_simplify_bounds_status(state->ctx, expanded_rhs,
                                             state->bounds, &rhs_limited);
  if (lhs_limited || rhs_limited) {
    state->limited = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (!expanded_lhs || !expanded_rhs) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (ixs_node_is_sentinel(expanded_lhs) ||
      ixs_node_is_sentinel(expanded_rhs)) {
    bounds_query_note_invalid(state->bounds->query_state);
    return IXS_CHECK_UNKNOWN;
  }
  if (expanded_lhs == expanded_rhs)
    return IXS_CHECK_TRUE;
  result = equivalence_difference(state, expanded_lhs, expanded_rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  result = equivalence_mod_shifts(state, expanded_lhs, expanded_rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  result = equivalence_scaled_mods(state, expanded_lhs, expanded_rhs, depth);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  if (ixs_node_is_bool_valued(expanded_lhs) &&
      ixs_node_is_bool_valued(expanded_rhs))
    return equivalence_predicate_shapes(state, expanded_lhs, expanded_rhs,
                                        depth);
  return IXS_CHECK_UNKNOWN;
}

static ixs_check_result equivalence_core(equivalence_state *state,
                                         ixs_node *lhs, ixs_node *rhs,
                                         unsigned depth) {
  equivalence_memo_entry *entry;
  ixs_check_result result;

  if (!lhs || !rhs || state->limited || state->invalid || state->oom ||
      state->arithmetic_unrepresentable)
    return IXS_CHECK_UNKNOWN;
  if ((uintptr_t)lhs > (uintptr_t)rhs) {
    ixs_node *tmp = lhs;
    lhs = rhs;
    rhs = tmp;
  }
  entry = equivalence_memo_get(state, lhs, rhs, true);
  if (!entry) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (entry->complete)
    return entry->result;
  if (entry->active)
    return IXS_CHECK_UNKNOWN;
  entry->active = true;
  result = equivalence_core_impl(state, lhs, rhs, depth);
  entry = equivalence_memo_get(state, lhs, rhs, false);
  if (!entry) {
    state->invalid = true;
    return IXS_CHECK_UNKNOWN;
  }
  entry->active = false;
  if (!state->limited && !state->invalid && !state->oom) {
    entry->result = result;
    entry->complete = true;
  }
  return result;
}

static ixs_check_result equivalence_predicate_truth(equivalence_state *state,
                                                    ixs_node *lhs,
                                                    ixs_node *rhs) {
  ixs_check_result lhs_truth;
  ixs_check_result rhs_truth;
  bool lhs_limited = false;
  bool rhs_limited = false;

  if (!ixs_node_is_bool_valued(lhs) || !ixs_node_is_bool_valued(rhs))
    return IXS_CHECK_UNKNOWN;
  lhs_truth = predicate_query_eval_detail(state->bounds, lhs, &lhs_limited);
  rhs_truth = predicate_query_eval_detail(state->bounds, rhs, &rhs_limited);
  if (lhs_limited || rhs_limited) {
    state->limited = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (lhs_truth == IXS_CHECK_UNKNOWN || rhs_truth == IXS_CHECK_UNKNOWN)
    return IXS_CHECK_UNKNOWN;
  return lhs_truth == rhs_truth ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
}

static ixs_check_result equivalence_projected(equivalence_state *state,
                                              ixs_node *lhs, ixs_node *rhs,
                                              unsigned depth) {
  ixs_node *projected_lhs;
  ixs_node *projected_rhs;
  ixs_check_result result;

  if (!equivalence_project_truncating_rounds(state, lhs, rhs, depth, false,
                                             &projected_lhs, &projected_rhs))
    return IXS_CHECK_UNKNOWN;
  if (projected_lhs == projected_rhs)
    return IXS_CHECK_TRUE;
  result = equivalence_difference(state, projected_lhs, projected_rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  result = equivalence_mod_shifts(state, projected_lhs, projected_rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  result = equivalence_scaled_mods(state, projected_lhs, projected_rhs, depth);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  return equivalence_expanded(state, projected_lhs, projected_rhs, depth);
}

static ixs_check_result equivalence_core_impl(equivalence_state *state,
                                              ixs_node *lhs, ixs_node *rhs,
                                              unsigned depth) {
  ixs_node *simplified_lhs;
  ixs_node *simplified_rhs;
  ixs_check_result result;
  bool lhs_limited = false;
  bool rhs_limited = false;

  if (state->visited != SIZE_MAX)
    state->visited++;
  if (lhs == rhs)
    return IXS_CHECK_TRUE;

  simplified_lhs =
      simp_simplify_bounds_status(state->ctx, lhs, state->bounds, &lhs_limited);
  simplified_rhs =
      simp_simplify_bounds_status(state->ctx, rhs, state->bounds, &rhs_limited);
  if (lhs_limited || rhs_limited) {
    state->limited = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (!simplified_lhs || !simplified_rhs) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (ixs_node_is_sentinel(simplified_lhs) ||
      ixs_node_is_sentinel(simplified_rhs)) {
    bounds_query_note_invalid(state->bounds->query_state);
    return IXS_CHECK_UNKNOWN;
  }
  if (simplified_lhs == simplified_rhs)
    return IXS_CHECK_TRUE;

  result = equivalence_predicate_truth(state, simplified_lhs, simplified_rhs);
  if (result != IXS_CHECK_UNKNOWN || state->limited)
    return result;

  result =
      equivalence_floor_mod_partition(state, simplified_lhs, simplified_rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;

  result = equivalence_difference(state, simplified_lhs, simplified_rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  if (state->arithmetic_unrepresentable)
    return IXS_CHECK_UNKNOWN;
  result = equivalence_mod_shifts(state, simplified_lhs, simplified_rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  result =
      equivalence_scaled_mods(state, simplified_lhs, simplified_rhs, depth);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  result = equivalence_mod_quotient_identity(state, simplified_lhs,
                                             simplified_rhs, depth);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  result = equivalence_projected(state, lhs, rhs, depth);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  result = equivalence_expanded(state, simplified_lhs, simplified_rhs, depth);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  return IXS_CHECK_UNKNOWN;
}

typedef enum {
  EQUIVALENCE_QUERY_COMPLETE,
  EQUIVALENCE_QUERY_LIMITED,
  EQUIVALENCE_QUERY_INVALID,
  EQUIVALENCE_QUERY_OOM
} equivalence_query_status;

static equivalence_query_status
equivalence_query_bounds_detail(ixs_bounds *bounds, ixs_ctx *ctx, ixs_node *lhs,
                                ixs_node *rhs, ixs_check_result *result) {
  ixs_arena_mark mark = ixs_arena_save(&ctx->scratch);
  equivalence_state state;
  size_t limit_blocks =
      bounds->query_state ? bounds->query_state->limit_blocks : 0u;
  size_t invalid_blocks =
      bounds->query_state ? bounds->query_state->invalid_blocks : 0u;
  bool old_oom = bounds->oom;
  bool track_limits = bounds_query_is_tracking(bounds);
  bool lhs_oom = false;
  bool rhs_oom = false;
  bool lhs_limited = false;
  bool rhs_limited = false;
  equivalence_query_status status = EQUIVALENCE_QUERY_COMPLETE;

  equivalence_state_init(&state, ctx, bounds);
  *result = IXS_CHECK_UNKNOWN;
  if (bounds_check_defined_detail(bounds, lhs, &lhs_oom, &lhs_limited) !=
          IXS_CHECK_TRUE ||
      bounds_check_defined_detail(bounds, rhs, &rhs_oom, &rhs_limited) !=
          IXS_CHECK_TRUE) {
    if (lhs_oom || rhs_oom || (!old_oom && bounds->oom))
      status = EQUIVALENCE_QUERY_OOM;
    else if (lhs_limited || rhs_limited)
      status = EQUIVALENCE_QUERY_LIMITED;
    goto restore;
  }
  if (bounds->query_state)
    limit_blocks = bounds->query_state->limit_blocks;
  *result = equivalence_core(&state, lhs, rhs, 0);
  if (state.invalid || bounds_query_invalid_since(bounds, invalid_blocks)) {
    *result = IXS_CHECK_UNKNOWN;
    status = EQUIVALENCE_QUERY_INVALID;
  } else if (state.oom || (!old_oom && bounds->oom)) {
    *result = IXS_CHECK_UNKNOWN;
    status = EQUIVALENCE_QUERY_OOM;
  } else if (*result == IXS_CHECK_UNKNOWN &&
             (state.limited || (track_limits && bounds_query_limited_since(
                                                    bounds, limit_blocks)))) {
    *result = IXS_CHECK_UNKNOWN;
    status = EQUIVALENCE_QUERY_LIMITED;
  }

restore:
  equivalence_state_destroy(&state);
  if (!old_oom && bounds->oom)
    bounds_cache_clear(bounds);
  bounds->oom = old_oom;
  ixs_arena_restore(&ctx->scratch, mark);
  return status;
}

static equivalence_query_status
equivalence_query_bound_detail(ixs_facts *facts, ixs_ctx *ctx, ixs_node *lhs,
                               ixs_node *rhs, ixs_check_result *result) {
  return equivalence_query_bounds_detail(&facts->bounds, ctx, lhs, rhs, result);
}

static ixs_check_result bounds_check_equivalence_atom(ixs_bounds *bounds,
                                                      ixs_node *cmp) {
  uint64_t saved_owner;
  equivalence_query_status status;
  ixs_check_result equivalent = IXS_CHECK_UNKNOWN;
  ixs_node *lhs;
  ixs_node *rhs;

  if (!bounds || !bounds->ctx || !cmp || cmp->tag != IXS_CMP ||
      bounds->predicate_equivalence_depth != 0u ||
      (cmp->u.binary.cmp_op != IXS_CMP_EQ &&
       cmp->u.binary.cmp_op != IXS_CMP_NE) ||
      (ixs_node_is_pred_kind(cmp->u.binary.lhs) &&
       cmp->u.binary.lhs->tag != IXS_INT) ||
      (ixs_node_is_pred_kind(cmp->u.binary.rhs) &&
       cmp->u.binary.rhs->tag != IXS_INT))
    return IXS_CHECK_UNKNOWN;

  lhs = cmp->u.binary.lhs;
  rhs = cmp->u.binary.rhs;
  if (ixs_node_is_zero(rhs) && !extract_add_node_equality(lhs, &lhs, &rhs)) {
    lhs = cmp->u.binary.lhs;
    rhs = cmp->u.binary.rhs;
  }

  saved_owner = bounds->query_owner;
  bounds->predicate_equivalence_depth++;
  bounds_query_refresh_owner(bounds);
  status = equivalence_query_bounds_detail(bounds, bounds->ctx, lhs, rhs,
                                           &equivalent);
  bounds->query_owner = saved_owner;
  bounds->predicate_equivalence_depth--;

  if (status == EQUIVALENCE_QUERY_LIMITED && bounds->query_state)
    bounds_query_note_limit(bounds->query_state);
  else if (status == EQUIVALENCE_QUERY_INVALID && bounds->query_state)
    bounds_query_note_invalid(bounds->query_state);
  else if (status == EQUIVALENCE_QUERY_OOM)
    bounds->oom = true;
  if (status != EQUIVALENCE_QUERY_COMPLETE)
    return IXS_CHECK_UNKNOWN;
  return cmp->u.binary.cmp_op == IXS_CMP_EQ ? equivalent
                                            : check_result_not(equivalent);
}

IXS_STATIC ixs_check_result ixs_bounds_check_query(ixs_bounds *bounds,
                                                   ixs_node *cmp) {
  ixs_check_result result;
  bool query_held = false;

  if (!ixs_bounds_query_hold_begin(bounds, cmp, &query_held))
    return IXS_CHECK_UNKNOWN;
  result = ixs_bounds_check(bounds, cmp);
  if (result == IXS_CHECK_UNKNOWN && cmp && cmp->tag == IXS_CMP &&
      ixs_node_is_zero(cmp->u.binary.rhs) &&
      (cmp->u.binary.cmp_op == IXS_CMP_EQ ||
       cmp->u.binary.cmp_op == IXS_CMP_NE))
    result = bounds_check_equivalence_atom(bounds, cmp);
  if (query_held)
    ixs_bounds_query_hold_end(bounds);
  return result;
}

static ixs_fact_query_status
constant_difference_query_status(bool oom, bool invalid, bool limited, bool ok,
                                 int64_t result, int64_t *delta,
                                 bool *matched) {
  *matched = false;
  if (oom)
    return IXS_FACT_QUERY_OOM;
  if (invalid)
    return IXS_FACT_QUERY_INVALID;
  if (limited)
    return IXS_FACT_QUERY_LIMITED;
  if (ok) {
    *delta = result;
    *matched = true;
  }
  return IXS_FACT_QUERY_COMPLETE;
}

typedef struct {
  int64_t result;
  bool invalid;
  bool delta_limited;
  bool delta_oom;
  bool limited;
  bool oom;
  bool ok;
} constant_difference_attempt;

static void constant_difference_try_projection(
    ixs_ctx *ctx, ixs_bounds *bounds, ixs_node *lhs, ixs_node *rhs,
    size_t limit_blocks, bool old_oom, constant_difference_attempt *attempt) {
  equivalence_state projection;
  ixs_node *nodes[2] = {lhs, rhs};

  equivalence_state_init(&projection, ctx, bounds);
  if (equivalence_project_truncating_rounds(&projection, lhs, rhs, 0, false,
                                            &nodes[0], &nodes[1]) &&
      !projection.limited && !projection.invalid && !projection.oom) {
    bool projected_invalid = false;
    bool projected_limited = false;
    bool projected_oom = false;
    attempt->ok = bounds_constant_delta_query_detail(
        ctx, bounds, nodes[0], nodes[1], true, &attempt->result,
        &projected_invalid, &projected_limited, &projected_oom);
    attempt->invalid = attempt->invalid || projected_invalid;
    attempt->delta_limited = attempt->delta_limited || projected_limited;
    attempt->delta_oom = attempt->delta_oom || projected_oom;
  }
  attempt->invalid = attempt->invalid || projection.invalid;
  attempt->oom =
      attempt->delta_oom || projection.oom || (!old_oom && bounds->oom);
  attempt->limited = attempt->delta_limited || projection.limited ||
                     bounds_query_limited_since(bounds, limit_blocks);
  equivalence_state_destroy(&projection);
}

static bool
constant_difference_normalize_operands(ixs_ctx *ctx, ixs_bounds *bounds,
                                       ixs_node **lhs, ixs_node **rhs,
                                       constant_difference_attempt *attempt) {
  bool lhs_limited = false;
  bool rhs_limited = false;
  ixs_node *normalized_lhs =
      simp_simplify_bounds_status(ctx, *lhs, bounds, &lhs_limited);
  ixs_node *normalized_rhs =
      simp_simplify_bounds_status(ctx, *rhs, bounds, &rhs_limited);

  attempt->limited = lhs_limited || rhs_limited;
  if (attempt->limited)
    return false;
  if (!normalized_lhs || !normalized_rhs) {
    attempt->oom = true;
    return false;
  }
  if (ixs_node_is_sentinel(normalized_lhs) ||
      ixs_node_is_sentinel(normalized_rhs)) {
    attempt->invalid = true;
    return false;
  }
  *lhs = normalized_lhs;
  *rhs = normalized_rhs;
  return true;
}

static ixs_fact_query_status
constant_difference_query_bound_detail(ixs_ctx *ctx, ixs_bounds *bounds,
                                       ixs_node *lhs, ixs_node *rhs,
                                       int64_t *delta, bool *matched) {
  ixs_arena_mark mark = ixs_arena_save(&ctx->scratch);
  constant_difference_attempt attempt;
  ixs_node *original_lhs = lhs;
  ixs_node *original_rhs = rhs;
  size_t limit_blocks =
      bounds->query_state ? bounds->query_state->limit_blocks : 0u;
  bool old_oom = bounds->oom;
  bool lhs_oom = false;
  bool rhs_oom = false;
  bool lhs_limited = false;
  bool rhs_limited = false;
  bool has_rounding =
      ixs_node_contains_rounding(lhs) || ixs_node_contains_rounding(rhs);
  ixs_fact_query_status status = IXS_FACT_QUERY_COMPLETE;

  memset(&attempt, 0, sizeof(attempt));
  if (bounds_check_defined_detail(bounds, lhs, &lhs_oom, &lhs_limited) !=
          IXS_CHECK_TRUE ||
      bounds_check_defined_detail(bounds, rhs, &rhs_oom, &rhs_limited) !=
          IXS_CHECK_TRUE) {
    attempt.oom = lhs_oom || rhs_oom;
    attempt.limited = lhs_limited || rhs_limited;
    goto finish;
  }
  if (bounds->query_state)
    limit_blocks = bounds->query_state->limit_blocks;

  /* Normalize each side before constructing the difference.  Rewriting only
   * lhs-rhs can erase the affine numerator shared by two exact remainder
   * encodings before either encoding is recognized. */
  if (has_rounding && !constant_difference_normalize_operands(ctx, bounds, &lhs,
                                                              &rhs, &attempt))
    goto finish;

  attempt.ok = bounds_constant_delta_query_detail(
      ctx, bounds, lhs, rhs, true, &attempt.result, &attempt.invalid,
      &attempt.delta_limited, &attempt.delta_oom);
  attempt.oom = attempt.delta_oom || (!old_oom && bounds->oom);
  attempt.limited =
      attempt.delta_limited || bounds_query_limited_since(bounds, limit_blocks);
  if (!attempt.ok && !attempt.oom && !attempt.limited && !attempt.invalid &&
      has_rounding) {
    /* Projection recognizes source-level truncating-remainder protocols.  A
     * useful partial normalization must not hide that independent proof
     * strategy when the normalized direct proof remains inconclusive. */
    constant_difference_try_projection(ctx, bounds, original_lhs, original_rhs,
                                       limit_blocks, old_oom, &attempt);
  }

finish:
  attempt.oom = attempt.oom || (!old_oom && bounds->oom);
  status = constant_difference_query_status(
      attempt.oom, attempt.invalid, attempt.limited && !attempt.ok, attempt.ok,
      attempt.result, delta, matched);
  if (!old_oom && bounds->oom)
    bounds_cache_clear(bounds);
  bounds->oom = old_oom;
  ixs_arena_restore(&ctx->scratch, mark);
  return status;
}

static ixs_fact_check_result fact_check_result(ixs_fact_query_status status,
                                               ixs_check_result check) {
  ixs_fact_check_result result;
  result.status = status;
  result.check = check;
  return result;
}

static ixs_fact_query_status
facts_status_from_equivalence(equivalence_query_status status) {
  switch (status) {
  case EQUIVALENCE_QUERY_COMPLETE:
    return IXS_FACT_QUERY_COMPLETE;
  case EQUIVALENCE_QUERY_LIMITED:
    return IXS_FACT_QUERY_LIMITED;
  case EQUIVALENCE_QUERY_INVALID:
    return IXS_FACT_QUERY_INVALID;
  case EQUIVALENCE_QUERY_OOM:
    return IXS_FACT_QUERY_OOM;
  }
  return IXS_FACT_QUERY_INVALID;
}

static ixs_fact_check_result facts_query_check_predicate(ixs_facts *facts,
                                                         ixs_node *predicate) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_node *simplified;
  ixs_fact_check_result result = {IXS_FACT_QUERY_INVALID, IXS_CHECK_UNKNOWN};
  bool predicate_limited = false;
  bool simplify_limited = false;
  bool query_held = false;
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "predicate");
  if (!facts_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "predicate: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, predicate, "predicate"))
    goto cleanup;
  if (!ixs_node_is_pred_kind(predicate)) {
    ixs_ctx_push_error(ctx, "predicate: expression is not a predicate tree");
    goto cleanup;
  }
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(&facts->bounds, predicate, &query_held)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }

  /* The predicate engine owns proof semantics, including reflexive equality
   * as a totality witness.  Simplification remains a fallback for predicates
   * whose original form is inconclusive. */
  result.check = predicate_query_eval_detail(&facts->bounds, predicate,
                                             &predicate_limited);
  if (predicate_limited) {
    result.status = IXS_FACT_QUERY_LIMITED;
    goto cleanup;
  }
  if (result.check != IXS_CHECK_UNKNOWN) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }

  mark = ixs_arena_save(&ctx->scratch);
  simplified = simp_simplify_bounds_status(ctx, predicate, &facts->bounds,
                                           &simplify_limited);
  if (simplify_limited) {
    result.status = IXS_FACT_QUERY_LIMITED;
  } else if (!simplified) {
    result.status = IXS_FACT_QUERY_OOM;
  } else if (ixs_node_is_sentinel(simplified)) {
    result.status = IXS_FACT_QUERY_INVALID;
  } else {
    result.check = predicate_query_eval_detail(&facts->bounds, simplified,
                                               &predicate_limited);
    if (!predicate_limited && result.check == IXS_CHECK_UNKNOWN)
      result.check =
          predicate_query_finite_domain(&facts->bounds, predicate, NULL);
    result.status =
        predicate_limited ? IXS_FACT_QUERY_LIMITED : IXS_FACT_QUERY_COMPLETE;
  }
  ixs_arena_restore(&ctx->scratch, mark);

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.check = IXS_CHECK_UNKNOWN;
  ixs_session_unbind(&binding);
  return result;
}

static ixs_fact_check_result
facts_query_equivalent(ixs_facts *facts, ixs_node *lhs, ixs_node *rhs) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  ixs_node *nodes[2] = {lhs, rhs};
  equivalence_query_status detail;
  bool query_held = false;
  ixs_fact_check_result result = {IXS_FACT_QUERY_INVALID, IXS_CHECK_UNKNOWN};
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "equivalence");
  if (!facts_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "equivalence: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, lhs, "equivalence") ||
      !facts_query_node_ok(ctx, rhs, "equivalence"))
    goto cleanup;
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(
          &facts->bounds, bounds_query_select_root(&facts->bounds, nodes, 2),
          &query_held)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  detail = equivalence_query_bound_detail(facts, ctx, lhs, rhs, &result.check);
  result.status = facts_status_from_equivalence(detail);

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.check = IXS_CHECK_UNKNOWN;
  ixs_session_unbind(&binding);
  return result;
}

typedef struct {
  ixs_session_binding binding;
  ixs_facts *facts;
  ixs_ctx *ctx;
  ixs_arena_mark scratch_mark;
  ixs_arena_mark diag_mark;
  const char **saved_errors;
  size_t saved_nerrors;
  size_t saved_errors_cap;
  facts_read_query_scope read_scope;
  ixs_fact_query_status status;
  bool bound;
  bool active;
  bool query_held;
} algebra_query_scope;

static bool algebra_query_begin(ixs_facts *facts, ixs_node *const *nodes,
                                size_t nnodes, const char *query,
                                bool outputs_ok, const char *output_error,
                                algebra_query_scope *scope) {
  size_t i;
  memset(scope, 0, sizeof(*scope));
  scope->status = IXS_FACT_QUERY_INVALID;
  if (!facts_bind(facts, &scope->binding, &scope->ctx))
    return false;
  scope->facts = facts;
  scope->bound = true;
  facts_read_query_begin(&scope->read_scope, &facts->bounds, scope->ctx, query);
  if (!facts_ready(facts)) {
    scope->status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(scope->ctx, "%s: fact set is unusable", query);
    goto fail;
  }
  if (!outputs_ok) {
    ixs_ctx_push_error(scope->ctx, "%s: %s", query, output_error);
    goto fail;
  }
  for (i = 0; i < nnodes; i++) {
    if (!facts_query_node_ok(scope->ctx, nodes[i], query))
      goto fail;
  }
  if (ixs_bounds_has_empty(&facts->bounds)) {
    scope->status = IXS_FACT_QUERY_COMPLETE;
    goto fail;
  }
  if (!ixs_bounds_query_hold_begin(
          &facts->bounds,
          bounds_query_select_root(&facts->bounds, nodes, nnodes),
          &scope->query_held)) {
    scope->status = IXS_FACT_QUERY_COMPLETE;
    goto fail;
  }
  scope->status = IXS_FACT_QUERY_COMPLETE;
  return true;

fail:
  if (scope->query_held) {
    ixs_bounds_query_hold_end(&facts->bounds);
    scope->query_held = false;
  }
  scope->status = facts_read_query_finish(&scope->read_scope, scope->status);
  ixs_session_unbind(&scope->binding);
  scope->bound = false;
  return false;
}

static void algebra_query_start(algebra_query_scope *scope) {
  scope->scratch_mark = ixs_arena_save(&scope->ctx->scratch);
  scope->diag_mark = ixs_arena_save(&scope->ctx->diag);
  scope->saved_errors = scope->ctx->errors;
  scope->saved_nerrors = scope->ctx->nerrors;
  scope->saved_errors_cap = scope->ctx->errors_cap;
  scope->active = true;
}

static bool algebra_query_finish(algebra_query_scope *scope, bool success) {
  if (scope->active) {
    ixs_arena_restore(&scope->ctx->scratch, scope->scratch_mark);
    ixs_arena_restore(&scope->ctx->diag, scope->diag_mark);
    scope->ctx->errors = scope->saved_errors;
    scope->ctx->nerrors = scope->saved_nerrors;
    scope->ctx->errors_cap = scope->saved_errors_cap;
  }
  if (scope->query_held) {
    ixs_bounds_query_hold_end(&scope->facts->bounds);
    scope->query_held = false;
  }
  if (scope->read_scope.active)
    scope->status = facts_read_query_finish(&scope->read_scope, scope->status);
  if (scope->status != IXS_FACT_QUERY_COMPLETE)
    success = false;
  if (scope->bound)
    ixs_session_unbind(&scope->binding);
  return success;
}

static ixs_node *algebra_query_normalize(algebra_query_scope *scope,
                                         ixs_node *expr) {
  bool limited = false;
  expr = simp_simplify_bounds_status(scope->ctx, expr, &scope->facts->bounds,
                                     &limited);
  if (limited) {
    scope->status = IXS_FACT_QUERY_LIMITED;
    return NULL;
  }
  if (!expr) {
    scope->status = IXS_FACT_QUERY_OOM;
    return NULL;
  }
  if (ixs_node_is_sentinel(expr)) {
    scope->status = IXS_FACT_QUERY_INVALID;
    return NULL;
  }
  expr = expand_impl(scope->ctx, expr);
  if (!expr) {
    scope->status = IXS_FACT_QUERY_OOM;
    return NULL;
  }
  if (ixs_node_is_sentinel(expr)) {
    scope->status = IXS_FACT_QUERY_INVALID;
    return NULL;
  }
  limited = false;
  expr = simp_simplify_bounds_status(scope->ctx, expr, &scope->facts->bounds,
                                     &limited);
  if (limited) {
    scope->status = IXS_FACT_QUERY_LIMITED;
    return NULL;
  }
  if (!expr) {
    scope->status = IXS_FACT_QUERY_OOM;
    return NULL;
  }
  if (ixs_node_is_sentinel(expr)) {
    scope->status = IXS_FACT_QUERY_INVALID;
    return NULL;
  }
  return expr;
}

static bool algebra_query_defined(algebra_query_scope *scope, ixs_node *expr) {
  bool oom = false;
  bool limited = false;
  ixs_check_result result =
      bounds_check_defined_detail(&scope->facts->bounds, expr, &oom, &limited);
  if (oom)
    scope->status = IXS_FACT_QUERY_OOM;
  else if (limited)
    scope->status = IXS_FACT_QUERY_LIMITED;
  return result == IXS_CHECK_TRUE && scope->status == IXS_FACT_QUERY_COMPLETE;
}

static bool algebra_contains_node(algebra_query_scope *scope, ixs_node *root,
                                  ixs_node *target, bool *contains) {
  ixs_arena_mark mark = ixs_arena_save(&scope->ctx->scratch);
  query_node_set visited;
  ixs_node **stack = NULL;
  size_t stack_count = 0;
  size_t stack_capacity = 0;
  bool ok = false;
  *contains = false;
  memset(&visited, 0, sizeof(visited));
  if (!root || !target) {
    scope->status = IXS_FACT_QUERY_INVALID;
    goto cleanup;
  }
  if (!query_node_stack_push(&scope->ctx->scratch, &stack, &stack_count,
                             &stack_capacity, root)) {
    scope->status = IXS_FACT_QUERY_OOM;
    goto cleanup;
  }
  while (stack_count > 0) {
    ixs_node *node = stack[--stack_count];
    uint32_t nchildren;
    uint32_t child;
    bool inserted;
    if (!node || !query_node_set_insert(&scope->ctx->scratch, &visited, node,
                                        &inserted)) {
      scope->status = node ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
      goto cleanup;
    }
    if (!inserted)
      continue;
    if (node == target) {
      *contains = true;
      ok = true;
      goto cleanup;
    }
    if (!defined_child_count(node, &nchildren)) {
      scope->status = IXS_FACT_QUERY_INVALID;
      goto cleanup;
    }
    for (child = 0; child < nchildren; child++) {
      if (!query_node_stack_push(&scope->ctx->scratch, &stack, &stack_count,
                                 &stack_capacity,
                                 defined_child_at(node, child))) {
        scope->status = IXS_FACT_QUERY_OOM;
        goto cleanup;
      }
    }
  }
  ok = true;

cleanup:
  ixs_arena_restore(&scope->ctx->scratch, mark);
  return ok;
}

static bool algebra_scalar_symbol(ixs_ctx *ctx, ixs_node *expr,
                                  ixs_node *symbol, ixs_node **coefficient) {
  if (expr == symbol) {
    *coefficient = ctx->node_one;
    return true;
  }
  if (expr->tag == IXS_MUL && expr->u.mul.nfactors == 1 &&
      expr->u.mul.factors[0].base == symbol &&
      expr->u.mul.factors[0].exp == 1) {
    *coefficient = expr->u.mul.coeff;
    return true;
  }
  return false;
}

static bool algebra_affine_extract(algebra_query_scope *scope, ixs_node *expr,
                                   ixs_node *symbol, ixs_node **coefficient,
                                   ixs_node **residual) {
  ixs_ctx *ctx = scope->ctx;
  ixs_node *symbol_coeff;
  bool contains;
  uint32_t i;

  if (algebra_scalar_symbol(ctx, expr, symbol, &symbol_coeff)) {
    *coefficient = symbol_coeff;
    *residual = ctx->node_zero;
    return true;
  }
  if (expr->tag != IXS_ADD) {
    if (!algebra_contains_node(scope, expr, symbol, &contains) || contains) {
      return false;
    }
    *coefficient = ctx->node_zero;
    *residual = expr;
    return true;
  }

  *coefficient = ctx->node_zero;
  *residual = expr->u.add.coeff;
  for (i = 0; i < expr->u.add.nterms; i++) {
    ixs_node *term = expr->u.add.terms[i].term;
    ixs_node *term_coeff = expr->u.add.terms[i].coeff;
    ixs_node *scaled;
    if (algebra_scalar_symbol(ctx, term, symbol, &symbol_coeff)) {
      scaled = simp_mul(ctx, term_coeff, symbol_coeff);
      if (!scaled || ixs_node_is_sentinel(scaled)) {
        scope->status = !scaled ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
        return false;
      }
      *coefficient = simp_add(ctx, *coefficient, scaled);
      if (!*coefficient || ixs_node_is_sentinel(*coefficient)) {
        scope->status =
            !*coefficient ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
        return false;
      }
      continue;
    }
    if (!algebra_contains_node(scope, term, symbol, &contains) || contains) {
      return false;
    }
    scaled = simp_mul(ctx, term_coeff, term);
    if (!scaled || ixs_node_is_sentinel(scaled)) {
      scope->status = !scaled ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
      return false;
    }
    *residual = simp_add(ctx, *residual, scaled);
    if (!*residual || ixs_node_is_sentinel(*residual)) {
      scope->status = !*residual ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
      return false;
    }
  }
  return ixs_node_is_const(*coefficient);
}

static ixs_constant_difference_result
facts_query_constant_difference(ixs_facts *facts, ixs_node *lhs,
                                ixs_node *rhs) {
  ixs_constant_difference_result result = {IXS_FACT_QUERY_INVALID, false, 0};
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  ixs_node *nodes[2] = {lhs, rhs};
  ixs_fact_query_status detail;
  bool query_held = false;
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx,
                         "constant difference");
  if (!facts_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "constant difference: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, lhs, "constant difference") ||
      !facts_query_node_ok(ctx, rhs, "constant difference"))
    goto cleanup;
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(
          &facts->bounds, bounds_query_select_root(&facts->bounds, nodes, 2),
          &query_held)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  {
    ixs_arena_mark diag_mark = ixs_arena_save(&ctx->diag);
    const char **saved_errors = ctx->errors;
    size_t saved_nerrors = ctx->nerrors;
    size_t saved_errors_cap = ctx->errors_cap;
    detail = constant_difference_query_bound_detail(
        ctx, &facts->bounds, lhs, rhs, &result.difference, &result.available);
    ixs_arena_restore(&ctx->diag, diag_mark);
    ctx->errors = saved_errors;
    ctx->nerrors = saved_nerrors;
    ctx->errors_cap = saved_errors_cap;
  }
  result.status = detail;

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE) {
    result.available = false;
    result.difference = 0;
  }
  ixs_session_unbind(&binding);
  return result;
}

static ixs_affine_decomposition_result
facts_query_affine_decompose(ixs_facts *facts, ixs_node *expr,
                             ixs_node *symbol) {
  algebra_query_scope scope;
  ixs_affine_decomposition_result result = {IXS_FACT_QUERY_INVALID, false, NULL,
                                            NULL};
  ixs_node *nodes[2] = {expr, symbol};
  if (!algebra_query_begin(facts, nodes, 2, "affine decomposition", true, NULL,
                           &scope)) {
    result.status = scope.status;
    return result;
  }
  if (symbol->tag != IXS_SYM) {
    ixs_ctx_push_error(scope.ctx,
                       "affine decomposition: expression must be a symbol");
    scope.status = IXS_FACT_QUERY_INVALID;
    (void)algebra_query_finish(&scope, false);
    result.status = scope.status;
    return result;
  }
  algebra_query_start(&scope);
  if (!algebra_query_defined(&scope, expr))
    goto cleanup;
  expr = algebra_query_normalize(&scope, expr);
  if (!expr)
    goto cleanup;
  result.available = algebra_affine_extract(&scope, expr, symbol,
                                            (ixs_node **)&result.coefficient,
                                            (ixs_node **)&result.residual);

cleanup:
  (void)algebra_query_finish(&scope, result.available);
  result.status = scope.status;
  if (result.status != IXS_FACT_QUERY_COMPLETE) {
    result.available = false;
    result.coefficient = NULL;
    result.residual = NULL;
  }
  return result;
}

static ixs_node *algebra_finite_difference(algebra_query_scope *scope,
                                           ixs_node *expr, ixs_node *symbol,
                                           ixs_node *step) {
  ixs_node *shifted_symbol;
  ixs_node *shifted_expr;
  ixs_node *result;
  bool contains;
  if (!algebra_query_defined(scope, expr) ||
      !algebra_query_defined(scope, step))
    return NULL;
  if (!algebra_contains_node(scope, step, symbol, &contains) || contains)
    return NULL;
  shifted_symbol = simp_add(scope->ctx, symbol, step);
  if (!shifted_symbol) {
    scope->status = IXS_FACT_QUERY_OOM;
    return NULL;
  }
  if (ixs_node_is_sentinel(shifted_symbol)) {
    scope->status = IXS_FACT_QUERY_INVALID;
    return NULL;
  }
  shifted_expr = simp_subs(scope->ctx, expr, symbol, shifted_symbol);
  if (!shifted_expr) {
    scope->status = IXS_FACT_QUERY_OOM;
    return NULL;
  }
  if (ixs_node_is_sentinel(shifted_expr)) {
    scope->status = IXS_FACT_QUERY_INVALID;
    return NULL;
  }
  if (!algebra_query_defined(scope, shifted_expr))
    return NULL;
  result = simp_sub(scope->ctx, shifted_expr, expr);
  if (!result) {
    scope->status = IXS_FACT_QUERY_OOM;
    return NULL;
  }
  if (ixs_node_is_sentinel(result)) {
    scope->status = IXS_FACT_QUERY_INVALID;
    return NULL;
  }
  return algebra_query_normalize(scope, result);
}

static ixs_finite_difference_result
facts_query_finite_difference(ixs_facts *facts, ixs_node *expr,
                              ixs_node *symbol, ixs_node *step) {
  algebra_query_scope scope;
  ixs_finite_difference_result query_result = {IXS_FACT_QUERY_INVALID, false,
                                               NULL};
  ixs_node *nodes[3] = {expr, symbol, step};
  ixs_node *result = NULL;
  if (!algebra_query_begin(facts, nodes, 3, "finite difference", true, NULL,
                           &scope)) {
    query_result.status = scope.status;
    return query_result;
  }
  if (symbol->tag != IXS_SYM) {
    ixs_ctx_push_error(scope.ctx,
                       "finite difference: expression must be a symbol");
    scope.status = IXS_FACT_QUERY_INVALID;
    (void)algebra_query_finish(&scope, false);
    query_result.status = scope.status;
    return query_result;
  }
  algebra_query_start(&scope);
  result = algebra_finite_difference(&scope, expr, symbol, step);
  query_result.available = result != NULL;
  (void)algebra_query_finish(&scope, query_result.available);
  query_result.status = scope.status;
  if (query_result.status == IXS_FACT_QUERY_COMPLETE && query_result.available)
    query_result.difference = result;
  else {
    query_result.available = false;
    query_result.difference = NULL;
  }
  return query_result;
}

static ixs_node *algebra_add_without_constant(ixs_ctx *ctx, ixs_node *expr) {
  ixs_node *residual = ctx->node_zero;
  uint32_t i;
  for (i = 0; i < expr->u.add.nterms; i++) {
    ixs_node *term =
        simp_mul(ctx, expr->u.add.terms[i].coeff, expr->u.add.terms[i].term);
    if (!term || ixs_node_is_sentinel(term))
      return NULL;
    residual = simp_add(ctx, residual, term);
    if (!residual || ixs_node_is_sentinel(residual))
      return NULL;
  }
  return residual;
}

static ixs_additive_constant_result
facts_query_split_additive_constant(ixs_facts *facts, ixs_node *expr) {
  algebra_query_scope scope;
  ixs_additive_constant_result query_result = {IXS_FACT_QUERY_INVALID, false,
                                               NULL, 0};
  ixs_node *nodes[1] = {expr};
  ixs_node *result_residual = NULL;
  int64_t result_constant = 0;
  int64_t q;
  bool ok = false;
  if (!algebra_query_begin(facts, nodes, 1, "additive constant", true, NULL,
                           &scope)) {
    query_result.status = scope.status;
    return query_result;
  }
  algebra_query_start(&scope);
  if (!algebra_query_defined(&scope, expr))
    goto cleanup;
  expr = algebra_query_normalize(&scope, expr);
  if (!expr)
    goto cleanup;
  if (ixs_node_is_const(expr)) {
    ixs_node_get_rat(expr, &result_constant, &q);
    if (q != 1)
      goto cleanup;
    result_residual = scope.ctx->node_zero;
  } else if (expr->tag == IXS_ADD) {
    ixs_node_get_rat(expr->u.add.coeff, &result_constant, &q);
    if (q != 1)
      goto cleanup;
    result_residual = algebra_add_without_constant(scope.ctx, expr);
    if (!result_residual) {
      scope.status = IXS_FACT_QUERY_OOM;
      goto cleanup;
    }
  } else {
    result_residual = expr;
  }
  ok = true;

cleanup:
  (void)algebra_query_finish(&scope, ok);
  query_result.status = scope.status;
  query_result.available = ok && scope.status == IXS_FACT_QUERY_COMPLETE;
  if (query_result.available) {
    query_result.residual = result_residual;
    query_result.constant = result_constant;
  }
  return query_result;
}

static ixs_fact_check_result facts_query_check(ixs_facts *facts,
                                               ixs_node *expr) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  ixs_fact_check_result result = {IXS_FACT_QUERY_INVALID, IXS_CHECK_UNKNOWN};
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "check");
  if (!facts_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "check: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, expr, "check"))
    goto cleanup;
  if (!ixs_node_is_known_true(expr) && !ixs_node_is_known_false(expr) &&
      (expr->tag != IXS_CMP || !ixs_node_is_zero(expr->u.binary.rhs))) {
    ixs_ctx_push_error(ctx,
                       "check: expression must be a normalized comparison");
    goto cleanup;
  }
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  result.check = ixs_bounds_check_query(&facts->bounds, expr);
  result.status = IXS_FACT_QUERY_COMPLETE;

cleanup:
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.check = IXS_CHECK_UNKNOWN;
  ixs_session_unbind(&binding);
  return result;
}

static ixs_fact_check_result facts_query_check_integer_valued(ixs_facts *facts,
                                                              ixs_node *expr) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  bool query_held = false;
  ixs_fact_check_result result = {IXS_FACT_QUERY_INVALID, IXS_CHECK_UNKNOWN};
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "integer valued");
  if (!facts_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "integer valued: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, expr, "integer valued"))
    goto cleanup;
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(&facts->bounds, expr, &query_held)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  result.check = ixs_bounds_check_integer_valued(&facts->bounds, expr);
  result.status = IXS_FACT_QUERY_COMPLETE;

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.check = IXS_CHECK_UNKNOWN;
  ixs_session_unbind(&binding);
  return result;
}

static ixs_fact_check_result facts_query_check_defined(ixs_facts *facts,
                                                       ixs_node *expr) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  bool oom = false;
  bool limited = false;
  bool query_held = false;
  ixs_fact_check_result result = {IXS_FACT_QUERY_INVALID, IXS_CHECK_UNKNOWN};
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "defined");
  if (!facts_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "defined: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, expr, "defined"))
    goto cleanup;
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(&facts->bounds, expr, &query_held)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  result.check =
      bounds_check_defined_detail(&facts->bounds, expr, &oom, &limited);
  result.status = oom       ? IXS_FACT_QUERY_OOM
                  : limited ? IXS_FACT_QUERY_LIMITED
                            : IXS_FACT_QUERY_COMPLETE;

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.check = IXS_CHECK_UNKNOWN;
  ixs_session_unbind(&binding);
  return result;
}

static ixs_fact_check_result
facts_query_check_divisible(ixs_facts *facts, ixs_node *expr, int64_t modulus) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  bool query_held = false;
  ixs_fact_check_result result = {IXS_FACT_QUERY_INVALID, IXS_CHECK_UNKNOWN};
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "divisibility");
  if (!facts_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "divisibility: fact set is unusable");
    goto cleanup;
  }
  if (modulus == 0) {
    ixs_ctx_push_error(ctx, "divisibility: modulus must be nonzero");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, expr, "divisibility"))
    goto cleanup;
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(&facts->bounds, expr, &query_held)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  result.check = ixs_bounds_check_divisible(&facts->bounds, expr, modulus);
  result.status = IXS_FACT_QUERY_COMPLETE;

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.check = IXS_CHECK_UNKNOWN;
  ixs_session_unbind(&binding);
  return result;
}

static ixs_exact_divide_result
exact_divide_result(ixs_exact_divide_status status, ixs_node *quotient) {
  ixs_exact_divide_result result;
  result.status = status;
  result.quotient = quotient;
  return result;
}

static ixs_exact_divide_result
exact_divide_failure(ixs_ctx *ctx, ixs_exact_divide_status status,
                     const char *message) {
  if (ctx && message)
    ixs_ctx_push_error(ctx, "exact divide: %s", message);
  return exact_divide_result(status, NULL);
}

static ixs_fact_query_status
exact_divide_simplify_facts(ixs_facts *facts, ixs_ctx *ctx, ixs_node *expr,
                            ixs_node **simplified) {
  /* Fact simplification is a proof probe; discard scratch and diagnostics. */
  ixs_arena_mark scratch_mark = ixs_arena_save(&ctx->scratch);
  ixs_arena_mark diag_mark = ixs_arena_save(&ctx->diag);
  const char **saved_errors = ctx->errors;
  size_t saved_nerrors = ctx->nerrors;
  size_t saved_errors_cap = ctx->errors_cap;
  bool old_oom = facts->bounds.oom;
  bool limited = false;
  ixs_node *result =
      simp_simplify_bounds_status(ctx, expr, &facts->bounds, &limited);
  ixs_fact_query_status status = IXS_FACT_QUERY_COMPLETE;

  *simplified = NULL;
  if (limited)
    status = IXS_FACT_QUERY_LIMITED;
  else if (!result || (!old_oom && facts->bounds.oom))
    status = IXS_FACT_QUERY_OOM;
  else if (ixs_node_is_sentinel(result))
    status = IXS_FACT_QUERY_INVALID;
  else
    *simplified = result;
  if (status == IXS_FACT_QUERY_OOM)
    bounds_cache_clear(&facts->bounds);
  facts->bounds.oom = old_oom;
  ixs_arena_restore(&ctx->scratch, scratch_mark);
  ixs_arena_restore(&ctx->diag, diag_mark);
  ctx->errors = saved_errors;
  ctx->nerrors = saved_nerrors;
  ctx->errors_cap = saved_errors_cap;
  return status;
}

static bool exact_divide_validate_request(ixs_facts *facts, ixs_ctx *ctx,
                                          ixs_node *expr, int64_t divisor,
                                          ixs_exact_divide_result *result) {
  if (!facts_ready(facts)) {
    *result = exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR,
                                   "fact set is unusable");
    return false;
  }
  if (!expr) {
    *result =
        exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR, "NULL expression");
    return false;
  }
  if (ixs_node_is_sentinel(expr)) {
    *result = exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR,
                                   "sentinel expression is not accepted");
    return false;
  }
  if (!ixs_ctx_owns_node(ctx, expr)) {
    *result = exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR,
                                   "expression belongs to a different context");
    return false;
  }
  if (divisor == 0) {
    *result = exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR,
                                   "divisor must be nonzero");
    return false;
  }
  return true;
}

static bool exact_divide_simplify_input(ixs_facts *facts, ixs_ctx *ctx,
                                        ixs_node *input, ixs_node **simplified,
                                        ixs_exact_divide_result *result) {
  ixs_fact_query_status status =
      exact_divide_simplify_facts(facts, ctx, input, simplified);
  if (status == IXS_FACT_QUERY_COMPLETE)
    return true;
  if (status == IXS_FACT_QUERY_OOM)
    *result =
        exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR, "out of memory");
  else if (status == IXS_FACT_QUERY_LIMITED)
    *result = exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR,
                                   "resource limit exceeded");
  else
    *result = exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR,
                                   "simplification produced invalid state");
  return false;
}

static bool exact_divide_input_defined(ixs_facts *facts, ixs_ctx *ctx,
                                       ixs_node *expr,
                                       ixs_exact_divide_result *result) {
  bool old_bounds_oom = facts->bounds.oom;
  bool defined_oom = false;
  bool defined_limited = false;
  ixs_check_result defined;

  if (ixs_node_is_known_total(expr))
    return true;
  defined = bounds_check_defined_detail(&facts->bounds, expr, &defined_oom,
                                        &defined_limited);
  if (defined_oom) {
    if (!old_bounds_oom && facts->bounds.oom) {
      bounds_cache_clear(&facts->bounds);
      facts->bounds.oom = old_bounds_oom;
    }
    *result =
        exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR, "out of memory");
    return false;
  }
  if (defined_limited) {
    *result = exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR,
                                   "resource limit exceeded");
    return false;
  }
  if (defined != IXS_CHECK_TRUE) {
    *result = exact_divide_result(IXS_EXACT_DIVIDE_UNKNOWN, NULL);
    return false;
  }
  return true;
}

static bool exact_divide_proven(ixs_facts *facts, ixs_ctx *ctx, ixs_node *expr,
                                int64_t divisor,
                                ixs_exact_divide_result *result) {
  bool old_bounds_oom = facts->bounds.oom;
  ixs_check_result proof =
      ixs_bounds_check_divisible(&facts->bounds, expr, divisor);
  if (facts->bounds.oom) {
    if (!old_bounds_oom)
      bounds_cache_clear(&facts->bounds);
    facts->bounds.oom = old_bounds_oom;
    *result =
        exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR, "out of memory");
    return false;
  }
  if (proof == IXS_CHECK_UNKNOWN) {
    *result = exact_divide_result(IXS_EXACT_DIVIDE_UNKNOWN, NULL);
    return false;
  }
  if (proof == IXS_CHECK_FALSE) {
    *result = exact_divide_result(IXS_EXACT_DIVIDE_NOT_EXACT, NULL);
    return false;
  }
  return true;
}

static ixs_node *
exact_divide_piecewise_quotient(ixs_ctx *ctx, ixs_node *expr, ixs_node *divisor,
                                ixs_fact_query_status *status) {
  ixs_arena_mark mark = ixs_arena_save(&ctx->scratch);
  ixs_node **values = NULL;
  ixs_node **conditions = NULL;
  ixs_node *quotient = NULL;
  size_t ncases = expr->u.pw.ncases;
  size_t i;

  if (ncases == 0u || !expr->u.pw.cases ||
      ncases > SIZE_MAX / sizeof(*values)) {
    *status = IXS_FACT_QUERY_INVALID;
    goto cleanup;
  }
  values =
      ixs_arena_alloc(&ctx->scratch, ncases * sizeof(*values), sizeof(void *));
  conditions = ixs_arena_alloc(&ctx->scratch, ncases * sizeof(*conditions),
                               sizeof(void *));
  if (!values || !conditions) {
    *status = IXS_FACT_QUERY_OOM;
    goto cleanup;
  }
  for (i = 0; i < ncases; i++) {
    values[i] = simp_div(ctx, expr->u.pw.cases[i].value, divisor);
    conditions[i] = expr->u.pw.cases[i].cond;
    if (!values[i]) {
      *status = IXS_FACT_QUERY_OOM;
      goto cleanup;
    }
    if (ixs_node_is_sentinel(values[i])) {
      *status = IXS_FACT_QUERY_INVALID;
      goto cleanup;
    }
  }
  quotient = simp_pw(ctx, (uint32_t)ncases, values, conditions);
  if (!quotient)
    *status = IXS_FACT_QUERY_OOM;
  else if (ixs_node_is_sentinel(quotient)) {
    *status = IXS_FACT_QUERY_INVALID;
    quotient = NULL;
  }

cleanup:
  ixs_arena_restore(&ctx->scratch, mark);
  return quotient;
}

static ixs_exact_divide_result
exact_divide_build_quotient(ixs_ctx *ctx, ixs_node *expr, int64_t divisor) {
  ixs_node *divisor_node = ixs_node_int(ctx, divisor);
  ixs_node *quotient;
  ixs_fact_query_status status = IXS_FACT_QUERY_COMPLETE;
  if (!divisor_node)
    return exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR, "out of memory");
  if (expr->tag == IXS_PIECEWISE) {
    quotient =
        exact_divide_piecewise_quotient(ctx, expr, divisor_node, &status);
  } else {
    quotient = simp_div(ctx, expr, divisor_node);
    if (!quotient)
      status = IXS_FACT_QUERY_OOM;
  }
  if (!quotient && status == IXS_FACT_QUERY_OOM)
    return exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR, "out of memory");
  if (!quotient || status == IXS_FACT_QUERY_INVALID ||
      ixs_node_is_sentinel(quotient))
    return exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR,
                                "quotient is not representable");
  quotient = expand_impl(ctx, quotient);
  if (!quotient)
    return exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR, "out of memory");
  if (ixs_node_is_sentinel(quotient))
    return exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR,
                                "quotient expansion failed");
  return exact_divide_result(IXS_EXACT_DIVIDE_PROVEN, quotient);
}

static ixs_exact_divide_result
exact_divide_finish_read_query(facts_read_query_scope *scope,
                               ixs_exact_divide_result result) {
  ixs_fact_query_status status = IXS_FACT_QUERY_COMPLETE;
  if (result.status == IXS_EXACT_DIVIDE_ERROR)
    status = IXS_FACT_QUERY_INVALID;
  status = facts_read_query_finish(scope, status);
  if (status != IXS_FACT_QUERY_COMPLETE)
    return exact_divide_result(IXS_EXACT_DIVIDE_ERROR, NULL);
  return result;
}

ixs_exact_divide_result
ixs_try_exact_divide_facts(ixs_facts *facts, ixs_node *expr, int64_t divisor) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  bool query_held = false;
  ixs_exact_divide_result result =
      exact_divide_result(IXS_EXACT_DIVIDE_ERROR, NULL);

  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "exact divide");
  if (!exact_divide_validate_request(facts, ctx, expr, divisor, &result))
    goto cleanup;
  if (!ixs_bounds_query_hold_begin(&facts->bounds, expr, &query_held)) {
    result =
        facts->bounds.oom
            ? exact_divide_failure(ctx, IXS_EXACT_DIVIDE_ERROR, "out of memory")
            : exact_divide_result(IXS_EXACT_DIVIDE_UNKNOWN, NULL);
    goto cleanup;
  }
  if (!exact_divide_input_defined(facts, ctx, expr, &result))
    goto cleanup;
  if (!exact_divide_simplify_input(facts, ctx, expr, &expr, &result))
    goto cleanup;
  if (!exact_divide_proven(facts, ctx, expr, divisor, &result))
    goto cleanup;
  result = exact_divide_build_quotient(ctx, expr, divisor);
  if (result.status == IXS_EXACT_DIVIDE_PROVEN) {
    ixs_node *quotient = result.quotient;
    if (!exact_divide_simplify_input(facts, ctx, quotient, &result.quotient,
                                     &result))
      goto cleanup;
  }

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result = exact_divide_finish_read_query(&read_scope, result);
  ixs_session_unbind(&binding);
  return result;
}

static ixs_pow2_fact bounds_pow2_fact_from_int64(int64_t value) {
  uint64_t u;
  if (value == 0)
    return IXS_POW2_OR_ZERO;
  if (value < 0)
    return IXS_POW2_UNKNOWN;
  u = (uint64_t)value;
  return (u & (u - 1u)) == 0 ? IXS_POW2_POSITIVE : IXS_POW2_UNKNOWN;
}

static ixs_pow2_query_result facts_query_get_pow2(ixs_facts *facts,
                                                  ixs_node *expr) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  ixs_bitfacts bits;
  ixs_interval iv;
  int64_t exact;
  bool defined_oom = false;
  bool defined_limited = false;
  bool query_held = false;
  ixs_pow2_query_result result = {IXS_FACT_QUERY_INVALID, IXS_POW2_UNKNOWN};
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "power of two");
  if (!facts_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "power of two: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, expr, "power of two"))
    goto cleanup;
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(&facts->bounds, expr, &query_held)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (bounds_check_defined_detail(&facts->bounds, expr, &defined_oom,
                                  &defined_limited) != IXS_CHECK_TRUE ||
      ixs_bounds_check_integer_valued(&facts->bounds, expr) != IXS_CHECK_TRUE) {
    result.status = defined_oom       ? IXS_FACT_QUERY_OOM
                    : defined_limited ? IXS_FACT_QUERY_LIMITED
                                      : IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (ixs_bounds_get_bitfacts(&facts->bounds, expr, &bits))
    result.fact = bits.pow2;
  if (result.fact == IXS_POW2_UNKNOWN) {
    iv = ixs_bounds_get(&facts->bounds, expr);
    if (ixs_interval_is_point_int(iv, &exact))
      result.fact = bounds_pow2_fact_from_int64(exact);
  }
  result.status = IXS_FACT_QUERY_COMPLETE;

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.fact = IXS_POW2_UNKNOWN;
  ixs_session_unbind(&binding);
  return result;
}

static ixs_known_bits_query_result facts_query_get_known_bits(ixs_facts *facts,
                                                              ixs_node *expr) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  ixs_bitfacts bits;
  bool defined_oom = false;
  bool defined_limited = false;
  bool query_held = false;
  ixs_known_bits_query_result result;
  result.status = IXS_FACT_QUERY_INVALID;
  result.bits.known_zero = 0;
  result.bits.known_one = 0;
  result.bits.pow2 = IXS_POW2_UNKNOWN;
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "known bits");
  if (!facts_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "known bits: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, expr, "known bits") ||
      ixs_bounds_has_empty(&facts->bounds)) {
    if (!ixs_bounds_has_empty(&facts->bounds))
      goto cleanup;
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(&facts->bounds, expr, &query_held)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }

  bitfacts_unknown(&bits);
  if (bounds_check_defined_detail(&facts->bounds, expr, &defined_oom,
                                  &defined_limited) == IXS_CHECK_TRUE &&
      ixs_bounds_check_integer_valued(&facts->bounds, expr) == IXS_CHECK_TRUE)
    (void)ixs_bounds_get_bitfacts(&facts->bounds, expr, &bits);
  result.status = defined_oom       ? IXS_FACT_QUERY_OOM
                  : defined_limited ? IXS_FACT_QUERY_LIMITED
                                    : IXS_FACT_QUERY_COMPLETE;
  result.bits.known_zero = bits.known_zero;
  result.bits.known_one = bits.known_one;
  result.bits.pow2 = bits.pow2;

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE) {
    result.bits.known_zero = 0;
    result.bits.known_one = 0;
    result.bits.pow2 = IXS_POW2_UNKNOWN;
  }
  ixs_session_unbind(&binding);
  return result;
}

static ixs_symbol_congruence_result
facts_query_get_symbol_congruence(ixs_facts *facts, ixs_node *symbol) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  ixs_symbol_congruence_result result = {IXS_FACT_QUERY_INVALID, false, 0, 0};
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "symbol congruence");
  if (!facts_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "symbol congruence: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, symbol, "symbol congruence") ||
      ixs_bounds_has_empty(&facts->bounds)) {
    if (!ixs_bounds_has_empty(&facts->bounds))
      goto cleanup;
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (symbol->tag != IXS_SYM) {
    ixs_ctx_push_error(ctx, "symbol congruence: expression must be a symbol");
    goto cleanup;
  }
  result.available = ixs_bounds_get_modrem(&facts->bounds, symbol->u.name,
                                           &result.modulus, &result.residue);
  result.status = IXS_FACT_QUERY_COMPLETE;

cleanup:
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE) {
    result.available = false;
    result.modulus = 0;
    result.residue = 0;
  }
  ixs_session_unbind(&binding);
  return result;
}

static ixs_fact_check_result facts_query_check_congruent(ixs_facts *facts,
                                                         ixs_node *expr,
                                                         int64_t modulus,
                                                         int64_t residue) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  bool query_held = false;
  ixs_fact_check_result result =
      fact_check_result(IXS_FACT_QUERY_INVALID, IXS_CHECK_UNKNOWN);
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "congruence");
  if (!facts_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "congruence: fact set is unusable");
    goto cleanup;
  }
  if (modulus == 0) {
    ixs_ctx_push_error(ctx, "congruence: modulus must be nonzero");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, expr, "congruence"))
    goto cleanup;
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(&facts->bounds, expr, &query_held)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  result.check =
      ixs_bounds_check_congruent(&facts->bounds, expr, modulus, residue);
  result.status = IXS_FACT_QUERY_COMPLETE;

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    result.check = IXS_CHECK_UNKNOWN;
  ixs_session_unbind(&binding);
  return result;
}

static ixs_range_query_result facts_query_range(ixs_facts *facts,
                                                ixs_node *expr) {
  ixs_session_binding binding;
  facts_read_query_scope read_scope;
  ixs_ctx *ctx;
  ixs_interval iv;
  ixs_interval truncating_remainder;
  bool defined_oom = false;
  bool defined_limited = false;
  bool query_held = false;
  ixs_check_result integer_valued;
  bounds_truncating_range_status truncating_status;
  ixs_range_query_result result;
  memset(&result, 0, sizeof(result));
  result.status = IXS_FACT_QUERY_INVALID;
  result.range.lower_q = 1;
  result.range.upper_q = 1;
  if (!facts_bind(facts, &binding, &ctx))
    return result;
  facts_read_query_begin(&read_scope, &facts->bounds, ctx, "range");
  if (!facts_ready(facts)) {
    result.status =
        facts->bounds.oom ? IXS_FACT_QUERY_OOM : IXS_FACT_QUERY_INVALID;
    ixs_ctx_push_error(ctx, "range: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, expr, "range"))
    goto cleanup;
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (!ixs_bounds_query_hold_begin(&facts->bounds, expr, &query_held)) {
    result.status = IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  if (bounds_check_defined_detail(&facts->bounds, expr, &defined_oom,
                                  &defined_limited) != IXS_CHECK_TRUE) {
    result.status = defined_oom       ? IXS_FACT_QUERY_OOM
                    : defined_limited ? IXS_FACT_QUERY_LIMITED
                                      : IXS_FACT_QUERY_COMPLETE;
    goto cleanup;
  }
  result.status = IXS_FACT_QUERY_COMPLETE;
  integer_valued = ixs_bounds_check_integer_valued(&facts->bounds, expr);
  iv = ixs_bounds_get(&facts->bounds, expr);
  if (integer_valued == IXS_CHECK_TRUE) {
    if (!bounds_refine_integral_interval(&facts->bounds, expr,
                                         /*expression_defined=*/true, &iv))
      goto cleanup;
    interval_to_range_result(iv, &result.range);
    result.available = true;
    goto cleanup;
  }
  truncating_status = bounds_get_truncating_remainder_range(
      &facts->bounds, expr, /*expression_defined=*/false,
      &truncating_remainder);
  if (truncating_status == BOUNDS_TRUNCATING_RANGE_MATCH)
    iv = iv_intersect(iv, truncating_remainder);
  else if (truncating_status != BOUNDS_TRUNCATING_RANGE_NO_MATCH) {
    result.status = truncating_status == BOUNDS_TRUNCATING_RANGE_OOM
                        ? IXS_FACT_QUERY_OOM
                    : truncating_status == BOUNDS_TRUNCATING_RANGE_INVALID
                        ? IXS_FACT_QUERY_INVALID
                        : IXS_FACT_QUERY_LIMITED;
    goto cleanup;
  }
  if (!iv.valid || ixs_interval_is_empty(iv))
    goto cleanup;
  interval_to_range_result(iv, &result.range);
  result.available = true;
  result.status = IXS_FACT_QUERY_COMPLETE;

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  result.status = facts_read_query_finish(&read_scope, result.status);
  if (result.status != IXS_FACT_QUERY_COMPLETE) {
    result.available = false;
    memset(&result.range, 0, sizeof(result.range));
    result.range.lower_q = 1;
    result.range.upper_q = 1;
  }
  ixs_session_unbind(&binding);
  return result;
}

static void facts_public_output_error(ixs_facts *facts, const char *query,
                                      const char *message) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  if (!facts_bind(facts, &binding, &ctx))
    return;
  ixs_ctx_push_error(ctx, "%s: %s", query, message);
  ixs_session_unbind(&binding);
}

const ixs_node *ixs_simplify_facts(ixs_facts *facts, const ixs_node *expr) {
  ixs_simplify_result result = facts_query_simplify(facts, (ixs_node *)expr);
  return result.status == IXS_FACT_QUERY_COMPLETE ? result.value : NULL;
}

void ixs_simplify_batch_facts(ixs_facts *facts, const ixs_node **exprs,
                              size_t n) {
  (void)facts_query_simplify_batch(facts, (ixs_node **)exprs, n);
}

ixs_check_result ixs_check_facts(ixs_facts *facts, const ixs_node *expr) {
  ixs_fact_check_result result = facts_query_check(facts, (ixs_node *)expr);
  return result.status == IXS_FACT_QUERY_COMPLETE ? result.check
                                                  : IXS_CHECK_UNKNOWN;
}

ixs_check_result ixs_check_predicate_facts(ixs_facts *facts,
                                           const ixs_node *predicate) {
  ixs_fact_check_result result =
      facts_query_check_predicate(facts, (ixs_node *)predicate);
  return result.status == IXS_FACT_QUERY_COMPLETE ? result.check
                                                  : IXS_CHECK_UNKNOWN;
}

ixs_check_result ixs_equivalent_facts(ixs_facts *facts, const ixs_node *lhs,
                                      const ixs_node *rhs) {
  ixs_fact_check_result result =
      facts_query_equivalent(facts, (ixs_node *)lhs, (ixs_node *)rhs);
  return result.status == IXS_FACT_QUERY_COMPLETE ? result.check
                                                  : IXS_CHECK_UNKNOWN;
}

ixs_check_result ixs_equivalent_finite_domain_facts(ixs_facts *facts,
                                                    const ixs_node *lhs,
                                                    const ixs_node *rhs,
                                                    size_t *remaining_points) {
  ixs_fact_check_result direct;
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_node *predicate;
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  bool query_held = false;

  if (!remaining_points) {
    facts_public_output_error(facts, "finite equivalence",
                              "remaining_points is NULL");
    return IXS_CHECK_UNKNOWN;
  }
  direct = facts_query_equivalent(facts, (ixs_node *)lhs, (ixs_node *)rhs);
  if (direct.status != IXS_FACT_QUERY_COMPLETE ||
      direct.check != IXS_CHECK_UNKNOWN)
    return direct.status == IXS_FACT_QUERY_COMPLETE ? direct.check
                                                    : IXS_CHECK_UNKNOWN;
  if (!facts_bind(facts, &binding, &ctx))
    return IXS_CHECK_UNKNOWN;
  if (!facts_ready(facts) ||
      !facts_query_node_ok(ctx, (ixs_node *)lhs, "finite equivalence") ||
      !facts_query_node_ok(ctx, (ixs_node *)rhs, "finite equivalence") ||
      ixs_bounds_has_empty(&facts->bounds))
    goto cleanup;
  predicate = simp_cmp(ctx, (ixs_node *)lhs, IXS_CMP_EQ, (ixs_node *)rhs);
  if (!predicate || ixs_node_is_sentinel(predicate))
    goto cleanup;
  if (!ixs_bounds_query_hold_begin(&facts->bounds, predicate, &query_held))
    goto cleanup;
  result = predicate_query_finite_domain(&facts->bounds, predicate,
                                         remaining_points);

cleanup:
  if (query_held)
    ixs_bounds_query_hold_end(&facts->bounds);
  ixs_session_unbind(&binding);
  return result;
}

bool ixs_constant_difference_facts(ixs_facts *facts, const ixs_node *lhs,
                                   const ixs_node *rhs, int64_t *delta) {
  ixs_constant_difference_result result;
  if (delta)
    *delta = 0;
  if (!delta) {
    facts_public_output_error(facts, "constant difference", "NULL output");
    return false;
  }
  result =
      facts_query_constant_difference(facts, (ixs_node *)lhs, (ixs_node *)rhs);
  if (result.status != IXS_FACT_QUERY_COMPLETE || !result.available)
    return false;
  *delta = result.difference;
  return true;
}

bool ixs_affine_decompose_facts(ixs_facts *facts, const ixs_node *expr,
                                const ixs_node *symbol,
                                const ixs_node **coefficient,
                                const ixs_node **residual) {
  ixs_affine_decomposition_result result;
  if (coefficient)
    *coefficient = NULL;
  if (residual)
    *residual = NULL;
  if (!coefficient || !residual || coefficient == residual) {
    facts_public_output_error(facts, "affine decomposition",
                              "outputs must be non-NULL and distinct");
    return false;
  }
  result =
      facts_query_affine_decompose(facts, (ixs_node *)expr, (ixs_node *)symbol);
  if (result.status != IXS_FACT_QUERY_COMPLETE || !result.available)
    return false;
  *coefficient = result.coefficient;
  *residual = result.residual;
  return true;
}

bool ixs_decompose_exact_quotient_facts(ixs_facts *facts, const ixs_node *expr,
                                        const ixs_node **numerator,
                                        const ixs_node **denominator) {
  algebra_query_scope scope;
  ixs_node *nodes[1] = {(ixs_node *)expr};
  ixs_node *result_numerator = NULL;
  ixs_node *result_denominator = NULL;
  ixs_quotient_parts_status status;
  bool outputs_ok = numerator && denominator && numerator != denominator;
  bool ok = false;

  if (numerator)
    *numerator = NULL;
  if (denominator)
    *denominator = NULL;
  if (!algebra_query_begin(facts, nodes, 1, "exact quotient decomposition",
                           outputs_ok, "outputs must be non-NULL and distinct",
                           &scope))
    return false;
  algebra_query_start(&scope);
  if (!algebra_query_defined(&scope, nodes[0]))
    goto cleanup;
  nodes[0] = algebra_query_normalize(&scope, nodes[0]);
  if (!nodes[0])
    goto cleanup;
  status = simp_decompose_exact_quotient(scope.ctx, nodes[0], &result_numerator,
                                         &result_denominator);
  if (status == IXS_QUOTIENT_PARTS_OOM)
    scope.status = IXS_FACT_QUERY_OOM;
  else
    ok = status == IXS_QUOTIENT_PARTS_MATCH;

cleanup:
  ok = algebra_query_finish(&scope, ok);
  if (ok) {
    *numerator = result_numerator;
    *denominator = result_denominator;
  }
  return ok;
}

bool ixs_finite_difference_facts(ixs_facts *facts, const ixs_node *expr,
                                 const ixs_node *symbol, const ixs_node *step,
                                 const ixs_node **difference) {
  ixs_finite_difference_result result;
  if (difference)
    *difference = NULL;
  if (!difference) {
    facts_public_output_error(facts, "finite difference", "NULL output");
    return false;
  }
  result = facts_query_finite_difference(facts, (ixs_node *)expr,
                                         (ixs_node *)symbol, (ixs_node *)step);
  if (result.status != IXS_FACT_QUERY_COMPLETE || !result.available)
    return false;
  *difference = result.difference;
  return true;
}

bool ixs_split_additive_constant_facts(ixs_facts *facts, const ixs_node *expr,
                                       const ixs_node **residual,
                                       int64_t *constant) {
  ixs_additive_constant_result result;
  if (residual)
    *residual = NULL;
  if (constant)
    *constant = 0;
  if (!residual || !constant) {
    facts_public_output_error(facts, "additive constant",
                              "outputs must be non-NULL");
    return false;
  }
  result = facts_query_split_additive_constant(facts, (ixs_node *)expr);
  if (result.status != IXS_FACT_QUERY_COMPLETE || !result.available)
    return false;
  *residual = result.residual;
  *constant = result.constant;
  return true;
}

ixs_check_result ixs_check_integer_valued_facts(ixs_facts *facts,
                                                const ixs_node *expr) {
  ixs_fact_check_result result =
      facts_query_check_integer_valued(facts, (ixs_node *)expr);
  return result.status == IXS_FACT_QUERY_COMPLETE ? result.check
                                                  : IXS_CHECK_UNKNOWN;
}

ixs_check_result ixs_check_defined_facts(ixs_facts *facts,
                                         const ixs_node *expr) {
  ixs_fact_check_result result =
      facts_query_check_defined(facts, (ixs_node *)expr);
  return result.status == IXS_FACT_QUERY_COMPLETE ? result.check
                                                  : IXS_CHECK_UNKNOWN;
}

ixs_check_result ixs_check_divisible_facts(ixs_facts *facts,
                                           const ixs_node *expr,
                                           int64_t modulus) {
  ixs_fact_check_result result =
      facts_query_check_divisible(facts, (ixs_node *)expr, modulus);
  return result.status == IXS_FACT_QUERY_COMPLETE ? result.check
                                                  : IXS_CHECK_UNKNOWN;
}

ixs_pow2_fact ixs_get_pow2_fact_facts(ixs_facts *facts, const ixs_node *expr) {
  ixs_pow2_query_result result = facts_query_get_pow2(facts, (ixs_node *)expr);
  return result.status == IXS_FACT_QUERY_COMPLETE ? result.fact
                                                  : IXS_POW2_UNKNOWN;
}

bool ixs_get_known_bits_facts(ixs_facts *facts, const ixs_node *expr,
                              ixs_known_bits *out) {
  ixs_known_bits_query_result result;
  if (out) {
    out->known_zero = 0;
    out->known_one = 0;
    out->pow2 = IXS_POW2_UNKNOWN;
  }
  if (!out) {
    facts_public_output_error(facts, "known bits", "NULL output");
    return false;
  }
  result = facts_query_get_known_bits(facts, (ixs_node *)expr);
  if (result.status != IXS_FACT_QUERY_COMPLETE)
    return false;
  *out = result.bits;
  return true;
}

bool ixs_get_symbol_congruence_facts(ixs_facts *facts, const ixs_node *symbol,
                                     int64_t *modulus, int64_t *residue) {
  ixs_symbol_congruence_result result;
  if (modulus)
    *modulus = 0;
  if (residue)
    *residue = 0;
  if (!modulus || !residue || modulus == residue) {
    facts_public_output_error(facts, "symbol congruence",
                              "outputs must be non-NULL and distinct");
    return false;
  }
  result = facts_query_get_symbol_congruence(facts, (ixs_node *)symbol);
  if (result.status != IXS_FACT_QUERY_COMPLETE || !result.available)
    return false;
  *modulus = result.modulus;
  *residue = result.residue;
  return true;
}

ixs_check_result ixs_check_congruent_facts(ixs_facts *facts,
                                           const ixs_node *expr,
                                           int64_t modulus, int64_t residue) {
  ixs_fact_check_result result =
      facts_query_check_congruent(facts, (ixs_node *)expr, modulus, residue);
  return result.status == IXS_FACT_QUERY_COMPLETE ? result.check
                                                  : IXS_CHECK_UNKNOWN;
}

bool ixs_range_facts(ixs_facts *facts, const ixs_node *expr,
                     ixs_range_result *out) {
  ixs_range_query_result result;
  if (out)
    memset(out, 0, sizeof(*out));
  if (!out) {
    facts_public_output_error(facts, "range", "NULL output");
    return false;
  }
  result = facts_query_range(facts, (ixs_node *)expr);
  if (result.status != IXS_FACT_QUERY_COMPLETE || !result.available)
    return false;
  *out = result.range;
  return true;
}

IXS_STATIC bool ixs_bounds_get_modrem(ixs_bounds *b, const char *name,
                                      int64_t *mod, int64_t *rem) {
  ixs_var_bound *v;
  if (!mod || !rem)
    return false;
  v = find_var(b, name);
  if (!v || v->modulus <= 0)
    return false;
  *mod = v->modulus;
  *rem = v->remainder;
  return true;
}
