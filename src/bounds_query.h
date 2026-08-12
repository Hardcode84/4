/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_QUERY_H
#define IXS_BOUNDS_QUERY_H

#include "bounds.h"

typedef enum {
  BOUNDS_QUERY_INTERVAL = 1,
  BOUNDS_QUERY_BITFACTS = 2,
  BOUNDS_QUERY_RESIDUE = 3,
  BOUNDS_QUERY_STRIDE = 4,
  BOUNDS_QUERY_EXACT_INTEGER = 5,
  BOUNDS_QUERY_EQUIVALENCE = 6
} bounds_query_kind;

/* VALUE and NO_FACT are semantic outcomes.  LIMITED, INVALID, and OOM are
 * transport failures: once observed they poison the whole current query
 * generation, so no parent can publish or reuse a partial semantic miss. */
typedef enum {
  BOUNDS_QUERY_OUTCOME_PENDING,
  BOUNDS_QUERY_OUTCOME_VALUE,
  BOUNDS_QUERY_OUTCOME_NO_FACT,
  BOUNDS_QUERY_OUTCOME_LIMITED = 4,
  BOUNDS_QUERY_OUTCOME_INVALID = 5,
  BOUNDS_QUERY_OUTCOME_OOM = 6
} bounds_query_outcome;

typedef enum {
  IXS_BOUNDS_TRANSPORT_CLEAN,
  IXS_BOUNDS_TRANSPORT_LIMITED,
  IXS_BOUNDS_TRANSPORT_OOM,
  IXS_BOUNDS_TRANSPORT_INVALID
} ixs_bounds_transport_status;

typedef struct {
  size_t limit_blocks;
  size_t invalid_blocks;
  uint64_t generation;
  bool oom;
  ixs_bounds_transport_status inherited;
} ixs_bounds_transport_snapshot;

typedef struct {
  bounds_query_kind kind;
  uint64_t owner;
  ixs_node *expr;
  union {
    uint64_t argument;
    ixs_node *peer;
  } selector;
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
    int64_t exact_integer;
    ixs_check_result equivalence;
    struct {
      uint64_t modulus;
      uint64_t residue;
    } stride;
  } result;
} bounds_query_cache_entry;

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

typedef struct {
  uint64_t owner;
  bool active;
} bounds_query_owner_scope;

IXS_STATIC void bounds_query_init(ixs_bounds *bounds);
IXS_STATIC void bounds_query_destroy(ixs_bounds *bounds);
IXS_STATIC void bounds_query_inherit_fork(ixs_bounds *dst,
                                          const ixs_bounds *src);
IXS_STATIC void bounds_query_note_oom(ixs_bounds *bounds);
IXS_STATIC void bounds_query_note_limit(ixs_bounds *bounds);
IXS_STATIC void bounds_query_note_invalid(ixs_bounds *bounds);
IXS_STATIC bool
bounds_query_limited_since(const ixs_bounds *bounds,
                           ixs_bounds_transport_snapshot before);
IXS_STATIC bool
bounds_query_invalid_since(const ixs_bounds *bounds,
                           ixs_bounds_transport_snapshot before);
IXS_STATIC size_t bounds_query_cycle_count(const ixs_bounds *bounds);
/* Raw central-state transport; contradiction and bounds-local OOM are mapped
 * by the consuming query boundary. */
IXS_STATIC ixs_bounds_transport_status
bounds_query_state_transport(const ixs_bounds *bounds);
IXS_STATIC void bounds_query_refresh_owner(ixs_bounds *bounds);
IXS_STATIC void bounds_query_owner_scope_begin(ixs_bounds *bounds,
                                               bounds_query_owner_scope *scope);
IXS_STATIC void bounds_query_owner_scope_end(ixs_bounds *bounds,
                                             bounds_query_owner_scope *scope);
IXS_STATIC bool bounds_query_is_tracking(const ixs_bounds *bounds);
IXS_STATIC const ixs_node *bounds_query_select_root(const ixs_bounds *bounds,
                                                    ixs_node *const *nodes,
                                                    size_t nnodes);
IXS_STATIC bounds_query_enter_result
bounds_query_begin(ixs_bounds *bounds, bounds_query_kind kind, ixs_node *expr,
                   uint64_t argument, bounds_query_scope *scope,
                   bounds_query_cache_entry **cached);
IXS_STATIC bounds_query_enter_result bounds_query_begin_pair(
    ixs_bounds *bounds, bounds_query_kind kind, ixs_node *expr, ixs_node *peer,
    bounds_query_scope *scope, bounds_query_cache_entry **cached);
IXS_STATIC bounds_query_cache_entry *
bounds_query_finish(bounds_query_scope *scope, bool success);
IXS_STATIC bool bounds_query_should_track(const ixs_bounds *bounds,
                                          const ixs_node *expr);
IXS_STATIC void bounds_query_reset_arena(ixs_bounds *bounds);

/* Bound one complete fact-backed query. Nested holds share the generation,
 * recursion guard, and transport. `entered` distinguishes a real hold from
 * the direct path for a flat root. */
IXS_STATIC bool ixs_bounds_query_hold_begin(ixs_bounds *bounds,
                                            const ixs_node *root,
                                            bool *entered);
IXS_STATIC bool bounds_query_force_hold_begin(ixs_bounds *bounds,
                                              bool *entered);
IXS_STATIC void ixs_bounds_query_hold_end(ixs_bounds *bounds);

IXS_STATIC ixs_bounds_transport_snapshot
ixs_bounds_query_transport_snapshot(const ixs_bounds *bounds);
IXS_STATIC ixs_bounds_transport_status ixs_bounds_query_transport_since(
    const ixs_bounds *bounds, ixs_bounds_transport_snapshot snapshot);
IXS_STATIC bool ixs_bounds_query_transport_clean(const ixs_bounds *bounds);

/* Internal hooks emitted only by the test-instrumented library. */
#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
typedef enum {
  IXS_BOUNDS_TEST_TRANSPORT_VALUE,
  IXS_BOUNDS_TEST_TRANSPORT_LIMITED,
  IXS_BOUNDS_TEST_TRANSPORT_INVALID
} ixs_bounds_test_transport;

IXS_STATIC void ixs_bounds_query_stats(const ixs_bounds *bounds, size_t *visits,
                                       size_t *stride_visits,
                                       size_t *cache_hits, size_t *cycle_blocks,
                                       size_t *limit_blocks,
                                       size_t *active_count, size_t *nesting);
IXS_STATIC bool ixs_bounds_query_cycle_probe(ixs_bounds *bounds,
                                             ixs_node *expr);
IXS_STATIC bool
ixs_bounds_query_transport_probe(ixs_bounds *bounds, ixs_node *expr,
                                 ixs_bounds_test_transport injected,
                                 ixs_bounds_test_transport *observed);
#endif

#endif /* IXS_BOUNDS_QUERY_H */
