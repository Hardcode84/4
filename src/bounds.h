/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_H
#define IXS_BOUNDS_H

#include "internal.h"

#include "interval.h"
#include "node.h"
#include "relation_algebra.h"
#include <ixsimpl.h>

/*
 * Lightweight interval analysis for bound-dependent rewrites.
 * Stores per-variable intervals extracted from comparison assumptions,
 * and propagates through expression structure.
 *
 * The var table is a growable array on the scratch arena with an
 * open-addressed index keyed by interned symbol-name pointers.
 */

typedef struct {
  uint64_t known_zero; /* low 64 bits known to be zero */
  uint64_t known_one;  /* low 64 bits known to be one */
  ixs_pow2_fact pow2;
} ixs_bitfacts;

typedef struct ixs_difference_constraint ixs_difference_constraint;
typedef struct ixs_bounds_query_state ixs_bounds_query_state;

/* Scratch-local pointer set shared by iterative proof components. */
typedef struct {
  ixs_node **slots;
  size_t capacity;
  size_t count;
} query_node_set;

typedef struct {
  ixs_difference_constraint *incoming;
  ixs_difference_constraint *outgoing;
  int64_t potential;
  size_t queue_epoch;
  size_t hops;
} ixs_difference_var;

typedef struct {
  const char *name; /* interned pointer -- identity compare only */
  ixs_interval iv;
  int64_t modulus;   /* 0 = no info, >0 = sym == remainder (mod modulus) */
  int64_t remainder; /* in [0, modulus) when modulus > 0                */
  ixs_bitfacts bits;
} ixs_var_bound;

typedef struct {
  ixs_node *expr; /* expression pointer -- identity compare only */
  ixs_interval iv;
} ixs_expr_bound;

typedef struct {
  size_t expr_index; /* stable dense index, never an exprs-array pointer */
  size_t next;       /* one-based watcher index, zero ends the list */
} ixs_mod_inverse_watcher;

typedef struct {
  ixs_node *expr;
  ixs_interval iv;
  bool equality_disabled;
} ixs_bounds_cache_entry;

typedef struct {
  ixs_ctx *ctx;        /* optional; enables expression canonical aliases */
  ixs_ctx *store_ctx;  /* stable owner while ctx is temporarily disabled */
  ixs_var_bound *vars; /* arena-allocated growable array */
  size_t nvars;
  size_t cap;
  size_t *var_index; /* open-addressed dense-index table */
  size_t var_index_cap;
  ixs_expr_bound *exprs; /* per-expression overrides from branch conditions */
  size_t *expr_index;    /* open-addressed dense-index table */
  size_t nexprs;
  size_t expr_cap;
  size_t expr_index_cap;
  /* Reverse incident lists for Mod(raw_symbol, positive_literal) overrides.
   * Heads are indexed by the stable variable index; watcher nodes reference
   * stable dense expression indices so array growth cannot invalidate them. */
  size_t *mod_inverse_heads;
  size_t mod_inverse_head_cap;
  ixs_mod_inverse_watcher *mod_inverse_watchers;
  size_t nmod_inverse_watchers;
  size_t mod_inverse_watcher_cap;
  size_t mod_inverse_watch_visits; /* internal work-bound test counter */
  ixs_difference_constraint **difference_index;
  ixs_difference_var *difference_vars;
  size_t ndifferences;
  size_t ndifference_vars;
  size_t difference_index_cap;
  size_t difference_var_cap;
  size_t difference_epoch;
  ixs_relation_algebra relations;
  ixs_node **nonzero; /* expressions excluded from zero by NE predicates */
  size_t nnonzero;
  size_t nonzero_cap;
  ixs_bounds_cache_entry *cache; /* direct-mapped interval cache */
  size_t cache_cap;
  size_t range_pw_depth;
  bool has_modrem;
  bool contradiction;
  bool empty_cache_valid;
  bool empty_cache_value;
  bool oom;
  /* Contextless query state and its growable tables live here.  Context-backed
   * bounds use the context arena instead, but still own this empty arena so a
   * fork never aliases arena ownership with its source. */
  ixs_arena query_arena;
  ixs_bounds_query_state *query_state;
  uint64_t query_owner;
  /* Owner-local exact-component projection memo.  Persistent fact bounds reuse
   * one table across scalar queries; forks use scratch-local transient tables
   * and facts_commit reuses the destination's persistent allocation. */
  void *equality_projection_cache;
  size_t equality_projection_cache_count;
  size_t equality_projection_cache_capacity;
  size_t query_tracking_depth;
  /* Scoped guard for intrinsic endpoint proofs.  Equality projection must not
   * use the relation being justified to prove its own domain. */
  unsigned equality_disabled_depth;
  /* Prevent predicate EQ/NE fallback from recursively re-entering itself. */
  unsigned predicate_equivalence_depth;
  /* Exact proofs own their structural traversal.  Auxiliary interval and
   * predicate probes may re-enter once, but cannot form an unbounded C call
   * chain through another exact proof. */
  unsigned exact_proof_call_depth;
  bool interval_evaluating;
  bool query_state_owner;
  bool query_state_borrowed;
  bool equality_projection_cache_transient;
  bool *semantic_changed; /* optional fact-mutation observer */
  ixs_arena *scratch;     /* borrowed; must outlive ixs_bounds */
} ixs_bounds;

struct ixs_facts {
  ixs_session_impl *impl;
  ixs_facts *session_next;
  ixs_ctx *ctx;
  uint64_t epoch;
  bool usable;
  ixs_bounds bounds;
};

/* Internal hooks emitted only by the test-instrumented library. */
#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
typedef struct {
  size_t lookups;
  size_t hits;
  size_t stores;
  size_t bypasses;
  size_t entries;
  size_t retained_bytes;
  size_t retained_limit;
  size_t slot_node_capacity;
} ixs_facts_closure_cache_stats_result;

typedef enum {
  IXS_BOUNDS_TEST_TRANSPORT_VALUE,
  IXS_BOUNDS_TEST_TRANSPORT_LIMITED,
  IXS_BOUNDS_TEST_TRANSPORT_INVALID
} ixs_bounds_test_transport;

IXS_STATIC void
ixs_facts_closure_cache_stats(const ixs_ctx *ctx,
                              ixs_facts_closure_cache_stats_result *stats);
IXS_STATIC void ixs_bounds_query_stats(const ixs_bounds *b, size_t *visits,
                                       size_t *stride_visits,
                                       size_t *range_pw_case_visits,
                                       size_t *range_pw_limit_blocks,
                                       size_t *cache_hits, size_t *cycle_blocks,
                                       size_t *limit_blocks,
                                       size_t *active_count, size_t *nesting);
IXS_STATIC ixs_check_result ixs_bounds_equivalence_subproof_limit_probe(
    ixs_facts *facts, const ixs_node *lhs, const ixs_node *rhs);
IXS_STATIC ixs_check_result ixs_bounds_equivalence_quotient_limit_probe(
    ixs_facts *facts, const ixs_node *lhs, const ixs_node *rhs);
/* Test hook: re-enter one active interval key and verify clean unwind. */
IXS_STATIC bool ixs_bounds_query_cycle_probe(ixs_bounds *b, ixs_node *expr);
/* Test hooks keep private query-cache and residue-walker types out of tests. */
IXS_STATIC bool
ixs_bounds_query_transport_probe(ixs_bounds *b, ixs_node *expr,
                                 ixs_bounds_test_transport injected,
                                 ixs_bounds_test_transport *observed);
IXS_STATIC bool ixs_bounds_known_residue_probe(ixs_bounds *b, ixs_node *expr,
                                               uint64_t modulus,
                                               uint64_t *residue);
#endif
/* Returns false on OOM (arena exhausted). */
IXS_STATIC bool ixs_bounds_init(ixs_bounds *b, ixs_arena *scratch);
IXS_STATIC bool ixs_bounds_init_ctx(ixs_bounds *b, ixs_ctx *ctx,
                                    ixs_arena *scratch);

/* Bound one complete fact-backed query.  Nested holds share the same
 * generation, recursion guard, and Piecewise budget.  `entered` distinguishes
 * a real tracked hold from the intentional direct path for a flat root. */
IXS_STATIC bool ixs_bounds_query_hold_begin(ixs_bounds *b, const ixs_node *root,
                                            bool *entered);
IXS_STATIC void ixs_bounds_query_hold_end(ixs_bounds *b);

/* True while nested proof queries have not reported a transport failure. */
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

IXS_STATIC ixs_bounds_transport_snapshot
ixs_bounds_query_transport_snapshot(const ixs_bounds *b);
IXS_STATIC ixs_bounds_transport_status ixs_bounds_query_transport_since(
    const ixs_bounds *b, ixs_bounds_transport_snapshot snapshot);
IXS_STATIC bool ixs_bounds_query_transport_clean(const ixs_bounds *b);

IXS_STATIC bool query_node_set_insert(ixs_arena *arena, query_node_set *set,
                                      ixs_node *node, bool *inserted);
IXS_STATIC bool query_node_stack_push(ixs_arena *arena, ixs_node ***stack,
                                      size_t *count, size_t *capacity,
                                      ixs_node *node);

/* Release bounds-owned contextless query workspace; arena-backed bounds
 * storage remains owned by the caller. */
IXS_STATIC void ixs_bounds_destroy(ixs_bounds *b);

/* Deep-copy bounds onto the shared scratch arena.  An active source query is
 * borrowed by the fork, so the source hold and scratch arena must outlive the
 * fork.  The fork owns a separate, initially empty query arena. */
IXS_STATIC bool ixs_bounds_fork(ixs_bounds *dst, const ixs_bounds *src);

/* Discard query results after a failed read while preserving semantic facts. */
IXS_STATIC void ixs_bounds_reset_read_cache(ixs_bounds *b, bool old_oom);

/* Extract variable bounds from one validated CMP assumption. */
IXS_STATIC bool ixs_bounds_add_assumption(ixs_bounds *b, ixs_node *assumption);

/* Store an explicit interval for an arbitrary expression node. */
IXS_STATIC void ixs_bounds_add_expr(ixs_bounds *b, ixs_node *expr,
                                    ixs_interval iv);

/* Get the interval for an expression using propagation rules. */
IXS_STATIC ixs_interval ixs_bounds_get(ixs_bounds *b, ixs_node *expr);

/* True if stored bounds contain a direct contradiction. */
IXS_STATIC bool ixs_bounds_has_empty(ixs_bounds *b);

/* Full modulus/remainder query.  Returns true when info is available.
 * On success *mod > 0 and 0 <= *rem < *mod. */
IXS_STATIC bool ixs_bounds_get_modrem(ixs_bounds *b, const char *name,
                                      int64_t *mod, int64_t *rem);

/* Low-bit and power-of-two facts inferred from assumptions and constants. */
IXS_STATIC bool ixs_bounds_get_bitfacts(ixs_bounds *b, ixs_node *expr,
                                        ixs_bitfacts *out);
IXS_STATIC bool ixs_bounds_is_pow2_or_zero(ixs_bounds *b, ixs_node *expr);
IXS_STATIC bool ixs_bounds_is_pow2_positive(ixs_bounds *b, ixs_node *expr);

/* True when expr is provably divisible by m (m > 0) given bounds. */
IXS_STATIC bool ixs_bounds_is_known_divisible(ixs_bounds *b, ixs_node *expr,
                                              int64_t m);

/* True when expr is provably integer-valued given congruence info. */
IXS_STATIC bool ixs_bounds_is_integer_with_divinfo(ixs_bounds *b,
                                                   ixs_node *expr);

/* Public-query semantics over an already populated bounds environment. */
IXS_STATIC ixs_check_result ixs_bounds_check_integer_valued(ixs_bounds *b,
                                                            ixs_node *expr);
IXS_STATIC ixs_check_result ixs_bounds_check_divisible(ixs_bounds *b,
                                                       ixs_node *expr,
                                                       int64_t modulus);
IXS_STATIC ixs_check_result ixs_bounds_check_congruent(ixs_bounds *b,
                                                       ixs_node *expr,
                                                       int64_t modulus,
                                                       int64_t residue);
IXS_STATIC ixs_check_result ixs_bounds_check_defined(ixs_bounds *b,
                                                     ixs_node *expr);

typedef enum {
  IXS_BOUNDS_BUILD_OK,
  IXS_BOUNDS_BUILD_INVALID,
  IXS_BOUNDS_BUILD_LIMIT,
  IXS_BOUNDS_BUILD_OOM
} ixs_bounds_build_status;

IXS_STATIC ixs_bounds_build_status
ixs_bounds_build_ctx(ixs_bounds *b, ixs_ctx *ctx, ixs_arena *scratch,
                     ixs_node *const *assumptions, size_t n_assumptions);

/* Check a normalized CMP node (lhs op 0) against current bounds.
 * Returns IXS_CHECK_TRUE / FALSE / UNKNOWN.  Non-CMP input or
 * non-zero rhs returns UNKNOWN. */
IXS_STATIC ixs_check_result ixs_bounds_check(ixs_bounds *b, ixs_node *cmp);

/* Complete public scalar check.  One query generation spans the fast bounds
 * check and the exact EQ/NE fallback, so all callers observe one proof
 * contract and one resource outcome. */
IXS_STATIC ixs_check_result ixs_bounds_check_query(ixs_bounds *b,
                                                   ixs_node *cmp);

#endif /* IXS_BOUNDS_H */
