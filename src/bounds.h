/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_H
#define IXS_BOUNDS_H

#include "internal.h"

#include "algebra_status.h"
#include "bounds_assume.h"
#include "bounds_bitfacts.h"
#include "bounds_integer.h"
#include "bounds_residue.h"
#include "bounds_stride.h"
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

typedef struct ixs_difference_constraint ixs_difference_constraint;
typedef struct ixs_difference_var ixs_difference_var;
typedef struct ixs_bounds_query_state ixs_bounds_query_state;

/* Scratch-local pointer set shared by iterative proof components. */
typedef struct {
  ixs_node **slots;
  size_t capacity;
  size_t count;
} query_node_set;

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

typedef struct ixs_bounds {
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
  ixs_node **nonzero;    /* dense insertion order; first four scan directly */
  size_t *nonzero_index; /* dense indices plus one after the fourth entry */
  size_t nnonzero;
  size_t nonzero_cap;
  size_t nonzero_index_cap;
  ixs_bounds_cache_entry *cache; /* direct-mapped interval cache */
  size_t cache_cap;
  size_t range_pw_depth;
  bool has_modrem;
  bool contradiction;
  bool empty_cache_valid;
  bool empty_cache_value;
  bool oom;
  /* Contextless central query state must outlive temporary proof restores.
   * Context-backed state uses the context arena instead. */
  ixs_arena query_state_arena;
  /* Operation-bounded proof and fork/contextless relation-projection
   * workspace. */
  ixs_arena query_arena;
  ixs_bounds_query_state *query_state;
  uint64_t query_owner;
  /* Owner-local exact-component projection memo. Its generation is independent
   * of query_owner. Persistent facts reuse one table across scalar queries;
   * forks use scratch-local tables, and facts_commit reuses the destination's
   * persistent allocation. */
  void *equality_projection_cache;
  size_t equality_projection_cache_count;
  size_t equality_projection_cache_capacity;
  size_t query_tracking_depth;
  uint32_t equality_projection_cache_generation;
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

IXS_STATIC void
ixs_facts_closure_cache_stats(const ixs_ctx *ctx,
                              ixs_facts_closure_cache_stats_result *stats);
IXS_STATIC ixs_check_result ixs_bounds_equivalence_subproof_limit_probe(
    ixs_facts *facts, const ixs_node *lhs, const ixs_node *rhs);
IXS_STATIC ixs_check_result ixs_bounds_equivalence_quotient_limit_probe(
    ixs_facts *facts, const ixs_node *lhs, const ixs_node *rhs);
#endif
/* Returns false on OOM (arena exhausted). */
IXS_STATIC bool ixs_bounds_init(ixs_bounds *b, ixs_arena *scratch);
IXS_STATIC bool ixs_bounds_init_ctx(ixs_bounds *b, ixs_ctx *ctx,
                                    ixs_arena *scratch);

/* Exact total-integer query used by typed algebra components. */
IXS_STATIC ixs_algebra_status ixs_bounds_check_integer_domain(ixs_bounds *b,
                                                              ixs_node *expr);

IXS_STATIC bool query_node_set_insert(ixs_arena *arena, query_node_set *set,
                                      ixs_node *node, bool *inserted);
IXS_STATIC bool query_node_stack_push(ixs_arena *arena, ixs_node ***stack,
                                      size_t *count, size_t *capacity,
                                      ixs_node *node);

/* Release bounds-owned query workspace; context-backed central state remains
 * context-owned. Arena-backed semantic bounds storage remains caller-owned. */
IXS_STATIC void ixs_bounds_destroy(ixs_bounds *b);

/* Deep-copy bounds onto the shared scratch arena.  An active source query
 * lends only its central state, so the source hold and scratch arena must
 * outlive the fork.  The fork's embedded arenas start empty; context-backed
 * central state allocates in the context arena instead of query_state_arena. */
IXS_STATIC bool ixs_bounds_fork(ixs_bounds *dst, const ixs_bounds *src);

/* Discard query results after a failed read while preserving semantic facts. */
IXS_STATIC void ixs_bounds_reset_read_cache(ixs_bounds *b, bool old_oom);

/* Upper proof-policy seams used by assumption ingestion. */
IXS_STATIC ixs_node *bounds_canonical_expr(ixs_bounds *b, ixs_node *expr);
IXS_STATIC void bounds_admit_exact_relation(ixs_bounds *b, ixs_node *lhs,
                                            ixs_node *rhs, int64_t offset);
IXS_STATIC ixs_check_result bounds_cmp_atom(ixs_bounds *b, ixs_node *cmp);
IXS_STATIC ixs_bounds_build_status bounds_ingest_predicate_branch(
    ixs_ctx *ctx, ixs_bounds *bounds, ixs_node *predicate);
/* Lower proof services borrow these query-policy operations. */
IXS_STATIC ixs_interval bounds_get_intrinsic(ixs_bounds *b, ixs_node *expr);
IXS_STATIC ixs_interval bounds_get_tracked(ixs_bounds *b, ixs_node *expr);
IXS_STATIC bool bounds_add_known_divisible(ixs_bounds *b, ixs_node *expr,
                                           int64_t modulus);
IXS_STATIC ixs_node *bounds_condition_assumption(ixs_bounds *bounds,
                                                 ixs_node *condition,
                                                 bool value,
                                                 struct ixs_node_impl *storage);
IXS_STATIC ixs_check_result bounds_condition_truth(ixs_bounds *bounds,
                                                   ixs_node *condition);

/* Get the interval for an expression using propagation rules. */
IXS_STATIC ixs_interval ixs_bounds_get(ixs_bounds *b, ixs_node *expr);

/* True if stored bounds contain a direct contradiction. */
IXS_STATIC bool ixs_bounds_has_empty(ixs_bounds *b);

/* Public-query semantics over an already populated bounds environment. */
IXS_STATIC ixs_check_result ixs_bounds_check_divisible(ixs_bounds *b,
                                                       ixs_node *expr,
                                                       int64_t modulus);
IXS_STATIC ixs_check_result ixs_bounds_check_congruent(ixs_bounds *b,
                                                       ixs_node *expr,
                                                       int64_t modulus,
                                                       int64_t residue);
IXS_STATIC ixs_check_result ixs_bounds_check_defined(ixs_bounds *b,
                                                     ixs_node *expr);

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
