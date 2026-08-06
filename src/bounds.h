/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_H
#define IXS_BOUNDS_H

#include "internal.h"

#include "interval.h"
#include "node.h"
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
typedef struct ixs_equality_edge ixs_equality_edge;
typedef struct ixs_bounds_query_state ixs_bounds_query_state;

typedef struct {
  ixs_difference_constraint *incoming;
  ixs_difference_constraint *outgoing;
  int64_t potential;
  size_t queue_epoch;
  size_t hops;
} ixs_difference_var;

typedef struct {
  size_t var_index;
  size_t parent;
  size_t size;
  int64_t offset;
} ixs_exact_var;

typedef struct {
  const char *name; /* interned pointer -- identity compare only */
  ixs_interval iv;
  int64_t modulus;   /* 0 = no info, >0 = sym ≡ remainder (mod modulus) */
  int64_t remainder; /* in [0, modulus) when modulus > 0                */
  ixs_bitfacts bits;
} ixs_var_bound;

typedef struct {
  ixs_node *expr; /* expression pointer -- identity compare only */
  ixs_interval iv;
} ixs_expr_bound;

typedef struct {
  uint64_t lo;
  uint64_t hi;
  bool negative;
} ixs_wide_offset;

typedef struct {
  ixs_node *expr;
  ixs_equality_edge *edges;
  size_t parent;
  size_t rank;
  ixs_wide_offset offset;
} ixs_equality_endpoint;

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
  ixs_difference_constraint **difference_index;
  ixs_difference_var *difference_vars;
  size_t ndifferences;
  size_t ndifference_vars;
  size_t difference_index_cap;
  size_t difference_var_cap;
  size_t difference_epoch;
  ixs_exact_var *exact_vars;
  size_t *exact_index;
  size_t nexact_vars;
  size_t exact_var_cap;
  size_t exact_index_cap;
  ixs_equality_endpoint *equality_endpoints;
  size_t *equality_endpoint_index;
  size_t nequality_endpoints;
  size_t equality_endpoint_cap;
  size_t equality_endpoint_index_cap;
  ixs_equality_edge **equality_index;
  size_t nequalities;
  size_t equality_index_cap;
  ixs_node **nonzero; /* expressions excluded from zero by NE predicates */
  size_t nnonzero;
  size_t nonzero_cap;
  ixs_bounds_cache_entry *cache; /* direct-mapped interval cache */
  size_t cache_cap;
  unsigned range_pw_depth;
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
  unsigned query_tracking_depth;
  /* Scoped guard for intrinsic endpoint proofs.  Equality projection must not
   * use the relation being justified to prove its own domain. */
  unsigned equality_disabled_depth;
  bool query_state_owner;
  bool query_state_borrowed;
  bool equality_projection_cache_transient;
  bool *semantic_changed; /* optional fact-mutation observer */
  ixs_arena *scratch;     /* borrowed; must outlive ixs_bounds */
} ixs_bounds;

struct ixs_facts {
  ixs_session_impl *impl;
  ixs_ctx *ctx;
  uint64_t epoch;
  bool usable;
  ixs_bounds bounds;
};

/* Internal hooks for bounded mutual-query regression tests. */
#ifndef IXS_AMALGAMATED
IXS_STATIC void ixs_bounds_query_stats(const ixs_bounds *b, size_t *visits,
                                       size_t *stride_visits,
                                       size_t *range_pw_case_visits,
                                       size_t *range_pw_limit_blocks,
                                       size_t *cache_hits, size_t *cycle_blocks,
                                       size_t *limit_blocks,
                                       size_t *active_count, size_t *nesting);
IXS_STATIC void ixs_bounds_equality_query_stats(
    const ixs_bounds *b, size_t *walks, size_t *endpoint_visits,
    size_t *edge_visits, size_t *defined_checks,
    size_t *intrinsic_evaluations);
/* Test hook: re-enter one active interval key and verify clean unwind. */
IXS_STATIC bool ixs_bounds_query_cycle_probe(ixs_bounds *b, ixs_node *expr);
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

/* Release bounds-owned contextless query workspace; arena-backed bounds
 * storage remains owned by the caller. */
IXS_STATIC void ixs_bounds_destroy(ixs_bounds *b);

/* Deep-copy bounds onto the shared scratch arena.  An active source query is
 * borrowed by the fork, so the source hold and scratch arena must outlive the
 * fork.  The fork owns a separate, initially empty query arena. */
IXS_STATIC bool ixs_bounds_fork(ixs_bounds *dst, const ixs_bounds *src);

/* Extract variable bounds from one validated CMP assumption. */
IXS_STATIC bool ixs_bounds_add_assumption(ixs_bounds *b, ixs_node *assumption);

/* Store an explicit interval for an arbitrary expression node. */
IXS_STATIC void ixs_bounds_add_expr(ixs_bounds *b, ixs_node *expr,
                                    ixs_interval iv);

/* Get the interval for an expression using propagation rules. */
IXS_STATIC ixs_interval ixs_bounds_get(ixs_bounds *b, ixs_node *expr);

/* Prove and return the representable inclusive integer domain of expr. */
IXS_STATIC bool ixs_bounds_get_integer_range(ixs_bounds *b, ixs_node *expr,
                                             ixs_integer_range_result *out);

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

#endif /* IXS_BOUNDS_H */
