/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_FACTS_STORE_H
#define IXS_FACTS_STORE_H

#include "bounds.h"
#include "bounds_store.h"

#define FACTS_QUERY_IDENTITY_CACHE_CAP 32u
#define FACTS_SIMPLIFY_CACHE_CAP 64u

typedef struct {
  ixs_node *source;
  ixs_check_result result;
  uint32_t generation;
} facts_query_identity_entry;

typedef struct {
  ixs_node *source;
  ixs_node *result;
  uint32_t generation;
} facts_query_simplify_entry;

struct facts_query_cache {
  facts_query_identity_entry identity[FACTS_QUERY_IDENTITY_CACHE_CAP];
  facts_query_simplify_entry simplify[FACTS_SIMPLIFY_CACHE_CAP];
  uint64_t domain_id;
  uint32_t generation;
#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
  size_t identity_hits;
  size_t identity_stores;
  size_t simplify_hits;
  size_t simplify_stores;
#endif
};

struct ixs_facts {
  ixs_session_impl *impl;
  ixs_facts *session_next;
  ixs_ctx *ctx;
  uint64_t epoch;
  uint64_t query_version;
  bool usable;
  ixs_bounds bounds;
};

static inline bool facts_store_bind(ixs_facts *facts,
                                    ixs_session_binding *binding,
                                    ixs_ctx **ctx) {
  if (!facts || !facts->impl || !facts->ctx || !binding || !ctx ||
      facts->epoch == 0 || facts->impl->ctx != facts->ctx ||
      facts->impl->epoch != facts->epoch)
    return false;
  *ctx = ixs_session_bind_impl(binding, facts->impl);
  bounds_store_bind(&facts->bounds, *ctx, &(*ctx)->scratch);
  return true;
}

static inline bool facts_store_ready(const ixs_facts *facts) {
  return facts && facts->usable && !facts->bounds.oom;
}

static inline void facts_store_unbind(ixs_facts *facts,
                                      ixs_session_binding *binding) {
  bounds_store_retarget_scratch(&facts->bounds, NULL);
  ixs_session_unbind(binding);
}

IXS_STATIC ixs_bounds_build_status facts_store_ingest_predicate_branch(
    ixs_ctx *ctx, ixs_bounds *bounds, ixs_node *predicate);
IXS_STATIC void facts_store_destroy_session(ixs_session_impl *impl);
/* The exact-domain cache stores only conclusive semantic proofs. */
IXS_STATIC bool facts_equivalence_cache_lookup(ixs_ctx *ctx, ixs_bounds *bounds,
                                               ixs_node *lhs, ixs_node *rhs,
                                               ixs_check_result *result);
IXS_STATIC void facts_equivalence_cache_store(ixs_ctx *ctx, ixs_bounds *bounds,
                                              ixs_node *lhs, ixs_node *rhs,
                                              ixs_check_result result);

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

typedef struct {
  size_t lookups;
  size_t hits;
  size_t stores;
  size_t replacements;
  size_t retained_bytes;
  size_t retained_limit;
} ixs_facts_equivalence_cache_stats_result;

IXS_STATIC void
ixs_facts_closure_cache_stats(const ixs_ctx *ctx,
                              ixs_facts_closure_cache_stats_result *stats);
IXS_STATIC void ixs_facts_equivalence_cache_stats(
    const ixs_ctx *ctx, ixs_facts_equivalence_cache_stats_result *stats);
#endif

#endif /* IXS_FACTS_STORE_H */
