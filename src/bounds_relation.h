/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_RELATION_H
#define IXS_BOUNDS_RELATION_H

#include "bounds.h"

typedef struct {
  ixs_node *node;
  size_t endpoint_index;
  /* Exact node - component-root offset. Signed magnitude preserves the
   * transient +2^63 reverse of an INT64_MIN edge. */
  ixs_relation_offset offset;
} bounds_relation_component_entry;

/* The caller proves the root before begin and each node returned by pull
 * before resolve. A rejected node skips only its pending edge. Component
 * storage is borrowed until destroy, and relations remain immutable while
 * its edge cursor is live. The aggregate loan is restricted to relation-owned
 * state and the caller's scratch arena. */
typedef struct {
  ixs_relation_algebra *relations;
  ixs_arena *scratch;
  ixs_arena_mark mark;
  bounds_relation_component_entry *entries;
  size_t *seen;
  const ixs_relation_edge *next_edge;
  ixs_relation_offset pending_step;
  size_t pending_endpoint;
  size_t count;
  size_t capacity;
  size_t seen_capacity;
  size_t head;
  bool pending;
} bounds_relation_component;

typedef enum {
  BOUNDS_RELATION_CURSOR_READY,
  BOUNDS_RELATION_CURSOR_ADMISSION,
  BOUNDS_RELATION_CURSOR_COMPLETE,
  BOUNDS_RELATION_CURSOR_INVALID,
  BOUNDS_RELATION_CURSOR_OOM
} bounds_relation_cursor_step;

typedef struct {
  int64_t p;
  int64_t q;
  ixs_relation_offset peer_offset;
  bool present;
} bounds_relation_projection_bound;

IXS_STATIC void bounds_relation_init(ixs_bounds *bounds, ixs_arena *arena,
                                     bool transient);
IXS_STATIC ixs_relation_status
bounds_relation_clone_fork(ixs_bounds *dst, const ixs_bounds *src);
IXS_STATIC void bounds_relation_destroy(ixs_bounds *bounds);
IXS_STATIC void bounds_relation_projection_reset(ixs_bounds *bounds,
                                                 bool transient);
IXS_STATIC void bounds_relation_projection_invalidate(ixs_bounds *bounds);
IXS_STATIC void bounds_relation_projection_commit(ixs_bounds *destination,
                                                  ixs_bounds *candidate);

IXS_STATIC bounds_relation_cursor_step bounds_relation_component_begin(
    ixs_relation_algebra *relations, ixs_arena *scratch, size_t root_endpoint,
    bounds_relation_component *component);
IXS_STATIC bounds_relation_cursor_step bounds_relation_component_pull(
    bounds_relation_component *component, ixs_node **candidate);
IXS_STATIC bounds_relation_cursor_step bounds_relation_component_resolve(
    bounds_relation_component *component, bool admitted);
IXS_STATIC void
bounds_relation_component_destroy(bounds_relation_component *component);
IXS_STATIC bool
bounds_relation_component_find(const bounds_relation_component *component,
                               size_t endpoint_index, size_t *entry_index);
IXS_STATIC bool bounds_relation_component_publish_defined(
    ixs_bounds *bounds, const bounds_relation_component *component);

/* Callers decide whether a central query is active. Component completion
 * reserves every row before publishing the first column. */
IXS_STATIC bool bounds_relation_projection_lookup_integer(
    const ixs_bounds *bounds, size_t endpoint_index, ixs_check_result *result);
IXS_STATIC void bounds_relation_projection_complete_integer_component(
    ixs_bounds *bounds, const bounds_relation_component *component,
    ixs_check_result result);
IXS_STATIC bool bounds_relation_projection_lookup_range(
    const ixs_bounds *bounds, size_t endpoint_index, ixs_interval *result);
IXS_STATIC void bounds_relation_projection_stage_range(ixs_bounds *bounds,
                                                       size_t endpoint_index,
                                                       ixs_interval range);
IXS_STATIC ixs_interval bounds_relation_projection_complete_range(
    ixs_bounds *bounds, size_t endpoint_index,
    ixs_relation_offset endpoint_offset,
    const bounds_relation_projection_bound *lower,
    const bounds_relation_projection_bound *upper, bool project);
IXS_STATIC bool bounds_relation_projection_lookup_defined(
    const ixs_bounds *bounds, size_t endpoint_index, bool without_equality,
    ixs_check_result *result);
IXS_STATIC bool bounds_relation_projection_complete_defined(
    ixs_bounds *bounds, size_t endpoint_index, bool without_equality,
    ixs_check_result result);

IXS_STATIC ixs_relation_query_status
bounds_relation_cached_offset(ixs_bounds *bounds, size_t lhs_endpoint,
                              size_t rhs_endpoint, ixs_relation_offset *offset);
IXS_STATIC bool bounds_relation_projection_bound_cmp(
    int64_t lhs_p, int64_t lhs_q, ixs_relation_offset lhs_offset, int64_t rhs_p,
    int64_t rhs_q, ixs_relation_offset rhs_offset, int *result);
IXS_STATIC ixs_interval bounds_relation_projection_apply(
    ixs_interval intrinsic, ixs_relation_offset endpoint_offset,
    const bounds_relation_projection_bound *lower,
    const bounds_relation_projection_bound *upper);

#if defined(IXS_TEST_INTERNAL) && !defined(IXS_AMALGAMATED)
IXS_STATIC void
bounds_relation_projection_force_generation_wrap(ixs_bounds *bounds);
IXS_STATIC size_t bounds_relation_projection_entry_size(void);
IXS_STATIC size_t bounds_relation_projection_generation_count(
    const ixs_bounds *bounds, uint32_t generation);
#endif

#endif /* IXS_BOUNDS_RELATION_H */
