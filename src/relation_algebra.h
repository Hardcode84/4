/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_RELATION_ALGEBRA_H
#define IXS_RELATION_ALGEBRA_H

#include "arena.h"

#include <ixsimpl.h>

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef struct ixs_relation_edge ixs_relation_edge;
typedef struct ixs_relation_endpoint ixs_relation_endpoint;
typedef struct ixs_relation_total_node ixs_relation_total_node;

/* Signed magnitude keeps the reverse of an INT64_MIN edge representable and
 * permits exact asserted chains whose accumulated offset exceeds int64_t. */
typedef struct {
  uint64_t lo;
  uint64_t hi;
  bool negative;
} ixs_relation_offset;

typedef enum {
  IXS_RELATION_STATUS_OK,
  IXS_RELATION_STATUS_UNCHANGED,
  IXS_RELATION_STATUS_ADDED,
  IXS_RELATION_STATUS_CONFLICT,
  IXS_RELATION_STATUS_UNREPRESENTABLE,
  IXS_RELATION_STATUS_OOM
} ixs_relation_status;

typedef enum {
  IXS_RELATION_QUERY_NONE,
  IXS_RELATION_QUERY_FOUND,
  IXS_RELATION_QUERY_UNREPRESENTABLE,
  IXS_RELATION_QUERY_INVALID
} ixs_relation_query_status;

/* Retained exact-relation state. Every pointer refers to storage owned by
 * arena. Endpoints are shared by the asserted graph and the lazy total
 * closure; total nodes need no second expression index. */
typedef struct {
  ixs_arena *arena;
  ixs_relation_endpoint *endpoints;
  size_t *endpoint_index;
  ixs_relation_edge **edge_index;
  ixs_relation_total_node *total_nodes;
  size_t endpoint_count;
  size_t endpoint_capacity;
  size_t endpoint_index_capacity;
  size_t edge_count;
  size_t edge_index_capacity;
  size_t total_count;
  size_t total_capacity;
} ixs_relation_algebra;

IXS_STATIC void ixs_relation_algebra_init(ixs_relation_algebra *algebra,
                                          ixs_arena *arena);

/* Clone cost is O(V + E). Destination edges and indexes never borrow source
 * arena storage. dst must not alias src. */
IXS_STATIC ixs_relation_status
ixs_relation_algebra_clone(ixs_relation_algebra *dst,
                           const ixs_relation_algebra *src, ixs_arena *arena);

/* Record lhs - rhs == offset in the asserted graph. Lookup is expected O(1);
 * insertion is amortized O(1), and weighted union/find is amortized
 * inverse-Ackermann in the number of endpoints. */
IXS_STATIC ixs_relation_status
ixs_relation_algebra_assert(ixs_relation_algebra *algebra, ixs_node *lhs,
                            ixs_node *rhs, int64_t offset);

/* Promote an already asserted equation into the independently safe total
 * closure after its reverse inequality arrives. */
IXS_STATIC ixs_relation_status
ixs_relation_algebra_certify_total(ixs_relation_algebra *algebra, ixs_node *lhs,
                                   ixs_node *rhs, int64_t offset);

IXS_STATIC bool
ixs_relation_algebra_find_endpoint(const ixs_relation_algebra *algebra,
                                   const ixs_node *expr,
                                   size_t *endpoint_index);
IXS_STATIC size_t
ixs_relation_algebra_endpoint_count(const ixs_relation_algebra *algebra);
IXS_STATIC ixs_node *
ixs_relation_algebra_endpoint_expr(const ixs_relation_algebra *algebra,
                                   size_t endpoint_index);

/* Adjacency accessors let the bounds owner apply its own definedness policy
 * without callbacks in this storage component. */
IXS_STATIC const ixs_relation_edge *
ixs_relation_algebra_first_edge(const ixs_relation_algebra *algebra,
                                size_t endpoint_index);
IXS_STATIC ixs_relation_query_status ixs_relation_algebra_edge_neighbor(
    const ixs_relation_algebra *algebra, size_t endpoint_index,
    const ixs_relation_edge *edge, size_t *neighbor_endpoint,
    ixs_relation_offset *step, const ixs_relation_edge **next);

/* Hash-slot iteration preserves the existing substitution replay boundary. */
IXS_STATIC size_t
ixs_relation_algebra_edge_slot_count(const ixs_relation_algebra *algebra);
IXS_STATIC const ixs_relation_edge *
ixs_relation_algebra_edge_at_slot(const ixs_relation_algebra *algebra,
                                  size_t slot);
IXS_STATIC size_t
ixs_relation_algebra_edge_count(const ixs_relation_algebra *algebra);
IXS_STATIC size_t
ixs_relation_algebra_total_count(const ixs_relation_algebra *algebra);
IXS_STATIC ixs_node *ixs_relation_edge_lhs(const ixs_relation_edge *edge);
IXS_STATIC ixs_node *ixs_relation_edge_rhs(const ixs_relation_edge *edge);
IXS_STATIC int64_t ixs_relation_edge_offset(const ixs_relation_edge *edge);

/* Query two trusted symbols in the certified-total closure. Checked int64
 * arithmetic at every parent edge preserves its narrower admission policy. */
IXS_STATIC bool ixs_relation_algebra_total_symbol_difference(
    ixs_relation_algebra *algebra, const ixs_node *lhs, const ixs_node *rhs,
    int64_t *difference);

IXS_STATIC ixs_relation_offset ixs_relation_offset_from_int64(int64_t value);
IXS_STATIC ixs_relation_offset
ixs_relation_offset_negate(ixs_relation_offset value);
IXS_STATIC bool ixs_relation_offset_add(ixs_relation_offset lhs,
                                        ixs_relation_offset rhs,
                                        ixs_relation_offset *result);
IXS_STATIC bool ixs_relation_offset_equal(ixs_relation_offset lhs,
                                          ixs_relation_offset rhs);
IXS_STATIC bool ixs_relation_offset_to_int64(ixs_relation_offset value,
                                             int64_t *result);

#endif /* IXS_RELATION_ALGEBRA_H */
