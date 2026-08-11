/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_PROOF_H
#define IXS_BOUNDS_PROOF_H

#include "bounds_query.h"
#include "query_walk.h"

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef enum {
  BOUNDS_PROOF_FRAME_NONE,
  BOUNDS_PROOF_FRAME_EXACT,
  BOUNDS_PROOF_FRAME_RESIDUE
} bounds_proof_frame_kind;

typedef enum {
  BOUNDS_PROOF_INTEGER,
  BOUNDS_PROOF_DIVISIBLE,
  BOUNDS_PROOF_RESIDUE
} bounds_proof_kind;

typedef enum {
  BOUNDS_EXACT_PROOF_INITIAL,
  BOUNDS_PROOF_INTEGER_MUL_SCAN,
  BOUNDS_PROOF_INTEGER_MUL_RATIONAL_SCAN,
  BOUNDS_PROOF_INTEGER_MUL_RATIONAL_RESIDUE,
  BOUNDS_PROOF_INTEGER_MUL_RATIONAL_INTEGER,
  BOUNDS_PROOF_INTEGER_ADD_SCAN,
  BOUNDS_PROOF_INTEGER_ADD_INTEGER,
  BOUNDS_PROOF_INTEGER_ADD_DIVISIBLE,
  BOUNDS_PROOF_INTEGER_ADD_RESIDUE,
  BOUNDS_PROOF_INTEGER_ASSOC_SCAN,
  BOUNDS_PROOF_INTEGER_PW_SCAN,
  BOUNDS_PROOF_INTEGER_PW_CHILD,
  BOUNDS_PROOF_INTEGER_MOD_LHS,
  BOUNDS_PROOF_INTEGER_MOD_RHS,
  BOUNDS_PROOF_DIVISIBLE_INTEGER,
  BOUNDS_PROOF_DIVISIBLE_RESIDUE
} bounds_exact_proof_stage;

typedef enum {
  BOUNDS_RESIDUE_INITIAL,
  BOUNDS_RESIDUE_INTEGER_CHILD,
  BOUNDS_RESIDUE_SCALED_ADD_START,
  BOUNDS_RESIDUE_ADD_INTEGER_SCAN,
  BOUNDS_RESIDUE_ADD_INTEGER_CHILD,
  BOUNDS_RESIDUE_ADD_SCALED_CHILD,
  BOUNDS_RESIDUE_ADD_SCAN,
  BOUNDS_RESIDUE_ADD_CHILD,
  BOUNDS_RESIDUE_MUL_INTEGER_SCAN,
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
  ixs_node *expr;
  ixs_bounds *bounds;
  uint64_t modulus;
  uint64_t residue;
  uint8_t kind;
  bool success;
  bool active;
  bool complete;
} bounds_proof_memo_entry;

typedef struct {
  bounds_proof_memo_entry *entries;
  size_t count;
  size_t capacity;
} bounds_proof_memo;

typedef struct {
  ixs_node *expr;
  uint64_t modulus;
  uint64_t denominator;
  uint32_t index;
  bounds_proof_kind kind;
  bounds_exact_proof_stage stage;
  bool denominator_cancelled;
  bool reachable;
  bool terminal_branch;
  uint8_t parent_kind;
} bounds_exact_proof_frame;

struct bounds_residue_group;

typedef struct {
  ixs_node *expr;
  ixs_bounds *bounds;
  uint64_t modulus;
  bounds_query_scope scope;
  struct bounds_residue_group *groups;
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
  bool memoized;
  bool synthetic_scaled;
  uint8_t parent_kind;
} bounds_residue_frame;

typedef struct bounds_proof_query {
  ixs_bounds *root;
  ixs_bounds *active_bounds;
  bounds_exact_proof_frame *exact_frames;
  size_t exact_count;
  size_t exact_capacity;
  bounds_residue_frame *residue_frames;
  size_t residue_count;
  size_t residue_capacity;
  size_t depth;
  bounds_proof_memo memo;
  uint64_t child_residue;
  bounds_proof_frame_kind top_kind;
  bool child_success;
  bool proof_independent;
  bounds_exact_proof_frame inline_exact[16];
  bounds_proof_memo_entry inline_memo[32];
} bounds_proof_query;

IXS_STATIC void bounds_proof_query_init(bounds_proof_query *query,
                                        ixs_bounds *root,
                                        bool proof_independent);
IXS_STATIC ixs_query_walk_step bounds_proof_drive(bounds_proof_query *query,
                                                  ixs_query_walk_step step);

IXS_STATIC ixs_query_walk_step bounds_proof_push_exact(
    bounds_proof_query *query, ixs_bounds *bounds, ixs_node *expr,
    bounds_proof_kind kind, uint64_t modulus);
IXS_STATIC ixs_query_walk_step
bounds_proof_push_residue(bounds_proof_query *query, ixs_bounds *bounds,
                          ixs_node *expr, uint64_t modulus);
IXS_STATIC ixs_query_walk_step
bounds_proof_push_residue_task(bounds_proof_query *query, ixs_bounds *bounds,
                               ixs_node *expr, uint64_t modulus);
IXS_STATIC bool bounds_proof_integer_cached(bounds_proof_query *query,
                                            ixs_bounds *bounds, ixs_node *expr);
IXS_STATIC ixs_query_walk_step
bounds_proof_push_scaled_add(bounds_proof_query *query, ixs_bounds *bounds,
                             ixs_node *expr, uint64_t scale, uint64_t modulus);
IXS_STATIC ixs_query_walk_step
bounds_proof_complete_exact(bounds_proof_query *query, bool success);
IXS_STATIC ixs_query_walk_step bounds_proof_complete_residue(
    bounds_proof_query *query, bool success, uint64_t residue);
IXS_STATIC ixs_query_walk_step bounds_exact_proof_advance(
    bounds_proof_query *query, bounds_exact_proof_frame *frame);
IXS_STATIC ixs_query_walk_step
bounds_residue_advance(bounds_proof_query *query, bounds_residue_frame *frame);
IXS_STATIC void bounds_residue_abort(bounds_proof_query *query,
                                     bounds_residue_frame *frame);

#endif /* IXS_BOUNDS_PROOF_H */
