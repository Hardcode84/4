/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_QUERY_WALK_H
#define IXS_QUERY_WALK_H

#include "arena.h"
#include "node.h"

/* Scratch-local pointer set shared by iterative proof components. */
typedef struct {
  ixs_node **slots;
  size_t capacity;
  size_t count;
} query_node_set;

IXS_STATIC bool query_node_set_insert(ixs_arena *arena, query_node_set *set,
                                      ixs_node *node, bool *inserted);
IXS_STATIC bool query_node_set_reserve(ixs_arena *arena, query_node_set *set,
                                       size_t count);
IXS_STATIC bool query_node_set_contains(const query_node_set *set,
                                        const ixs_node *node);
IXS_STATIC bool query_node_stack_push(ixs_arena *arena, ixs_node ***stack,
                                      size_t *count, size_t *capacity,
                                      ixs_node *node);

typedef struct {
  ixs_arena *arena;
  bool *oom;
  void *frames;
  size_t frame_size;
  size_t depth;
  size_t capacity;
  size_t initial_capacity;
} ixs_query_walk;

typedef struct {
  ixs_node *node;
  ixs_check_result result;
  bool active;
  bool complete;
} ixs_query_check_memo_entry;

typedef enum {
  IXS_QUERY_WALK_ADVANCED,
  IXS_QUERY_WALK_NEXT,
  IXS_QUERY_WALK_STOP,
  IXS_QUERY_WALK_OOM
} ixs_query_walk_step;

typedef ixs_query_walk_step (*ixs_query_walk_advance)(void *state, void *frame);
typedef void (*ixs_query_walk_abort)(void *state, void *frame);

#define IXS_QUERY_WALK_FRAME_OK(frame_type, expr_member)                       \
  (offsetof(frame_type, expr_member) == 0 &&                                   \
   sizeof(((frame_type *)0)->expr_member) == sizeof(ixs_node *))
#define IXS_QUERY_WALK_INIT_CAP(walk, scratch, oom_out, frame_type,            \
                                expr_member, start_capacity)                   \
  do {                                                                         \
    (void)sizeof(                                                              \
        char[IXS_QUERY_WALK_FRAME_OK(frame_type, expr_member) ? 1 : -1]);      \
    *(walk) = (ixs_query_walk){.arena = (scratch),                             \
                               .oom = (oom_out),                               \
                               .frame_size = sizeof(frame_type),               \
                               .initial_capacity = (start_capacity)};          \
  } while (0)
#define IXS_QUERY_WALK_INIT(walk, scratch, oom_out, frame_type, expr_member)   \
  IXS_QUERY_WALK_INIT_CAP(walk, scratch, oom_out, frame_type, expr_member, 16u)
#define IXS_QUERY_WALK_INIT_INLINE(walk, scratch, oom_out, frame_type,         \
                                   expr_member, inline_frames)                 \
  do {                                                                         \
    IXS_QUERY_WALK_INIT_CAP(walk, scratch, oom_out, frame_type, expr_member,   \
                            sizeof(inline_frames) /                            \
                                sizeof((inline_frames)[0]));                   \
    (walk)->frames = (inline_frames);                                          \
    (walk)->capacity = sizeof(inline_frames) / sizeof((inline_frames)[0]);     \
  } while (0)

IXS_STATIC ixs_query_walk_step ixs_query_walk_push(ixs_query_walk *walk,
                                                   ixs_node *expr);
#define IXS_QUERY_WALK_TOP(walk)                                               \
  ((void *)((char *)(walk)->frames + ((walk)->depth - 1u) * (walk)->frame_size))
#define IXS_QUERY_WALK_POP(walk) ((walk)->depth--)

typedef struct {
  ixs_arena *arena;
  void *entries;
  size_t entry_size;
  size_t count;
  size_t capacity;
} ixs_query_node_memo;

#define IXS_QUERY_NODE_MEMO_INIT(memo, storage, entry_type, node_member)       \
  do {                                                                         \
    (void)sizeof(                                                              \
        char[IXS_QUERY_WALK_FRAME_OK(entry_type, node_member) ? 1 : -1]);      \
    *(memo) = (ixs_query_node_memo){.arena = (storage),                        \
                                    .entry_size = sizeof(entry_type)};         \
  } while (0)

/* Entries are keyed only by their first-member node pointer.  The caller owns
 * the arena mark and all value/status policy.  Storage starts at 32 entries,
 * doubles above half load, and is discarded with that mark.  Any creating
 * lookup may grow the table and invalidate every earlier entry pointer.
 * Lookup and insertion are expected amortized O(1). */
IXS_STATIC void *ixs_query_node_memo_get(ixs_query_node_memo *memo,
                                         ixs_node *node, bool create);

IXS_STATIC bool ixs_query_node_vector_push(ixs_arena *arena, ixs_node ***nodes,
                                           size_t *count, size_t *capacity,
                                           ixs_node *node,
                                           size_t initial_capacity);

/* CAP is positive and INLINE receives an actual nonempty array.  Push doubles
 * dynamic pointer-aligned storage, zeroes the complete frame, then publishes
 * expr; growth may relocate every frame.
 * arena, oom, and state are borrowed by drive; root is additionally borrowed
 * by run.  Drive starts from a prepopulated walk and owns no arena mark.  Run
 * owns and restores one around root push and drive.  Advance makes structural
 * progress and never returns NEXT.  STOP is consumer-directed non-OOM
 * termination; its semantic/status meaning remains consumer-owned.  Push
 * latches *oom before returning OOM; an advance OOM is returned unchanged for
 * consumer mapping.  Optional abort closes active scopes in LIFO order before
 * the driver pops each frame.  Neither callback may retain or inspect a frame
 * after push or pop.
 */
IXS_STATIC ixs_query_walk_step ixs_query_walk_drive(
    ixs_query_walk *walk, void *state, ixs_query_walk_advance advance,
    ixs_query_walk_abort abort);
IXS_STATIC bool ixs_query_walk_run(ixs_query_walk *walk, ixs_node *root,
                                   void *state, ixs_query_walk_advance advance,
                                   ixs_query_walk_abort abort);

#endif /* IXS_QUERY_WALK_H */
