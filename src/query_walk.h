/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_QUERY_WALK_H
#define IXS_QUERY_WALK_H

#include "arena.h"
#include "node.h"

typedef struct {
  ixs_arena *arena;
  bool *oom;
  void *frames;
  size_t frame_size;
  size_t depth;
  size_t capacity;
} ixs_query_walk;

typedef enum {
  IXS_QUERY_WALK_ADVANCED,
  IXS_QUERY_WALK_NEXT,
  IXS_QUERY_WALK_OOM
} ixs_query_walk_step;

typedef ixs_query_walk_step (*ixs_query_walk_advance)(void *state, void *frame);
typedef void (*ixs_query_walk_abort)(void *state, void *frame);

#define IXS_QUERY_WALK_FRAME_OK(frame_type, expr_member)                       \
  (offsetof(frame_type, expr_member) == 0 &&                                   \
   sizeof(((frame_type *)0)->expr_member) == sizeof(ixs_node *))
#define IXS_QUERY_WALK_INIT(walk, scratch, oom_out, frame_type, expr_member)   \
  do {                                                                         \
    (void)sizeof(                                                              \
        char[IXS_QUERY_WALK_FRAME_OK(frame_type, expr_member) ? 1 : -1]);      \
    *(walk) = (ixs_query_walk){.arena = (scratch),                             \
                               .oom = (oom_out),                               \
                               .frame_size = sizeof(frame_type)};              \
  } while (0)

IXS_STATIC ixs_query_walk_step ixs_query_walk_push(ixs_query_walk *walk,
                                                   ixs_node *expr);
#define IXS_QUERY_WALK_TOP(walk)                                               \
  ((void *)((char *)(walk)->frames + ((walk)->depth - 1u) * (walk)->frame_size))
#define IXS_QUERY_WALK_POP(walk) ((walk)->depth--)

/* arena, oom, state, and root are borrowed for one run.  Pointer alignment,
 * the 16-frame start, and doubling preserve the original allocation sequence.
 * Advance makes structural progress and never returns NEXT.  Abort closes the
 * current consumer scope; the driver then pops it.  Neither callback may
 * retain or inspect a frame after push or pop because growth can relocate it.
 */
IXS_STATIC bool ixs_query_walk_run(ixs_query_walk *walk, ixs_node *root,
                                   void *state, ixs_query_walk_advance advance,
                                   ixs_query_walk_abort abort);

#endif /* IXS_QUERY_WALK_H */
