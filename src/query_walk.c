/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "query_walk.h"

#include <assert.h>
#include <stdint.h>
#include <string.h>

IXS_STATIC ixs_query_walk_step ixs_query_walk_push(ixs_query_walk *walk,
                                                   ixs_node *expr) {
  size_t capacity;
  void *grown;
  char *frame;
  if (walk->depth == walk->capacity) {
    capacity = walk->capacity ? walk->capacity * 2u : 16u;
    if (capacity < walk->capacity || capacity > SIZE_MAX / walk->frame_size)
      goto oom;
    grown = ixs_arena_grow(walk->arena, walk->frames,
                           walk->capacity * walk->frame_size,
                           capacity * walk->frame_size, sizeof(void *));
    if (!grown)
      goto oom;
    walk->frames = grown;
    walk->capacity = capacity;
  }
  frame = (char *)walk->frames + walk->depth++ * walk->frame_size;
  memset(frame, 0, walk->frame_size);
  memcpy(frame, &expr, sizeof(expr));
  return IXS_QUERY_WALK_ADVANCED;
oom:
  *walk->oom = true;
  return IXS_QUERY_WALK_OOM;
}

IXS_STATIC bool ixs_query_walk_run(ixs_query_walk *walk, ixs_node *root,
                                   void *state, ixs_query_walk_advance advance,
                                   ixs_query_walk_abort abort) {
  ixs_arena_mark mark = ixs_arena_save(walk->arena);
  bool success = ixs_query_walk_push(walk, root) != IXS_QUERY_WALK_OOM;
  while (success && walk->depth != 0) {
    ixs_query_walk_step step = advance(state, IXS_QUERY_WALK_TOP(walk));
    assert(step != IXS_QUERY_WALK_NEXT);
    success = step != IXS_QUERY_WALK_OOM;
  }
  while (walk->depth != 0) {
    abort(state, IXS_QUERY_WALK_TOP(walk));
    IXS_QUERY_WALK_POP(walk);
  }
  ixs_arena_restore(walk->arena, mark);
  return success;
}
