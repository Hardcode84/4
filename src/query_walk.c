/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "query_walk.h"

#include <assert.h>
#include <stdint.h>
#include <string.h>

IXS_STATIC bool ixs_query_node_vector_push(ixs_arena *arena, ixs_node ***nodes,
                                           size_t *count, size_t *capacity,
                                           ixs_node *node,
                                           size_t initial_capacity) {
  if (*count >= *capacity) {
    size_t new_capacity = *capacity ? *capacity * 2u : initial_capacity;
    ixs_node **grown;
    assert(initial_capacity != 0u);
    if (new_capacity <= *capacity || new_capacity > SIZE_MAX / sizeof(**nodes))
      return false;
    grown = ixs_arena_grow(arena, *nodes, *capacity * sizeof(**nodes),
                           new_capacity * sizeof(**nodes), sizeof(void *));
    if (!grown)
      return false;
    *nodes = grown;
    *capacity = new_capacity;
  }
  (*nodes)[(*count)++] = node;
  return true;
}

IXS_STATIC ixs_query_walk_step ixs_query_walk_push(ixs_query_walk *walk,
                                                   ixs_node *expr) {
  size_t capacity;
  void *grown;
  char *frame;
  assert(walk->initial_capacity != 0u);
  if (walk->depth == walk->capacity) {
    capacity = walk->capacity ? walk->capacity * 2u : walk->initial_capacity;
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

IXS_STATIC ixs_query_walk_step ixs_query_walk_drive(
    ixs_query_walk *walk, void *state, ixs_query_walk_advance advance,
    ixs_query_walk_abort abort) {
  ixs_query_walk_step step = IXS_QUERY_WALK_ADVANCED;
  while (walk->depth != 0) {
    step = advance(state, IXS_QUERY_WALK_TOP(walk));
    assert(step != IXS_QUERY_WALK_NEXT);
    if (step != IXS_QUERY_WALK_ADVANCED)
      break;
  }
  while (walk->depth != 0) {
    if (abort)
      abort(state, IXS_QUERY_WALK_TOP(walk));
    IXS_QUERY_WALK_POP(walk);
  }
  return step;
}

IXS_STATIC bool ixs_query_walk_run(ixs_query_walk *walk, ixs_node *root,
                                   void *state, ixs_query_walk_advance advance,
                                   ixs_query_walk_abort abort) {
  ixs_arena_mark mark = ixs_arena_save(walk->arena);
  ixs_query_walk_step step = ixs_query_walk_push(walk, root);
  if (step == IXS_QUERY_WALK_ADVANCED)
    step = ixs_query_walk_drive(walk, state, advance, abort);
  ixs_arena_restore(walk->arena, mark);
  return step == IXS_QUERY_WALK_ADVANCED;
}

static ixs_node *query_node_at(void *entries, size_t entry_size, size_t index) {
  ixs_node *node;
  memcpy(&node, (char *)entries + index * entry_size, sizeof(node));
  return node;
}

static bool query_node_memo_grow(ixs_query_node_memo *memo) {
  size_t capacity = memo->capacity ? memo->capacity * 2u : 32u;
  void *grown;
  size_t i;
  if (capacity <= memo->capacity || capacity > SIZE_MAX / memo->entry_size)
    return false;
  grown =
      ixs_arena_alloc(memo->arena, capacity * memo->entry_size, sizeof(void *));
  if (!grown)
    return false;
  memset(grown, 0, capacity * memo->entry_size);
  for (i = 0; i < memo->capacity; i++) {
    ixs_node *node = query_node_at(memo->entries, memo->entry_size, i);
    size_t slot;
    if (!node)
      continue;
    slot = node->hash & (capacity - 1u);
    while (query_node_at(grown, memo->entry_size, slot))
      slot = (slot + 1u) & (capacity - 1u);
    memcpy((char *)grown + slot * memo->entry_size,
           (char *)memo->entries + i * memo->entry_size, memo->entry_size);
  }
  memo->entries = grown;
  memo->capacity = capacity;
  return true;
}

IXS_STATIC void *ixs_query_node_memo_get(ixs_query_node_memo *memo,
                                         ixs_node *node, bool create) {
  size_t slot;
  char *entry;
  if (create && (!memo->capacity || memo->count + 1u > memo->capacity / 2u) &&
      !query_node_memo_grow(memo))
    return NULL;
  if (!memo->capacity)
    return NULL;
  slot = node->hash & (memo->capacity - 1u);
  while (query_node_at(memo->entries, memo->entry_size, slot) &&
         query_node_at(memo->entries, memo->entry_size, slot) != node)
    slot = (slot + 1u) & (memo->capacity - 1u);
  entry = (char *)memo->entries + slot * memo->entry_size;
  if (!query_node_at(memo->entries, memo->entry_size, slot)) {
    if (!create)
      return NULL;
    memcpy(entry, &node, sizeof(node));
    memo->count++;
  }
  return entry;
}
