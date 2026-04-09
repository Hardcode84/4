/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "node.h"

#define WALK_STACK_INIT_CAP 64u

typedef struct {
  ixs_node *node;
  uint32_t next_child;
} walk_frame;

static void *walk_stack_reserve(ixs_ctx *ctx, void *ptr, size_t *cap,
                                size_t need, size_t elem_size) {
  if (need <= *cap)
    return ptr;
  while (*cap < need) {
    size_t old_cap = *cap;
    size_t new_cap = old_cap * 2;
    if (new_cap <= old_cap || new_cap > (size_t)-1 / elem_size)
      return NULL;
    ptr = ixs_arena_grow(&ctx->scratch, ptr, old_cap * elem_size,
                         new_cap * elem_size, sizeof(void *));
    if (!ptr)
      return NULL;
    *cap = new_cap;
  }
  return ptr;
}

static ixs_node *walk_pre(ixs_ctx *ctx, ixs_node *root, ixs_visit_fn fn,
                          void *ud) {
  ixs_arena_mark m = ixs_arena_save(&ctx->scratch);
  size_t cap = WALK_STACK_INIT_CAP;
  size_t nstack = 0;
  ixs_node **stack =
      ixs_arena_alloc(&ctx->scratch, cap * sizeof(*stack), sizeof(void *));
  if (!stack) {
    ixs_arena_restore(&ctx->scratch, m);
    return NULL;
  }

  stack[nstack++] = root;
  while (nstack > 0) {
    ixs_node *node = stack[--nstack];
    ixs_walk_action act = fn(node, ud);
    if (act == IXS_WALK_STOP) {
      ixs_arena_restore(&ctx->scratch, m);
      return node;
    }
    if (act == IXS_WALK_SKIP)
      continue;

    uint32_t n = ixs_node_nchildren(node);
    stack = walk_stack_reserve(ctx, stack, &cap, nstack + (size_t)n,
                               sizeof(*stack));
    if (!stack) {
      ixs_arena_restore(&ctx->scratch, m);
      return NULL;
    }
    for (uint32_t i = n; i > 0; i--)
      stack[nstack++] = ixs_node_child(node, i - 1);
  }

  ixs_arena_restore(&ctx->scratch, m);
  return root;
}

static ixs_node *walk_post(ixs_ctx *ctx, ixs_node *root, ixs_visit_fn fn,
                           void *ud) {
  ixs_arena_mark m = ixs_arena_save(&ctx->scratch);
  size_t cap = WALK_STACK_INIT_CAP;
  size_t nstack = 0;
  walk_frame *stack =
      ixs_arena_alloc(&ctx->scratch, cap * sizeof(*stack), sizeof(void *));
  if (!stack) {
    ixs_arena_restore(&ctx->scratch, m);
    return NULL;
  }

  stack[nstack].node = root;
  stack[nstack].next_child = 0;
  nstack++;
  while (nstack > 0) {
    walk_frame *frame = &stack[nstack - 1];
    uint32_t n = ixs_node_nchildren(frame->node);
    if (frame->next_child < n) {
      ixs_node *child = ixs_node_child(frame->node, frame->next_child);
      frame->next_child++;
      stack = walk_stack_reserve(ctx, stack, &cap, nstack + 1, sizeof(*stack));
      if (!stack) {
        ixs_arena_restore(&ctx->scratch, m);
        return NULL;
      }
      stack[nstack].node = child;
      stack[nstack].next_child = 0;
      nstack++;
      continue;
    }

    ixs_node *node = frame->node;
    ixs_walk_action act = fn(node, ud);
    nstack--;
    if (act == IXS_WALK_STOP) {
      ixs_arena_restore(&ctx->scratch, m);
      return node;
    }
  }

  ixs_arena_restore(&ctx->scratch, m);
  return root;
}

ixs_node *ixs_walk_pre(ixs_ctx *ctx, ixs_node *root, ixs_visit_fn fn,
                       void *userdata) {
  if (!root)
    return NULL;
  return walk_pre(ctx, root, fn, userdata);
}

ixs_node *ixs_walk_post(ixs_ctx *ctx, ixs_node *root, ixs_visit_fn fn,
                        void *userdata) {
  if (!root)
    return NULL;
  return walk_post(ctx, root, fn, userdata);
}
