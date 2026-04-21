/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "arena.h"
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

#define ARENA_MAX_ALIGN 16

static size_t align_up(size_t val, size_t align) {
  return (val + align - 1) & ~(align - 1);
}

static bool chunk_is_inline(const ixs_arena *a, const ixs_arena_chunk *c) {
  return c && c == a->inline_chunk;
}

/*
 * Single allocation per chunk: the ixs_arena_chunk header lives at the
 * start of the malloc'd block, followed by the data region aligned to
 * ARENA_MAX_ALIGN.  One malloc, one free.  Returns NULL on overflow/OOM.
 */
static ixs_arena_chunk *chunk_new(size_t data_capacity) {
  size_t header_sz = align_up(sizeof(ixs_arena_chunk), ARENA_MAX_ALIGN);
  size_t total = header_sz + data_capacity;
  if (total < data_capacity)
    return NULL; /* overflow */
  ixs_arena_chunk *c = malloc(total);
  if (!c)
    return NULL;
  c->base = (char *)c + header_sz;
  c->used = 0;
  c->capacity = data_capacity;
  c->next = NULL;
  return c;
}

IXS_STATIC void ixs_arena_init(ixs_arena *a, size_t initial_size) {
  if (initial_size < IXS_ARENA_DEFAULT_SIZE)
    initial_size = IXS_ARENA_DEFAULT_SIZE;
  a->min_chunk = initial_size;
  a->current = NULL;
  a->spare = NULL;
  a->inline_chunk = NULL;
}

IXS_STATIC void ixs_arena_init_inline(ixs_arena *a, void *storage,
                                      size_t storage_bytes,
                                      size_t initial_size) {
  ixs_arena_chunk *c = (ixs_arena_chunk *)storage;
  size_t header_sz = align_up(sizeof(*c), ARENA_MAX_ALIGN);
  if (initial_size < IXS_ARENA_DEFAULT_SIZE)
    initial_size = IXS_ARENA_DEFAULT_SIZE;
  c->base = (char *)storage + header_sz;
  c->used = 0;
  c->capacity = storage_bytes > header_sz ? storage_bytes - header_sz : 0;
  c->next = NULL;
  a->min_chunk = initial_size;
  a->current = c;
  a->spare = NULL;
  a->inline_chunk = c;
}

IXS_STATIC void ixs_arena_destroy(ixs_arena *a) {
  ixs_arena_chunk *c = a->current;
  while (c) {
    ixs_arena_chunk *next = c->next;
    if (!chunk_is_inline(a, c))
      free(c);
    c = next;
  }
  if (a->spare && !chunk_is_inline(a, a->spare))
    free(a->spare);
  a->current = NULL;
  a->spare = NULL;
}

IXS_STATIC void *ixs_arena_alloc(ixs_arena *a, size_t size, size_t align) {
  if (size == 0)
    size = 1;
  if (align == 0)
    align = 1;

  if (a->current) {
    size_t off = align_up(a->current->used, align);
    if (off <= a->current->capacity && size <= a->current->capacity - off) {
      a->current->used = off + size;
      return a->current->base + off;
    }
  }

  size_t prev = a->current ? a->current->capacity : 0;
  size_t want = size + align;
  if (want < size)
    return NULL; /* overflow */
  size_t cap = prev > 0 ? prev : a->min_chunk;

  while (cap < want) {
    size_t doubled = cap * 2;
    if (doubled <= cap)
      return NULL;
    cap = doubled;
  }

  ixs_arena_chunk *c = NULL;
  if (a->spare && a->spare->capacity >= cap) {
    c = a->spare;
    a->spare = NULL;
    c->used = 0;
    c->next = NULL;
  } else {
    if (a->spare) {
      free(a->spare);
      a->spare = NULL;
    }
    c = chunk_new(cap);
  }
  if (!c)
    return NULL;
  c->next = a->current;
  a->current = c;

  c->used = size;
  return c->base;
}

IXS_STATIC char *ixs_arena_strdup(ixs_arena *a, const char *s, size_t len) {
  if (len == (size_t)-1)
    return NULL;
  char *p = ixs_arena_alloc(a, len + 1, 1);
  if (!p)
    return NULL;
  memcpy(p, s, len);
  p[len] = '\0';
  return p;
}

IXS_STATIC ixs_arena_mark ixs_arena_save(ixs_arena *a) {
  ixs_arena_mark m;
  m.chunk = a->current;
  m.used = a->current ? a->current->used : 0;
  return m;
}

IXS_STATIC void ixs_arena_restore(ixs_arena *a, ixs_arena_mark m) {
  while (a->current != m.chunk) {
    if (!a->current)
      return;
    ixs_arena_chunk *doomed = a->current;
    a->current = doomed->next;
    doomed->used = 0;
    doomed->next = NULL;
    if (chunk_is_inline(a, doomed))
      continue;
    if (!a->spare) {
      a->spare = doomed;
    } else {
      free(doomed);
    }
  }
  if (a->current)
    a->current->used = m.used;
}

IXS_STATIC bool ixs_arena_contains(const ixs_arena *a, const void *ptr) {
  const char *p = (const char *)ptr;
  const ixs_arena_chunk *chunk;

  if (!ptr)
    return false;

  for (chunk = a->current; chunk; chunk = chunk->next) {
    if (p >= chunk->base && p < chunk->base + chunk->used)
      return true;
  }
  return false;
}

IXS_STATIC void *ixs_arena_grow(ixs_arena *a, void *ptr, size_t old_size,
                                size_t new_size, size_t align) {
  if (!ptr)
    return ixs_arena_alloc(a, new_size, align);
  if (new_size < old_size)
    return NULL;
  if (a->current && (char *)ptr >= a->current->base &&
      (size_t)((char *)ptr - a->current->base) + old_size == a->current->used) {
    size_t extra = new_size - old_size;
    if (extra <= a->current->capacity - a->current->used) {
      a->current->used += extra;
      return ptr;
    }
  }
  void *p = ixs_arena_alloc(a, new_size, align);
  if (p)
    memcpy(p, ptr, old_size);
  return p;
}
