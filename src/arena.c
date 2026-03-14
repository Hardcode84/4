#include "arena.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

static size_t align_up(size_t val, size_t align) {
  return (val + align - 1) & ~(align - 1);
}

static ixs_arena_chunk *chunk_new(size_t capacity) {
  ixs_arena_chunk *c = malloc(sizeof(*c));
  if (!c)
    return NULL;
  c->base = malloc(capacity);
  if (!c->base) {
    free(c);
    return NULL;
  }
  c->used = 0;
  c->capacity = capacity;
  c->next = NULL;
  return c;
}

void ixs_arena_init(ixs_arena *a, size_t initial_size) {
  if (initial_size < IXS_ARENA_DEFAULT_SIZE)
    initial_size = IXS_ARENA_DEFAULT_SIZE;
  a->min_chunk = initial_size;
  a->current = NULL;
}

void ixs_arena_destroy(ixs_arena *a) {
  ixs_arena_chunk *c = a->current;
  while (c) {
    ixs_arena_chunk *next = c->next;
    free(c->base);
    free(c);
    c = next;
  }
  a->current = NULL;
}

void *ixs_arena_alloc(ixs_arena *a, size_t size, size_t align) {
  if (size == 0)
    size = 1;
  if (align == 0)
    align = 1;

  if (a->current) {
    size_t off = align_up(a->current->used, align);
    if (off + size <= a->current->capacity) {
      a->current->used = off + size;
      return a->current->base + off;
    }
  }

  /* Need a new chunk. Double previous, but at least big enough. */
  size_t prev = a->current ? a->current->capacity : 0;
  size_t want = size + align;
  size_t cap = prev > 0 ? prev : a->min_chunk;

  /* Double until big enough, with overflow check. */
  while (cap < want) {
    size_t doubled = cap * 2;
    if (doubled <= cap)
      return NULL; /* overflow */
    cap = doubled;
  }

  ixs_arena_chunk *c = chunk_new(cap);
  if (!c)
    return NULL;
  c->next = a->current;
  a->current = c;

  size_t off = align_up(0, align);
  c->used = off + size;
  return c->base + off;
}

char *ixs_arena_strdup(ixs_arena *a, const char *s, size_t len) {
  char *p = ixs_arena_alloc(a, len + 1, 1);
  if (!p)
    return NULL;
  memcpy(p, s, len);
  p[len] = '\0';
  return p;
}
