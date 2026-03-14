#ifndef IXS_ARENA_H
#define IXS_ARENA_H

#include <stddef.h>

#define IXS_ARENA_DEFAULT_SIZE 4096

typedef struct ixs_arena_chunk {
  char *base;
  size_t used;
  size_t capacity;
  struct ixs_arena_chunk *next;
} ixs_arena_chunk;

typedef struct {
  ixs_arena_chunk *current;
  size_t min_chunk;
} ixs_arena;

void ixs_arena_init(ixs_arena *a, size_t initial_size);
void ixs_arena_destroy(ixs_arena *a);

/* Returns NULL on OOM. align must be a power of 2. */
void *ixs_arena_alloc(ixs_arena *a, size_t size, size_t align);

/* Copy len bytes of s into the arena, null-terminate. NULL on OOM. */
char *ixs_arena_strdup(ixs_arena *a, const char *s, size_t len);

#endif /* IXS_ARENA_H */
