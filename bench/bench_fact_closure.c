/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
/* Controlled benchmark for repeated empty-domain fact batches. */

#include "node.h"

#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CACHE_SLOT_COUNT 32u
#define CACHEABLE_CHAIN_PREDICATES 16u
#define INDEPENDENT_PREDICATES 32u
#define INDEPENDENT_BATCHES 16u
#define COLLIDING_BATCHES 8u
#define BATCH_POOL_SIZE 512u
#define LONG_CHAIN_PREDICATES 96u
#define LARGE_BATCH_PREDICATES 160u
#define GROWTH_BATCH_PREDICATES 64u

typedef struct {
  const ixs_node **predicates;
  size_t count;
  const ixs_node *query;
} closure_batch;

typedef struct {
  ixs_ctx *ctx;
  ixs_session session;
  closure_batch *batches;
  size_t batch_count;
  size_t *schedule;
  size_t schedule_count;
  size_t iterations;
  size_t prepared_bytes;
  size_t ready_bytes;
  bool reset_each;
} closure_benchmark;

static bool parse_size(const char *text, size_t *value) {
  char *end = NULL;
  unsigned long long parsed;
  if (!text || !value || !*text)
    return false;
  errno = 0;
  parsed = strtoull(text, &end, 10);
  if (errno != 0 || !end || *end != '\0' || parsed == 0 ||
      parsed > (unsigned long long)SIZE_MAX)
    return false;
  *value = (size_t)parsed;
  return true;
}

static bool checked_add_size(size_t *total, size_t value) {
  if (*total > SIZE_MAX - value)
    return false;
  *total += value;
  return true;
}

static bool arena_retained_bytes(const ixs_arena *arena, size_t *bytes) {
  const ixs_arena_chunk *chunk;
  size_t total = 0;
  if (!arena || !bytes)
    return false;
  for (chunk = arena->current; chunk; chunk = chunk->next) {
    if (!checked_add_size(&total, chunk->capacity))
      return false;
  }
  if (arena->spare && !checked_add_size(&total, arena->spare->capacity))
    return false;
  *bytes = total;
  return true;
}

static bool benchmark_retained_bytes(const closure_benchmark *benchmark,
                                     size_t *bytes) {
  const ixs_session_impl *impl;
  size_t total = 0;
  size_t part;
  if (!benchmark || !benchmark->ctx || !bytes)
    return false;
  impl = ixs_session_cget(&benchmark->session);
  if (!arena_retained_bytes(&benchmark->ctx->arena, &part) ||
      !checked_add_size(&total, part) ||
      benchmark->ctx->htab_cap > SIZE_MAX / sizeof(*benchmark->ctx->htab) ||
      !checked_add_size(&total, benchmark->ctx->htab_cap *
                                    sizeof(*benchmark->ctx->htab)) ||
      !arena_retained_bytes(&impl->scratch, &part) ||
      !checked_add_size(&total, part) ||
      !arena_retained_bytes(&impl->diag, &part) ||
      !checked_add_size(&total, part))
    return false;
  *bytes = total;
  return true;
}

static void closure_batch_destroy(closure_batch *batch) {
  if (!batch)
    return;
  free(batch->predicates);
  memset(batch, 0, sizeof(*batch));
}

static void closure_benchmark_destroy(closure_benchmark *benchmark) {
  size_t i;
  if (!benchmark)
    return;
  for (i = 0; i < benchmark->batch_count; i++)
    closure_batch_destroy(&benchmark->batches[i]);
  free(benchmark->batches);
  free(benchmark->schedule);
  if (benchmark->ctx) {
    ixs_session_destroy(&benchmark->session);
    ixs_ctx_destroy(benchmark->ctx);
  }
  memset(benchmark, 0, sizeof(*benchmark));
}

static bool make_name(char *buffer, size_t capacity, const char *prefix,
                      size_t batch, size_t index) {
  int written = snprintf(buffer, capacity, "%s_%lu_%lu", prefix,
                         (unsigned long)batch, (unsigned long)index);
  return written > 0 && (size_t)written < capacity;
}

static bool build_chain_batch(closure_benchmark *benchmark,
                              closure_batch *batch, size_t batch_index,
                              size_t predicate_count) {
  const ixs_node **nodes = NULL;
  const ixs_node *zero;
  size_t i;
  char name[64];
  bool ok = false;
  if (!benchmark || !batch || predicate_count < 2u ||
      predicate_count > SIZE_MAX / sizeof(*nodes))
    return false;
  nodes = calloc(predicate_count, sizeof(*nodes));
  batch->predicates = calloc(predicate_count, sizeof(*batch->predicates));
  if (!nodes || !batch->predicates)
    goto cleanup;
  batch->count = predicate_count;
  zero = ixs_int(&benchmark->session, 0);
  if (!zero)
    goto cleanup;
  for (i = 0; i < predicate_count; i++) {
    if (!make_name(name, sizeof(name), "closure_chain", batch_index, i))
      goto cleanup;
    nodes[i] = ixs_sym(&benchmark->session, name);
    if (!nodes[i])
      goto cleanup;
  }
  batch->predicates[0] = ixs_cmp(
      &benchmark->session, ixs_add(&benchmark->session, nodes[0], nodes[1]),
      IXS_CMP_GE, zero);
  for (i = 1; i + 1u < predicate_count; i++) {
    batch->predicates[i] =
        ixs_cmp(&benchmark->session,
                ixs_add(&benchmark->session, nodes[i], nodes[i + 1u]),
                IXS_CMP_EQ, zero);
  }
  batch->predicates[predicate_count - 1u] = ixs_cmp(
      &benchmark->session, nodes[predicate_count - 1u], IXS_CMP_EQ, zero);
  batch->query = ixs_cmp(&benchmark->session, nodes[0], IXS_CMP_GE, zero);
  for (i = 0; i < predicate_count; i++) {
    if (!batch->predicates[i])
      goto cleanup;
  }
  ok = batch->query != NULL;

cleanup:
  free(nodes);
  if (!ok)
    closure_batch_destroy(batch);
  return ok;
}

static bool build_independent_batch(closure_benchmark *benchmark,
                                    closure_batch *batch, size_t batch_index,
                                    size_t predicate_count) {
  const ixs_node *zero;
  size_t i;
  char name[64];
  if (!benchmark || !batch || predicate_count == 0 ||
      predicate_count > SIZE_MAX / sizeof(*batch->predicates))
    return false;
  batch->predicates = calloc(predicate_count, sizeof(*batch->predicates));
  if (!batch->predicates)
    return false;
  batch->count = predicate_count;
  zero = ixs_int(&benchmark->session, 0);
  if (!zero)
    goto failed;
  for (i = 0; i < predicate_count; i++) {
    const ixs_node *symbol;
    if (!make_name(name, sizeof(name), "closure_independent", batch_index, i))
      goto failed;
    symbol = ixs_sym(&benchmark->session, name);
    batch->predicates[i] =
        symbol ? ixs_cmp(&benchmark->session, symbol, IXS_CMP_GE, zero) : NULL;
    if (!batch->predicates[i])
      goto failed;
  }
  batch->query = batch->predicates[0];
  return true;

failed:
  closure_batch_destroy(batch);
  return false;
}

static size_t closure_cache_slot(const closure_batch *batch) {
  uint64_t hash = UINT64_C(0x9e3779b97f4a7c15) ^ (uint64_t)batch->count;
  size_t i;
  for (i = 0; i < batch->count; i++) {
    uint64_t value = (uint64_t)(uintptr_t)batch->predicates[i];
    hash ^= value + UINT64_C(0x9e3779b97f4a7c15) + (hash << 6) + (hash >> 2);
  }
  hash ^= hash >> 33;
  hash *= UINT64_C(0xff51afd7ed558ccd);
  hash ^= hash >> 33;
  return (size_t)hash & (CACHE_SLOT_COUNT - 1u);
}

static bool allocate_batches(closure_benchmark *benchmark, size_t count) {
  if (!benchmark || count == 0 ||
      count > SIZE_MAX / sizeof(*benchmark->batches))
    return false;
  benchmark->batches = calloc(count, sizeof(*benchmark->batches));
  if (!benchmark->batches)
    return false;
  benchmark->batch_count = count;
  return true;
}

static bool allocate_schedule(closure_benchmark *benchmark, size_t count) {
  if (!benchmark || count == 0 ||
      count > SIZE_MAX / sizeof(*benchmark->schedule))
    return false;
  benchmark->schedule = calloc(count, sizeof(*benchmark->schedule));
  if (!benchmark->schedule)
    return false;
  benchmark->schedule_count = count;
  return true;
}

static bool setup_single_batch(closure_benchmark *benchmark, bool chain,
                               size_t predicate_count) {
  if (!allocate_batches(benchmark, 1u) || !allocate_schedule(benchmark, 1u))
    return false;
  benchmark->schedule[0] = 0;
  return chain ? build_chain_batch(benchmark, &benchmark->batches[0], 0,
                                   predicate_count)
               : build_independent_batch(benchmark, &benchmark->batches[0], 0,
                                         predicate_count);
}

static bool setup_cold_chains(closure_benchmark *benchmark) {
  size_t i;
  if (!allocate_batches(benchmark, benchmark->iterations) ||
      !allocate_schedule(benchmark, benchmark->iterations))
    return false;
  for (i = 0; i < benchmark->iterations; i++) {
    benchmark->schedule[i] = i;
    if (!build_chain_batch(benchmark, &benchmark->batches[i], i,
                           CACHEABLE_CHAIN_PREDICATES))
      return false;
  }
  benchmark->reset_each = true;
  return true;
}

static bool setup_batch_pool(closure_benchmark *benchmark, bool collisions) {
  size_t slot_indices[CACHE_SLOT_COUNT][COLLIDING_BATCHES];
  size_t slot_counts[CACHE_SLOT_COUNT];
  bool used[CACHE_SLOT_COUNT];
  size_t selected = 0;
  size_t i;
  size_t slot;
  memset(slot_counts, 0, sizeof(slot_counts));
  memset(slot_indices, 0, sizeof(slot_indices));
  memset(used, 0, sizeof(used));
  if (!allocate_batches(benchmark, BATCH_POOL_SIZE))
    return false;
  for (i = 0; i < BATCH_POOL_SIZE; i++) {
    if (!build_independent_batch(benchmark, &benchmark->batches[i], i,
                                 INDEPENDENT_PREDICATES))
      return false;
    slot = closure_cache_slot(&benchmark->batches[i]);
    if (slot_counts[slot] < COLLIDING_BATCHES)
      slot_indices[slot][slot_counts[slot]] = i;
    slot_counts[slot]++;
  }
  if (collisions) {
    if (!allocate_schedule(benchmark, COLLIDING_BATCHES))
      return false;
    for (slot = 0; slot < CACHE_SLOT_COUNT; slot++) {
      if (slot_counts[slot] < COLLIDING_BATCHES)
        continue;
      for (i = 0; i < COLLIDING_BATCHES; i++)
        benchmark->schedule[i] = slot_indices[slot][i];
      selected = COLLIDING_BATCHES;
      break;
    }
  } else {
    if (!allocate_schedule(benchmark, INDEPENDENT_BATCHES))
      return false;
    for (i = 0; i < BATCH_POOL_SIZE && selected < INDEPENDENT_BATCHES; i++) {
      slot = closure_cache_slot(&benchmark->batches[i]);
      if (used[slot])
        continue;
      used[slot] = true;
      benchmark->schedule[selected++] = i;
    }
  }
  benchmark->reset_each = true;
  return selected == benchmark->schedule_count;
}

static bool assume_batch(closure_benchmark *benchmark, size_t batch_index,
                         bool verify) {
  closure_batch *batch = &benchmark->batches[batch_index];
  ixs_facts *facts = ixs_facts_create(&benchmark->session);
  if (!facts || !ixs_facts_assume_preds(facts, batch->predicates, batch->count))
    return false;
  return !verify || ixs_check_facts(facts, batch->query) == IXS_CHECK_TRUE;
}

static bool seed_schedule(closure_benchmark *benchmark) {
  size_t i;
  for (i = 0; i < benchmark->schedule_count; i++) {
    if (!assume_batch(benchmark, benchmark->schedule[i], true))
      return false;
    ixs_session_reset(&benchmark->session);
  }
  return true;
}

static bool setup_scenario(closure_benchmark *benchmark, const char *scenario,
                           size_t iterations) {
  bool seed = false;
  memset(benchmark, 0, sizeof(*benchmark));
  benchmark->iterations = iterations;
  benchmark->ctx = ixs_ctx_create();
  if (!benchmark->ctx)
    return false;
  ixs_session_init(&benchmark->session, benchmark->ctx);
  if (strcmp(scenario, "cold-chain") == 0) {
    if (!setup_cold_chains(benchmark))
      return false;
  } else if (strcmp(scenario, "warm-chain") == 0) {
    if (!setup_single_batch(benchmark, true, CACHEABLE_CHAIN_PREDICATES))
      return false;
    seed = true;
  } else if (strcmp(scenario, "independent") == 0) {
    if (!setup_batch_pool(benchmark, false))
      return false;
    seed = true;
  } else if (strcmp(scenario, "collisions") == 0) {
    if (!setup_batch_pool(benchmark, true))
      return false;
    seed = true;
  } else if (strcmp(scenario, "long-chain") == 0) {
    if (!setup_single_batch(benchmark, true, LONG_CHAIN_PREDICATES))
      return false;
    benchmark->reset_each = true;
  } else if (strcmp(scenario, "large-batch") == 0) {
    if (!setup_single_batch(benchmark, false, LARGE_BATCH_PREDICATES))
      return false;
    benchmark->reset_each = true;
  } else if (strcmp(scenario, "session-reset") == 0) {
    if (!setup_single_batch(benchmark, true, CACHEABLE_CHAIN_PREDICATES))
      return false;
    benchmark->reset_each = true;
    seed = true;
  } else if (strcmp(scenario, "arena-growth") == 0) {
    if (!setup_single_batch(benchmark, false, GROWTH_BATCH_PREDICATES))
      return false;
    seed = true;
  } else {
    return false;
  }
  if (!benchmark_retained_bytes(benchmark, &benchmark->prepared_bytes))
    return false;
  if (seed && !seed_schedule(benchmark))
    return false;
  return benchmark_retained_bytes(benchmark, &benchmark->ready_bytes);
}

static bool run_scenario(closure_benchmark *benchmark, bool profile_memory,
                         size_t *peak_bytes) {
  size_t peak = benchmark->ready_bytes;
  size_t i;
  for (i = 0; i < benchmark->iterations; i++) {
    size_t scheduled = benchmark->schedule[i % benchmark->schedule_count];
    size_t retained;
    if (!assume_batch(benchmark, scheduled, i == 0))
      return false;
    if (benchmark->reset_each)
      ixs_session_reset(&benchmark->session);
    if (!profile_memory)
      continue;
    if (!benchmark_retained_bytes(benchmark, &retained))
      return false;
    if (retained > peak)
      peak = retained;
  }
  if (!benchmark_retained_bytes(benchmark, peak_bytes))
    return false;
  if (peak > *peak_bytes)
    *peak_bytes = peak;
  return true;
}

static void usage(const char *program) {
  fprintf(stderr,
          "usage: %s SCENARIO ITERATIONS [--profile-memory] [--immediate]\n",
          program);
}

int main(int argc, char **argv) {
  closure_benchmark benchmark;
  const char *scenario;
  char command[32];
  size_t iterations;
  size_t peak_bytes;
  bool immediate = false;
  bool profile_memory = false;
  int i;
  if (argc < 3 || !parse_size(argv[2], &iterations)) {
    usage(argv[0]);
    return 2;
  }
  scenario = argv[1];
  for (i = 3; i < argc; i++) {
    if (strcmp(argv[i], "--profile-memory") == 0)
      profile_memory = true;
    else if (strcmp(argv[i], "--immediate") == 0)
      immediate = true;
    else {
      usage(argv[0]);
      return 2;
    }
  }
  if (!setup_scenario(&benchmark, scenario, iterations)) {
    fprintf(stderr, "bench_fact_closure: setup failed\n");
    closure_benchmark_destroy(&benchmark);
    return 1;
  }
  printf("READY\n");
  fflush(stdout);
  if (!immediate && !fgets(command, sizeof(command), stdin)) {
    fprintf(stderr, "bench_fact_closure: missing run command\n");
    closure_benchmark_destroy(&benchmark);
    return 1;
  }
  if (!run_scenario(&benchmark, profile_memory, &peak_bytes)) {
    fprintf(stderr, "bench_fact_closure: mutation or proof failed\n");
    closure_benchmark_destroy(&benchmark);
    return 1;
  }
  printf("scenario=%s\n", scenario);
  printf("operations=%lu\n", (unsigned long)iterations);
  printf("prepared_bytes=%lu\n", (unsigned long)benchmark.prepared_bytes);
  printf("ready_bytes=%lu\n", (unsigned long)benchmark.ready_bytes);
  printf("peak_bytes=%lu\n", (unsigned long)peak_bytes);
  closure_benchmark_destroy(&benchmark);
  return 0;
}
