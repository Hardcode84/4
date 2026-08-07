/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
/*
 * Public-API benchmark for the loop-bound relation and long-chain scaling.
 * Facts remain arena-owned so peak RSS exposes retained bytes per fact set as
 * the iteration count grows.
 */

#include <errno.h>
#include <ixsimpl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define DEFAULT_ITERATIONS 20000u
#define DEFAULT_CHAIN_ITERATIONS 100u
#define PREDICATE_COUNT 4u

static bool parse_iterations(const char *text, size_t *iterations) {
  char *end;
  unsigned long long parsed;
  if (!text || !iterations || !*text)
    return false;
  errno = 0;
  end = NULL;
  parsed = strtoull(text, &end, 10);
  if (errno != 0 || !end || *end != '\0' || parsed == 0 ||
      parsed > (unsigned long long)SIZE_MAX)
    return false;
  *iterations = (size_t)parsed;
  return true;
}

static bool assume_all(ixs_facts *facts, const ixs_node *const *predicates) {
  size_t i;
  for (i = 0; i < PREDICATE_COUNT; i++) {
    if (!ixs_facts_assume_pred(facts, predicates[i]))
      return false;
  }
  return true;
}

static bool is_expected_loop_range(const ixs_range_result *range) {
  return range->has_lower && range->lower_p == 0 && range->lower_q == 1 &&
         range->has_upper && range->upper_p == INT64_C(2147483646) &&
         range->upper_q == 1;
}

static int run_chain_benchmark(ixs_session *session, size_t iterations,
                               size_t edges, bool require_proof) {
  ixs_node **nodes;
  ixs_node **predicates;
  size_t predicate_count;
  size_t i;
  size_t iteration;
  size_t proven = 0;
  clock_t start;
  clock_t finish;
  double elapsed_ms;

  if (edges == SIZE_MAX || edges + 1u > SIZE_MAX / sizeof(*nodes) ||
      edges + 1u > SIZE_MAX / sizeof(*predicates))
    return 1;
  predicate_count = edges + 1u;
  nodes = malloc(predicate_count * sizeof(*nodes));
  predicates = malloc(predicate_count * sizeof(*predicates));
  if (!nodes || !predicates)
    goto failed;

  for (i = 0; i < predicate_count; i++) {
    char name[48];
    int written =
        snprintf(name, sizeof(name), "benchmark_chain_%lu", (unsigned long)i);
    if (written <= 0 || (size_t)written >= sizeof(name))
      goto failed;
    nodes[i] = ixs_sym(session, name);
    if (!nodes[i])
      goto failed;
  }
  for (i = 0; i < edges; i++) {
    predicates[i] = ixs_cmp(session, ixs_sub(session, nodes[i], nodes[i + 1u]),
                            IXS_CMP_LE, ixs_int(session, 0));
    if (!predicates[i])
      goto failed;
  }
  predicates[edges] =
      ixs_cmp(session, nodes[edges], IXS_CMP_LE, ixs_int(session, 0));
  if (!predicates[edges])
    goto failed;

  start = clock();
  if (start == (clock_t)-1)
    goto failed;
  for (iteration = 0; iteration < iterations; iteration++) {
    ixs_facts *facts = ixs_facts_create(session);
    ixs_range_query_result range;
    if (!facts || !ixs_facts_assume_preds(facts, predicates, predicate_count))
      goto failed;
    range = ixs_range_facts(facts, nodes[0]);
    if (range.status == IXS_FACT_QUERY_COMPLETE && range.available &&
        range.range.has_upper && range.range.upper_p == 0 &&
        range.range.upper_q == 1)
      proven++;
  }
  finish = clock();
  if (finish == (clock_t)-1)
    goto failed;

  elapsed_ms = 1000.0 * (double)(finish - start) / (double)CLOCKS_PER_SEC;
  printf("bench_relational_facts: %zu fact sets, %zu-edge chain mode\n",
         iterations, edges);
  printf("  proofs: %zu/%zu\n", proven, iterations);
  printf("  cpu: %.3f ms total, %.3f us/fact\n", elapsed_ms,
         1000.0 * elapsed_ms / (double)iterations);
  free(predicates);
  free(nodes);
  return require_proof && proven != iterations ? 1 : 0;

failed:
  free(predicates);
  free(nodes);
  return 1;
}

int main(int argc, char **argv) {
  bool control = false;
  bool require_proof = false;
  bool have_iterations = false;
  size_t chain_edges = 0;
  size_t iterations = DEFAULT_ITERATIONS;
  size_t i;
  size_t proven = 0;
  clock_t start;
  clock_t finish;
  double elapsed_ms;
  ixs_ctx *ctx;
  ixs_session session;
  const ixs_node *iv;
  const ixs_node *trip;
  const ixs_node *zero;
  const ixs_node *relation_predicates[PREDICATE_COUNT];
  const ixs_node *control_predicates[PREDICATE_COUNT];
  const ixs_node *const *predicates;
  int argi;

  for (argi = 1; argi < argc; argi++) {
    if (strcmp(argv[argi], "--control") == 0) {
      control = true;
    } else if (strcmp(argv[argi], "--require-proof") == 0) {
      require_proof = true;
    } else if (strcmp(argv[argi], "--chain-edges") == 0) {
      if (++argi >= argc || !parse_iterations(argv[argi], &chain_edges)) {
        fprintf(stderr, "bench_relational_facts: invalid chain length\n");
        return 1;
      }
    } else if (!have_iterations && parse_iterations(argv[argi], &iterations)) {
      have_iterations = true;
    } else {
      fprintf(stderr, "usage: bench_relational_facts [--control] "
                      "[--require-proof] [--chain-edges N] [iterations]\n");
      return 1;
    }
  }
  if (control && chain_edges != 0) {
    fprintf(stderr, "bench_relational_facts: chain mode has no control mode\n");
    return 1;
  }
  if (chain_edges != 0 && !have_iterations)
    iterations = DEFAULT_CHAIN_ITERATIONS;

  ctx = ixs_ctx_create();
  if (!ctx) {
    fprintf(stderr, "bench_relational_facts: out of memory\n");
    return 1;
  }
  ixs_session_init(&session, ctx);
  if (chain_edges != 0) {
    int status =
        run_chain_benchmark(&session, iterations, chain_edges, require_proof);
    ixs_session_destroy(&session);
    ixs_ctx_destroy(ctx);
    return status;
  }
  iv = ixs_sym(&session, "benchmark_loop_iv");
  trip = ixs_sym(&session, "benchmark_loop_trip");
  zero = ixs_int(&session, 0);
  if (!iv || !trip || !zero)
    goto failed;

  relation_predicates[0] = ixs_cmp(&session, ixs_sub(&session, iv, trip),
                                   IXS_CMP_LE, ixs_int(&session, -1));
  relation_predicates[1] = ixs_cmp(&session, iv, IXS_CMP_GE, zero);
  relation_predicates[2] =
      ixs_cmp(&session, trip, IXS_CMP_GE, ixs_int(&session, INT32_MIN));
  relation_predicates[3] =
      ixs_cmp(&session, trip, IXS_CMP_LE, ixs_int(&session, INT32_MAX));

  control_predicates[0] =
      ixs_cmp(&session, iv, IXS_CMP_LE, ixs_int(&session, INT64_C(2147483646)));
  control_predicates[1] = relation_predicates[1];
  control_predicates[2] = relation_predicates[2];
  control_predicates[3] = relation_predicates[3];
  for (i = 0; i < PREDICATE_COUNT; i++) {
    if (!relation_predicates[i] || !control_predicates[i])
      goto failed;
  }
  predicates = control ? control_predicates : relation_predicates;

  start = clock();
  if (start == (clock_t)-1)
    goto failed;
  for (i = 0; i < iterations; i++) {
    ixs_facts *facts = ixs_facts_create(&session);
    ixs_range_query_result range;
    if (!facts || !assume_all(facts, predicates))
      goto failed;
    range = ixs_range_facts(facts, iv);
    if (range.status == IXS_FACT_QUERY_COMPLETE && range.available &&
        is_expected_loop_range(&range.range))
      proven++;
  }
  finish = clock();
  if (finish == (clock_t)-1)
    goto failed;

  elapsed_ms = 1000.0 * (double)(finish - start) / (double)CLOCKS_PER_SEC;
  printf("bench_relational_facts: %zu fact sets, %s mode\n", iterations,
         control ? "control" : "relation");
  printf("  proofs: %zu/%zu\n", proven, iterations);
  printf("  cpu: %.3f ms total, %.3f us/fact\n", elapsed_ms,
         1000.0 * elapsed_ms / (double)iterations);

  ixs_session_destroy(&session);
  ixs_ctx_destroy(ctx);
  return require_proof && proven != iterations ? 1 : 0;

failed:
  fprintf(stderr, "bench_relational_facts: construction or mutation failed\n");
  ixs_session_destroy(&session);
  ixs_ctx_destroy(ctx);
  return 1;
}
