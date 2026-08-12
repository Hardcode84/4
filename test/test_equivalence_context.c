/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
/* Canonical grouped-arithmetic and XOR equivalence contracts. */

#include "arena.h"
#include "bounds.h"
#include "bounds_equivalence.h"
#include "facts_store.h"

#include "test_check.h"
#include <stdio.h>
#include <string.h>

static void test_equivalent_expression_contexts(void) {
  static const char left_text[] =
      "context_base + Mod(context_item + floor(Mod(context_item, 16)/4) - "
      "Mod(Mod(context_item, 64), 16), 64)";
  static const char right_text[] =
      "context_base + 16*floor(Mod(context_item, 64)/16) + "
      "floor(Mod(Mod(context_item, 64), 16)/4)";
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *item = ixs_sym(ctx, "context_item");
  ixs_node *round_seed = ixs_sym(ctx, "context_round_seed");
  ixs_node *noninjective = ixs_sym(ctx, "context_noninjective");
  ixs_node *partial_divisor = ixs_sym(ctx, "context_partial_divisor");
  ixs_node *left = ixs_parse_expr(ctx, left_text, sizeof(left_text) - 1u);
  ixs_node *right = ixs_parse_expr(ctx, right_text, sizeof(right_text) - 1u);
  ixs_node *right_bad = ixs_add(ctx, right, ixs_int(ctx, 1));
  ixs_node *two = ixs_int(ctx, 2);
  ixs_node *sixty_four = ixs_int(ctx, 64);
  ixs_node *round_residual = ixs_div(ctx, round_seed, two);
  ixs_node *left_grouped =
      ixs_add(ctx,
              ixs_mul(ctx, ixs_int(ctx, 1024),
                      ixs_floor(ctx, ixs_div(ctx, left, sixty_four))),
              ixs_mul(ctx, ixs_int(ctx, 8), ixs_mod(ctx, left, sixty_four)));
  ixs_node *right_grouped =
      ixs_add(ctx,
              ixs_mul(ctx, ixs_int(ctx, 1024),
                      ixs_floor(ctx, ixs_div(ctx, right, sixty_four))),
              ixs_mul(ctx, ixs_int(ctx, 8), ixs_mod(ctx, right, sixty_four)));
  ixs_node *bad_grouped = ixs_add(
      ctx,
      ixs_mul(ctx, ixs_int(ctx, 1024),
              ixs_floor(ctx, ixs_div(ctx, right_bad, sixty_four))),
      ixs_mul(ctx, ixs_int(ctx, 8), ixs_mod(ctx, right_bad, sixty_four)));
  ixs_node *left_xor =
      ixs_xor(ctx, left, ixs_floor(ctx, ixs_div(ctx, left, two)));
  ixs_node *right_xor =
      ixs_xor(ctx, right, ixs_floor(ctx, ixs_div(ctx, right, two)));
  ixs_node *bad_xor =
      ixs_xor(ctx, right_bad, ixs_floor(ctx, ixs_div(ctx, right_bad, two)));
  ixs_node *wide_left_xor = ixs_xor(ctx, left_xor, ixs_int(ctx, 1));
  ixs_node *wide_right_xor = ixs_xor(ctx, right_xor, ixs_int(ctx, 1));
  ixs_node *left_floor = ixs_add(
      ctx, ixs_floor(ctx, ixs_div(ctx, left, sixty_four)), round_residual);
  ixs_node *right_floor = ixs_floor(
      ctx, ixs_add(ctx, ixs_div(ctx, right, sixty_four), round_residual));
  ixs_node *left_ceil = ixs_add(
      ctx, ixs_ceil(ctx, ixs_div(ctx, left, sixty_four)), round_residual);
  ixs_node *right_ceil = ixs_ceil(
      ctx, ixs_add(ctx, ixs_div(ctx, right, sixty_four), round_residual));
  ixs_node *noninjective_lhs = ixs_floor(ctx, ixs_div(ctx, noninjective, two));
  ixs_node *noninjective_rhs = ixs_floor(
      ctx, ixs_div(ctx, ixs_add(ctx, noninjective, ixs_int(ctx, 1)), two));
  ixs_node *partial_round =
      ixs_floor(ctx, ixs_div(ctx, ixs_int(ctx, 1), partial_divisor));
  ixs_node *partial_lhs = ixs_xor(ctx, left, partial_round);
  ixs_node *partial_rhs = ixs_xor(ctx, right, partial_round);
  ixs_node *outer =
      ixs_cmp(ctx, ixs_sym(ctx, "context_outer"), IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *left_predicate = ixs_cmp(ctx, item, IXS_CMP_LT, ixs_int(ctx, 4));
  ixs_node *right_predicate = ixs_cmp(ctx, item, IXS_CMP_LE, ixs_int(ctx, 3));
  ixs_node *left_and = ixs_and(ctx, outer, left_predicate);
  ixs_node *right_and = ixs_and(ctx, right_predicate, outer);
  ixs_node *grouped_equality =
      ixs_cmp(ctx, left_grouped, IXS_CMP_EQ, right_grouped);
  ixs_node *xor_equality = ixs_cmp(ctx, left_xor, IXS_CMP_EQ, right_xor);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *without_residual_integrality = ixs_facts_create(ctx);
  ixs_facts *narrow = ixs_facts_create(ctx);
  ixs_facts *cycle = ixs_facts_create(ctx);
  ixs_node *cycle_a = ixs_sym(ctx, "context_cycle_a");
  ixs_node *cycle_b = ixs_sym(ctx, "context_cycle_b");
  size_t errors;

  CHECK(ctx && item && round_seed && noninjective && partial_divisor && left &&
        right && right_bad && two && sixty_four && round_residual &&
        left_grouped && right_grouped && bad_grouped && left_xor && right_xor &&
        bad_xor && wide_left_xor && wide_right_xor && left_floor &&
        right_floor && left_ceil && right_ceil && noninjective_lhs &&
        noninjective_rhs && partial_round && partial_lhs && partial_rhs &&
        outer && left_predicate && right_predicate && left_and && right_and &&
        grouped_equality && xor_equality && facts &&
        without_residual_integrality && narrow && cycle && cycle_a && cycle_b);
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, item, IXS_CMP_LE, ixs_int(ctx, 255))));
  CHECK(ixs_facts_assume_pred(facts, ixs_cmp(ctx, ixs_mod(ctx, round_seed, two),
                                             IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(without_residual_integrality,
                              ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(
      ixs_facts_assume_pred(without_residual_integrality,
                            ixs_cmp(ctx, item, IXS_CMP_LE, ixs_int(ctx, 255))));

  CHECK(test_ixs_equivalent_facts(facts, left, right) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, ixs_mod(ctx, left, sixty_four),
                                  ixs_mod(ctx, right, sixty_four)) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, left_grouped, right_grouped) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(facts, grouped_equality) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_predicate_facts(facts, grouped_equality) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, left_xor, right_xor) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(facts, xor_equality) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_predicate_facts(facts, xor_equality) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, left_floor, right_floor) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, left_ceil, right_ceil) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, left_and, right_and) ==
        IXS_CHECK_TRUE);

  CHECK(test_ixs_equivalent_facts(facts, left_grouped, bad_grouped) !=
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, left_xor, bad_xor) != IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, wide_left_xor, wide_right_xor) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(without_residual_integrality, left_floor,
                                  right_floor) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_facts(without_residual_integrality, left_ceil,
                                  right_ceil) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_facts(facts, partial_lhs, partial_rhs) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(
      narrow, ixs_cmp(ctx, noninjective, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      narrow, ixs_cmp(ctx, noninjective, IXS_CMP_LE, ixs_int(ctx, 1))));
  CHECK(test_ixs_equivalent_facts(narrow, noninjective_lhs, noninjective_rhs) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_bounds_equivalence_subproof_limit_probe(
            facts, left_xor, right_xor) == IXS_CHECK_UNKNOWN);

  CHECK(
      ixs_facts_assume_pred(cycle, ixs_cmp(ctx, ixs_sub(ctx, cycle_a, cycle_b),
                                           IXS_CMP_LE, ixs_int(ctx, -1))));
  CHECK(
      ixs_facts_assume_pred(cycle, ixs_cmp(ctx, ixs_sub(ctx, cycle_b, cycle_a),
                                           IXS_CMP_LE, ixs_int(ctx, 0))));
  CHECK(cycle->bounds.contradiction);
  CHECK(test_ixs_equivalent_facts(cycle, left_grouped, right_grouped) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_facts(cycle, left_xor, right_xor) ==
        IXS_CHECK_UNKNOWN);

  errors = ixs_ctx_nerrors(ctx);
  ixs_arena_set_fail_after(&facts->bounds.query_arena, 0);
  CHECK(test_ixs_equivalent_facts(facts, left_xor, right_xor) ==
        IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(&facts->bounds.query_arena,
                           IXS_ARENA_FAILURE_DISABLED);
  CHECK(!facts->bounds.oom);
  CHECK(ixs_ctx_nerrors(ctx) == errors + 1u);
  if (ixs_ctx_nerrors(ctx) != errors)
    CHECK(strstr(ixs_ctx_error(ctx, errors), "out of memory") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_equivalent_facts(facts, left_xor, right_xor) ==
        IXS_CHECK_TRUE);
  CHECK(ixs_ctx_nerrors(ctx) == 0u);

  ixs_arena_set_fail_after(ixs_test_scratch(ctx), 0);
  CHECK(test_ixs_equivalent_facts(facts, wide_left_xor, wide_right_xor) ==
        IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(ixs_test_scratch(ctx), IXS_ARENA_FAILURE_DISABLED);
  CHECK(!facts->bounds.oom);
  CHECK(ixs_ctx_nerrors(ctx) == 1u);
  if (ixs_ctx_nerrors(ctx) != 0u)
    CHECK(strstr(ixs_ctx_error(ctx, 0u), "out of memory") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_equivalent_facts(facts, wide_left_xor, wide_right_xor) ==
        IXS_CHECK_TRUE);
  CHECK(ixs_ctx_nerrors(ctx) == 0u);

  ixs_ctx_destroy(ctx);
}

static void test_generic_context_cancellation(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *item = ixs_sym(ctx, "context_cancel_item");
  ixs_node *within = ixs_sym(ctx, "context_cancel_within");
  ixs_node *two = ixs_int(ctx, 2);
  ixs_node *four = ixs_int(ctx, 4);
  ixs_node *eight = ixs_int(ctx, 8);
  ixs_node *sixteen = ixs_int(ctx, 16);
  ixs_node *sixty_four = ixs_int(ctx, 64);
  ixs_node *digit1_64 = ixs_mod(
      ctx, ixs_floor(ctx, ixs_div(ctx, ixs_mod(ctx, item, sixty_four), two)),
      two);
  ixs_node *digit2_16 = ixs_mod(
      ctx, ixs_floor(ctx, ixs_div(ctx, ixs_mod(ctx, item, sixteen), four)),
      two);
  ixs_node *digit2_64 = ixs_mod(
      ctx, ixs_floor(ctx, ixs_div(ctx, ixs_mod(ctx, item, sixty_four), four)),
      two);
  ixs_node *digit3_16 =
      ixs_floor(ctx, ixs_div(ctx, ixs_mod(ctx, item, sixteen), eight));
  ixs_node *digit3_64 = ixs_mod(
      ctx, ixs_floor(ctx, ixs_div(ctx, ixs_mod(ctx, item, sixty_four), eight)),
      two);
  ixs_node *within_bit = ixs_mod(ctx, within, two);
  ixs_node *xor_16 = ixs_xor(ctx, ixs_mul(ctx, eight, digit3_16),
                             ixs_mul(ctx, ixs_int(ctx, 136), within_bit));
  ixs_node *xor_64 = ixs_xor(ctx, ixs_mul(ctx, ixs_int(ctx, 136), within_bit),
                             ixs_mul(ctx, eight, digit3_64));
  ixs_node *zero_sum =
      ixs_add(ctx,
              ixs_sub(ctx, ixs_mul(ctx, sixteen, ixs_mod(ctx, item, two)),
                      ixs_mul(ctx, sixteen, ixs_mod(ctx, item, four))),
              ixs_add(ctx,
                      ixs_sub(ctx, ixs_mul(ctx, sixty_four, digit2_64),
                              ixs_mul(ctx, sixty_four, digit2_16)),
                      ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 32), digit1_64),
                              ixs_sub(ctx, ixs_mul(ctx, sixteen, xor_64),
                                      ixs_mul(ctx, sixteen, xor_16)))));
  ixs_node *near_miss =
      ixs_add(ctx, zero_sum, ixs_mul(ctx, ixs_int(ctx, -1), digit1_64));
  ixs_node *wrong_width = ixs_mod(
      ctx, ixs_floor(ctx, ixs_div(ctx, ixs_mod(ctx, item, sixty_four), eight)),
      four);
  ixs_node *different_arity = ixs_xor(ctx, xor_16, ixs_int(ctx, 1));
  ixs_node *different_cmp_lhs = ixs_cmp(ctx, item, IXS_CMP_LT, within);
  ixs_node *different_cmp_rhs = ixs_cmp(ctx, item, IXS_CMP_LE, within);
  ixs_node *left_square = ixs_mul(ctx, digit2_16, digit2_16);
  ixs_node *right_square = ixs_mul(ctx, digit2_64, digit2_64);
  ixs_node *right_cube = ixs_mul(ctx, right_square, digit2_64);
  ixs_node *left_max = ixs_max(ctx, digit2_16, digit3_16);
  ixs_node *right_max = ixs_max(ctx, digit3_64, digit2_64);
  ixs_facts *facts = ixs_facts_create(ctx);
  const ixs_node *batch[2] = {zero_sum, near_miss};
  facts_query_cache *fact_cache;
  ixs_facts_equivalence_cache_stats_result proof_cache;
  size_t proof_hits;
  size_t projection_visits;
  size_t projection_skips;

  CHECK(ctx && item && within && digit1_64 && digit2_16 && digit2_64 &&
        digit3_16 && digit3_64 && within_bit && xor_16 && xor_64 && zero_sum &&
        near_miss && wrong_width && different_arity && different_cmp_lhs &&
        different_cmp_rhs && left_square && right_square && right_cube &&
        left_max && right_max && facts);
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, item, IXS_CMP_EQ, ixs_floor(ctx, item))));
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, within, IXS_CMP_EQ, ixs_floor(ctx, within))));
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, within, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, within, IXS_CMP_LE, ixs_int(ctx, 3))));

  CHECK(test_ixs_equivalent_facts(facts, digit2_16, digit2_64) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, digit3_16, digit3_64) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, xor_16, xor_64) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, left_square, right_square) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, left_max, right_max) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, zero_sum, ixs_int(ctx, 0)) ==
        IXS_CHECK_TRUE);
  ixs_facts_equivalence_cache_stats(ctx, &proof_cache);
  CHECK(proof_cache.stores != 0u);
  CHECK(proof_cache.retained_bytes <= proof_cache.retained_limit);
  proof_hits = proof_cache.hits;
  CHECK(test_ixs_equivalent_facts(facts, zero_sum, ixs_int(ctx, 0)) ==
        IXS_CHECK_TRUE);
  ixs_facts_equivalence_cache_stats(ctx, &proof_cache);
  CHECK(proof_cache.hits > proof_hits);
  fact_cache = facts->bounds.facts_query_cache;
  CHECK(fact_cache != NULL);
  projection_visits = facts->bounds.exact_projection_visits;
  projection_skips = facts->bounds.exact_projection_skips;
  CHECK(ixs_simplify_facts(facts, zero_sum) == ixs_int(ctx, 0));
  CHECK(facts->bounds.exact_projection_visits - projection_visits < 128u);
  CHECK(facts->bounds.exact_projection_skips != projection_skips);
  CHECK(fact_cache->identity_stores != 0u);
  CHECK(fact_cache->simplify_stores != 0u);
  CHECK(ixs_simplify_facts(facts, zero_sum) == ixs_int(ctx, 0));
  CHECK(fact_cache->simplify_hits != 0u);
  fact_cache->simplify[zero_sum->hash & (FACTS_SIMPLIFY_CACHE_CAP - 1u)]
      .source = NULL;
  CHECK(ixs_simplify_facts(facts, zero_sum) == ixs_int(ctx, 0));
  CHECK(fact_cache->identity_hits != 0u);
  ixs_simplify_batch_facts(facts, batch, 2u);
  CHECK(batch[0] == ixs_int(ctx, 0));
  CHECK(batch[1] != ixs_int(ctx, 0));

  CHECK(test_ixs_equivalent_facts(facts, near_miss, ixs_int(ctx, 0)) !=
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, digit3_16, wrong_width) !=
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, different_arity, xor_64) !=
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, different_cmp_lhs,
                                  different_cmp_rhs) != IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, left_square, right_cube) !=
        IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_direct_fact_query_cache(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "direct_cache_x");
  ixs_node *y = ixs_sym(ctx, "direct_cache_y");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *predicate = ixs_cmp(ctx, x, IXS_CMP_EQ, zero);
  const ixs_node *predicates[1] = {predicate};
  ixs_facts *first =
      ixs_facts_create_preds(IXS_TEST_SESSION(ctx), predicates, 1u);
  ixs_facts *second =
      ixs_facts_create_preds(IXS_TEST_SESSION(ctx), predicates, 1u);
  ixs_facts *empty_first = ixs_facts_create(ctx);
  ixs_facts *empty_second = ixs_facts_create(ctx);
  ixs_facts_closure_cache_stats_result after;
  ixs_facts_closure_cache_stats_result before;
  facts_query_cache *shared;
  size_t hits;
  size_t i;

  CHECK(ctx && x && y && zero && predicate && first && second && empty_first &&
        empty_second);
  CHECK(sizeof(*first) <= sizeof(first->bounds) + 64u);
  CHECK(empty_first->bounds.facts_query_cache == NULL);
  CHECK(empty_second->bounds.facts_query_cache == NULL);
  ixs_facts_closure_cache_stats(ctx, &before);
  for (i = 0; i < 256u; i++)
    CHECK(ixs_facts_create(ctx) != NULL);
  ixs_facts_closure_cache_stats(ctx, &after);
  CHECK(after.retained_bytes == before.retained_bytes);
  shared = first->bounds.facts_query_cache;
  CHECK(shared && shared == second->bounds.facts_query_cache);
  CHECK(test_ixs_simplify_facts(first, x) == zero);
  hits = shared->simplify_hits;
  CHECK(test_ixs_simplify_facts(second, x) == zero);
  CHECK(shared->simplify_hits == hits + 1u);

  CHECK(ixs_facts_assume_pred(second,
                              ixs_cmp(ctx, y, IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(second->bounds.facts_query_cache != NULL);
  CHECK(second->bounds.facts_query_cache != first->bounds.facts_query_cache ||
        second->bounds.facts_query_generation !=
            first->bounds.facts_query_generation);
  CHECK(first->bounds.facts_query_cache == shared);
  CHECK(test_ixs_simplify_facts(first, x) == zero);
  CHECK(test_ixs_simplify_facts(second, y) == zero);

  ixs_ctx_destroy(ctx);
}

static void test_equivalence_cache_clean_miss(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *a = ixs_sym(ctx, "proof_cache_a");
  ixs_node *b = ixs_sym(ctx, "proof_cache_b");
  ixs_node *c = ixs_sym(ctx, "proof_cache_c");
  ixs_node *d = ixs_sym(ctx, "proof_cache_d");
  ixs_node *e = ixs_sym(ctx, "proof_cache_e");
  ixs_node *lhs = ixs_max(ctx, a, b);
  ixs_node *rhs = ixs_max(ctx, c, d);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_session_binding binding;
  ixs_facts_equivalence_cache_stats_result after;
  ixs_facts_equivalence_cache_stats_result before;
  ixs_check_result cached = IXS_CHECK_TRUE;
  uint64_t domain_id;

  CHECK(ctx && a && b && c && d && e && lhs && rhs && facts);
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, a, IXS_CMP_GE, ixs_int(ctx, 0))));

  ixs_facts_equivalence_cache_stats(ctx, &before);
  CHECK(test_ixs_equivalent_facts(facts, lhs, rhs) == IXS_CHECK_UNKNOWN);
  ixs_facts_equivalence_cache_stats(ctx, &after);
  CHECK(after.stores > before.stores);
  CHECK(after.retained_bytes <= after.retained_limit);
  before = after;
  CHECK(test_ixs_equivalent_facts(facts, lhs, rhs) == IXS_CHECK_UNKNOWN);
  ixs_facts_equivalence_cache_stats(ctx, &after);
  CHECK(after.hits > before.hits);

  CHECK(ixs_session_bind(&binding, IXS_TEST_SESSION(ctx)) == ctx);
  facts_equivalence_cache_store(ctx, &facts->bounds, a, b, 3u, 1u,
                                IXS_CHECK_UNKNOWN);
  CHECK(facts_equivalence_cache_lookup(ctx, &facts->bounds, b, a, 3u, 1u,
                                       &cached));
  CHECK(cached == IXS_CHECK_UNKNOWN);
  CHECK(!facts_equivalence_cache_lookup(ctx, &facts->bounds, a, b, 4u, 1u,
                                        &cached));
  CHECK(!facts_equivalence_cache_lookup(ctx, &facts->bounds, a, b, 3u, 2u,
                                        &cached));
  facts->bounds.exact_projection_depth++;
  CHECK(!facts_equivalence_cache_lookup(ctx, &facts->bounds, a, b, 3u, 1u,
                                        &cached));
  facts_equivalence_cache_store(ctx, &facts->bounds, a, b, 3u, 1u,
                                IXS_CHECK_FALSE);
  CHECK(facts_equivalence_cache_lookup(ctx, &facts->bounds, a, b, 3u, 1u,
                                       &cached));
  CHECK(cached == IXS_CHECK_FALSE);
  facts->bounds.exact_projection_depth--;
  CHECK(facts_equivalence_cache_lookup(ctx, &facts->bounds, a, b, 3u, 1u,
                                       &cached));
  CHECK(cached == IXS_CHECK_UNKNOWN);
  ixs_session_unbind(&binding);

  domain_id = facts->bounds.facts_query_cache->domain_id;
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, e, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(facts->bounds.facts_query_cache->domain_id != domain_id);
  CHECK(!facts_equivalence_cache_lookup(ctx, &facts->bounds, a, b, 3u, 1u,
                                        &cached));

  ixs_facts_equivalence_cache_stats(ctx, &before);
  ixs_arena_set_fail_after(&facts->bounds.query_arena, 0);
  CHECK(test_ixs_equivalent_facts(facts, lhs, rhs) == IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(&facts->bounds.query_arena,
                           IXS_ARENA_FAILURE_DISABLED);
  ixs_facts_equivalence_cache_stats(ctx, &after);
  CHECK(after.stores == before.stores);
  CHECK(test_ixs_equivalent_facts(facts, lhs, rhs) == IXS_CHECK_UNKNOWN);
  ixs_facts_equivalence_cache_stats(ctx, &after);
  CHECK(after.stores > before.stores);

  ixs_ctx_destroy(ctx);
}

static void test_equivalence_keeps_exact_projection(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *y = ixs_sym(ctx, "exact_projection_y");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *masked = ixs_and(ctx, ixs_int(ctx, 2), y);
  ixs_facts *facts = ixs_facts_create(ctx);

  CHECK(ctx && y && zero && masked && facts);
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, y, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, y, IXS_CMP_LE, ixs_int(ctx, 63))));
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, ixs_mod(ctx, y, ixs_int(ctx, 4)),
                                      IXS_CMP_EQ, ixs_int(ctx, 1))));
  CHECK(test_ixs_equivalent_facts(facts, masked, zero) == IXS_CHECK_TRUE);
  CHECK(test_ixs_simplify_facts(facts, masked) == zero);
  CHECK(test_ixs_equivalent_facts(facts, masked, zero) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

int main(void) {
  test_equivalent_expression_contexts();
  test_generic_context_cancellation();
  test_direct_fact_query_cache();
  test_equivalence_cache_clean_miss();
  test_equivalence_keeps_exact_projection();
  printf("test_equivalence_context: %d/%d passed\n", tests_passed, tests_run);
  return tests_passed == tests_run ? 0 : 1;
}
