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
        IXS_CHECK_UNKNOWN);
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

  ixs_ctx_destroy(ctx);
}

int main(void) {
  test_equivalent_expression_contexts();
  printf("test_equivalence_context: %d/%d passed\n", tests_passed, tests_run);
  return tests_passed == tests_run ? 0 : 1;
}
