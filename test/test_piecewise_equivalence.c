/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
/* Bounded first-match Piecewise equivalence contracts. */

#include "arena.h"
#include "bounds.h"
#include "bounds_equivalence.h"
#include "facts_store.h"

#include "test_check.h"
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static void test_piecewise_partition_equivalence(void) {
  static const int64_t keys[4] = {2, 0, 3, 1};
  static const int64_t duplicate_keys[4] = {0, 1, 1, 2};
  static const int64_t even_keys[4] = {4, 0, 6, 2};
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *selector = ixs_sym(ctx, "piecewise_partition_selector");
  ixs_node *even_selector = ixs_sym(ctx, "piecewise_even_selector");
  ixs_node *base = ixs_sym(ctx, "piecewise_partition_base");
  ixs_node *partial_divisor = ixs_sym(ctx, "piecewise_partial_divisor");
  ixs_node *expected = ixs_add(ctx, base, selector);
  ixs_node *negative_expected = ixs_sub(ctx, base, selector);
  ixs_node *lookup_expected =
      ixs_add(ctx, base, ixs_mul(ctx, ixs_int(ctx, 16), selector));
  ixs_node *even_expected =
      ixs_add(ctx, base, ixs_mul(ctx, ixs_int(ctx, 16), even_selector));
  ixs_node *threshold_conditions[4];
  ixs_node *threshold_values[4];
  ixs_node *dead_conditions[5];
  ixs_node *dead_values[5];
  ixs_node *wrong_values[4];
  ixs_node *negative_values[4];
  ixs_node *lookup_conditions[5];
  ixs_node *lookup_values[5];
  ixs_node *duplicate_conditions[5];
  ixs_node *duplicate_values[5];
  ixs_node *even_conditions[5];
  ixs_node *even_values[5];
  ixs_node *partial_conditions[2];
  ixs_node *partial_values[2];
  ixs_node *threshold;
  ixs_node *dead_first;
  ixs_node *wrong;
  ixs_node *negative_threshold;
  ixs_node *uncovered;
  ixs_node *lookup;
  ixs_node *duplicate;
  ixs_node *even_lookup;
  ixs_node *partial;
  ixs_node *threshold_equality;
  ixs_node *negative_equality;
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *exact = ixs_facts_create(ctx);
  ixs_facts *huge = ixs_facts_create(ctx);
  ixs_facts *even = ixs_facts_create(ctx);
  size_t errors;
  uint32_t i;

  for (i = 0; i < 3u; i++)
    threshold_conditions[i] =
        ixs_cmp(ctx, selector, IXS_CMP_LT, ixs_int(ctx, (int64_t)i + 1));
  threshold_conditions[3] = ixs_true(ctx);
  for (i = 0; i < 4u; i++)
    threshold_values[i] = ixs_add(ctx, base, ixs_int(ctx, (int64_t)i));
  threshold = ixs_pw(ctx, 4u, threshold_values, threshold_conditions);
  for (i = 0; i < 4u; i++)
    negative_values[i] = ixs_sub(ctx, base, ixs_int(ctx, (int64_t)i));
  negative_threshold = ixs_pw(ctx, 4u, negative_values, threshold_conditions);

  dead_conditions[0] = ixs_cmp(ctx, selector, IXS_CMP_LT, ixs_int(ctx, 0));
  dead_values[0] = ixs_add(ctx, base, ixs_int(ctx, 99));
  for (i = 0; i < 4u; i++) {
    dead_conditions[i + 1u] = threshold_conditions[i];
    dead_values[i + 1u] = threshold_values[i];
    wrong_values[i] = threshold_values[i];
  }
  dead_first = ixs_pw(ctx, 5u, dead_values, dead_conditions);
  wrong_values[2] = ixs_add(ctx, base, ixs_int(ctx, 99));
  wrong = ixs_pw(ctx, 4u, wrong_values, threshold_conditions);
  uncovered = ixs_pw(ctx, 3u, threshold_values, threshold_conditions);

  for (i = 0; i < 4u; i++) {
    lookup_conditions[i] =
        ixs_cmp(ctx, selector, IXS_CMP_EQ, ixs_int(ctx, keys[i]));
    lookup_values[i] = ixs_add(ctx, base, ixs_int(ctx, INT64_C(16) * keys[i]));
    duplicate_conditions[i] =
        ixs_cmp(ctx, selector, IXS_CMP_EQ, ixs_int(ctx, duplicate_keys[i]));
    duplicate_values[i] =
        ixs_add(ctx, base, ixs_int(ctx, INT64_C(16) * duplicate_keys[i]));
    even_conditions[i] =
        ixs_cmp(ctx, ixs_mul(ctx, ixs_int(ctx, 2), even_selector), IXS_CMP_EQ,
                ixs_int(ctx, INT64_C(2) * even_keys[i]));
    even_values[i] =
        ixs_add(ctx, base, ixs_int(ctx, INT64_C(16) * even_keys[i]));
  }
  lookup_conditions[4] = ixs_true(ctx);
  lookup_values[4] = ixs_add(ctx, base, ixs_int(ctx, 99));
  duplicate_conditions[4] = ixs_true(ctx);
  duplicate_values[4] = ixs_add(ctx, base, ixs_int(ctx, 99));
  even_conditions[4] = ixs_true(ctx);
  even_values[4] = ixs_add(ctx, base, ixs_int(ctx, 99));
  lookup = ixs_pw(ctx, 5u, lookup_values, lookup_conditions);
  duplicate = ixs_pw(ctx, 5u, duplicate_values, duplicate_conditions);
  even_lookup = ixs_pw(ctx, 5u, even_values, even_conditions);

  partial_conditions[0] =
      ixs_cmp(ctx, ixs_div(ctx, ixs_int(ctx, 1), partial_divisor), IXS_CMP_GT,
              ixs_int(ctx, 0));
  partial_conditions[1] = ixs_true(ctx);
  partial_values[0] = expected;
  partial_values[1] = expected;
  partial = ixs_pw(ctx, 2u, partial_values, partial_conditions);
  threshold_equality = ixs_cmp(ctx, threshold, IXS_CMP_EQ, expected);
  negative_equality =
      ixs_cmp(ctx, negative_threshold, IXS_CMP_EQ, negative_expected);

  CHECK(ctx && selector && even_selector && base && partial_divisor &&
        expected && negative_expected && lookup_expected && even_expected &&
        threshold && negative_threshold && dead_first && wrong && uncovered &&
        lookup && duplicate && even_lookup && partial && threshold_equality &&
        negative_equality && facts && exact && huge && even);
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, selector, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, selector, IXS_CMP_LE, ixs_int(ctx, 3))));
  CHECK(ixs_facts_assume_pred(
      exact, ixs_cmp(ctx, selector, IXS_CMP_EQ, ixs_int(ctx, 2))));
  CHECK(ixs_facts_assume_pred(
      huge, ixs_cmp(ctx, selector, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      huge, ixs_cmp(ctx, selector, IXS_CMP_LE, ixs_int(ctx, INT64_MAX))));
  CHECK(ixs_facts_assume_pred(
      even, ixs_cmp(ctx, even_selector, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      even, ixs_cmp(ctx, even_selector, IXS_CMP_LE, ixs_int(ctx, 6))));
  CHECK(ixs_facts_assume_pred(
      even, ixs_cmp(ctx, ixs_mod(ctx, even_selector, ixs_int(ctx, 2)),
                    IXS_CMP_EQ, ixs_int(ctx, 0))));

  errors = ixs_ctx_nerrors(ctx);
  CHECK(test_ixs_equivalent_facts(facts, threshold, expected) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, expected, threshold) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(facts, threshold_equality) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_predicate_facts(facts, threshold_equality) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_facts(facts, negative_equality) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, dead_first, expected) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, lookup, lookup_expected) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(even, even_lookup, even_expected) ==
        IXS_CHECK_TRUE);

  CHECK(test_ixs_equivalent_facts(facts, duplicate, lookup_expected) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_facts(huge, lookup, lookup_expected) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_facts(facts, wrong, expected) == IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_facts(exact, wrong, expected) == IXS_CHECK_FALSE);
  CHECK(test_ixs_equivalent_facts(facts, uncovered, expected) ==
        IXS_CHECK_UNKNOWN);
  CHECK(test_ixs_equivalent_facts(facts, partial, expected) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_bounds_equivalence_subproof_limit_probe(
            facts, threshold, expected) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == errors);

  ixs_arena_set_fail_after(&facts->bounds.query_arena, 0);
  CHECK(test_ixs_equivalent_facts(facts, threshold, expected) ==
        IXS_CHECK_UNKNOWN);
  ixs_arena_set_fail_after(&facts->bounds.query_arena,
                           IXS_ARENA_FAILURE_DISABLED);
  CHECK(!facts->bounds.oom);
  CHECK(ixs_ctx_nerrors(ctx) == errors + 1u);
  if (ixs_ctx_nerrors(ctx) != errors)
    CHECK(strstr(ixs_ctx_error(ctx, errors), "out of memory") != NULL);
  ixs_ctx_clear_errors(ctx);
  CHECK(test_ixs_equivalent_facts(facts, threshold, expected) ==
        IXS_CHECK_TRUE);
  CHECK(ixs_ctx_nerrors(ctx) == 0u);

  ixs_ctx_destroy(ctx);
}

int main(void) {
  test_piecewise_partition_equivalence();
  printf("test_piecewise_equivalence: %d/%d passed\n", tests_passed, tests_run);
  return tests_passed == tests_run ? 0 : 1;
}
