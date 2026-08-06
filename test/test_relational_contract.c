/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
/* Public contract witnesses for relational fact propagation. */

#include "test_check.h"
#include <stdint.h>
#include <stdio.h>

#define RELATIONAL_CONTRACT_CHAIN_EDGES 300u
#define RELATIONAL_CONTRACT_CHAIN_NODES (RELATIONAL_CONTRACT_CHAIN_EDGES + 1u)

static bool assume_unit_difference_upper(ixs_ctx *ctx, ixs_facts *facts,
                                         ixs_node *lhs, ixs_node *rhs,
                                         int64_t upper) {
  return ixs_facts_assume_pred(facts, ixs_cmp(ctx, ixs_sub(ctx, lhs, rhs),
                                              IXS_CMP_LE, ixs_int(ctx, upper)));
}

static bool public_ranges_equal(bool lhs_ok, const ixs_range_result *lhs,
                                bool rhs_ok, const ixs_range_result *rhs) {
  if (lhs_ok != rhs_ok)
    return false;
  if (!lhs_ok)
    return true;
  if (lhs->has_lower != rhs->has_lower || lhs->has_upper != rhs->has_upper)
    return false;
  if (lhs->has_lower &&
      (lhs->lower_p != rhs->lower_p || lhs->lower_q != rhs->lower_q))
    return false;
  if (lhs->has_upper &&
      (lhs->upper_p != rhs->upper_p || lhs->upper_q != rhs->upper_q))
    return false;
  return true;
}

static void test_relational_negative_cycle_contract(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "relation_cycle_x");
  ixs_node *y = ixs_sym(ctx, "relation_cycle_y");
  ixs_node *z = ixs_sym(ctx, "relation_cycle_z");
  ixs_node *a = ixs_sym(ctx, "relation_cycle_unrelated");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *x_nonpositive = ixs_cmp(ctx, x, IXS_CMP_LE, zero);
  ixs_node *a_nonnegative = ixs_cmp(ctx, a, IXS_CMP_GE, zero);
  ixs_facts *capability = ixs_facts_create(ctx);
  ixs_facts *cycle = ixs_facts_create(ctx);
  ixs_facts *zero_cycle = ixs_facts_create(ctx);
  ixs_range_result range;
  ixs_check_result relation_support;
  int64_t delta = 0;

  CHECK(assume_unit_difference_upper(ctx, capability, x, y, 0));
  CHECK(ixs_facts_assume_pred(capability, ixs_cmp(ctx, y, IXS_CMP_LE, zero)));
  relation_support = test_ixs_check_facts(capability, x_nonpositive);
  CHECK(relation_support == IXS_CHECK_TRUE);

  CHECK(assume_unit_difference_upper(ctx, cycle, x, y, -1));
  CHECK(assume_unit_difference_upper(ctx, cycle, y, z, 0));
  CHECK(assume_unit_difference_upper(ctx, cycle, z, x, 0));
  CHECK(ixs_facts_assume_pred(cycle, a_nonnegative));

  CHECK(test_ixs_check_facts(cycle, a_nonnegative) == IXS_CHECK_UNKNOWN);
  CHECK(!test_ixs_range_facts(cycle, a, &range));
  CHECK(test_ixs_equivalent_facts(cycle, a, a) == IXS_CHECK_UNKNOWN);
  CHECK(!test_ixs_constant_difference_facts(cycle, a, a, &delta));

  CHECK(assume_unit_difference_upper(ctx, zero_cycle, x, y, -1));
  CHECK(assume_unit_difference_upper(ctx, zero_cycle, y, z, 0));
  CHECK(assume_unit_difference_upper(ctx, zero_cycle, z, x, 1));
  CHECK(ixs_facts_assume_pred(zero_cycle, a_nonnegative));
  CHECK(test_ixs_check_facts(zero_cycle, a_nonnegative) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void make_relational_chain(ixs_ctx *ctx, ixs_node **nodes,
                                  char names[][40]) {
  size_t i;
  for (i = 0; i < RELATIONAL_CONTRACT_CHAIN_NODES; i++) {
    int written = snprintf(names[i], sizeof(names[i]), "relation_chain_%lu",
                           (unsigned long)i);
    CHECK(written > 0 && (size_t)written < sizeof(names[i]));
    nodes[i] = ixs_sym(ctx, names[i]);
    CHECK(nodes[i] != NULL);
  }
}

static void test_relational_chain_insertion_order_contract(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *nodes[RELATIONAL_CONTRACT_CHAIN_NODES];
  char names[RELATIONAL_CONTRACT_CHAIN_NODES][40];
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_facts *late_anchor = ixs_facts_create(ctx);
  ixs_facts *early_anchor = ixs_facts_create(ctx);
  ixs_check_result late_check;
  ixs_check_result early_check;
  ixs_range_result late_range;
  ixs_range_result early_range;
  bool late_range_ok;
  bool early_range_ok;
  size_t i;

  make_relational_chain(ctx, nodes, names);

  for (i = 0; i < RELATIONAL_CONTRACT_CHAIN_EDGES; i++)
    CHECK(assume_unit_difference_upper(ctx, late_anchor, nodes[i],
                                       nodes[i + 1u], 0));
  CHECK(ixs_facts_assume_pred(
      late_anchor,
      ixs_cmp(ctx, nodes[RELATIONAL_CONTRACT_CHAIN_EDGES], IXS_CMP_LE, zero)));

  CHECK(ixs_facts_assume_pred(
      early_anchor,
      ixs_cmp(ctx, nodes[RELATIONAL_CONTRACT_CHAIN_EDGES], IXS_CMP_LE, zero)));
  for (i = RELATIONAL_CONTRACT_CHAIN_EDGES; i > 0; i--)
    CHECK(assume_unit_difference_upper(ctx, early_anchor, nodes[i - 1u],
                                       nodes[i], 0));

  late_check =
      test_ixs_check_facts(late_anchor, ixs_cmp(ctx, nodes[0], IXS_CMP_LE, zero));
  early_check =
      test_ixs_check_facts(early_anchor, ixs_cmp(ctx, nodes[0], IXS_CMP_LE, zero));
  CHECK(late_check == IXS_CHECK_TRUE);
  CHECK(early_check == IXS_CHECK_TRUE);

  late_range_ok = test_ixs_range_facts(late_anchor, nodes[0], &late_range);
  early_range_ok = test_ixs_range_facts(early_anchor, nodes[0], &early_range);
  CHECK(public_ranges_equal(late_range_ok, &late_range, early_range_ok,
                            &early_range));
  CHECK(late_range_ok && late_range.has_upper && late_range.upper_p == 0 &&
        late_range.upper_q == 1);

  ixs_ctx_destroy(ctx);
}

static void test_relational_exact_equality_noise_contract(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "relation_exact_x");
  ixs_node *y = ixs_sym(ctx, "relation_exact_y");
  ixs_node *z = ixs_sym(ctx, "relation_exact_z");
  ixs_node *noise[RELATIONAL_CONTRACT_CHAIN_EDGES];
  char names[RELATIONAL_CONTRACT_CHAIN_EDGES][40];
  ixs_node *difference = ixs_sub(ctx, x, z);
  ixs_facts *base = ixs_facts_create(ctx);
  ixs_facts *loaded = ixs_facts_create(ctx);
  ixs_check_result base_equivalent;
  ixs_check_result loaded_equivalent;
  ixs_range_result base_range;
  ixs_range_result loaded_range;
  int64_t base_delta = 0;
  int64_t loaded_delta = 0;
  bool base_delta_ok;
  bool loaded_delta_ok;
  bool base_range_ok;
  bool loaded_range_ok;
  size_t i;

  CHECK(ixs_facts_assume_pred(base, ixs_cmp(ctx, x, IXS_CMP_EQ, y)));
  CHECK(ixs_facts_assume_pred(base, ixs_cmp(ctx, y, IXS_CMP_EQ, z)));
  CHECK(ixs_facts_assume_pred(loaded, ixs_cmp(ctx, x, IXS_CMP_EQ, y)));
  CHECK(ixs_facts_assume_pred(loaded, ixs_cmp(ctx, y, IXS_CMP_EQ, z)));

  for (i = 0; i < RELATIONAL_CONTRACT_CHAIN_EDGES; i++) {
    int written = snprintf(names[i], sizeof(names[i]), "relation_noise_%lu",
                           (unsigned long)i);
    CHECK(written > 0 && (size_t)written < sizeof(names[i]));
    noise[i] = ixs_sym(ctx, names[i]);
    CHECK(noise[i] != NULL);
    CHECK(
        assume_unit_difference_upper(ctx, loaded, y, noise[i], (int64_t)i + 1));
  }

  base_equivalent = test_ixs_equivalent_facts(base, x, z);
  loaded_equivalent = test_ixs_equivalent_facts(loaded, x, z);
  CHECK(base_equivalent == IXS_CHECK_TRUE);
  CHECK(loaded_equivalent == IXS_CHECK_TRUE);

  base_delta_ok = test_ixs_constant_difference_facts(base, x, z, &base_delta);
  loaded_delta_ok = test_ixs_constant_difference_facts(loaded, x, z, &loaded_delta);
  CHECK(base_delta_ok && base_delta == 0);
  CHECK(loaded_delta_ok && loaded_delta == 0);

  base_range_ok = test_ixs_range_facts(base, difference, &base_range);
  loaded_range_ok = test_ixs_range_facts(loaded, difference, &loaded_range);
  CHECK(base_range_ok && base_range.has_lower && base_range.lower_p == 0 &&
        base_range.lower_q == 1 && base_range.has_upper &&
        base_range.upper_p == 0 && base_range.upper_q == 1);
  CHECK(loaded_range_ok && loaded_range.has_lower &&
        loaded_range.lower_p == 0 && loaded_range.lower_q == 1 &&
        loaded_range.has_upper && loaded_range.upper_p == 0 &&
        loaded_range.upper_q == 1);

  ixs_ctx_destroy(ctx);
}

static void test_relational_loop_bound_production_witness(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *iv = ixs_sym(ctx, "relation_loop_iv");
  ixs_node *trip = ixs_sym(ctx, "relation_loop_trip");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *capability = ixs_facts_create(ctx);
  ixs_range_result range;
  ixs_check_result relation_support;

  CHECK(assume_unit_difference_upper(ctx, capability, iv, trip, 0));
  CHECK(
      ixs_facts_assume_pred(capability, ixs_cmp(ctx, trip, IXS_CMP_LE, zero)));
  relation_support =
      test_ixs_check_facts(capability, ixs_cmp(ctx, iv, IXS_CMP_LE, zero));
  CHECK(relation_support == IXS_CHECK_TRUE);

  CHECK(assume_unit_difference_upper(ctx, facts, iv, trip, -1));
  CHECK(ixs_facts_assume_pred(facts, ixs_cmp(ctx, iv, IXS_CMP_GE, zero)));
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, trip, IXS_CMP_GE, ixs_int(ctx, INT32_MIN))));
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, trip, IXS_CMP_LE, ixs_int(ctx, INT32_MAX))));
  CHECK(test_ixs_range_facts(facts, iv, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == INT64_C(2147483646) &&
        range.upper_q == 1);

  ixs_ctx_destroy(ctx);
}

int main(void) {
  test_relational_negative_cycle_contract();
  test_relational_chain_insertion_order_contract();
  test_relational_exact_equality_noise_contract();
  test_relational_loop_bound_production_witness();

  printf("test_relational_contract: %d/%d passed\n", tests_passed, tests_run);
  return tests_passed == tests_run ? 0 : 1;
}
