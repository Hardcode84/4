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

  late_check = test_ixs_check_facts(late_anchor,
                                    ixs_cmp(ctx, nodes[0], IXS_CMP_LE, zero));
  early_check = test_ixs_check_facts(early_anchor,
                                     ixs_cmp(ctx, nodes[0], IXS_CMP_LE, zero));
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
  loaded_delta_ok =
      test_ixs_constant_difference_facts(loaded, x, z, &loaded_delta);
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

static void test_mapped_predicate_fallback_budget_contract(void) {
  const int64_t points[4] = {0, 1, 2, 3};
  const ixs_mapped_expression_row rows[4] = {
      {0, 0, 0, 0}, {0, 2, 1, 0}, {0, 4, 2, 0}, {0, 6, 3, 0}};
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *item = ixs_sym(ctx, "mapped_contract_item");
  ixs_node *limit = ixs_sym(ctx, "mapped_contract_limit");
  const ixs_node *expressions[1] = {ixs_cmp(ctx, item, IXS_CMP_LT, limit)};
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_finite_domain_result result;
  const ixs_node *candidate;
  size_t budget;

  CHECK(ctx && item && limit && expressions[0] && facts);
  budget = 23;
  result = ixs_synthesize_mapped_expression_facts(facts, item, expressions, 1,
                                                  points, 4, rows, 4, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_EXHAUSTED &&
        result.check == IXS_CHECK_UNKNOWN && result.value == NULL &&
        budget == 7);

  budget = 24;
  result = ixs_synthesize_mapped_expression_facts(facts, item, expressions, 1,
                                                  points, 4, rows, 4, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value != NULL &&
        ixs_node_is_pred(result.value) && budget == 0);
  candidate = result.value;

  budget = 4;
  result = ixs_verify_mapped_expression_facts(facts, item, expressions, 1, rows,
                                              4, candidate, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && result.value == NULL && budget == 0);

  ixs_ctx_destroy(ctx);
}

static void test_mapped_bundle_atomic_contract(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *item = ixs_sym(ctx, "mapped_bundle_contract_item");
  ixs_node *base = ixs_sym(ctx, "mapped_bundle_contract_base");
  const ixs_node *address[1] = {ixs_add(ctx, base, item)};
  const ixs_node *predicate[1] = {
      ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 1))};
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_mapped_bundle_row rows[2] = {{facts, {0, 1, 1, 0}},
                                   {facts, {0, 0, 0, 0}}};
  ixs_mapped_bundle_component components[2] = {
      {IXS_MAPPED_BUNDLE_SCALAR, facts, item, address, 1, rows, 2},
      {IXS_MAPPED_BUNDLE_PREDICATE, facts, item, predicate, 1, rows, 2}};
  const ixs_node *candidates[2] = {base, base};
  ixs_mapped_bundle_result result;
  size_t budget = 12;

  CHECK(ctx && item && base && address[0] && predicate[0] && facts);
  result =
      ixs_synthesize_mapped_bundle_facts(components, 2, candidates, 2, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE &&
        result.check == IXS_CHECK_TRUE && candidates[0] != NULL &&
        candidates[1] != NULL && ixs_node_is_pred(candidates[1]) &&
        budget == 0);

  ixs_ctx_destroy(ctx);
}

static void test_modulo_recurrence_plan_contract(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *i = ixs_sym(ctx, "modulo_plan_i");
  ixs_node *k = ixs_sym(ctx, "modulo_plan_k");
  ixs_node *x = ixs_sym(ctx, "modulo_plan_x");
  ixs_node *y = ixs_sym(ctx, "modulo_plan_y");
  ixs_node *z = ixs_sym(ctx, "modulo_plan_z");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *hundred = ixs_int(ctx, 100);
  ixs_node *successor = ixs_add(ctx, i, one);
  ixs_node *minus_one = ixs_sub(ctx, i, one);
  ixs_facts *loop_facts = ixs_facts_create(ctx);
  ixs_facts *derived_facts = ixs_facts_create(ctx);
  ixs_facts *identity_facts = ixs_facts_create(ctx);
  ixs_modulo_recurrence_reference derived_reference[1] = {{0u, y}};
  ixs_modulo_recurrence_reference identity_reference[1] = {{2u, NULL}};
  ixs_modulo_recurrence_target targets[4];
  ixs_modulo_recurrence_plan_group groups[4];
  ixs_modulo_recurrence_plan_entry entries[4];
  ixs_modulo_recurrence_plan_result result;
  size_t budget;

  CHECK(ctx && i && k && x && y && z && zero && one && hundred && successor &&
        minus_one && loop_facts && derived_facts && identity_facts);
  CHECK(ixs_facts_assume_pred(loop_facts,
                              ixs_cmp(ctx, i, IXS_CMP_GE, ixs_int(ctx, 1))));
  CHECK(
      ixs_facts_assume_pred(loop_facts, ixs_cmp(ctx, i, IXS_CMP_LE, hundred)));
  CHECK(
      ixs_facts_assume_pred(derived_facts, ixs_cmp(ctx, k, IXS_CMP_GE, zero)));
  CHECK(ixs_facts_assume_pred(derived_facts,
                              ixs_cmp(ctx, k, IXS_CMP_LE, hundred)));
  CHECK(
      ixs_facts_assume_pred(derived_facts, ixs_cmp(ctx, x, IXS_CMP_GE, zero)));
  CHECK(ixs_facts_assume_pred(derived_facts,
                              ixs_cmp(ctx, x, IXS_CMP_LE, hundred)));
  CHECK(
      ixs_facts_assume_pred(derived_facts, ixs_cmp(ctx, y, IXS_CMP_GE, zero)));
  CHECK(ixs_facts_assume_pred(derived_facts,
                              ixs_cmp(ctx, y, IXS_CMP_LE, hundred)));
  CHECK(ixs_facts_assume_pred(
      derived_facts,
      ixs_cmp(ctx, ixs_sub(ctx, x, y), IXS_CMP_EQ, ixs_int(ctx, 2))));
  CHECK(
      ixs_facts_assume_pred(identity_facts, ixs_cmp(ctx, k, IXS_CMP_GE, zero)));
  CHECK(ixs_facts_assume_pred(identity_facts,
                              ixs_cmp(ctx, k, IXS_CMP_LE, hundred)));
  CHECK(
      ixs_facts_assume_pred(identity_facts, ixs_cmp(ctx, z, IXS_CMP_GE, zero)));

  targets[0] = (ixs_modulo_recurrence_target){
      loop_facts, i, i, NULL, 0u, IXS_REMAINDER_SIGNED, 5u};
  targets[1] = (ixs_modulo_recurrence_target){
      loop_facts,           minus_one,           i, NULL, 0u,
      IXS_REMAINDER_SIGNED, UINT64_C(4294967291)};
  targets[2] = (ixs_modulo_recurrence_target){
      derived_facts, x, k, derived_reference, 1u, IXS_REMAINDER_SIGNED, 5u};
  targets[3] = (ixs_modulo_recurrence_target){
      identity_facts, z, k, identity_reference, 1u, IXS_REMAINDER_SIGNED, 5u};

  budget = 10u;
  result = ixs_plan_modulo_recurrences_facts(loop_facts, successor, i, i, 32u,
                                             targets, 4u, groups, 4u, entries,
                                             4u, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE && result.ngroups == 1u &&
        budget == 0u);
  CHECK(groups[0].signedness == IXS_REMAINDER_SIGNED &&
        groups[0].divisor == 5u && groups[0].successor_increment == 1u &&
        groups[0].remainder != NULL);
  CHECK(entries[0].group_index == 0u && entries[0].increment == 0u);
  CHECK(entries[1].group_index == 0u && entries[1].increment == 4u);
  CHECK(entries[2].group_index == 0u && entries[2].increment == 2u);
  CHECK(entries[3].group_index == 0u && entries[3].increment == 2u);

  groups[0].divisor = 99u;
  entries[0].group_index = 0u;
  budget = 9u;
  result = ixs_plan_modulo_recurrences_facts(loop_facts, successor, i, i, 32u,
                                             targets, 4u, groups, 4u, entries,
                                             4u, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_EXHAUSTED && result.ngroups == 0u &&
        budget == 9u && groups[0].divisor == 0u &&
        entries[0].group_index == SIZE_MAX && entries[0].increment == 0u);

  ixs_ctx_destroy(ctx);
}

static void test_modulo_recurrence_plan_fixed_width_contract(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *current = ixs_int(ctx, INT32_MAX);
  ixs_node *successor = ixs_int(ctx, INT32_MIN);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_modulo_recurrence_target target = {
      facts, current, current, NULL, 0u, IXS_REMAINDER_UNSIGNED, 5u};
  ixs_modulo_recurrence_plan_group group;
  ixs_modulo_recurrence_plan_entry entry;
  ixs_modulo_recurrence_plan_result result;
  size_t budget = 2u;

  CHECK(ctx && current && successor && facts);
  result = ixs_plan_modulo_recurrences_facts(facts, successor, current, current,
                                             32u, &target, 1u, &group, 1u,
                                             &entry, 1u, &budget);
  CHECK(result.status == IXS_FINITE_DOMAIN_COMPLETE && result.ngroups == 1u &&
        budget == 0u && group.successor_increment == 1u &&
        group.divisor == 5u && entry.group_index == 0u &&
        entry.increment == 0u);

  ixs_ctx_destroy(ctx);
}

int main(void) {
  test_relational_negative_cycle_contract();
  test_relational_chain_insertion_order_contract();
  test_relational_exact_equality_noise_contract();
  test_relational_loop_bound_production_witness();
  test_mapped_predicate_fallback_budget_contract();
  test_mapped_bundle_atomic_contract();
  test_modulo_recurrence_plan_contract();
  test_modulo_recurrence_plan_fixed_width_contract();

  printf("test_relational_contract: %d/%d passed\n", tests_passed, tests_run);
  return tests_passed == tests_run ? 0 : 1;
}
