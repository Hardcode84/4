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

static ixs_range_result closed_integer_range(int64_t lower, int64_t upper) {
  ixs_range_result range = {true, true, lower, 1, upper, 1};
  return range;
}

static void check_closed_integer_range(ixs_facts *facts, ixs_node *expr,
                                       int64_t lower, int64_t upper) {
  ixs_range_result range;
  CHECK(test_ixs_range_facts(facts, expr, &range));
  CHECK(range.has_lower && range.lower_p == lower && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == upper && range.upper_q == 1);
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

static void test_relational_mod_quotient_identity(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *item = ixs_sym(ctx, "relation_mod_item");
  ixs_node *rank = ixs_sym(ctx, "relation_mod_rank");
  ixs_node *flat = ixs_mul(ctx, ixs_int(ctx, 8), item);
  ixs_node *mod = ixs_mod(ctx, flat, ixs_int(ctx, 64));
  ixs_node *quotient = ixs_floor(ctx, ixs_div(ctx, flat, ixs_int(ctx, 64)));
  ixs_node *observed =
      ixs_mul(ctx, ixs_int(ctx, 2),
              ixs_add(ctx, mod, ixs_mul(ctx, ixs_int(ctx, 64), rank)));
  ixs_node *expected = ixs_mul(ctx, ixs_int(ctx, 2), flat);
  ixs_node *equality = ixs_cmp(ctx, observed, IXS_CMP_EQ, expected);
  ixs_facts *facts = ixs_facts_create(ctx);

  CHECK(ctx && item && rank && flat && mod && quotient && observed &&
        expected && equality && facts);
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, item, IXS_CMP_LE, ixs_int(ctx, 63))));
  CHECK(ixs_facts_assume_pred(facts, ixs_cmp(ctx, quotient, IXS_CMP_EQ, rank)));
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, rank, IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(test_ixs_equivalent_facts(facts, mod, flat) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, observed, expected) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_predicate_facts(facts, equality) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_relational_cyclic_xor_recurrence(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *i = ixs_sym(ctx, "relation_cyclic_i");
  ixs_node *a = ixs_sym(ctx, "relation_cyclic_a");
  ixs_node *b = ixs_sym(ctx, "relation_cyclic_b");
  ixs_node *c = ixs_sym(ctx, "relation_cyclic_c");
  ixs_node *x = ixs_xor(
      ctx,
      ixs_xor(ctx,
              ixs_add(ctx, ixs_int(ctx, 32), ixs_mul(ctx, ixs_int(ctx, 4), b)),
              ixs_mul(ctx, ixs_int(ctx, 8), c)),
      ixs_mul(ctx, ixs_int(ctx, 16), a));
  ixs_node *e = ixs_add(
      ctx, ixs_mul(ctx, ixs_int(ctx, 8192), ixs_mod(ctx, i, ixs_int(ctx, 4))),
      x);
  ixs_node *next =
      (ixs_node *)ixs_subs(ctx, e, i, ixs_add(ctx, i, ixs_int(ctx, 1)));
  ixs_node *wrapped =
      ixs_mod(ctx, ixs_add(ctx, e, ixs_int(ctx, 8192)), ixs_int(ctx, 32768));
  ixs_node *equality = ixs_cmp(ctx, next, IXS_CMP_EQ, wrapped);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_node *symbols[4] = {i, a, b, c};
  int64_t uppers[4] = {7, 1, 1, 1};
  size_t index;

  CHECK(ctx && i && a && b && c && x && e && next && wrapped && equality &&
        facts);
  for (index = 0; index < 4; index++) {
    CHECK(ixs_facts_assume_pred(
        facts, ixs_cmp(ctx, symbols[index], IXS_CMP_GE, ixs_int(ctx, 0))));
    CHECK(ixs_facts_assume_pred(facts, ixs_cmp(ctx, symbols[index], IXS_CMP_LE,
                                               ixs_int(ctx, uppers[index]))));
  }
  CHECK(test_ixs_check_integer_valued_facts(facts, x) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_predicate_facts(
            facts, ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0))) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_predicate_facts(
            facts, ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 8192))) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(
            facts,
            ixs_mod(ctx, ixs_add(ctx, i, ixs_int(ctx, 1)), ixs_int(ctx, 4)),
            ixs_mod(
                ctx,
                ixs_add(ctx, ixs_mod(ctx, i, ixs_int(ctx, 4)), ixs_int(ctx, 1)),
                ixs_int(ctx, 4))) == IXS_CHECK_TRUE);
  CHECK(test_ixs_equivalent_facts(facts, next, wrapped) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_predicate_facts(facts, equality) == IXS_CHECK_TRUE);

  {
    ixs_node *next_mod =
        ixs_mod(ctx, ixs_add(ctx, i, ixs_int(ctx, 1)), ixs_int(ctx, 4));
    ixs_node *wrapped_quotient =
        ixs_add(ctx, ixs_mod(ctx, i, ixs_int(ctx, 4)), ixs_int(ctx, 1));
    ixs_node *lhs_residuals[4] = {ixs_int(ctx, -1), ixs_int(ctx, 8192),
                                  ixs_rat(ctx, 1, 2), ixs_int(ctx, 32)};
    ixs_node *rhs_residuals[4] = {ixs_int(ctx, -1), ixs_int(ctx, 8192),
                                  ixs_rat(ctx, 1, 2), ixs_int(ctx, 33)};

    for (index = 0; index < 4; index++) {
      ixs_node *guard_lhs = ixs_add(ctx, lhs_residuals[index],
                                    ixs_mul(ctx, ixs_int(ctx, 8192), next_mod));
      ixs_node *guard_rhs =
          ixs_mod(ctx,
                  ixs_add(ctx, rhs_residuals[index],
                          ixs_mul(ctx, ixs_int(ctx, 8192), wrapped_quotient)),
                  ixs_int(ctx, 32768));
      CHECK(test_ixs_equivalent_facts(facts, guard_lhs, guard_rhs) !=
            IXS_CHECK_TRUE);
    }
  }

  ixs_ctx_destroy(ctx);
}

static void test_relational_mod_quotient_order(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *item = ixs_sym(ctx, "relation_mod_order_item");
  ixs_node *multiple = ixs_sub(ctx, item, ixs_mod(ctx, item, ixs_int(ctx, 64)));
  ixs_node *nonnegative = ixs_cmp(ctx, multiple, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_facts *bounded = ixs_facts_create(ctx);
  ixs_facts *upper_only = ixs_facts_create(ctx);

  CHECK(ctx && item && multiple && nonnegative && bounded && upper_only);
  CHECK(ixs_facts_assume_pred(bounded,
                              ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      bounded, ixs_cmp(ctx, item, IXS_CMP_LE, ixs_int(ctx, 255))));
  CHECK(test_ixs_check_predicate_facts(bounded, nonnegative) == IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(
      upper_only, ixs_cmp(ctx, item, IXS_CMP_LE, ixs_int(ctx, 255))));
  CHECK(test_ixs_check_predicate_facts(upper_only, nonnegative) ==
        IXS_CHECK_UNKNOWN);

  ixs_ctx_destroy(ctx);
}

static void test_relational_equivalence_probe_guards(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "relation_probe_x");
  ixs_node *scaled =
      ixs_mul(ctx, ixs_int(ctx, INT64_MAX), ixs_mod(ctx, x, ixs_int(ctx, 2)));
  ixs_facts *facts = ixs_facts_create(ctx);
  size_t errors = ixs_ctx_nerrors(ctx);

  CHECK(ctx && x && scaled && facts);
  CHECK(test_ixs_equivalent_facts(facts, scaled, ixs_int(ctx, 0)) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == errors);
  CHECK(test_ixs_check_predicate_facts(
            facts, ixs_cmp(ctx, scaled, IXS_CMP_EQ, ixs_int(ctx, 0))) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == errors);
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(test_ixs_equivalent_facts(facts, scaled, ixs_int(ctx, 0)) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == errors);
  CHECK(test_ixs_check_predicate_facts(
            facts, ixs_cmp(ctx, scaled, IXS_CMP_NE, ixs_int(ctx, 0))) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == errors);

  ixs_ctx_destroy(ctx);
}

static void test_relational_totality_predicate_contract(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "relation_totality_x");
  ixs_node *modulus = ixs_sym(ctx, "relation_totality_modulus");
  ixs_node *mod = ixs_mod(ctx, x, modulus);
  ixs_node *total = ixs_cmp(ctx, mod, IXS_CMP_EQ, mod);
  ixs_facts *negative = ixs_facts_create(ctx);
  ixs_facts *positive = ixs_facts_create(ctx);
  size_t errors;

  CHECK(ctx && x && modulus && mod && total && negative && positive);
  CHECK(ixs_facts_assume_pred(
      negative, ixs_cmp(ctx, modulus, IXS_CMP_LT, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      positive, ixs_cmp(ctx, modulus, IXS_CMP_GT, ixs_int(ctx, 0))));

  ixs_ctx_clear_errors(ctx);
  errors = ixs_ctx_nerrors(ctx);
  CHECK(test_ixs_check_predicate_facts(negative, total) == IXS_CHECK_FALSE);
  CHECK(ixs_ctx_nerrors(ctx) == errors);
  CHECK(test_ixs_check_predicate_facts(positive, total) == IXS_CHECK_TRUE);
  CHECK(ixs_ctx_nerrors(ctx) == errors);

  ixs_ctx_destroy(ctx);
}

static void check_unknown_equivalence_without_diagnostic(ixs_ctx *ctx,
                                                         ixs_facts *facts,
                                                         ixs_node *lhs,
                                                         ixs_node *rhs) {
  size_t errors;
  CHECK(ctx && facts && lhs && rhs && !ixs_is_error(lhs) && !ixs_is_error(rhs));
  ixs_ctx_clear_errors(ctx);
  errors = ixs_ctx_nerrors(ctx);
  CHECK(test_ixs_equivalent_facts(facts, lhs, rhs) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == errors);
}

static void test_relational_optional_proof_extrema(void) {
  const int64_t large_q = INT64_C(3037000500);
  const int64_t large_r = INT64_C(3037000501);
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *zero = ixs_int(ctx, 0);

  CHECK(ctx && zero);
  {
    ixs_node *x = ixs_sym(ctx, "relation_extreme_integer_sum_x");
    ixs_node *lhs = ixs_add(ctx,
                            ixs_mul(ctx, ixs_int(ctx, INT64_MAX / 2),
                                    ixs_mod(ctx, x, ixs_int(ctx, 2))),
                            ixs_mul(ctx, ixs_int(ctx, INT64_MAX), x));
    check_unknown_equivalence_without_diagnostic(ctx, ixs_facts_create(ctx),
                                                 lhs, zero);
  }
  {
    ixs_node *x = ixs_sym(ctx, "relation_extreme_integer_sum_negative_x");
    ixs_node *lhs = ixs_add(ctx,
                            ixs_mul(ctx, ixs_int(ctx, -(INT64_MAX / 2)),
                                    ixs_mod(ctx, x, ixs_int(ctx, 2))),
                            ixs_mul(ctx, ixs_int(ctx, INT64_MIN), x));
    check_unknown_equivalence_without_diagnostic(ctx, ixs_facts_create(ctx),
                                                 lhs, zero);
  }
  {
    ixs_node *x = ixs_sym(ctx, "relation_extreme_rational_sum_x");
    ixs_node *lhs = ixs_add(ctx,
                            ixs_mul(ctx, ixs_rat(ctx, 1, large_q),
                                    ixs_mod(ctx, x, ixs_int(ctx, large_q))),
                            ixs_mul(ctx, ixs_rat(ctx, 1, large_r), x));
    check_unknown_equivalence_without_diagnostic(ctx, ixs_facts_create(ctx),
                                                 lhs, zero);
  }
  {
    ixs_node *x = ixs_sym(ctx, "relation_extreme_quotient_argument_x");
    ixs_node *dividend = ixs_div(ctx, x, ixs_int(ctx, INT64_MAX));
    ixs_node *lhs =
        ixs_add(ctx, ixs_mod(ctx, dividend, ixs_int(ctx, 2)),
                ixs_sym(ctx, "relation_extreme_quotient_argument_rest"));
    ixs_facts *facts = ixs_facts_create(ctx);
    CHECK(ixs_facts_assume_pred(
        facts, ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, INT64_MAX)),
                       IXS_CMP_EQ, zero)));
    check_unknown_equivalence_without_diagnostic(ctx, facts, lhs, zero);
  }
  {
    ixs_node *x = ixs_sym(ctx, "relation_extreme_scaled_dividend_x");
    ixs_node *y = ixs_sym(ctx, "relation_extreme_scaled_dividend_y");
    ixs_node *dividend = ixs_div(ctx, x, ixs_int(ctx, INT64_MAX));
    ixs_node *lhs =
        ixs_mul(ctx, ixs_int(ctx, 2), ixs_mod(ctx, y, ixs_int(ctx, 2)));
    ixs_node *rhs = ixs_mod(ctx, dividend, ixs_int(ctx, 4));
    ixs_facts *facts = ixs_facts_create(ctx);
    CHECK(ixs_facts_assume_pred(
        facts, ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, INT64_MAX)),
                       IXS_CMP_EQ, zero)));
    check_unknown_equivalence_without_diagnostic(ctx, facts, lhs, rhs);
  }
  {
    ixs_node *x = ixs_sym(ctx, "relation_extreme_quotient_parts_x");
    ixs_node *lhs = ixs_trunc(ctx, ixs_add(ctx, ixs_int(ctx, INT64_MAX),
                                           ixs_div(ctx, x, ixs_int(ctx, 2))));
    check_unknown_equivalence_without_diagnostic(
        ctx, ixs_facts_create(ctx), lhs,
        ixs_sym(ctx, "relation_extreme_quotient_parts_other"));
  }
  {
    ixs_node *d = ixs_sym(ctx, "relation_extreme_signed_positive_d");
    ixs_node *lhs = ixs_trunc(ctx, ixs_div(ctx, ixs_int(ctx, INT64_MIN), d));
    ixs_facts *facts = ixs_facts_create(ctx);
    CHECK(ixs_facts_assume_pred(facts,
                                ixs_cmp(ctx, d, IXS_CMP_GE, ixs_int(ctx, 1))));
    CHECK(ixs_facts_assume_pred(facts,
                                ixs_cmp(ctx, d, IXS_CMP_LE, ixs_int(ctx, 7))));
    check_unknown_equivalence_without_diagnostic(
        ctx, facts, lhs, ixs_sym(ctx, "relation_extreme_signed_other"));
  }
  {
    ixs_node *d = ixs_sym(ctx, "relation_extreme_signed_negative_d");
    ixs_node *lhs = ixs_trunc(ctx, ixs_div(ctx, ixs_int(ctx, INT64_MIN), d));
    ixs_facts *facts = ixs_facts_create(ctx);
    CHECK(ixs_facts_assume_pred(facts,
                                ixs_cmp(ctx, d, IXS_CMP_GE, ixs_int(ctx, -7))));
    CHECK(ixs_facts_assume_pred(facts,
                                ixs_cmp(ctx, d, IXS_CMP_LE, ixs_int(ctx, -1))));
    check_unknown_equivalence_without_diagnostic(
        ctx, facts, lhs,
        ixs_sym(ctx, "relation_extreme_signed_negative_other"));
  }
  {
    ixs_node *x = ixs_sym(ctx, "relation_extreme_piecewise_x");
    ixs_node *argument = ixs_div(ctx, x, ixs_int(ctx, large_q));
    ixs_node *residual = ixs_div(ctx, x, ixs_int(ctx, large_r));
    ixs_node *values[2] = {ixs_add(ctx, ixs_floor(ctx, argument), residual),
                           ixs_add(ctx, ixs_ceil(ctx, argument), residual)};
    ixs_node *conditions[2] = {ixs_cmp(ctx, x, IXS_CMP_GE, zero),
                               ixs_true(ctx)};
    ixs_node *lhs = ixs_pw(ctx, 2, values, conditions);
    ixs_facts *facts = ixs_facts_create(ctx);
    CHECK(ixs_facts_assume_pred(
        facts, ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, large_r)), IXS_CMP_EQ,
                       zero)));
    check_unknown_equivalence_without_diagnostic(
        ctx, facts, lhs, ixs_sym(ctx, "relation_extreme_piecewise_other"));
  }

  ixs_ctx_destroy(ctx);
}

static void test_relational_inverse_range_guards(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "relation_inverse_x");
  ixs_node *y = ixs_sym(ctx, "relation_inverse_y");
  ixs_node *item = ixs_sym(ctx, "relation_inverse_item");
  ixs_node *mod_x = ixs_mod(ctx, x, ixs_int(ctx, 16));
  ixs_node *mod_y = ixs_mod(ctx, y, ixs_int(ctx, 16));
  ixs_node *selector = ixs_floor(ctx, ixs_div(ctx, item, ixs_int(ctx, 8)));
  ixs_node *negative_selector =
      ixs_floor(ctx, ixs_div(ctx, item, ixs_int(ctx, -8)));
  ixs_facts *ambiguous = ixs_facts_create(ctx);
  ixs_facts *unbounded = ixs_facts_create(ctx);
  ixs_facts *floor_first = ixs_facts_create(ctx);
  ixs_facts *range_first = ixs_facts_create(ctx);
  ixs_facts *negative_denominator = ixs_facts_create(ctx);
  ixs_facts *u32_reversed = ixs_facts_create(ctx);
  ixs_node *u32 = ixs_mod(ctx, x, ixs_int(ctx, INT64_C(4294967296)));

  CHECK(ctx && x && y && item && mod_x && mod_y && selector &&
        negative_selector && ambiguous && unbounded && floor_first &&
        range_first && negative_denominator && u32_reversed && u32);

  CHECK(ixs_facts_assume_pred(ambiguous,
                              ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, -8))));
  CHECK(ixs_facts_assume_pred(ambiguous,
                              ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 8))));
  CHECK(ixs_facts_assume_pred(
      ambiguous, ixs_cmp(ctx, mod_x, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      ambiguous, ixs_cmp(ctx, mod_x, IXS_CMP_LE, ixs_int(ctx, 8))));
  CHECK(test_ixs_check_predicate_facts(
            ambiguous, ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0))) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(
      unbounded, ixs_cmp(ctx, mod_y, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      unbounded, ixs_cmp(ctx, mod_y, IXS_CMP_LE, ixs_int(ctx, 3))));
  CHECK(test_ixs_check_predicate_facts(
            unbounded, ixs_cmp(ctx, y, IXS_CMP_GE, ixs_int(ctx, 0))) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(
      floor_first, ixs_cmp(ctx, selector, IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      floor_first, ixs_cmp(ctx, item, IXS_CMP_LE, ixs_int(ctx, 63))));
  CHECK(ixs_facts_assume_pred(
      range_first, ixs_cmp(ctx, item, IXS_CMP_LE, ixs_int(ctx, 63))));
  CHECK(ixs_facts_assume_pred(
      range_first, ixs_cmp(ctx, selector, IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(test_ixs_check_predicate_facts(
            floor_first, ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 0))) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_predicate_facts(
            floor_first, ixs_cmp(ctx, item, IXS_CMP_LE, ixs_int(ctx, 7))) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_predicate_facts(
            range_first, ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 0))) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_predicate_facts(
            range_first, ixs_cmp(ctx, item, IXS_CMP_LE, ixs_int(ctx, 7))) ==
        IXS_CHECK_TRUE);

  CHECK(ixs_facts_assume_pred(
      negative_denominator, ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, -63))));
  CHECK(ixs_facts_assume_pred(
      negative_denominator, ixs_cmp(ctx, item, IXS_CMP_LE, ixs_int(ctx, 63))));
  CHECK(ixs_facts_assume_pred(
      negative_denominator,
      ixs_cmp(ctx, negative_selector, IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(test_ixs_check_predicate_facts(
            negative_denominator,
            ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 0))) ==
        IXS_CHECK_UNKNOWN);

  CHECK(ixs_facts_assume_pred(u32_reversed,
                              ixs_cmp(ctx, u32, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(u32_reversed,
                              ixs_cmp(ctx, u32, IXS_CMP_LT, ixs_int(ctx, 42))));
  CHECK(ixs_facts_assume_pred(
      u32_reversed,
      ixs_cmp(ctx, ixs_add(ctx, ixs_int(ctx, INT64_C(2147483648)), x),
              IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      u32_reversed,
      ixs_cmp(ctx, ixs_add(ctx, ixs_int(ctx, INT64_C(-2147483647)), x),
              IXS_CMP_LE, ixs_int(ctx, 0))));
  CHECK(test_ixs_check_predicate_facts(
            u32_reversed, ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0))) ==
        IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_relational_inverse_watchers_public_contract(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "relation_inverse_watch_x");
  ixs_node *y = ixs_sym(ctx, "relation_inverse_watch_y");
  ixs_node *mod8 = ixs_mod(ctx, x, ixs_int(ctx, 8));
  ixs_node *mod16 = ixs_mod(ctx, x, ixs_int(ctx, 16));
  ixs_node *twice_mod8 = ixs_mul(ctx, ixs_int(ctx, 2), mod8);
  ixs_node *floor8 = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 8)));
  ixs_range_result positive = closed_integer_range(0, 7);
  ixs_range_result negative = closed_integer_range(-7, -1);
  ixs_range_result broad = closed_integer_range(-63, 63);
  ixs_range_result residue3 = closed_integer_range(3, 3);
  ixs_range_result residue0_to7 = closed_integer_range(0, 7);
  ixs_range_result twice_residue = closed_integer_range(6, 6);
  ixs_range_result floor_zero = closed_integer_range(0, 0);
  ixs_range_result floor_negative_one = closed_integer_range(-1, -1);
  ixs_facts *positive_mod_first = ixs_facts_create(ctx);
  ixs_facts *positive_range_first = ixs_facts_create(ctx);
  ixs_facts *negative_mod_first = ixs_facts_create(ctx);
  ixs_facts *negative_range_first = ixs_facts_create(ctx);
  ixs_facts *fixed_forward = ixs_facts_create(ctx);
  ixs_facts *fixed_reverse = ixs_facts_create(ctx);
  ixs_facts *proportional = ixs_facts_create(ctx);
  ixs_facts *floor_positive_first = ixs_facts_create(ctx);
  ixs_facts *range_positive_first = ixs_facts_create(ctx);
  ixs_facts *floor_negative_first = ixs_facts_create(ctx);
  ixs_facts *range_negative_first = ixs_facts_create(ctx);
  ixs_facts *mod_then_floor = ixs_facts_create(ctx);
  ixs_facts *floor_then_mod = ixs_facts_create(ctx);
  ixs_facts *source = ixs_facts_create(ctx);
  ixs_facts *substituted = ixs_facts_create(ctx);

  CHECK(ctx && x && y && mod8 && mod16 && twice_mod8 && floor8 &&
        positive_mod_first && positive_range_first && negative_mod_first &&
        negative_range_first && fixed_forward && fixed_reverse &&
        proportional && floor_positive_first && range_positive_first &&
        floor_negative_first && range_negative_first && mod_then_floor &&
        floor_then_mod && source && substituted);

  CHECK(ixs_facts_assume_range(positive_mod_first, mod8, &residue3));
  CHECK(ixs_facts_assume_range(positive_mod_first, x, &positive));
  check_closed_integer_range(positive_mod_first, x, 3, 3);
  CHECK(ixs_facts_assume_range(positive_range_first, x, &positive));
  CHECK(ixs_facts_assume_range(positive_range_first, mod8, &residue3));
  check_closed_integer_range(positive_range_first, x, 3, 3);

  CHECK(ixs_facts_assume_range(negative_mod_first, mod8, &residue3));
  CHECK(ixs_facts_assume_range(negative_mod_first, x, &negative));
  check_closed_integer_range(negative_mod_first, x, -5, -5);
  CHECK(ixs_facts_assume_range(negative_range_first, x, &negative));
  CHECK(ixs_facts_assume_range(negative_range_first, mod8, &residue3));
  check_closed_integer_range(negative_range_first, x, -5, -5);

  CHECK(ixs_facts_assume_range(fixed_forward, mod8, &residue3));
  CHECK(ixs_facts_assume_range(fixed_forward, mod16, &residue0_to7));
  CHECK(ixs_facts_assume_range(fixed_forward, x,
                               &(ixs_range_result){true, true, -7, 1, 7, 1}));
  check_closed_integer_range(fixed_forward, x, 3, 3);
  CHECK(ixs_facts_assume_range(fixed_reverse, mod16, &residue0_to7));
  CHECK(ixs_facts_assume_range(fixed_reverse, mod8, &residue3));
  CHECK(ixs_facts_assume_range(fixed_reverse, x,
                               &(ixs_range_result){true, true, -7, 1, 7, 1}));
  check_closed_integer_range(fixed_reverse, x, 3, 3);

  CHECK(ixs_facts_assume_range(proportional, twice_mod8, &twice_residue));
  CHECK(ixs_facts_assume_range(proportional, x, &positive));
  check_closed_integer_range(proportional, x, 3, 3);

  CHECK(ixs_facts_assume_range(floor_positive_first, floor8, &floor_zero));
  CHECK(ixs_facts_assume_range(floor_positive_first, x, &broad));
  check_closed_integer_range(floor_positive_first, x, 0, 7);
  CHECK(ixs_facts_assume_range(range_positive_first, x, &broad));
  CHECK(ixs_facts_assume_range(range_positive_first, floor8, &floor_zero));
  check_closed_integer_range(range_positive_first, x, 0, 7);
  CHECK(ixs_facts_assume_range(floor_negative_first, floor8,
                               &floor_negative_one));
  CHECK(ixs_facts_assume_range(floor_negative_first, x, &broad));
  check_closed_integer_range(floor_negative_first, x, -8, -1);
  CHECK(ixs_facts_assume_range(range_negative_first, x, &broad));
  CHECK(ixs_facts_assume_range(range_negative_first, floor8,
                               &floor_negative_one));
  check_closed_integer_range(range_negative_first, x, -8, -1);

  CHECK(ixs_facts_assume_range(mod_then_floor, x, &broad));
  CHECK(ixs_facts_assume_range(mod_then_floor, mod8, &residue3));
  CHECK(ixs_facts_assume_range(mod_then_floor, floor8, &floor_zero));
  check_closed_integer_range(mod_then_floor, x, 3, 3);
  CHECK(ixs_facts_assume_range(floor_then_mod, x, &broad));
  CHECK(ixs_facts_assume_range(floor_then_mod, floor8, &floor_zero));
  CHECK(ixs_facts_assume_range(floor_then_mod, mod8, &residue3));
  check_closed_integer_range(floor_then_mod, x, 3, 3);

  CHECK(ixs_facts_assume_range(source, mod8, &residue3));
  CHECK(ixs_facts_substitute(substituted, source, x, y));
  CHECK(ixs_facts_assume_range(substituted, y, &positive));
  check_closed_integer_range(substituted, y, 3, 3);
  CHECK(ixs_facts_assume_range(source, x, &positive));
  check_closed_integer_range(source, x, 3, 3);

  ixs_ctx_destroy(ctx);
}

static void test_relational_substituted_congruence_range_contract(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "relation_substituted_range_x");
  ixs_node *y = ixs_sym(ctx, "relation_substituted_range_y");
  ixs_node *mod4 = ixs_mod(ctx, x, ixs_int(ctx, 4));
  ixs_range_result bounded = closed_integer_range(0, 31);
  ixs_facts *source = ixs_facts_create(ctx);
  ixs_facts *substituted = ixs_facts_create(ctx);

  CHECK(ctx && x && y && mod4 && source && substituted);
  CHECK(ixs_facts_assume_range(source, x, &bounded));
  CHECK(ixs_facts_assume_pred(source,
                              ixs_cmp(ctx, mod4, IXS_CMP_EQ, ixs_int(ctx, 0))));
  CHECK(ixs_facts_substitute(substituted, source, x, y));
  check_closed_integer_range(substituted, y, 0, 28);
  CHECK(test_ixs_check_congruent_facts(substituted, y, 4, 0) == IXS_CHECK_TRUE);

  ixs_ctx_destroy(ctx);
}

static void test_relational_numeric_piecewise_equality_contract(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "relation_numeric_piecewise_x");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *two = ixs_int(ctx, 2);
  ixs_node *half = ixs_rat(ctx, 1, 2);
  ixs_node *condition = ixs_cmp(ctx, x, IXS_CMP_EQ, zero);
  ixs_node *values[2] = {half, zero};
  ixs_node *conditions[2] = {condition, ixs_true(ctx)};
  ixs_node *selector = ixs_pw(ctx, 2, values, conditions);
  ixs_node *expr = ixs_add(ctx, ixs_mul(ctx, half, x), selector);
  ixs_node *scaled = ixs_mul(ctx, two, expr);
  ixs_node *candidate = ixs_add(ctx, x, condition);
  ixs_node *equality = ixs_cmp(ctx, scaled, IXS_CMP_EQ, candidate);
  ixs_node *candidate_defined = ixs_cmp(ctx, candidate, IXS_CMP_EQ, candidate);
  ixs_node *candidate_integer =
      ixs_cmp(ctx, candidate, IXS_CMP_EQ, ixs_floor(ctx, candidate));
  ixs_node *carrier_valid = ixs_and(
      ctx, ixs_and(ctx, candidate_defined, candidate_integer), equality);
  ixs_node *range_lower =
      ixs_cmp(ctx, candidate, IXS_CMP_GE, ixs_int(ctx, INT64_MIN));
  ixs_node *range_upper =
      ixs_cmp(ctx, candidate, IXS_CMP_LE, ixs_int(ctx, INT64_MAX));
  ixs_node *range_valid = ixs_and(ctx, range_lower, range_upper);
  ixs_range_result bounded = closed_integer_range(0, INT64_C(1099511627775));
  ixs_facts *facts = ixs_facts_create(ctx);
  size_t errors = ixs_ctx_nerrors(ctx);

  CHECK(ctx && x && zero && two && half && condition && selector && expr &&
        scaled && candidate && equality && candidate_defined &&
        candidate_integer && carrier_valid && range_lower && range_upper &&
        range_valid && facts);
  CHECK(ixs_facts_assume_range(facts, x, &bounded));
  CHECK(test_ixs_check_predicate_facts(facts, carrier_valid) == IXS_CHECK_TRUE);
  check_closed_integer_range(facts, condition, 0, 1);
  CHECK(test_ixs_check_predicate_facts(facts, range_valid) == IXS_CHECK_TRUE);
  CHECK(ixs_ctx_nerrors(ctx) == errors);

  ixs_ctx_destroy(ctx);
}

static void test_relational_numeric_boolean_equality_contract(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *origin = ixs_sym(ctx, "relation_boolean_origin");
  ixs_node *limit = ixs_sym(ctx, "relation_boolean_limit");
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *difference = ixs_sub(ctx, origin, limit);
  ixs_node *left = ixs_cmp(ctx, difference, IXS_CMP_LT, zero);
  ixs_node *right =
      ixs_cmp(ctx, ixs_add(ctx, ixs_int(ctx, 1), difference), IXS_CMP_LT, zero);
  ixs_node *equality = ixs_cmp(ctx, left, IXS_CMP_EQ, right);
  ixs_range_result signed_i32 = closed_integer_range(INT32_MIN, INT32_MAX);
  ixs_facts *facts = ixs_facts_create(ctx);
  size_t errors = ixs_ctx_nerrors(ctx);

  CHECK(ctx && origin && limit && zero && difference && left && right &&
        equality && facts);
  CHECK(ixs_facts_assume_range(facts, origin, &signed_i32));
  CHECK(ixs_facts_assume_range(facts, limit, &signed_i32));
  CHECK(ixs_facts_assume_pred(
      facts,
      ixs_cmp(ctx, ixs_mod(ctx, origin, ixs_int(ctx, 4)), IXS_CMP_EQ, zero)));
  CHECK(ixs_facts_assume_pred(
      facts,
      ixs_cmp(ctx, ixs_mod(ctx, limit, ixs_int(ctx, 4)), IXS_CMP_EQ, zero)));
  CHECK(test_ixs_equivalent_facts(facts, left, right) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_predicate_facts(facts, equality) == IXS_CHECK_TRUE);
  CHECK(ixs_ctx_nerrors(ctx) == errors);

  ixs_ctx_destroy(ctx);
}

static void test_relational_finite_symbol_domain_contract(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *lane = ixs_sym(ctx, "relation_finite_lane");
  ixs_node *polynomial = lane;
  ixs_node *zero = ixs_int(ctx, 0);
  ixs_node *is_zero;
  ixs_node *is_nonzero;
  ixs_node *partially_defined;
  ixs_range_result lane_domain = closed_integer_range(0, 3);
  ixs_facts *facts = ixs_facts_create(ctx);
  size_t errors;
  int64_t value;

  CHECK(ctx && lane && polynomial && zero && facts);
  for (value = 1; value <= 3; value++)
    polynomial =
        ixs_mul(ctx, polynomial, ixs_sub(ctx, lane, ixs_int(ctx, value)));
  is_zero = ixs_cmp(ctx, polynomial, IXS_CMP_EQ, zero);
  is_nonzero = ixs_cmp(ctx, polynomial, IXS_CMP_NE, zero);
  partially_defined = ixs_cmp(
      ctx, ixs_mod(ctx, ixs_int(ctx, 1), ixs_sub(ctx, ixs_int(ctx, 1), lane)),
      IXS_CMP_EQ, zero);
  CHECK(polynomial && is_zero && is_nonzero && partially_defined);
  CHECK(ixs_facts_assume_range(facts, lane, &lane_domain));
  errors = ixs_ctx_nerrors(ctx);
  CHECK(test_ixs_check_predicate_facts(facts, is_zero) == IXS_CHECK_TRUE);
  CHECK(test_ixs_check_predicate_facts(facts, is_nonzero) == IXS_CHECK_FALSE);
  CHECK(test_ixs_check_predicate_facts(facts, partially_defined) ==
        IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == errors);

  ixs_ctx_destroy(ctx);
}

static void test_relational_modular_floor_partition_contract(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *item = ixs_sym(ctx, "relation_floor_partition_item");
  ixs_node *mod64 = ixs_mod(ctx, item, ixs_int(ctx, 64));
  ixs_node *direct = ixs_floor(ctx, ixs_div(ctx, item, ixs_int(ctx, 128)));
  ixs_node *partitioned = ixs_floor(
      ctx, ixs_div(ctx, ixs_sub(ctx, item, mod64), ixs_int(ctx, 128)));
  ixs_node *equality = ixs_cmp(ctx, direct, IXS_CMP_EQ, partitioned);
  ixs_range_result item_domain = closed_integer_range(0, 255);
  ixs_facts *facts = ixs_facts_create(ctx);
  size_t errors = ixs_ctx_nerrors(ctx);

  CHECK(ctx && item && mod64 && direct && partitioned && equality && facts);
  CHECK(ixs_facts_assume_range(facts, item, &item_domain));
  CHECK(test_ixs_equivalent_facts(facts, direct, partitioned) ==
        IXS_CHECK_TRUE);
  CHECK(test_ixs_check_predicate_facts(facts, equality) == IXS_CHECK_TRUE);
  CHECK(ixs_ctx_nerrors(ctx) == errors);

  ixs_ctx_destroy(ctx);
}

static void test_relational_modular_product_reduction_contract(void) {
  static const struct {
    int64_t inner_modulus;
    int64_t outer_modulus;
    int64_t radix;
    int64_t increment;
  } cases[] = {
      {INT64_C(4294967296), INT64_C(4294967296), 2, 1},
      {17, 17, 3, 5},
      {97, 97, 7, 11},
      {35, 7, 4, 3},
  };
  size_t i;

  for (i = 0; i < sizeof(cases) / sizeof(cases[0]); ++i) {
    ixs_ctx *ctx = ixs_ctx_create();
    ixs_node *x = ixs_sym(ctx, "relation_ring_x");
    ixs_node *slot = ixs_sym(ctx, "relation_ring_slot");
    ixs_node *inner_modulus = ixs_int(ctx, cases[i].inner_modulus);
    ixs_node *outer_modulus = ixs_int(ctx, cases[i].outer_modulus);
    ixs_node *selector = ixs_mod(ctx, slot, ixs_int(ctx, cases[i].radix));
    ixs_node *difference =
        ixs_sub(ctx,
                ixs_mod(ctx, ixs_add(ctx, x, ixs_int(ctx, cases[i].increment)),
                        inner_modulus),
                ixs_mod(ctx, x, inner_modulus));
    ixs_node *actual =
        ixs_mod(ctx, ixs_mul(ctx, selector, difference), outer_modulus);
    ixs_node *expected =
        ixs_mod(ctx, ixs_mul(ctx, selector, ixs_int(ctx, cases[i].increment)),
                outer_modulus);
    ixs_node *equality = ixs_cmp(ctx, actual, IXS_CMP_EQ, expected);
    ixs_node *x_integer = ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_floor(ctx, x));
    ixs_node *slot_integer =
        ixs_cmp(ctx, slot, IXS_CMP_EQ, ixs_floor(ctx, slot));
    ixs_range_result x_domain = closed_integer_range(-1000, 1000);
    ixs_range_result slot_domain = closed_integer_range(0, cases[i].radix - 1);
    ixs_facts *facts = ixs_facts_create(ctx);
    size_t errors = ixs_ctx_nerrors(ctx);

    CHECK(ctx && x && slot && inner_modulus && outer_modulus && selector &&
          difference && actual && expected && equality && x_integer &&
          slot_integer && facts);
    CHECK(ixs_facts_assume_range(facts, x, &x_domain));
    CHECK(ixs_facts_assume_range(facts, slot, &slot_domain));
    CHECK(ixs_facts_assume_pred(facts, x_integer));
    CHECK(ixs_facts_assume_pred(facts, slot_integer));
    CHECK(test_ixs_equivalent_facts(facts, actual, expected) == IXS_CHECK_TRUE);
    CHECK(test_ixs_check_predicate_facts(facts, equality) == IXS_CHECK_TRUE);
    CHECK(ixs_ctx_nerrors(ctx) == errors);

    ixs_ctx_destroy(ctx);
  }

  /* Multiplication preserves a residue only through integer multipliers.
   * At x=4 the inner difference is -4 modulo 5, so replacing it by 1 before
   * multiplying by one half would be unsound modulo 5. */
  {
    ixs_ctx *ctx = ixs_ctx_create();
    ixs_node *x = ixs_sym(ctx, "relation_ring_fractional_x");
    ixs_node *five = ixs_int(ctx, 5);
    ixs_node *difference =
        ixs_sub(ctx, ixs_mod(ctx, ixs_add(ctx, x, ixs_int(ctx, 1)), five),
                ixs_mod(ctx, x, five));
    ixs_node *actual =
        ixs_mod(ctx, ixs_mul(ctx, ixs_rat(ctx, 1, 2), difference), five);
    ixs_node *expected = ixs_rat(ctx, 1, 2);
    ixs_facts *facts = ixs_facts_create(ctx);

    CHECK(ctx && x && difference && actual && expected && facts);
    CHECK(ixs_facts_assume_pred(facts,
                                ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, 4))));
    CHECK(test_ixs_equivalent_facts(facts, actual, expected) ==
          IXS_CHECK_FALSE);
    ixs_ctx_destroy(ctx);
  }
}

static void test_relational_scaled_mod_depth_guard(void) {
  enum { DEPTH = 128 };
  ixs_ctx *ctx = ixs_ctx_create();
  ixs_node *lhs = ixs_sym(ctx, "relation_scaled_depth_lhs");
  ixs_node *rhs = ixs_sym(ctx, "relation_scaled_depth_rhs");
  ixs_facts *facts = ixs_facts_create(ctx);
  size_t errors = ixs_ctx_nerrors(ctx);
  int level;

  CHECK(ctx && lhs && rhs && facts);
  for (level = 0; level < DEPTH; level++) {
    int64_t modulus = 3 + 2 * level;
    lhs =
        ixs_mul(ctx, ixs_int(ctx, 2), ixs_mod(ctx, lhs, ixs_int(ctx, modulus)));
    rhs = ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, 2), rhs),
                  ixs_int(ctx, 2 * modulus));
    CHECK(lhs && rhs);
  }
  CHECK(test_ixs_equivalent_facts(facts, lhs, rhs) == IXS_CHECK_UNKNOWN);
  CHECK(ixs_ctx_nerrors(ctx) == errors);

  ixs_ctx_destroy(ctx);
}

int main(void) {
  test_relational_negative_cycle_contract();
  test_relational_chain_insertion_order_contract();
  test_relational_exact_equality_noise_contract();
  test_relational_loop_bound_production_witness();
  test_relational_mod_quotient_identity();
  test_relational_cyclic_xor_recurrence();
  test_relational_mod_quotient_order();
  test_relational_equivalence_probe_guards();
  test_relational_totality_predicate_contract();
  test_relational_optional_proof_extrema();
  test_relational_inverse_range_guards();
  test_relational_inverse_watchers_public_contract();
  test_relational_substituted_congruence_range_contract();
  test_relational_numeric_piecewise_equality_contract();
  test_relational_numeric_boolean_equality_contract();
  test_relational_finite_symbol_domain_contract();
  test_relational_modular_floor_partition_contract();
  test_relational_modular_product_reduction_contract();
  test_relational_scaled_mod_depth_guard();

  printf("test_relational_contract: %d/%d passed\n", tests_passed, tests_run);
  return tests_passed == tests_run ? 0 : 1;
}
