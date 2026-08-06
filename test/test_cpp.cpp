/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include <ixsimpl.hpp>

#include <cstdint>
#include <type_traits>
#include <vector>

static_assert(std::is_const<ixs_node>::value,
              "ixs_node must be an immutable handle type");

int main() {
  ixs::Context ctx;
  ixs::Expr x = ixs::Expr::sym(ctx, "x");
  ixs::Expr y = ixs::Expr::sym(ctx, "y");
  ixs::Expr zero = ixs::Expr::integer(ctx, 0);
  ixs::Expr one = ixs::Expr::integer(ctx, 1);
  ixs::Expr eight = ixs::Expr::integer(ctx, 8);
  ixs::Expr nonnegative = ixs::Expr::parse_pred(ctx, "x >= 0");
  ixs::Expr congruent = ixs::Expr::parse_pred(ctx, "Mod(x, 8) == 0");
  ixs::Expr rational_eighth = ixs::Expr::parse_expr(ctx, "x/8");
  ixs::Expr rational_floor = ixs::Expr::parse_expr(ctx, "floor(x/8)");
  ixs::Expr assumptions[1] = {nonnegative};
  ixs_range_result range = {};
  ixs_integer_range_result integer_range = {};

  if (nonnegative.check(assumptions, 1) != IXS_CHECK_TRUE ||
      x.check_integer_valued() != IXS_CHECK_TRUE ||
      x.check_defined() != IXS_CHECK_TRUE ||
      eight.get_pow2_fact() != IXS_POW2_POSITIVE ||
      !x.range(range, assumptions, 1) || !range.has_lower ||
      !x.integer_range(integer_range, assumptions, 1) ||
      !integer_range.has_lower || integer_range.lower != 0 ||
      integer_range.has_upper || (x * (y + one)).expand().is_null())
    return 1;

  const ixs::Expr &const_expr = x + one;
  const ixs_node *const_node = const_expr.raw();
  const ixs_node *child = ixs_node_child(const_node, 0);
  char text[64];
  if (ixs_node_tag(const_node) != IXS_ADD || !child ||
      ixs_print(const_node, text, sizeof(text)) == 0)
    return 2;

  ixs::Facts facts = ctx.facts();
  ixs_range_result explicit_range = {true, true, 0, 1, 63, 1};
  ixs::Expr twice_x = x * ixs::Expr::integer(ctx, 2);
  std::vector<ixs::Expr> fact_predicates = {nonnegative, congruent};
  if (facts.check_consistent() != IXS_CHECK_TRUE ||
      !facts.assume_many(fact_predicates) ||
      !facts.assume_range(x, explicit_range) ||
      !facts.derive_affine(x, 2, 0, twice_x))
    return 3;

  std::vector<ixs::Expr> batch = {x + zero, twice_x + zero};
  size_t finite_budget = 0;
  ixs::FiniteDomainResult finite_equivalence =
      facts.equivalent_finite_domain(x, x, finite_budget);
  facts.simplify_batch(batch);
  if (facts.simplify(x + zero).is_null() ||
      facts.check(nonnegative) != IXS_CHECK_TRUE ||
      facts.check_integer_valued(x) != IXS_CHECK_TRUE ||
      facts.check_defined(x) != IXS_CHECK_TRUE ||
      facts.check_predicate(nonnegative) != IXS_CHECK_TRUE ||
      facts.equivalent(x, x) != IXS_CHECK_TRUE ||
      finite_equivalence.status != IXS_FINITE_DOMAIN_COMPLETE ||
      finite_equivalence.check != IXS_CHECK_TRUE ||
      !finite_equivalence.value.is_null() || finite_budget != 0 ||
      facts.check_divisible(twice_x, 2) != IXS_CHECK_TRUE ||
      facts.get_pow2_fact(eight) != IXS_POW2_POSITIVE ||
      !facts.range(x, range) || !facts.integer_range(x, integer_range) ||
      !integer_range.has_lower || integer_range.lower != 0 ||
      !integer_range.has_upper || integer_range.upper != 56 ||
      facts.rational_intermediates_fit(rational_floor, 8) != IXS_CHECK_TRUE)
    return 4;
  ixs::RationalMaterializationPlan plan =
      facts.plan_rational_materialization(rational_eighth, 8);
  if (plan.status != IXS_CHECK_TRUE || plan.denominator != 8 ||
      plan.numerator.str() != "x")
    return 4;

  ixs::Expr finite_item = ixs::Expr::sym(ctx, "finite_item");
  std::vector<int64_t> finite_points = {0, 1, 2, 3};
  std::vector<ixs::Expr> finite_values = {y, y + one, y + one, y};
  size_t synthesis_budget = 8;
  ixs::FiniteDomainResult finite_expression =
      facts.synthesize_finite_expression(finite_item, finite_points,
                                         finite_values, synthesis_budget);
  if (finite_expression.status != IXS_FINITE_DOMAIN_COMPLETE ||
      finite_expression.check != IXS_CHECK_TRUE ||
      finite_expression.value.is_null() || synthesis_budget != 0)
    return 16;
  synthesis_budget = finite_points.size();
  ixs::FiniteDomainResult verified_expression =
      facts.verify_finite_expression(finite_item, finite_points, finite_values,
                                     finite_expression.value, synthesis_budget);
  if (verified_expression.status != IXS_FINITE_DOMAIN_COMPLETE ||
      verified_expression.check != IXS_CHECK_TRUE ||
      !verified_expression.value.is_null() || synthesis_budget != 0)
    return 19;
  std::vector<ixs::Expr> finite_predicates;
  finite_predicates.reserve(finite_values.size());
  for (const ixs::Expr &value : finite_values)
    finite_predicates.push_back(value >= x);
  synthesis_budget = 24;
  ixs::FiniteDomainResult finite_predicate = facts.synthesize_finite_predicate(
      finite_item, finite_points, finite_predicates, synthesis_budget);
  if (finite_predicate.status != IXS_FINITE_DOMAIN_COMPLETE ||
      finite_predicate.check != IXS_CHECK_TRUE ||
      !finite_predicate.value.is_pred() || synthesis_budget != 0)
    return 17;
  synthesis_budget = finite_points.size();
  ixs::FiniteDomainResult verified_predicate = facts.verify_finite_predicate(
      finite_item, finite_points, finite_predicates, finite_predicate.value,
      synthesis_budget);
  if (verified_predicate.status != IXS_FINITE_DOMAIN_COMPLETE ||
      verified_predicate.check != IXS_CHECK_TRUE ||
      !verified_predicate.value.is_null() || synthesis_budget != 0)
    return 20;
  std::vector<int64_t> mismatched_points = {0};
  synthesis_budget = 8;
  ixs::FiniteDomainResult mismatched = facts.synthesize_finite_expression(
      finite_item, mismatched_points, finite_values, synthesis_budget);
  ixs::FiniteDomainResult mismatched_verify = facts.verify_finite_expression(
      finite_item, mismatched_points, finite_values, finite_expression.value,
      synthesis_budget);
  if (mismatched.status != IXS_FINITE_DOMAIN_INVALID ||
      mismatched.check != IXS_CHECK_UNKNOWN || !mismatched.value.is_null() ||
      synthesis_budget != 8 ||
      mismatched_verify.status != IXS_FINITE_DOMAIN_INVALID ||
      mismatched_verify.check != IXS_CHECK_UNKNOWN ||
      !mismatched_verify.value.is_null() || synthesis_budget != 8)
    return 21;

  std::vector<ixs::FiniteIntegerDomain> finite_domains = {
      {finite_item, finite_points}};
  std::vector<ixs::FiniteDomainBatchQuery> finite_queries = {
      {IXS_FINITE_DOMAIN_PREDICATE_TRUE,
       finite_item < ixs::Expr::integer(ctx, 2)},
      {IXS_FINITE_DOMAIN_DEFINED, finite_item + one}};
  std::vector<ixs::FiniteDomainBatchResult> finite_results;
  size_t finite_batch_budget = 8;
  ixs_finite_domain_status finite_batch_status =
      facts.check_finite_domain_batch(finite_domains, finite_queries,
                                      finite_results, finite_batch_budget);
  if (finite_batch_status != IXS_FINITE_DOMAIN_COMPLETE ||
      finite_batch_budget != 0 || finite_results.size() != 2 ||
      finite_results[0].check != IXS_CHECK_FALSE ||
      finite_results[0].witness != 2 ||
      finite_results[1].check != IXS_CHECK_TRUE ||
      finite_results[1].witness != SIZE_MAX)
    return 22;
  std::vector<ixs::FiniteIntegerDomain> no_finite_domains;
  std::vector<ixs::FiniteDomainBatchQuery> one_finite_query = {
      finite_queries[0]};
  finite_results = {{IXS_CHECK_TRUE, 0}};
  finite_batch_budget = 1;
  finite_batch_status = facts.check_finite_domain_batch(
      no_finite_domains, one_finite_query, finite_results, finite_batch_budget);
  if (finite_batch_status != IXS_FINITE_DOMAIN_INVALID ||
      finite_batch_budget != 1 || finite_results.size() != 1 ||
      finite_results[0].check != IXS_CHECK_UNKNOWN ||
      finite_results[0].witness != SIZE_MAX)
    return 23;

  int64_t delta = 0;
  int64_t constant = 0;
  int64_t modulus = 0;
  int64_t residue = 0;
  ixs_known_bits bits = {};
  ixs::Expr coefficient = zero;
  ixs::Expr residual = zero;
  ixs::Expr difference = zero;
  ixs::Expr numerator = zero;
  ixs::Expr denominator = zero;
  ixs::Expr rational_product = ixs::Expr::rational(ctx, 3, 4) * x;
  ixs::Expr wrapped_y =
      ixs::mod(y, ixs::Expr::integer(ctx, INT64_C(4294967296)));
  ixs::ModuloRecurrenceResult modulo_recurrence =
      facts.modulo_recurrence(x + one, x, x, IXS_REMAINDER_SIGNED, 32, 5);
  if (!facts.constant_difference(x + eight, x + one, delta) || delta != 7 ||
      modulo_recurrence.status != IXS_MODULO_RECURRENCE_PROVEN ||
      modulo_recurrence.increment != 1 ||
      modulo_recurrence.remainder.str() != "Mod(x, 5)" ||
      !facts.affine_decompose(twice_x + one, x, coefficient, residual) ||
      !facts.decompose_exact_quotient(rational_product, numerator,
                                      denominator) ||
      !(numerator == ixs::Expr::integer(ctx, 3) * x) ||
      !(denominator == ixs::Expr::integer(ctx, 4)) ||
      !facts.finite_difference(twice_x, x, one, difference) ||
      !facts.split_additive_constant(twice_x + eight, residual, constant) ||
      !facts.get_known_bits(x, bits) ||
      !facts.get_symbol_congruence(x, modulus, residue) || modulus != 8 ||
      facts.equivalent_modulo_pow2(y, wrapped_y, 32) != IXS_CHECK_TRUE ||
      facts.check_congruent(x, 8, 0) != IXS_CHECK_TRUE)
    return 5;

  numerator = one;
  denominator = eight;
  if (facts.decompose_exact_quotient(x, numerator, denominator) ||
      !(numerator == one) || !(denominator == eight))
    return 6;

  ixs::Expr loop_iv = ixs::Expr::sym(ctx, "loop_iv");
  ixs::Expr cyclic_expr =
      ixs::Expr::parse_expr(ctx, "1024*wave_id + 32768*Mod(loop_iv - 2, 4)");
  ixs::Facts cyclic_facts = ctx.facts();
  std::vector<ixs::Expr> cyclic_predicates = {
      ixs::Expr::parse_pred(ctx, "wave_id >= 0"),
      ixs::Expr::parse_pred(ctx, "wave_id <= 15")};
  ixs::CyclicDecomposition cyclic{zero, 0, 0, 0, 0, false};
  if (!cyclic_facts.assume_many(cyclic_predicates) ||
      !cyclic_facts.decompose_cyclic(cyclic_expr, loop_iv, cyclic) ||
      cyclic.residual.str() != "1024*wave_id" || cyclic.scale != 32768 ||
      cyclic.modulus != 4 || cyclic.phase != 2 || cyclic.ring != 131072 ||
      !cyclic.residual_bounded ||
      cyclic_facts.decompose_cyclic(
          loop_iv + ixs::Expr::integer(ctx, 8) *
                        ixs::mod(loop_iv, ixs::Expr::integer(ctx, 4)),
          loop_iv, cyclic))
    return 15;

  ixs::ExactDivideResult exact = facts.try_exact_divide(twice_x, 2);
  if (exact.status != IXS_EXACT_DIVIDE_PROVEN || exact.quotient.is_null())
    return 7;

  ixs::Facts contradictory = ctx.facts();
  std::vector<ixs::Expr> contradictory_predicates = {
      ixs::Expr::parse_pred(ctx, "x >= 1"),
      ixs::Expr::parse_pred(ctx, "x <= 0")};
  if (!contradictory.assume_many(contradictory_predicates) ||
      contradictory.check_consistent() != IXS_CHECK_FALSE)
    return 14;

  std::vector<std::vector<ixs::Expr>> relation_groups = {
      {ixs::Expr::parse_pred(ctx, "group_x == 0"), nonnegative},
      {ixs::Expr::parse_pred(ctx, "group_y == 1"), nonnegative},
      {ixs::Expr::parse_pred(ctx, "group_z == 2"), nonnegative}};
  ixs::Expr group_x = ixs::Expr::sym(ctx, "group_x");
  ixs::Expr group_y = ixs::Expr::sym(ctx, "group_y");
  ixs::Expr group_z = ixs::Expr::sym(ctx, "group_z");
  std::vector<ixs::GroupUnionQuery> relation_queries = {
      {0, 1, IXS_GROUP_UNION_EQUIVALENT, group_y, group_x + one},
      {0, 2, IXS_GROUP_UNION_CONSTANT_DIFFERENCE, group_z, group_x}};
  std::vector<ixs::GroupUnionResult> relation_results;
  size_t relation_work = 10000;
  if (ixs::query_group_unions(ctx, relation_groups, relation_queries,
                              relation_results,
                              relation_work) != IXS_GROUP_UNION_COMPLETE ||
      relation_results.size() != 2 ||
      relation_results[0].status != IXS_CHECK_TRUE ||
      relation_results[1].status != IXS_CHECK_TRUE ||
      relation_results[1].difference != 2)
    return 18;

  ixs::Facts transferred = ctx.facts();
  if (!transferred.substitute(facts, x, y))
    return 8;
  std::vector<ixs::Expr> targets = {x, y};
  std::vector<ixs::Expr> replacements = {y, x};
  if (!transferred.substitute_multi(facts, targets, replacements))
    return 9;

  std::vector<ixs::Expr> assoc_values = {x, y, one};
  ixs::Expr assoc_nodes[] = {
      ixs::max(assoc_values), ixs::min({x, y, one}),  ixs::xor_(assoc_values),
      ixs::and_({x, y, one}), ixs::or_(assoc_values),
  };
  ixs::Expr canonical_nodes[] = {
      ixs::max(ixs::max(one, y), x),   ixs::min(ixs::min(one, y), x),
      ixs::xor_(ixs::xor_(one, y), x), ixs::and_(ixs::and_(one, y), x),
      ixs::or_(ixs::or_(one, y), x),
  };
  const ixs_tag assoc_tags[] = {IXS_MAX, IXS_MIN, IXS_XOR, IXS_AND, IXS_OR};
  for (std::size_t i = 0; i < 5; ++i) {
    const ixs::Expr &expr = assoc_nodes[i];
    if (ixs_node_tag(expr.raw()) != assoc_tags[i])
      return 9;
    if (ixs_node_assoc_nargs(expr.raw()) != 3)
      return 10;
    if (expr.raw() != canonical_nodes[i].raw())
      return 11;
  }
  bool rejected_empty = false;
  try {
    std::vector<ixs::Expr> empty;
    (void)ixs::max(empty);
  } catch (const std::invalid_argument &) {
    rejected_empty = true;
  }
  if (!rejected_empty)
    return 12;

  bool rejected_foreign = false;
  try {
    ixs::Context other_ctx;
    std::vector<ixs::Expr> mixed = {x, ixs::Expr::sym(other_ctx, "z")};
    (void)ixs::or_(mixed);
  } catch (const std::invalid_argument &) {
    rejected_foreign = true;
  }
  if (!rejected_foreign)
    return 13;

  return 0;
}
