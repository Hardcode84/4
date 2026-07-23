/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include <ixsimpl.hpp>

#include <cstdint>
#include <vector>

int main() {
  ixs::Context ctx;
  ixs::Expr x = ixs::Expr::sym(ctx, "x");
  ixs::Expr y = ixs::Expr::sym(ctx, "y");
  ixs::Expr zero = ixs::Expr::integer(ctx, 0);
  ixs::Expr one = ixs::Expr::integer(ctx, 1);
  ixs::Expr eight = ixs::Expr::integer(ctx, 8);
  ixs::Expr nonnegative = ixs::Expr::parse_pred(ctx, "x >= 0");
  ixs::Expr congruent = ixs::Expr::parse_pred(ctx, "Mod(x, 8) == 0");
  ixs::Expr assumptions[1] = {nonnegative};
  ixs_range_result range = {};

  if (nonnegative.check(assumptions, 1) != IXS_CHECK_TRUE ||
      x.check_integer_valued() != IXS_CHECK_TRUE ||
      x.check_defined() != IXS_CHECK_TRUE ||
      eight.get_pow2_fact() != IXS_POW2_POSITIVE ||
      !x.range(range, assumptions, 1) || !range.has_lower ||
      (x * (y + one)).expand().is_null())
    return 1;

  const ixs::Expr &const_expr = x + one;
  const ixs_node *const_node = const_expr.raw_const();
  ixs_node *child = ixs_node_child(const_node, 0);
  char text[64];
  if (ixs_node_tag(const_node) != IXS_ADD || !child ||
      ixs_print(const_node, text, sizeof(text)) == 0)
    return 2;

  ixs::Facts facts = ctx.facts();
  ixs_range_result explicit_range = {true, true, 0, 1, 63, 1};
  ixs::Expr twice_x = x * ixs::Expr::integer(ctx, 2);
  std::vector<ixs::Expr> fact_predicates = {nonnegative, congruent};
  if (!facts.assume_many(fact_predicates) ||
      !facts.assume_range(x, explicit_range) ||
      !facts.derive_affine(x, 2, 0, twice_x))
    return 3;

  std::vector<ixs::Expr> batch = {x + zero, twice_x + zero};
  facts.simplify_batch(batch);
  if (facts.simplify(x + zero).is_null() ||
      facts.check(nonnegative) != IXS_CHECK_TRUE ||
      facts.check_integer_valued(x) != IXS_CHECK_TRUE ||
      facts.check_defined(x) != IXS_CHECK_TRUE ||
      facts.check_predicate(nonnegative) != IXS_CHECK_TRUE ||
      facts.equivalent(x, x) != IXS_CHECK_TRUE ||
      facts.check_divisible(twice_x, 2) != IXS_CHECK_TRUE ||
      facts.get_pow2_fact(eight) != IXS_POW2_POSITIVE || !facts.range(x, range))
    return 4;

  int64_t delta = 0;
  int64_t constant = 0;
  int64_t modulus = 0;
  int64_t residue = 0;
  ixs_known_bits bits = {};
  ixs::Expr coefficient = zero;
  ixs::Expr residual = zero;
  ixs::Expr difference = zero;
  if (!facts.constant_difference(x + eight, x + one, delta) || delta != 7 ||
      !facts.affine_decompose(twice_x + one, x, coefficient, residual) ||
      !facts.finite_difference(twice_x, x, one, difference) ||
      !facts.split_additive_constant(twice_x + eight, residual, constant) ||
      !facts.get_known_bits(x, bits) ||
      !facts.get_symbol_congruence(x, modulus, residue) || modulus != 8 ||
      facts.check_congruent(x, 8, 0) != IXS_CHECK_TRUE)
    return 5;

  ixs::ExactDivideResult exact = facts.try_exact_divide(twice_x, 2);
  if (exact.status != IXS_EXACT_DIVIDE_PROVEN || exact.quotient.is_null())
    return 6;

  ixs::Facts transferred = ctx.facts();
  if (!transferred.substitute(facts, x, y))
    return 7;
  std::vector<ixs::Expr> targets = {x, y};
  std::vector<ixs::Expr> replacements = {y, x};
  if (!transferred.substitute_multi(facts, targets, replacements))
    return 8;

  return 0;
}
