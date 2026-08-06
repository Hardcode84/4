/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef TEST_CHECK_H
#define TEST_CHECK_H

#include <ixsimpl.h>

#include "test_session_compat.h"

#include <stdio.h>

static int tests_run = 0;
static int tests_passed = 0;

#define CHECK(cond)                                                            \
  do {                                                                         \
    tests_run++;                                                               \
    if (!(cond)) {                                                             \
      fprintf(stderr, "FAIL: %s:%d: %s\n", __FILE__, __LINE__, #cond);         \
    } else {                                                                   \
      tests_passed++;                                                          \
    }                                                                          \
  } while (0)

/* Most tests exercise semantic proof results and have separate cases for the
 * public transport status.  These helpers keep those assertions compact while
 * making the required COMPLETE boundary explicit in one place. */
static inline const ixs_node *test_ixs_simplify_facts(ixs_facts *facts,
                                                const ixs_node *expr) {
  ixs_simplify_result result = ixs_simplify_facts(facts, expr);
  return result.status == IXS_FACT_QUERY_COMPLETE ? result.value : NULL;
}

static inline void test_ixs_simplify_batch_facts(ixs_facts *facts,
                                          const ixs_node **exprs, size_t n) {
  (void)ixs_simplify_batch_facts(facts, exprs, n);
}

static inline ixs_check_result
test_ixs_fact_check_value(ixs_fact_check_result result) {
  return result.status == IXS_FACT_QUERY_COMPLETE ? result.check
                                                  : IXS_CHECK_UNKNOWN;
}

static inline ixs_check_result test_ixs_check_facts(ixs_facts *facts,
                                             const ixs_node *expr) {
  return test_ixs_fact_check_value(ixs_check_facts(facts, expr));
}

static inline ixs_check_result
test_ixs_check_predicate_facts(ixs_facts *facts, const ixs_node *predicate) {
  return test_ixs_fact_check_value(
      ixs_check_predicate_facts(facts, predicate));
}

static inline ixs_check_result test_ixs_check_consistent_facts(ixs_facts *facts) {
  return test_ixs_fact_check_value(ixs_check_consistent_facts(facts));
}

static inline ixs_check_result test_ixs_equivalent_facts(ixs_facts *facts,
                                                  const ixs_node *lhs,
                                                  const ixs_node *rhs) {
  ixs_fact_check_result result = ixs_equivalent_facts(facts, lhs, rhs);
  return test_ixs_fact_check_value(result);
}

static inline ixs_check_result test_ixs_equivalent_modulo_pow2_facts(
    ixs_facts *facts, const ixs_node *lhs, const ixs_node *rhs,
    unsigned bits) {
  return test_ixs_fact_check_value(
      ixs_equivalent_modulo_pow2_facts(facts, lhs, rhs, bits));
}

static inline ixs_check_result
test_ixs_check_integer_valued_facts(ixs_facts *facts, const ixs_node *expr) {
  return test_ixs_fact_check_value(
      ixs_check_integer_valued_facts(facts, expr));
}

static inline ixs_check_result test_ixs_check_defined_facts(ixs_facts *facts,
                                                     const ixs_node *expr) {
  return test_ixs_fact_check_value(ixs_check_defined_facts(facts, expr));
}

static inline ixs_check_result test_ixs_check_divisible_facts(ixs_facts *facts,
                                                       const ixs_node *expr,
                                                       int64_t modulus) {
  return test_ixs_fact_check_value(
      ixs_check_divisible_facts(facts, expr, modulus));
}

static inline ixs_check_result test_ixs_check_congruent_facts(
    ixs_facts *facts, const ixs_node *expr, int64_t modulus, int64_t residue) {
  return test_ixs_fact_check_value(
      ixs_check_congruent_facts(facts, expr, modulus, residue));
}

static inline ixs_check_result test_ixs_check_rational_intermediates_facts(
    ixs_facts *facts, const ixs_node *expr, uint32_t word_bits) {
  return test_ixs_fact_check_value(
      ixs_check_rational_intermediates_facts(facts, expr, word_bits));
}

static inline bool test_ixs_constant_difference_facts(ixs_facts *facts,
                                               const ixs_node *lhs,
                                               const ixs_node *rhs,
                                               int64_t *difference) {
  ixs_constant_difference_result result =
      ixs_constant_difference_facts(facts, lhs, rhs);
  if (difference)
    *difference = result.available ? result.difference : 0;
  return result.status == IXS_FACT_QUERY_COMPLETE && result.available;
}

static inline ixs_pow2_fact test_ixs_get_pow2_fact_facts(ixs_facts *facts,
                                                  const ixs_node *expr) {
  ixs_pow2_query_result result = ixs_get_pow2_fact_facts(facts, expr);
  return result.status == IXS_FACT_QUERY_COMPLETE ? result.fact
                                                  : IXS_POW2_UNKNOWN;
}

static inline bool test_ixs_get_known_bits_facts(ixs_facts *facts,
                                          const ixs_node *expr,
                                          ixs_known_bits *out) {
  ixs_known_bits_query_result result = ixs_get_known_bits_facts(facts, expr);
  if (out)
    *out = result.bits;
  return out && result.status == IXS_FACT_QUERY_COMPLETE;
}

static inline bool test_ixs_get_symbol_congruence_facts(
    ixs_facts *facts, const ixs_node *symbol, int64_t *modulus,
    int64_t *residue) {
  ixs_symbol_congruence_result result =
      ixs_get_symbol_congruence_facts(facts, symbol);
  if (modulus)
    *modulus = result.available ? result.modulus : 0;
  if (residue)
    *residue = result.available ? result.residue : 0;
  return modulus && residue && modulus != residue &&
         result.status == IXS_FACT_QUERY_COMPLETE && result.available;
}

static inline bool test_ixs_range_facts(ixs_facts *facts, const ixs_node *expr,
                                 ixs_range_result *out) {
  ixs_range_query_result result = ixs_range_facts(facts, expr);
  if (out)
    *out = result.range;
  return out && result.status == IXS_FACT_QUERY_COMPLETE && result.available;
}

static inline bool test_ixs_integer_range_facts(ixs_facts *facts,
                                         const ixs_node *expr,
                                         ixs_integer_range_result *out) {
  ixs_integer_range_query_result result = ixs_integer_range_facts(facts, expr);
  if (out)
    *out = result.range;
  return out && result.status == IXS_FACT_QUERY_COMPLETE && result.available;
}

static inline bool test_ixs_affine_decompose_facts(
    ixs_facts *facts, const ixs_node *expr, const ixs_node *symbol,
    const ixs_node **coefficient, const ixs_node **residual) {
  ixs_affine_decomposition_result result =
      ixs_affine_decompose_facts(facts, expr, symbol);
  if (coefficient)
    *coefficient = result.available ? result.coefficient : NULL;
  if (residual)
    *residual = result.available ? result.residual : NULL;
  return coefficient && residual && result.status == IXS_FACT_QUERY_COMPLETE &&
         result.available;
}

static inline bool test_ixs_decompose_exact_quotient_facts(
    ixs_facts *facts, const ixs_node *expr, const ixs_node **numerator,
    const ixs_node **denominator) {
  ixs_exact_quotient_result result =
      ixs_decompose_exact_quotient_facts(facts, expr);
  if (numerator)
    *numerator = result.available ? result.numerator : NULL;
  if (denominator)
    *denominator = result.available ? result.denominator : NULL;
  return numerator && denominator &&
         result.status == IXS_FACT_QUERY_COMPLETE && result.available;
}

static inline bool test_ixs_finite_difference_facts(
    ixs_facts *facts, const ixs_node *expr, const ixs_node *symbol,
    const ixs_node *step, const ixs_node **difference) {
  ixs_finite_difference_result result =
      ixs_finite_difference_facts(facts, expr, symbol, step);
  if (difference)
    *difference = result.available ? result.difference : NULL;
  return difference && result.status == IXS_FACT_QUERY_COMPLETE &&
         result.available;
}

static inline bool test_ixs_decompose_cyclic_facts(
    ixs_facts *facts, const ixs_node *expr, const ixs_node *symbol,
    ixs_cyclic_decomposition *out) {
  ixs_cyclic_decomposition_result result =
      ixs_decompose_cyclic_facts(facts, expr, symbol);
  if (out)
    *out = result.decomposition;
  return out && result.status == IXS_FACT_QUERY_COMPLETE && result.available;
}

static inline bool test_ixs_split_additive_constant_facts(
    ixs_facts *facts, const ixs_node *expr, const ixs_node **residual,
    int64_t *constant) {
  ixs_additive_constant_result result =
      ixs_split_additive_constant_facts(facts, expr);
  if (residual)
    *residual = result.available ? result.residual : NULL;
  if (constant)
    *constant = result.available ? result.constant : 0;
  return residual && constant && result.status == IXS_FACT_QUERY_COMPLETE &&
         result.available;
}

#endif /* TEST_CHECK_H */
