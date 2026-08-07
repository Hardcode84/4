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

static inline const ixs_node *test_ixs_simplify_facts(ixs_facts *facts,
                                                      const ixs_node *expr) {
  return ixs_simplify_facts(facts, expr);
}

static inline void test_ixs_simplify_batch_facts(ixs_facts *facts,
                                                 const ixs_node **exprs,
                                                 size_t n) {
  ixs_simplify_batch_facts(facts, exprs, n);
}

static inline ixs_check_result test_ixs_check_facts(ixs_facts *facts,
                                                    const ixs_node *expr) {
  return ixs_check_facts(facts, expr);
}

static inline ixs_check_result
test_ixs_check_predicate_facts(ixs_facts *facts, const ixs_node *predicate) {
  return ixs_check_predicate_facts(facts, predicate);
}

static inline ixs_check_result test_ixs_equivalent_facts(ixs_facts *facts,
                                                         const ixs_node *lhs,
                                                         const ixs_node *rhs) {
  return ixs_equivalent_facts(facts, lhs, rhs);
}

static inline ixs_check_result
test_ixs_check_integer_valued_facts(ixs_facts *facts, const ixs_node *expr) {
  return ixs_check_integer_valued_facts(facts, expr);
}

static inline ixs_check_result
test_ixs_check_defined_facts(ixs_facts *facts, const ixs_node *expr) {
  return ixs_check_defined_facts(facts, expr);
}

static inline ixs_check_result
test_ixs_check_divisible_facts(ixs_facts *facts, const ixs_node *expr,
                               int64_t modulus) {
  return ixs_check_divisible_facts(facts, expr, modulus);
}

static inline ixs_check_result
test_ixs_check_congruent_facts(ixs_facts *facts, const ixs_node *expr,
                               int64_t modulus, int64_t residue) {
  return ixs_check_congruent_facts(facts, expr, modulus, residue);
}

static inline bool test_ixs_constant_difference_facts(ixs_facts *facts,
                                                      const ixs_node *lhs,
                                                      const ixs_node *rhs,
                                                      int64_t *difference) {
  return ixs_constant_difference_facts(facts, lhs, rhs, difference);
}

static inline ixs_pow2_fact test_ixs_get_pow2_fact_facts(ixs_facts *facts,
                                                         const ixs_node *expr) {
  return ixs_get_pow2_fact_facts(facts, expr);
}

static inline bool test_ixs_get_known_bits_facts(ixs_facts *facts,
                                                 const ixs_node *expr,
                                                 ixs_known_bits *out) {
  return ixs_get_known_bits_facts(facts, expr, out);
}

static inline bool test_ixs_get_symbol_congruence_facts(ixs_facts *facts,
                                                        const ixs_node *symbol,
                                                        int64_t *modulus,
                                                        int64_t *residue) {
  return ixs_get_symbol_congruence_facts(facts, symbol, modulus, residue);
}

static inline bool test_ixs_range_facts(ixs_facts *facts, const ixs_node *expr,
                                        ixs_range_result *out) {
  return ixs_range_facts(facts, expr, out);
}

static inline bool test_ixs_affine_decompose_facts(ixs_facts *facts,
                                                   const ixs_node *expr,
                                                   const ixs_node *symbol,
                                                   const ixs_node **coefficient,
                                                   const ixs_node **residual) {
  return ixs_affine_decompose_facts(facts, expr, symbol, coefficient, residual);
}

static inline bool
test_ixs_finite_difference_facts(ixs_facts *facts, const ixs_node *expr,
                                 const ixs_node *symbol, const ixs_node *step,
                                 const ixs_node **difference) {
  return ixs_finite_difference_facts(facts, expr, symbol, step, difference);
}

static inline bool
test_ixs_split_additive_constant_facts(ixs_facts *facts, const ixs_node *expr,
                                       const ixs_node **residual,
                                       int64_t *constant) {
  return ixs_split_additive_constant_facts(facts, expr, residual, constant);
}

#endif /* TEST_CHECK_H */
