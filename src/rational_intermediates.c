/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "rational_intermediates.h"

#include "rational.h"
#include "simplify.h"

#include <limits.h>
#include <string.h>

#define RATIONAL_INTERMEDIATE_DEPTH_LIMIT 64u
#define RATIONAL_INTERMEDIATE_VISIT_LIMIT 16384u
#define RATIONAL_INTERMEDIATE_CASE_LIMIT 1024u
#define RATIONAL_INTERMEDIATE_POWER_LIMIT 64u
#define RATIONAL_INTERMEDIATE_MEMO_INIT_CAP 64u

typedef struct {
  ixs_node *numerator;
  int64_t denominator;
  ixs_check_result fits;
  bool valid;
} rational_intermediate_proof;

/* One bottom-up result carries every semantic property needed by the root
 * query.  In particular, containment, island ownership, proof construction,
 * and child-island aggregation are not separate walks. */
typedef struct {
  rational_intermediate_proof proof;
  ixs_check_result islands_fit;
  bool contains_materialization;
  bool owns_materialization;
} rational_intermediate_analysis;

typedef struct {
  ixs_node *expr;
  rational_intermediate_analysis analysis;
} rational_intermediate_memo_entry;

typedef struct {
  ixs_ctx *ctx;
  ixs_bounds *bounds;
  int64_t word_lower;
  int64_t word_upper;
  int64_t signed_lower;
  int64_t signed_upper;
  uint64_t word_modulus;
  rational_intermediate_memo_entry *memo;
  size_t memo_cap;
  size_t memo_used;
  size_t visited;
  bool limited;
  bool oom;
} rational_intermediate_state;

static ixs_check_result rational_check_and(ixs_check_result lhs,
                                           ixs_check_result rhs) {
  if (lhs == IXS_CHECK_FALSE || rhs == IXS_CHECK_FALSE)
    return IXS_CHECK_FALSE;
  if (lhs == IXS_CHECK_TRUE && rhs == IXS_CHECK_TRUE)
    return IXS_CHECK_TRUE;
  return IXS_CHECK_UNKNOWN;
}

static rational_intermediate_proof rational_invalid_proof(void) {
  rational_intermediate_proof proof;
  proof.numerator = NULL;
  proof.denominator = 1;
  proof.fits = IXS_CHECK_UNKNOWN;
  proof.valid = false;
  return proof;
}

static rational_intermediate_analysis rational_empty_analysis(void) {
  rational_intermediate_analysis analysis;
  analysis.proof = rational_invalid_proof();
  analysis.islands_fit = IXS_CHECK_TRUE;
  analysis.contains_materialization = false;
  analysis.owns_materialization = false;
  return analysis;
}

static ixs_check_result rational_proof_fit(rational_intermediate_proof proof) {
  return proof.valid ? proof.fits : IXS_CHECK_UNKNOWN;
}

static size_t rational_memo_hash(const ixs_node *expr) {
  uint64_t value = (uint64_t)(uintptr_t)expr;
  value ^= value >> 33;
  value *= UINT64_C(0xff51afd7ed558ccd);
  value ^= value >> 33;
  return (size_t)value;
}

static rational_intermediate_memo_entry *
rational_memo_slot(rational_intermediate_memo_entry *memo, size_t cap,
                   const ixs_node *expr) {
  size_t index = rational_memo_hash(expr) & (cap - 1u);
  while (memo[index].expr && memo[index].expr != expr)
    index = (index + 1u) & (cap - 1u);
  return &memo[index];
}

static bool rational_memo_grow(rational_intermediate_state *state) {
  size_t new_cap = state->memo_cap ? state->memo_cap * 2u
                                   : RATIONAL_INTERMEDIATE_MEMO_INIT_CAP;
  rational_intermediate_memo_entry *memo;
  size_t i;
  if (new_cap <= state->memo_cap || new_cap > (size_t)-1 / sizeof(*memo)) {
    state->limited = true;
    return false;
  }
  memo = ixs_arena_alloc(state->bounds->scratch, new_cap * sizeof(*memo),
                         sizeof(void *));
  if (!memo) {
    state->oom = true;
    return false;
  }
  memset(memo, 0, new_cap * sizeof(*memo));
  for (i = 0; i < state->memo_cap; i++) {
    if (state->memo[i].expr) {
      rational_intermediate_memo_entry *slot =
          rational_memo_slot(memo, new_cap, state->memo[i].expr);
      *slot = state->memo[i];
    }
  }
  state->memo = memo;
  state->memo_cap = new_cap;
  return true;
}

static rational_intermediate_memo_entry *
rational_memo_find(rational_intermediate_state *state, const ixs_node *expr) {
  rational_intermediate_memo_entry *slot;
  if (!state->memo_cap)
    return NULL;
  slot = rational_memo_slot(state->memo, state->memo_cap, expr);
  return slot->expr ? slot : NULL;
}

static bool rational_memo_store(rational_intermediate_state *state,
                                ixs_node *expr,
                                rational_intermediate_analysis analysis) {
  rational_intermediate_memo_entry *slot;
  if (!state->memo_cap && !rational_memo_grow(state))
    return false;
  slot = rational_memo_slot(state->memo, state->memo_cap, expr);
  if (slot->expr) {
    slot->analysis = analysis;
    return true;
  }
  if (state->memo_used + 1u > state->memo_cap - state->memo_cap / 4u) {
    if (!rational_memo_grow(state))
      return false;
    slot = rational_memo_slot(state->memo, state->memo_cap, expr);
  }
  slot->expr = expr;
  slot->analysis = analysis;
  state->memo_used++;
  return true;
}

static bool rational_enter(rational_intermediate_state *state, unsigned depth) {
  if (depth >= RATIONAL_INTERMEDIATE_DEPTH_LIMIT ||
      state->visited >= RATIONAL_INTERMEDIATE_VISIT_LIMIT) {
    state->limited = true;
    return false;
  }
  state->visited++;
  return true;
}

static ixs_check_result rational_range_fits(rational_intermediate_state *state,
                                            ixs_node *expr, int64_t lower,
                                            int64_t upper) {
  ixs_integer_range_result range;
  if (!ixs_bounds_get_integer_range(state->bounds, expr, &range) ||
      !range.has_lower || !range.has_upper)
    return IXS_CHECK_UNKNOWN;
  if (range.lower >= lower && range.upper <= upper)
    return IXS_CHECK_TRUE;
  if (range.upper < lower || range.lower > upper)
    return IXS_CHECK_FALSE;
  return IXS_CHECK_UNKNOWN;
}

static ixs_check_result rational_word_fits(rational_intermediate_state *state,
                                           ixs_node *expr) {
  return rational_range_fits(state, expr, state->word_lower, state->word_upper);
}

static ixs_check_result rational_signed_fits(rational_intermediate_state *state,
                                             ixs_node *expr) {
  return rational_range_fits(state, expr, state->signed_lower,
                             state->signed_upper);
}

static bool rational_is_nonnegative(rational_intermediate_state *state,
                                    ixs_node *expr) {
  ixs_interval range;
  if (ixs_bounds_check_defined(state->bounds, expr) != IXS_CHECK_TRUE)
    return false;
  range = ixs_bounds_get(state->bounds, expr);
  return range.valid && !range.lo_inf &&
         ixs_rat_cmp(range.lo_p, range.lo_q, 0, 1) >= 0;
}

static ixs_node *rational_make_integer(rational_intermediate_state *state,
                                       int64_t value) {
  ixs_node *result = ixs_node_int(state->ctx, value);
  if (!result)
    state->oom = true;
  return result;
}

static ixs_node *rational_make_binary(rational_intermediate_state *state,
                                      ixs_node *lhs, ixs_tag tag,
                                      ixs_node *rhs) {
  ixs_node *result;
  if (!lhs || !rhs)
    return NULL;
  result = tag == IXS_ADD ? simp_add(state->ctx, lhs, rhs)
                          : simp_mul(state->ctx, lhs, rhs);
  if (!result)
    state->oom = true;
  if (!result || ixs_node_is_sentinel(result))
    return NULL;
  return result;
}

static bool rational_checked_lcm(int64_t lhs, int64_t rhs, int64_t *result) {
  int64_t gcd;
  if (lhs <= 0 || rhs <= 0 || !result)
    return false;
  gcd = ixs_gcd(lhs, rhs);
  return gcd > 0 && ixs_safe_mul(lhs / gcd, rhs, result) && *result > 0;
}

static rational_intermediate_proof
rational_scale_proof(rational_intermediate_state *state,
                     rational_intermediate_proof proof, int64_t scale) {
  ixs_node *scale_node;
  ixs_node *numerator;
  if (!proof.valid || scale <= 0)
    return rational_invalid_proof();
  if (scale == 1)
    return proof;
  scale_node = rational_make_integer(state, scale);
  numerator = rational_make_binary(state, proof.numerator, IXS_MUL, scale_node);
  if (!numerator)
    return rational_invalid_proof();
  proof.numerator = numerator;
  proof.fits =
      rational_check_and(proof.fits, rational_word_fits(state, numerator));
  return proof;
}

static rational_intermediate_proof
rational_multiply_proofs(rational_intermediate_state *state,
                         rational_intermediate_proof lhs,
                         rational_intermediate_proof rhs) {
  rational_intermediate_proof result = rational_invalid_proof();
  if (!lhs.valid || !rhs.valid ||
      !ixs_safe_mul(lhs.denominator, rhs.denominator, &result.denominator) ||
      result.denominator <= 0)
    return result;
  result.numerator =
      rational_make_binary(state, lhs.numerator, IXS_MUL, rhs.numerator);
  if (!result.numerator)
    return rational_invalid_proof();
  result.fits = rational_check_and(lhs.fits, rhs.fits);
  result.fits = rational_check_and(result.fits,
                                   rational_word_fits(state, result.numerator));
  result.valid = true;
  return result;
}

static rational_intermediate_proof
rational_add_proofs(rational_intermediate_state *state,
                    rational_intermediate_proof lhs,
                    rational_intermediate_proof rhs) {
  rational_intermediate_proof result = rational_invalid_proof();
  rational_intermediate_proof scaled_lhs;
  rational_intermediate_proof scaled_rhs;
  if (!lhs.valid || !rhs.valid ||
      !rational_checked_lcm(lhs.denominator, rhs.denominator,
                            &result.denominator))
    return result;
  scaled_lhs =
      rational_scale_proof(state, lhs, result.denominator / lhs.denominator);
  scaled_rhs =
      rational_scale_proof(state, rhs, result.denominator / rhs.denominator);
  if (!scaled_lhs.valid || !scaled_rhs.valid)
    return rational_invalid_proof();
  result.numerator = rational_make_binary(state, scaled_lhs.numerator, IXS_ADD,
                                          scaled_rhs.numerator);
  if (!result.numerator)
    return rational_invalid_proof();
  result.fits = rational_check_and(scaled_lhs.fits, scaled_rhs.fits);
  result.fits = rational_check_and(result.fits,
                                   rational_word_fits(state, result.numerator));
  result.valid = true;
  return result;
}

static rational_intermediate_proof
rational_raise_proof(rational_intermediate_state *state,
                     rational_intermediate_proof base, int32_t exponent) {
  rational_intermediate_proof result = rational_invalid_proof();
  uint32_t i;
  if (!base.valid || exponent <= 0 ||
      (uint32_t)exponent > RATIONAL_INTERMEDIATE_POWER_LIMIT)
    return result;
  result.numerator = rational_make_integer(state, 1);
  if (!result.numerator)
    return rational_invalid_proof();
  result.denominator = 1;
  result.fits = IXS_CHECK_TRUE;
  result.valid = true;
  for (i = 0; result.valid && i < (uint32_t)exponent; i++)
    result = rational_multiply_proofs(state, result, base);
  return result;
}

static rational_intermediate_proof
rational_rounded_proof(rational_intermediate_state *state, ixs_node *expr,
                       rational_intermediate_proof child, bool is_ceil) {
  ixs_node *child_expr = expr->u.unary.arg;
  rational_intermediate_proof result = rational_invalid_proof();
  bool nonnegative;
  if (!child.valid)
    return result;
  nonnegative = rational_is_nonnegative(state, child_expr);
  result.fits = rational_check_and(child.fits,
                                   rational_word_fits(state, child.numerator));
  if (!nonnegative)
    result.fits = rational_check_and(
        result.fits, rational_signed_fits(state, child.numerator));
  if (is_ceil && child.denominator > 1) {
    ixs_node *bias =
        rational_make_integer(state, child.denominator - INT64_C(1));
    ixs_node *biased =
        rational_make_binary(state, child.numerator, IXS_ADD, bias);
    if (!biased)
      return rational_invalid_proof();
    result.fits =
        rational_check_and(result.fits, rational_word_fits(state, biased));
    if (!nonnegative)
      result.fits =
          rational_check_and(result.fits, rational_signed_fits(state, biased));
  }
  result.numerator = expr;
  result.denominator = 1;
  result.fits =
      rational_check_and(result.fits, rational_word_fits(state, expr));
  result.valid = true;
  return result;
}

static bool rational_is_power_of_two(uint64_t value) {
  return value != 0 && (value & (value - UINT64_C(1))) == 0;
}

static bool
rational_mod_truncates_dividend(const rational_intermediate_state *state,
                                const ixs_node *expr) {
  int64_t divisor;
  if (expr->tag != IXS_MOD || expr->u.binary.rhs->tag != IXS_INT)
    return false;
  divisor = expr->u.binary.rhs->u.ival;
  return divisor > 0 && rational_is_power_of_two((uint64_t)divisor) &&
         (uint64_t)divisor <= state->word_modulus;
}

static rational_intermediate_proof
rational_mod_proof(rational_intermediate_state *state, ixs_node *expr,
                   rational_intermediate_proof lhs,
                   rational_intermediate_proof rhs) {
  rational_intermediate_proof result = rational_invalid_proof();
  ixs_check_result operands;
  if (!lhs.valid || !rhs.valid ||
      ixs_bounds_check_integer_valued(state->bounds, expr) != IXS_CHECK_TRUE)
    return result;
  operands = rational_mod_truncates_dividend(state, expr)
                 ? rhs.fits
                 : rational_check_and(lhs.fits, rhs.fits);
  result.numerator = expr;
  result.denominator = 1;
  result.fits = rational_check_and(operands, rational_word_fits(state, expr));
  result.valid = true;
  return result;
}

static rational_intermediate_analysis
rational_analyze(rational_intermediate_state *state, ixs_node *expr,
                 unsigned depth);

static void rational_merge_child(rational_intermediate_analysis *parent,
                                 rational_intermediate_analysis child) {
  parent->contains_materialization |= child.contains_materialization;
  parent->owns_materialization |= child.owns_materialization;
  parent->islands_fit =
      rational_check_and(parent->islands_fit, child.islands_fit);
}

static rational_intermediate_analysis
rational_analyze_add(rational_intermediate_state *state, ixs_node *expr,
                     unsigned depth) {
  rational_intermediate_analysis result = rational_empty_analysis();
  rational_intermediate_analysis child =
      rational_analyze(state, expr->u.add.coeff, depth + 1u);
  uint32_t i;
  result.proof = child.proof;
  rational_merge_child(&result, child);
  for (i = 0; i < expr->u.add.nterms; i++) {
    rational_intermediate_analysis coefficient =
        rational_analyze(state, expr->u.add.terms[i].coeff, depth + 1u);
    rational_intermediate_analysis term =
        rational_analyze(state, expr->u.add.terms[i].term, depth + 1u);
    rational_intermediate_proof product =
        rational_multiply_proofs(state, coefficient.proof, term.proof);
    result.proof = rational_add_proofs(state, result.proof, product);
    rational_merge_child(&result, coefficient);
    rational_merge_child(&result, term);
  }
  if (result.owns_materialization)
    result.islands_fit = rational_proof_fit(result.proof);
  return result;
}

static rational_intermediate_analysis
rational_analyze_mul(rational_intermediate_state *state, ixs_node *expr,
                     unsigned depth) {
  rational_intermediate_analysis result = rational_empty_analysis();
  rational_intermediate_analysis child =
      rational_analyze(state, expr->u.mul.coeff, depth + 1u);
  uint32_t i;
  result.proof = child.proof;
  rational_merge_child(&result, child);
  for (i = 0; i < expr->u.mul.nfactors; i++) {
    rational_intermediate_analysis base =
        rational_analyze(state, expr->u.mul.factors[i].base, depth + 1u);
    rational_intermediate_proof power =
        rational_raise_proof(state, base.proof, expr->u.mul.factors[i].exp);
    result.proof = rational_multiply_proofs(state, result.proof, power);
    rational_merge_child(&result, base);
  }
  if (result.owns_materialization)
    result.islands_fit = rational_proof_fit(result.proof);
  return result;
}

static rational_intermediate_analysis
rational_analyze_rounded(rational_intermediate_state *state, ixs_node *expr,
                         unsigned depth, bool is_ceil) {
  rational_intermediate_analysis child =
      rational_analyze(state, expr->u.unary.arg, depth + 1u);
  rational_intermediate_analysis result = rational_empty_analysis();
  result.contains_materialization = child.contains_materialization;
  result.proof = rational_rounded_proof(state, expr, child.proof, is_ceil);
  result.islands_fit = rational_proof_fit(result.proof);
  return result;
}

static rational_intermediate_analysis
rational_analyze_mod(rational_intermediate_state *state, ixs_node *expr,
                     unsigned depth) {
  rational_intermediate_analysis lhs =
      rational_analyze(state, expr->u.binary.lhs, depth + 1u);
  rational_intermediate_analysis rhs =
      rational_analyze(state, expr->u.binary.rhs, depth + 1u);
  rational_intermediate_analysis result = rational_empty_analysis();
  result.contains_materialization =
      lhs.contains_materialization || rhs.contains_materialization;
  /* Mod owns a surrounding rational island only through its dividend. */
  result.owns_materialization = lhs.owns_materialization;
  result.proof = rational_mod_proof(state, expr, lhs.proof, rhs.proof);
  result.islands_fit = rational_check_and(lhs.islands_fit, rhs.islands_fit);
  return result;
}

static rational_intermediate_analysis
rational_analyze_bitwise(rational_intermediate_state *state, ixs_node *expr,
                         unsigned depth) {
  rational_intermediate_analysis result = rational_empty_analysis();
  ixs_check_result operands_fit = IXS_CHECK_TRUE;
  uint32_t i;
  for (i = 0; i < expr->u.assoc.nargs; i++) {
    rational_intermediate_analysis child =
        rational_analyze(state, expr->u.assoc.args[i], depth + 1u);
    rational_merge_child(&result, child);
    operands_fit =
        rational_check_and(operands_fit, rational_proof_fit(child.proof));
  }
  /* Bitwise operations terminate, rather than own, a rational island. */
  result.owns_materialization = false;
  if (ixs_bounds_check_integer_valued(state->bounds, expr) == IXS_CHECK_TRUE) {
    result.proof.numerator = expr;
    result.proof.denominator = 1;
    result.proof.fits =
        rational_check_and(operands_fit, rational_word_fits(state, expr));
    result.proof.valid = true;
  }
  return result;
}

static rational_intermediate_analysis
rational_analyze_piecewise(rational_intermediate_state *state, ixs_node *expr,
                           unsigned depth) {
  rational_intermediate_analysis result = rational_empty_analysis();
  rational_intermediate_analysis *children;
  ixs_node **values;
  ixs_node **conditions;
  int64_t denominator = 1;
  uint32_t count = expr->u.pw.ncases;
  uint32_t i;
  if (count == 0 || count > RATIONAL_INTERMEDIATE_CASE_LIMIT) {
    state->limited = true;
    return result;
  }
  children = ixs_arena_alloc(state->bounds->scratch,
                             (size_t)count * sizeof(*children), sizeof(void *));
  values = ixs_arena_alloc(state->bounds->scratch,
                           (size_t)count * sizeof(*values), sizeof(void *));
  conditions =
      ixs_arena_alloc(state->bounds->scratch,
                      (size_t)count * sizeof(*conditions), sizeof(void *));
  if (!children || !values || !conditions) {
    state->oom = true;
    return result;
  }
  for (i = 0; i < count; i++) {
    children[i] =
        rational_analyze(state, expr->u.pw.cases[i].value, depth + 1u);
    rational_merge_child(&result, children[i]);
    if (!children[i].proof.valid ||
        !rational_checked_lcm(denominator, children[i].proof.denominator,
                              &denominator))
      denominator = 0;
  }
  result.proof = rational_invalid_proof();
  if (denominator > 0) {
    ixs_check_result fits = IXS_CHECK_TRUE;
    for (i = 0; i < count; i++) {
      rational_intermediate_proof scaled =
          rational_scale_proof(state, children[i].proof,
                               denominator / children[i].proof.denominator);
      if (!scaled.valid) {
        denominator = 0;
        break;
      }
      fits = rational_check_and(fits, scaled.fits);
      values[i] = scaled.numerator;
      conditions[i] = expr->u.pw.cases[i].cond;
    }
    if (denominator > 0) {
      ixs_node *numerator = simp_pw(state->ctx, count, values, conditions);
      if (!numerator)
        state->oom = true;
      if (numerator && !ixs_node_is_sentinel(numerator)) {
        result.proof.numerator = numerator;
        result.proof.denominator = denominator;
        result.proof.fits = rational_check_and(
            fits, rational_word_fits(state, result.proof.numerator));
        result.proof.valid = true;
      }
    }
  }
  if (result.owns_materialization)
    result.islands_fit = rational_proof_fit(result.proof);
  return result;
}

static rational_intermediate_analysis
rational_analyze_uncached(rational_intermediate_state *state, ixs_node *expr,
                          unsigned depth) {
  rational_intermediate_analysis result = rational_empty_analysis();
  int64_t denominator;
  switch (expr->tag) {
  case IXS_INT:
  case IXS_SYM:
    result.proof.numerator = expr;
    result.proof.denominator = 1;
    result.proof.fits = rational_word_fits(state, expr);
    result.proof.valid = true;
    return result;
  case IXS_RAT:
    denominator = expr->u.rat.q;
    if (denominator <= 0)
      return result;
    /* A literal supplies a proof to an enclosing island but performs no
     * intermediate arithmetic by itself.  islands_fit therefore stays TRUE. */
    result.contains_materialization = denominator != 1;
    result.owns_materialization = result.contains_materialization;
    result.proof.numerator = rational_make_integer(state, expr->u.rat.p);
    if (!result.proof.numerator)
      return result;
    result.proof.denominator = denominator;
    result.proof.fits = rational_word_fits(state, result.proof.numerator);
    result.proof.valid = true;
    return result;
  case IXS_ADD:
    return rational_analyze_add(state, expr, depth);
  case IXS_MUL:
    return rational_analyze_mul(state, expr, depth);
  case IXS_FLOOR:
    return rational_analyze_rounded(state, expr, depth, false);
  case IXS_CEIL:
    return rational_analyze_rounded(state, expr, depth, true);
  case IXS_MOD:
    return rational_analyze_mod(state, expr, depth);
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
    return rational_analyze_bitwise(state, expr, depth);
  case IXS_PIECEWISE:
    return rational_analyze_piecewise(state, expr, depth);
  default:
    return result;
  }
}

static rational_intermediate_analysis
rational_analyze(rational_intermediate_state *state, ixs_node *expr,
                 unsigned depth) {
  rational_intermediate_analysis result = rational_empty_analysis();
  rational_intermediate_memo_entry *cached;
  if (!expr)
    return result;
  cached = rational_memo_find(state, expr);
  if (cached)
    return cached->analysis;
  if (!rational_enter(state, depth))
    return result;
  result = rational_analyze_uncached(state, expr, depth);
  if (!state->limited && !state->oom)
    (void)rational_memo_store(state, expr, result);
  return result;
}

IXS_STATIC ixs_check_result ixs_bounds_check_rational_intermediates(
    ixs_ctx *ctx, ixs_bounds *bounds, ixs_node *expr, uint32_t word_bits) {
  rational_intermediate_state state;
  rational_intermediate_analysis analysis;
  uint64_t signed_modulus;
  if (!ctx || !bounds || !expr || word_bits < 2u || word_bits > 62u)
    return IXS_CHECK_UNKNOWN;
  memset(&state, 0, sizeof(state));
  state.ctx = ctx;
  state.bounds = bounds;
  state.word_modulus = UINT64_C(1) << word_bits;
  signed_modulus = UINT64_C(1) << (word_bits - 1u);
  state.word_lower = -(int64_t)signed_modulus;
  state.word_upper = (int64_t)(state.word_modulus - UINT64_C(1));
  state.signed_lower = state.word_lower;
  state.signed_upper = (int64_t)(signed_modulus - UINT64_C(1));
  analysis = rational_analyze(&state, expr, 0);
  if (state.limited || state.oom || bounds->oom)
    return IXS_CHECK_UNKNOWN;
  if (!analysis.contains_materialization)
    return IXS_CHECK_TRUE;
  return analysis.islands_fit;
}
