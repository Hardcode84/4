/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "rational_intermediates.h"

#include "rational.h"
#include "simplify.h"

#include <limits.h>
#include <string.h>

#define RATIONAL_MEMO_INIT_CAP 64u
#define RATIONAL_STACK_INIT_CAP 64u

typedef struct {
  ixs_node *numerator;
  int64_t denominator;
  bool valid;
} rational_proof;

/* closed_fit contains obligations that are not represented by proof.  An open
 * rational island is deliberately kept separate: an enclosing Add, Mul, or
 * Piecewise first builds its final common-denominator numerator, then validates
 * that final tree.  This prevents a construction-order proof from becoming a
 * claim about a different consumer materialization order. */
typedef struct {
  rational_proof proof;
  ixs_check_result closed_fit;
  ixs_check_result full_fit;
  bool contains_materialization;
  bool owns_materialization;
  bool nonnegative;
} rational_analysis;

typedef enum {
  RATIONAL_MEMO_EMPTY,
  RATIONAL_MEMO_ACTIVE,
  RATIONAL_MEMO_DONE
} rational_memo_state;

typedef struct {
  ixs_node *expr;
  rational_analysis analysis;
  uint8_t state;
} rational_analysis_entry;

typedef struct {
  ixs_node *expr;
  ixs_check_result result;
  uint8_t state;
} rational_validation_entry;

typedef struct {
  ixs_node *expr;
  size_t next_child;
  size_t child_count;
  ixs_node *exact_numerator;
  ixs_node *exact_denominator;
  bool exact_checked;
} rational_analysis_frame;

typedef struct {
  ixs_node *expr;
  size_t next_child;
  size_t child_count;
} rational_validation_frame;

typedef struct {
  int64_t lower;
  int64_t upper;
  bool known;
} rational_range;

typedef struct {
  ixs_ctx *ctx;
  ixs_bounds *bounds;
  int64_t word_lower;
  int64_t word_upper;
  int64_t signed_lower;
  int64_t signed_upper;
  uint64_t word_modulus;

  rational_analysis_entry *analysis_memo;
  size_t analysis_memo_cap;
  size_t analysis_memo_used;
  rational_analysis_frame *analysis_stack;
  size_t analysis_stack_cap;
  size_t analysis_stack_used;

  rational_validation_entry *validation_memo;
  size_t validation_memo_cap;
  size_t validation_memo_used;
  rational_validation_frame *validation_stack;
  size_t validation_stack_cap;
  size_t validation_stack_used;

  bool cycle;
  bool oom;
} rational_state;

static ixs_check_result rational_check_and(ixs_check_result lhs,
                                           ixs_check_result rhs) {
  if (lhs == IXS_CHECK_FALSE || rhs == IXS_CHECK_FALSE)
    return IXS_CHECK_FALSE;
  if (lhs == IXS_CHECK_TRUE && rhs == IXS_CHECK_TRUE)
    return IXS_CHECK_TRUE;
  return IXS_CHECK_UNKNOWN;
}

static rational_proof rational_invalid_proof(void) {
  rational_proof proof;
  proof.numerator = NULL;
  proof.denominator = 1;
  proof.valid = false;
  return proof;
}

static rational_analysis rational_empty_analysis(void) {
  rational_analysis analysis;
  analysis.proof = rational_invalid_proof();
  analysis.closed_fit = IXS_CHECK_TRUE;
  analysis.full_fit = IXS_CHECK_UNKNOWN;
  analysis.contains_materialization = false;
  analysis.owns_materialization = false;
  analysis.nonnegative = false;
  return analysis;
}

static size_t rational_pointer_hash(const ixs_node *expr) {
  uint64_t value = (uint64_t)(uintptr_t)expr;
  value ^= value >> 33;
  value *= UINT64_C(0xff51afd7ed558ccd);
  value ^= value >> 33;
  return (size_t)value;
}

static bool rational_allocation_size(rational_state *state, size_t count,
                                     size_t element_size, size_t *bytes) {
  if (!bytes || (element_size != 0 && count > (size_t)-1 / element_size)) {
    state->oom = true;
    return false;
  }
  *bytes = count * element_size;
  return true;
}

static size_t rational_next_capacity(rational_state *state, size_t current,
                                     size_t needed) {
  size_t capacity = current ? current : RATIONAL_STACK_INIT_CAP;
  while (capacity < needed) {
    if (capacity > (size_t)-1 / 2u) {
      state->oom = true;
      return 0;
    }
    capacity *= 2u;
  }
  return capacity;
}

static rational_analysis_entry *
rational_analysis_slot(rational_analysis_entry *memo, size_t cap,
                       const ixs_node *expr) {
  size_t index = rational_pointer_hash(expr) & (cap - 1u);
  while (memo[index].expr && memo[index].expr != expr)
    index = (index + 1u) & (cap - 1u);
  return &memo[index];
}

static bool rational_analysis_memo_grow(rational_state *state) {
  size_t new_cap = state->analysis_memo_cap ? state->analysis_memo_cap * 2u
                                            : RATIONAL_MEMO_INIT_CAP;
  rational_analysis_entry *memo;
  size_t bytes;
  size_t i;
  if (new_cap <= state->analysis_memo_cap ||
      !rational_allocation_size(state, new_cap, sizeof(*memo), &bytes))
    return false;
  memo = ixs_arena_alloc(state->bounds->scratch, bytes, sizeof(void *));
  if (!memo) {
    state->oom = true;
    return false;
  }
  memset(memo, 0, bytes);
  for (i = 0; i < state->analysis_memo_cap; i++) {
    if (state->analysis_memo[i].expr) {
      rational_analysis_entry *slot =
          rational_analysis_slot(memo, new_cap, state->analysis_memo[i].expr);
      *slot = state->analysis_memo[i];
    }
  }
  state->analysis_memo = memo;
  state->analysis_memo_cap = new_cap;
  return true;
}

static rational_analysis_entry *rational_analysis_find(rational_state *state,
                                                       const ixs_node *expr) {
  rational_analysis_entry *slot;
  if (!state->analysis_memo_cap)
    return NULL;
  slot = rational_analysis_slot(state->analysis_memo, state->analysis_memo_cap,
                                expr);
  return slot->expr ? slot : NULL;
}

static rational_analysis_entry *rational_analysis_insert(rational_state *state,
                                                         ixs_node *expr) {
  rational_analysis_entry *slot;
  if (!state->analysis_memo_cap && !rational_analysis_memo_grow(state))
    return NULL;
  slot = rational_analysis_slot(state->analysis_memo, state->analysis_memo_cap,
                                expr);
  if (slot->expr)
    return slot;
  if (state->analysis_memo_used + 1u >
      state->analysis_memo_cap - state->analysis_memo_cap / 4u) {
    if (!rational_analysis_memo_grow(state))
      return NULL;
    slot = rational_analysis_slot(state->analysis_memo,
                                  state->analysis_memo_cap, expr);
  }
  slot->expr = expr;
  slot->analysis = rational_empty_analysis();
  slot->state = RATIONAL_MEMO_ACTIVE;
  state->analysis_memo_used++;
  return slot;
}

static rational_validation_entry *
rational_validation_slot(rational_validation_entry *memo, size_t cap,
                         const ixs_node *expr) {
  size_t index = rational_pointer_hash(expr) & (cap - 1u);
  while (memo[index].expr && memo[index].expr != expr)
    index = (index + 1u) & (cap - 1u);
  return &memo[index];
}

static bool rational_validation_memo_grow(rational_state *state) {
  size_t new_cap = state->validation_memo_cap ? state->validation_memo_cap * 2u
                                              : RATIONAL_MEMO_INIT_CAP;
  rational_validation_entry *memo;
  size_t bytes;
  size_t i;
  if (new_cap <= state->validation_memo_cap ||
      !rational_allocation_size(state, new_cap, sizeof(*memo), &bytes))
    return false;
  memo = ixs_arena_alloc(state->bounds->scratch, bytes, sizeof(void *));
  if (!memo) {
    state->oom = true;
    return false;
  }
  memset(memo, 0, bytes);
  for (i = 0; i < state->validation_memo_cap; i++) {
    if (state->validation_memo[i].expr) {
      rational_validation_entry *slot = rational_validation_slot(
          memo, new_cap, state->validation_memo[i].expr);
      *slot = state->validation_memo[i];
    }
  }
  state->validation_memo = memo;
  state->validation_memo_cap = new_cap;
  return true;
}

static rational_validation_entry *
rational_validation_find(rational_state *state, const ixs_node *expr) {
  rational_validation_entry *slot;
  if (!state->validation_memo_cap)
    return NULL;
  slot = rational_validation_slot(state->validation_memo,
                                  state->validation_memo_cap, expr);
  return slot->expr ? slot : NULL;
}

static rational_validation_entry *
rational_validation_insert(rational_state *state, ixs_node *expr) {
  rational_validation_entry *slot;
  if (!state->validation_memo_cap && !rational_validation_memo_grow(state))
    return NULL;
  slot = rational_validation_slot(state->validation_memo,
                                  state->validation_memo_cap, expr);
  if (slot->expr)
    return slot;
  if (state->validation_memo_used + 1u >
      state->validation_memo_cap - state->validation_memo_cap / 4u) {
    if (!rational_validation_memo_grow(state))
      return NULL;
    slot = rational_validation_slot(state->validation_memo,
                                    state->validation_memo_cap, expr);
  }
  slot->expr = expr;
  slot->result = IXS_CHECK_UNKNOWN;
  slot->state = RATIONAL_MEMO_ACTIVE;
  state->validation_memo_used++;
  return slot;
}

static bool rational_analysis_stack_push(rational_state *state,
                                         rational_analysis_frame frame) {
  size_t needed = state->analysis_stack_used + 1u;
  if (needed > state->analysis_stack_cap) {
    size_t new_cap =
        rational_next_capacity(state, state->analysis_stack_cap, needed);
    size_t old_bytes;
    size_t new_bytes;
    rational_analysis_frame *grown;
    if (!new_cap ||
        !rational_allocation_size(state, state->analysis_stack_cap,
                                  sizeof(*grown), &old_bytes) ||
        !rational_allocation_size(state, new_cap, sizeof(*grown), &new_bytes))
      return false;
    grown = ixs_arena_grow(state->bounds->scratch, state->analysis_stack,
                           old_bytes, new_bytes, sizeof(void *));
    if (!grown) {
      state->oom = true;
      return false;
    }
    state->analysis_stack = grown;
    state->analysis_stack_cap = new_cap;
  }
  state->analysis_stack[state->analysis_stack_used++] = frame;
  return true;
}

static bool rational_validation_stack_push(rational_state *state,
                                           rational_validation_frame frame) {
  size_t needed = state->validation_stack_used + 1u;
  if (needed > state->validation_stack_cap) {
    size_t new_cap =
        rational_next_capacity(state, state->validation_stack_cap, needed);
    size_t old_bytes;
    size_t new_bytes;
    rational_validation_frame *grown;
    if (!new_cap ||
        !rational_allocation_size(state, state->validation_stack_cap,
                                  sizeof(*grown), &old_bytes) ||
        !rational_allocation_size(state, new_cap, sizeof(*grown), &new_bytes))
      return false;
    grown = ixs_arena_grow(state->bounds->scratch, state->validation_stack,
                           old_bytes, new_bytes, sizeof(void *));
    if (!grown) {
      state->oom = true;
      return false;
    }
    state->validation_stack = grown;
    state->validation_stack_cap = new_cap;
  }
  state->validation_stack[state->validation_stack_used++] = frame;
  return true;
}

static bool rational_assoc_shape_ok(const ixs_node *expr) {
  switch (expr->tag) {
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
    return expr->u.assoc.nargs != 0 && expr->u.assoc.args;
  default:
    return false;
  }
}

static bool rational_cmp_op_ok(ixs_cmp_op op) {
  switch (op) {
  case IXS_CMP_GT:
  case IXS_CMP_GE:
  case IXS_CMP_LT:
  case IXS_CMP_LE:
  case IXS_CMP_EQ:
  case IXS_CMP_NE:
    return true;
  }
  return false;
}

static bool rational_node_shape_ok(rational_state *state,
                                   const ixs_node *expr) {
  if (!expr || !ixs_ctx_owns_node(state->ctx, expr) ||
      ixs_node_is_sentinel(expr) ||
      (expr->properties & IXS_NODE_PROPERTY_VALID) == 0)
    return false;
  switch (expr->tag) {
  case IXS_INT:
  case IXS_RAT:
  case IXS_SYM:
    return true;
  case IXS_ADD:
    return expr->u.add.coeff && (expr->u.add.nterms == 0 || expr->u.add.terms);
  case IXS_MUL:
    return expr->u.mul.coeff &&
           (expr->u.mul.nfactors == 0 || expr->u.mul.factors);
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
    return expr->u.unary.arg != NULL;
  case IXS_MOD:
    return expr->u.binary.lhs && expr->u.binary.rhs;
  case IXS_CMP:
    return expr->u.binary.lhs && expr->u.binary.rhs &&
           rational_cmp_op_ok(expr->u.binary.cmp_op);
  case IXS_PIECEWISE:
    return expr->u.pw.ncases != 0 && expr->u.pw.cases;
  case IXS_NOT:
    return expr->u.unary_bool.arg != NULL;
  default:
    return rational_assoc_shape_ok(expr);
  }
}

static bool rational_direct_child_count(rational_state *state,
                                        const ixs_node *expr, size_t *count) {
  size_t n;
  if (!count || !rational_node_shape_ok(state, expr))
    return false;
  switch (expr->tag) {
  case IXS_ADD:
    n = expr->u.add.nterms;
    if (n > ((size_t)-1 - 1u) / 2u)
      return false;
    *count = 1u + 2u * n;
    return true;
  case IXS_MUL:
    *count = 1u + (size_t)expr->u.mul.nfactors;
    return true;
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
  case IXS_NOT:
    *count = 1u;
    return true;
  case IXS_MOD:
  case IXS_CMP:
    *count = 2u;
    return true;
  case IXS_PIECEWISE:
    n = expr->u.pw.ncases;
    if (n > (size_t)-1 / 2u)
      return false;
    *count = 2u * n;
    return true;
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
    *count = expr->u.assoc.nargs;
    return true;
  default:
    *count = 0;
    return true;
  }
}

static ixs_node *rational_direct_child(const ixs_node *expr, size_t index) {
  switch (expr->tag) {
  case IXS_ADD:
    if (index == 0)
      return expr->u.add.coeff;
    index--;
    return (index & 1u) ? expr->u.add.terms[index / 2u].term
                        : expr->u.add.terms[index / 2u].coeff;
  case IXS_MUL:
    return index == 0 ? expr->u.mul.coeff
                      : expr->u.mul.factors[index - 1u].base;
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
    return expr->u.unary.arg;
  case IXS_NOT:
    return expr->u.unary_bool.arg;
  case IXS_MOD:
  case IXS_CMP:
    return index == 0 ? expr->u.binary.lhs : expr->u.binary.rhs;
  case IXS_PIECEWISE:
    return (index & 1u) ? expr->u.pw.cases[index / 2u].cond
                        : expr->u.pw.cases[index / 2u].value;
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
    return expr->u.assoc.args[index];
  default:
    return NULL;
  }
}

static rational_range rational_unknown_range(void) {
  rational_range range;
  range.lower = 0;
  range.upper = 0;
  range.known = false;
  return range;
}

static rational_range rational_get_range(rational_state *state,
                                         ixs_node *expr) {
  ixs_integer_range_result result;
  rational_range range = rational_unknown_range();
  if (ixs_bounds_get_integer_range(state->bounds, expr, &result) &&
      result.has_lower && result.has_upper) {
    range.lower = result.lower;
    range.upper = result.upper;
    range.known = result.lower <= result.upper;
  }
  return range;
}

static ixs_check_result
rational_range_fits_bounds(rational_range range, int64_t lower, int64_t upper) {
  if (!range.known)
    return IXS_CHECK_UNKNOWN;
  if (range.lower >= lower && range.upper <= upper)
    return IXS_CHECK_TRUE;
  if (range.upper < lower || range.lower > upper)
    return IXS_CHECK_FALSE;
  return IXS_CHECK_UNKNOWN;
}

static ixs_check_result rational_word_range_fits(rational_state *state,
                                                 rational_range range) {
  return rational_range_fits_bounds(range, state->word_lower,
                                    state->word_upper);
}

static ixs_check_result rational_word_fits(rational_state *state,
                                           ixs_node *expr) {
  return rational_word_range_fits(state, rational_get_range(state, expr));
}

static ixs_check_result rational_signed_fits(rational_state *state,
                                             ixs_node *expr) {
  return rational_range_fits_bounds(rational_get_range(state, expr),
                                    state->signed_lower, state->signed_upper);
}

static bool rational_is_nonnegative(rational_state *state, ixs_node *expr) {
  ixs_interval range;
  if (ixs_bounds_check_defined(state->bounds, expr) != IXS_CHECK_TRUE)
    return false;
  range = ixs_bounds_get(state->bounds, expr);
  return range.valid && !range.lo_inf &&
         ixs_rat_cmp(range.lo_p, range.lo_q, 0, 1) >= 0;
}

static ixs_node *rational_make_integer(rational_state *state, int64_t value) {
  ixs_node *result = ixs_node_int(state->ctx, value);
  if (!result)
    state->oom = true;
  return result;
}

static ixs_node *rational_make_binary(rational_state *state, ixs_node *lhs,
                                      ixs_tag tag, ixs_node *rhs) {
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

static bool rational_checked_positive_power(int64_t base, uint32_t exponent,
                                            int64_t *result) {
  int64_t acc = 1;
  int64_t factor = base;
  uint32_t remaining = exponent;
  if (base <= 0 || !result)
    return false;
  while (remaining) {
    if ((remaining & 1u) && !ixs_safe_mul(acc, factor, &acc))
      return false;
    remaining >>= 1u;
    if (remaining && !ixs_safe_mul(factor, factor, &factor))
      return false;
  }
  *result = acc;
  return true;
}

static rational_proof rational_scale_proof(rational_state *state,
                                           rational_proof proof,
                                           int64_t scale) {
  ixs_node *scale_node;
  if (!proof.valid || scale <= 0)
    return rational_invalid_proof();
  if (scale == 1)
    return proof;
  scale_node = rational_make_integer(state, scale);
  proof.numerator =
      rational_make_binary(state, proof.numerator, IXS_MUL, scale_node);
  if (!proof.numerator)
    return rational_invalid_proof();
  return proof;
}

static rational_proof rational_multiply_proofs(rational_state *state,
                                               rational_proof lhs,
                                               rational_proof rhs) {
  rational_proof result = rational_invalid_proof();
  if (!lhs.valid || !rhs.valid ||
      !ixs_safe_mul(lhs.denominator, rhs.denominator, &result.denominator) ||
      result.denominator <= 0)
    return result;
  result.numerator =
      rational_make_binary(state, lhs.numerator, IXS_MUL, rhs.numerator);
  result.valid = result.numerator != NULL;
  return result;
}

static ixs_node *rational_power_node(rational_state *state, ixs_node *base,
                                     uint32_t exponent) {
  ixs_node *acc = rational_make_integer(state, 1);
  ixs_node *factor = base;
  uint32_t remaining = exponent;
  if (!acc)
    return NULL;
  while (remaining) {
    if (remaining & 1u) {
      acc = rational_make_binary(state, acc, IXS_MUL, factor);
      if (!acc)
        return NULL;
    }
    remaining >>= 1u;
    if (remaining) {
      factor = rational_make_binary(state, factor, IXS_MUL, factor);
      if (!factor)
        return NULL;
    }
  }
  return acc;
}

static rational_proof rational_raise_proof(rational_state *state,
                                           rational_proof base,
                                           int32_t exponent) {
  rational_proof result = rational_invalid_proof();
  uint32_t magnitude;
  if (!base.valid || exponent == 0)
    return result;
  magnitude =
      exponent > 0 ? (uint32_t)exponent : (uint32_t)(-(int64_t)exponent);
  if (exponent < 0) {
    ixs_integer_range_result range;
    int64_t value;
    if (!ixs_bounds_get_integer_range(state->bounds, base.numerator, &range) ||
        !range.has_lower || !range.has_upper || range.lower != range.upper ||
        range.lower == 0 || range.lower == INT64_MIN)
      return result;
    value = range.lower;
    base.numerator = rational_make_integer(state, value < 0 ? -base.denominator
                                                            : base.denominator);
    base.denominator = value < 0 ? -value : value;
    if (!base.numerator || base.denominator <= 0)
      return rational_invalid_proof();
  }
  if (!rational_checked_positive_power(base.denominator, magnitude,
                                       &result.denominator))
    return result;
  result.numerator = rational_power_node(state, base.numerator, magnitude);
  result.valid = result.numerator != NULL;
  return result;
}

static bool rational_checked_power(int64_t base, uint32_t exponent,
                                   int64_t *result) {
  int64_t acc = 1;
  int64_t factor = base;
  uint32_t remaining = exponent;
  if (!result)
    return false;
  while (remaining) {
    if ((remaining & 1u) && !ixs_safe_mul(acc, factor, &acc))
      return false;
    remaining >>= 1u;
    if (remaining && !ixs_safe_mul(factor, factor, &factor))
      return false;
  }
  *result = acc;
  return true;
}

static rational_range rational_range_hull(rational_range lhs,
                                          rational_range rhs) {
  if (!lhs.known || !rhs.known)
    return rational_unknown_range();
  if (rhs.lower < lhs.lower)
    lhs.lower = rhs.lower;
  if (rhs.upper > lhs.upper)
    lhs.upper = rhs.upper;
  return lhs;
}

static rational_range rational_range_multiply(rational_range lhs,
                                              rational_range rhs) {
  int64_t products[4];
  rational_range result = rational_unknown_range();
  size_t i;
  if (!lhs.known || !rhs.known ||
      !ixs_safe_mul(lhs.lower, rhs.lower, &products[0]) ||
      !ixs_safe_mul(lhs.lower, rhs.upper, &products[1]) ||
      !ixs_safe_mul(lhs.upper, rhs.lower, &products[2]) ||
      !ixs_safe_mul(lhs.upper, rhs.upper, &products[3]))
    return result;
  result.lower = products[0];
  result.upper = products[0];
  result.known = true;
  for (i = 1; i < 4u; i++) {
    if (products[i] < result.lower)
      result.lower = products[i];
    if (products[i] > result.upper)
      result.upper = products[i];
  }
  return result;
}

/* Hull of every base^k for 0 <= k <= exponent.  Only O(log exponent)
 * checked arithmetic is needed: extrema occur at an endpoint and at the
 * largest relevant odd/even exponent. */
static rational_range rational_power_closure(rational_range base,
                                             uint32_t exponent) {
  rational_range result;
  int64_t value;
  uint32_t even_exponent;
  uint32_t odd_exponent;
  if (!base.known || exponent == 0)
    return rational_unknown_range();
  result.lower = 1;
  result.upper = 1;
  result.known = true;
  result = rational_range_hull(result, base);

  if (base.upper > 1) {
    if (!rational_checked_power(base.upper, exponent, &value))
      return rational_unknown_range();
    if (value > result.upper)
      result.upper = value;
  }

  if (base.lower < -1) {
    odd_exponent = (exponent & 1u) ? exponent : exponent - 1u;
    if (odd_exponent &&
        !rational_checked_power(base.lower, odd_exponent, &value))
      return rational_unknown_range();
    if (odd_exponent && value < result.lower)
      result.lower = value;
    even_exponent = (exponent & 1u) ? exponent - 1u : exponent;
    if (even_exponent &&
        !rational_checked_power(base.lower, even_exponent, &value))
      return rational_unknown_range();
    if (even_exponent && value > result.upper)
      result.upper = value;
  }

  if (base.lower <= 0 && base.upper >= 0 && result.lower > 0)
    result.lower = 0;
  return result;
}

static ixs_check_result rational_subset_product_fit(rational_state *state,
                                                    const ixs_node *expr) {
  rational_range closure;
  rational_range factor;
  uint32_t i;
  if (expr->tag != IXS_MUL)
    return IXS_CHECK_UNKNOWN;
  closure.lower = 1;
  closure.upper = 1;
  closure.known = true;
  factor =
      rational_power_closure(rational_get_range(state, expr->u.mul.coeff), 1u);
  closure = rational_range_multiply(closure, factor);
  for (i = 0; closure.known && i < expr->u.mul.nfactors; i++) {
    int32_t exponent = expr->u.mul.factors[i].exp;
    if (exponent <= 0)
      return IXS_CHECK_UNKNOWN;
    factor = rational_power_closure(
        rational_get_range(state, expr->u.mul.factors[i].base),
        (uint32_t)exponent);
    closure = rational_range_multiply(closure, factor);
  }
  /* A closure is an over-approximation.  Escaping the word is not a false
   * witness; it merely withholds the narrow proof. */
  return rational_word_range_fits(state, closure) == IXS_CHECK_TRUE
             ? IXS_CHECK_TRUE
             : IXS_CHECK_UNKNOWN;
}

static ixs_check_result rational_pair_product_fit(rational_state *state,
                                                  ixs_node *lhs, ixs_node *rhs,
                                                  ixs_node *product) {
  rational_range closure;
  ixs_check_result envelope_fit;
  ixs_check_result product_fit;
  ixs_check_result result = IXS_CHECK_TRUE;
  closure.lower = 1;
  closure.upper = 1;
  closure.known = true;
  result = rational_check_and(result, rational_word_fits(state, lhs));
  result = rational_check_and(result, rational_word_fits(state, rhs));
  closure = rational_range_multiply(
      closure, rational_power_closure(rational_get_range(state, lhs), 1u));
  closure = rational_range_multiply(
      closure, rational_power_closure(rational_get_range(state, rhs), 1u));
  envelope_fit = rational_word_range_fits(state, closure);
  product_fit = rational_word_fits(state, product);
  /* The subset envelope proves the final product as one of its members.  A
   * separate range query is only useful as a conclusive witness when the
   * envelope itself cannot be proved. */
  result = rational_check_and(result, envelope_fit == IXS_CHECK_TRUE
                                          ? IXS_CHECK_TRUE
                                          : (product_fit == IXS_CHECK_FALSE
                                                 ? IXS_CHECK_FALSE
                                                 : IXS_CHECK_UNKNOWN));
  return result;
}

static bool rational_is_power_of_two(uint64_t value) {
  return value != 0 && (value & (value - UINT64_C(1))) == 0;
}

static bool rational_mod_truncates_dividend(const rational_state *state,
                                            const ixs_node *expr) {
  int64_t divisor;
  if (expr->tag != IXS_MOD || !expr->u.binary.rhs ||
      expr->u.binary.rhs->tag != IXS_INT)
    return false;
  divisor = expr->u.binary.rhs->u.ival;
  return divisor > 0 && rational_is_power_of_two((uint64_t)divisor) &&
         (uint64_t)divisor <= state->word_modulus;
}

static bool rational_validation_is_structural(const ixs_node *expr) {
  return expr->tag == IXS_INT || expr->tag == IXS_SYM || expr->tag == IXS_ADD ||
         expr->tag == IXS_MUL || expr->tag == IXS_PIECEWISE;
}

static bool rational_validation_child_count(rational_state *state,
                                            const ixs_node *expr,
                                            size_t *count) {
  if (!rational_node_shape_ok(state, expr))
    return false;
  if (!rational_validation_is_structural(expr)) {
    *count = 0;
    return true;
  }
  return rational_direct_child_count(state, expr, count);
}

static bool rational_validation_schedule(rational_state *state,
                                         ixs_node *expr) {
  rational_validation_entry *entry = rational_validation_find(state, expr);
  rational_validation_frame frame;
  if (entry) {
    if (entry->state == RATIONAL_MEMO_ACTIVE) {
      state->cycle = true;
      return false;
    }
    return true;
  }
  entry = rational_validation_insert(state, expr);
  if (!entry)
    return false;
  if (!rational_validation_child_count(state, expr, &frame.child_count)) {
    entry->state = RATIONAL_MEMO_DONE;
    return true;
  }
  frame.expr = expr;
  frame.next_child = 0;
  return rational_validation_stack_push(state, frame);
}

static ixs_check_result rational_validation_child_result(rational_state *state,
                                                         ixs_node *expr) {
  rational_validation_entry *entry = rational_validation_find(state, expr);
  return entry && entry->state == RATIONAL_MEMO_DONE ? entry->result
                                                     : IXS_CHECK_UNKNOWN;
}

static ixs_check_result rational_validate_add(rational_state *state,
                                              ixs_node *expr) {
  ixs_check_result result = IXS_CHECK_TRUE;
  ixs_check_result envelope_fit;
  ixs_check_result expression_fit;
  rational_range envelope;
  rational_range constant_range;
  uint32_t i;
  bool envelope_known;
  if (ixs_bounds_check_integer_valued(state->bounds, expr) != IXS_CHECK_TRUE)
    return IXS_CHECK_UNKNOWN;
  result = rational_check_and(
      result, rational_validation_child_result(state, expr->u.add.coeff));
  result =
      rational_check_and(result, rational_word_fits(state, expr->u.add.coeff));
  constant_range = rational_get_range(state, expr->u.add.coeff);
  envelope = constant_range;
  envelope_known = envelope.known;
  for (i = 0; i < expr->u.add.nterms; i++) {
    ixs_node *coefficient = expr->u.add.terms[i].coeff;
    ixs_node *term = expr->u.add.terms[i].term;
    ixs_node *addend = rational_make_binary(state, coefficient, IXS_MUL, term);
    rational_range addend_range;
    int64_t contribution;
    result = rational_check_and(
        result, rational_validation_child_result(state, coefficient));
    result = rational_check_and(result,
                                rational_validation_child_result(state, term));
    if (!addend)
      return rational_check_and(result, IXS_CHECK_UNKNOWN);
    result = rational_check_and(
        result, rational_pair_product_fit(state, coefficient, term, addend));
    addend_range = rational_get_range(state, addend);
    if (!envelope_known || !addend_range.known) {
      envelope_known = false;
      continue;
    }
    contribution = addend_range.lower < 0 ? addend_range.lower : 0;
    if (!ixs_safe_add(envelope.lower, contribution, &envelope.lower))
      envelope_known = false;
    contribution = addend_range.upper > 0 ? addend_range.upper : 0;
    if (envelope_known &&
        !ixs_safe_add(envelope.upper, contribution, &envelope.upper))
      envelope_known = false;
  }
  envelope_fit = envelope_known ? rational_word_range_fits(state, envelope)
                                : IXS_CHECK_UNKNOWN;
  expression_fit = rational_word_fits(state, expr);
  result = rational_check_and(result, envelope_fit == IXS_CHECK_TRUE
                                          ? IXS_CHECK_TRUE
                                          : (expression_fit == IXS_CHECK_FALSE
                                                 ? IXS_CHECK_FALSE
                                                 : IXS_CHECK_UNKNOWN));
  return result;
}

static ixs_check_result rational_validate_mul(rational_state *state,
                                              ixs_node *expr) {
  ixs_check_result result = IXS_CHECK_TRUE;
  ixs_check_result envelope_fit;
  ixs_check_result expression_fit;
  uint32_t i;
  if (ixs_bounds_check_integer_valued(state->bounds, expr) != IXS_CHECK_TRUE)
    return IXS_CHECK_UNKNOWN;
  result = rational_check_and(
      result, rational_validation_child_result(state, expr->u.mul.coeff));
  result =
      rational_check_and(result, rational_word_fits(state, expr->u.mul.coeff));
  for (i = 0; i < expr->u.mul.nfactors; i++) {
    ixs_node *base = expr->u.mul.factors[i].base;
    if (expr->u.mul.factors[i].exp <= 0)
      return rational_check_and(result, IXS_CHECK_UNKNOWN);
    result = rational_check_and(result,
                                rational_validation_child_result(state, base));
    result = rational_check_and(result, rational_word_fits(state, base));
  }
  envelope_fit = rational_subset_product_fit(state, expr);
  expression_fit = rational_word_fits(state, expr);
  result = rational_check_and(result, envelope_fit == IXS_CHECK_TRUE
                                          ? IXS_CHECK_TRUE
                                          : (expression_fit == IXS_CHECK_FALSE
                                                 ? IXS_CHECK_FALSE
                                                 : IXS_CHECK_UNKNOWN));
  return result;
}

static ixs_check_result rational_validate_piecewise(rational_state *state,
                                                    ixs_node *expr) {
  ixs_check_result result = IXS_CHECK_TRUE;
  uint32_t i;
  if (ixs_bounds_check_integer_valued(state->bounds, expr) != IXS_CHECK_TRUE)
    return IXS_CHECK_UNKNOWN;
  for (i = 0; i < expr->u.pw.ncases; i++) {
    result = rational_check_and(result, rational_validation_child_result(
                                            state, expr->u.pw.cases[i].value));
    result = rational_check_and(result, rational_validation_child_result(
                                            state, expr->u.pw.cases[i].cond));
  }
  /* Exactly one value is selected.  Proving every arm separately is both
   * stronger and cheaper than asking the generic range engine to revisit all
   * cases, and does not turn that engine's Piecewise work budget into a
   * rational-plan case limit. */
  return result;
}

static ixs_check_result rational_validate_boundary(rational_state *state,
                                                   ixs_node *expr) {
  rational_analysis_entry *entry = rational_analysis_find(state, expr);
  ixs_check_result result;
  if (!entry || entry->state != RATIONAL_MEMO_DONE ||
      !entry->analysis.proof.valid)
    return IXS_CHECK_UNKNOWN;
  result = entry->analysis.full_fit;
  if (expr->tag == IXS_FLOOR || expr->tag == IXS_CEIL || expr->tag == IXS_TRUNC)
    return result;
  return rational_check_and(result, rational_word_fits(state, expr));
}

static ixs_check_result rational_validation_evaluate(rational_state *state,
                                                     ixs_node *expr) {
  if (!rational_node_shape_ok(state, expr))
    return IXS_CHECK_UNKNOWN;
  switch (expr->tag) {
  case IXS_INT:
  case IXS_SYM:
    return rational_word_fits(state, expr);
  case IXS_ADD:
    return rational_validate_add(state, expr);
  case IXS_MUL:
    return rational_validate_mul(state, expr);
  case IXS_PIECEWISE:
    return rational_validate_piecewise(state, expr);
  default:
    return rational_validate_boundary(state, expr);
  }
}

static ixs_check_result rational_validate_integer(rational_state *state,
                                                  ixs_node *expr) {
  rational_validation_entry *root;
  size_t base_depth = state->validation_stack_used;
  if (!expr || !rational_validation_schedule(state, expr))
    return IXS_CHECK_UNKNOWN;
  while (!state->oom && !state->cycle &&
         state->validation_stack_used > base_depth) {
    rational_validation_frame *frame =
        &state->validation_stack[state->validation_stack_used - 1u];
    if (frame->next_child < frame->child_count) {
      ixs_node *child = rational_direct_child(frame->expr, frame->next_child++);
      if (!rational_validation_schedule(state, child))
        break;
      continue;
    }
    {
      ixs_node *done_expr = frame->expr;
      ixs_check_result result = rational_validation_evaluate(state, done_expr);
      rational_validation_entry *entry =
          rational_validation_find(state, done_expr);
      if (entry) {
        entry->result = result;
        entry->state = RATIONAL_MEMO_DONE;
      }
      state->validation_stack_used--;
    }
  }
  if (state->oom || state->cycle)
    return IXS_CHECK_UNKNOWN;
  root = rational_validation_find(state, expr);
  return root && root->state == RATIONAL_MEMO_DONE ? root->result
                                                   : IXS_CHECK_UNKNOWN;
}

static ixs_check_result rational_open_fit(rational_state *state,
                                          ixs_node *source,
                                          rational_proof proof,
                                          bool nonnegative) {
  ixs_check_result result;
  if (!proof.valid || !proof.numerator || proof.denominator <= 0)
    return IXS_CHECK_UNKNOWN;
  result = rational_validate_integer(state, proof.numerator);
  if (proof.denominator > 1 && !nonnegative &&
      !rational_is_nonnegative(state, source))
    result = rational_check_and(result,
                                rational_signed_fits(state, proof.numerator));
  return result;
}

static ixs_check_result rational_selected_trunc_bias_fit(rational_state *state,
                                                         ixs_node *numerator,
                                                         int64_t denominator) {
  rational_range source = rational_get_range(state, numerator);
  rational_range selected = rational_unknown_range();
  int64_t bias;
  int64_t lower;
  int64_t upper;
  if (!source.known || denominator <= 1 || !ixs_safe_sub(denominator, 1, &bias))
    return IXS_CHECK_UNKNOWN;
  if (source.lower < 0) {
    int64_t negative_upper = source.upper < -1 ? source.upper : -1;
    if (!ixs_safe_add(source.lower, bias, &lower) ||
        !ixs_safe_add(negative_upper, bias, &upper))
      return IXS_CHECK_UNKNOWN;
    selected.lower = lower;
    selected.upper = upper;
    selected.known = true;
  }
  if (source.upper >= 0) {
    rational_range nonnegative;
    nonnegative.lower = source.lower > 0 ? source.lower : 0;
    nonnegative.upper = source.upper;
    nonnegative.known = true;
    selected = selected.known ? rational_range_hull(selected, nonnegative)
                              : nonnegative;
  }
  return rational_word_range_fits(state, selected);
}

static ixs_check_result
rational_validate_static_round(rational_state *state, ixs_node *expr,
                               rational_analysis child) {
  ixs_check_result result = child.closed_fit;
  ixs_node *source = expr->u.unary.arg;
  rational_proof proof = child.proof;
  bool nonnegative;
  if (!proof.valid || proof.denominator <= 0 ||
      ixs_bounds_check_defined(state->bounds, source) != IXS_CHECK_TRUE)
    return rational_check_and(result, IXS_CHECK_UNKNOWN);
  result = rational_check_and(
      result, rational_validate_integer(state, proof.numerator));
  nonnegative = child.nonnegative || rational_is_nonnegative(state, source);
  if (!nonnegative)
    result = rational_check_and(result,
                                rational_signed_fits(state, proof.numerator));
  /* A denominator wider than the requested unsigned word selects the
   * compare/zero lowering: every fitting numerator has magnitude below it.
   * Otherwise Ceil and negative Trunc materialize denominator - 1. */
  if (proof.denominator > 1 &&
      (uint64_t)proof.denominator <= (uint64_t)state->word_upper) {
    if (expr->tag == IXS_CEIL) {
      ixs_node *bias = rational_make_integer(state, proof.denominator - 1);
      ixs_node *biased =
          rational_make_binary(state, proof.numerator, IXS_ADD, bias);
      if (!biased)
        return rational_check_and(result, IXS_CHECK_UNKNOWN);
      result =
          rational_check_and(result, rational_validate_integer(state, biased));
      if (!nonnegative)
        result =
            rational_check_and(result, rational_signed_fits(state, biased));
    } else if (expr->tag == IXS_TRUNC && !nonnegative) {
      result = rational_check_and(
          result, rational_selected_trunc_bias_fit(state, proof.numerator,
                                                   proof.denominator));
    }
  }
  /* Division by a positive denominator cannot enlarge a fitting integer
   * numerator beyond the signed/word domain checked above.  Avoid a redundant
   * recursive range query on the rounded tree; doing so would reintroduce a
   * depth-dependent semantic cutoff through the bounds implementation. */
  return result;
}

static ixs_check_result
rational_validate_dynamic_round(rational_state *state, ixs_node *expr,
                                rational_analysis numerator,
                                rational_analysis denominator) {
  ixs_check_result result = IXS_CHECK_TRUE;
  if (!numerator.proof.valid || numerator.proof.denominator != 1 ||
      !denominator.proof.valid || denominator.proof.denominator != 1 ||
      ixs_bounds_check_defined(state->bounds, expr->u.unary.arg) !=
          IXS_CHECK_TRUE ||
      ixs_bounds_check_integer_valued(
          state->bounds, numerator.proof.numerator) != IXS_CHECK_TRUE ||
      ixs_bounds_check_integer_valued(
          state->bounds, denominator.proof.numerator) != IXS_CHECK_TRUE)
    return IXS_CHECK_UNKNOWN;
  result = rational_check_and(result, numerator.closed_fit);
  result = rational_check_and(result, denominator.closed_fit);
  result = rational_check_and(
      result, rational_validate_integer(state, numerator.proof.numerator));
  result = rational_check_and(
      result, rational_validate_integer(state, denominator.proof.numerator));
  result = rational_check_and(
      result, rational_signed_fits(state, numerator.proof.numerator));
  result = rational_check_and(
      result, rational_signed_fits(state, denominator.proof.numerator));
  return rational_check_and(result, rational_signed_fits(state, expr));
}

static rational_analysis rational_analysis_done(rational_state *state,
                                                ixs_node *expr) {
  rational_analysis_entry *entry = rational_analysis_find(state, expr);
  return entry && entry->state == RATIONAL_MEMO_DONE
             ? entry->analysis
             : rational_empty_analysis();
}

static void rational_merge_closed(rational_analysis *parent,
                                  rational_analysis child) {
  parent->closed_fit = rational_check_and(parent->closed_fit, child.closed_fit);
  parent->contains_materialization |= child.contains_materialization;
}

static void rational_finalize_analysis(rational_state *state, ixs_node *expr,
                                       rational_analysis *analysis) {
  if (!analysis->proof.valid) {
    analysis->full_fit =
        rational_check_and(analysis->closed_fit, IXS_CHECK_UNKNOWN);
    return;
  }
  if (!analysis->contains_materialization) {
    analysis->full_fit = IXS_CHECK_TRUE;
    return;
  }
  /* A literal has no arithmetic intermediate.  Its exact numerator remains a
   * valid plan carrier even when the literal's mathematical value is outside
   * the requested word; an enclosing operation will validate the scaled final
   * numerator before receiving TRUE. */
  if (expr->tag == IXS_RAT) {
    analysis->full_fit = IXS_CHECK_TRUE;
    return;
  }
  analysis->full_fit = analysis->closed_fit;
  if (analysis->owns_materialization)
    analysis->full_fit = rational_check_and(
        analysis->full_fit,
        rational_open_fit(state, expr, analysis->proof, analysis->nonnegative));
}

static rational_analysis rational_evaluate_add(rational_state *state,
                                               ixs_node *expr) {
  rational_analysis result = rational_empty_analysis();
  rational_proof *operands;
  rational_analysis child;
  size_t count = (size_t)expr->u.add.nterms + 1u;
  size_t bytes;
  size_t i;
  int64_t denominator = 1;
  ixs_node *numerator;
  if (!rational_allocation_size(state, count, sizeof(*operands), &bytes))
    return result;
  operands = ixs_arena_alloc(state->bounds->scratch, bytes, sizeof(void *));
  if (!operands) {
    state->oom = true;
    return result;
  }
  child = rational_analysis_done(state, expr->u.add.coeff);
  operands[0] = child.proof;
  rational_merge_closed(&result, child);
  result.owns_materialization |= child.owns_materialization;
  result.nonnegative = child.nonnegative;
  for (i = 0; i < expr->u.add.nterms; i++) {
    rational_analysis coefficient =
        rational_analysis_done(state, expr->u.add.terms[i].coeff);
    rational_analysis term =
        rational_analysis_done(state, expr->u.add.terms[i].term);
    operands[i + 1u] =
        rational_multiply_proofs(state, coefficient.proof, term.proof);
    rational_merge_closed(&result, coefficient);
    rational_merge_closed(&result, term);
    result.owns_materialization |=
        coefficient.owns_materialization || term.owns_materialization;
    result.nonnegative &= coefficient.nonnegative && term.nonnegative;
  }
  for (i = 0; i < count; i++) {
    if (!operands[i].valid ||
        !rational_checked_lcm(denominator, operands[i].denominator,
                              &denominator))
      return result;
  }
  numerator = rational_make_integer(state, 0);
  if (!numerator)
    return result;
  for (i = 0; i < count; i++) {
    rational_proof scaled = rational_scale_proof(
        state, operands[i], denominator / operands[i].denominator);
    if (!scaled.valid)
      return result;
    numerator =
        rational_make_binary(state, numerator, IXS_ADD, scaled.numerator);
    if (!numerator)
      return result;
  }
  result.proof.numerator = numerator;
  result.proof.denominator = denominator;
  result.proof.valid = true;
  rational_finalize_analysis(state, expr, &result);
  return result;
}

static rational_analysis rational_evaluate_mul(rational_state *state,
                                               ixs_node *expr) {
  rational_analysis result = rational_empty_analysis();
  rational_analysis coefficient =
      rational_analysis_done(state, expr->u.mul.coeff);
  rational_proof proof = coefficient.proof;
  uint32_t i;
  rational_merge_closed(&result, coefficient);
  result.owns_materialization = coefficient.owns_materialization;
  result.nonnegative = coefficient.nonnegative;
  for (i = 0; i < expr->u.mul.nfactors; i++) {
    rational_analysis base =
        rational_analysis_done(state, expr->u.mul.factors[i].base);
    rational_proof power =
        rational_raise_proof(state, base.proof, expr->u.mul.factors[i].exp);
    proof = rational_multiply_proofs(state, proof, power);
    rational_merge_closed(&result, base);
    result.owns_materialization |=
        base.owns_materialization || expr->u.mul.factors[i].exp < 0;
    result.nonnegative &=
        (expr->u.mul.factors[i].exp % 2 == 0) || base.nonnegative;
    if (expr->u.mul.factors[i].exp < 0)
      result.contains_materialization = true;
  }
  result.proof = proof;
  rational_finalize_analysis(state, expr, &result);
  return result;
}

static rational_analysis
rational_evaluate_round(rational_state *state, rational_analysis_frame *frame) {
  ixs_node *expr = frame->expr;
  rational_analysis child = rational_analysis_done(state, expr->u.unary.arg);
  rational_analysis result = rational_empty_analysis();
  result.contains_materialization = child.contains_materialization;
  result.closed_fit = child.closed_fit;
  result.nonnegative = child.nonnegative;
  if (child.proof.valid) {
    result.proof.numerator = expr;
    result.proof.denominator = 1;
    result.proof.valid = true;
    if (child.owns_materialization || child.contains_materialization) {
      result.contains_materialization = true;
      result.closed_fit = rational_validate_static_round(state, expr, child);
    }
    rational_finalize_analysis(state, expr, &result);
    return result;
  }
  if (frame->exact_numerator && frame->exact_denominator) {
    rational_analysis numerator =
        rational_analysis_done(state, frame->exact_numerator);
    rational_analysis denominator =
        rational_analysis_done(state, frame->exact_denominator);
    result.contains_materialization = true;
    result.proof.numerator = expr;
    result.proof.denominator = 1;
    result.proof.valid = numerator.proof.valid && denominator.proof.valid;
    result.closed_fit =
        rational_validate_dynamic_round(state, expr, numerator, denominator);
  }
  rational_finalize_analysis(state, expr, &result);
  return result;
}

static rational_analysis rational_evaluate_mod(rational_state *state,
                                               ixs_node *expr) {
  rational_analysis lhs = rational_analysis_done(state, expr->u.binary.lhs);
  rational_analysis rhs = rational_analysis_done(state, expr->u.binary.rhs);
  rational_analysis result = rational_empty_analysis();
  rational_merge_closed(&result, lhs);
  rational_merge_closed(&result, rhs);
  result.proof.numerator = expr;
  result.proof.denominator = 1;
  result.proof.valid =
      lhs.proof.valid && rhs.proof.valid &&
      ixs_bounds_check_integer_valued(state->bounds, expr) == IXS_CHECK_TRUE &&
      ixs_bounds_check_defined(state->bounds, expr) == IXS_CHECK_TRUE;
  if (result.proof.valid && result.contains_materialization) {
    if (lhs.owns_materialization &&
        !rational_mod_truncates_dividend(state, expr))
      result.closed_fit = rational_check_and(
          result.closed_fit, rational_open_fit(state, expr->u.binary.lhs,
                                               lhs.proof, lhs.nonnegative));
    if (rhs.owns_materialization)
      result.closed_fit = rational_check_and(
          result.closed_fit, rational_open_fit(state, expr->u.binary.rhs,
                                               rhs.proof, rhs.nonnegative));
    result.closed_fit =
        rational_check_and(result.closed_fit, rational_word_fits(state, expr));
  }
  rational_finalize_analysis(state, expr, &result);
  return result;
}

static rational_analysis rational_evaluate_assoc(rational_state *state,
                                                 ixs_node *expr) {
  rational_analysis result = rational_empty_analysis();
  uint32_t i;
  bool proofs_valid = true;
  for (i = 0; i < expr->u.assoc.nargs; i++) {
    rational_analysis child =
        rational_analysis_done(state, expr->u.assoc.args[i]);
    rational_merge_closed(&result, child);
    proofs_valid &= child.proof.valid;
    if (child.owns_materialization)
      result.closed_fit = rational_check_and(
          result.closed_fit, rational_open_fit(state, expr->u.assoc.args[i],
                                               child.proof, child.nonnegative));
  }
  if (expr->tag != IXS_MAX && expr->tag != IXS_MIN && proofs_valid &&
      ixs_bounds_check_integer_valued(state->bounds, expr) == IXS_CHECK_TRUE &&
      ixs_bounds_check_defined(state->bounds, expr) == IXS_CHECK_TRUE) {
    result.proof.numerator = expr;
    result.proof.denominator = 1;
    result.proof.valid = true;
    result.nonnegative = ixs_node_is_bool_valued(expr);
    if (result.contains_materialization)
      result.closed_fit = rational_check_and(result.closed_fit,
                                             rational_word_fits(state, expr));
  } else if (result.contains_materialization) {
    result.closed_fit =
        rational_check_and(result.closed_fit, IXS_CHECK_UNKNOWN);
  }
  rational_finalize_analysis(state, expr, &result);
  return result;
}

static rational_analysis rational_evaluate_predicate(rational_state *state,
                                                     ixs_node *expr) {
  rational_analysis result = rational_empty_analysis();
  size_t count;
  size_t i;
  bool proofs_valid = true;
  if (!rational_direct_child_count(state, expr, &count))
    return result;
  for (i = 0; i < count; i++) {
    ixs_node *child_expr = rational_direct_child(expr, i);
    rational_analysis child = rational_analysis_done(state, child_expr);
    rational_merge_closed(&result, child);
    proofs_valid &= child.proof.valid;
    if (child.owns_materialization)
      result.closed_fit = rational_check_and(
          result.closed_fit,
          rational_open_fit(state, child_expr, child.proof, child.nonnegative));
  }
  if (proofs_valid &&
      ixs_bounds_check_defined(state->bounds, expr) == IXS_CHECK_TRUE) {
    result.proof.numerator = expr;
    result.proof.denominator = 1;
    result.proof.valid = true;
    result.nonnegative = true;
  }
  rational_finalize_analysis(state, expr, &result);
  return result;
}

static rational_analysis rational_evaluate_piecewise(rational_state *state,
                                                     ixs_node *expr) {
  rational_analysis result = rational_empty_analysis();
  ixs_node **values;
  ixs_node **conditions;
  int64_t denominator = 1;
  size_t bytes;
  uint32_t i;
  bool valid = true;
  bool values_nonnegative = true;
  if (!rational_allocation_size(state, expr->u.pw.ncases, sizeof(*values),
                                &bytes))
    return result;
  values = ixs_arena_alloc(state->bounds->scratch, bytes, sizeof(void *));
  conditions = ixs_arena_alloc(state->bounds->scratch, bytes, sizeof(void *));
  if (!values || !conditions) {
    state->oom = true;
    return result;
  }
  for (i = 0; i < expr->u.pw.ncases; i++) {
    rational_analysis value =
        rational_analysis_done(state, expr->u.pw.cases[i].value);
    rational_analysis condition =
        rational_analysis_done(state, expr->u.pw.cases[i].cond);
    rational_merge_closed(&result, value);
    result.contains_materialization |= condition.contains_materialization;
    result.closed_fit =
        rational_check_and(result.closed_fit, condition.full_fit);
    result.owns_materialization |= value.owns_materialization;
    values_nonnegative &= value.nonnegative;
    valid &= value.proof.valid && condition.proof.valid;
    if (valid && !rational_checked_lcm(denominator, value.proof.denominator,
                                       &denominator))
      valid = false;
  }
  if (!valid)
    goto done;
  for (i = 0; i < expr->u.pw.ncases; i++) {
    rational_analysis value =
        rational_analysis_done(state, expr->u.pw.cases[i].value);
    rational_proof scaled = rational_scale_proof(
        state, value.proof, denominator / value.proof.denominator);
    if (!scaled.valid)
      goto done;
    values[i] = scaled.numerator;
    conditions[i] = expr->u.pw.cases[i].cond;
  }
  result.proof.numerator =
      simp_pw(state->ctx, expr->u.pw.ncases, values, conditions);
  if (!result.proof.numerator)
    state->oom = true;
  if (result.proof.numerator && !ixs_node_is_sentinel(result.proof.numerator)) {
    result.proof.denominator = denominator;
    result.proof.valid = true;
    result.nonnegative = values_nonnegative;
  } else {
    result.proof.numerator = NULL;
  }

done:
  rational_finalize_analysis(state, expr, &result);
  return result;
}

static rational_analysis
rational_analysis_evaluate(rational_state *state,
                           rational_analysis_frame *frame) {
  ixs_node *expr = frame->expr;
  rational_analysis result = rational_empty_analysis();
  switch (expr->tag) {
  case IXS_INT:
  case IXS_SYM:
    result.proof.numerator = expr;
    result.proof.denominator = 1;
    result.proof.valid = true;
    result.nonnegative = expr->tag == IXS_INT
                             ? expr->u.ival >= 0
                             : rational_is_nonnegative(state, expr);
    break;
  case IXS_RAT:
    if (expr->u.rat.q <= 0)
      break;
    result.proof.numerator = rational_make_integer(state, expr->u.rat.p);
    result.proof.denominator = expr->u.rat.q;
    result.proof.valid = result.proof.numerator != NULL;
    result.contains_materialization = expr->u.rat.q != 1;
    result.owns_materialization = result.contains_materialization;
    result.nonnegative = expr->u.rat.p >= 0;
    break;
  case IXS_ADD:
    return rational_evaluate_add(state, expr);
  case IXS_MUL:
    return rational_evaluate_mul(state, expr);
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_TRUNC:
    return rational_evaluate_round(state, frame);
  case IXS_MOD:
    return rational_evaluate_mod(state, expr);
  case IXS_XOR:
  case IXS_AND:
  case IXS_OR:
  case IXS_MAX:
  case IXS_MIN:
    return rational_evaluate_assoc(state, expr);
  case IXS_CMP:
  case IXS_NOT:
    return rational_evaluate_predicate(state, expr);
  case IXS_PIECEWISE:
    return rational_evaluate_piecewise(state, expr);
  default:
    break;
  }
  rational_finalize_analysis(state, expr, &result);
  return result;
}

static bool rational_analysis_schedule(rational_state *state, ixs_node *expr) {
  rational_analysis_entry *entry = rational_analysis_find(state, expr);
  rational_analysis_frame frame;
  if (entry) {
    if (entry->state == RATIONAL_MEMO_ACTIVE) {
      state->cycle = true;
      return false;
    }
    return true;
  }
  entry = rational_analysis_insert(state, expr);
  if (!entry)
    return false;
  if (!rational_direct_child_count(state, expr, &frame.child_count)) {
    entry->state = RATIONAL_MEMO_DONE;
    return true;
  }
  frame.expr = expr;
  frame.next_child = 0;
  frame.exact_numerator = NULL;
  frame.exact_denominator = NULL;
  frame.exact_checked = false;
  return rational_analysis_stack_push(state, frame);
}

typedef enum {
  RATIONAL_FRAME_READY,
  RATIONAL_FRAME_WAITING,
  RATIONAL_FRAME_FAILED
} rational_frame_status;

static rational_frame_status
rational_analysis_prepare_frame(rational_state *state,
                                rational_analysis_frame *frame) {
  if (!frame->exact_checked) {
    frame->exact_checked = true;
    if (frame->expr->tag == IXS_FLOOR || frame->expr->tag == IXS_CEIL ||
        frame->expr->tag == IXS_TRUNC) {
      rational_analysis child =
          rational_analysis_done(state, frame->expr->u.unary.arg);
      if (!child.proof.valid &&
          simp_decompose_exact_quotient(state->ctx, frame->expr->u.unary.arg,
                                        &frame->exact_numerator,
                                        &frame->exact_denominator)) {
        if (!rational_analysis_schedule(state, frame->exact_numerator))
          return RATIONAL_FRAME_FAILED;
        return RATIONAL_FRAME_WAITING;
      }
    }
  }
  if (frame->exact_numerator) {
    rational_analysis_entry *numerator =
        rational_analysis_find(state, frame->exact_numerator);
    rational_analysis_entry *denominator;
    if (!numerator || numerator->state != RATIONAL_MEMO_DONE) {
      if (!rational_analysis_schedule(state, frame->exact_numerator))
        return RATIONAL_FRAME_FAILED;
      return RATIONAL_FRAME_WAITING;
    }
    denominator = rational_analysis_find(state, frame->exact_denominator);
    if (!denominator || denominator->state != RATIONAL_MEMO_DONE) {
      if (!rational_analysis_schedule(state, frame->exact_denominator))
        return RATIONAL_FRAME_FAILED;
      return RATIONAL_FRAME_WAITING;
    }
  }
  return RATIONAL_FRAME_READY;
}

static rational_analysis rational_analyze(rational_state *state,
                                          ixs_node *expr) {
  rational_analysis_entry *root;
  if (!rational_analysis_schedule(state, expr))
    return rational_empty_analysis();
  while (!state->oom && !state->cycle && state->analysis_stack_used) {
    rational_analysis_frame *frame =
        &state->analysis_stack[state->analysis_stack_used - 1u];
    if (frame->next_child < frame->child_count) {
      ixs_node *child = rational_direct_child(frame->expr, frame->next_child++);
      if (!rational_analysis_schedule(state, child))
        break;
      continue;
    }
    {
      rational_frame_status status =
          rational_analysis_prepare_frame(state, frame);
      if (status == RATIONAL_FRAME_FAILED)
        break;
      if (status == RATIONAL_FRAME_WAITING)
        continue;
    }
    {
      ixs_node *done_expr = frame->expr;
      rational_analysis analysis = rational_analysis_evaluate(state, frame);
      rational_analysis_entry *entry = rational_analysis_find(state, done_expr);
      if (entry) {
        entry->analysis = analysis;
        entry->state = RATIONAL_MEMO_DONE;
      }
      state->analysis_stack_used--;
    }
  }
  if (state->oom || state->cycle)
    return rational_empty_analysis();
  root = rational_analysis_find(state, expr);
  return root && root->state == RATIONAL_MEMO_DONE ? root->analysis
                                                   : rational_empty_analysis();
}

IXS_STATIC ixs_rational_materialization_plan
ixs_bounds_plan_rational_materialization(ixs_ctx *ctx, ixs_bounds *bounds,
                                         ixs_node *expr, uint32_t word_bits) {
  rational_state state;
  rational_analysis analysis;
  ixs_rational_materialization_plan result;
  uint64_t signed_modulus;
  result.status = IXS_CHECK_UNKNOWN;
  result.numerator = NULL;
  result.denominator = 1;
  if (!ctx || !bounds || !expr || word_bits < 2u || word_bits > 64u)
    return result;
  memset(&state, 0, sizeof(state));
  state.ctx = ctx;
  state.bounds = bounds;
  if (word_bits == 64u) {
    state.word_modulus = UINT64_MAX;
    state.word_lower = INT64_MIN;
    state.word_upper = INT64_MAX;
    state.signed_lower = INT64_MIN;
    state.signed_upper = INT64_MAX;
  } else {
    state.word_modulus = UINT64_C(1) << word_bits;
    signed_modulus = UINT64_C(1) << (word_bits - 1u);
    state.word_lower = -(int64_t)signed_modulus;
    state.word_upper = (int64_t)(state.word_modulus - UINT64_C(1));
    state.signed_lower = state.word_lower;
    state.signed_upper = (int64_t)(signed_modulus - UINT64_C(1));
  }
  analysis = rational_analyze(&state, expr);
  if (state.oom || state.cycle || bounds->oom)
    return result;
  result.status =
      analysis.contains_materialization ? analysis.full_fit : IXS_CHECK_TRUE;
  /* A TRUE plan is executable, not merely a statement that no rational leaf
   * happened to be found.  Unsupported and malformed roots remain UNKNOWN. */
  if (result.status != IXS_CHECK_TRUE || !analysis.proof.valid ||
      !analysis.proof.numerator || analysis.proof.denominator <= 0) {
    if (result.status == IXS_CHECK_TRUE)
      result.status = IXS_CHECK_UNKNOWN;
    return result;
  }
  result.numerator = analysis.proof.numerator;
  result.denominator = analysis.proof.denominator;
  return result;
}
