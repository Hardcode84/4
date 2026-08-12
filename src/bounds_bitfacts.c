/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds_bitfacts.h"

#include "bounds.h"
#include "bounds_query.h"
#include "bounds_store.h"
#include "query_walk.h"
#include "rational.h"

#include <stdint.h>
#include <string.h>

static void bounds_bitfacts_unknown(ixs_bitfacts *bits) {
  bits->known_zero = 0;
  bits->known_one = 0;
  bits->pow2 = IXS_POW2_UNKNOWN;
}

static unsigned bit_ctz64(uint64_t v) {
  unsigned n = 0;
  while (v != 0 && (v & 1u) == 0) {
    n++;
    v >>= 1;
  }
  return n;
}

static uint64_t low_mask(unsigned nbits) {
  if (nbits >= 64u)
    return ~(uint64_t)0;
  return (((uint64_t)1) << nbits) - 1u;
}

IXS_STATIC uint64_t bounds_bitfacts_value_span_mask(uint64_t hi) {
  uint64_t mask = 0;
  while (hi) {
    mask = (mask << 1) | 1u;
    hi >>= 1;
  }
  return mask;
}

static void bitfacts_apply_exact(ixs_bitfacts *bits, int64_t val) {
  uint64_t u = (uint64_t)val;
  bits->known_zero |= ~u;
  bits->known_one |= u;
  if (val == 0)
    bits->pow2 = IXS_POW2_OR_ZERO;
  else if (ixs_int64_is_positive_pow2(val))
    bits->pow2 = IXS_POW2_POSITIVE;
}

static void bitfacts_apply_interval(ixs_bitfacts *bits,
                                    const ixs_interval *iv) {
  int64_t exact;
  if (ixs_interval_is_point_int(*iv, &exact)) {
    bitfacts_apply_exact(bits, exact);
    return;
  }
  if (!iv->valid || iv->lo_inf || iv->hi_inf || iv->hi_q != 1 || iv->hi_p < 0 ||
      !ixs_interval_lower_at_least(iv, 0, 1))
    return;
  bits->known_zero |= ~bounds_bitfacts_value_span_mask((uint64_t)iv->hi_p);
}

static bool bitfacts_low_value(const ixs_bitfacts *bits, unsigned nbits,
                               uint64_t *value) {
  uint64_t mask = low_mask(nbits);
  if (((bits->known_zero | bits->known_one) & mask) != mask)
    return false;
  *value = bits->known_one & mask;
  return true;
}

static void bitfacts_set_low_value(ixs_bitfacts *bits, unsigned nbits,
                                   uint64_t value) {
  uint64_t mask = low_mask(nbits);
  bits->known_one |= value & mask;
  bits->known_zero |= (~value) & mask;
}

static void bitfacts_apply_modrem(ixs_bitfacts *bits, int64_t modulus,
                                  int64_t remainder) {
  uint64_t mask, rem;
  if (!ixs_int64_is_positive_pow2(modulus))
    return;
  mask = (uint64_t)modulus - 1u;
  rem = (uint64_t)remainder & mask;
  bits->known_zero |= (~rem) & mask;
  bits->known_one |= rem & mask;
}

static bool bounds_get_symbol_bitfacts(ixs_bounds *b, const char *name,
                                       ixs_bitfacts *out) {
  int64_t exact;
  ixs_var_bound *v = bounds_store_find_var(b, name);
  if (v) {
    out->known_zero |= v->bits.known_zero;
    out->known_one |= v->bits.known_one;
    if (v->bits.pow2 == IXS_POW2_POSITIVE ||
        (v->bits.pow2 == IXS_POW2_OR_ZERO && out->pow2 == IXS_POW2_UNKNOWN))
      out->pow2 = v->bits.pow2;
    bitfacts_apply_modrem(out, v->modulus, v->remainder);
    if (ixs_interval_is_point_int(v->iv, &exact))
      bitfacts_apply_exact(out, exact);
    if (out->pow2 == IXS_POW2_OR_ZERO &&
        ixs_interval_lower_at_least(&v->iv, 1, 1))
      out->pow2 = IXS_POW2_POSITIVE;
  }
  return true;
}

static void bitfacts_apply_and(ixs_bitfacts *out, const ixs_bitfacts *a,
                               const ixs_bitfacts *b) {
  out->known_one = a->known_one & b->known_one;
  out->known_zero = a->known_zero | b->known_zero;
  out->pow2 = IXS_POW2_UNKNOWN;
}

static void bitfacts_apply_or(ixs_bitfacts *out, const ixs_bitfacts *a,
                              const ixs_bitfacts *b) {
  out->known_one = a->known_one | b->known_one;
  out->known_zero = a->known_zero & b->known_zero;
  out->pow2 = IXS_POW2_UNKNOWN;
}

IXS_STATIC void bounds_bitfacts_apply_xor(ixs_bitfacts *out,
                                          const ixs_bitfacts *a,
                                          const ixs_bitfacts *b) {
  out->known_one =
      (a->known_one & b->known_zero) | (a->known_zero & b->known_one);
  out->known_zero =
      (a->known_zero & b->known_zero) | (a->known_one & b->known_one);
  out->pow2 = IXS_POW2_UNKNOWN;
}

typedef struct {
  ixs_bitfacts bits;
  bool success;
} bounds_bitfacts_child;

static bool bitfacts_scale_nonnegative_pow2_known(
    ixs_bounds *b, ixs_node *term, int64_t coeff,
    const bounds_bitfacts_child *child, ixs_bitfacts *out) {
  ixs_interval iv;
  uint64_t scale;
  unsigned shift;

  if (!child->success || !ixs_int64_is_positive_pow2(coeff) ||
      !ixs_node_is_integer_valued(term))
    return false;

  iv = bounds_get_tracked(b, term);
  scale = (uint64_t)coeff;
  if (!ixs_interval_lower_at_least(&iv, 0, 1) || iv.hi_inf || iv.hi_q != 1 ||
      iv.hi_p < 0 || (uint64_t)iv.hi_p > (uint64_t)INT64_MAX / scale)
    return false;

  shift = bit_ctz64(scale);
  bounds_bitfacts_unknown(out);
  out->known_zero = (child->bits.known_zero << shift) | low_mask(shift);
  out->known_one = child->bits.known_one << shift;
  return true;
}

/* One linear pass over normalized addends. Pairwise-disjoint possible-one
 * masks prove that integer addition cannot carry between addends. */
static void
bitfacts_apply_carry_free_add_known(ixs_bounds *b, ixs_node *expr,
                                    const bounds_bitfacts_child *children,
                                    ixs_bitfacts *out) {
  ixs_bitfacts addend;
  uint64_t known_one, possible;
  int64_t cp, cq;
  uint32_t i;

  ixs_node_get_rat(expr->u.add.coeff, &cp, &cq);
  if (cq != 1 || cp < 0)
    return;

  bounds_bitfacts_unknown(&addend);
  bitfacts_apply_exact(&addend, cp);
  possible = ~addend.known_zero;
  known_one = addend.known_one;

  for (i = 0; i < expr->u.add.nterms; i++) {
    uint64_t term_possible;
    int64_t tp, tq;

    ixs_node_get_rat(expr->u.add.terms[i].coeff, &tp, &tq);
    if (tq != 1 || !bitfacts_scale_nonnegative_pow2_known(
                       b, expr->u.add.terms[i].term, tp, &children[i], &addend))
      return;

    term_possible = ~addend.known_zero;
    if ((possible & term_possible) != 0)
      return;
    possible |= term_possible;
    known_one |= addend.known_one;
  }

  out->known_zero |= ~possible;
  out->known_one |= known_one;
}

static void bitfacts_apply_add_known(ixs_bounds *b, ixs_node *expr,
                                     const bounds_bitfacts_child *children,
                                     ixs_bitfacts *out) {
  unsigned nbits;
  int64_t cp, cq;

  ixs_node_get_rat(expr->u.add.coeff, &cp, &cq);
  if (cq != 1)
    return;

  bitfacts_apply_carry_free_add_known(b, expr, children, out);

  for (nbits = 1; nbits <= 64u; nbits++) {
    uint64_t mask = low_mask(nbits);
    uint64_t sum = (uint64_t)cp & mask;
    uint32_t i;
    bool known = true;

    for (i = 0; i < expr->u.add.nterms; i++) {
      uint64_t term_value;
      int64_t tp, tq;

      ixs_node_get_rat(expr->u.add.terms[i].coeff, &tp, &tq);
      if (tq != 1 || !children[i].success ||
          !bitfacts_low_value(&children[i].bits, nbits, &term_value)) {
        known = false;
        break;
      }
      sum = (sum + (((uint64_t)tp * term_value) & mask)) & mask;
    }

    if (!known)
      break;
    bitfacts_set_low_value(out, nbits, sum);
    if (nbits == 64u)
      break;
  }
}

static void bitfacts_apply_mul_known(ixs_node *expr,
                                     const bounds_bitfacts_child *child,
                                     ixs_bitfacts *out) {
  uint64_t child_possible;
  uint64_t coeff;
  unsigned shift, i;

  if (expr->u.mul.coeff->tag != IXS_INT || expr->u.mul.coeff->u.ival <= 0 ||
      expr->u.mul.nfactors != 1 || expr->u.mul.factors[0].exp != 1 ||
      !ixs_node_is_integer_valued(expr))
    return;

  coeff = (uint64_t)expr->u.mul.coeff->u.ival;
  if (!child->success)
    return;

  /* A binary integer selects either zero or the coefficient.  Preserve the
   * coefficient's sparse support even when it is not a power of two. */
  child_possible = ~child->bits.known_zero;
  if ((child_possible & ~UINT64_C(1)) == 0u) {
    if (child_possible == 0u) {
      out->known_zero = UINT64_MAX;
      out->known_one = 0u;
      return;
    }
    out->known_zero |= ~coeff;
    if ((child->bits.known_one & UINT64_C(1)) != 0u)
      out->known_one |= coeff;
    return;
  }
  if (!ixs_u64_is_pow2(coeff))
    return;

  shift = bit_ctz64(coeff);
  out->known_zero |= low_mask(shift);
  for (i = shift; i < 64u; i++) {
    uint64_t src = ((uint64_t)1) << (i - shift);
    uint64_t dst = ((uint64_t)1) << i;
    if (child->bits.known_zero & src)
      out->known_zero |= dst;
    if (child->bits.known_one & src)
      out->known_one |= dst;
  }
}

static bool extract_pow2_dividend(ixs_node *expr, ixs_node **dividend,
                                  uint64_t *denom) {
  int64_t cp, cq;
  if (!expr || expr->tag != IXS_MUL || expr->u.mul.nfactors != 1 ||
      expr->u.mul.factors[0].exp != 1)
    return false;
  ixs_node_get_rat(expr->u.mul.coeff, &cp, &cq);
  if (cp != 1 || cq <= 0 || !ixs_int64_is_positive_pow2(cq))
    return false;
  *dividend = expr->u.mul.factors[0].base;
  *denom = (uint64_t)cq;
  return true;
}

static void bitfacts_apply_floor_div_known(ixs_bounds *b, ixs_node *dividend,
                                           uint64_t denom,
                                           const bounds_bitfacts_child *child,
                                           ixs_bitfacts *out) {
  ixs_interval iv;
  unsigned shift, i;

  iv = bounds_get_tracked(b, dividend);
  if (!child->success || !ixs_interval_lower_at_least(&iv, 0, 1))
    return;

  shift = bit_ctz64(denom);
  for (i = 0; i + shift < 64u; i++) {
    uint64_t src = ((uint64_t)1) << (i + shift);
    uint64_t dst = ((uint64_t)1) << i;
    if (child->bits.known_zero & src)
      out->known_zero |= dst;
    if (child->bits.known_one & src)
      out->known_one |= dst;
  }
}

static void bitfacts_apply_mod_known(ixs_node *expr,
                                     const bounds_bitfacts_child *child,
                                     ixs_bitfacts *out) {
  uint64_t mask;
  int64_t modulus;

  if (expr->u.binary.rhs->tag != IXS_INT ||
      !ixs_int64_is_positive_pow2(expr->u.binary.rhs->u.ival) ||
      !ixs_node_is_integer_valued(expr->u.binary.lhs))
    return;

  modulus = expr->u.binary.rhs->u.ival;
  mask = (uint64_t)modulus - 1u;
  out->known_zero |= ~mask;
  if (child->success) {
    out->known_zero |= child->bits.known_zero & mask;
    out->known_one |= child->bits.known_one & mask;
  }
}

static bool bitfacts_apply_assoc_known(ixs_node *expr,
                                       const bounds_bitfacts_child *children,
                                       ixs_bitfacts *out) {
  ixs_bitfacts result, arg, next;
  uint32_t i;
  if (expr->u.assoc.nargs == 0 || !expr->u.assoc.args)
    return false;
  if (!children[0].success)
    return false;
  result = children[0].bits;
  for (i = 1; i < expr->u.assoc.nargs; i++) {
    if (!children[i].success)
      return false;
    arg = children[i].bits;
    if (expr->tag == IXS_AND)
      bitfacts_apply_and(&next, &result, &arg);
    else if (expr->tag == IXS_OR)
      bitfacts_apply_or(&next, &result, &arg);
    else
      bounds_bitfacts_apply_xor(&next, &result, &arg);
    result = next;
  }
  *out = result;
  return true;
}

static inline bool bitfacts_apply_bool_value(ixs_bitfacts *out) {
  out->known_zero = ~(uint64_t)1;
  out->known_one = 0;
  return true;
}

typedef enum {
  BOUNDS_BITFACTS_INITIAL,
  BOUNDS_BITFACTS_ADD,
  BOUNDS_BITFACTS_MUL,
  BOUNDS_BITFACTS_FLOOR,
  BOUNDS_BITFACTS_MOD,
  BOUNDS_BITFACTS_ASSOC
} bounds_bitfacts_stage;

typedef struct {
  ixs_node *expr;
  ixs_node *child_expr;
  bounds_query_scope scope;
  bounds_bitfacts_child *children;
  ixs_bitfacts bits;
  uint64_t argument;
  uint32_t index;
  uint32_t child_count;
  bounds_bitfacts_stage stage;
  bool tracked;
} bounds_bitfacts_frame;

typedef struct {
  ixs_bounds *bounds;
  ixs_query_walk walk;
  bounds_bitfacts_child child;
  ixs_bitfacts unknown;
} bounds_bitfacts_query;

static bool bounds_bitfacts_alloc_children(bounds_bitfacts_query *query,
                                           bounds_bitfacts_frame *frame,
                                           uint32_t count) {
  size_t bytes;
  if (count == 0)
    return false;
  bytes = (size_t)count * sizeof(*frame->children);
  frame->children =
      ixs_arena_alloc(query->bounds->scratch, bytes, sizeof(void *));
  if (!frame->children) {
    query->bounds->oom = true;
    return false;
  }
  memset(frame->children, 0, bytes);
  frame->child_count = count;
  return true;
}

IXS_STATIC bool bounds_bitfacts_may_refine(ixs_bounds *bounds, ixs_node *expr) {
  ixs_node *dividend;
  uint64_t shift;
  if (!bounds || !expr)
    return false;
  switch (expr->tag) {
  case IXS_SYM: {
    ixs_var_bound *var = bounds_store_find_var(bounds, expr->u.name);
    return var &&
           ((var->bits.known_zero | var->bits.known_one) != 0 ||
            (var->modulus > 1 && ixs_int64_is_positive_pow2(var->modulus)));
  }
  case IXS_ADD: {
    int64_t p;
    int64_t q;
    uint32_t i;
    ixs_node_get_rat(expr->u.add.coeff, &p, &q);
    if (q != 1)
      return false;
    for (i = 0; i < expr->u.add.nterms; i++) {
      ixs_node_get_rat(expr->u.add.terms[i].coeff, &p, &q);
      if (q != 1)
        return false;
    }
    return true;
  }
  case IXS_MUL:
    return expr->u.mul.coeff->tag == IXS_INT && expr->u.mul.coeff->u.ival > 0 &&
           expr->u.mul.nfactors == 1 && expr->u.mul.factors[0].exp == 1 &&
           ixs_node_is_integer_valued(expr);
  case IXS_FLOOR:
    return extract_pow2_dividend(expr->u.unary.arg, &dividend, &shift);
  case IXS_MOD:
    return expr->u.binary.rhs->tag == IXS_INT &&
           ixs_int64_is_positive_pow2(expr->u.binary.rhs->u.ival) &&
           ixs_node_is_integer_valued(expr->u.binary.lhs);
  case IXS_AND:
  case IXS_OR:
  case IXS_XOR:
    return true;
  default:
    return false;
  }
}

static ixs_query_walk_step
bounds_bitfacts_complete(bounds_bitfacts_query *query, bool success,
                         ixs_bitfacts bits) {
  bounds_bitfacts_frame *frame = IXS_QUERY_WALK_TOP(&query->walk);
  if (frame->tracked) {
    bounds_query_cache_entry *entry =
        bounds_query_finish(&frame->scope, success);
    if (entry->outcome == BOUNDS_QUERY_OUTCOME_VALUE)
      entry->result.bitfacts = bits;
    else
      success = false;
  }
  IXS_QUERY_WALK_POP(&query->walk);
  query->child.success = success;
  query->child.bits = bits;
  return IXS_QUERY_WALK_ADVANCED;
}

/* hot */
static void bounds_bitfacts_abort(void *state, void *raw_frame) {
  bounds_bitfacts_frame *frame = raw_frame;
  (void)state;
  if (frame->tracked)
    (void)bounds_query_finish(&frame->scope, false);
}

static ixs_query_walk_step
bounds_bitfacts_prepare_frame(bounds_bitfacts_query *query,
                              bounds_bitfacts_frame *frame,
                              ixs_bitfacts unknown) {
  ixs_bounds *b = query->bounds;
  ixs_node *node = frame->expr;
  ixs_interval iv;

  /* Stack-local synthetic symbols are valid read-only operands but are not
   * memoized because bounds_query_should_track requires VALID. */
  if (!node)
    return bounds_bitfacts_complete(query, false, unknown);
  if (bounds_query_should_track(b, node)) {
    bounds_query_cache_entry *cached = NULL;
    bounds_query_enter_result enter = bounds_query_begin(
        b, BOUNDS_QUERY_BITFACTS, node, 0, &frame->scope, &cached);
    if (enter == BOUNDS_QUERY_ENTER_CACHED) {
      return bounds_bitfacts_complete(query, cached->success,
                                      cached->result.bitfacts);
    }
    if (enter != BOUNDS_QUERY_ENTER_STARTED) {
      return bounds_bitfacts_complete(query, false, unknown);
    }
    frame->tracked = true;
  }
  bounds_bitfacts_unknown(&frame->bits);
  iv = bounds_get_tracked(b, node);
  bitfacts_apply_interval(&frame->bits, &iv);
  return b->oom ? IXS_QUERY_WALK_OOM : IXS_QUERY_WALK_NEXT;
}

static ixs_query_walk_step
bounds_bitfacts_start_scalar(bounds_bitfacts_query *query,
                             bounds_bitfacts_frame *frame) {
  ixs_node *node = frame->expr;
  switch (node->tag) {
  case IXS_INT:
    bitfacts_apply_exact(&frame->bits, node->u.ival);
    return bounds_bitfacts_complete(query, true, frame->bits);
  case IXS_RAT:
    if (node->u.rat.q == 1)
      bitfacts_apply_exact(&frame->bits, node->u.rat.p);
    return bounds_bitfacts_complete(query, node->u.rat.q == 1, frame->bits);
  case IXS_SYM:
    bounds_get_symbol_bitfacts(query->bounds, node->u.name, &frame->bits);
    return bounds_bitfacts_complete(query, true, frame->bits);
  case IXS_CMP:
  case IXS_NOT:
    bitfacts_apply_bool_value(&frame->bits);
    return bounds_bitfacts_complete(query, true, frame->bits);
  case IXS_CEIL:
  case IXS_TRUNC:
  case IXS_PIECEWISE:
  case IXS_MAX:
  case IXS_MIN:
    return bounds_bitfacts_complete(query, ixs_node_is_integer_valued(node),
                                    frame->bits);
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    return bounds_bitfacts_complete(query, false, frame->bits);
  default:
    return IXS_QUERY_WALK_NEXT;
  }
}

static ixs_query_walk_step
bounds_bitfacts_start_assoc(bounds_bitfacts_query *query,
                            bounds_bitfacts_frame *frame) {
  ixs_node *node = frame->expr;
  if (!node->u.assoc.args || node->u.assoc.nargs == 0) {
    return bounds_bitfacts_complete(query, false, frame->bits);
  }
  if (!bounds_bitfacts_alloc_children(query, frame, node->u.assoc.nargs))
    return IXS_QUERY_WALK_OOM;
  frame->stage = BOUNDS_BITFACTS_ASSOC;
  return ixs_query_walk_push(&query->walk, node->u.assoc.args[0]);
}

static ixs_query_walk_step
bounds_bitfacts_start_composite(bounds_bitfacts_query *query,
                                bounds_bitfacts_frame *frame) {
  ixs_node *node = frame->expr;
  switch (node->tag) {
  case IXS_ADD:
    if (node->u.add.nterms == 0) {
      bitfacts_apply_add_known(query->bounds, node, NULL, &frame->bits);
      return bounds_bitfacts_complete(query, true, frame->bits);
    }
    if (!bounds_bitfacts_alloc_children(query, frame, node->u.add.nterms))
      return IXS_QUERY_WALK_OOM;
    frame->stage = BOUNDS_BITFACTS_ADD;
    return ixs_query_walk_push(&query->walk, node->u.add.terms[0].term);
  case IXS_MUL:
    if (node->u.mul.coeff->tag != IXS_INT || node->u.mul.coeff->u.ival <= 0 ||
        node->u.mul.nfactors != 1 || node->u.mul.factors[0].exp != 1 ||
        !ixs_node_is_integer_valued(node)) {
      return bounds_bitfacts_complete(query, true, frame->bits);
    }
    frame->stage = BOUNDS_BITFACTS_MUL;
    return ixs_query_walk_push(&query->walk, node->u.mul.factors[0].base);
  case IXS_FLOOR:
    if (!extract_pow2_dividend(node->u.unary.arg, &frame->child_expr,
                               &frame->argument)) {
      return bounds_bitfacts_complete(query, true, frame->bits);
    }
    frame->stage = BOUNDS_BITFACTS_FLOOR;
    return ixs_query_walk_push(&query->walk, frame->child_expr);
  case IXS_MOD:
    if (node->u.binary.rhs->tag != IXS_INT ||
        !ixs_int64_is_positive_pow2(node->u.binary.rhs->u.ival) ||
        !ixs_node_is_integer_valued(node->u.binary.lhs)) {
      return bounds_bitfacts_complete(query, true, frame->bits);
    }
    frame->stage = BOUNDS_BITFACTS_MOD;
    return ixs_query_walk_push(&query->walk, node->u.binary.lhs);
  case IXS_AND:
  case IXS_OR:
  case IXS_XOR:
    return bounds_bitfacts_start_assoc(query, frame);
  default:
    return bounds_bitfacts_complete(query, false, frame->bits);
  }
}

static ixs_query_walk_step
bounds_bitfacts_resume_frame(bounds_bitfacts_query *query,
                             bounds_bitfacts_frame *frame) {
  ixs_node *node = frame->expr;
  switch (frame->stage) {
  case BOUNDS_BITFACTS_ADD:
  case BOUNDS_BITFACTS_ASSOC:
    frame->children[frame->index++] = query->child;
    if (frame->index < frame->child_count) {
      ixs_node *child = frame->stage == BOUNDS_BITFACTS_ADD
                            ? node->u.add.terms[frame->index].term
                            : node->u.assoc.args[frame->index];
      return ixs_query_walk_push(&query->walk, child);
    }
    if (frame->stage == BOUNDS_BITFACTS_ADD) {
      bitfacts_apply_add_known(query->bounds, node, frame->children,
                               &frame->bits);
      return bounds_bitfacts_complete(query, true, frame->bits);
    } else {
      bool success =
          bitfacts_apply_assoc_known(node, frame->children, &frame->bits);
      return bounds_bitfacts_complete(query, success, frame->bits);
    }
  case BOUNDS_BITFACTS_MUL:
    bitfacts_apply_mul_known(node, &query->child, &frame->bits);
    return bounds_bitfacts_complete(query, true, frame->bits);
  case BOUNDS_BITFACTS_FLOOR:
    bitfacts_apply_floor_div_known(query->bounds, frame->child_expr,
                                   frame->argument, &query->child,
                                   &frame->bits);
    return bounds_bitfacts_complete(query, true, frame->bits);
  case BOUNDS_BITFACTS_MOD:
    bitfacts_apply_mod_known(node, &query->child, &frame->bits);
    return bounds_bitfacts_complete(query, true, frame->bits);
  case BOUNDS_BITFACTS_INITIAL:
    return bounds_bitfacts_complete(query, false, frame->bits);
  }
  return IXS_QUERY_WALK_ADVANCED;
}

/* hot */
static ixs_query_walk_step bounds_bitfacts_advance(void *state,
                                                   void *raw_frame) {
  bounds_bitfacts_query *query = state;
  bounds_bitfacts_frame *frame = raw_frame;
  ixs_query_walk_step step;
  if (frame->stage != BOUNDS_BITFACTS_INITIAL)
    return bounds_bitfacts_resume_frame(query, frame);
  step = bounds_bitfacts_prepare_frame(query, frame, query->unknown);
  if (step != IXS_QUERY_WALK_NEXT)
    return step;
  step = bounds_bitfacts_start_scalar(query, frame);
  if (step == IXS_QUERY_WALK_NEXT)
    step = bounds_bitfacts_start_composite(query, frame);
  return step;
}

IXS_STATIC bool ixs_bounds_get_bitfacts(ixs_bounds *b, ixs_node *expr,
                                        ixs_bitfacts *out) {
  bounds_bitfacts_query query;
  if (!b || !expr || !out || b->oom)
    return false;
  memset(&query, 0, sizeof(query));
  query.bounds = b;
  bounds_bitfacts_unknown(&query.unknown);
  IXS_QUERY_WALK_INIT(&query.walk, b->scratch, &b->oom, bounds_bitfacts_frame,
                      expr);
  if (!ixs_query_walk_run(&query.walk, expr, &query, bounds_bitfacts_advance,
                          bounds_bitfacts_abort)) {
    bounds_bitfacts_unknown(out);
    return false;
  }
  *out = query.child.bits;
  return query.child.success;
}

IXS_STATIC bool ixs_bounds_is_pow2_or_zero(ixs_bounds *b, ixs_node *expr) {
  ixs_bitfacts bits;
  if (!ixs_bounds_get_bitfacts(b, expr, &bits))
    return false;
  return bits.pow2 == IXS_POW2_OR_ZERO || bits.pow2 == IXS_POW2_POSITIVE;
}
