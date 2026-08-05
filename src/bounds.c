/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds.h"
#include "expand.h"
#include "simplify.h"
#include <limits.h>
#include <string.h>

#define BOUNDS_INIT_CAP 16
#define BOUNDS_VAR_INDEX_INIT_CAP 8u
#define BOUNDS_EXPR_INDEX_INIT_CAP 8u
#define BOUNDS_DIFFERENCE_INDEX_INIT_CAP 8u
#define BOUNDS_EXACT_INDEX_INIT_CAP 8u
#define BOUNDS_CACHE_CAP 32u
#define BOUNDS_CACHE_DISABLED ((size_t)-1)
#define ASSUMPTION_NODE_LIMIT 1024u
#define FACT_WORK_INIT_CAP 64u
#define RANGE_POWER_EXP_LIMIT 64u
#define RANGE_PW_DEPTH_LIMIT 32u
#define RANGE_PW_CASE_LIMIT 1024u
#define MOD_RANGE_ENUM_LIMIT 1024u

/* lhs - rhs <= offset, equivalently the directed edge rhs -> lhs. Edge
 * objects are immutable after publication. Variable indices remain valid
 * across append-only table growth and transactional forks. */
struct ixs_difference_constraint {
  ixs_node *lhs;
  ixs_node *rhs;
  ixs_difference_constraint *next_lhs;
  ixs_difference_constraint *next_rhs;
  size_t lhs_var;
  size_t rhs_var;
  int64_t offset;
};

typedef struct {
  ixs_arena_mark mark;
  size_t *queue;
  size_t epoch;
  size_t capacity;
  size_t head;
  size_t tail;
  size_t count;
} difference_worklist;

static void bounds_propagate_difference_bounds(ixs_bounds *b, const char *first,
                                               const char *second);

static void bounds_empty_cache_invalidate(ixs_bounds *b) {
  if (b)
    b->empty_cache_valid = false;
}

static void bounds_mark_semantic_changed(ixs_bounds *b) {
  if (b && b->semantic_changed)
    *b->semantic_changed = true;
}

static void bounds_mark_contradiction(ixs_bounds *b) {
  if (!b->contradiction)
    bounds_mark_semantic_changed(b);
  b->contradiction = true;
  bounds_empty_cache_invalidate(b);
}

static bool bounds_intervals_equal(ixs_interval a, ixs_interval b) {
  return a.lo_p == b.lo_p && a.lo_q == b.lo_q && a.hi_p == b.hi_p &&
         a.hi_q == b.hi_q && a.lo_inf == b.lo_inf && a.hi_inf == b.hi_inf &&
         a.valid == b.valid;
}

static void bounds_cache_clear(ixs_bounds *b) {
  bounds_empty_cache_invalidate(b);
  if (b && b->cache && b->cache_cap != BOUNDS_CACHE_DISABLED)
    memset(b->cache, 0, b->cache_cap * sizeof(*b->cache));
}

static void bounds_cache_alloc(ixs_bounds *b) {
  if (!b || b->cache_cap == BOUNDS_CACHE_DISABLED)
    return;
  if (b->cache)
    return;
  b->cache = ixs_arena_alloc(b->scratch, BOUNDS_CACHE_CAP * sizeof(*b->cache),
                             sizeof(void *));
  if (!b->cache) {
    b->cache_cap = BOUNDS_CACHE_DISABLED;
    return;
  }
  b->cache_cap = BOUNDS_CACHE_CAP;
  memset(b->cache, 0, b->cache_cap * sizeof(*b->cache));
}

static bool bounds_cache_lookup(ixs_bounds *b, ixs_node *expr,
                                ixs_interval *out) {
  size_t idx;
  if (!b || !expr || !out || !b->cache || b->cache_cap == BOUNDS_CACHE_DISABLED)
    return false;
  idx = expr->hash & (b->cache_cap - 1u);
  if (b->cache[idx].expr != expr)
    return false;
  *out = b->cache[idx].iv;
  return true;
}

static void bounds_cache_store(ixs_bounds *b, ixs_node *expr, ixs_interval iv) {
  size_t idx;
  if (!expr || !b || !b->cache || b->cache_cap == BOUNDS_CACHE_DISABLED)
    return;
  idx = expr->hash & (b->cache_cap - 1u);
  b->cache[idx].expr = expr;
  b->cache[idx].iv = iv;
}

static bool bounds_cacheable_expr(ixs_node *expr) {
  return expr && expr->tag != IXS_INT && expr->tag != IXS_RAT &&
         expr->tag != IXS_SYM;
}

IXS_STATIC bool ixs_bounds_init(ixs_bounds *b, ixs_arena *scratch) {
  b->ctx = NULL;
  b->scratch = scratch;
  b->nvars = 0;
  b->cap = BOUNDS_INIT_CAP;
  b->vars = ixs_arena_alloc(scratch, BOUNDS_INIT_CAP * sizeof(*b->vars),
                            sizeof(void *));
  b->var_index = NULL;
  b->var_index_cap = 0;
  b->nexprs = 0;
  b->expr_cap = 0;
  b->exprs = NULL;
  b->expr_index = NULL;
  b->expr_index_cap = 0;
  b->difference_index = NULL;
  b->difference_vars = NULL;
  b->ndifferences = 0;
  b->ndifference_vars = 0;
  b->difference_index_cap = 0;
  b->difference_var_cap = 0;
  b->difference_epoch = 0;
  b->exact_vars = NULL;
  b->exact_index = NULL;
  b->nexact_vars = 0;
  b->exact_var_cap = 0;
  b->exact_index_cap = 0;
  b->nonzero = NULL;
  b->nnonzero = 0;
  b->nonzero_cap = 0;
  b->cache = NULL;
  b->cache_cap = 0;
  b->range_pw_depth = 0;
  b->has_modrem = false;
  b->contradiction = false;
  b->empty_cache_valid = false;
  b->empty_cache_value = false;
  b->oom = false;
  b->semantic_changed = NULL;
  if (b->vars)
    bounds_cache_alloc(b);
  return b->vars != NULL;
}

IXS_STATIC bool ixs_bounds_init_ctx(ixs_bounds *b, ixs_ctx *ctx,
                                    ixs_arena *scratch) {
  if (!ixs_bounds_init(b, scratch))
    return false;
  b->ctx = ctx;
  return true;
}

/* All bounds storage lives in the scratch arena; no per-object cleanup. */
IXS_STATIC void ixs_bounds_destroy(ixs_bounds *b) { (void)b; }

static bool bounds_fork_index_state(ixs_bounds *dst, const ixs_bounds *src) {
  if (src->nvars) {
    if (!src->var_index || !src->var_index_cap ||
        src->var_index_cap > SIZE_MAX / sizeof(*dst->var_index))
      return false;
    dst->var_index = ixs_arena_alloc(
        dst->scratch, src->var_index_cap * sizeof(*dst->var_index),
        sizeof(void *));
    if (!dst->var_index)
      return false;
    memcpy(dst->var_index, src->var_index,
           src->var_index_cap * sizeof(*src->var_index));
  }
  if (src->difference_index_cap) {
    if (!src->difference_index ||
        src->difference_index_cap > SIZE_MAX / sizeof(*dst->difference_index))
      return false;
    dst->difference_index = ixs_arena_alloc(dst->scratch,
                                            src->difference_index_cap *
                                                sizeof(*dst->difference_index),
                                            sizeof(void *));
    if (!dst->difference_index)
      return false;
    memcpy(dst->difference_index, src->difference_index,
           src->difference_index_cap * sizeof(*src->difference_index));
  }
  if (src->difference_var_cap) {
    if (!src->difference_vars ||
        src->difference_var_cap > SIZE_MAX / sizeof(*dst->difference_vars))
      return false;
    dst->difference_vars = ixs_arena_alloc(
        dst->scratch, src->difference_var_cap * sizeof(*dst->difference_vars),
        sizeof(void *));
    if (!dst->difference_vars)
      return false;
    memcpy(dst->difference_vars, src->difference_vars,
           src->difference_var_cap * sizeof(*src->difference_vars));
  }
  return true;
}

static bool bounds_fork_exact_state(ixs_bounds *dst, const ixs_bounds *src) {
  if (src->exact_var_cap) {
    if (!src->exact_vars ||
        src->exact_var_cap > SIZE_MAX / sizeof(*dst->exact_vars))
      return false;
    dst->exact_vars = ixs_arena_alloc(
        dst->scratch, src->exact_var_cap * sizeof(*dst->exact_vars),
        sizeof(void *));
    if (!dst->exact_vars)
      return false;
    memcpy(dst->exact_vars, src->exact_vars,
           src->exact_var_cap * sizeof(*src->exact_vars));
  }
  if (src->exact_index_cap) {
    if (!src->exact_index ||
        src->exact_index_cap > SIZE_MAX / sizeof(*dst->exact_index))
      return false;
    dst->exact_index = ixs_arena_alloc(
        dst->scratch, src->exact_index_cap * sizeof(*dst->exact_index),
        sizeof(void *));
    if (!dst->exact_index)
      return false;
    memcpy(dst->exact_index, src->exact_index,
           src->exact_index_cap * sizeof(*src->exact_index));
  }
  return true;
}

IXS_STATIC bool ixs_bounds_fork(ixs_bounds *dst, const ixs_bounds *src) {
  if (!dst || !src || src->oom)
    return false;
  dst->ctx = src->ctx;
  dst->scratch = src->scratch;
  dst->nvars = src->nvars;
  dst->cap = src->nvars ? src->nvars : 1;
  dst->vars = ixs_arena_alloc(dst->scratch, dst->cap * sizeof(*dst->vars),
                              sizeof(void *));
  if (!dst->vars)
    return false;
  if (src->nvars)
    memcpy(dst->vars, src->vars, src->nvars * sizeof(*src->vars));
  dst->var_index = NULL;
  dst->var_index_cap = src->nvars ? src->var_index_cap : 0;
  dst->nexprs = src->nexprs;
  dst->expr_cap = src->nexprs ? src->nexprs : 0;
  dst->exprs = NULL;
  dst->expr_index = NULL;
  dst->expr_index_cap = src->nexprs ? src->expr_index_cap : 0;
  dst->difference_index = NULL;
  dst->difference_vars = NULL;
  dst->ndifferences = src->ndifferences;
  dst->ndifference_vars = src->ndifference_vars;
  dst->difference_index_cap = src->difference_index_cap;
  dst->difference_var_cap = src->difference_var_cap;
  dst->difference_epoch = src->difference_epoch;
  dst->exact_vars = NULL;
  dst->exact_index = NULL;
  dst->nexact_vars = src->nexact_vars;
  dst->exact_var_cap = src->exact_var_cap;
  dst->exact_index_cap = src->exact_index_cap;
  dst->nnonzero = src->nnonzero;
  dst->nonzero_cap = src->nnonzero;
  dst->nonzero = NULL;
  dst->cache = NULL;
  dst->cache_cap = BOUNDS_CACHE_DISABLED;
  dst->range_pw_depth = src->range_pw_depth;
  dst->has_modrem = src->has_modrem;
  dst->contradiction = src->contradiction;
  dst->empty_cache_valid = false;
  dst->empty_cache_value = false;
  dst->oom = false;
  dst->semantic_changed = NULL;
  if (!bounds_fork_index_state(dst, src) || !bounds_fork_exact_state(dst, src))
    return false;
  if (src->nexprs) {
    dst->exprs = ixs_arena_alloc(
        dst->scratch, dst->expr_cap * sizeof(*dst->exprs), sizeof(void *));
    if (!dst->exprs)
      return false;
    memcpy(dst->exprs, src->exprs, src->nexprs * sizeof(*src->exprs));
    if (!src->expr_index || !src->expr_index_cap ||
        src->expr_index_cap > SIZE_MAX / sizeof(*dst->expr_index))
      return false;
    dst->expr_index = ixs_arena_alloc(
        dst->scratch, dst->expr_index_cap * sizeof(*dst->expr_index),
        sizeof(void *));
    if (!dst->expr_index)
      return false;
    memcpy(dst->expr_index, src->expr_index,
           src->expr_index_cap * sizeof(*src->expr_index));
  }
  if (src->nnonzero) {
    dst->nonzero = ixs_arena_alloc(
        dst->scratch, dst->nonzero_cap * sizeof(*dst->nonzero), sizeof(void *));
    if (!dst->nonzero)
      return false;
    memcpy(dst->nonzero, src->nonzero, src->nnonzero * sizeof(*src->nonzero));
  }
  return true;
}

static size_t bounds_hash_ptr(const void *ptr) {
  uint64_t x = (uint64_t)(uintptr_t)ptr;
  x ^= x >> 33;
  x *= UINT64_C(0xff51afd7ed558ccd);
  x ^= x >> 33;
  return (size_t)x;
}

static size_t bounds_var_index_slot(const size_t *index, size_t capacity,
                                    const ixs_var_bound *vars,
                                    const char *name) {
  size_t slot = bounds_hash_ptr(name) & (capacity - 1u);
  while (index[slot] && vars[index[slot] - 1u].name != name)
    slot = (slot + 1u) & (capacity - 1u);
  return slot;
}

/* Variable lookup is expected O(1); growth rehashes at 75% load. */
static bool bounds_prepare_var_index(ixs_bounds *b, size_t count,
                                     size_t **prepared,
                                     size_t *prepared_capacity) {
  size_t capacity = b->var_index_cap;
  size_t *index;
  size_t i;

  if (capacity && count <= capacity - capacity / 4u) {
    *prepared = b->var_index;
    *prepared_capacity = capacity;
    return true;
  }
  if (!capacity)
    capacity = BOUNDS_VAR_INDEX_INIT_CAP;
  while (count > capacity - capacity / 4u) {
    if (capacity > SIZE_MAX / 2u)
      return false;
    capacity *= 2u;
  }
  if (capacity > SIZE_MAX / sizeof(*index))
    return false;
  index =
      ixs_arena_alloc(b->scratch, capacity * sizeof(*index), sizeof(void *));
  if (!index)
    return false;
  memset(index, 0, capacity * sizeof(*index));
  for (i = 0; i < b->nvars; i++) {
    size_t slot =
        bounds_var_index_slot(index, capacity, b->vars, b->vars[i].name);
    index[slot] = i + 1u;
  }
  *prepared = index;
  *prepared_capacity = capacity;
  return true;
}

static ixs_var_bound *find_var(ixs_bounds *b, const char *name) {
  size_t slot;
  if (!b || !b->vars || !name || b->nvars == 0)
    return NULL;
  if (!b->var_index || !b->var_index_cap) {
    b->oom = true;
    return NULL;
  }
  slot = bounds_var_index_slot(b->var_index, b->var_index_cap, b->vars, name);
  return b->var_index[slot] ? &b->vars[b->var_index[slot] - 1u] : NULL;
}

static bool get_or_create_var_index(ixs_bounds *b, const char *name,
                                    size_t *index) {
  ixs_var_bound *v = find_var(b, name);
  size_t *prepared_index;
  size_t prepared_index_cap;
  size_t slot;
  if (v) {
    *index = (size_t)(v - b->vars);
    return true;
  }
  if (!b->vars || b->oom || b->nvars == SIZE_MAX ||
      !bounds_prepare_var_index(b, b->nvars + 1u, &prepared_index,
                                &prepared_index_cap)) {
    b->oom = true;
    return false;
  }
  if (b->nvars >= b->cap) {
    ixs_var_bound *grown;
    size_t new_cap;
    if (b->cap > SIZE_MAX / 2u || b->cap * 2u > SIZE_MAX / sizeof(*b->vars)) {
      b->oom = true;
      return false;
    }
    new_cap = b->cap * 2u;
    grown = ixs_arena_grow(b->scratch, b->vars, b->cap * sizeof(*b->vars),
                           new_cap * sizeof(*b->vars), sizeof(void *));
    if (!grown) {
      b->oom = true;
      return false;
    }
    b->vars = grown;
    b->cap = new_cap;
  }
  bounds_empty_cache_invalidate(b);
  *index = b->nvars;
  v = &b->vars[*index];
  v->name = name;
  v->iv.valid = true;
  v->iv.lo_inf = false;
  v->iv.hi_inf = false;
  ixs_interval_set_lo_neg_inf(&v->iv);
  ixs_interval_set_hi_pos_inf(&v->iv);
  v->modulus = 0;
  v->remainder = 0;
  v->bits.known_zero = 0;
  v->bits.known_one = 0;
  v->bits.pow2 = IXS_POW2_UNKNOWN;
  b->var_index = prepared_index;
  b->var_index_cap = prepared_index_cap;
  slot = bounds_var_index_slot(b->var_index, b->var_index_cap, b->vars, name);
  b->var_index[slot] = *index + 1u;
  b->nvars++;
  bounds_mark_semantic_changed(b);
  return true;
}

static ixs_var_bound *get_or_create_var(ixs_bounds *b, const char *name) {
  size_t index;
  if (!get_or_create_var_index(b, name, &index))
    return NULL;
  return &b->vars[index];
}

static void bitfacts_unknown(ixs_bitfacts *bits) {
  bits->known_zero = 0;
  bits->known_one = 0;
  bits->pow2 = IXS_POW2_UNKNOWN;
}

static unsigned bit_popcount64(uint64_t v) {
  unsigned n = 0;
  while (v) {
    n += (unsigned)(v & 1u);
    v >>= 1;
  }
  return n;
}

static bool uint64_is_pow2(uint64_t v) { return v != 0 && (v & (v - 1u)) == 0; }

static bool int64_is_positive_pow2(int64_t v) {
  return v > 0 && uint64_is_pow2((uint64_t)v);
}

static bool int64_modulus_is_pow2(int64_t v) {
  return v > 0 && uint64_is_pow2((uint64_t)v);
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

static uint64_t value_span_mask(uint64_t hi) {
  uint64_t mask = 0;
  while (hi) {
    mask = (mask << 1) | 1u;
    hi >>= 1;
  }
  return mask;
}

static bool bitfacts_conflict(const ixs_bitfacts *bits) {
  if ((bits->known_zero & bits->known_one) != 0)
    return true;
  if ((bits->pow2 == IXS_POW2_OR_ZERO || bits->pow2 == IXS_POW2_POSITIVE) &&
      bit_popcount64(bits->known_one) > 1)
    return true;
  return false;
}

static bool interval_lower_at_least(const ixs_interval *iv, int64_t p,
                                    int64_t q) {
  return iv->valid && !iv->lo_inf && ixs_rat_cmp(iv->lo_p, iv->lo_q, p, q) >= 0;
}

static bool interval_upper_less_than(const ixs_interval *iv, int64_t p,
                                     int64_t q) {
  return iv->valid && !iv->hi_inf && ixs_rat_cmp(iv->hi_p, iv->hi_q, p, q) < 0;
}

static bool interval_exact_int(const ixs_interval *iv, int64_t *value) {
  if (!iv->valid || iv->lo_inf || iv->hi_inf || iv->lo_q != 1 ||
      iv->hi_q != 1 || iv->lo_p != iv->hi_p)
    return false;
  *value = iv->lo_p;
  return true;
}

static int64_t integer_congruence_residue(int64_t value, int64_t modulus) {
  int64_t residue = value % modulus;
  return residue < 0 ? residue + modulus : residue;
}

static bool integer_align_congruence_up(int64_t value, int64_t modulus,
                                        int64_t remainder, int64_t *out) {
  int64_t current, delta;
  if (modulus <= 0 || remainder < 0 || remainder >= modulus || !out)
    return false;
  current = integer_congruence_residue(value, modulus);
  delta = remainder >= current ? remainder - current
                               : modulus - (current - remainder);
  return ixs_safe_add(value, delta, out);
}

static bool integer_align_congruence_down(int64_t value, int64_t modulus,
                                          int64_t remainder, int64_t *out) {
  int64_t current, delta;
  if (modulus <= 0 || remainder < 0 || remainder >= modulus || !out)
    return false;
  current = integer_congruence_residue(value, modulus);
  delta = current >= remainder ? current - remainder
                               : modulus - (remainder - current);
  return ixs_safe_sub(value, delta, out);
}

static ixs_interval interval_intersect_congruence(ixs_interval iv,
                                                  int64_t modulus,
                                                  int64_t remainder) {
  int64_t aligned;
  if (!iv.valid || modulus <= 0)
    return iv;
  if (!iv.lo_inf && integer_align_congruence_up(ixs_rat_ceil(iv.lo_p, iv.lo_q),
                                                modulus, remainder, &aligned)) {
    iv.lo_p = aligned;
    iv.lo_q = 1;
  }
  if (!iv.hi_inf &&
      integer_align_congruence_down(ixs_rat_floor(iv.hi_p, iv.hi_q), modulus,
                                    remainder, &aligned)) {
    iv.hi_p = aligned;
    iv.hi_q = 1;
  }
  return iv;
}

static bool interval_has_congruent_integer(const ixs_interval *iv,
                                           int64_t modulus, int64_t remainder) {
  int64_t lo, hi, first;
  if (!iv->valid || iv->lo_inf || iv->hi_inf || modulus <= 0)
    return true;
  lo = ixs_rat_ceil(iv->lo_p, iv->lo_q);
  hi = ixs_rat_floor(iv->hi_p, iv->hi_q);
  if (lo > hi)
    return false;
  return integer_align_congruence_up(lo, modulus, remainder, &first) &&
         first <= hi;
}

static void refine_var_bit_consistency(ixs_bounds *b, ixs_var_bound *v) {
  int64_t exact;
  if (!v)
    return;
  bounds_empty_cache_invalidate(b);
  if (v->bits.pow2 == IXS_POW2_OR_ZERO &&
      interval_lower_at_least(&v->iv, 1, 1)) {
    v->bits.pow2 = IXS_POW2_POSITIVE;
    bounds_mark_semantic_changed(b);
  }
  if ((v->bits.pow2 == IXS_POW2_OR_ZERO &&
       interval_upper_less_than(&v->iv, 0, 1)) ||
      (v->bits.pow2 == IXS_POW2_POSITIVE &&
       interval_upper_less_than(&v->iv, 1, 1)))
    bounds_mark_contradiction(b);
  if (interval_exact_int(&v->iv, &exact)) {
    uint64_t u = (uint64_t)exact;
    if ((v->bits.known_zero & u) != 0 || (v->bits.known_one & ~u) != 0)
      bounds_mark_contradiction(b);
    if ((v->bits.pow2 == IXS_POW2_OR_ZERO ||
         v->bits.pow2 == IXS_POW2_POSITIVE) &&
        exact != 0 && !int64_is_positive_pow2(exact))
      bounds_mark_contradiction(b);
    if (v->bits.pow2 == IXS_POW2_POSITIVE && exact == 0)
      bounds_mark_contradiction(b);
  }
  if (v->modulus > 0 &&
      !interval_has_congruent_integer(&v->iv, v->modulus, v->remainder))
    bounds_mark_contradiction(b);
  if (bitfacts_conflict(&v->bits))
    bounds_mark_contradiction(b);
}

static void apply_var_known_bits(ixs_bounds *b, ixs_var_bound *v,
                                 uint64_t known_zero, uint64_t known_one) {
  uint64_t old_zero;
  uint64_t old_one;
  if (!v)
    return;
  old_zero = v->bits.known_zero;
  old_one = v->bits.known_one;
  v->bits.known_zero |= known_zero;
  v->bits.known_one |= known_one;
  if (old_zero != v->bits.known_zero || old_one != v->bits.known_one)
    bounds_mark_semantic_changed(b);
  refine_var_bit_consistency(b, v);
}

static void apply_known_bits(ixs_bounds *b, const char *name,
                             uint64_t known_zero, uint64_t known_one) {
  ixs_var_bound *v = get_or_create_var(b, name);
  apply_var_known_bits(b, v, known_zero, known_one);
}

static void apply_pow2_fact(ixs_bounds *b, ixs_var_bound *v,
                            ixs_pow2_fact pow2) {
  if (!v)
    return;
  if (pow2 == IXS_POW2_POSITIVE) {
    if (v->bits.pow2 == IXS_POW2_UNKNOWN || v->bits.pow2 == IXS_POW2_OR_ZERO) {
      v->bits.pow2 = IXS_POW2_POSITIVE;
      bounds_mark_semantic_changed(b);
    }
  } else if (pow2 == IXS_POW2_OR_ZERO && v->bits.pow2 == IXS_POW2_UNKNOWN) {
    v->bits.pow2 = IXS_POW2_OR_ZERO;
    bounds_mark_semantic_changed(b);
  }
  refine_var_bit_consistency(b, v);
}

static void apply_exact_int_bits(ixs_bounds *b, ixs_var_bound *v, int64_t val) {
  uint64_t u = (uint64_t)val;
  if (!v)
    return;
  apply_var_known_bits(b, v, ~u, u);
  if (val == 0) {
    if (v->bits.pow2 == IXS_POW2_POSITIVE)
      bounds_mark_contradiction(b);
    else if (v->bits.pow2 != IXS_POW2_OR_ZERO) {
      v->bits.pow2 = IXS_POW2_OR_ZERO;
      bounds_mark_semantic_changed(b);
    }
  } else if (int64_is_positive_pow2(val)) {
    if (v->bits.pow2 != IXS_POW2_POSITIVE) {
      v->bits.pow2 = IXS_POW2_POSITIVE;
      bounds_mark_semantic_changed(b);
    }
  } else if (v->bits.pow2 == IXS_POW2_OR_ZERO ||
             v->bits.pow2 == IXS_POW2_POSITIVE) {
    bounds_mark_contradiction(b);
  }
  refine_var_bit_consistency(b, v);
}

static void apply_congruence_known_bits(ixs_bounds *b, ixs_var_bound *v) {
  uint64_t mask, rem;
  if (!v || !int64_modulus_is_pow2(v->modulus))
    return;
  mask = (uint64_t)v->modulus - 1u;
  rem = (uint64_t)v->remainder & mask;
  apply_var_known_bits(b, v, (~rem) & mask, rem & mask);
}

static uint64_t bounds_normalize_residue(int64_t value, uint64_t modulus);
static uint64_t bounds_mul_mod(uint64_t a, uint64_t b, uint64_t modulus);
static bool bounds_mod_inverse(uint64_t value, uint64_t modulus,
                               uint64_t *inverse);

/* Record sym ≡ rem (mod m).  Merges with existing info via CRT.
 * Overflowing constraints are silently ignored.  Direct contradictions are
 * recorded on the bounds object so query APIs can decline concrete answers. */
static void apply_modrem(ixs_bounds *b, const char *name, int64_t m,
                         int64_t rem) {
  ixs_var_bound *v;
  int64_t g, new_mod, old_mod, step, m_div_g, difference;
  uint64_t inverse, k, merged;
  bool changed = false;
  if (m <= 0)
    return;
  bounds_empty_cache_invalidate(b);
  rem = (int64_t)bounds_normalize_residue(rem, (uint64_t)m);
  v = get_or_create_var(b, name);
  if (!v)
    return;
  b->has_modrem = true;
  if (v->modulus == 0) {
    v->modulus = m;
    v->remainder = rem;
    bounds_mark_semantic_changed(b);
    apply_congruence_known_bits(b, v);
    bounds_propagate_difference_bounds(b, name, NULL);
    return;
  }
  old_mod = v->modulus;
  g = ixs_gcd(old_mod, m);
  difference = rem - v->remainder;
  if (bounds_normalize_residue(difference, (uint64_t)g) != 0) {
    bounds_mark_contradiction(b);
    return;
  }
  if (old_mod > INT64_MAX / (m / g))
    return;
  new_mod = old_mod / g * m;
  /* Solve old_mod/g * k == (rem - old_remainder)/g (mod m/g).
   * Keep the modular arithmetic bounded so large public moduli do not turn
   * this merge into either an overflow or a linear scan. */
  step = old_mod / g;
  m_div_g = m / g;
  if (m_div_g == 1) {
    k = 0;
  } else {
    uint64_t target =
        bounds_normalize_residue(difference / g, (uint64_t)m_div_g);
    if (!bounds_mod_inverse((uint64_t)step, (uint64_t)m_div_g, &inverse))
      return;
    k = bounds_mul_mod(target, inverse, (uint64_t)m_div_g);
  }
  merged = bounds_mul_mod((uint64_t)old_mod, k, (uint64_t)new_mod);
  merged += (uint64_t)v->remainder;
  rem = (int64_t)(merged % (uint64_t)new_mod);
  if (v->modulus != new_mod || v->remainder != rem) {
    v->modulus = new_mod;
    v->remainder = rem;
    bounds_mark_semantic_changed(b);
    changed = true;
  }
  apply_congruence_known_bits(b, v);
  if (changed)
    bounds_propagate_difference_bounds(b, name, NULL);
}

/* Recognize Mod(sym, M) == R as a modular congruence.
 *
 * Depends on the CMP normalizer in simp_cmp (cmp_normalize_to_zero):
 * "Mod(sym,M) == R" is rewritten to "(Mod(sym,M) - R) == 0", producing an
 * ADD node.  We must handle both the direct form (R == 0, no normalization)
 * and the normalized ADD form (R != 0). */
static void extract_modrem(ixs_bounds *b, ixs_node *a) {
  ixs_node *mod_node;
  int64_t rem_val;

  if (a->tag != IXS_CMP || a->u.binary.cmp_op != IXS_CMP_EQ)
    return;

  ixs_node *lhs = a->u.binary.lhs;
  ixs_node *rhs = a->u.binary.rhs;

  /* Direct: Mod(sym, M) == 0 */
  if (lhs->tag == IXS_MOD && ixs_node_is_zero(rhs)) {
    mod_node = lhs;
    rem_val = 0;
  } else if (rhs->tag == IXS_MOD && ixs_node_is_zero(lhs)) {
    mod_node = rhs;
    rem_val = 0;
  }
  /* Normalized: ADD(k, c*Mod(sym, M)) == 0, where c = ±1 and k is integer.
   * c=1:  Mod(sym,M) == -k;   c=-1: Mod(sym,M) == k. */
  else if (ixs_node_is_zero(rhs) && lhs->tag == IXS_ADD &&
           lhs->u.add.nterms == 1 && lhs->u.add.terms[0].term->tag == IXS_MOD) {
    int64_t cp, cq, kp, kq;
    ixs_node_get_rat(lhs->u.add.terms[0].coeff, &cp, &cq);
    ixs_node_get_rat(lhs->u.add.coeff, &kp, &kq);
    if (cq != 1 || kq != 1)
      return;
    if (cp == 1) {
      if (kp == INT64_MIN)
        return;
      rem_val = -kp;
    } else if (cp == -1) {
      rem_val = kp;
    } else {
      return;
    }
    mod_node = lhs->u.add.terms[0].term;
  } else {
    return;
  }

  /* Validate Mod operands and record the congruence. */
  {
    ixs_node *dividend = mod_node->u.binary.lhs;
    ixs_node *modulus = mod_node->u.binary.rhs;
    if (dividend->tag != IXS_SYM || modulus->tag != IXS_INT ||
        modulus->u.ival <= 0)
      return;
    rem_val =
        (int64_t)bounds_normalize_residue(rem_val, (uint64_t)modulus->u.ival);
    apply_modrem(b, dividend->u.name, modulus->u.ival, rem_val);
  }
}

static ixs_cmp_op flip_cmp(ixs_cmp_op op) {
  switch (op) {
  case IXS_CMP_GE:
    return IXS_CMP_LE;
  case IXS_CMP_GT:
    return IXS_CMP_LT;
  case IXS_CMP_LE:
    return IXS_CMP_GE;
  case IXS_CMP_LT:
    return IXS_CMP_GT;
  default:
    return op;
  }
}

static ixs_interval interval_from_integer_zero_cmp(ixs_cmp_op op) {
  ixs_interval iv = ixs_interval_unknown();
  iv.lo_inf = false;
  iv.hi_inf = false;
  switch (op) {
  case IXS_CMP_GT:
    iv.valid = true;
    iv.lo_p = 1;
    iv.lo_q = 1;
    ixs_interval_set_hi_pos_inf(&iv);
    break;
  case IXS_CMP_GE:
    iv.valid = true;
    iv.lo_p = 0;
    iv.lo_q = 1;
    ixs_interval_set_hi_pos_inf(&iv);
    break;
  case IXS_CMP_LT:
    iv.valid = true;
    ixs_interval_set_lo_neg_inf(&iv);
    iv.hi_p = -1;
    iv.hi_q = 1;
    break;
  case IXS_CMP_LE:
    iv.valid = true;
    ixs_interval_set_lo_neg_inf(&iv);
    iv.hi_p = 0;
    iv.hi_q = 1;
    break;
  case IXS_CMP_EQ:
    iv = ixs_interval_exact(0, 1);
    break;
  case IXS_CMP_NE:
    break;
  }
  return iv;
}

static ixs_interval interval_from_sym_cmp_const(ixs_cmp_op op, int64_t cp,
                                                int64_t cq) {
  ixs_interval iv = ixs_interval_unknown();
  iv.lo_inf = false;
  iv.hi_inf = false;
  switch (op) {
  case IXS_CMP_GE:
    iv.valid = true;
    iv.lo_p = cp;
    iv.lo_q = cq;
    ixs_interval_set_hi_pos_inf(&iv);
    break;
  case IXS_CMP_GT: {
    int64_t lo;
    if (!ixs_safe_add(ixs_rat_floor(cp, cq), 1, &lo))
      break;
    iv.valid = true;
    iv.lo_p = lo;
    iv.lo_q = 1;
    ixs_interval_set_hi_pos_inf(&iv);
    break;
  }
  case IXS_CMP_LE:
    iv.valid = true;
    ixs_interval_set_lo_neg_inf(&iv);
    iv.hi_p = cp;
    iv.hi_q = cq;
    break;
  case IXS_CMP_LT: {
    int64_t hi;
    if (!ixs_safe_sub(ixs_rat_ceil(cp, cq), 1, &hi))
      break;
    iv.valid = true;
    ixs_interval_set_lo_neg_inf(&iv);
    iv.hi_p = hi;
    iv.hi_q = 1;
    break;
  }
  case IXS_CMP_EQ:
    iv = ixs_interval_exact(cp, cq);
    break;
  case IXS_CMP_NE:
    break;
  }
  return iv;
}

/* Cache hits are expected O(1); a miss rebuilds the n immediate ADD terms. */
static ixs_node *bounds_expr_without_add_const(ixs_bounds *b, ixs_node *expr) {
  ixs_node *cached;
  ixs_node *result;
  uint32_t i;
  if (!b || !b->ctx || !expr || expr->tag != IXS_ADD ||
      ixs_node_is_zero(expr->u.add.coeff) || expr->u.add.nterms == 0)
    return NULL;

  cached = ixs_node_transform_cache_lookup(
      b->ctx, expr, IXS_NODE_TRANSFORM_ADD_WITHOUT_CONST);
  if (cached)
    return cached;

  result = b->ctx->node_zero;
  for (i = 0; i < expr->u.add.nterms; i++) {
    ixs_node *term = expr->u.add.terms[i].term;
    ixs_node *coeff = expr->u.add.terms[i].coeff;
    ixs_node *scaled =
        ixs_node_is_one(coeff) ? term : simp_mul(b->ctx, coeff, term);
    if (!scaled) {
      b->oom = true;
      return NULL;
    }
    result = simp_add(b->ctx, result, scaled);
    if (!result) {
      b->oom = true;
      return NULL;
    }
  }
  ixs_node_transform_cache_store(b->ctx, expr,
                                 IXS_NODE_TRANSFORM_ADD_WITHOUT_CONST, result);
  return result;
}

/*
 * Write an ADD as offset + scale * primitive, using its first canonical term
 * coefficient as scale. The transform cache makes repeated range queries
 * O(1); a miss is linear only in the immediate ADD terms.
 */
static bool bounds_get_proportional_primitive(
    ixs_bounds *b, ixs_node *expr, ixs_node **primitive, int64_t *scale_p,
    int64_t *scale_q, int64_t *offset_p, int64_t *offset_q) {
  ixs_node *normalized;
  ixs_addterm *terms;
  ixs_arena_mark mark;
  size_t term_bytes;
  uint32_t i;
  /* Context-free proof scopes intentionally disable canonical alias creation.
   */
  if (!b->ctx)
    return false;

  if (expr->tag != IXS_ADD || expr->u.add.nterms == 0)
    return false;
  ixs_node_get_rat(expr->u.add.terms[0].coeff, scale_p, scale_q);
  ixs_node_get_rat(expr->u.add.coeff, offset_p, offset_q);
  if (*scale_p == 0)
    return false;

  normalized = ixs_node_transform_cache_lookup(
      b->ctx, expr, IXS_NODE_TRANSFORM_PROPORTIONAL_PRIMITIVE);
  if (!normalized) {
    mark = ixs_arena_save(b->scratch);
    term_bytes = (size_t)expr->u.add.nterms * sizeof(*terms);
    if (term_bytes / sizeof(*terms) != expr->u.add.nterms) {
      b->oom = true;
      ixs_arena_restore(b->scratch, mark);
      return false;
    }
    terms = ixs_arena_alloc(b->scratch, term_bytes, sizeof(void *));
    if (!terms) {
      b->oom = true;
      ixs_arena_restore(b->scratch, mark);
      return false;
    }
    for (i = 0; i < expr->u.add.nterms; i++) {
      int64_t coeff_p, coeff_q, normalized_p, normalized_q;
      ixs_node_get_rat(expr->u.add.terms[i].coeff, &coeff_p, &coeff_q);
      if (!ixs_rat_div(coeff_p, coeff_q, *scale_p, *scale_q, &normalized_p,
                       &normalized_q)) {
        ixs_arena_restore(b->scratch, mark);
        return false;
      }
      terms[i].term = expr->u.add.terms[i].term;
      terms[i].coeff = ixs_node_rat(b->ctx, normalized_p, normalized_q);
      if (!terms[i].coeff) {
        b->oom = true;
        ixs_arena_restore(b->scratch, mark);
        return false;
      }
    }
    /* Dividing by the first coefficient makes this coefficient exactly one. */
    normalized = expr->u.add.nterms == 1
                     ? terms[0].term
                     : ixs_node_add(b->ctx, b->ctx->node_zero,
                                    expr->u.add.nterms, terms);
    ixs_arena_restore(b->scratch, mark);
    if (!normalized) {
      b->oom = true;
      return false;
    }
    if (ixs_node_is_sentinel(normalized))
      return false;
    ixs_node_transform_cache_store(
        b->ctx, expr, IXS_NODE_TRANSFORM_PROPORTIONAL_PRIMITIVE, normalized);
  }
  *primitive = normalized;
  return true;
}

static ixs_interval bounds_apply_affine(ixs_interval iv, int64_t scale_p,
                                        int64_t scale_q, int64_t offset_p,
                                        int64_t offset_q) {
  return iv_add(iv_mul_const(iv, scale_p, scale_q),
                ixs_interval_exact(offset_p, offset_q));
}

static ixs_interval bounds_invert_affine(ixs_interval iv, int64_t scale_p,
                                         int64_t scale_q, int64_t offset_p,
                                         int64_t offset_q) {
  int64_t neg_p, neg_q, inverse_p, inverse_q;
  if (!ixs_rat_neg(offset_p, offset_q, &neg_p, &neg_q) ||
      !ixs_rat_div(1, 1, scale_p, scale_q, &inverse_p, &inverse_q))
    return ixs_interval_unknown();
  return iv_mul_const(iv_add(iv, ixs_interval_exact(neg_p, neg_q)), inverse_p,
                      inverse_q);
}

static void add_shifted_add_range(ixs_bounds *b, ixs_node *expr,
                                  ixs_interval iv) {
  ixs_node *base;
  int64_t cp, cq, np, nq;
  ixs_interval offset, shifted;

  base = bounds_expr_without_add_const(b, expr);
  if (!base || base == expr)
    return;
  ixs_node_get_rat(expr->u.add.coeff, &cp, &cq);
  if (!ixs_rat_neg(cp, cq, &np, &nq))
    return;
  offset = ixs_interval_exact(np, nq);
  shifted = iv_add(iv, offset);
  if (shifted.valid)
    ixs_bounds_add_expr(b, base, shifted);
}

static void add_expr_integer_zero_cmp(ixs_bounds *b, ixs_node *expr,
                                      ixs_cmp_op op) {
  ixs_interval iv;
  if (!ixs_node_is_integer_valued(expr))
    return;
  iv = interval_from_integer_zero_cmp(op);
  if (!iv.valid)
    return;
  ixs_bounds_add_expr(b, expr, iv);
  add_shifted_add_range(b, expr, iv);
}

/*
 * Apply "sym op const" bound to the variable's interval.
 */
static void apply_sym_cmp_const(ixs_bounds *b, const char *name, ixs_cmp_op op,
                                int64_t cp, int64_t cq) {
  ixs_var_bound *v = get_or_create_var(b, name);
  ixs_interval old;
  bool changed;
  if (!v)
    return;
  old = v->iv;
  switch (op) {
  case IXS_CMP_GE:
    if (v->iv.lo_inf || ixs_rat_cmp(cp, cq, v->iv.lo_p, v->iv.lo_q) > 0) {
      v->iv.lo_p = cp;
      v->iv.lo_q = cq;
      v->iv.lo_inf = false;
    }
    break;
  case IXS_CMP_GT: {
    int64_t lo;
    if (!ixs_safe_add(ixs_rat_floor(cp, cq), 1, &lo))
      break;
    if (v->iv.lo_inf || ixs_rat_cmp(lo, 1, v->iv.lo_p, v->iv.lo_q) > 0) {
      v->iv.lo_p = lo;
      v->iv.lo_q = 1;
      v->iv.lo_inf = false;
    }
    break;
  }
  case IXS_CMP_LE:
    if (v->iv.hi_inf || ixs_rat_cmp(cp, cq, v->iv.hi_p, v->iv.hi_q) < 0) {
      v->iv.hi_p = cp;
      v->iv.hi_q = cq;
      v->iv.hi_inf = false;
    }
    break;
  case IXS_CMP_LT: {
    int64_t hi;
    if (!ixs_safe_sub(ixs_rat_ceil(cp, cq), 1, &hi))
      break;
    if (v->iv.hi_inf || ixs_rat_cmp(hi, 1, v->iv.hi_p, v->iv.hi_q) < 0) {
      v->iv.hi_p = hi;
      v->iv.hi_q = 1;
      v->iv.hi_inf = false;
    }
    break;
  }
  case IXS_CMP_EQ:
    v->iv.lo_p = cp;
    v->iv.lo_q = cq;
    v->iv.hi_p = cp;
    v->iv.hi_q = cq;
    v->iv.lo_inf = false;
    v->iv.hi_inf = false;
    if (cq == 1)
      apply_exact_int_bits(b, v, cp);
    break;
  case IXS_CMP_NE:
    break;
  }
  changed = !bounds_intervals_equal(old, v->iv);
  if (changed)
    bounds_mark_semantic_changed(b);
  refine_var_bit_consistency(b, v);
  if (changed)
    bounds_propagate_difference_bounds(b, name, NULL);
}

static bool node_get_int_const(ixs_node *n, int64_t *out) {
  if (!n || !out)
    return false;
  if (n->tag == IXS_INT) {
    *out = n->u.ival;
    return true;
  }
  if (n->tag == IXS_RAT && n->u.rat.q == 1) {
    *out = n->u.rat.p;
    return true;
  }
  return false;
}

static bool node_coeff_is(ixs_node *n, int64_t value) {
  int64_t p, q;
  if (!n)
    return false;
  ixs_node_get_rat(n, &p, &q);
  return p == value && q == 1;
}

static bool extract_add_term_eq_const(ixs_node *n, ixs_node **expr,
                                      int64_t *value) {
  int64_t kp, kq, cp, cq;
  if (!n || n->tag != IXS_ADD || n->u.add.nterms != 1)
    return false;
  ixs_node_get_rat(n->u.add.coeff, &kp, &kq);
  ixs_node_get_rat(n->u.add.terms[0].coeff, &cp, &cq);
  if (kq != 1 || cq != 1)
    return false;
  if (cp == 1) {
    if (kp == INT64_MIN)
      return false;
    *value = -kp;
  } else if (cp == -1) {
    *value = kp;
  } else {
    return false;
  }
  *expr = n->u.add.terms[0].term;
  return true;
}

/* Recover "expr == integer" from either direct comparisons or the normalized
 * ADD(k, +/-expr) == 0 form produced by cmp_normalize_to_zero. */
static bool extract_cmp_expr_const(ixs_node *cmp, ixs_node **expr,
                                   int64_t *value) {
  int64_t c;
  if (!cmp || cmp->tag != IXS_CMP || !expr || !value)
    return false;

  if (ixs_node_is_zero(cmp->u.binary.rhs) &&
      extract_add_term_eq_const(cmp->u.binary.lhs, expr, value))
    return true;
  if (ixs_node_is_zero(cmp->u.binary.lhs) &&
      extract_add_term_eq_const(cmp->u.binary.rhs, expr, value))
    return true;

  if (node_get_int_const(cmp->u.binary.rhs, &c) &&
      !ixs_node_is_const(cmp->u.binary.lhs)) {
    *expr = cmp->u.binary.lhs;
    *value = c;
    return true;
  }
  if (node_get_int_const(cmp->u.binary.lhs, &c) &&
      !ixs_node_is_const(cmp->u.binary.rhs)) {
    *expr = cmp->u.binary.rhs;
    *value = c;
    return true;
  }

  return false;
}

static bool extract_add_node_equality(ixs_node *n, ixs_node **a, ixs_node **b) {
  int64_t kp, kq;
  const ixs_addterm *t0, *t1;
  if (!n || n->tag != IXS_ADD || n->u.add.nterms != 2)
    return false;
  ixs_node_get_rat(n->u.add.coeff, &kp, &kq);
  if (kp != 0 || kq != 1)
    return false;
  t0 = &n->u.add.terms[0];
  t1 = &n->u.add.terms[1];
  if (node_coeff_is(t0->coeff, 1) && node_coeff_is(t1->coeff, -1)) {
    *a = t0->term;
    *b = t1->term;
    return true;
  }
  if (node_coeff_is(t0->coeff, -1) && node_coeff_is(t1->coeff, 1)) {
    *a = t0->term;
    *b = t1->term;
    return true;
  }
  return false;
}

static bool extract_cmp_node_equality(ixs_node *cmp, ixs_node **a,
                                      ixs_node **b) {
  if (!cmp || cmp->tag != IXS_CMP || cmp->u.binary.cmp_op != IXS_CMP_EQ)
    return false;
  if (ixs_node_is_zero(cmp->u.binary.rhs))
    return extract_add_node_equality(cmp->u.binary.lhs, a, b);
  if (ixs_node_is_zero(cmp->u.binary.lhs))
    return extract_add_node_equality(cmp->u.binary.rhs, a, b);
  if (!ixs_node_is_const(cmp->u.binary.lhs) &&
      !ixs_node_is_const(cmp->u.binary.rhs)) {
    *a = cmp->u.binary.lhs;
    *b = cmp->u.binary.rhs;
    return true;
  }
  return false;
}

static bool sym_name_matches(ixs_node *n, const char *name) {
  return n && n->tag == IXS_SYM && n->u.name == name;
}

static bool node_is_sym_minus_one(ixs_node *n, const char *name) {
  int64_t kp, kq, cp, cq;
  if (!n || n->tag != IXS_ADD || n->u.add.nterms != 1 ||
      !sym_name_matches(n->u.add.terms[0].term, name))
    return false;
  ixs_node_get_rat(n->u.add.coeff, &kp, &kq);
  ixs_node_get_rat(n->u.add.terms[0].coeff, &cp, &cq);
  return kp == -1 && kq == 1 && cp == 1 && cq == 1;
}

static bool extract_pow2_and(ixs_node *expr, const char **name) {
  ixs_node *a, *b;
  if (!expr || expr->tag != IXS_AND || expr->u.assoc.nargs != 2 || !name)
    return false;
  a = expr->u.assoc.args[0];
  b = expr->u.assoc.args[1];
  if (a->tag == IXS_SYM && node_is_sym_minus_one(b, a->u.name)) {
    *name = a->u.name;
    return true;
  }
  if (b->tag == IXS_SYM && node_is_sym_minus_one(a, b->u.name)) {
    *name = b->u.name;
    return true;
  }
  return false;
}

static bool extract_bitop_sym_mask(ixs_node *expr, ixs_tag tag,
                                   const char **name, int64_t *mask) {
  ixs_node *a, *b;
  if (!expr || expr->tag != tag || expr->u.assoc.nargs != 2 || !name || !mask)
    return false;
  a = expr->u.assoc.args[0];
  b = expr->u.assoc.args[1];
  if (a->tag == IXS_SYM && node_get_int_const(b, mask)) {
    *name = a->u.name;
    return true;
  }
  if (b->tag == IXS_SYM && node_get_int_const(a, mask)) {
    *name = b->u.name;
    return true;
  }
  return false;
}

static void apply_pow2_or_zero(ixs_bounds *b, const char *name) {
  ixs_var_bound *v = get_or_create_var(b, name);
  if (!v)
    return;
  if (v->bits.pow2 == IXS_POW2_UNKNOWN) {
    v->bits.pow2 = IXS_POW2_OR_ZERO;
    bounds_mark_semantic_changed(b);
  }
  refine_var_bit_consistency(b, v);
  apply_sym_cmp_const(b, name, IXS_CMP_GE, 0, 1);
}

static void extract_bitfacts_from_const_eq(ixs_bounds *b, ixs_node *expr,
                                           int64_t value) {
  const char *name;
  int64_t mask;
  uint64_t mask_bits, value_bits;

  if (extract_pow2_and(expr, &name)) {
    if (value == 0)
      apply_pow2_or_zero(b, name);
    return;
  }

  if (extract_bitop_sym_mask(expr, IXS_AND, &name, &mask)) {
    mask_bits = (uint64_t)mask;
    value_bits = (uint64_t)value;
    if ((value_bits & ~mask_bits) != 0) {
      bounds_mark_contradiction(b);
      return;
    }
    apply_known_bits(b, name, (~value_bits) & mask_bits,
                     value_bits & mask_bits);
    return;
  }

  if (extract_bitop_sym_mask(expr, IXS_OR, &name, &mask)) {
    mask_bits = (uint64_t)mask;
    value_bits = (uint64_t)value;
    if ((value_bits & mask_bits) != mask_bits) {
      bounds_mark_contradiction(b);
      return;
    }
    apply_known_bits(b, name, ~value_bits, value_bits & ~mask_bits);
  }
}

static void extract_bitfacts_from_node_eq(ixs_bounds *b, ixs_node *a,
                                          ixs_node *other) {
  const char *name;
  int64_t mask;
  uint64_t mask_bits;

  if (other->tag != IXS_SYM)
    return;
  if (extract_bitop_sym_mask(a, IXS_OR, &name, &mask) &&
      name == other->u.name) {
    apply_known_bits(b, name, 0, (uint64_t)mask);
    return;
  }
  if (extract_bitop_sym_mask(a, IXS_AND, &name, &mask) &&
      name == other->u.name) {
    mask_bits = (uint64_t)mask;
    apply_known_bits(b, name, ~mask_bits, 0);
  }
}

static void extract_bitfacts(ixs_bounds *b, ixs_node *a) {
  ixs_node *expr, *lhs, *rhs;
  int64_t value;
  if (a->tag != IXS_CMP || a->u.binary.cmp_op != IXS_CMP_EQ)
    return;

  if (extract_cmp_expr_const(a, &expr, &value))
    extract_bitfacts_from_const_eq(b, expr, value);

  if (extract_cmp_node_equality(a, &lhs, &rhs)) {
    extract_bitfacts_from_node_eq(b, lhs, rhs);
    extract_bitfacts_from_node_eq(b, rhs, lhs);
  }
}

static ixs_node *bounds_simplify_fact_free(ixs_ctx *ctx, ixs_node *expr) {
  ixs_arena_mark mark = ixs_arena_save(&ctx->scratch);
  ixs_bounds empty;
  ixs_node *result = NULL;
  if (ixs_bounds_init_ctx(&empty, ctx, &ctx->scratch)) {
    result = simp_simplify_bounds(ctx, expr, &empty);
    if (empty.oom)
      result = NULL;
    ixs_bounds_destroy(&empty);
  }
  ixs_arena_restore(&ctx->scratch, mark);
  return result;
}

static ixs_node *bounds_canonical_expr(ixs_bounds *b, ixs_node *expr) {
  ixs_node *cached, *canonical, *expanded;
  ixs_arena_mark diag_mark;
  const char **saved_errors;
  size_t saved_nerrors, saved_errors_cap;
  if (!b || !b->ctx || !expr || ixs_node_is_sentinel(expr))
    return expr;
  if (expr->tag == IXS_INT || expr->tag == IXS_RAT || expr->tag == IXS_SYM)
    return expr;

  cached = ixs_node_transform_cache_lookup(b->ctx, expr,
                                           IXS_NODE_TRANSFORM_BOUNDS_CANONICAL);
  if (cached)
    return cached;

  /* Alias diagnostics must not leak into otherwise valid range queries. */
  diag_mark = ixs_arena_save(&b->ctx->diag);
  saved_errors = b->ctx->errors;
  saved_nerrors = b->ctx->nerrors;
  saved_errors_cap = b->ctx->errors_cap;
  expanded = expand_impl(b->ctx, expr);
  canonical = expanded && !ixs_node_is_sentinel(expanded)
                  ? bounds_simplify_fact_free(b->ctx, expanded)
                  : expanded;
  ixs_arena_restore(&b->ctx->diag, diag_mark);
  b->ctx->errors = saved_errors;
  b->ctx->nerrors = saved_nerrors;
  b->ctx->errors_cap = saved_errors_cap;

  if (!expanded) {
    b->oom = true;
    return expr;
  }
  if (ixs_node_is_sentinel(expanded))
    return expr;
  if (!canonical) {
    b->oom = true;
    return expr;
  }
  if (ixs_node_is_sentinel(canonical))
    return expanded;
  ixs_node_transform_cache_store(
      b->ctx, expr, IXS_NODE_TRANSFORM_BOUNDS_CANONICAL, canonical);
  return canonical;
}

/* Pointer hashing and bounded linear probing keep range lookup expected O(1).
 */
static size_t bounds_expr_hash_ptr(const ixs_node *expr) {
  return bounds_hash_ptr(expr);
}

static size_t bounds_expr_index_slot(const size_t *index, size_t capacity,
                                     const ixs_expr_bound *exprs,
                                     const ixs_node *expr) {
  size_t slot = bounds_expr_hash_ptr(expr) & (capacity - 1u);
  while (index[slot] && exprs[index[slot] - 1u].expr != expr)
    slot = (slot + 1u) & (capacity - 1u);
  return slot;
}

static ixs_interval bounds_get_expr_overrides(ixs_bounds *b, ixs_node *expr) {
  size_t slot;
  if (!b || !expr || !b->expr_index || !b->expr_index_cap)
    return ixs_interval_unknown();
  slot =
      bounds_expr_index_slot(b->expr_index, b->expr_index_cap, b->exprs, expr);
  if (!b->expr_index[slot])
    return ixs_interval_unknown();
  return b->exprs[b->expr_index[slot] - 1u].iv;
}

/*
 * Rebuilds only at 75% load. Growth is amortized O(1), and publication stays
 * with the caller so a later dense-array allocation cannot split the index.
 */
static bool bounds_prepare_expr_index(ixs_bounds *b, size_t count,
                                      size_t **prepared,
                                      size_t *prepared_capacity) {
  size_t capacity = b->expr_index_cap;
  size_t *index;
  size_t i;

  if (capacity && count <= capacity - capacity / 4u) {
    *prepared = b->expr_index;
    *prepared_capacity = capacity;
    return true;
  }
  if (!capacity)
    capacity = BOUNDS_EXPR_INDEX_INIT_CAP;
  while (count > capacity - capacity / 4u) {
    if (capacity > SIZE_MAX / 2u)
      return false;
    capacity *= 2u;
  }
  if (capacity > SIZE_MAX / sizeof(*index))
    return false;
  index =
      ixs_arena_alloc(b->scratch, capacity * sizeof(*index), sizeof(void *));
  if (!index)
    return false;
  memset(index, 0, capacity * sizeof(*index));
  for (i = 0; i < b->nexprs; i++) {
    size_t slot =
        bounds_expr_index_slot(index, capacity, b->exprs, b->exprs[i].expr);
    index[slot] = i + 1u;
  }
  *prepared = index;
  *prepared_capacity = capacity;
  return true;
}

static void bounds_add_expr_raw(ixs_bounds *b, ixs_node *expr,
                                ixs_interval iv) {
  ixs_expr_bound *exprs;
  size_t *index;
  size_t expr_capacity;
  size_t index_capacity;
  size_t slot;

  if (!b || !expr || !iv.valid || b->oom)
    return;

  if (b->expr_index_cap) {
    slot = bounds_expr_index_slot(b->expr_index, b->expr_index_cap, b->exprs,
                                  expr);
    if (b->expr_index[slot]) {
      ixs_expr_bound *bound = &b->exprs[b->expr_index[slot] - 1u];
      if (bound->iv.valid) {
        ixs_interval refined = iv_intersect(bound->iv, iv);
        if (!bounds_intervals_equal(bound->iv, refined)) {
          bound->iv = refined;
          bounds_mark_semantic_changed(b);
        }
      }
      bounds_cache_clear(b);
      return;
    }
  }

  if (b->nexprs == SIZE_MAX ||
      !bounds_prepare_expr_index(b, b->nexprs + 1u, &index, &index_capacity)) {
    b->oom = true;
    return;
  }

  exprs = b->exprs;
  expr_capacity = b->expr_cap;
  if (b->nexprs >= expr_capacity) {
    if (expr_capacity > SIZE_MAX / 2u) {
      b->oom = true;
      return;
    }
    expr_capacity = expr_capacity ? expr_capacity * 2u : 4u;
    if (expr_capacity > SIZE_MAX / sizeof(*exprs)) {
      b->oom = true;
      return;
    }
    exprs = ixs_arena_alloc(b->scratch, expr_capacity * sizeof(*exprs),
                            sizeof(void *));
    if (!exprs) {
      b->oom = true;
      return;
    }
    if (b->nexprs)
      memcpy(exprs, b->exprs, b->nexprs * sizeof(*exprs));
  }

  b->exprs = exprs;
  b->expr_cap = expr_capacity;
  b->expr_index = index;
  b->expr_index_cap = index_capacity;
  slot =
      bounds_expr_index_slot(b->expr_index, b->expr_index_cap, b->exprs, expr);
  b->exprs[b->nexprs].expr = expr;
  b->exprs[b->nexprs].iv = iv;
  b->expr_index[slot] = b->nexprs + 1u;
  b->nexprs++;
  bounds_mark_semantic_changed(b);
  bounds_cache_clear(b);
}

static size_t bounds_difference_hash(ixs_node *lhs, ixs_node *rhs,
                                     int64_t offset) {
  uint64_t x = (uint64_t)bounds_expr_hash_ptr(lhs);
  x ^= (uint64_t)bounds_expr_hash_ptr(rhs) + UINT64_C(0x9e3779b97f4a7c15) +
       (x << 6) + (x >> 2);
  x ^= (uint64_t)offset + UINT64_C(0x9e3779b97f4a7c15) + (x << 6) + (x >> 2);
  x ^= x >> 33;
  x *= UINT64_C(0xff51afd7ed558ccd);
  x ^= x >> 33;
  return (size_t)x;
}

/* Exact-edge lookup is expected O(1); growth rehashes at 75% load. */
static size_t
bounds_difference_index_slot(ixs_difference_constraint *const *index,
                             size_t capacity, ixs_node *lhs, ixs_node *rhs,
                             int64_t offset) {
  size_t slot = bounds_difference_hash(lhs, rhs, offset) & (capacity - 1u);
  while (index[slot] && (index[slot]->lhs != lhs || index[slot]->rhs != rhs ||
                         index[slot]->offset != offset))
    slot = (slot + 1u) & (capacity - 1u);
  return slot;
}

static bool
bounds_prepare_difference_index(ixs_bounds *b, size_t count,
                                ixs_difference_constraint ***prepared,
                                size_t *prepared_capacity) {
  size_t capacity = b->difference_index_cap;
  ixs_difference_constraint **index;
  size_t i;

  if (capacity && count <= capacity - capacity / 4u) {
    *prepared = b->difference_index;
    *prepared_capacity = capacity;
    return true;
  }
  if (!capacity)
    capacity = BOUNDS_DIFFERENCE_INDEX_INIT_CAP;
  while (count > capacity - capacity / 4u) {
    if (capacity > SIZE_MAX / 2u)
      return false;
    capacity *= 2u;
  }
  if (capacity > SIZE_MAX / sizeof(*index))
    return false;
  index =
      ixs_arena_alloc(b->scratch, capacity * sizeof(*index), sizeof(void *));
  if (!index)
    return false;
  memset(index, 0, capacity * sizeof(*index));
  for (i = 0; i < b->difference_index_cap; i++) {
    ixs_difference_constraint *edge = b->difference_index[i];
    size_t slot;
    if (!edge)
      continue;
    slot = bounds_difference_index_slot(index, capacity, edge->lhs, edge->rhs,
                                        edge->offset);
    index[slot] = edge;
  }
  *prepared = index;
  *prepared_capacity = capacity;
  return true;
}

/* Relation metadata is absent from non-relational fact sets. Geometric growth
 * keeps appending graph variables amortized O(1) while stable var indices keep
 * the parallel table independent of var-array relocation. */
static bool bounds_prepare_difference_vars(ixs_bounds *b, size_t count) {
  ixs_difference_var *vars;
  size_t capacity = b->difference_var_cap;
  size_t old_bytes;
  size_t new_bytes;

  if (count <= capacity)
    return true;
  if (!capacity)
    capacity = 1u;
  while (capacity < count) {
    if (capacity > SIZE_MAX / 2u)
      return false;
    capacity *= 2u;
  }
  if (b->difference_var_cap > SIZE_MAX / sizeof(*vars) ||
      capacity > SIZE_MAX / sizeof(*vars))
    return false;
  old_bytes = b->difference_var_cap * sizeof(*vars);
  new_bytes = capacity * sizeof(*vars);
  vars = ixs_arena_grow(b->scratch, b->difference_vars, old_bytes, new_bytes,
                        sizeof(void *));
  if (!vars)
    return false;
  memset(vars + b->difference_var_cap, 0,
         (capacity - b->difference_var_cap) * sizeof(*vars));
  b->difference_vars = vars;
  b->difference_var_cap = capacity;
  return true;
}

static size_t bounds_exact_hash(size_t var_index) {
  uint64_t x = (uint64_t)var_index + UINT64_C(0x9e3779b97f4a7c15);
  x ^= x >> 33;
  x *= UINT64_C(0xff51afd7ed558ccd);
  x ^= x >> 33;
  return (size_t)x;
}

static size_t bounds_exact_index_slot(const size_t *index, size_t capacity,
                                      const ixs_exact_var *vars,
                                      size_t var_index) {
  size_t slot = bounds_exact_hash(var_index) & (capacity - 1u);
  while (index[slot] && vars[index[slot] - 1u].var_index != var_index)
    slot = (slot + 1u) & (capacity - 1u);
  return slot;
}

static bool bounds_exact_lookup(const ixs_bounds *b, size_t var_index,
                                size_t *exact_index) {
  size_t slot;
  if (!b->exact_index || !b->exact_index_cap)
    return false;
  slot = bounds_exact_index_slot(b->exact_index, b->exact_index_cap,
                                 b->exact_vars, var_index);
  if (!b->exact_index[slot])
    return false;
  *exact_index = b->exact_index[slot] - 1u;
  return true;
}

/* Exact-index growth is amortized O(1) and touches only exact participants. */
static bool bounds_prepare_exact_index(ixs_bounds *b, size_t count,
                                       size_t **prepared,
                                       size_t *prepared_capacity) {
  size_t capacity = b->exact_index_cap;
  size_t *index;
  size_t i;

  if (capacity && count <= capacity - capacity / 4u) {
    *prepared = b->exact_index;
    *prepared_capacity = capacity;
    return true;
  }
  if (!capacity)
    capacity = BOUNDS_EXACT_INDEX_INIT_CAP;
  while (count > capacity - capacity / 4u) {
    if (capacity > SIZE_MAX / 2u)
      return false;
    capacity *= 2u;
  }
  if (capacity > SIZE_MAX / sizeof(*index))
    return false;
  index =
      ixs_arena_alloc(b->scratch, capacity * sizeof(*index), sizeof(void *));
  if (!index)
    return false;
  memset(index, 0, capacity * sizeof(*index));
  for (i = 0; i < b->nexact_vars; i++) {
    size_t slot = bounds_exact_index_slot(index, capacity, b->exact_vars,
                                          b->exact_vars[i].var_index);
    index[slot] = i + 1u;
  }
  *prepared = index;
  *prepared_capacity = capacity;
  return true;
}

static bool bounds_prepare_exact_vars(ixs_bounds *b, size_t count,
                                      ixs_exact_var **prepared,
                                      size_t *prepared_capacity) {
  ixs_exact_var *vars;
  size_t capacity = b->exact_var_cap;
  size_t old_bytes;
  size_t new_bytes;

  if (count <= capacity) {
    *prepared = b->exact_vars;
    *prepared_capacity = capacity;
    return true;
  }
  if (!capacity)
    capacity = 2u;
  while (capacity < count) {
    if (capacity > SIZE_MAX / 2u)
      return false;
    capacity *= 2u;
  }
  if (b->exact_var_cap > SIZE_MAX / sizeof(*vars) ||
      capacity > SIZE_MAX / sizeof(*vars))
    return false;
  old_bytes = b->exact_var_cap * sizeof(*vars);
  new_bytes = capacity * sizeof(*vars);
  vars = ixs_arena_grow(b->scratch, b->exact_vars, old_bytes, new_bytes,
                        sizeof(void *));
  if (!vars)
    return false;
  memset(vars + b->exact_var_cap, 0,
         (capacity - b->exact_var_cap) * sizeof(*vars));
  *prepared = vars;
  *prepared_capacity = capacity;
  return true;
}

static void bounds_exact_init_var(ixs_bounds *b, size_t var_index,
                                  size_t *exact_index) {
  size_t slot;
  size_t id = b->nexact_vars++;
  b->exact_vars[id].var_index = var_index;
  b->exact_vars[id].parent = id;
  b->exact_vars[id].size = 1u;
  b->exact_vars[id].offset = 0;
  slot = bounds_exact_index_slot(b->exact_index, b->exact_index_cap,
                                 b->exact_vars, var_index);
  b->exact_index[slot] = id + 1u;
  *exact_index = id;
}

static bool bounds_prepare_exact_pair(ixs_bounds *b, size_t lhs_var,
                                      size_t rhs_var, size_t *lhs_exact,
                                      size_t *rhs_exact) {
  ixs_exact_var *vars;
  size_t *index;
  size_t var_capacity;
  size_t index_capacity;
  size_t missing = 0;
  bool have_lhs = bounds_exact_lookup(b, lhs_var, lhs_exact);
  bool have_rhs = bounds_exact_lookup(b, rhs_var, rhs_exact);

  if (!have_lhs)
    missing++;
  if (!have_rhs)
    missing++;
  if (b->nexact_vars > SIZE_MAX - missing ||
      !bounds_prepare_exact_index(b, b->nexact_vars + missing, &index,
                                  &index_capacity) ||
      !bounds_prepare_exact_vars(b, b->nexact_vars + missing, &vars,
                                 &var_capacity))
    return false;

  b->exact_vars = vars;
  b->exact_var_cap = var_capacity;
  b->exact_index = index;
  b->exact_index_cap = index_capacity;
  if (!have_lhs)
    bounds_exact_init_var(b, lhs_var, lhs_exact);
  if (!have_rhs)
    bounds_exact_init_var(b, rhs_var, rhs_exact);
  return true;
}

/* Weighted parent links use value(node) - value(parent). Union by size and
 * path compression make representable exact queries amortized inverse-Ackermann
 * in the number of exact participants, independent of inequality fan-out. */
static bool bounds_exact_find(ixs_bounds *b, size_t id, size_t *root,
                              int64_t *offset) {
  size_t current = id;
  int64_t total = 0;

  while (b->exact_vars[current].parent != current) {
    if (!ixs_safe_add(total, b->exact_vars[current].offset, &total))
      return false;
    current = b->exact_vars[current].parent;
  }
  *root = current;
  *offset = total;

  current = id;
  while (b->exact_vars[current].parent != current) {
    size_t parent = b->exact_vars[current].parent;
    int64_t edge = b->exact_vars[current].offset;
    int64_t remaining;
    if (!ixs_safe_sub(total, edge, &remaining))
      break;
    b->exact_vars[current].parent = *root;
    b->exact_vars[current].offset = total;
    current = parent;
    total = remaining;
  }
  return true;
}

/* Record lhs - rhs == offset. Overflow leaves the exact forest unchanged;
 * the complete directed graph still owns and validates both inequalities. */
static bool bounds_union_exact(ixs_bounds *b, size_t lhs_var, size_t rhs_var,
                               int64_t offset) {
  size_t lhs_exact;
  size_t rhs_exact;
  size_t lhs_root;
  size_t rhs_root;
  int64_t lhs_offset;
  int64_t rhs_offset;
  int64_t root_offset;
  int64_t reverse_offset;

  if (!bounds_prepare_exact_pair(b, lhs_var, rhs_var, &lhs_exact, &rhs_exact)) {
    b->oom = true;
    return false;
  }
  if (!bounds_exact_find(b, lhs_exact, &lhs_root, &lhs_offset) ||
      !bounds_exact_find(b, rhs_exact, &rhs_root, &rhs_offset))
    return true;
  if (lhs_root == rhs_root) {
    int64_t existing;
    if (ixs_safe_sub(lhs_offset, rhs_offset, &existing) && existing != offset)
      bounds_mark_contradiction(b);
    return true;
  }
  if (!ixs_safe_sub(offset, lhs_offset, &root_offset) ||
      !ixs_safe_add(root_offset, rhs_offset, &root_offset))
    return true;

  if (b->exact_vars[lhs_root].size <= b->exact_vars[rhs_root].size) {
    b->exact_vars[lhs_root].parent = rhs_root;
    b->exact_vars[lhs_root].offset = root_offset;
    b->exact_vars[rhs_root].size += b->exact_vars[lhs_root].size;
  } else {
    if (!ixs_safe_neg(root_offset, &reverse_offset))
      return true;
    b->exact_vars[rhs_root].parent = lhs_root;
    b->exact_vars[rhs_root].offset = reverse_offset;
    b->exact_vars[lhs_root].size += b->exact_vars[rhs_root].size;
  }
  bounds_mark_semantic_changed(b);
  bounds_cache_clear(b);
  return true;
}

static bool bounds_exact_symbol_difference(ixs_bounds *b, ixs_node *lhs,
                                           ixs_node *rhs, int64_t *delta) {
  ixs_var_bound *lhs_var;
  ixs_var_bound *rhs_var;
  size_t lhs_exact;
  size_t rhs_exact;
  size_t lhs_root;
  size_t rhs_root;
  int64_t lhs_offset;
  int64_t rhs_offset;

  if (!b || !lhs || !rhs || !delta || b->oom || b->contradiction ||
      lhs->tag != IXS_SYM || rhs->tag != IXS_SYM)
    return false;
  if (lhs == rhs) {
    *delta = 0;
    return true;
  }
  lhs_var = find_var(b, lhs->u.name);
  rhs_var = find_var(b, rhs->u.name);
  if (!lhs_var || !rhs_var ||
      !bounds_exact_lookup(b, (size_t)(lhs_var - b->vars), &lhs_exact) ||
      !bounds_exact_lookup(b, (size_t)(rhs_var - b->vars), &rhs_exact) ||
      !bounds_exact_find(b, lhs_exact, &lhs_root, &lhs_offset) ||
      !bounds_exact_find(b, rhs_exact, &rhs_root, &rhs_offset) ||
      lhs_root != rhs_root)
    return false;
  return ixs_safe_sub(lhs_offset, rhs_offset, delta);
}

static bool bounds_difference_worklist_init(ixs_bounds *b,
                                            difference_worklist *work) {
  size_t count = b->ndifference_vars;
  memset(work, 0, sizeof(*work));
  work->mark = ixs_arena_save(b->scratch);
  work->capacity = count;
  if (count == 0)
    return true;
  if (b->difference_epoch == SIZE_MAX ||
      count > SIZE_MAX / sizeof(*work->queue)) {
    b->oom = true;
    return false;
  }
  work->epoch = ++b->difference_epoch;
  work->queue =
      ixs_arena_alloc(b->scratch, count * sizeof(*work->queue), sizeof(void *));
  if (!work->queue) {
    ixs_arena_restore(b->scratch, work->mark);
    b->oom = true;
    return false;
  }
  return true;
}

static void bounds_difference_worklist_destroy(ixs_bounds *b,
                                               difference_worklist *work) {
  ixs_arena_restore(b->scratch, work->mark);
}

static bool bounds_difference_var_active(const ixs_bounds *b,
                                         size_t var_index) {
  const ixs_difference_var *var;
  if (var_index >= b->nvars || var_index >= b->difference_var_cap)
    return false;
  var = &b->difference_vars[var_index];
  return var->incoming || var->outgoing;
}

static bool bounds_difference_enqueue(ixs_bounds *b, difference_worklist *work,
                                      size_t var_index) {
  ixs_difference_var *var;
  if (var_index >= b->nvars)
    return false;
  if (!bounds_difference_var_active(b, var_index))
    return true;
  var = &b->difference_vars[var_index];
  if (var->queue_epoch == work->epoch)
    return true;
  if (work->count >= work->capacity)
    return false;
  work->queue[work->tail] = var_index;
  work->tail = (work->tail + 1u) % work->capacity;
  work->count++;
  var->queue_epoch = work->epoch;
  return true;
}

static size_t bounds_difference_pop(ixs_bounds *b, difference_worklist *work) {
  size_t var_index = work->queue[work->head];
  work->head = (work->head + 1u) % work->capacity;
  work->count--;
  b->difference_vars[var_index].queue_epoch = 0;
  return var_index;
}

/* Existing potentials satisfy every published edge. Adding one edge can only
 * invalidate paths containing that edge. A strictly improving path of nvars
 * edges repeats a vertex, so its repeated segment is a negative cycle. The
 * work is proportional to the affected directed component and has no semantic
 * iteration cap. */
static bool bounds_validate_difference_edge(ixs_bounds *b, size_t lhs_var,
                                            size_t rhs_var, int64_t offset) {
  difference_worklist work;
  int64_t candidate;

  if (!ixs_safe_add(b->difference_vars[rhs_var].potential, offset,
                    &candidate)) {
    b->oom = true;
    return false;
  }
  if (b->difference_vars[lhs_var].potential <= candidate)
    return true;
  if (!bounds_difference_worklist_init(b, &work))
    return false;

  b->difference_vars[lhs_var].potential = candidate;
  b->difference_vars[lhs_var].hops = 1u;
  if (!bounds_difference_enqueue(b, &work, lhs_var)) {
    b->oom = true;
    bounds_difference_worklist_destroy(b, &work);
    return false;
  }

  while (work.count && !b->contradiction && !b->oom) {
    size_t source = bounds_difference_pop(b, &work);
    ixs_difference_constraint *edge = b->difference_vars[source].outgoing;
    while (edge) {
      size_t target = edge->lhs_var;
      if (!ixs_safe_add(b->difference_vars[source].potential, edge->offset,
                        &candidate)) {
        b->oom = true;
        break;
      }
      if (b->difference_vars[target].potential > candidate) {
        if (b->difference_vars[source].hops >= b->ndifference_vars - 1u) {
          bounds_mark_contradiction(b);
          break;
        }
        b->difference_vars[target].potential = candidate;
        b->difference_vars[target].hops = b->difference_vars[source].hops + 1u;
        if (!bounds_difference_enqueue(b, &work, target)) {
          b->oom = true;
          break;
        }
      }
      edge = edge->next_rhs;
    }
  }
  bounds_difference_worklist_destroy(b, &work);
  return !b->oom;
}

static bool bounds_refine_var_upper(ixs_bounds *b, ixs_var_bound *v,
                                    int64_t upper) {
  if (!v ||
      (!v->iv.hi_inf && ixs_rat_cmp(upper, 1, v->iv.hi_p, v->iv.hi_q) >= 0))
    return false;
  v->iv.hi_p = upper;
  v->iv.hi_q = 1;
  v->iv.hi_inf = false;
  bounds_mark_semantic_changed(b);
  bounds_cache_clear(b);
  refine_var_bit_consistency(b, v);
  return true;
}

static bool bounds_refine_var_lower(ixs_bounds *b, ixs_var_bound *v,
                                    int64_t lower) {
  if (!v ||
      (!v->iv.lo_inf && ixs_rat_cmp(lower, 1, v->iv.lo_p, v->iv.lo_q) <= 0))
    return false;
  v->iv.lo_p = lower;
  v->iv.lo_q = 1;
  v->iv.lo_inf = false;
  bounds_mark_semantic_changed(b);
  bounds_cache_clear(b);
  refine_var_bit_consistency(b, v);
  return true;
}

static ixs_interval bounds_get_difference_symbol(ixs_bounds *b,
                                                 ixs_var_bound *var,
                                                 ixs_node *symbol) {
  ixs_interval iv = var->iv;
  if (b->nexprs) {
    ixs_node *canon;
    iv = iv_intersect(iv, bounds_get_expr_overrides(b, symbol));
    canon = bounds_canonical_expr(b, symbol);
    if (canon && canon != symbol)
      iv = iv_intersect(iv, bounds_get_expr_overrides(b, canon));
  }
  if (var->modulus > 0)
    iv = interval_intersect_congruence(iv, var->modulus, var->remainder);
  return iv;
}

static bool bounds_propagate_difference_upper(ixs_bounds *b,
                                              difference_worklist *work,
                                              size_t var_index) {
  ixs_difference_constraint *edge = b->difference_vars[var_index].outgoing;
  ixs_var_bound *var = &b->vars[var_index];
  ixs_interval iv;
  int64_t endpoint;
  int64_t derived;
  if (!edge)
    return true;
  iv = bounds_get_difference_symbol(b, var, edge->rhs);
  if (!iv.valid || iv.hi_inf)
    return !b->oom;
  endpoint = ixs_rat_floor(iv.hi_p, iv.hi_q);
  while (edge && !b->contradiction) {
    if (ixs_safe_add(endpoint, edge->offset, &derived) &&
        bounds_refine_var_upper(b, &b->vars[edge->lhs_var], derived) &&
        !bounds_difference_enqueue(b, work, edge->lhs_var)) {
      b->oom = true;
      return false;
    }
    edge = edge->next_rhs;
  }
  return !b->oom;
}

static bool bounds_propagate_difference_lower(ixs_bounds *b,
                                              difference_worklist *work,
                                              size_t var_index) {
  ixs_difference_constraint *edge = b->difference_vars[var_index].incoming;
  ixs_var_bound *var = &b->vars[var_index];
  ixs_interval iv;
  int64_t endpoint;
  int64_t derived;
  if (!edge)
    return true;
  iv = bounds_get_difference_symbol(b, var, edge->lhs);
  if (!iv.valid || iv.lo_inf)
    return !b->oom;
  endpoint = ixs_rat_ceil(iv.lo_p, iv.lo_q);
  while (edge && !b->contradiction) {
    if (ixs_safe_sub(endpoint, edge->offset, &derived) &&
        bounds_refine_var_lower(b, &b->vars[edge->rhs_var], derived) &&
        !bounds_difference_enqueue(b, work, edge->rhs_var)) {
      b->oom = true;
      return false;
    }
    edge = edge->next_lhs;
  }
  return !b->oom;
}

/* Existing edges are already closed. An insertion needs an endpoint worklist
 * only when the new edge itself can tighten one of its endpoints. */
static bool
bounds_difference_edge_can_refine(ixs_bounds *b,
                                  const ixs_difference_constraint *edge) {
  ixs_interval iv;
  int64_t endpoint;
  int64_t derived;

  iv = bounds_get_difference_symbol(b, &b->vars[edge->rhs_var], edge->rhs);
  if (iv.valid && !iv.hi_inf) {
    endpoint = ixs_rat_floor(iv.hi_p, iv.hi_q);
    if (ixs_safe_add(endpoint, edge->offset, &derived) &&
        (b->vars[edge->lhs_var].iv.hi_inf ||
         ixs_rat_cmp(derived, 1, b->vars[edge->lhs_var].iv.hi_p,
                     b->vars[edge->lhs_var].iv.hi_q) < 0))
      return true;
  }

  iv = bounds_get_difference_symbol(b, &b->vars[edge->lhs_var], edge->lhs);
  if (!iv.valid || iv.lo_inf)
    return false;
  endpoint = ixs_rat_ceil(iv.lo_p, iv.lo_q);
  return ixs_safe_sub(endpoint, edge->offset, &derived) &&
         (b->vars[edge->rhs_var].iv.lo_inf ||
          ixs_rat_cmp(derived, 1, b->vars[edge->rhs_var].iv.lo_p,
                      b->vars[edge->rhs_var].iv.lo_q) > 0);
}

static bool bounds_propagate_difference_indices(ixs_bounds *b, size_t first,
                                                size_t second,
                                                bool have_second) {
  difference_worklist work;
  bool first_active;
  bool second_active;

  if (!b || b->oom || b->contradiction || b->ndifferences == 0)
    return true;
  first_active = bounds_difference_var_active(b, first);
  second_active =
      have_second && second != first && bounds_difference_var_active(b, second);
  if (!first_active && !second_active)
    return true;
  if (!bounds_difference_worklist_init(b, &work))
    return false;
  if ((first_active && !bounds_difference_enqueue(b, &work, first)) ||
      (second_active && !bounds_difference_enqueue(b, &work, second))) {
    b->oom = true;
    bounds_difference_worklist_destroy(b, &work);
    return false;
  }

  /* Each strict interval refinement schedules only its adjacent variable.
   * With a feasible graph, closure is finite and costs the successful
   * relaxations plus the incident edges they inspect. */
  while (work.count && !b->oom && !b->contradiction) {
    size_t var_index = bounds_difference_pop(b, &work);
    if (!bounds_propagate_difference_upper(b, &work, var_index) ||
        b->contradiction ||
        !bounds_propagate_difference_lower(b, &work, var_index))
      break;
  }
  bounds_difference_worklist_destroy(b, &work);
  return !b->oom;
}

static void bounds_propagate_difference_bounds(ixs_bounds *b, const char *first,
                                               const char *second) {
  ixs_var_bound *first_var;
  ixs_var_bound *second_var = NULL;
  size_t first_index;
  size_t second_index = 0;
  if (!b || b->oom || !first || b->ndifferences == 0)
    return;
  first_var = find_var(b, first);
  if (!first_var)
    return;
  first_index = (size_t)(first_var - b->vars);
  if (second && second != first) {
    second_var = find_var(b, second);
    if (second_var)
      second_index = (size_t)(second_var - b->vars);
  }
  (void)bounds_propagate_difference_indices(b, first_index, second_index,
                                            second_var != NULL);
}

static bool bounds_register_exact_reverse(
    ixs_bounds *b, ixs_difference_constraint *const *index,
    size_t index_capacity, ixs_node *lhs, ixs_node *rhs, size_t lhs_var,
    size_t rhs_var, int64_t offset) {
  int64_t reverse_offset;
  size_t slot;
  if (!ixs_safe_neg(offset, &reverse_offset))
    return true;
  slot = bounds_difference_index_slot(index, index_capacity, rhs, lhs,
                                      reverse_offset);
  return !index[slot] || bounds_union_exact(b, lhs_var, rhs_var, offset);
}

static void bounds_add_difference_constraint(ixs_bounds *b, ixs_node *lhs,
                                             ixs_node *rhs, int64_t offset) {
  ixs_difference_constraint **index;
  ixs_difference_constraint *edge;
  size_t lhs_var;
  size_t rhs_var;
  size_t index_capacity;
  size_t new_vertices;
  size_t slot;

  if (!b || !lhs || !rhs || lhs == rhs || lhs->tag != IXS_SYM ||
      rhs->tag != IXS_SYM || b->oom || b->contradiction)
    return;
  if (b->difference_index_cap) {
    slot = bounds_difference_index_slot(
        b->difference_index, b->difference_index_cap, lhs, rhs, offset);
    if (b->difference_index[slot])
      return;
  }
  if (!get_or_create_var_index(b, lhs->u.name, &lhs_var) ||
      !get_or_create_var_index(b, rhs->u.name, &rhs_var) ||
      b->ndifferences == SIZE_MAX ||
      !bounds_prepare_difference_vars(b, b->nvars) ||
      !bounds_prepare_difference_index(b, b->ndifferences + 1u, &index,
                                       &index_capacity)) {
    b->oom = true;
    return;
  }
  new_vertices = (!b->difference_vars[lhs_var].incoming &&
                  !b->difference_vars[lhs_var].outgoing) +
                 (!b->difference_vars[rhs_var].incoming &&
                  !b->difference_vars[rhs_var].outgoing);
  if (b->ndifference_vars > SIZE_MAX - new_vertices) {
    b->oom = true;
    return;
  }
  edge = ixs_arena_alloc(b->scratch, sizeof(*edge), sizeof(void *));
  if (!edge) {
    b->oom = true;
    return;
  }
  edge->lhs = lhs;
  edge->rhs = rhs;
  edge->next_lhs = b->difference_vars[lhs_var].incoming;
  edge->next_rhs = b->difference_vars[rhs_var].outgoing;
  edge->lhs_var = lhs_var;
  edge->rhs_var = rhs_var;
  edge->offset = offset;
  b->difference_vars[lhs_var].incoming = edge;
  b->difference_vars[rhs_var].outgoing = edge;
  b->difference_index = index;
  b->difference_index_cap = index_capacity;
  slot = bounds_difference_index_slot(index, index_capacity, lhs, rhs, offset);
  index[slot] = edge;
  b->ndifferences++;
  b->ndifference_vars += new_vertices;
  bounds_mark_semantic_changed(b);
  bounds_cache_clear(b);
  if (!bounds_validate_difference_edge(b, lhs_var, rhs_var, offset) ||
      b->contradiction)
    return;
  if (!bounds_register_exact_reverse(b, index, index_capacity, lhs, rhs,
                                     lhs_var, rhs_var, offset) ||
      b->contradiction)
    return;
  if (bounds_difference_edge_can_refine(b, edge))
    (void)bounds_propagate_difference_indices(b, lhs_var, rhs_var, true);
}

static bool bounds_extract_unit_difference(ixs_node *expr, ixs_node **lhs,
                                           ixs_node **rhs, int64_t *constant) {
  uint32_t i;
  int64_t p;
  int64_t q;
  if (!expr || !lhs || !rhs || !constant || expr->tag != IXS_ADD ||
      expr->u.add.nterms != 2u)
    return false;
  ixs_node_get_rat(expr->u.add.coeff, &p, &q);
  if (q != 1)
    return false;
  *constant = p;
  *lhs = NULL;
  *rhs = NULL;
  for (i = 0; i < 2u; i++) {
    ixs_node *term = expr->u.add.terms[i].term;
    ixs_node_get_rat(expr->u.add.terms[i].coeff, &p, &q);
    if (term->tag != IXS_SYM || q != 1 || (p != 1 && p != -1))
      return false;
    if (p == 1) {
      if (*lhs)
        return false;
      *lhs = term;
    } else {
      if (*rhs)
        return false;
      *rhs = term;
    }
  }
  return *lhs && *rhs && *lhs != *rhs;
}

static bool bounds_exact_unit_difference_value(ixs_bounds *b, ixs_node *expr,
                                               int64_t *value) {
  ixs_node *lhs;
  ixs_node *rhs;
  int64_t constant;
  int64_t difference;
  return bounds_extract_unit_difference(expr, &lhs, &rhs, &constant) &&
         bounds_exact_symbol_difference(b, lhs, rhs, &difference) &&
         ixs_safe_add(constant, difference, value);
}

static void bounds_add_difference_range(ixs_bounds *b, ixs_node *expr,
                                        ixs_interval iv) {
  ixs_node *lhs;
  ixs_node *rhs;
  int64_t constant;
  int64_t endpoint;
  int64_t offset;
  if (!iv.valid || !bounds_extract_unit_difference(expr, &lhs, &rhs, &constant))
    return;
  if (!iv.hi_inf) {
    endpoint = ixs_rat_floor(iv.hi_p, iv.hi_q);
    if (ixs_safe_sub(endpoint, constant, &offset))
      bounds_add_difference_constraint(b, lhs, rhs, offset);
  }
  if (!b->oom && !b->contradiction && !iv.lo_inf) {
    endpoint = ixs_rat_ceil(iv.lo_p, iv.lo_q);
    if (ixs_safe_sub(constant, endpoint, &offset))
      bounds_add_difference_constraint(b, rhs, lhs, offset);
  }
}

static void bounds_add_proportional_range(ixs_bounds *b, ixs_node *expr,
                                          ixs_interval iv) {
  ixs_node *primitive, *canonical;
  ixs_interval primitive_iv;
  int64_t scale_p, scale_q, offset_p, offset_q;
  if (!bounds_get_proportional_primitive(b, expr, &primitive, &scale_p,
                                         &scale_q, &offset_p, &offset_q) ||
      (primitive == expr && scale_p == 1 && scale_q == 1 && offset_p == 0))
    return;
  primitive_iv = bounds_invert_affine(iv, scale_p, scale_q, offset_p, offset_q);
  if (!primitive_iv.valid)
    return;
  bounds_add_expr_raw(b, primitive, primitive_iv);
  if (b->oom)
    return;
  canonical = bounds_canonical_expr(b, primitive);
  if (canonical && canonical != primitive)
    bounds_add_expr_raw(b, canonical, primitive_iv);
}

IXS_STATIC void ixs_bounds_add_expr(ixs_bounds *b, ixs_node *expr,
                                    ixs_interval iv) {
  ixs_node *canon = NULL;
  bounds_add_expr_raw(b, expr, iv);
  if (b->oom)
    return;
  bounds_add_proportional_range(b, expr, iv);
  if (b->oom)
    return;
  canon = bounds_canonical_expr(b, expr);
  if (canon && canon != expr) {
    bounds_add_expr_raw(b, canon, iv);
    if (!b->oom)
      bounds_add_proportional_range(b, canon, iv);
  }
  if (b->oom || b->contradiction)
    return;
  bounds_add_difference_range(b, expr, iv);
  if (canon && canon != expr)
    bounds_add_difference_range(b, canon, iv);
  if (b->oom || b->contradiction)
    return;
  if (expr->tag == IXS_SYM)
    bounds_propagate_difference_bounds(b, expr->u.name, NULL);
  if (canon && canon != expr && canon->tag == IXS_SYM)
    bounds_propagate_difference_bounds(b, canon->u.name, NULL);
}

static bool bounds_is_known_nonzero(const ixs_bounds *b, const ixs_node *expr) {
  size_t i;
  if (!b || !expr)
    return false;
  for (i = 0; i < b->nnonzero; i++) {
    if (b->nonzero[i] == expr)
      return true;
  }
  return false;
}

static void bounds_add_nonzero(ixs_bounds *b, ixs_node *expr) {
  ixs_node **grown;
  size_t new_cap;
  if (!b || !expr || b->oom || bounds_is_known_nonzero(b, expr))
    return;
  bounds_empty_cache_invalidate(b);
  if (b->nnonzero < b->nonzero_cap) {
    b->nonzero[b->nnonzero++] = expr;
    bounds_mark_semantic_changed(b);
    return;
  }
  new_cap = b->nonzero_cap ? b->nonzero_cap * 2u : 4u;
  if (new_cap < b->nonzero_cap || new_cap > SIZE_MAX / sizeof(*b->nonzero)) {
    b->oom = true;
    return;
  }
  grown = ixs_arena_alloc(b->scratch, new_cap * sizeof(*grown), sizeof(void *));
  if (!grown) {
    b->oom = true;
    return;
  }
  if (b->nnonzero)
    memcpy(grown, b->nonzero, b->nnonzero * sizeof(*grown));
  b->nonzero = grown;
  b->nonzero_cap = new_cap;
  b->nonzero[b->nnonzero++] = expr;
  bounds_mark_semantic_changed(b);
}

/*
 * Extract interval bounds and modular congruence from a comparison.
 * Patterns: sym >= 0, sym < N, Mod(sym, M) == R, etc.
 */
static bool bounds_add_sym_cmp_const(ixs_bounds *b, ixs_node *lhs,
                                     ixs_node *rhs, ixs_cmp_op op) {
  ixs_node *sym;
  ixs_node *constant;
  ixs_cmp_op effective_op;
  ixs_interval sym_iv;
  int64_t p;
  int64_t q;

  if (lhs->tag == IXS_SYM && ixs_node_is_const(rhs)) {
    sym = lhs;
    constant = rhs;
    effective_op = op;
  } else if (rhs->tag == IXS_SYM && ixs_node_is_const(lhs)) {
    sym = rhs;
    constant = lhs;
    effective_op = flip_cmp(op);
  } else {
    return false;
  }

  ixs_node_get_rat(constant, &p, &q);
  apply_sym_cmp_const(b, sym->u.name, effective_op, p, q);
  sym_iv = interval_from_sym_cmp_const(effective_op, p, q);
  if (sym_iv.valid)
    ixs_bounds_add_expr(b, sym, sym_iv);
  return true;
}

static bool bounds_add_affine_zero_cmp(ixs_bounds *b, ixs_node *lhs,
                                       ixs_node *rhs, ixs_cmp_op op) {
  ixs_node *sym;
  ixs_cmp_op effective_op;
  ixs_interval sym_iv;
  int64_t tp;
  int64_t tq;
  int64_t kp;
  int64_t kq;
  int64_t np;
  int64_t nq;
  int64_t raw_p;
  int64_t raw_q;
  int64_t p;
  int64_t q;

  if (!ixs_node_is_zero(rhs) || lhs->tag != IXS_ADD || lhs->u.add.nterms != 1 ||
      lhs->u.add.terms[0].term->tag != IXS_SYM)
    return false;

  sym = lhs->u.add.terms[0].term;
  ixs_node_get_rat(lhs->u.add.terms[0].coeff, &tp, &tq);
  ixs_node_get_rat(lhs->u.add.coeff, &kp, &kq);

  /* tp/tq * sym + kp/kq OP 0, so divide -kp/kq by tp/tq. */
  if (tp == 0 || !ixs_rat_neg(kp, kq, &np, &nq) ||
      !ixs_rat_mul(np, nq, tq, tp, &raw_p, &raw_q) ||
      !ixs_rat_normalize(raw_p, raw_q, &p, &q))
    return true;

  effective_op = (ixs_rat_cmp(tp, tq, 0, 1) < 0) ? flip_cmp(op) : op;
  apply_sym_cmp_const(b, sym->u.name, effective_op, p, q);
  sym_iv = interval_from_sym_cmp_const(effective_op, p, q);
  if (sym_iv.valid)
    ixs_bounds_add_expr(b, sym, sym_iv);
  return true;
}

static void bounds_add_assumption_impl(ixs_bounds *b, ixs_node *a) {
  ixs_node *lhs;
  ixs_node *rhs;
  ixs_cmp_op op;

  if (a->tag != IXS_CMP)
    return;
  bounds_cache_clear(b);

  extract_modrem(b, a);
  extract_bitfacts(b, a);

  lhs = a->u.binary.lhs;
  rhs = a->u.binary.rhs;
  op = a->u.binary.cmp_op;

  if (op == IXS_CMP_NE) {
    if (ixs_node_is_zero(rhs))
      bounds_add_nonzero(b, lhs);
    else if (ixs_node_is_zero(lhs))
      bounds_add_nonzero(b, rhs);
  }

  if (bounds_add_sym_cmp_const(b, lhs, rhs, op))
    return;

  if (bounds_add_affine_zero_cmp(b, lhs, rhs, op))
    return;

  /* Fallback: expr op 0 for non-symbol lhs. Store as expression bound. */
  if (ixs_node_is_zero(rhs)) {
    add_expr_integer_zero_cmp(b, lhs, op);
  } else if (ixs_bounds_check_defined(b, lhs) == IXS_CHECK_TRUE &&
             ixs_bounds_check_defined(b, rhs) == IXS_CHECK_TRUE) {
    ixs_node *difference = simp_sub(b->ctx, lhs, rhs);
    if (!difference) {
      b->oom = true;
      return;
    }
    if (!ixs_node_is_sentinel(difference))
      add_expr_integer_zero_cmp(b, difference, op);
  }
}

IXS_STATIC bool ixs_bounds_add_assumption(ixs_bounds *b, ixs_node *a) {
  if (!b || !a || b->oom)
    return false;
  bounds_add_assumption_impl(b, a);
  return !b->oom;
}

/* GCD of a positive modulus and a conservative dividend step.  Computing the
 * GCD directly keeps the result representable when a coefficient is
 * INT64_MIN, whose magnitude is one past INT64_MAX. */
static int64_t mod_dividend_gcd(ixs_node *expr, int64_t modulus) {
  int64_t p, q, g;
  uint32_t i;
  switch (expr->tag) {
  case IXS_MUL:
    ixs_node_get_rat(expr->u.mul.coeff, &p, &q);
    return (q == 1) ? ixs_gcd(p, modulus) : 1;
  case IXS_ADD:
    ixs_node_get_rat(expr->u.add.coeff, &p, &q);
    if (q != 1)
      return 1;
    g = ixs_gcd(p, modulus);
    for (i = 0; i < expr->u.add.nterms; i++) {
      ixs_node_get_rat(expr->u.add.terms[i].coeff, &p, &q);
      if (q != 1)
        return 1;
      g = ixs_gcd(g, p);
    }
    return g;
  default:
    return 1;
  }
}

#define BITFACTS_DEPTH_LIMIT 64u

static bool bounds_get_bitfacts_depth(ixs_bounds *b, ixs_node *expr,
                                      ixs_bitfacts *out, unsigned depth);

static void bitfacts_apply_exact(ixs_bitfacts *bits, int64_t val) {
  uint64_t u = (uint64_t)val;
  bits->known_zero |= ~u;
  bits->known_one |= u;
  if (val == 0)
    bits->pow2 = IXS_POW2_OR_ZERO;
  else if (int64_is_positive_pow2(val))
    bits->pow2 = IXS_POW2_POSITIVE;
}

static void bitfacts_apply_interval(ixs_bitfacts *bits,
                                    const ixs_interval *iv) {
  int64_t exact;
  if (interval_exact_int(iv, &exact)) {
    bitfacts_apply_exact(bits, exact);
    return;
  }
  if (!iv->valid || iv->lo_inf || iv->hi_inf || iv->hi_q != 1 || iv->hi_p < 0 ||
      !interval_lower_at_least(iv, 0, 1))
    return;
  bits->known_zero |= ~value_span_mask((uint64_t)iv->hi_p);
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
  if (!int64_modulus_is_pow2(modulus))
    return;
  mask = (uint64_t)modulus - 1u;
  rem = (uint64_t)remainder & mask;
  bits->known_zero |= (~rem) & mask;
  bits->known_one |= rem & mask;
}

static bool bounds_get_symbol_bitfacts(ixs_bounds *b, const char *name,
                                       ixs_bitfacts *out) {
  int64_t exact;
  ixs_var_bound *v = find_var(b, name);
  if (v) {
    out->known_zero |= v->bits.known_zero;
    out->known_one |= v->bits.known_one;
    if (v->bits.pow2 == IXS_POW2_POSITIVE ||
        (v->bits.pow2 == IXS_POW2_OR_ZERO && out->pow2 == IXS_POW2_UNKNOWN))
      out->pow2 = v->bits.pow2;
    bitfacts_apply_modrem(out, v->modulus, v->remainder);
    if (interval_exact_int(&v->iv, &exact))
      bitfacts_apply_exact(out, exact);
    if (out->pow2 == IXS_POW2_OR_ZERO && interval_lower_at_least(&v->iv, 1, 1))
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

static void bitfacts_apply_xor(ixs_bitfacts *out, const ixs_bitfacts *a,
                               const ixs_bitfacts *b) {
  out->known_one =
      (a->known_one & b->known_zero) | (a->known_zero & b->known_one);
  out->known_zero =
      (a->known_zero & b->known_zero) | (a->known_one & b->known_one);
  out->pow2 = IXS_POW2_UNKNOWN;
}

static bool bitfacts_scale_nonnegative_pow2(ixs_bounds *b, ixs_node *term,
                                            int64_t coeff, ixs_bitfacts *out,
                                            unsigned depth) {
  ixs_bitfacts base;
  ixs_interval iv;
  uint64_t scale;
  unsigned shift;

  if (!int64_is_positive_pow2(coeff) || !ixs_node_is_integer_valued(term))
    return false;

  iv = ixs_bounds_get(b, term);
  scale = (uint64_t)coeff;
  if (!interval_lower_at_least(&iv, 0, 1) || iv.hi_inf || iv.hi_q != 1 ||
      iv.hi_p < 0 || (uint64_t)iv.hi_p > (uint64_t)INT64_MAX / scale ||
      !bounds_get_bitfacts_depth(b, term, &base, depth))
    return false;

  shift = bit_ctz64(scale);
  bitfacts_unknown(out);
  out->known_zero = (base.known_zero << shift) | low_mask(shift);
  out->known_one = base.known_one << shift;
  return true;
}

/* One bounded pass over normalized addends. Pairwise-disjoint possible-one
 * masks prove that integer addition cannot carry between addends. */
static void bitfacts_apply_carry_free_add(ixs_bounds *b, ixs_node *expr,
                                          ixs_bitfacts *out, unsigned depth) {
  ixs_bitfacts addend;
  uint64_t known_one, possible;
  int64_t cp, cq;
  uint32_t i;

  ixs_node_get_rat(expr->u.add.coeff, &cp, &cq);
  if (cq != 1 || cp < 0)
    return;

  bitfacts_unknown(&addend);
  bitfacts_apply_exact(&addend, cp);
  possible = ~addend.known_zero;
  known_one = addend.known_one;

  for (i = 0; i < expr->u.add.nterms; i++) {
    uint64_t term_possible;
    int64_t tp, tq;

    ixs_node_get_rat(expr->u.add.terms[i].coeff, &tp, &tq);
    if (tq != 1 || !bitfacts_scale_nonnegative_pow2(
                       b, expr->u.add.terms[i].term, tp, &addend, depth))
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

static bool bitfacts_apply_add(ixs_bounds *b, ixs_node *expr, ixs_bitfacts *out,
                               unsigned depth) {
  unsigned nbits;
  int64_t cp, cq;

  ixs_node_get_rat(expr->u.add.coeff, &cp, &cq);
  if (cq != 1)
    return true;

  bitfacts_apply_carry_free_add(b, expr, out, depth - 1u);

  for (nbits = 1; nbits <= 64u; nbits++) {
    uint64_t mask = low_mask(nbits);
    uint64_t sum = (uint64_t)cp & mask;
    uint32_t i;
    bool known = true;

    for (i = 0; i < expr->u.add.nterms; i++) {
      ixs_bitfacts term_bits;
      uint64_t term_value;
      int64_t tp, tq;

      ixs_node_get_rat(expr->u.add.terms[i].coeff, &tp, &tq);
      if (tq != 1 ||
          !bounds_get_bitfacts_depth(b, expr->u.add.terms[i].term, &term_bits,
                                     depth - 1) ||
          !bitfacts_low_value(&term_bits, nbits, &term_value)) {
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
  return true;
}

static bool bitfacts_apply_mul(ixs_bounds *b, ixs_node *expr, ixs_bitfacts *out,
                               unsigned depth) {
  ixs_bitfacts base_bits;
  uint64_t coeff;
  unsigned shift, i;

  if (expr->u.mul.coeff->tag != IXS_INT || expr->u.mul.coeff->u.ival <= 0 ||
      expr->u.mul.nfactors != 1 || expr->u.mul.factors[0].exp != 1 ||
      !ixs_node_is_integer_valued(expr))
    return true;

  coeff = (uint64_t)expr->u.mul.coeff->u.ival;
  if (!uint64_is_pow2(coeff) ||
      !bounds_get_bitfacts_depth(b, expr->u.mul.factors[0].base, &base_bits,
                                 depth - 1))
    return true;

  shift = bit_ctz64(coeff);
  out->known_zero |= low_mask(shift);
  for (i = shift; i < 64u; i++) {
    uint64_t src = ((uint64_t)1) << (i - shift);
    uint64_t dst = ((uint64_t)1) << i;
    if (base_bits.known_zero & src)
      out->known_zero |= dst;
    if (base_bits.known_one & src)
      out->known_one |= dst;
  }
  return true;
}

static bool extract_pow2_dividend(ixs_node *expr, ixs_node **dividend,
                                  uint64_t *denom) {
  int64_t cp, cq;
  if (!expr || expr->tag != IXS_MUL || expr->u.mul.nfactors != 1 ||
      expr->u.mul.factors[0].exp != 1)
    return false;
  ixs_node_get_rat(expr->u.mul.coeff, &cp, &cq);
  if (cp != 1 || cq <= 0 || !int64_modulus_is_pow2(cq))
    return false;
  *dividend = expr->u.mul.factors[0].base;
  *denom = (uint64_t)cq;
  return true;
}

static bool bitfacts_apply_floor_div(ixs_bounds *b, ixs_node *expr,
                                     ixs_bitfacts *out, unsigned depth) {
  ixs_node *dividend;
  ixs_interval iv;
  ixs_bitfacts bits;
  uint64_t denom;
  unsigned shift, i;

  if (!extract_pow2_dividend(expr->u.unary.arg, &dividend, &denom))
    return true;

  iv = ixs_bounds_get(b, dividend);
  if (!interval_lower_at_least(&iv, 0, 1) ||
      !bounds_get_bitfacts_depth(b, dividend, &bits, depth - 1))
    return true;

  shift = bit_ctz64(denom);
  for (i = 0; i + shift < 64u; i++) {
    uint64_t src = ((uint64_t)1) << (i + shift);
    uint64_t dst = ((uint64_t)1) << i;
    if (bits.known_zero & src)
      out->known_zero |= dst;
    if (bits.known_one & src)
      out->known_one |= dst;
  }
  return true;
}

static bool bitfacts_apply_mod(ixs_bounds *b, ixs_node *expr, ixs_bitfacts *out,
                               unsigned depth) {
  ixs_bitfacts lhs;
  uint64_t mask;
  int64_t modulus;

  if (expr->u.binary.rhs->tag != IXS_INT ||
      !int64_modulus_is_pow2(expr->u.binary.rhs->u.ival) ||
      !ixs_node_is_integer_valued(expr->u.binary.lhs))
    return true;

  modulus = expr->u.binary.rhs->u.ival;
  mask = (uint64_t)modulus - 1u;
  out->known_zero |= ~mask;
  if (bounds_get_bitfacts_depth(b, expr->u.binary.lhs, &lhs, depth - 1)) {
    out->known_zero |= lhs.known_zero & mask;
    out->known_one |= lhs.known_one & mask;
  }
  return true;
}

static inline bool bitfacts_apply_assoc(ixs_bounds *b, ixs_node *expr,
                                        ixs_bitfacts *out, unsigned depth) {
  ixs_bitfacts result, arg, next;
  uint32_t i;
  if (expr->u.assoc.nargs == 0 || !expr->u.assoc.args)
    return false;
  if (!bounds_get_bitfacts_depth(b, expr->u.assoc.args[0], &result, depth - 1))
    return false;
  for (i = 1; i < expr->u.assoc.nargs; i++) {
    if (!bounds_get_bitfacts_depth(b, expr->u.assoc.args[i], &arg, depth - 1))
      return false;
    if (expr->tag == IXS_AND)
      bitfacts_apply_and(&next, &result, &arg);
    else if (expr->tag == IXS_OR)
      bitfacts_apply_or(&next, &result, &arg);
    else
      bitfacts_apply_xor(&next, &result, &arg);
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

static bool bounds_get_bitfacts_depth(ixs_bounds *b, ixs_node *expr,
                                      ixs_bitfacts *out, unsigned depth) {
  ixs_interval iv;

  bitfacts_unknown(out);
  if (!expr || depth == 0)
    return false;

  iv = ixs_bounds_get(b, expr);
  bitfacts_apply_interval(out, &iv);

  switch (expr->tag) {
  case IXS_INT:
    bitfacts_apply_exact(out, expr->u.ival);
    return true;
  case IXS_RAT:
    if (expr->u.rat.q != 1)
      return false;
    bitfacts_apply_exact(out, expr->u.rat.p);
    return true;
  case IXS_SYM: {
    return bounds_get_symbol_bitfacts(b, expr->u.name, out);
  }
  case IXS_CMP:
  case IXS_NOT:
    return bitfacts_apply_bool_value(out);
  case IXS_AND:
  case IXS_OR:
  case IXS_XOR:
    return bitfacts_apply_assoc(b, expr, out, depth);
  case IXS_ADD:
    return bitfacts_apply_add(b, expr, out, depth);
  case IXS_MUL:
    return bitfacts_apply_mul(b, expr, out, depth);
  case IXS_FLOOR:
    return bitfacts_apply_floor_div(b, expr, out, depth);
  case IXS_MOD:
    return bitfacts_apply_mod(b, expr, out, depth);
  case IXS_CEIL:
  case IXS_PIECEWISE:
  case IXS_MAX:
  case IXS_MIN:
    return ixs_node_is_integer_valued(expr);
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    return false;
  }
  return false;
}

IXS_STATIC bool ixs_bounds_get_bitfacts(ixs_bounds *b, ixs_node *expr,
                                        ixs_bitfacts *out) {
  if (!b || !out)
    return false;
  return bounds_get_bitfacts_depth(b, expr, out, BITFACTS_DEPTH_LIMIT);
}

IXS_STATIC bool ixs_bounds_is_pow2_positive(ixs_bounds *b, ixs_node *expr) {
  ixs_bitfacts bits;
  if (!ixs_bounds_get_bitfacts(b, expr, &bits))
    return false;
  return bits.pow2 == IXS_POW2_POSITIVE;
}

IXS_STATIC bool ixs_bounds_is_pow2_or_zero(ixs_bounds *b, ixs_node *expr) {
  ixs_bitfacts bits;
  if (!ixs_bounds_get_bitfacts(b, expr, &bits))
    return false;
  return bits.pow2 == IXS_POW2_OR_ZERO || ixs_bounds_is_pow2_positive(b, expr);
}

static inline bool bounds_symbol_divisible(ixs_bounds *b, const char *name,
                                           int64_t m) {
  int64_t sym_mod, sym_rem;
  if (!ixs_bounds_get_modrem(b, name, &sym_mod, &sym_rem))
    return false;
  return sym_mod % m == 0 && sym_rem % m == 0;
}

static inline bool bounds_mul_divisible(ixs_bounds *b, ixs_node *expr,
                                        int64_t m) {
  int64_t c = expr->u.mul.coeff->u.ival;
  int64_t remain;
  uint32_t i;
  if (c == 0)
    return true;
  for (i = 0; i < expr->u.mul.nfactors; i++) {
    if (expr->u.mul.factors[i].exp < 0 ||
        !ixs_bounds_is_integer_with_divinfo(b, expr->u.mul.factors[i].base))
      return false;
  }
  remain = m / ixs_gcd(c, m);
  if (remain == 1)
    return true;
  for (i = 0; i < expr->u.mul.nfactors; i++) {
    if (expr->u.mul.factors[i].exp >= 1 &&
        ixs_bounds_is_known_divisible(b, expr->u.mul.factors[i].base, remain))
      return true;
  }
  return false;
}

static inline bool bounds_add_divisible(ixs_bounds *b, ixs_node *expr,
                                        int64_t m) {
  int64_t cp, cq;
  uint32_t i;
  ixs_node_get_rat(expr->u.add.coeff, &cp, &cq);
  if (cq != 1 || cp % m != 0)
    return false;
  for (i = 0; i < expr->u.add.nterms; i++) {
    int64_t tp, tq, g, remain;
    ixs_node_get_rat(expr->u.add.terms[i].coeff, &tp, &tq);
    if (tq != 1)
      return false;
    g = ixs_gcd(tp, m);
    remain = m / g;
    if (!ixs_bounds_is_known_divisible(b, expr->u.add.terms[i].term, remain))
      return false;
  }
  return true;
}

IXS_STATIC bool ixs_bounds_is_known_divisible(ixs_bounds *b, ixs_node *expr,
                                              int64_t m) {
  ixs_bitfacts bits;
  uint64_t low_mask;
  uint32_t i;
  if (!b || !expr || m <= 0)
    return false;

  if (int64_modulus_is_pow2(m)) {
    low_mask = (uint64_t)m - 1u;
    if (ixs_bounds_get_bitfacts(b, expr, &bits) &&
        (bits.known_zero & low_mask) == low_mask)
      return true;
  }

  if (expr->tag == IXS_INT)
    return expr->u.ival % m == 0;

  if (expr->tag == IXS_SYM) {
    return bounds_symbol_divisible(b, expr->u.name, m);
  }

  if (expr->tag == IXS_MUL && expr->u.mul.coeff->tag == IXS_INT) {
    return bounds_mul_divisible(b, expr, m);
  }

  if (expr->tag == IXS_ADD) {
    return bounds_add_divisible(b, expr, m);
  }

  if (expr->tag == IXS_MAX || expr->tag == IXS_MIN) {
    if (expr->u.assoc.nargs == 0 || !expr->u.assoc.args)
      return false;
    for (i = 0; i < expr->u.assoc.nargs; i++) {
      if (!ixs_bounds_is_known_divisible(b, expr->u.assoc.args[i], m))
        return false;
    }
    return true;
  }

  return false;
}

static bool bounds_piecewise_is_integer_with_divinfo(ixs_bounds *b,
                                                     ixs_node *expr) {
  uint32_t i;
  bool reachable = false;
  for (i = 0; i < expr->u.pw.ncases; i++) {
    ixs_node *cond = expr->u.pw.cases[i].cond;
    ixs_check_result truth = IXS_CHECK_UNKNOWN;
    if (ixs_node_is_known_false(cond))
      truth = IXS_CHECK_FALSE;
    else if (ixs_node_is_known_true(cond))
      truth = IXS_CHECK_TRUE;
    else if (cond && cond->tag == IXS_CMP)
      truth = ixs_bounds_check(b, cond);
    /* An unknown condition leaves both this value and later values reachable.
     */
    if (truth == IXS_CHECK_FALSE)
      continue;
    reachable = true;
    if (!ixs_bounds_is_integer_with_divinfo(b, expr->u.pw.cases[i].value))
      return false;
    if (truth == IXS_CHECK_TRUE)
      return true;
  }
  return reachable;
}

static bool bounds_mul_is_integer_with_divinfo(ixs_bounds *b, ixs_node *expr) {
  uint32_t i;
  int64_t cp;
  int64_t cq;
  int64_t g;
  int64_t denom;

  ixs_node_get_rat(expr->u.mul.coeff, &cp, &cq);
  for (i = 0; i < expr->u.mul.nfactors; i++) {
    if (expr->u.mul.factors[i].exp < 0 ||
        !ixs_bounds_is_integer_with_divinfo(b, expr->u.mul.factors[i].base))
      return false;
  }
  if (cq <= 1)
    return true;
  g = ixs_gcd(cp, cq);
  denom = cq / g;
  for (i = 0; i < expr->u.mul.nfactors; i++) {
    if (expr->u.mul.factors[i].exp >= 1 &&
        ixs_bounds_is_known_divisible(b, expr->u.mul.factors[i].base, denom))
      return true;
  }
  return false;
}

static bool bounds_add_is_integer_with_divinfo(ixs_bounds *b, ixs_node *expr) {
  uint32_t i;

  if (!ixs_bounds_is_integer_with_divinfo(b, expr->u.add.coeff))
    return false;
  for (i = 0; i < expr->u.add.nterms; i++) {
    int64_t cp;
    int64_t cq;
    int64_t g;
    int64_t denom;

    ixs_node_get_rat(expr->u.add.terms[i].coeff, &cp, &cq);
    if (cq == 1) {
      if (!ixs_bounds_is_integer_with_divinfo(b, expr->u.add.terms[i].term))
        return false;
      continue;
    }
    g = ixs_gcd(cp, cq);
    denom = cq / g;
    if (!ixs_bounds_is_known_divisible(b, expr->u.add.terms[i].term, denom))
      return false;
  }
  return true;
}

static bool bounds_assoc_is_integer_with_divinfo(ixs_bounds *b,
                                                 ixs_node *expr) {
  uint32_t i;

  if (expr->u.assoc.nargs == 0 || !expr->u.assoc.args)
    return false;
  for (i = 0; i < expr->u.assoc.nargs; i++) {
    if (!ixs_bounds_is_integer_with_divinfo(b, expr->u.assoc.args[i]))
      return false;
  }
  return true;
}

static bool bounds_mod_is_integer_with_divinfo(ixs_bounds *b, ixs_node *expr) {
  /* Divisor positivity is a separate definedness obligation. */
  return ixs_bounds_is_integer_with_divinfo(b, expr->u.binary.lhs) &&
         ixs_bounds_is_integer_with_divinfo(b, expr->u.binary.rhs);
}

IXS_STATIC bool ixs_bounds_is_integer_with_divinfo(ixs_bounds *b,
                                                   ixs_node *expr) {
  if (!expr)
    return false;
  if (ixs_node_is_integer_valued(expr))
    return true;
  if (!b)
    return false;

  if (expr->tag == IXS_MUL)
    return bounds_mul_is_integer_with_divinfo(b, expr);

  if (expr->tag == IXS_ADD)
    return bounds_add_is_integer_with_divinfo(b, expr);

  if (expr->tag == IXS_MAX || expr->tag == IXS_MIN || expr->tag == IXS_XOR ||
      expr->tag == IXS_AND || expr->tag == IXS_OR)
    return bounds_assoc_is_integer_with_divinfo(b, expr);

  if (expr->tag == IXS_PIECEWISE)
    return bounds_piecewise_is_integer_with_divinfo(b, expr);

  if (expr->tag == IXS_MOD)
    return bounds_mod_is_integer_with_divinfo(b, expr);

  return false;
}

static bool bounds_interval_point_rational(ixs_interval iv, int64_t *p,
                                           int64_t *q) {
  if (!iv.valid || iv.lo_inf || iv.hi_inf ||
      ixs_rat_cmp(iv.lo_p, iv.lo_q, iv.hi_p, iv.hi_q) != 0)
    return false;
  if (p)
    *p = iv.lo_p;
  if (q)
    *q = iv.lo_q;
  return true;
}

IXS_STATIC ixs_check_result ixs_bounds_check_integer_valued(ixs_bounds *b,
                                                            ixs_node *expr) {
  ixs_interval iv;
  int64_t p, q;
  bool proven;
  if (!b || !expr || b->oom || ixs_bounds_has_empty(b))
    return IXS_CHECK_UNKNOWN;
  proven = ixs_bounds_is_integer_with_divinfo(b, expr);
  if (b->oom)
    return IXS_CHECK_UNKNOWN;
  if (proven)
    return IXS_CHECK_TRUE;
  iv = ixs_bounds_get(b, expr);
  if (b->oom || !bounds_interval_point_rational(iv, &p, &q))
    return IXS_CHECK_UNKNOWN;
  (void)p;
  return q == 1 ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
}

static uint64_t bounds_int64_magnitude(int64_t value) {
  if (value >= 0)
    return (uint64_t)value;
  return (uint64_t)(-(value + 1)) + 1u;
}

static bool bounds_int64_divisible_by_u64(int64_t value, uint64_t modulus) {
  return bounds_int64_magnitude(value) % modulus == 0;
}

static uint64_t bounds_normalize_residue(int64_t value, uint64_t modulus) {
  uint64_t magnitude;
  uint64_t remainder;
  if (value >= 0)
    return (uint64_t)value % modulus;
  magnitude = bounds_int64_magnitude(value);
  remainder = magnitude % modulus;
  return remainder == 0 ? 0 : modulus - remainder;
}

static uint64_t bounds_u64_gcd(uint64_t a, uint64_t b) {
  while (b != 0) {
    uint64_t next = a % b;
    a = b;
    b = next;
  }
  return a;
}

static uint64_t bounds_add_mod(uint64_t a, uint64_t b, uint64_t modulus) {
  return (a + b) % modulus;
}

/* modulus is at most 2^63, so doubling two normalized operands cannot
 * overflow uint64_t.  This keeps modular multiplication portable C99. */
static uint64_t bounds_mul_mod(uint64_t a, uint64_t b, uint64_t modulus) {
  uint64_t result = 0;
  a %= modulus;
  while (b != 0) {
    if ((b & 1u) != 0)
      result = bounds_add_mod(result, a, modulus);
    b >>= 1;
    if (b != 0)
      a = bounds_add_mod(a, a, modulus);
  }
  return result;
}

static uint64_t bounds_sub_mod(uint64_t a, uint64_t b, uint64_t modulus) {
  a %= modulus;
  b %= modulus;
  return a >= b ? a - b : modulus - (b - a);
}

/* Extended Euclid with coefficients kept as residues.  This avoids signed
 * coefficient overflow while retaining portable C99 arithmetic. */
static bool bounds_mod_inverse(uint64_t value, uint64_t modulus,
                               uint64_t *inverse) {
  uint64_t r, new_r, t, new_t;
  if (!inverse || modulus <= 1u)
    return false;
  r = modulus;
  new_r = value % modulus;
  t = 0;
  new_t = 1u;
  while (new_r != 0) {
    uint64_t quotient = r / new_r;
    uint64_t next_r = r % new_r;
    uint64_t product = bounds_mul_mod(quotient, new_t, modulus);
    uint64_t next_t = bounds_sub_mod(t, product, modulus);
    r = new_r;
    new_r = next_r;
    t = new_t;
    new_t = next_t;
  }
  if (r != 1u)
    return false;
  *inverse = t;
  return true;
}

static uint64_t bounds_pow_mod(uint64_t base, int32_t exponent,
                               uint64_t modulus) {
  uint64_t result = 1u % modulus;
  while (exponent > 0) {
    if ((exponent & 1) != 0)
      result = bounds_mul_mod(result, base, modulus);
    exponent >>= 1;
    if (exponent != 0)
      base = bounds_mul_mod(base, base, modulus);
  }
  return result;
}

#define CONGRUENCE_DEPTH_LIMIT 64u

static bool bounds_known_residue_depth(ixs_bounds *b, ixs_node *expr,
                                       uint64_t modulus, uint64_t *out,
                                       unsigned depth);

static bool bounds_known_scaled_residue(ixs_bounds *b, ixs_node *expr,
                                        int64_t coefficient, uint64_t modulus,
                                        uint64_t *out, unsigned depth) {
  uint64_t coeff = bounds_normalize_residue(coefficient, modulus);
  uint64_t reduced = modulus / bounds_u64_gcd(coeff, modulus);
  uint64_t residue;
  if (reduced == 1u) {
    *out = 0;
    return true;
  }
  if (!bounds_known_residue_depth(b, expr, reduced, &residue, depth))
    return false;
  *out = bounds_mul_mod(coeff, residue, modulus);
  return true;
}

static bool bounds_known_add_residue(ixs_bounds *b, ixs_node *expr,
                                     uint64_t modulus, uint64_t *out,
                                     unsigned depth) {
  uint64_t result;
  uint32_t i;
  int64_t p, q;
  ixs_node_get_rat(expr->u.add.coeff, &p, &q);
  if (q != 1)
    return false;
  result = bounds_normalize_residue(p, modulus);
  for (i = 0; i < expr->u.add.nterms; i++) {
    uint64_t term;
    ixs_node_get_rat(expr->u.add.terms[i].coeff, &p, &q);
    if (q != 1 || !bounds_known_scaled_residue(b, expr->u.add.terms[i].term, p,
                                               modulus, &term, depth - 1))
      return false;
    result = bounds_add_mod(result, term, modulus);
  }
  *out = result;
  return true;
}

static bool bounds_known_mul_residue(ixs_bounds *b, ixs_node *expr,
                                     uint64_t modulus, uint64_t *out,
                                     unsigned depth) {
  uint64_t coeff, reduced, product;
  uint32_t i;
  int64_t p, q;
  ixs_node_get_rat(expr->u.mul.coeff, &p, &q);
  if (q != 1)
    return false;
  coeff = bounds_normalize_residue(p, modulus);
  reduced = modulus / bounds_u64_gcd(coeff, modulus);
  if (reduced == 1u) {
    *out = 0;
    return true;
  }
  product = 1u % reduced;
  for (i = 0; i < expr->u.mul.nfactors; i++) {
    uint64_t base;
    int32_t exponent = expr->u.mul.factors[i].exp;
    if (exponent < 0 ||
        !bounds_known_residue_depth(b, expr->u.mul.factors[i].base, reduced,
                                    &base, depth - 1))
      return false;
    product = bounds_mul_mod(product, bounds_pow_mod(base, exponent, reduced),
                             reduced);
    if (product == 0)
      break;
  }
  *out = bounds_mul_mod(coeff, product, modulus);
  return true;
}

static bool bounds_known_symbol_residue(ixs_bounds *b, ixs_node *expr,
                                        uint64_t modulus, uint64_t *out) {
  int64_t stored_modulus, stored_residue;
  if (modulus > (uint64_t)INT64_MAX ||
      !ixs_bounds_get_modrem(b, expr->u.name, &stored_modulus,
                             &stored_residue) ||
      (uint64_t)stored_modulus % modulus != 0)
    return false;
  *out = (uint64_t)stored_residue % modulus;
  return true;
}

static bool bounds_known_mod_residue(ixs_bounds *b, ixs_node *expr,
                                     uint64_t modulus, uint64_t *out,
                                     unsigned depth) {
  if (expr->u.binary.rhs->tag != IXS_INT || expr->u.binary.rhs->u.ival <= 0 ||
      (uint64_t)expr->u.binary.rhs->u.ival % modulus != 0)
    return false;
  return bounds_known_residue_depth(b, expr->u.binary.lhs, modulus, out,
                                    depth - 1);
}

static bool bounds_known_extrema_residue(ixs_bounds *b, ixs_node *expr,
                                         uint64_t modulus, uint64_t *out,
                                         unsigned depth) {
  uint64_t result, arg;
  uint32_t i;
  if (expr->u.assoc.nargs == 0 || !expr->u.assoc.args ||
      !bounds_known_residue_depth(b, expr->u.assoc.args[0], modulus, &result,
                                  depth - 1))
    return false;
  for (i = 1; i < expr->u.assoc.nargs; i++) {
    if (!bounds_known_residue_depth(b, expr->u.assoc.args[i], modulus, &arg,
                                    depth - 1) ||
        result != arg)
      return false;
  }
  *out = result;
  return true;
}

static bool bounds_known_structural_residue(ixs_bounds *b, ixs_node *expr,
                                            uint64_t modulus, uint64_t *out,
                                            unsigned depth) {
  switch (expr->tag) {
  case IXS_INT:
    *out = bounds_normalize_residue(expr->u.ival, modulus);
    return true;
  case IXS_RAT:
    if (expr->u.rat.q != 1)
      return false;
    *out = bounds_normalize_residue(expr->u.rat.p, modulus);
    return true;
  case IXS_SYM:
    return bounds_known_symbol_residue(b, expr, modulus, out);
  case IXS_ADD:
    return bounds_known_add_residue(b, expr, modulus, out, depth);
  case IXS_MUL:
    return bounds_known_mul_residue(b, expr, modulus, out, depth);
  case IXS_MOD:
    return bounds_known_mod_residue(b, expr, modulus, out, depth);
  case IXS_MAX:
  case IXS_MIN:
    return bounds_known_extrema_residue(b, expr, modulus, out, depth);
  default:
    return false;
  }
}

static bool bounds_known_residue_depth(ixs_bounds *b, ixs_node *expr,
                                       uint64_t modulus, uint64_t *out,
                                       unsigned depth) {
  ixs_interval iv;
  ixs_bitfacts bits;
  int64_t exact;
  if (!b || !expr || !out || modulus == 0 || depth == 0 || b->oom ||
      ixs_bounds_check_integer_valued(b, expr) != IXS_CHECK_TRUE)
    return false;
  if (modulus == 1u) {
    *out = 0;
    return true;
  }

  iv = ixs_bounds_get(b, expr);
  if (b->oom)
    return false;
  if (ixs_interval_is_point_int(iv, &exact)) {
    *out = bounds_normalize_residue(exact, modulus);
    return true;
  }

  if (uint64_is_pow2(modulus) && ixs_bounds_get_bitfacts(b, expr, &bits)) {
    uint64_t mask = modulus - 1u;
    if (((bits.known_zero | bits.known_one) & mask) == mask) {
      *out = bits.known_one & mask;
      return true;
    }
  }
  if (b->oom)
    return false;
  return bounds_known_structural_residue(b, expr, modulus, out, depth);
}

IXS_STATIC ixs_check_result ixs_bounds_check_divisible(ixs_bounds *b,
                                                       ixs_node *expr,
                                                       int64_t modulus) {
  ixs_check_result integer_result;
  ixs_interval iv;
  ixs_bitfacts bits;
  uint64_t magnitude;
  int64_t exact;

  if (!b || !expr || modulus == 0 || b->oom || ixs_bounds_has_empty(b))
    return IXS_CHECK_UNKNOWN;

  integer_result = ixs_bounds_check_integer_valued(b, expr);
  if (integer_result != IXS_CHECK_TRUE)
    return integer_result;

  magnitude = bounds_int64_magnitude(modulus);
  if (magnitude == 1u)
    return IXS_CHECK_TRUE;

  iv = ixs_bounds_get(b, expr);
  if (b->oom)
    return IXS_CHECK_UNKNOWN;
  if (ixs_interval_is_point_int(iv, &exact))
    return bounds_int64_divisible_by_u64(exact, magnitude) ? IXS_CHECK_TRUE
                                                           : IXS_CHECK_FALSE;

  if (magnitude <= (uint64_t)INT64_MAX) {
    bool proven = ixs_bounds_is_known_divisible(b, expr, (int64_t)magnitude);
    if (b->oom)
      return IXS_CHECK_UNKNOWN;
    if (proven)
      return IXS_CHECK_TRUE;
  }

  if (magnitude == (uint64_t)INT64_MAX + 1u) {
    bool has_bits = ixs_bounds_get_bitfacts(b, expr, &bits);
    if (b->oom)
      return IXS_CHECK_UNKNOWN;
    if (has_bits && (bits.known_zero & (magnitude - 1u)) == magnitude - 1u)
      return IXS_CHECK_TRUE;
  }

  return IXS_CHECK_UNKNOWN;
}

IXS_STATIC ixs_check_result ixs_bounds_check_congruent(ixs_bounds *b,
                                                       ixs_node *expr,
                                                       int64_t modulus,
                                                       int64_t residue) {
  ixs_check_result integer_result;
  uint64_t actual;
  uint64_t magnitude;
  uint64_t expected;
  if (!b || !expr || modulus == 0 || b->oom || ixs_bounds_has_empty(b))
    return IXS_CHECK_UNKNOWN;
  integer_result = ixs_bounds_check_integer_valued(b, expr);
  if (integer_result != IXS_CHECK_TRUE)
    return integer_result;
  magnitude = bounds_int64_magnitude(modulus);
  expected = bounds_normalize_residue(residue, magnitude);
  if (!bounds_known_residue_depth(b, expr, magnitude, &actual,
                                  CONGRUENCE_DEPTH_LIMIT))
    return IXS_CHECK_UNKNOWN;
  return actual == expected ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
}

static ixs_interval bounds_get_and_mask(ixs_bounds *b, ixs_node *expr) {
  int64_t mask = 0;
  uint32_t i;
  bool have_mask = false;
  if (expr->u.assoc.nargs == 0 || !expr->u.assoc.args)
    return ixs_interval_unknown();
  for (i = 0; i < expr->u.assoc.nargs; i++) {
    ixs_node *arg = expr->u.assoc.args[i];
    if (!ixs_bounds_is_integer_with_divinfo(b, arg))
      return ixs_interval_unknown();
    if (arg->tag == IXS_INT && arg->u.ival >= 0 &&
        (!have_mask || arg->u.ival < mask)) {
      mask = arg->u.ival;
      have_mask = true;
    }
  }
  return have_mask ? ixs_interval_range(0, 1, mask, 1) : ixs_interval_unknown();
}

static ixs_interval bounds_get_xor(ixs_bounds *b, ixs_node *expr) {
  ixs_interval arg_iv, result;
  ixs_bitfacts arg_bits, next_bits, result_bits;
  int64_t arg_hi, max_hi = 0;
  uint64_t span, possible, required;
  uint32_t i;
  bool have_bits;

  if (expr->u.assoc.nargs == 0 || !expr->u.assoc.args)
    return ixs_interval_unknown();

  result = ixs_interval_unknown();
  result.valid = true;
  result.lo_p = 0;
  result.lo_q = 1;
  result.lo_inf = false;
  result.hi_inf = false;
  for (i = 0; i < expr->u.assoc.nargs; i++) {
    ixs_node *arg = expr->u.assoc.args[i];
    if (!ixs_bounds_is_integer_with_divinfo(b, arg))
      return ixs_interval_unknown();
    arg_iv = ixs_bounds_get(b, arg);
    if (!interval_lower_at_least(&arg_iv, 0, 1))
      return ixs_interval_unknown();
    if (arg_iv.hi_inf) {
      result.hi_inf = true;
      continue;
    }
    arg_hi = ixs_rat_floor(arg_iv.hi_p, arg_iv.hi_q);
    if (arg_hi > max_hi)
      max_hi = arg_hi;
  }
  if (result.hi_inf) {
    ixs_interval_set_hi_pos_inf(&result);
    return result;
  }

  span = value_span_mask((uint64_t)max_hi);
  possible = span;
  required = 0;
  have_bits = ixs_bounds_get_bitfacts(b, expr->u.assoc.args[0], &result_bits);
  for (i = 1; have_bits && i < expr->u.assoc.nargs; i++) {
    if (!ixs_bounds_get_bitfacts(b, expr->u.assoc.args[i], &arg_bits)) {
      have_bits = false;
      break;
    }
    bitfacts_apply_xor(&next_bits, &result_bits, &arg_bits);
    result_bits = next_bits;
  }
  if (have_bits) {
    possible &= ~result_bits.known_zero;
    required = result_bits.known_one & span;
  }
  if (required > possible)
    return ixs_interval_unknown();
  result.lo_p = (int64_t)required;
  result.hi_p = (int64_t)possible;
  result.hi_q = 1;
  return result;
}

static ixs_interval bounds_get_proportional_range(ixs_bounds *b,
                                                  ixs_node *expr) {
  ixs_node *primitive, *canonical;
  ixs_interval primitive_iv;
  int64_t scale_p, scale_q, offset_p, offset_q;
  if (!bounds_get_proportional_primitive(b, expr, &primitive, &scale_p,
                                         &scale_q, &offset_p, &offset_q) ||
      (primitive == expr && scale_p == 1 && scale_q == 1 && offset_p == 0))
    return ixs_interval_unknown();
  primitive_iv = bounds_get_expr_overrides(b, primitive);
  canonical = bounds_canonical_expr(b, primitive);
  if (canonical && canonical != primitive)
    primitive_iv =
        iv_intersect(primitive_iv, bounds_get_expr_overrides(b, canonical));
  if (!primitive_iv.valid)
    return ixs_interval_unknown();
  return bounds_apply_affine(primitive_iv, scale_p, scale_q, offset_p,
                             offset_q);
}

static inline ixs_interval bounds_get_add(ixs_bounds *b, ixs_node *expr) {
  uint32_t i;
  ixs_interval result = ixs_bounds_get(b, expr->u.add.coeff);
  for (i = 0; i < expr->u.add.nterms; i++) {
    int64_t cp, cq;
    ixs_interval ti = ixs_bounds_get(b, expr->u.add.terms[i].term);
    ixs_interval scaled;
    ixs_node_get_rat(expr->u.add.terms[i].coeff, &cp, &cq);
    scaled = iv_mul_const(ti, cp, cq);
    result = iv_add(result, scaled);
  }
  if (!b->oom && b->nexprs != 0)
    result = iv_intersect(result, bounds_get_proportional_range(b, expr));
  if (!b->oom && b->nexprs != 0 && !ixs_node_is_zero(expr->u.add.coeff)) {
    ixs_node *base = bounds_expr_without_add_const(b, expr);
    if (base && base != expr) {
      ixs_interval base_iv = ixs_bounds_get(b, base);
      ixs_interval offset = ixs_bounds_get(b, expr->u.add.coeff);
      result = iv_intersect(result, iv_add(base_iv, offset));
    }
  }
  return result;
}

static inline ixs_interval bounds_get_mul(ixs_bounds *b, ixs_node *expr) {
  uint32_t i;
  int64_t cp, cq;
  ixs_interval result;
  ixs_node_get_rat(expr->u.mul.coeff, &cp, &cq);
  result = ixs_interval_exact(cp, cq);
  for (i = 0; i < expr->u.mul.nfactors; i++) {
    int32_t exp = expr->u.mul.factors[i].exp;
    int64_t exp64 = exp;
    uint32_t magnitude;
    ixs_interval fi = ixs_bounds_get(b, expr->u.mul.factors[i].base);
    ixs_interval powered;
    if (!fi.valid)
      return ixs_interval_unknown();
    if (exp == 0)
      return ixs_interval_unknown();
    magnitude = (uint32_t)(exp64 < 0 ? -exp64 : exp64);
    if (magnitude > RANGE_POWER_EXP_LIMIT)
      return ixs_interval_unknown();
    powered = iv_pow(fi, magnitude);
    if (exp < 0)
      powered = iv_recip(powered);
    if (!powered.valid)
      return ixs_interval_unknown();
    result = iv_mul(result, powered);
  }
  return result;
}

/* O(1) for a full residue cycle; partial cycles inspect at most
 * MOD_RANGE_ENUM_LIMIT reachable values. */
static bool bounds_symbol_mod_range(ixs_bounds *b, ixs_node *symbol,
                                    const ixs_interval *iv, int64_t modulus,
                                    ixs_interval *out) {
  int64_t known_modulus, known_remainder, lo, hi, current, delta, first;
  uint64_t steps, cycle, step, residue, min_residue, max_residue, i;
  uint64_t g;

  if (symbol->tag != IXS_SYM || !iv->valid || iv->lo_inf || iv->hi_inf ||
      modulus <= 0 ||
      !ixs_bounds_get_modrem(b, symbol->u.name, &known_modulus,
                             &known_remainder))
    return false;

  lo = ixs_rat_ceil(iv->lo_p, iv->lo_q);
  hi = ixs_rat_floor(iv->hi_p, iv->hi_q);
  if (lo > hi)
    return false;
  current = lo % known_modulus;
  if (current < 0)
    current += known_modulus;
  delta = known_remainder >= current
              ? known_remainder - current
              : known_modulus - (current - known_remainder);
  if (!ixs_safe_add(lo, delta, &first) || first > hi)
    return false;

  steps = ((uint64_t)hi - (uint64_t)first) / (uint64_t)known_modulus;
  step = (uint64_t)known_modulus % (uint64_t)modulus;
  residue = bounds_normalize_residue(first, (uint64_t)modulus);
  g = bounds_u64_gcd(step, (uint64_t)modulus);
  cycle = (uint64_t)modulus / g;
  if (steps >= cycle - 1u) {
    min_residue = residue % g;
    max_residue = min_residue + (uint64_t)modulus - g;
  } else {
    if (steps > MOD_RANGE_ENUM_LIMIT)
      return false;
    min_residue = residue;
    max_residue = residue;
    for (i = 0; i < steps; i++) {
      residue = bounds_add_mod(residue, step, (uint64_t)modulus);
      if (residue < min_residue)
        min_residue = residue;
      if (residue > max_residue)
        max_residue = residue;
    }
  }

  *out = ixs_interval_range((int64_t)min_residue, 1, (int64_t)max_residue, 1);
  return true;
}

static inline ixs_interval bounds_get_mod(ixs_bounds *b, ixs_node *expr) {
  ixs_node *m = expr->u.binary.rhs;
  ixs_interval mi = ixs_bounds_get(b, m);
  int64_t exact_m;

  if (interval_exact_int(&mi, &exact_m) && exact_m > 0) {
    ixs_interval pi = ixs_bounds_get(b, expr->u.binary.lhs);
    int64_t exact_lhs;
    uint64_t residue;
    ixs_interval congruent;
    if (interval_exact_int(&pi, &exact_lhs))
      return ixs_interval_exact(
          (int64_t)bounds_normalize_residue(exact_lhs, (uint64_t)exact_m), 1);
    if (b->has_modrem &&
        bounds_known_residue_depth(b, expr->u.binary.lhs, (uint64_t)exact_m,
                                   &residue, CONGRUENCE_DEPTH_LIMIT))
      return ixs_interval_exact((int64_t)residue, 1);
    if (b->has_modrem && bounds_symbol_mod_range(b, expr->u.binary.lhs, &pi,
                                                 exact_m, &congruent))
      return congruent;
    if (pi.valid && pi.lo_q == 1 && pi.hi_q == 1 && pi.lo_p >= 0 &&
        pi.hi_p < exact_m)
      return pi;
    if (ixs_node_is_integer_valued(expr->u.binary.lhs)) {
      int64_t g = mod_dividend_gcd(expr->u.binary.lhs, exact_m);
      return ixs_interval_range(0, 1, exact_m - g, 1);
    }
  }

  if (ixs_node_is_integer_valued(expr->u.binary.lhs) &&
      ixs_node_is_integer_valued(m) && interval_lower_at_least(&mi, 1, 1)) {
    ixs_interval result = ixs_interval_unknown();
    result.valid = true;
    result.lo_inf = false;
    result.lo_p = 0;
    result.lo_q = 1;
    if (mi.hi_inf) {
      ixs_interval_set_hi_pos_inf(&result);
    } else {
      int64_t upper = ixs_rat_floor(mi.hi_p, mi.hi_q);
      if (!ixs_safe_sub(upper, 1, &result.hi_p))
        ixs_interval_set_hi_pos_inf(&result);
      else {
        result.hi_q = 1;
        result.hi_inf = false;
      }
    }
    return result;
  }
  return ixs_interval_unknown();
}

static inline ixs_interval bounds_get_round(ixs_bounds *b, ixs_node *expr,
                                            bool is_ceil) {
  ixs_interval ai = ixs_bounds_get(b, expr->u.unary.arg);
  ixs_interval result;
  if (!ai.valid)
    return ixs_interval_unknown();
  if (is_ceil) {
    result = ixs_interval_range(ixs_rat_ceil(ai.lo_p, ai.lo_q), 1,
                                ixs_rat_ceil(ai.hi_p, ai.hi_q), 1);
  } else {
    result = ixs_interval_range(ixs_rat_floor(ai.lo_p, ai.lo_q), 1,
                                ixs_rat_floor(ai.hi_p, ai.hi_q), 1);
  }
  result.lo_inf = ai.lo_inf;
  result.hi_inf = ai.hi_inf;
  return result;
}

static inline void interval_set_max_lower(ixs_interval *result,
                                          const ixs_interval *li,
                                          const ixs_interval *ri) {
  if (li->lo_inf && !ri->lo_inf) {
    result->lo_p = ri->lo_p;
    result->lo_q = ri->lo_q;
  } else if (!li->lo_inf && ri->lo_inf) {
    result->lo_p = li->lo_p;
    result->lo_q = li->lo_q;
  } else if (ixs_rat_cmp(li->lo_p, li->lo_q, ri->lo_p, ri->lo_q) >= 0) {
    result->lo_p = li->lo_p;
    result->lo_q = li->lo_q;
    result->lo_inf = li->lo_inf;
  } else {
    result->lo_p = ri->lo_p;
    result->lo_q = ri->lo_q;
    result->lo_inf = ri->lo_inf;
  }
}

static inline void interval_set_max_upper(ixs_interval *result,
                                          const ixs_interval *li,
                                          const ixs_interval *ri) {
  if (li->hi_inf || ri->hi_inf) {
    ixs_interval_set_hi_pos_inf(result);
  } else if (ixs_rat_cmp(li->hi_p, li->hi_q, ri->hi_p, ri->hi_q) >= 0) {
    result->hi_p = li->hi_p;
    result->hi_q = li->hi_q;
  } else {
    result->hi_p = ri->hi_p;
    result->hi_q = ri->hi_q;
  }
}

static inline void interval_set_min_lower(ixs_interval *result,
                                          const ixs_interval *li,
                                          const ixs_interval *ri) {
  if (li->lo_inf || ri->lo_inf) {
    ixs_interval_set_lo_neg_inf(result);
  } else if (ixs_rat_cmp(li->lo_p, li->lo_q, ri->lo_p, ri->lo_q) <= 0) {
    result->lo_p = li->lo_p;
    result->lo_q = li->lo_q;
  } else {
    result->lo_p = ri->lo_p;
    result->lo_q = ri->lo_q;
  }
}

static inline void interval_set_min_upper(ixs_interval *result,
                                          const ixs_interval *li,
                                          const ixs_interval *ri) {
  if (li->hi_inf && !ri->hi_inf) {
    result->hi_p = ri->hi_p;
    result->hi_q = ri->hi_q;
  } else if (!li->hi_inf && ri->hi_inf) {
    result->hi_p = li->hi_p;
    result->hi_q = li->hi_q;
  } else if (ixs_rat_cmp(li->hi_p, li->hi_q, ri->hi_p, ri->hi_q) <= 0) {
    result->hi_p = li->hi_p;
    result->hi_q = li->hi_q;
    result->hi_inf = li->hi_inf;
  } else {
    result->hi_p = ri->hi_p;
    result->hi_q = ri->hi_q;
    result->hi_inf = ri->hi_inf;
  }
}

static inline ixs_interval bounds_get_extrema(ixs_bounds *b, ixs_node *expr,
                                              bool is_max) {
  ixs_interval result, arg, merged;
  uint32_t i;
  if (expr->u.assoc.nargs == 0 || !expr->u.assoc.args)
    return ixs_interval_unknown();
  result = ixs_bounds_get(b, expr->u.assoc.args[0]);
  if (!result.valid)
    return ixs_interval_unknown();
  for (i = 1; i < expr->u.assoc.nargs; i++) {
    arg = ixs_bounds_get(b, expr->u.assoc.args[i]);
    if (!arg.valid)
      return ixs_interval_unknown();
    merged = ixs_interval_unknown();
    merged.valid = true;
    if (is_max) {
      interval_set_max_lower(&merged, &result, &arg);
      interval_set_max_upper(&merged, &result, &arg);
    } else {
      interval_set_min_lower(&merged, &result, &arg);
      interval_set_min_upper(&merged, &result, &arg);
    }
    result = merged;
  }
  return result;
}

static ixs_cmp_op bounds_negate_cmp_op(ixs_cmp_op op) {
  switch (op) {
  case IXS_CMP_GT:
    return IXS_CMP_LE;
  case IXS_CMP_GE:
    return IXS_CMP_LT;
  case IXS_CMP_LT:
    return IXS_CMP_GE;
  case IXS_CMP_LE:
    return IXS_CMP_GT;
  case IXS_CMP_EQ:
    return IXS_CMP_NE;
  case IXS_CMP_NE:
    return IXS_CMP_EQ;
  }
  return op;
}

static ixs_node *bounds_condition_assumption(ixs_bounds *b, ixs_node *cond,
                                             bool value,
                                             struct ixs_node_impl *storage) {
  if (!b->ctx)
    return NULL;
  memset(storage, 0, sizeof(*storage));
  storage->tag = IXS_CMP;
  storage->u.binary.rhs = b->ctx->node_zero;
  if (cond->tag == IXS_CMP) {
    storage->u.binary.lhs = cond->u.binary.lhs;
    storage->u.binary.rhs = cond->u.binary.rhs;
    storage->u.binary.cmp_op =
        value ? cond->u.binary.cmp_op
              : bounds_negate_cmp_op(cond->u.binary.cmp_op);
  } else {
    storage->u.binary.lhs = cond;
    storage->u.binary.cmp_op = value ? IXS_CMP_NE : IXS_CMP_EQ;
  }
  return storage;
}

static ixs_check_result bounds_condition_truth(ixs_bounds *b, ixs_node *cond) {
  struct ixs_node_impl cmp;
  if (ixs_node_is_known_false(cond))
    return IXS_CHECK_FALSE;
  if (ixs_node_is_known_true(cond))
    return IXS_CHECK_TRUE;
  if (!bounds_condition_assumption(b, cond, true, &cmp))
    return IXS_CHECK_UNKNOWN;
  return ixs_bounds_check(b, &cmp);
}

static bool bounds_piecewise_active(ixs_bounds *owner, ixs_bounds *remaining,
                                    ixs_node *cond, ixs_node *value,
                                    ixs_interval *result, bool *have_result) {
  ixs_arena_mark mark = ixs_arena_save(owner->scratch);
  ixs_bounds active;
  struct ixs_node_impl assumption;
  ixs_interval branch;
  bool ok = false;

  memset(&active, 0, sizeof(active));
  if (!ixs_bounds_fork(&active, remaining)) {
    owner->oom = true;
    goto cleanup;
  }
  if (!ixs_bounds_add_assumption(
          &active,
          bounds_condition_assumption(&active, cond, true, &assumption))) {
    if (active.oom)
      owner->oom = true;
    goto cleanup;
  }
  if (ixs_bounds_has_empty(&active)) {
    ok = true;
    goto cleanup;
  }
  if (ixs_bounds_check_defined(&active, value) != IXS_CHECK_TRUE)
    goto cleanup;
  branch = ixs_bounds_get(&active, value);
  if (!branch.valid)
    goto cleanup;
  if (!*have_result) {
    *result = branch;
    *have_result = true;
  } else {
    *result = iv_hull(*result, branch);
  }
  ok = true;

cleanup:
  if (active.oom)
    owner->oom = true;
  ixs_arena_restore(owner->scratch, mark);
  return ok;
}

static ixs_interval bounds_get_piecewise(ixs_bounds *b, ixs_node *expr) {
  ixs_interval result = ixs_interval_unknown();
  ixs_arena_mark outer_mark;
  ixs_bounds remaining;
  bool have_result = false;
  bool covered = false;
  bool failed = false;
  uint32_t i;

  if (!b->ctx || b->range_pw_depth >= RANGE_PW_DEPTH_LIMIT ||
      expr->u.pw.ncases == 0 || expr->u.pw.ncases > RANGE_PW_CASE_LIMIT ||
      (expr->u.pw.ncases > 0 && !expr->u.pw.cases))
    return result;

  outer_mark = ixs_arena_save(b->scratch);
  b->range_pw_depth++;
  if (!ixs_bounds_fork(&remaining, b)) {
    b->oom = true;
    failed = true;
    goto cleanup;
  }

  for (i = 0; i < expr->u.pw.ncases; i++) {
    ixs_node *cond = expr->u.pw.cases[i].cond;
    ixs_node *value = expr->u.pw.cases[i].value;
    ixs_check_result truth;
    struct ixs_node_impl assumption;

    if (!cond || !value || remaining.oom) {
      failed = true;
      break;
    }
    if (ixs_bounds_has_empty(&remaining)) {
      covered = true;
      break;
    }
    if (ixs_bounds_check_defined(&remaining, cond) != IXS_CHECK_TRUE) {
      failed = true;
      break;
    }
    truth = bounds_condition_truth(&remaining, cond);
    if (truth == IXS_CHECK_FALSE)
      continue;

    if (!bounds_piecewise_active(b, &remaining, cond, value, &result,
                                 &have_result)) {
      failed = true;
      break;
    }
    if (truth == IXS_CHECK_TRUE) {
      covered = true;
      break;
    }
    if (!ixs_bounds_add_assumption(
            &remaining, bounds_condition_assumption(&remaining, cond, false,
                                                    &assumption))) {
      b->oom = true;
      failed = true;
      break;
    }
  }

  if (!failed && !covered && ixs_bounds_has_empty(&remaining))
    covered = true;
  if (!covered)
    failed = true;

cleanup:
  ixs_arena_restore(b->scratch, outer_mark);
  b->range_pw_depth--;
  if (failed || !have_result)
    return ixs_interval_unknown();
  return result;
}

static inline ixs_interval bounds_get_propagated(ixs_bounds *b,
                                                 ixs_node *expr) {
  if (!expr)
    return ixs_interval_unknown();

  switch (expr->tag) {
  case IXS_INT:
    return ixs_interval_exact(expr->u.ival, 1);
  case IXS_RAT:
    return ixs_interval_exact(expr->u.rat.p, expr->u.rat.q);
  case IXS_ADD:
    return bounds_get_add(b, expr);
  case IXS_MUL:
    return bounds_get_mul(b, expr);
  case IXS_MOD:
    return bounds_get_mod(b, expr);
  case IXS_FLOOR:
    return bounds_get_round(b, expr, false);
  case IXS_CEIL:
    return bounds_get_round(b, expr, true);
  case IXS_MAX:
    return bounds_get_extrema(b, expr, true);
  case IXS_MIN:
    return bounds_get_extrema(b, expr, false);
  case IXS_AND:
    return bounds_get_and_mask(b, expr);
  case IXS_XOR:
    return bounds_get_xor(b, expr);
  case IXS_PIECEWISE:
    return bounds_get_piecewise(b, expr);
  default:
    return ixs_interval_unknown();
  }
}

IXS_STATIC ixs_interval ixs_bounds_get(ixs_bounds *b, ixs_node *expr) {
  ixs_interval iv;
  ixs_node *canon = NULL;
  ixs_var_bound *var = NULL;
  int64_t exact;
  if (!b)
    return ixs_interval_unknown();
  if (bounds_cacheable_expr(expr) && bounds_cache_lookup(b, expr, &iv))
    return iv;

  if (expr && expr->tag == IXS_SYM) {
    /* Retain the indexed symbol result through override intersection. */
    var = find_var(b, expr->u.name);
    iv = var ? var->iv : ixs_interval_unknown();
  } else {
    iv = bounds_get_propagated(b, expr);
  }
  if (b->nexprs && expr) {
    iv = iv_intersect(iv, bounds_get_expr_overrides(b, expr));
    canon = bounds_canonical_expr(b, expr);
    if (canon && canon != expr)
      iv = iv_intersect(iv, bounds_get_expr_overrides(b, canon));
  }
  if (var && var->modulus > 0)
    iv = interval_intersect_congruence(iv, var->modulus, var->remainder);
  if (bounds_exact_unit_difference_value(b, expr, &exact) ||
      (canon && canon != expr &&
       bounds_exact_unit_difference_value(b, canon, &exact)))
    iv = iv_intersect(iv, ixs_interval_exact(exact, 1));
  if (bounds_cacheable_expr(expr))
    bounds_cache_store(b, expr, iv);
  return iv;
}

static bool bounds_exact_integer_difference(ixs_bounds *b, ixs_node *difference,
                                            int64_t *delta) {
  int64_t p;
  int64_t q;
  if (!b || !difference || !delta || b->oom || b->contradiction ||
      ixs_node_is_sentinel(difference))
    return false;
  if (ixs_node_is_const(difference)) {
    ixs_node_get_rat(difference, &p, &q);
    if (q == 1) {
      *delta = p;
      return true;
    }
  }
  return ixs_interval_is_point_int(ixs_bounds_get(b, difference), delta);
}

static bool bounds_interval_is_zero(ixs_interval iv) {
  return iv.valid && !iv.lo_inf && !iv.hi_inf && iv.lo_p == 0 && iv.hi_p == 0;
}

static bool bounds_has_zero_nonzero_conflict(ixs_bounds *b) {
  size_t i;
  for (i = 0; i < b->nnonzero; i++) {
    ixs_node *expr = b->nonzero[i];
    ixs_interval iv;
    if (ixs_node_is_zero(expr))
      return true;
    if (expr->tag == IXS_SYM) {
      ixs_var_bound *var = find_var(b, expr->u.name);
      if (var && bounds_interval_is_zero(var->iv))
        return true;
    }
    iv = bounds_get_expr_overrides(b, expr);
    if (bounds_interval_is_zero(iv))
      return true;
  }
  return false;
}

static bool bounds_cache_empty_result(ixs_bounds *b, bool result) {
  b->empty_cache_valid = true;
  b->empty_cache_value = result;
  return result;
}

/* Cache hit is O(1); miss scans variables, expressions, and exclusions. */
IXS_STATIC bool ixs_bounds_has_empty(ixs_bounds *b) {
  size_t i;

  if (b->empty_cache_valid)
    return b->empty_cache_value;
  if (b->contradiction)
    return bounds_cache_empty_result(b, true);

  for (i = 0; i < b->nvars; i++) {
    refine_var_bit_consistency(b, &b->vars[i]);
    if (b->contradiction)
      return bounds_cache_empty_result(b, true);
    if (ixs_interval_is_empty(b->vars[i].iv))
      return bounds_cache_empty_result(b, true);
  }

  for (i = 0; i < b->nexprs; i++) {
    ixs_interval iv = b->exprs[i].iv;
    ixs_var_bound *var = NULL;
    if (!iv.valid || ixs_interval_is_empty(iv))
      return bounds_cache_empty_result(b, true);
    if (b->exprs[i].expr->tag == IXS_SYM)
      var = find_var(b, b->exprs[i].expr->u.name);
    if (var) {
      iv = iv_intersect(iv, var->iv);
      if (!iv.valid || ixs_interval_is_empty(iv) ||
          (var->modulus > 0 &&
           !interval_has_congruent_integer(&iv, var->modulus, var->remainder)))
        return bounds_cache_empty_result(b, true);
    }
  }

  if (bounds_has_zero_nonzero_conflict(b))
    return bounds_cache_empty_result(b, true);

  return bounds_cache_empty_result(b, false);
}

typedef struct {
  ixs_node *dividend;
  int64_t modulus;
  int64_t remainder;
} ixs_mod_query;

static bool bounds_extract_mod_query(ixs_node *expr, ixs_mod_query *out) {
  ixs_node *mod_node;
  int64_t rem_val;

  if (!expr || !out)
    return false;

  if (expr->tag == IXS_MOD) {
    mod_node = expr;
    rem_val = 0;
  } else if (expr->tag == IXS_ADD && expr->u.add.nterms == 1 &&
             expr->u.add.terms[0].term->tag == IXS_MOD) {
    int64_t cp, cq, kp, kq;
    ixs_node_get_rat(expr->u.add.terms[0].coeff, &cp, &cq);
    ixs_node_get_rat(expr->u.add.coeff, &kp, &kq);
    if (cq != 1 || kq != 1)
      return false;
    if (cp == 1) {
      if (kp == INT64_MIN)
        return false;
      rem_val = -kp;
    } else if (cp == -1) {
      rem_val = kp;
    } else {
      return false;
    }
    mod_node = expr->u.add.terms[0].term;
  } else {
    return false;
  }

  if (mod_node->u.binary.rhs->tag != IXS_INT ||
      mod_node->u.binary.rhs->u.ival <= 0)
    return false;

  out->dividend = mod_node->u.binary.lhs;
  out->modulus = mod_node->u.binary.rhs->u.ival;
  out->remainder = rem_val;
  return true;
}

static ixs_check_result bounds_check_mod_query(ixs_bounds *b, ixs_node *cmp) {
  ixs_mod_query q;
  int64_t actual;
  bool known = false;
  bool equal;

  if (cmp->u.binary.cmp_op != IXS_CMP_EQ && cmp->u.binary.cmp_op != IXS_CMP_NE)
    return IXS_CHECK_UNKNOWN;
  if (!bounds_extract_mod_query(cmp->u.binary.lhs, &q))
    return IXS_CHECK_UNKNOWN;

  if (q.remainder < 0 || q.remainder >= q.modulus) {
    if (cmp->u.binary.cmp_op == IXS_CMP_EQ)
      return IXS_CHECK_FALSE;
    return IXS_CHECK_TRUE;
  }

  if (q.dividend->tag == IXS_INT) {
    actual = ((q.dividend->u.ival % q.modulus) + q.modulus) % q.modulus;
    known = true;
  } else if (q.dividend->tag == IXS_SYM) {
    int64_t sym_mod, sym_rem;
    if (ixs_bounds_get_modrem(b, q.dividend->u.name, &sym_mod, &sym_rem) &&
        sym_mod % q.modulus == 0) {
      actual = sym_rem % q.modulus;
      known = true;
    }
  }

  if (!known && q.remainder == 0 &&
      ixs_bounds_is_known_divisible(b, q.dividend, q.modulus)) {
    actual = 0;
    known = true;
  }

  if (!known)
    return IXS_CHECK_UNKNOWN;

  equal = actual == q.remainder;
  if (cmp->u.binary.cmp_op == IXS_CMP_EQ)
    return equal ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
  return equal ? IXS_CHECK_FALSE : IXS_CHECK_TRUE;
}

static ixs_check_result check_equal_result(ixs_cmp_op op, bool equal) {
  if (op == IXS_CMP_EQ)
    return equal ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
  if (op == IXS_CMP_NE)
    return equal ? IXS_CHECK_FALSE : IXS_CHECK_TRUE;
  return IXS_CHECK_UNKNOWN;
}

static ixs_check_result bounds_check_pow2_query(ixs_bounds *b, ixs_node *cmp,
                                                ixs_node *expr, int64_t value) {
  const char *name;
  struct ixs_node_impl sym_tmp;
  if (!extract_pow2_and(expr, &name))
    return IXS_CHECK_UNKNOWN;
  memset(&sym_tmp, 0, sizeof(sym_tmp));
  sym_tmp.tag = IXS_SYM;
  sym_tmp.u.name = name;
  if (!ixs_bounds_is_pow2_or_zero(b, &sym_tmp))
    return IXS_CHECK_UNKNOWN;
  return check_equal_result(cmp->u.binary.cmp_op, value == 0);
}

static ixs_check_result bounds_check_and_mask_query(ixs_bounds *b,
                                                    ixs_node *cmp,
                                                    ixs_node *expr,
                                                    int64_t value) {
  const char *name;
  int64_t mask;
  uint64_t mask_bits, value_bits, known;
  struct ixs_node_impl sym_tmp;
  ixs_bitfacts bits;
  bool equal;

  if (!extract_bitop_sym_mask(expr, IXS_AND, &name, &mask))
    return IXS_CHECK_UNKNOWN;

  /* A non-negative constant mask makes the result a finite int64 value whose
   * high bits are all zero.  Negative masks leave untracked high bits live. */
  if (mask < 0)
    return IXS_CHECK_UNKNOWN;

  mask_bits = (uint64_t)mask;
  value_bits = (uint64_t)value;
  if (value < 0 || (value_bits & ~mask_bits) != 0)
    return check_equal_result(cmp->u.binary.cmp_op, false);

  memset(&sym_tmp, 0, sizeof(sym_tmp));
  sym_tmp.tag = IXS_SYM;
  sym_tmp.hash = 0;
  sym_tmp.u.name = name;
  if (!ixs_bounds_get_bitfacts(b, &sym_tmp, &bits))
    return IXS_CHECK_UNKNOWN;

  if ((bits.known_one & mask_bits & ~value_bits) != 0 ||
      (bits.known_zero & mask_bits & value_bits) != 0)
    return check_equal_result(cmp->u.binary.cmp_op, false);

  known = (bits.known_zero | bits.known_one) & mask_bits;
  if (known != mask_bits)
    return IXS_CHECK_UNKNOWN;

  equal = (bits.known_one & mask_bits) == (value_bits & mask_bits);
  return check_equal_result(cmp->u.binary.cmp_op, equal);
}

static ixs_check_result bounds_check_bit_query(ixs_bounds *b, ixs_node *cmp) {
  ixs_node *expr;
  int64_t value;
  ixs_check_result r;

  if (cmp->u.binary.cmp_op != IXS_CMP_EQ && cmp->u.binary.cmp_op != IXS_CMP_NE)
    return IXS_CHECK_UNKNOWN;
  if (!extract_cmp_expr_const(cmp, &expr, &value))
    return IXS_CHECK_UNKNOWN;

  r = bounds_check_pow2_query(b, cmp, expr, value);
  if (r != IXS_CHECK_UNKNOWN)
    return r;

  return bounds_check_and_mask_query(b, cmp, expr, value);
}

static ixs_check_result interval_check_zero(const ixs_interval *iv,
                                            ixs_cmp_op op) {
  int lo_cmp = ixs_rat_cmp(iv->lo_p, iv->lo_q, 0, 1);
  int hi_cmp = ixs_rat_cmp(iv->hi_p, iv->hi_q, 0, 1);
  switch (op) {
  case IXS_CMP_GT:
    if (lo_cmp > 0)
      return IXS_CHECK_TRUE;
    if (hi_cmp <= 0)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_GE:
    if (lo_cmp >= 0)
      return IXS_CHECK_TRUE;
    if (hi_cmp < 0)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_LT:
    if (hi_cmp < 0)
      return IXS_CHECK_TRUE;
    if (lo_cmp >= 0)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_LE:
    if (hi_cmp <= 0)
      return IXS_CHECK_TRUE;
    if (lo_cmp > 0)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_EQ:
    if (lo_cmp == 0 && hi_cmp == 0)
      return IXS_CHECK_TRUE;
    if (lo_cmp > 0 || hi_cmp < 0)
      return IXS_CHECK_FALSE;
    break;
  case IXS_CMP_NE:
    if (lo_cmp > 0 || hi_cmp < 0)
      return IXS_CHECK_TRUE;
    if (lo_cmp == 0 && hi_cmp == 0)
      return IXS_CHECK_FALSE;
    break;
  }
  return IXS_CHECK_UNKNOWN;
}

static ixs_check_result bounds_check_raw(ixs_bounds *b, ixs_node *cmp) {
  ixs_interval iv;
  ixs_check_result mod_result, bit_result;

  if (!cmp)
    return IXS_CHECK_UNKNOWN;

  if (ixs_bounds_has_empty(b))
    return IXS_CHECK_UNKNOWN;

  /* Smart constructors can reduce a comparison to its canonical predicate
   * constant before it reaches the query API. */
  if (cmp->tag == IXS_INT && cmp->u.ival == 1)
    return IXS_CHECK_TRUE;
  if (cmp->tag == IXS_INT && cmp->u.ival == 0)
    return IXS_CHECK_FALSE;

  if (cmp->tag != IXS_CMP || !ixs_node_is_zero(cmp->u.binary.rhs))
    return IXS_CHECK_UNKNOWN;

  mod_result = bounds_check_mod_query(b, cmp);
  if (mod_result != IXS_CHECK_UNKNOWN)
    return mod_result;

  bit_result = bounds_check_bit_query(b, cmp);
  if (bit_result != IXS_CHECK_UNKNOWN)
    return bit_result;

  iv = ixs_bounds_get(b, cmp->u.binary.lhs);
  if (!iv.valid)
    return IXS_CHECK_UNKNOWN;

  return interval_check_zero(&iv, cmp->u.binary.cmp_op);
}

IXS_STATIC ixs_check_result ixs_bounds_check(ixs_bounds *b, ixs_node *cmp) {
  if (cmp && cmp->tag == IXS_CMP &&
      ((!ixs_node_is_known_total(cmp->u.binary.lhs) &&
        ixs_bounds_check_defined(b, cmp->u.binary.lhs) != IXS_CHECK_TRUE) ||
       (!ixs_node_is_known_total(cmp->u.binary.rhs) &&
        ixs_bounds_check_defined(b, cmp->u.binary.rhs) != IXS_CHECK_TRUE)))
    return IXS_CHECK_UNKNOWN;
  return bounds_check_raw(b, cmp);
}

/* Definedness is a proof query, not an evaluator.  Keep its traversal bounds
 * explicit so a hostile or deeply shared DAG cannot consume the C call stack
 * or expand without limit.  Piecewise needs nested fact environments; those
 * calls have a separate, small bound and share the global node budget. */
#define DEFINED_NODE_LIMIT 8192u
#define DEFINED_STACK_LIMIT 1024u
#define DEFINED_MEMO_CAP 16384u
#define DEFINED_PW_DEPTH_LIMIT 32u
#define DEFINED_BOUNDS_DEPTH_LIMIT 64u
#define DEFINED_BOUNDS_VISIT_LIMIT 4096u
#define DEFINED_BOUNDS_MEMO_CAP 8192u
#define DEFINED_BOUNDS_CACHE_MIN_CAP 32u
#define DEFINED_BOUNDS_CACHE_CAP 8192u

typedef struct {
  ixs_ctx *ctx;
  size_t visited;
  bool oom;
  bool limited;
} defined_state;

typedef struct {
  ixs_node *node;
  ixs_check_result result;
} defined_memo_entry;

typedef struct {
  ixs_node *node;
  uint32_t next_child;
  uint32_t nchildren;
  ixs_check_result result;
  bool started;
} defined_frame;

typedef struct {
  ixs_node *node;
  uint32_t next_child;
  uint32_t nchildren;
} defined_depth_frame;

typedef struct {
  ixs_node *node;
  unsigned depth;
} defined_depth_entry;

typedef struct {
  ixs_arena_mark mark;
  ixs_ctx *old_ctx;
  ixs_bounds_cache_entry *old_cache;
  size_t old_cache_cap;
  bool active;
} defined_cache_scope;

static ixs_check_result defined_combine(ixs_check_result lhs,
                                        ixs_check_result rhs) {
  if (lhs == IXS_CHECK_FALSE || rhs == IXS_CHECK_FALSE)
    return IXS_CHECK_FALSE;
  if (lhs == IXS_CHECK_UNKNOWN || rhs == IXS_CHECK_UNKNOWN)
    return IXS_CHECK_UNKNOWN;
  return IXS_CHECK_TRUE;
}

static bool defined_cmp_op_valid(ixs_cmp_op op) {
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

static ixs_cmp_op defined_negate_cmp_op(ixs_cmp_op op) {
  switch (op) {
  case IXS_CMP_GT:
    return IXS_CMP_LE;
  case IXS_CMP_GE:
    return IXS_CMP_LT;
  case IXS_CMP_LT:
    return IXS_CMP_GE;
  case IXS_CMP_LE:
    return IXS_CMP_GT;
  case IXS_CMP_EQ:
    return IXS_CMP_NE;
  case IXS_CMP_NE:
    return IXS_CMP_EQ;
  }
  return op;
}

static int defined_fixed_child_count(ixs_tag tag) {
  switch (tag) {
  case IXS_INT:
  case IXS_RAT:
  case IXS_SYM:
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    return 0;
  case IXS_FLOOR:
  case IXS_CEIL:
  case IXS_NOT:
    return 1;
  case IXS_MOD:
  case IXS_CMP:
    return 2;
  default:
    return -1;
  }
}

/* Keep this local walker independent of the public assert-based accessors.
 * It also gives malformed internal nodes the required conservative result. */
static bool defined_child_count(ixs_node *node, uint32_t *out) {
  int fixed;
  if (!node || !out)
    return false;
  fixed = defined_fixed_child_count(node->tag);
  if (fixed >= 0) {
    *out = (uint32_t)fixed;
    return true;
  }
  switch (node->tag) {
  case IXS_ADD:
    if (!node->u.add.coeff || (node->u.add.nterms > 0 && !node->u.add.terms) ||
        node->u.add.nterms > (UINT32_MAX - 1u) / 2u)
      return false;
    *out = 1u + 2u * node->u.add.nterms;
    return true;
  case IXS_MUL:
    if (!node->u.mul.coeff ||
        (node->u.mul.nfactors > 0 && !node->u.mul.factors) ||
        node->u.mul.nfactors == UINT32_MAX)
      return false;
    *out = 1u + node->u.mul.nfactors;
    return true;
  case IXS_PIECEWISE:
    if ((node->u.pw.ncases > 0 && !node->u.pw.cases) ||
        node->u.pw.ncases > UINT32_MAX / 2u)
      return false;
    *out = 2u * node->u.pw.ncases;
    return true;
  case IXS_AND:
  case IXS_OR:
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
    if (node->u.assoc.nargs < 2 || !node->u.assoc.args)
      return false;
    *out = node->u.assoc.nargs;
    return true;
  default:
    return false;
  }
}

static ixs_node *defined_child_at(ixs_node *node, uint32_t child) {
  switch (node->tag) {
  case IXS_ADD:
    if (child == 0)
      return node->u.add.coeff;
    child--;
    return (child & 1u) == 0u ? node->u.add.terms[child / 2u].coeff
                              : node->u.add.terms[child / 2u].term;
  case IXS_MUL:
    return child == 0 ? node->u.mul.coeff
                      : node->u.mul.factors[child - 1u].base;
  case IXS_FLOOR:
  case IXS_CEIL:
    return node->u.unary.arg;
  case IXS_NOT:
    return node->u.unary_bool.arg;
  case IXS_MOD:
  case IXS_CMP:
    return child == 0 ? node->u.binary.lhs : node->u.binary.rhs;
  case IXS_PIECEWISE:
    return (child & 1u) == 0u ? node->u.pw.cases[child / 2u].value
                              : node->u.pw.cases[child / 2u].cond;
  case IXS_AND:
  case IXS_OR:
  case IXS_MAX:
  case IXS_MIN:
  case IXS_XOR:
    return node->u.assoc.args[child];
  default:
    return NULL;
  }
}

static defined_depth_entry *defined_depth_find(defined_depth_entry *memo,
                                               ixs_node *node) {
  size_t index = ((uintptr_t)node >> 3) & (DEFINED_BOUNDS_MEMO_CAP - 1u);
  size_t probe;
  for (probe = 0; probe < DEFINED_BOUNDS_MEMO_CAP; probe++) {
    defined_depth_entry *entry = &memo[index];
    if (!entry->node || entry->node == node)
      return entry;
    index = (index + 1u) & (DEFINED_BOUNDS_MEMO_CAP - 1u);
  }
  return NULL;
}

static bool defined_bounds_depth_safe(defined_state *state, ixs_bounds *b,
                                      ixs_node *root, bool *shared,
                                      size_t *node_visits) {
  defined_depth_frame stack[DEFINED_BOUNDS_DEPTH_LIMIT];
  ixs_arena_mark mark;
  defined_depth_entry *memo;
  defined_depth_entry *entry;
  size_t depth = 0;
  size_t visited = 1;
  uint32_t nchildren;
  bool safe = false;

  if (shared)
    *shared = false;
  if (node_visits)
    *node_visits = 0;
  if (!root || !defined_child_count(root, &nchildren))
    return false;
  mark = ixs_arena_save(b->scratch);
  memo = ixs_arena_alloc(b->scratch, DEFINED_BOUNDS_MEMO_CAP * sizeof(*memo),
                         sizeof(void *));
  if (!memo) {
    state->oom = true;
    ixs_arena_restore(b->scratch, mark);
    return false;
  }
  memset(memo, 0, DEFINED_BOUNDS_MEMO_CAP * sizeof(*memo));
  entry = defined_depth_find(memo, root);
  entry->node = root;
  entry->depth = 1;
  stack[depth].node = root;
  stack[depth].next_child = 0;
  stack[depth].nchildren = nchildren;
  depth++;

  while (depth > 0) {
    defined_depth_frame *frame = &stack[depth - 1];
    ixs_node *child;
    if (frame->next_child >= frame->nchildren) {
      depth--;
      continue;
    }
    child = defined_child_at(frame->node, frame->next_child++);
    if (!child || depth >= DEFINED_BOUNDS_DEPTH_LIMIT ||
        !defined_child_count(child, &nchildren))
      goto cleanup;
    entry = defined_depth_find(memo, child);
    if (!entry)
      goto cleanup;
    if (entry->node) {
      if (shared)
        *shared = true;
      if (entry->depth >= depth + 1u)
        continue;
    }
    if (++visited > DEFINED_BOUNDS_VISIT_LIMIT)
      goto cleanup;
    entry->node = child;
    entry->depth = (unsigned)depth + 1u;
    stack[depth].node = child;
    stack[depth].next_child = 0;
    stack[depth].nchildren = nchildren;
    depth++;
  }
  safe = true;
  if (node_visits)
    *node_visits = visited;

cleanup:
  ixs_arena_restore(b->scratch, mark);
  return safe;
}

static size_t defined_bounds_cache_capacity(size_t node_visits) {
  size_t cap = DEFINED_BOUNDS_CACHE_MIN_CAP;
  while (cap < DEFINED_BOUNDS_CACHE_CAP && node_visits > cap / 2u)
    cap *= 2u;
  return cap;
}

static bool defined_cache_scope_init(defined_cache_scope *scope,
                                     defined_state *state, ixs_bounds *b,
                                     size_t node_visits) {
  ixs_bounds_cache_entry *cache;
  size_t cache_cap = defined_bounds_cache_capacity(node_visits);
  scope->mark = ixs_arena_save(b->scratch);
  scope->old_ctx = b->ctx;
  scope->old_cache = b->cache;
  scope->old_cache_cap = b->cache_cap;
  scope->active = false;
  cache =
      ixs_arena_alloc(b->scratch, cache_cap * sizeof(*cache), sizeof(void *));
  if (!cache) {
    state->oom = true;
    ixs_arena_restore(b->scratch, scope->mark);
    return false;
  }
  memset(cache, 0, cache_cap * sizeof(*cache));
  b->cache = cache;
  b->cache_cap = cache_cap;
  /* Direct overrides are enough for a proof query. Canonical aliases expand
   * recursively and can revisit a shared DAG before the interval cache sees
   * it, so disable that optional path inside this bounded scope. */
  b->ctx = NULL;
  scope->active = true;
  return true;
}

static void defined_cache_scope_destroy(defined_cache_scope *scope,
                                        ixs_bounds *b) {
  if (!scope->active)
    return;
  b->ctx = scope->old_ctx;
  b->cache = scope->old_cache;
  b->cache_cap = scope->old_cache_cap;
  ixs_arena_restore(b->scratch, scope->mark);
  scope->active = false;
}

static ixs_check_result defined_relation_zero(defined_state *state,
                                              ixs_bounds *b, ixs_node *expr,
                                              ixs_cmp_op op) {
  ixs_interval iv;
  ixs_check_result result;
  ixs_bitfacts bits;
  int64_t modulus, remainder;
  defined_cache_scope cache_scope;
  size_t node_visits;
  bool shared;

  if ((op == IXS_CMP_EQ || op == IXS_CMP_NE) &&
      bounds_is_known_nonzero(b, expr))
    return op == IXS_CMP_NE ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
  if (!defined_bounds_depth_safe(state, b, expr, &shared, &node_visits) ||
      !defined_cache_scope_init(&cache_scope, state, b, node_visits))
    return IXS_CHECK_UNKNOWN;
  iv = ixs_bounds_get(b, expr);
  if (b->oom) {
    state->oom = true;
    result = IXS_CHECK_UNKNOWN;
    goto cleanup;
  }
  if (iv.valid) {
    result = interval_check_zero(&iv, op);
    if (result != IXS_CHECK_UNKNOWN)
      goto cleanup;
  }

  result = IXS_CHECK_UNKNOWN;
  if (op != IXS_CMP_EQ && op != IXS_CMP_NE)
    goto cleanup;
  if (!shared && ixs_bounds_get_bitfacts(b, expr, &bits) &&
      bits.known_one != 0) {
    result = op == IXS_CMP_NE ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
    goto cleanup;
  }
  if (b->oom) {
    state->oom = true;
    goto cleanup;
  }
  if (expr->tag == IXS_SYM &&
      ixs_bounds_get_modrem(b, expr->u.name, &modulus, &remainder) &&
      remainder != 0) {
    (void)modulus;
    result = op == IXS_CMP_NE ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
  }

cleanup:
  defined_cache_scope_destroy(&cache_scope, b);
  return result;
}

static ixs_check_result defined_condition_truth(defined_state *state,
                                                ixs_bounds *b, ixs_node *cond) {
  ixs_check_result result;
  defined_cache_scope cache_scope;
  size_t node_visits;
  bool shared;
  if (ixs_node_is_known_false(cond))
    return IXS_CHECK_FALSE;
  if (ixs_node_is_known_true(cond))
    return IXS_CHECK_TRUE;
  if (cond->tag == IXS_CMP) {
    if (ixs_node_is_zero(cond->u.binary.rhs)) {
      result = defined_relation_zero(state, b, cond->u.binary.lhs,
                                     cond->u.binary.cmp_op);
      if (result != IXS_CHECK_UNKNOWN || state->oom)
        return result;
    }
    if (!defined_bounds_depth_safe(state, b, cond, &shared, &node_visits))
      return IXS_CHECK_UNKNOWN;
    if (shared) {
      if (!ixs_node_is_zero(cond->u.binary.rhs))
        return IXS_CHECK_UNKNOWN;
      return defined_relation_zero(state, b, cond->u.binary.lhs,
                                   cond->u.binary.cmp_op);
    }
    if (!defined_cache_scope_init(&cache_scope, state, b, node_visits))
      return IXS_CHECK_UNKNOWN;
    result = bounds_check_raw(b, cond);
    if (b->oom)
      state->oom = true;
    defined_cache_scope_destroy(&cache_scope, b);
    return result;
  }
  return defined_relation_zero(state, b, cond, IXS_CMP_NE);
}

static ixs_node *defined_condition_assumption(defined_state *state,
                                              ixs_node *cond, bool value,
                                              struct ixs_node_impl *storage) {
  memset(storage, 0, sizeof(*storage));
  storage->tag = IXS_CMP;
  storage->u.binary.rhs = state->ctx->node_zero;
  if (cond->tag == IXS_CMP) {
    storage->u.binary.lhs = cond->u.binary.lhs;
    storage->u.binary.rhs = cond->u.binary.rhs;
    storage->u.binary.cmp_op =
        value ? cond->u.binary.cmp_op
              : defined_negate_cmp_op(cond->u.binary.cmp_op);
  } else {
    storage->u.binary.lhs = cond;
    storage->u.binary.cmp_op = value ? IXS_CMP_NE : IXS_CMP_EQ;
  }
  return storage;
}

static defined_memo_entry *defined_memo_find(defined_memo_entry *memo,
                                             ixs_node *node) {
  size_t index = ((uintptr_t)node >> 3) & (DEFINED_MEMO_CAP - 1u);
  size_t probe;
  for (probe = 0; probe < DEFINED_MEMO_CAP; probe++) {
    defined_memo_entry *entry = &memo[index];
    if (!entry->node || entry->node == node)
      return entry;
    index = (index + 1u) & (DEFINED_MEMO_CAP - 1u);
  }
  return NULL;
}

static void defined_frame_init(defined_frame *frame, ixs_node *node) {
  frame->node = node;
  frame->next_child = 0;
  frame->nchildren = 0;
  frame->result = IXS_CHECK_TRUE;
  frame->started = false;
}

static ixs_check_result defined_eval(defined_state *state, ixs_bounds *b,
                                     ixs_node *root, unsigned pw_depth);

static void defined_partition_add(unsigned *partitions,
                                  ixs_check_result result) {
  if (result == IXS_CHECK_TRUE)
    *partitions |= 1u;
  else if (result == IXS_CHECK_FALSE)
    *partitions |= 2u;
  else
    *partitions |= 4u;
}

static ixs_check_result defined_partition_result(unsigned partitions) {
  if (partitions == 1u)
    return IXS_CHECK_TRUE;
  if (partitions == 2u)
    return IXS_CHECK_FALSE;
  return IXS_CHECK_UNKNOWN;
}

typedef enum {
  DEFINED_PW_NEXT,
  DEFINED_PW_STOP,
  DEFINED_PW_FAILED
} defined_pw_step;

static bool defined_piecewise_active(defined_state *state,
                                     ixs_bounds *remaining, ixs_node *cond,
                                     ixs_node *value, unsigned pw_depth,
                                     unsigned *partitions) {
  ixs_arena_mark mark = ixs_arena_save(remaining->scratch);
  ixs_bounds active;
  struct ixs_node_impl assumption;
  if (!ixs_bounds_fork(&active, remaining)) {
    state->oom = true;
    ixs_arena_restore(remaining->scratch, mark);
    return false;
  }
  if (!ixs_bounds_add_assumption(
          &active,
          defined_condition_assumption(state, cond, true, &assumption))) {
    state->oom = true;
    ixs_arena_restore(remaining->scratch, mark);
    return false;
  }
  if (!ixs_bounds_has_empty(&active)) {
    ixs_check_result result = defined_eval(state, &active, value, pw_depth);
    defined_partition_add(partitions, result);
  }
  ixs_arena_restore(remaining->scratch, mark);
  return !state->oom && !state->limited;
}

static defined_pw_step defined_piecewise_case(defined_state *state,
                                              ixs_bounds *remaining,
                                              const ixs_pwcase *pwcase,
                                              unsigned pw_depth,
                                              unsigned *partitions) {
  ixs_node *cond = pwcase->cond;
  ixs_check_result cond_defined =
      defined_eval(state, remaining, cond, pw_depth);
  ixs_check_result truth;
  struct ixs_node_impl assumption;

  if (state->oom || state->limited)
    return DEFINED_PW_FAILED;
  if (cond_defined != IXS_CHECK_TRUE) {
    defined_partition_add(partitions, cond_defined);
    return DEFINED_PW_STOP;
  }

  truth = defined_condition_truth(state, remaining, cond);
  if (state->oom)
    return DEFINED_PW_FAILED;
  if (truth == IXS_CHECK_FALSE)
    return DEFINED_PW_NEXT;
  if (!defined_bounds_depth_safe(state, remaining, cond, NULL, NULL)) {
    defined_partition_add(partitions, IXS_CHECK_UNKNOWN);
    return DEFINED_PW_STOP;
  }
  if (!defined_piecewise_active(state, remaining, cond, pwcase->value, pw_depth,
                                partitions))
    return DEFINED_PW_FAILED;
  if (truth == IXS_CHECK_TRUE)
    return DEFINED_PW_STOP;

  if (!ixs_bounds_add_assumption(
          remaining,
          defined_condition_assumption(state, cond, false, &assumption))) {
    state->oom = true;
    return DEFINED_PW_FAILED;
  }
  return DEFINED_PW_NEXT;
}

static ixs_check_result defined_piecewise(defined_state *state, ixs_bounds *b,
                                          ixs_node *expr, unsigned pw_depth) {
  ixs_arena_mark outer_mark;
  ixs_bounds remaining;
  unsigned partitions = 0;
  uint32_t i;
  bool stopped = false;

  if (pw_depth > DEFINED_PW_DEPTH_LIMIT)
    return IXS_CHECK_UNKNOWN;
  if ((expr->u.pw.ncases > 0 && !expr->u.pw.cases) ||
      expr->u.pw.ncases > UINT32_MAX / 2u)
    return IXS_CHECK_UNKNOWN;
  if (expr->u.pw.ncases == 0)
    return IXS_CHECK_FALSE;

  outer_mark = ixs_arena_save(b->scratch);
  if (!ixs_bounds_fork(&remaining, b)) {
    state->oom = true;
    ixs_arena_restore(b->scratch, outer_mark);
    return IXS_CHECK_UNKNOWN;
  }

  for (i = 0; i < expr->u.pw.ncases; i++) {
    defined_pw_step step;

    if (remaining.oom) {
      state->oom = true;
      break;
    }
    if (ixs_bounds_has_empty(&remaining)) {
      stopped = true;
      break;
    }
    step = defined_piecewise_case(state, &remaining, &expr->u.pw.cases[i],
                                  pw_depth, &partitions);
    if (step == DEFINED_PW_STOP) {
      stopped = true;
      break;
    }
    if (step == DEFINED_PW_FAILED)
      break;
  }

  if (!state->oom && !state->limited && !stopped && !remaining.oom &&
      !ixs_bounds_has_empty(&remaining))
    defined_partition_add(&partitions, IXS_CHECK_FALSE);
  if (remaining.oom)
    state->oom = true;

  ixs_arena_restore(b->scratch, outer_mark);
  if (state->oom || state->limited)
    return IXS_CHECK_UNKNOWN;
  return defined_partition_result(partitions);
}

static ixs_check_result defined_finalize_node(defined_state *state,
                                              ixs_bounds *b, ixs_node *node,
                                              ixs_check_result result) {
  uint32_t i;
  if (node->tag == IXS_MUL) {
    for (i = 0; i < node->u.mul.nfactors; i++) {
      ixs_check_result guard;
      if (node->u.mul.factors[i].exp == 0)
        result = defined_combine(result, IXS_CHECK_UNKNOWN);
      if (node->u.mul.factors[i].exp >= 0)
        continue;
      guard = defined_relation_zero(state, b, node->u.mul.factors[i].base,
                                    IXS_CMP_NE);
      result = defined_combine(result, guard);
    }
  } else if (node->tag == IXS_MOD) {
    ixs_check_result guard =
        defined_relation_zero(state, b, node->u.binary.rhs, IXS_CMP_GT);
    result = defined_combine(result, guard);
  } else if (node->tag == IXS_XOR || node->tag == IXS_AND ||
             node->tag == IXS_OR) {
    for (i = 0; i < node->u.assoc.nargs; i++) {
      ixs_check_result guard =
          ixs_bounds_check_integer_valued(b, node->u.assoc.args[i]);
      result = defined_combine(result, guard);
    }
  }
  return result;
}

static bool defined_complete_frame(defined_state *state,
                                   defined_memo_entry *memo,
                                   defined_frame *stack, size_t *depth,
                                   ixs_check_result result,
                                   ixs_check_result *answer) {
  defined_frame *frame = &stack[*depth - 1u];
  defined_memo_entry *entry = defined_memo_find(memo, frame->node);
  if (!entry) {
    state->limited = true;
    result = IXS_CHECK_UNKNOWN;
  } else {
    entry->node = frame->node;
    entry->result = result;
  }
  (*depth)--;
  if (*depth == 0) {
    *answer = result;
    return true;
  }
  frame = &stack[*depth - 1u];
  frame->result = defined_combine(frame->result, result);
  frame->next_child++;
  return false;
}

static void defined_start_frame(defined_state *state, ixs_bounds *b,
                                defined_frame *frame, unsigned pw_depth,
                                ixs_check_result *direct, bool *has_direct) {
  ixs_node *node = frame->node;
  *direct = IXS_CHECK_UNKNOWN;
  *has_direct = false;

  if (!node || !ixs_ctx_owns_node(state->ctx, node) ||
      ixs_node_is_sentinel(node)) {
    *has_direct = true;
    return;
  }
  if (++state->visited > DEFINED_NODE_LIMIT) {
    state->limited = true;
    return;
  }

  /* A range constrains a node only where that node is defined. It cannot skip
   * the structural walk or discharge an operation's domain guards. */

  switch (node->tag) {
  case IXS_INT:
    *direct = IXS_CHECK_TRUE;
    *has_direct = true;
    return;
  case IXS_RAT:
    *direct = node->u.rat.q > 0 ? IXS_CHECK_TRUE : IXS_CHECK_UNKNOWN;
    *has_direct = true;
    return;
  case IXS_SYM:
    *direct = node->u.name ? IXS_CHECK_TRUE : IXS_CHECK_UNKNOWN;
    *has_direct = true;
    return;
  case IXS_ERROR:
  case IXS_PARSE_ERROR:
    *has_direct = true;
    return;
  case IXS_PIECEWISE:
    *direct = defined_piecewise(state, b, node, pw_depth + 1u);
    *has_direct = true;
    return;
  case IXS_CMP:
    if (!defined_cmp_op_valid(node->u.binary.cmp_op)) {
      *has_direct = true;
      return;
    }
    break;
  default:
    break;
  }
  if (!defined_child_count(node, &frame->nchildren))
    *has_direct = true;
}

static bool defined_process_child(defined_state *state,
                                  defined_memo_entry *memo,
                                  defined_frame *stack, size_t *depth) {
  defined_frame *frame = &stack[*depth - 1u];
  ixs_node *child;
  defined_memo_entry *entry;
  if (frame->next_child >= frame->nchildren)
    return false;

  child = defined_child_at(frame->node, frame->next_child);
  if (!child) {
    frame->result = defined_combine(frame->result, IXS_CHECK_UNKNOWN);
    frame->next_child++;
    return true;
  }
  entry = defined_memo_find(memo, child);
  if (entry && entry->node) {
    frame->result = defined_combine(frame->result, entry->result);
    frame->next_child++;
    return true;
  }
  if (*depth >= DEFINED_STACK_LIMIT) {
    state->limited = true;
    return true;
  }
  defined_frame_init(&stack[(*depth)++], child);
  return true;
}

static ixs_check_result defined_eval(defined_state *state, ixs_bounds *b,
                                     ixs_node *root, unsigned pw_depth) {
  ixs_arena_mark mark;
  defined_memo_entry *memo;
  defined_frame *stack;
  size_t depth = 0;
  ixs_check_result answer = IXS_CHECK_UNKNOWN;

  if (!root || state->oom || state->limited)
    return IXS_CHECK_UNKNOWN;
  mark = ixs_arena_save(b->scratch);
  memo = ixs_arena_alloc(b->scratch, DEFINED_MEMO_CAP * sizeof(*memo),
                         sizeof(void *));
  stack = ixs_arena_alloc(b->scratch, DEFINED_STACK_LIMIT * sizeof(*stack),
                          sizeof(void *));
  if (!memo || !stack) {
    state->oom = true;
    ixs_arena_restore(b->scratch, mark);
    return IXS_CHECK_UNKNOWN;
  }
  memset(memo, 0, DEFINED_MEMO_CAP * sizeof(*memo));
  defined_frame_init(&stack[depth++], root);

  while (depth > 0 && !state->oom && !state->limited) {
    defined_frame *frame = &stack[depth - 1u];
    ixs_node *node = frame->node;

    if (!frame->started) {
      ixs_check_result direct = IXS_CHECK_UNKNOWN;
      bool has_direct = false;
      defined_start_frame(state, b, frame, pw_depth, &direct, &has_direct);
      if (state->limited)
        break;
      if (has_direct) {
        if (defined_complete_frame(state, memo, stack, &depth, direct, &answer))
          break;
        continue;
      }
      frame->started = true;
    }

    if (defined_process_child(state, memo, stack, &depth))
      continue;

    frame->result = defined_finalize_node(state, b, node, frame->result);
    if (defined_complete_frame(state, memo, stack, &depth, frame->result,
                               &answer))
      break;
  }

  ixs_arena_restore(b->scratch, mark);
  if (state->oom || state->limited)
    return IXS_CHECK_UNKNOWN;
  return answer;
}

static ixs_check_result bounds_check_defined_status(ixs_bounds *b,
                                                    ixs_node *expr, bool *oom) {
  defined_state state;
  ixs_check_result result;
  if (oom)
    *oom = false;
  if (!b || !b->ctx || !b->scratch || !expr || b->oom ||
      ixs_bounds_has_empty(b))
    return IXS_CHECK_UNKNOWN;
  state.ctx = b->ctx;
  state.visited = 0;
  state.oom = false;
  state.limited = false;
  result = defined_eval(&state, b, expr, 0);
  if (oom)
    *oom = state.oom || b->oom;
  if (state.oom || state.limited || b->oom)
    return IXS_CHECK_UNKNOWN;
  return result;
}

IXS_STATIC ixs_check_result ixs_bounds_check_defined(ixs_bounds *b,
                                                     ixs_node *expr) {
  return bounds_check_defined_status(b, expr, NULL);
}

static ixs_bounds_build_status assumption_invalid(ixs_bounds *b,
                                                  const char *message) {
  if (b && b->ctx)
    ixs_ctx_push_error(b->ctx, "assumptions: %s", message);
  return IXS_BOUNDS_BUILD_INVALID;
}

static bool assumption_cmp_op_valid(ixs_cmp_op op) {
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

static void bounds_ingest_validated_leaf(ixs_bounds *b, ixs_node *pred,
                                         bool ingest) {
  if (!ingest)
    return;
  if (pred == b->ctx->node_false) {
    bounds_mark_contradiction(b);
    bounds_cache_clear(b);
    return;
  }
  (void)ixs_bounds_add_assumption(b, pred);
}

static ixs_bounds_build_status
bounds_process_predicate(ixs_bounds *b, ixs_node *pred, bool ingest) {
  ixs_node *stack[ASSUMPTION_NODE_LIMIT];
  size_t nstack = 0;
  size_t visited = 0;

  if (!pred)
    return assumption_invalid(b, "NULL predicate");
  stack[nstack++] = pred;

  while (nstack > 0) {
    ixs_node *cur = stack[--nstack];
    uint32_t i;

    if (++visited > ASSUMPTION_NODE_LIMIT)
      return assumption_invalid(b, "predicate node limit (1024) exceeded");
    if (!cur)
      return assumption_invalid(b, "NULL predicate child");
    if (!ixs_ctx_owns_node(b->ctx, cur))
      return assumption_invalid(b, "predicate belongs to a different context");
    if (ixs_node_is_sentinel(cur))
      return assumption_invalid(b, "sentinel predicates are not accepted");

    if (cur == b->ctx->node_true)
      continue;
    if (cur == b->ctx->node_false) {
      bounds_ingest_validated_leaf(b, cur, ingest);
      continue;
    }

    if (cur->tag == IXS_CMP) {
      ixs_node *lhs = cur->u.binary.lhs;
      ixs_node *rhs = cur->u.binary.rhs;
      if (!lhs || !rhs || !assumption_cmp_op_valid(cur->u.binary.cmp_op))
        return assumption_invalid(b, "malformed CMP predicate");
      if (!ixs_ctx_owns_node(b->ctx, lhs) || !ixs_ctx_owns_node(b->ctx, rhs))
        return assumption_invalid(b,
                                  "CMP child belongs to a different context");
      if (ixs_node_is_sentinel(lhs) || ixs_node_is_sentinel(rhs))
        return assumption_invalid(b, "sentinel CMP children are not accepted");
      bounds_ingest_validated_leaf(b, cur, ingest);
      if (b->oom)
        return IXS_BOUNDS_BUILD_OOM;
      continue;
    }

    if (cur->tag == IXS_AND) {
      if (cur->u.assoc.nargs < 2 || !cur->u.assoc.args)
        return assumption_invalid(b, "malformed AND predicate");
      if ((size_t)cur->u.assoc.nargs > ASSUMPTION_NODE_LIMIT - nstack)
        return assumption_invalid(b, "predicate node limit (1024) exceeded");
      for (i = cur->u.assoc.nargs; i > 0; i--)
        stack[nstack++] = cur->u.assoc.args[i - 1];
      continue;
    }

    if (cur->tag == IXS_OR)
      return assumption_invalid(b, "OR predicates are not supported");
    if (cur->tag == IXS_NOT)
      return assumption_invalid(b, "NOT predicates are not supported");
    return assumption_invalid(
        b, "expected a CMP, AND, or boolean constant predicate");
  }

  return IXS_BOUNDS_BUILD_OK;
}

static ixs_bounds_build_status bounds_validate_predicate(ixs_bounds *b,
                                                         ixs_node *pred) {
  return bounds_process_predicate(b, pred, false);
}

static ixs_bounds_build_status bounds_ingest_predicate(ixs_bounds *b,
                                                       ixs_node *pred) {
  return bounds_process_predicate(b, pred, true);
}

static ixs_bounds_build_status
bounds_validate_predicates(ixs_bounds *b, ixs_node *const *predicates,
                           size_t n_predicates) {
  size_t i;
  ixs_bounds_build_status status;

  if (n_predicates > 0 && !predicates)
    return assumption_invalid(b, "NULL array with nonzero count");
  for (i = 0; i < n_predicates; i++) {
    status = bounds_validate_predicate(b, predicates[i]);
    if (status != IXS_BOUNDS_BUILD_OK)
      return status;
  }
  return IXS_BOUNDS_BUILD_OK;
}

static ixs_bounds_build_status
bounds_ingest_predicates(ixs_bounds *b, ixs_node *const *predicates,
                         size_t n_predicates) {
  size_t i;
  ixs_bounds_build_status status;

  if (n_predicates > 0 && !predicates)
    return assumption_invalid(b, "NULL array with nonzero count");
  for (i = 0; i < n_predicates; i++) {
    status = bounds_ingest_predicate(b, predicates[i]);
    if (status != IXS_BOUNDS_BUILD_OK)
      return status;
  }
  return IXS_BOUNDS_BUILD_OK;
}

IXS_STATIC ixs_bounds_build_status
ixs_bounds_build_ctx(ixs_bounds *b, ixs_ctx *ctx, ixs_arena *scratch,
                     ixs_node *const *assumptions, size_t n_assumptions) {
  if (n_assumptions > 0 && !assumptions) {
    ixs_ctx_push_error(ctx, "assumptions: NULL array with nonzero count");
    return IXS_BOUNDS_BUILD_INVALID;
  }
  if (!ixs_bounds_init_ctx(b, ctx, scratch))
    return IXS_BOUNDS_BUILD_OOM;
  return bounds_ingest_predicates(b, assumptions, n_assumptions);
}

static bool range_result_to_interval(const ixs_range_result *range,
                                     ixs_interval *out) {
  ixs_interval iv;
  if (!range || !out)
    return false;
  iv.valid = true;
  iv.lo_inf = false;
  iv.hi_inf = false;
  if (range->has_lower) {
    if (!ixs_rat_normalize(range->lower_p, range->lower_q, &iv.lo_p, &iv.lo_q))
      return false;
  } else {
    ixs_interval_set_lo_neg_inf(&iv);
  }
  if (range->has_upper) {
    if (!ixs_rat_normalize(range->upper_p, range->upper_q, &iv.hi_p, &iv.hi_q))
      return false;
  } else {
    ixs_interval_set_hi_pos_inf(&iv);
  }
  if (ixs_interval_is_empty(iv))
    return false;
  *out = iv;
  return true;
}

static void interval_to_range_result(ixs_interval iv, ixs_range_result *out) {
  out->has_lower = !iv.lo_inf;
  out->has_upper = !iv.hi_inf;
  out->lower_p = iv.lo_inf ? 0 : iv.lo_p;
  out->lower_q = iv.lo_inf ? 1 : iv.lo_q;
  out->upper_p = iv.hi_inf ? 0 : iv.hi_p;
  out->upper_q = iv.hi_inf ? 1 : iv.hi_q;
}

static bool facts_bind(ixs_facts *facts, ixs_session_binding *binding,
                       ixs_ctx **ctx) {
  if (!facts || !facts->impl || !facts->ctx || !binding || !ctx ||
      facts->epoch == 0 || facts->impl->ctx != facts->ctx ||
      facts->impl->epoch != facts->epoch)
    return false;
  *ctx = ixs_session_bind_impl(binding, facts->impl);
  facts->bounds.ctx = *ctx;
  facts->bounds.scratch = &(*ctx)->scratch;
  return true;
}

static bool facts_ready(const ixs_facts *facts) {
  return facts && facts->usable && !facts->bounds.oom;
}

static void facts_poison(ixs_facts *facts) {
  if (facts)
    facts->usable = false;
}

static void facts_commit(ixs_facts *facts, ixs_bounds *candidate) {
  candidate->cache = facts->bounds.cache;
  candidate->cache_cap = facts->bounds.cache_cap;
  bounds_cache_clear(candidate);
  facts->bounds = *candidate;
}

static bool facts_node_ok(ixs_ctx *ctx, ixs_node *node) {
  return node && !ixs_node_is_sentinel(node) && ixs_ctx_owns_node(ctx, node);
}

static bool facts_query_node_ok(ixs_ctx *ctx, ixs_node *node,
                                const char *query) {
  if (!node) {
    ixs_ctx_push_error(ctx, "%s: NULL expression", query);
    return false;
  }
  if (ixs_node_is_sentinel(node)) {
    ixs_ctx_push_error(ctx, "%s: sentinel expression is not accepted", query);
    return false;
  }
  if (!ixs_ctx_owns_node(ctx, node)) {
    ixs_ctx_push_error(ctx, "%s: expression belongs to a different context",
                       query);
    return false;
  }
  return true;
}

static void bounds_add_var_fact(ixs_bounds *dst, const ixs_var_bound *src) {
  ixs_var_bound *v = find_var(dst, src->name);
  ixs_interval old;
  bool changed;
  bounds_cache_clear(dst);
  if (!v) {
    v = get_or_create_var(dst, src->name);
    if (!v)
      return;
    *v = *src;
    if (src->modulus > 0)
      dst->has_modrem = true;
    refine_var_bit_consistency(dst, v);
    bounds_propagate_difference_bounds(dst, src->name, NULL);
    return;
  }

  old = v->iv;
  v->iv = iv_intersect(v->iv, src->iv);
  changed = !bounds_intervals_equal(old, v->iv);
  if (changed)
    bounds_mark_semantic_changed(dst);
  if (src->modulus > 0)
    apply_modrem(dst, src->name, src->modulus, src->remainder);
  apply_var_known_bits(dst, v, src->bits.known_zero, src->bits.known_one);
  apply_pow2_fact(dst, v, src->bits.pow2);
  if (changed)
    bounds_propagate_difference_bounds(dst, src->name, NULL);
}

static void bounds_add_var_interval(ixs_bounds *dst, const char *name,
                                    ixs_interval iv) {
  ixs_var_bound fact;
  if (!iv.valid)
    return;
  memset(&fact, 0, sizeof(fact));
  fact.name = name;
  fact.iv = iv;
  bounds_add_var_fact(dst, &fact);
}

static bool bounds_extract_integer_affine(ixs_node *expr, const char **name,
                                          int64_t *scale, int64_t *offset) {
  int64_t p, q;
  if (!expr || !name || !scale || !offset)
    return false;
  if (expr->tag == IXS_SYM) {
    *name = expr->u.name;
    *scale = 1;
    *offset = 0;
    return true;
  }
  if (expr->tag == IXS_MUL && expr->u.mul.nfactors == 1 &&
      expr->u.mul.factors[0].exp == 1 &&
      expr->u.mul.factors[0].base->tag == IXS_SYM) {
    ixs_node_get_rat(expr->u.mul.coeff, &p, &q);
    if (q != 1 || p == 0)
      return false;
    *name = expr->u.mul.factors[0].base->u.name;
    *scale = p;
    *offset = 0;
    return true;
  }
  if (expr->tag == IXS_ADD && expr->u.add.nterms == 1 &&
      expr->u.add.terms[0].term->tag == IXS_SYM) {
    ixs_node_get_rat(expr->u.add.coeff, offset, &q);
    if (q != 1)
      return false;
    ixs_node_get_rat(expr->u.add.terms[0].coeff, scale, &q);
    if (q != 1 || *scale == 0)
      return false;
    *name = expr->u.add.terms[0].term->u.name;
    return true;
  }
  return false;
}

static bool bounds_interval_contains_rational(ixs_interval iv, int64_t p,
                                              int64_t q) {
  if (!iv.valid)
    return true;
  if (!iv.lo_inf && ixs_rat_cmp(p, q, iv.lo_p, iv.lo_q) < 0)
    return false;
  if (!iv.hi_inf && ixs_rat_cmp(p, q, iv.hi_p, iv.hi_q) > 0)
    return false;
  return true;
}

static void bounds_transfer_inverse_congruence(ixs_bounds *dst,
                                               const char *name, int64_t scale,
                                               int64_t offset, int64_t modulus,
                                               int64_t residue) {
  uint64_t m, a, rhs, g, reduced, inverse, result;
  if (modulus <= 0)
    return;
  m = (uint64_t)modulus;
  a = bounds_normalize_residue(scale, m);
  rhs = bounds_sub_mod(bounds_normalize_residue(residue, m),
                       bounds_normalize_residue(offset, m), m);
  g = bounds_u64_gcd(a, m);
  if (rhs % g != 0) {
    bounds_mark_contradiction(dst);
    return;
  }
  reduced = m / g;
  if (reduced == 1u)
    return;
  if (!bounds_mod_inverse((a / g) % reduced, reduced, &inverse)) {
    bounds_mark_contradiction(dst);
    return;
  }
  result = bounds_mul_mod((rhs / g) % reduced, inverse, reduced);
  apply_modrem(dst, name, (int64_t)reduced, (int64_t)result);
}

static void bounds_transfer_affine_range(ixs_bounds *dst, const char *name,
                                         int64_t scale, int64_t offset,
                                         ixs_interval iv) {
  int64_t neg_offset, denominator;
  ixs_interval shifted, inverse;
  if (!iv.valid || !ixs_safe_neg(offset, &neg_offset))
    return;
  shifted = iv_add(iv, ixs_interval_exact(neg_offset, 1));
  if (scale > 0) {
    denominator = scale;
    inverse = iv_mul_const(shifted, 1, denominator);
  } else {
    if (!ixs_safe_neg(scale, &denominator))
      return;
    inverse = iv_mul_const(shifted, -1, denominator);
  }
  if (inverse.valid)
    bounds_add_var_interval(dst, name, inverse);
}

static void bounds_check_constant_var_fact(ixs_bounds *dst,
                                           const ixs_var_bound *src, int64_t p,
                                           int64_t q) {
  uint64_t value;
  if (!bounds_interval_contains_rational(src->iv, p, q))
    bounds_mark_contradiction(dst);
  if (src->modulus > 0 &&
      (q != 1 || bounds_normalize_residue(p, (uint64_t)src->modulus) !=
                     (uint64_t)src->remainder))
    bounds_mark_contradiction(dst);
  if (src->bits.known_zero != 0 || src->bits.known_one != 0) {
    if (q != 1) {
      bounds_mark_contradiction(dst);
    } else {
      value = (uint64_t)p;
      if ((src->bits.known_zero & value) != 0 ||
          (src->bits.known_one & ~value) != 0)
        bounds_mark_contradiction(dst);
    }
  }
  if (src->bits.pow2 != IXS_POW2_UNKNOWN) {
    if (q != 1 ||
        (src->bits.pow2 == IXS_POW2_POSITIVE && !int64_is_positive_pow2(p)) ||
        (src->bits.pow2 == IXS_POW2_OR_ZERO && p != 0 &&
         !int64_is_positive_pow2(p)))
      bounds_mark_contradiction(dst);
  }
}

static void bounds_transfer_range(ixs_bounds *dst, ixs_node *replacement,
                                  ixs_interval iv) {
  const char *name;
  int64_t scale, offset, p, q;
  if (!iv.valid)
    return;
  if (ixs_node_is_const(replacement)) {
    ixs_node_get_rat(replacement, &p, &q);
    if (!bounds_interval_contains_rational(iv, p, q))
      bounds_mark_contradiction(dst);
    return;
  }
  if (bounds_extract_integer_affine(replacement, &name, &scale, &offset))
    bounds_transfer_affine_range(dst, name, scale, offset, iv);
}

static void bounds_transfer_var_fact(ixs_bounds *dst, const ixs_var_bound *src,
                                     ixs_node *replacement) {
  const char *name;
  int64_t scale, offset, p, q;
  unsigned low_bits = 0;
  uint64_t known, modulus, mask, residue;
  ixs_var_bound renamed;
  ixs_var_bound *var;

  if (replacement->tag == IXS_SYM) {
    renamed = *src;
    renamed.name = replacement->u.name;
    bounds_add_var_fact(dst, &renamed);
    return;
  }
  if (ixs_node_is_const(replacement)) {
    ixs_node_get_rat(replacement, &p, &q);
    bounds_check_constant_var_fact(dst, src, p, q);
    return;
  }
  if (!bounds_extract_integer_affine(replacement, &name, &scale, &offset))
    return;

  bounds_transfer_affine_range(dst, name, scale, offset, src->iv);
  if (src->modulus > 0)
    bounds_transfer_inverse_congruence(dst, name, scale, offset, src->modulus,
                                       src->remainder);

  known = src->bits.known_zero | src->bits.known_one;
  while (low_bits < 62u && (known & (UINT64_C(1) << low_bits)) != 0)
    low_bits++;
  if (low_bits != 0) {
    modulus = UINT64_C(1) << low_bits;
    mask = modulus - 1u;
    residue = src->bits.known_one & mask;
    bounds_transfer_inverse_congruence(dst, name, scale, offset,
                                       (int64_t)modulus, (int64_t)residue);
  }

  if (offset == 0 && int64_is_positive_pow2(scale) &&
      src->bits.pow2 != IXS_POW2_UNKNOWN) {
    var = get_or_create_var(dst, name);
    apply_pow2_fact(dst, var, src->bits.pow2);
  }
}

/* Build a fixed-capacity table at no more than half load. Initialization is
 * O(count); predicate processing never grows the table. */
static bool facts_predicate_set_init(ixs_arena *arena, size_t count,
                                     ixs_node ***slots, size_t *capacity) {
  size_t needed;
  *slots = NULL;
  *capacity = 0;
  if (count < 2)
    return true;
  if (count > SIZE_MAX / 2u)
    return false;
  needed = count * 2u;
  *capacity = 2u;
  while (*capacity < needed) {
    if (*capacity > SIZE_MAX / 2u)
      return false;
    *capacity *= 2u;
  }
  if (*capacity > SIZE_MAX / sizeof(**slots))
    return false;
  *slots = ixs_arena_alloc(arena, *capacity * sizeof(**slots), sizeof(void *));
  if (!*slots)
    return false;
  memset(*slots, 0, *capacity * sizeof(**slots));
  return true;
}

/* Expected O(1) at the fixed half-load bound; collisions probe linearly. */
static bool facts_predicate_seen_or_insert(ixs_node **slots, size_t capacity,
                                           ixs_node *predicate) {
  size_t index = predicate->hash & (capacity - 1u);
  while (slots[index] && slots[index] != predicate)
    index = (index + 1u) & (capacity - 1u);
  if (slots[index])
    return true;
  slots[index] = predicate;
  return false;
}

typedef struct {
  const char *name;
  size_t first_occurrence;
} facts_symbol_slot;

typedef struct {
  const char *name;
  size_t predicate;
  size_t next_for_predicate;
  size_t next_for_symbol;
} facts_symbol_occurrence;

typedef struct {
  ixs_arena arena;
  size_t n_predicates;
  bool *active;
  bool *queued;
  size_t *queue;
  size_t queue_head;
  size_t queue_tail;
  size_t queue_count;
  size_t *predicate_occurrences;
  facts_symbol_slot *symbols;
  size_t symbol_capacity;
  size_t symbol_count;
  facts_symbol_occurrence *occurrences;
  size_t occurrence_capacity;
  size_t occurrence_count;
  ixs_node **seen;
  size_t seen_capacity;
} facts_worklist;

typedef struct {
  ixs_node **slots;
  size_t capacity;
  size_t count;
} facts_node_set;

typedef union {
  void *align;
  unsigned char bytes[IXS_ARENA_DEFAULT_SIZE];
} facts_work_storage;

static bool facts_worklist_alloc_arrays(facts_worklist *work) {
  size_t count = work->n_predicates;
  size_t i;
  if (count > SIZE_MAX / sizeof(*work->queue) ||
      count > SIZE_MAX / sizeof(*work->predicate_occurrences))
    return false;
  work->active = ixs_arena_alloc(&work->arena, count * sizeof(*work->active),
                                 sizeof(void *));
  work->queued = ixs_arena_alloc(&work->arena, count * sizeof(*work->queued),
                                 sizeof(void *));
  work->queue = ixs_arena_alloc(&work->arena, count * sizeof(*work->queue),
                                sizeof(void *));
  work->predicate_occurrences = ixs_arena_alloc(
      &work->arena, count * sizeof(*work->predicate_occurrences),
      sizeof(void *));
  if (!work->active || !work->queued || !work->queue ||
      !work->predicate_occurrences)
    return false;
  memset(work->active, 0, count * sizeof(*work->active));
  memset(work->queued, 0, count * sizeof(*work->queued));
  for (i = 0; i < count; i++)
    work->predicate_occurrences[i] = SIZE_MAX;
  return true;
}

static bool facts_worklist_init(facts_worklist *work,
                                facts_work_storage *storage,
                                size_t n_predicates) {
  memset(work, 0, sizeof(*work));
  ixs_arena_init_inline(&work->arena, storage->bytes, sizeof(storage->bytes),
                        IXS_ARENA_DEFAULT_SIZE);
  work->n_predicates = n_predicates;
  if (!facts_worklist_alloc_arrays(work) ||
      !facts_predicate_set_init(&work->arena, n_predicates, &work->seen,
                                &work->seen_capacity)) {
    ixs_arena_destroy_transient(&work->arena);
    return false;
  }
  return true;
}

static void facts_worklist_destroy(facts_worklist *work) {
  ixs_arena_destroy_transient(&work->arena);
}

static facts_symbol_slot *facts_symbol_find(facts_worklist *work,
                                            const char *name) {
  size_t index;
  if (!work->symbols)
    return NULL;
  index = bounds_hash_ptr(name) & (work->symbol_capacity - 1u);
  while (work->symbols[index].name && work->symbols[index].name != name)
    index = (index + 1u) & (work->symbol_capacity - 1u);
  return &work->symbols[index];
}

static bool facts_symbol_table_grow(facts_worklist *work) {
  size_t new_capacity =
      work->symbol_capacity ? work->symbol_capacity * 2u : FACT_WORK_INIT_CAP;
  facts_symbol_slot *symbols;
  size_t i;
  if (new_capacity <= work->symbol_capacity ||
      new_capacity > SIZE_MAX / sizeof(*symbols))
    return false;
  symbols = ixs_arena_alloc(&work->arena, new_capacity * sizeof(*symbols),
                            sizeof(void *));
  if (!symbols)
    return false;
  memset(symbols, 0, new_capacity * sizeof(*symbols));
  for (i = 0; i < work->symbol_capacity; i++) {
    if (work->symbols[i].name) {
      size_t index =
          bounds_hash_ptr(work->symbols[i].name) & (new_capacity - 1u);
      while (symbols[index].name)
        index = (index + 1u) & (new_capacity - 1u);
      symbols[index] = work->symbols[i];
    }
  }
  work->symbols = symbols;
  work->symbol_capacity = new_capacity;
  return true;
}

static bool facts_occurrences_grow(facts_worklist *work) {
  size_t new_capacity = work->occurrence_capacity
                            ? work->occurrence_capacity * 2u
                            : FACT_WORK_INIT_CAP;
  facts_symbol_occurrence *occurrences;
  if (new_capacity <= work->occurrence_capacity ||
      new_capacity > SIZE_MAX / sizeof(*occurrences))
    return false;
  occurrences =
      ixs_arena_grow(&work->arena, work->occurrences,
                     work->occurrence_capacity * sizeof(*work->occurrences),
                     new_capacity * sizeof(*work->occurrences), sizeof(void *));
  if (!occurrences)
    return false;
  work->occurrences = occurrences;
  work->occurrence_capacity = new_capacity;
  return true;
}

static bool facts_worklist_add_symbol(facts_worklist *work, size_t predicate,
                                      const char *name) {
  facts_symbol_slot *slot;
  facts_symbol_occurrence *occurrence;
  size_t index;
  if (!work->symbol_capacity ||
      work->symbol_count >= work->symbol_capacity / 2u) {
    if (!facts_symbol_table_grow(work))
      return false;
  }
  if (work->occurrence_count >= work->occurrence_capacity &&
      !facts_occurrences_grow(work))
    return false;
  slot = facts_symbol_find(work, name);
  if (!slot)
    return false;
  if (!slot->name) {
    slot->name = name;
    slot->first_occurrence = SIZE_MAX;
    work->symbol_count++;
  }
  index = work->occurrence_count++;
  occurrence = &work->occurrences[index];
  occurrence->name = name;
  occurrence->predicate = predicate;
  occurrence->next_for_predicate = work->predicate_occurrences[predicate];
  occurrence->next_for_symbol = slot->first_occurrence;
  work->predicate_occurrences[predicate] = index;
  slot->first_occurrence = index;
  return true;
}

static bool facts_node_set_grow(ixs_arena *arena, facts_node_set *set) {
  size_t new_capacity = set->capacity ? set->capacity * 2u : FACT_WORK_INIT_CAP;
  ixs_node **slots;
  size_t i;
  if (new_capacity <= set->capacity || new_capacity > SIZE_MAX / sizeof(*slots))
    return false;
  slots = ixs_arena_alloc(arena, new_capacity * sizeof(*slots), sizeof(void *));
  if (!slots)
    return false;
  memset(slots, 0, new_capacity * sizeof(*slots));
  for (i = 0; i < set->capacity; i++) {
    if (set->slots[i]) {
      size_t index = set->slots[i]->hash & (new_capacity - 1u);
      while (slots[index])
        index = (index + 1u) & (new_capacity - 1u);
      slots[index] = set->slots[i];
    }
  }
  set->slots = slots;
  set->capacity = new_capacity;
  return true;
}

static bool facts_node_set_insert(ixs_arena *arena, facts_node_set *set,
                                  ixs_node *node, bool *inserted) {
  size_t index;
  if (!set->capacity || set->count >= set->capacity / 2u) {
    if (!facts_node_set_grow(arena, set))
      return false;
  }
  index = node->hash & (set->capacity - 1u);
  while (set->slots[index] && set->slots[index] != node)
    index = (index + 1u) & (set->capacity - 1u);
  if (set->slots[index]) {
    *inserted = false;
    return true;
  }
  set->slots[index] = node;
  set->count++;
  *inserted = true;
  return true;
}

static bool facts_node_stack_push(ixs_arena *arena, ixs_node ***stack,
                                  size_t *count, size_t *capacity,
                                  ixs_node *node) {
  if (*count >= *capacity) {
    size_t new_capacity = *capacity ? *capacity * 2u : FACT_WORK_INIT_CAP;
    ixs_node **grown;
    if (new_capacity <= *capacity || new_capacity > SIZE_MAX / sizeof(**stack))
      return false;
    grown = ixs_arena_grow(arena, *stack, *capacity * sizeof(**stack),
                           new_capacity * sizeof(**stack), sizeof(void *));
    if (!grown)
      return false;
    *stack = grown;
    *capacity = new_capacity;
  }
  (*stack)[(*count)++] = node;
  return true;
}

static bool facts_worklist_index_predicate(facts_worklist *work,
                                           size_t predicate, ixs_node *root) {
  facts_work_storage storage;
  ixs_arena traversal;
  facts_node_set visited;
  ixs_node **stack = NULL;
  size_t stack_capacity = 0;
  size_t stack_count = 0;
  bool ok = false;
  ixs_arena_init_inline(&traversal, storage.bytes, sizeof(storage.bytes),
                        IXS_ARENA_DEFAULT_SIZE);
  memset(&visited, 0, sizeof(visited));
  if (!facts_node_stack_push(&traversal, &stack, &stack_count, &stack_capacity,
                             root))
    goto cleanup;
  while (stack_count > 0) {
    ixs_node *node = stack[--stack_count];
    uint32_t child_count;
    uint32_t i;
    bool inserted;
    if (!facts_node_set_insert(&traversal, &visited, node, &inserted))
      goto cleanup;
    if (!inserted)
      continue;
    if (node->tag == IXS_SYM &&
        !facts_worklist_add_symbol(work, predicate, node->u.name))
      goto cleanup;
    child_count = ixs_node_nchildren(node);
    for (i = 0; i < child_count; i++) {
      if (!facts_node_stack_push(&traversal, &stack, &stack_count,
                                 &stack_capacity, ixs_node_child(node, i)))
        goto cleanup;
    }
  }
  ok = true;

cleanup:
  ixs_arena_destroy_transient(&traversal);
  return ok;
}

static bool facts_worklist_enqueue(facts_worklist *work, size_t predicate) {
  if (!work->active[predicate] || work->queued[predicate])
    return true;
  if (work->queue_count >= work->n_predicates)
    return false;
  work->queue[work->queue_tail] = predicate;
  work->queue_tail = (work->queue_tail + 1u) % work->n_predicates;
  work->queue_count++;
  work->queued[predicate] = true;
  return true;
}

static bool facts_worklist_build(facts_worklist *work,
                                 ixs_node *const *predicates) {
  size_t i;
  for (i = 0; i < work->n_predicates; i++) {
    if (work->seen && facts_predicate_seen_or_insert(
                          work->seen, work->seen_capacity, predicates[i]))
      continue;
    work->active[i] = true;
    if (!facts_worklist_index_predicate(work, i, predicates[i]) ||
        !facts_worklist_enqueue(work, i))
      return false;
  }
  return true;
}

static size_t facts_worklist_pop(facts_worklist *work) {
  size_t predicate = work->queue[work->queue_head];
  work->queue_head = (work->queue_head + 1u) % work->n_predicates;
  work->queue_count--;
  work->queued[predicate] = false;
  return predicate;
}

static bool facts_worklist_enqueue_all(facts_worklist *work) {
  size_t i;
  for (i = 0; i < work->n_predicates; i++) {
    if (!facts_worklist_enqueue(work, i))
      return false;
  }
  return true;
}

static bool facts_worklist_enqueue_dependencies(facts_worklist *work,
                                                size_t predicate) {
  size_t occurrence_index = work->predicate_occurrences[predicate];
  if (occurrence_index == SIZE_MAX)
    return facts_worklist_enqueue_all(work);
  while (occurrence_index != SIZE_MAX) {
    facts_symbol_occurrence *occurrence = &work->occurrences[occurrence_index];
    facts_symbol_slot *slot = facts_symbol_find(work, occurrence->name);
    size_t dependent;
    if (!slot || !slot->name)
      return false;
    dependent = slot->first_occurrence;
    while (dependent != SIZE_MAX) {
      if (!facts_worklist_enqueue(work, work->occurrences[dependent].predicate))
        return false;
      dependent = work->occurrences[dependent].next_for_symbol;
    }
    occurrence_index = occurrence->next_for_predicate;
  }
  return true;
}

static ixs_bounds_build_status
facts_ingest_original_predicates(ixs_bounds *candidate,
                                 ixs_node *const *predicates,
                                 const facts_worklist *work) {
  size_t i;
  for (i = 0; i < work->n_predicates; i++) {
    ixs_bounds_build_status status;
    if (!work->active[i])
      continue;
    status = bounds_ingest_predicate(candidate, predicates[i]);
    if (status != IXS_BOUNDS_BUILD_OK)
      return status;
  }
  return IXS_BOUNDS_BUILD_OK;
}

static ixs_bounds_build_status
facts_process_predicate_worklist(ixs_ctx *ctx, ixs_bounds *candidate,
                                 ixs_node *const *predicates,
                                 facts_worklist *work) {
  while (work->queue_count > 0) {
    size_t predicate_index = facts_worklist_pop(work);
    ixs_node *predicate;
    ixs_bounds_build_status status;
    bool changed = false;
    candidate->semantic_changed = &changed;
    predicate =
        simp_simplify_bounds(ctx, predicates[predicate_index], candidate);
    if (!predicate || candidate->oom) {
      candidate->semantic_changed = NULL;
      return IXS_BOUNDS_BUILD_OOM;
    }
    status = bounds_ingest_predicate(candidate, predicate);
    candidate->semantic_changed = NULL;
    if (status != IXS_BOUNDS_BUILD_OK)
      return status;
    if (candidate->contradiction || ixs_bounds_has_empty(candidate))
      return IXS_BOUNDS_BUILD_OK;
    if (changed && !facts_worklist_enqueue_dependencies(work, predicate_index))
      return IXS_BOUNDS_BUILD_OOM;
  }
  return IXS_BOUNDS_BUILD_OK;
}

static ixs_bounds_build_status
facts_ingest_predicate_closure(ixs_ctx *ctx, ixs_bounds *candidate,
                               ixs_node *const *predicates,
                               size_t n_predicates) {
  facts_work_storage storage;
  facts_worklist work;
  ixs_bounds_build_status status = IXS_BOUNDS_BUILD_OOM;
  if (!facts_worklist_init(&work, &storage, n_predicates))
    return IXS_BOUNDS_BUILD_OOM;
  if (!facts_worklist_build(&work, predicates))
    goto cleanup;

  /* Preserve original expression identities before fact-conditioned
   * rewrites. */
  status = facts_ingest_original_predicates(candidate, predicates, &work);
  if (status != IXS_BOUNDS_BUILD_OK || candidate->contradiction ||
      ixs_bounds_has_empty(candidate))
    goto cleanup;

  /* A rewrite cannot introduce a symbol absent from its original predicate.
   * Revisit only predicates that share a symbol with a semantic refinement. */
  status = facts_process_predicate_worklist(ctx, candidate, predicates, &work);

cleanup:
  candidate->semantic_changed = NULL;
  facts_worklist_destroy(&work);
  return status;
}

ixs_facts *ixs_facts_create_preds(ixs_session *s, ixs_node *const *predicates,
                                  size_t n_predicates) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds bounds;
  ixs_bounds_build_status status;
  ixs_facts *facts;
  if (!s)
    return NULL;
  ctx = ixs_session_bind(&binding, s);
  mark = ixs_arena_save(&ctx->scratch);
  status = ixs_bounds_build_ctx(&bounds, ctx, &ctx->scratch, predicates,
                                n_predicates);
  if (status != IXS_BOUNDS_BUILD_OK)
    goto failed;
  facts = ixs_arena_alloc(&ctx->arena, sizeof(*facts), sizeof(void *));
  if (!facts)
    goto failed;
  memset(facts, 0, sizeof(*facts));
  facts->impl = binding.impl;
  facts->ctx = ctx;
  facts->epoch = binding.impl->epoch;
  facts->bounds = bounds;
  facts->usable = true;
  ixs_session_unbind(&binding);
  return facts;

failed:
  ixs_arena_restore(&ctx->scratch, mark);
  ixs_session_unbind(&binding);
  return NULL;
}

ixs_facts *ixs_facts_create(ixs_session *s) {
  return ixs_facts_create_preds(s, NULL, 0);
}

bool ixs_facts_assume_preds(ixs_facts *facts, ixs_node *const *predicates,
                            size_t n_predicates) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds candidate;
  ixs_bounds_build_status status;
  if (!facts_bind(facts, &binding, &ctx))
    return false;
  if (!facts_ready(facts)) {
    ixs_session_unbind(&binding);
    return false;
  }
  if (n_predicates == 0) {
    ixs_session_unbind(&binding);
    return true;
  }
  if (!predicates) {
    (void)assumption_invalid(&facts->bounds, "NULL array with nonzero count");
    facts_poison(facts);
    ixs_session_unbind(&binding);
    return false;
  }
  mark = ixs_arena_save(&ctx->scratch);
  if (!ixs_bounds_fork(&candidate, &facts->bounds)) {
    ixs_arena_restore(&ctx->scratch, mark);
    facts_poison(facts);
    ixs_session_unbind(&binding);
    return false;
  }
  status = bounds_validate_predicates(&candidate, predicates, n_predicates);
  if (status == IXS_BOUNDS_BUILD_OK)
    status = facts_ingest_predicate_closure(ctx, &candidate, predicates,
                                            n_predicates);
  if (status == IXS_BOUNDS_BUILD_OK) {
    facts_commit(facts, &candidate);
  } else {
    ixs_arena_restore(&ctx->scratch, mark);
    facts_poison(facts);
  }
  ixs_session_unbind(&binding);
  return status == IXS_BOUNDS_BUILD_OK;
}

bool ixs_facts_assume_pred(ixs_facts *facts, ixs_node *pred) {
  return ixs_facts_assume_preds(facts, &pred, 1);
}

bool ixs_facts_assume_range(ixs_facts *facts, ixs_node *expr,
                            const ixs_range_result *range) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds candidate;
  ixs_interval iv;
  bool ok = false;
  if (!facts_bind(facts, &binding, &ctx))
    return false;
  if (!facts_ready(facts))
    goto cleanup;
  mark = ixs_arena_save(&ctx->scratch);
  if (!facts_node_ok(ctx, expr) || !range_result_to_interval(range, &iv) ||
      !ixs_bounds_fork(&candidate, &facts->bounds))
    goto failed;
  ixs_bounds_add_expr(&candidate, expr, iv);
  if (candidate.oom)
    goto failed;
  facts_commit(facts, &candidate);
  ok = true;
  goto cleanup;

failed:
  ixs_arena_restore(&ctx->scratch, mark);
  facts_poison(facts);

cleanup:
  ixs_session_unbind(&binding);
  return ok;
}

bool ixs_facts_derive_affine(ixs_facts *facts, ixs_node *base, int64_t scale,
                             int64_t offset, ixs_node *derived) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds candidate;
  ixs_interval iv, shifted;
  bool ok = false;
  if (!facts_bind(facts, &binding, &ctx))
    return false;
  if (!facts_ready(facts))
    goto cleanup;
  mark = ixs_arena_save(&ctx->scratch);
  if (!facts_node_ok(ctx, base) || !facts_node_ok(ctx, derived))
    goto failed;
  if (!ixs_bounds_fork(&candidate, &facts->bounds))
    goto failed;
  iv = ixs_bounds_get(&candidate, base);
  if (candidate.oom || !iv.valid || ixs_interval_is_empty(iv))
    goto failed;
  shifted = iv_add(iv_mul_const(iv, scale, 1), ixs_interval_exact(offset, 1));
  if (!shifted.valid || ixs_interval_is_empty(shifted))
    goto failed;
  ixs_bounds_add_expr(&candidate, derived, shifted);
  if (candidate.oom)
    goto failed;
  facts_commit(facts, &candidate);
  ok = true;
  goto cleanup;

failed:
  ixs_arena_restore(&ctx->scratch, mark);
  facts_poison(facts);

cleanup:
  ixs_session_unbind(&binding);
  return ok;
}

bool ixs_facts_substitute(ixs_facts *dst, const ixs_facts *src,
                          ixs_node *target, ixs_node *replacement) {
  return ixs_facts_substitute_multi(dst, src, 1, &target, &replacement);
}

static bool facts_substitution_inputs_ok(const ixs_facts *dst,
                                         const ixs_facts *src, ixs_ctx *ctx,
                                         uint32_t nsubs,
                                         ixs_node *const *targets,
                                         ixs_node *const *replacements) {
  uint32_t i;
  if (!src || src->impl != dst->impl || src->ctx != ctx ||
      src->epoch != dst->epoch || !facts_ready(src) ||
      (nsubs != 0 && (!targets || !replacements)))
    return false;
  for (i = 0; i < nsubs; i++) {
    if (!facts_node_ok(ctx, targets[i]) || !facts_node_ok(ctx, replacements[i]))
      return false;
  }
  return true;
}

static bool bounds_transfer_substituted_exprs(ixs_bounds *dst,
                                              const ixs_bounds *src,
                                              ixs_ctx *ctx, uint32_t nsubs,
                                              ixs_node *const *targets,
                                              ixs_node *const *replacements) {
  size_t i;
  for (i = 0; i < src->nexprs; i++) {
    if (!src->exprs[i].iv.valid) {
      bounds_mark_contradiction(dst);
      continue;
    }
    ixs_node *subst =
        simp_subs_multi(ctx, src->exprs[i].expr, nsubs, targets, replacements);
    if (!subst || ixs_node_is_sentinel(subst))
      return false;
    ixs_bounds_add_expr(dst, subst, src->exprs[i].iv);
    if (subst != src->exprs[i].expr)
      bounds_transfer_range(dst, subst, src->exprs[i].iv);
    if (dst->oom)
      return false;
  }
  return true;
}

static bool bounds_transfer_substituted_vars(ixs_bounds *dst,
                                             const ixs_bounds *src,
                                             ixs_ctx *ctx, uint32_t nsubs,
                                             ixs_node *const *targets,
                                             ixs_node *const *replacements) {
  size_t i;
  for (i = 0; i < src->nvars; i++) {
    ixs_node *sym =
        ixs_node_sym(ctx, src->vars[i].name, strlen(src->vars[i].name));
    ixs_node *subst;
    if (!sym || ixs_node_is_sentinel(sym))
      return false;
    subst = simp_subs_multi(ctx, sym, nsubs, targets, replacements);
    if (!subst || ixs_node_is_sentinel(subst))
      return false;
    if (subst == sym) {
      bounds_add_var_fact(dst, &src->vars[i]);
    } else {
      ixs_bounds_add_expr(dst, subst, src->vars[i].iv);
      bounds_transfer_var_fact(dst, &src->vars[i], subst);
    }
    if (dst->oom)
      return false;
  }
  return true;
}

static bool bounds_transfer_substituted_nonzero(ixs_bounds *dst,
                                                const ixs_bounds *src,
                                                ixs_ctx *ctx, uint32_t nsubs,
                                                ixs_node *const *targets,
                                                ixs_node *const *replacements) {
  size_t i;
  for (i = 0; i < src->nnonzero; i++) {
    ixs_node *subst =
        simp_subs_multi(ctx, src->nonzero[i], nsubs, targets, replacements);
    if (!subst || ixs_node_is_sentinel(subst))
      return false;
    bounds_add_nonzero(dst, subst);
    if (dst->oom)
      return false;
  }
  return true;
}

bool ixs_facts_substitute_multi(ixs_facts *dst, const ixs_facts *src,
                                uint32_t nsubs, ixs_node *const *targets,
                                ixs_node *const *replacements) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_bounds candidate;
  bool ok = false;

  if (!facts_bind(dst, &binding, &ctx))
    return false;
  if (!facts_ready(dst))
    goto cleanup;
  mark = ixs_arena_save(&ctx->scratch);
  if (!facts_substitution_inputs_ok(dst, src, ctx, nsubs, targets,
                                    replacements))
    goto failed;
  if (src == dst && nsubs == 0) {
    ok = true;
    goto cleanup;
  }
  if (!ixs_bounds_fork(&candidate, &dst->bounds))
    goto failed;
  if (src->bounds.contradiction)
    bounds_mark_contradiction(&candidate);
  if (!bounds_transfer_substituted_exprs(&candidate, &src->bounds, ctx, nsubs,
                                         targets, replacements) ||
      !bounds_transfer_substituted_vars(&candidate, &src->bounds, ctx, nsubs,
                                        targets, replacements) ||
      !bounds_transfer_substituted_nonzero(&candidate, &src->bounds, ctx, nsubs,
                                           targets, replacements))
    goto failed;
  facts_commit(dst, &candidate);
  ok = true;
  goto cleanup;

failed:
  ixs_arena_restore(&ctx->scratch, mark);
  facts_poison(dst);

cleanup:
  ixs_session_unbind(&binding);
  return ok;
}

static ixs_node *facts_simplify_error(ixs_ctx *ctx, const char *message) {
  ixs_ctx_push_error(ctx, "facts: %s", message);
  return ctx->sentinel_error;
}

ixs_node *ixs_simplify_facts(ixs_facts *facts, ixs_node *expr) {
  ixs_session_binding binding;
  ixs_arena_mark mark;
  ixs_ctx *ctx;
  ixs_node *result;
  bool old_oom;

  if (!facts_bind(facts, &binding, &ctx))
    return NULL;
  if (!facts_ready(facts)) {
    result = facts_simplify_error(ctx, "fact set is unusable");
    goto cleanup;
  }
  if (!expr) {
    result = NULL;
    goto cleanup;
  }
  if (!ixs_ctx_owns_node(ctx, expr)) {
    result =
        facts_simplify_error(ctx, "expression belongs to a different context");
    goto cleanup;
  }
  if (ixs_node_is_sentinel(expr)) {
    result = expr;
    goto cleanup;
  }
  if (ixs_bounds_has_empty(&facts->bounds)) {
    result = expr;
    goto cleanup;
  }

  mark = ixs_arena_save(&ctx->scratch);
  old_oom = facts->bounds.oom;
  result = simp_simplify_bounds(ctx, expr, &facts->bounds);
  if (!result || (!old_oom && facts->bounds.oom)) {
    result = NULL;
    bounds_cache_clear(&facts->bounds);
  }
  facts->bounds.oom = old_oom;
  ixs_arena_restore(&ctx->scratch, mark);

cleanup:
  ixs_session_unbind(&binding);
  return result;
}

static void facts_fill_batch(ixs_node **exprs, size_t n, ixs_node *value) {
  size_t i;
  if (!exprs)
    return;
  for (i = 0; i < n; i++)
    exprs[i] = value;
}

void ixs_simplify_batch_facts(ixs_facts *facts, ixs_node **exprs, size_t n) {
  ixs_session_binding binding;
  ixs_arena_mark mark;
  ixs_ctx *ctx;
  bool old_oom;
  size_t i;

  if (!facts_bind(facts, &binding, &ctx)) {
    facts_fill_batch(exprs, n, NULL);
    return;
  }
  if (n > 0 && !exprs) {
    (void)facts_simplify_error(ctx, "NULL batch with nonzero count");
    goto cleanup;
  }
  if (!facts_ready(facts)) {
    facts_fill_batch(exprs, n,
                     facts_simplify_error(ctx, "fact set is unusable"));
    goto cleanup;
  }
  for (i = 0; i < n; i++) {
    if (exprs[i] && !ixs_ctx_owns_node(ctx, exprs[i])) {
      facts_fill_batch(
          exprs, n,
          facts_simplify_error(
              ctx, "batch expression belongs to a different context"));
      goto cleanup;
    }
  }
  if (ixs_bounds_has_empty(&facts->bounds))
    goto cleanup;

  mark = ixs_arena_save(&ctx->scratch);
  old_oom = facts->bounds.oom;
  if (!simp_simplify_batch_bounds(ctx, exprs, n, &facts->bounds) ||
      (!old_oom && facts->bounds.oom)) {
    facts_fill_batch(exprs, n, NULL);
    bounds_cache_clear(&facts->bounds);
  }
  facts->bounds.oom = old_oom;
  ixs_arena_restore(&ctx->scratch, mark);

cleanup:
  ixs_session_unbind(&binding);
}

#define PREDICATE_QUERY_STACK_LIMIT 1024u
#define PREDICATE_QUERY_VISIT_LIMIT 8192u

typedef struct {
  ixs_node *node;
  uint32_t next_child;
  ixs_check_result result;
  bool started;
} predicate_query_frame;

static ixs_check_result check_result_not(ixs_check_result result) {
  if (result == IXS_CHECK_TRUE)
    return IXS_CHECK_FALSE;
  if (result == IXS_CHECK_FALSE)
    return IXS_CHECK_TRUE;
  return IXS_CHECK_UNKNOWN;
}

static ixs_check_result predicate_query_atom(ixs_bounds *bounds,
                                             ixs_node *node) {
  ixs_interval iv;
  int lo_cmp;
  int hi_cmp;
  if (!node)
    return IXS_CHECK_UNKNOWN;
  if (node->tag == IXS_INT)
    return node->u.ival == 0 ? IXS_CHECK_FALSE : IXS_CHECK_TRUE;
  if (node->tag == IXS_RAT)
    return node->u.rat.p == 0 ? IXS_CHECK_FALSE : IXS_CHECK_TRUE;
  if (node->tag == IXS_CMP) {
    ixs_check_result result = ixs_bounds_check(bounds, node);
    if (result == IXS_CHECK_UNKNOWN && ixs_node_is_zero(node->u.binary.rhs) &&
        bounds_is_known_nonzero(bounds, node->u.binary.lhs)) {
      if (node->u.binary.cmp_op == IXS_CMP_NE)
        return IXS_CHECK_TRUE;
      if (node->u.binary.cmp_op == IXS_CMP_EQ)
        return IXS_CHECK_FALSE;
    }
    return result;
  }

  /* NOT accepts numeric operands.  Interval truthiness is a bounded
   * sufficient proof for those operands; a range crossing zero is unknown. */
  iv = ixs_bounds_get(bounds, node);
  if (!iv.valid || ixs_interval_is_empty(iv))
    return IXS_CHECK_UNKNOWN;
  lo_cmp = iv.lo_inf ? -1 : ixs_rat_cmp(iv.lo_p, iv.lo_q, 0, 1);
  hi_cmp = iv.hi_inf ? 1 : ixs_rat_cmp(iv.hi_p, iv.hi_q, 0, 1);
  if (!iv.lo_inf && !iv.hi_inf && lo_cmp == 0 && hi_cmp == 0)
    return IXS_CHECK_FALSE;
  if ((!iv.lo_inf && lo_cmp > 0) || (!iv.hi_inf && hi_cmp < 0))
    return IXS_CHECK_TRUE;
  return IXS_CHECK_UNKNOWN;
}

static void predicate_query_fold(predicate_query_frame *parent,
                                 ixs_check_result child) {
  if (parent->node->tag == IXS_NOT) {
    parent->result = check_result_not(child);
    return;
  }
  if (parent->node->tag == IXS_AND) {
    if (child == IXS_CHECK_FALSE)
      parent->result = IXS_CHECK_FALSE;
    else if (child == IXS_CHECK_UNKNOWN && parent->result == IXS_CHECK_TRUE)
      parent->result = IXS_CHECK_UNKNOWN;
    return;
  }
  if (parent->node->tag == IXS_OR) {
    if (child == IXS_CHECK_TRUE)
      parent->result = IXS_CHECK_TRUE;
    else if (child == IXS_CHECK_UNKNOWN && parent->result == IXS_CHECK_FALSE)
      parent->result = IXS_CHECK_UNKNOWN;
  }
}

static bool
predicate_query_short_circuited(const predicate_query_frame *frame) {
  return (frame->node->tag == IXS_AND && frame->result == IXS_CHECK_FALSE) ||
         (frame->node->tag == IXS_OR && frame->result == IXS_CHECK_TRUE);
}

/* An absorber determines a total result only when every retained operand is
 * defined and integer-valued. */
static bool predicate_query_assoc_domain_proven(ixs_bounds *bounds,
                                                ixs_node *node) {
  return ixs_bounds_check_defined(bounds, node) == IXS_CHECK_TRUE &&
         ixs_bounds_check_integer_valued(bounds, node) == IXS_CHECK_TRUE;
}

static void predicate_query_start(predicate_query_frame *frame) {
  if (frame->started)
    return;
  frame->started = true;
  if (frame->node && frame->node->tag == IXS_AND)
    frame->result = IXS_CHECK_TRUE;
  else if (frame->node && frame->node->tag == IXS_OR)
    frame->result = IXS_CHECK_FALSE;
  else
    frame->result = IXS_CHECK_UNKNOWN;
}

static ixs_node *predicate_query_next_child(predicate_query_frame *frame) {
  ixs_node *node = frame->node;

  if (node && (node->tag == IXS_AND || node->tag == IXS_OR) &&
      !predicate_query_short_circuited(frame) &&
      frame->next_child < node->u.assoc.nargs)
    return node->u.assoc.args[frame->next_child++];
  if (node && node->tag == IXS_NOT && frame->next_child == 0) {
    frame->next_child = 1;
    return node->u.unary_bool.arg;
  }
  return NULL;
}

static ixs_check_result
predicate_query_complete(ixs_bounds *bounds,
                         const predicate_query_frame *frame) {
  ixs_node *node = frame->node;
  ixs_check_result result;

  if (!node ||
      (node->tag != IXS_AND && node->tag != IXS_OR && node->tag != IXS_NOT))
    return predicate_query_atom(bounds, node);

  result = frame->result;
  if (predicate_query_short_circuited(frame) &&
      !predicate_query_assoc_domain_proven(bounds, node))
    result = IXS_CHECK_UNKNOWN;
  return result;
}

static ixs_check_result predicate_query_eval(ixs_bounds *bounds,
                                             ixs_node *predicate) {
  predicate_query_frame stack[PREDICATE_QUERY_STACK_LIMIT];
  size_t depth = 1;
  size_t visited = 1;
  ixs_check_result answer = IXS_CHECK_UNKNOWN;

  memset(stack, 0, sizeof(stack));
  stack[0].node = predicate;
  while (depth > 0) {
    predicate_query_frame *frame = &stack[depth - 1u];
    ixs_node *child = NULL;
    ixs_check_result completed;

    predicate_query_start(frame);
    child = predicate_query_next_child(frame);

    if (child) {
      if (depth >= PREDICATE_QUERY_STACK_LIMIT ||
          visited >= PREDICATE_QUERY_VISIT_LIMIT)
        return IXS_CHECK_UNKNOWN;
      memset(&stack[depth], 0, sizeof(stack[depth]));
      stack[depth].node = child;
      depth++;
      visited++;
      continue;
    }

    completed = predicate_query_complete(bounds, frame);
    depth--;
    if (depth == 0) {
      answer = completed;
      break;
    }
    predicate_query_fold(&stack[depth - 1u], completed);
  }
  return bounds->oom ? IXS_CHECK_UNKNOWN : answer;
}

#define EQUIVALENCE_DEPTH_LIMIT 32u
#define EQUIVALENCE_VISIT_LIMIT 4096u
#define EQUIVALENCE_TERM_LIMIT 1024u

typedef struct {
  ixs_ctx *ctx;
  ixs_bounds *bounds;
  size_t visited;
  bool limited;
  bool oom;
} equivalence_state;

typedef struct {
  ixs_node *dividend;
  int64_t modulus;
  int64_t term_coeff;
  int64_t offset_p;
  int64_t offset_q;
  ixs_cmp_op op;
} equivalence_mod_cmp;

static ixs_check_result equivalence_core(equivalence_state *state,
                                         ixs_node *lhs, ixs_node *rhs,
                                         unsigned depth);

static ixs_check_result equivalence_difference(equivalence_state *state,
                                               ixs_node *lhs, ixs_node *rhs) {
  ixs_node *difference = simp_sub(state->ctx, lhs, rhs);
  int64_t delta;
  if (!difference) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (ixs_node_is_sentinel(difference))
    return IXS_CHECK_UNKNOWN;
  difference = simp_simplify_bounds(state->ctx, difference, state->bounds);
  if (!difference) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (bounds_exact_integer_difference(state->bounds, difference, &delta))
    return delta == 0 ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
  return IXS_CHECK_UNKNOWN;
}

static bool equivalence_integer_delta(equivalence_state *state, ixs_node *lhs,
                                      ixs_node *rhs, int64_t *delta) {
  ixs_node *difference = simp_sub(state->ctx, lhs, rhs);
  if (!difference) {
    state->oom = true;
    return false;
  }
  difference = simp_simplify_bounds(state->ctx, difference, state->bounds);
  if (!difference) {
    state->oom = true;
    return false;
  }
  if (ixs_node_is_sentinel(difference))
    return false;
  if (!bounds_exact_integer_difference(state->bounds, difference, delta)) {
    difference = expand_impl(state->ctx, difference);
    if (!difference) {
      state->oom = true;
      return false;
    }
    if (ixs_node_is_sentinel(difference))
      return false;
    difference = simp_simplify_bounds(state->ctx, difference, state->bounds);
    if (!difference) {
      state->oom = true;
      return false;
    }
  }
  return bounds_exact_integer_difference(state->bounds, difference, delta);
}

static uint64_t equivalence_scale_stride(uint64_t stride, int64_t coefficient) {
  uint64_t magnitude = bounds_int64_magnitude(coefficient);
  if (stride == 0 || magnitude == 0)
    return 0;
  if (magnitude <= (uint64_t)INT64_MAX / stride)
    return magnitude * stride;
  return stride;
}

static bool equivalence_known_stride(equivalence_state *state, ixs_node *expr,
                                     uint64_t *stride, unsigned depth);

static bool equivalence_add_stride(equivalence_state *state, ixs_node *expr,
                                   uint64_t *stride, unsigned depth) {
  uint64_t result = 0;
  int64_t cp, cq;
  uint32_t i;
  ixs_node_get_rat(expr->u.add.coeff, &cp, &cq);
  (void)cp;
  if (cq != 1)
    return false;
  for (i = 0; i < expr->u.add.nterms; i++) {
    uint64_t term_stride;
    int64_t p, q;
    ixs_node_get_rat(expr->u.add.terms[i].coeff, &p, &q);
    if (q != 1 || !equivalence_known_stride(state, expr->u.add.terms[i].term,
                                            &term_stride, depth - 1u))
      return false;
    term_stride = equivalence_scale_stride(term_stride, p);
    result = bounds_u64_gcd(result, term_stride);
  }
  *stride = result;
  return true;
}

static bool equivalence_mul_stride(equivalence_state *state, ixs_node *expr,
                                   uint64_t *stride, unsigned depth) {
  uint64_t result;
  int64_t p, q;
  uint32_t i;
  ixs_node_get_rat(expr->u.mul.coeff, &p, &q);
  if (q != 1)
    return false;
  if (p == 0) {
    *stride = 0;
    return true;
  }
  if (expr->u.mul.nfactors == 1 && expr->u.mul.factors[0].exp == 1) {
    if (!equivalence_known_stride(state, expr->u.mul.factors[0].base, &result,
                                  depth - 1u))
      return false;
    *stride = equivalence_scale_stride(result, p);
    return true;
  }
  for (i = 0; i < expr->u.mul.nfactors; i++) {
    if (expr->u.mul.factors[i].exp <= 0 ||
        !ixs_node_is_integer_valued(expr->u.mul.factors[i].base)) {
      *stride = 1;
      return true;
    }
  }
  result = bounds_int64_magnitude(p);
  *stride = result <= (uint64_t)INT64_MAX ? result : 1;
  return true;
}

/* Stride inference is bounded by CONGRUENCE_DEPTH_LIMIT. Each ADD or MUL
 * level scans only its normalized immediate operands, so one proof is O(n)
 * in the visited expression rather than restarting integrality walks. */
static bool equivalence_known_stride(equivalence_state *state, ixs_node *expr,
                                     uint64_t *stride, unsigned depth) {
  if (!expr || !stride || depth == 0 || state->oom || state->limited)
    return false;
  switch (expr->tag) {
  case IXS_INT:
    *stride = 0;
    return true;
  case IXS_RAT:
    *stride = expr->u.rat.q == 1 ? 0 : 1;
    return expr->u.rat.q == 1;
  case IXS_SYM: {
    int64_t modulus, remainder;
    if (ixs_bounds_get_modrem(state->bounds, expr->u.name, &modulus,
                              &remainder)) {
      (void)remainder;
      *stride = (uint64_t)modulus;
    } else {
      *stride = 1;
    }
    if (state->bounds->oom) {
      state->oom = true;
      return false;
    }
    return true;
  }
  case IXS_ADD:
    return equivalence_add_stride(state, expr, stride, depth);
  case IXS_MUL:
    return equivalence_mul_stride(state, expr, stride, depth);
  case IXS_MOD:
    if (expr->u.binary.rhs->tag == IXS_INT && expr->u.binary.rhs->u.ival > 0 &&
        equivalence_known_stride(state, expr->u.binary.lhs, stride,
                                 depth - 1u)) {
      *stride = bounds_u64_gcd(*stride, (uint64_t)expr->u.binary.rhs->u.ival);
      return true;
    }
    *stride = 1;
    return true;
  default:
    if (ixs_node_is_integer_valued(expr)) {
      *stride = 1;
      return true;
    }
    return false;
  }
}

static bool equivalence_no_reachable_integer(equivalence_state *state,
                                             ixs_node *expr, int64_t lo,
                                             int64_t hi) {
  ixs_interval region;
  ixs_interval known;
  uint64_t stride;
  uint64_t residue;
  if (lo > hi)
    return true;
  region = ixs_interval_range(lo, 1, hi, 1);
  known = ixs_bounds_get(state->bounds, expr);
  if (state->bounds->oom) {
    state->oom = true;
    return false;
  }
  if (known.valid) {
    region = iv_intersect(region, known);
    if (!region.valid)
      return true;
  }
  if (!equivalence_known_stride(state, expr, &stride, CONGRUENCE_DEPTH_LIMIT) ||
      stride <= 1u || stride > (uint64_t)INT64_MAX ||
      !bounds_known_residue_depth(state->bounds, expr, stride, &residue,
                                  CONGRUENCE_DEPTH_LIMIT)) {
    if (state->bounds->oom)
      state->oom = true;
    return false;
  }
  return !interval_has_congruent_integer(&region, (int64_t)stride,
                                         (int64_t)residue);
}

static bool equivalence_ordered_cut(ixs_cmp_op op, bool *lower,
                                    int64_t *threshold) {
  switch (op) {
  case IXS_CMP_LT:
    *lower = false;
    *threshold = -1;
    return true;
  case IXS_CMP_LE:
    *lower = false;
    *threshold = 0;
    return true;
  case IXS_CMP_GT:
    *lower = true;
    *threshold = 1;
    return true;
  case IXS_CMP_GE:
    *lower = true;
    *threshold = 0;
    return true;
  default:
    return false;
  }
}

static ixs_check_result
equivalence_ordered_comparisons(equivalence_state *state, ixs_node *lhs,
                                ixs_node *rhs) {
  bool left_lower, right_lower;
  int64_t left_threshold, right_threshold, delta, mapped_threshold;
  int64_t lo, hi;
  if (!lhs || !rhs || lhs->tag != IXS_CMP || rhs->tag != IXS_CMP ||
      !ixs_node_is_zero(lhs->u.binary.rhs) ||
      !ixs_node_is_zero(rhs->u.binary.rhs) ||
      !equivalence_ordered_cut(lhs->u.binary.cmp_op, &left_lower,
                               &left_threshold) ||
      !equivalence_ordered_cut(rhs->u.binary.cmp_op, &right_lower,
                               &right_threshold) ||
      left_lower != right_lower ||
      ixs_bounds_check_integer_valued(state->bounds, lhs->u.binary.lhs) !=
          IXS_CHECK_TRUE ||
      ixs_bounds_check_integer_valued(state->bounds, rhs->u.binary.lhs) !=
          IXS_CHECK_TRUE ||
      !equivalence_integer_delta(state, lhs->u.binary.lhs, rhs->u.binary.lhs,
                                 &delta) ||
      !ixs_safe_add(right_threshold, delta, &mapped_threshold))
    return IXS_CHECK_UNKNOWN;
  if (left_threshold == mapped_threshold)
    return IXS_CHECK_TRUE;
  lo = left_threshold < mapped_threshold ? left_threshold : mapped_threshold;
  hi = left_threshold < mapped_threshold ? mapped_threshold : left_threshold;
  if (left_lower) {
    if (!ixs_safe_sub(hi, 1, &hi))
      return IXS_CHECK_UNKNOWN;
  } else {
    if (!ixs_safe_add(lo, 1, &lo))
      return IXS_CHECK_UNKNOWN;
  }
  return equivalence_no_reachable_integer(state, lhs->u.binary.lhs, lo, hi)
             ? IXS_CHECK_TRUE
             : IXS_CHECK_UNKNOWN;
}

static bool equivalence_extract_mod_sum(ixs_node *expr, ixs_node **dividend,
                                        ixs_node **denominator,
                                        int64_t *offset) {
  ixs_node *mod;
  int64_t cp, cq, kp, kq;
  if (expr->tag == IXS_MOD) {
    mod = expr;
    *offset = 0;
  } else if (expr->tag == IXS_ADD && expr->u.add.nterms == 1u &&
             expr->u.add.terms[0].term->tag == IXS_MOD) {
    ixs_node_get_rat(expr->u.add.terms[0].coeff, &cp, &cq);
    ixs_node_get_rat(expr->u.add.coeff, &kp, &kq);
    if (cp != 1 || cq != 1 || kq != 1)
      return false;
    mod = expr->u.add.terms[0].term;
    *offset = kp;
  } else {
    return false;
  }
  *dividend = mod->u.binary.lhs;
  *denominator = mod->u.binary.rhs;
  return true;
}

static bool equivalence_proves_zero_cmp(equivalence_state *state, ixs_node *lhs,
                                        ixs_cmp_op op) {
  struct ixs_node_impl cmp;
  bool result;
  memset(&cmp, 0, sizeof(cmp));
  cmp.tag = IXS_CMP;
  cmp.u.binary.lhs = lhs;
  cmp.u.binary.rhs = state->ctx->node_zero;
  cmp.u.binary.cmp_op = op;
  result = ixs_bounds_check(state->bounds, &cmp) == IXS_CHECK_TRUE;
  if (state->bounds->oom)
    state->oom = true;
  return result;
}

static bool equivalence_mod_sum_in_range(equivalence_state *state,
                                         ixs_node *sum, ixs_node *denominator) {
  ixs_node *upper;
  if (!equivalence_proves_zero_cmp(state, denominator, IXS_CMP_GT))
    return false;
  upper = simp_sub(state->ctx, sum, denominator);
  if (!upper) {
    state->oom = true;
    return false;
  }
  if (ixs_node_is_sentinel(upper))
    return false;
  return equivalence_proves_zero_cmp(state, sum, IXS_CMP_GE) &&
         equivalence_proves_zero_cmp(state, upper, IXS_CMP_LT);
}

static bool equivalence_residue_shift_in_range(uint64_t residue,
                                               uint64_t modulus,
                                               int64_t shift) {
  uint64_t magnitude;
  if (shift >= 0) {
    uint64_t positive = (uint64_t)shift;
    return positive < modulus && residue < modulus - positive;
  }
  magnitude = bounds_int64_magnitude(shift);
  return magnitude <= residue;
}

static bool equivalence_mod_shift_by_congruence(equivalence_state *state,
                                                ixs_node *dividend,
                                                ixs_node *denominator,
                                                int64_t shift) {
  uint64_t modulus;
  uint64_t residue;
  if (!equivalence_proves_zero_cmp(state, denominator, IXS_CMP_GT) ||
      !equivalence_known_stride(state, dividend, &modulus,
                                CONGRUENCE_DEPTH_LIMIT) ||
      modulus <= 1u || modulus > (uint64_t)INT64_MAX ||
      !bounds_known_residue_depth(state->bounds, dividend, modulus, &residue,
                                  CONGRUENCE_DEPTH_LIMIT) ||
      ixs_bounds_check_divisible(state->bounds, denominator,
                                 (int64_t)modulus) != IXS_CHECK_TRUE) {
    if (state->bounds->oom)
      state->oom = true;
    return false;
  }
  return equivalence_residue_shift_in_range(residue, modulus, shift);
}

static ixs_check_result
equivalence_mod_shift_direction(equivalence_state *state, ixs_node *shifted,
                                ixs_node *sum) {
  ixs_node *shifted_dividend;
  ixs_node *shifted_denominator;
  ixs_node *base_dividend;
  ixs_node *base_denominator;
  int64_t sum_offset;
  int64_t dividend_shift;
  if (shifted->tag != IXS_MOD ||
      !equivalence_extract_mod_sum(shifted, &shifted_dividend,
                                   &shifted_denominator, &dividend_shift) ||
      dividend_shift != 0 ||
      !equivalence_extract_mod_sum(sum, &base_dividend, &base_denominator,
                                   &sum_offset) ||
      shifted_denominator != base_denominator ||
      !equivalence_integer_delta(state, shifted_dividend, base_dividend,
                                 &dividend_shift) ||
      dividend_shift != sum_offset ||
      ixs_bounds_check_integer_valued(state->bounds, base_dividend) !=
          IXS_CHECK_TRUE ||
      ixs_bounds_check_integer_valued(state->bounds, base_denominator) !=
          IXS_CHECK_TRUE)
    return IXS_CHECK_UNKNOWN;
  if (equivalence_mod_sum_in_range(state, sum, base_denominator) ||
      equivalence_mod_shift_by_congruence(state, base_dividend,
                                          base_denominator, sum_offset))
    return IXS_CHECK_TRUE;
  return IXS_CHECK_UNKNOWN;
}

static ixs_check_result equivalence_mod_shifts(equivalence_state *state,
                                               ixs_node *lhs, ixs_node *rhs) {
  ixs_check_result result = equivalence_mod_shift_direction(state, lhs, rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  return equivalence_mod_shift_direction(state, rhs, lhs);
}

static bool equivalence_extract_mod_cmp(ixs_node *cmp,
                                        equivalence_mod_cmp *out) {
  ixs_node *residual;
  ixs_node *mod;
  int64_t cp;
  int64_t cq;
  if (!cmp || !out || cmp->tag != IXS_CMP ||
      !ixs_node_is_zero(cmp->u.binary.rhs))
    return false;
  residual = cmp->u.binary.lhs;
  out->offset_p = 0;
  out->offset_q = 1;
  out->term_coeff = 1;
  if (residual->tag == IXS_MOD) {
    mod = residual;
  } else if (residual->tag == IXS_ADD && residual->u.add.nterms == 1 &&
             residual->u.add.terms[0].term->tag == IXS_MOD) {
    ixs_node_get_rat(residual->u.add.terms[0].coeff, &cp, &cq);
    if (cq != 1 || (cp != 1 && cp != -1))
      return false;
    out->term_coeff = cp;
    ixs_node_get_rat(residual->u.add.coeff, &out->offset_p, &out->offset_q);
    mod = residual->u.add.terms[0].term;
  } else {
    return false;
  }
  if (mod->u.binary.rhs->tag != IXS_INT || mod->u.binary.rhs->u.ival <= 0)
    return false;
  out->dividend = mod->u.binary.lhs;
  out->modulus = mod->u.binary.rhs->u.ival;
  out->op = cmp->u.binary.cmp_op;
  return true;
}

static ixs_check_result equivalence_mod_comparisons(equivalence_state *state,
                                                    ixs_node *lhs,
                                                    ixs_node *rhs) {
  equivalence_mod_cmp left;
  equivalence_mod_cmp right;
  ixs_node *delta;
  ixs_check_result congruent;
  if (!equivalence_extract_mod_cmp(lhs, &left) ||
      !equivalence_extract_mod_cmp(rhs, &right))
    return IXS_CHECK_UNKNOWN;
  if (left.modulus != right.modulus || left.term_coeff != right.term_coeff ||
      left.offset_p != right.offset_p || left.offset_q != right.offset_q ||
      left.op != right.op)
    return IXS_CHECK_UNKNOWN;
  delta = simp_sub(state->ctx, left.dividend, right.dividend);
  if (!delta) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (ixs_node_is_sentinel(delta))
    return IXS_CHECK_UNKNOWN;
  congruent = ixs_bounds_check_congruent(state->bounds, delta, left.modulus, 0);
  return congruent == IXS_CHECK_TRUE ? IXS_CHECK_TRUE : IXS_CHECK_UNKNOWN;
}

static bool equivalence_flatten_logic(equivalence_state *state, ixs_node *root,
                                      ixs_tag tag, ixs_node **stack,
                                      ixs_node **terms, size_t *nterms) {
  size_t nstack = 1;
  *nterms = 0;
  stack[0] = root;
  while (nstack > 0) {
    ixs_node *node = stack[--nstack];
    if (node->tag == tag && ixs_node_is_bool_valued(node)) {
      uint32_t i;
      if ((size_t)node->u.assoc.nargs > EQUIVALENCE_TERM_LIMIT - nstack) {
        state->limited = true;
        return false;
      }
      for (i = 0; i < node->u.assoc.nargs; i++)
        stack[nstack++] = node->u.assoc.args[i];
    } else {
      if (*nterms >= EQUIVALENCE_TERM_LIMIT) {
        state->limited = true;
        return false;
      }
      terms[(*nterms)++] = node;
    }
  }
  return true;
}

static ixs_check_result equivalence_match_logic(equivalence_state *state,
                                                ixs_node *lhs, ixs_node *rhs,
                                                unsigned depth) {
  ixs_arena_mark mark = ixs_arena_save(&state->ctx->scratch);
  ixs_node **left_stack;
  ixs_node **right_stack;
  ixs_node **left_terms;
  ixs_node **right_terms;
  unsigned char *left_matched;
  unsigned char *right_matched;
  size_t nleft;
  size_t nright;
  size_t i;
  size_t j;
  ixs_check_result result = IXS_CHECK_UNKNOWN;

  left_stack = ixs_arena_alloc(&state->ctx->scratch,
                               EQUIVALENCE_TERM_LIMIT * sizeof(*left_stack),
                               sizeof(void *));
  right_stack = ixs_arena_alloc(&state->ctx->scratch,
                                EQUIVALENCE_TERM_LIMIT * sizeof(*right_stack),
                                sizeof(void *));
  left_terms = ixs_arena_alloc(&state->ctx->scratch,
                               EQUIVALENCE_TERM_LIMIT * sizeof(*left_terms),
                               sizeof(void *));
  right_terms = ixs_arena_alloc(&state->ctx->scratch,
                                EQUIVALENCE_TERM_LIMIT * sizeof(*right_terms),
                                sizeof(void *));
  left_matched =
      ixs_arena_alloc(&state->ctx->scratch, EQUIVALENCE_TERM_LIMIT, 1);
  right_matched =
      ixs_arena_alloc(&state->ctx->scratch, EQUIVALENCE_TERM_LIMIT, 1);
  if (!left_stack || !right_stack || !left_terms || !right_terms ||
      !left_matched || !right_matched) {
    state->oom = true;
    goto cleanup;
  }
  memset(left_matched, 0, EQUIVALENCE_TERM_LIMIT);
  memset(right_matched, 0, EQUIVALENCE_TERM_LIMIT);
  if (!equivalence_flatten_logic(state, lhs, lhs->tag, left_stack, left_terms,
                                 &nleft) ||
      !equivalence_flatten_logic(state, rhs, rhs->tag, right_stack, right_terms,
                                 &nright) ||
      nleft != nright)
    goto cleanup;

  /* Exact terms first.  This makes the bounded greedy phase deterministic
   * and avoids spending proof budget on the common reordered-tree case. */
  for (i = 0; i < nleft; i++) {
    for (j = 0; j < nright; j++) {
      if (!right_matched[j] && left_terms[i] == right_terms[j]) {
        left_matched[i] = 1;
        right_matched[j] = 1;
        break;
      }
    }
  }
  for (i = 0; i < nleft; i++) {
    if (left_matched[i])
      continue;
    for (j = 0; j < nright; j++) {
      if (!right_matched[j] &&
          equivalence_core(state, left_terms[i], right_terms[j], depth + 1u) ==
              IXS_CHECK_TRUE) {
        left_matched[i] = 1;
        right_matched[j] = 1;
        break;
      }
    }
    if (!left_matched[i])
      goto cleanup;
  }
  result = IXS_CHECK_TRUE;

cleanup:
  ixs_arena_restore(&state->ctx->scratch, mark);
  return result;
}

static ixs_check_result equivalence_predicate_shapes(equivalence_state *state,
                                                     ixs_node *lhs,
                                                     ixs_node *rhs,
                                                     unsigned depth) {
  if (lhs->tag == rhs->tag && (lhs->tag == IXS_AND || lhs->tag == IXS_OR))
    return equivalence_match_logic(state, lhs, rhs, depth);
  if (lhs->tag == IXS_NOT && rhs->tag == IXS_NOT)
    return equivalence_core(state, lhs->u.unary_bool.arg, rhs->u.unary_bool.arg,
                            depth + 1u);
  if (lhs->tag == IXS_CMP && rhs->tag == IXS_CMP) {
    ixs_check_result result = equivalence_mod_comparisons(state, lhs, rhs);
    if (result != IXS_CHECK_UNKNOWN)
      return result;
    return equivalence_ordered_comparisons(state, lhs, rhs);
  }
  return IXS_CHECK_UNKNOWN;
}

static ixs_check_result equivalence_expanded(equivalence_state *state,
                                             ixs_node *lhs, ixs_node *rhs,
                                             unsigned depth) {
  ixs_node *expanded_lhs = expand_impl(state->ctx, lhs);
  ixs_node *expanded_rhs = expand_impl(state->ctx, rhs);
  ixs_check_result result;
  if (!expanded_lhs || !expanded_rhs) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (ixs_node_is_sentinel(expanded_lhs) || ixs_node_is_sentinel(expanded_rhs))
    return IXS_CHECK_UNKNOWN;
  expanded_lhs = simp_simplify_bounds(state->ctx, expanded_lhs, state->bounds);
  expanded_rhs = simp_simplify_bounds(state->ctx, expanded_rhs, state->bounds);
  if (!expanded_lhs || !expanded_rhs) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (ixs_node_is_sentinel(expanded_lhs) || ixs_node_is_sentinel(expanded_rhs))
    return IXS_CHECK_UNKNOWN;
  if (expanded_lhs == expanded_rhs)
    return IXS_CHECK_TRUE;
  result = equivalence_difference(state, expanded_lhs, expanded_rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  result = equivalence_mod_shifts(state, expanded_lhs, expanded_rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  if (ixs_node_is_bool_valued(expanded_lhs) &&
      ixs_node_is_bool_valued(expanded_rhs))
    return equivalence_predicate_shapes(state, expanded_lhs, expanded_rhs,
                                        depth);
  return IXS_CHECK_UNKNOWN;
}

static ixs_check_result equivalence_core(equivalence_state *state,
                                         ixs_node *lhs, ixs_node *rhs,
                                         unsigned depth) {
  ixs_node *simplified_lhs;
  ixs_node *simplified_rhs;
  ixs_check_result left_truth;
  ixs_check_result right_truth;
  ixs_check_result result;
  bool predicates;

  if (depth >= EQUIVALENCE_DEPTH_LIMIT ||
      state->visited >= EQUIVALENCE_VISIT_LIMIT) {
    state->limited = true;
    return IXS_CHECK_UNKNOWN;
  }
  state->visited++;
  if (lhs == rhs)
    return IXS_CHECK_TRUE;

  simplified_lhs = simp_simplify_bounds(state->ctx, lhs, state->bounds);
  simplified_rhs = simp_simplify_bounds(state->ctx, rhs, state->bounds);
  if (!simplified_lhs || !simplified_rhs) {
    state->oom = true;
    return IXS_CHECK_UNKNOWN;
  }
  if (ixs_node_is_sentinel(simplified_lhs) ||
      ixs_node_is_sentinel(simplified_rhs))
    return IXS_CHECK_UNKNOWN;
  if (simplified_lhs == simplified_rhs)
    return IXS_CHECK_TRUE;

  predicates = ixs_node_is_bool_valued(simplified_lhs) &&
               ixs_node_is_bool_valued(simplified_rhs);
  if (predicates) {
    left_truth = predicate_query_eval(state->bounds, simplified_lhs);
    right_truth = predicate_query_eval(state->bounds, simplified_rhs);
    if (left_truth != IXS_CHECK_UNKNOWN && right_truth != IXS_CHECK_UNKNOWN)
      return left_truth == right_truth ? IXS_CHECK_TRUE : IXS_CHECK_FALSE;
  }

  result = equivalence_difference(state, simplified_lhs, simplified_rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  result = equivalence_mod_shifts(state, simplified_lhs, simplified_rhs);
  if (result != IXS_CHECK_UNKNOWN)
    return result;
  return equivalence_expanded(state, simplified_lhs, simplified_rhs, depth);
}

ixs_check_result ixs_check_predicate_facts(ixs_facts *facts,
                                           ixs_node *predicate) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  ixs_node *simplified;
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  bool old_oom;
  if (!facts_bind(facts, &binding, &ctx))
    return IXS_CHECK_UNKNOWN;
  if (!facts_ready(facts))
    goto cleanup;
  if (!facts_query_node_ok(ctx, predicate, "predicate"))
    goto cleanup;
  if (!ixs_node_is_pred_kind(predicate)) {
    ixs_ctx_push_error(ctx, "predicate: expression is not a predicate tree");
    goto cleanup;
  }
  if (ixs_bounds_has_empty(&facts->bounds))
    goto cleanup;

  mark = ixs_arena_save(&ctx->scratch);
  old_oom = facts->bounds.oom;
  simplified = simp_simplify_bounds(ctx, predicate, &facts->bounds);
  if (simplified && !ixs_node_is_sentinel(simplified))
    result = predicate_query_eval(&facts->bounds, simplified);
  if (!simplified || (!old_oom && facts->bounds.oom)) {
    result = IXS_CHECK_UNKNOWN;
    bounds_cache_clear(&facts->bounds);
  }
  facts->bounds.oom = old_oom;
  ixs_arena_restore(&ctx->scratch, mark);

cleanup:
  ixs_session_unbind(&binding);
  return result;
}

ixs_check_result ixs_equivalent_facts(ixs_facts *facts, ixs_node *lhs,
                                      ixs_node *rhs) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_arena_mark mark;
  equivalence_state state;
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  bool old_oom;
  if (!facts_bind(facts, &binding, &ctx))
    return IXS_CHECK_UNKNOWN;
  if (!facts_ready(facts))
    goto cleanup;
  if (!facts_query_node_ok(ctx, lhs, "equivalence") ||
      !facts_query_node_ok(ctx, rhs, "equivalence"))
    goto cleanup;
  if (ixs_bounds_has_empty(&facts->bounds))
    goto cleanup;

  mark = ixs_arena_save(&ctx->scratch);
  old_oom = facts->bounds.oom;
  if (ixs_bounds_check_defined(&facts->bounds, lhs) != IXS_CHECK_TRUE ||
      ixs_bounds_check_defined(&facts->bounds, rhs) != IXS_CHECK_TRUE)
    goto restore;
  state.ctx = ctx;
  state.bounds = &facts->bounds;
  state.visited = 0;
  state.limited = false;
  state.oom = false;
  result = equivalence_core(&state, lhs, rhs, 0);
  if (state.oom || state.limited || (!old_oom && facts->bounds.oom))
    result = IXS_CHECK_UNKNOWN;

restore:
  if (!old_oom && facts->bounds.oom)
    bounds_cache_clear(&facts->bounds);
  facts->bounds.oom = old_oom;
  ixs_arena_restore(&ctx->scratch, mark);

cleanup:
  ixs_session_unbind(&binding);
  return result;
}

#define ALGEBRA_QUERY_STACK_LIMIT 1024u
#define ALGEBRA_QUERY_VISIT_LIMIT 8192u

typedef struct {
  ixs_session_binding binding;
  ixs_facts *facts;
  ixs_ctx *ctx;
  ixs_arena_mark scratch_mark;
  ixs_arena_mark diag_mark;
  const char **saved_errors;
  size_t saved_nerrors;
  size_t saved_errors_cap;
  bool old_oom;
  bool bound;
  bool active;
} algebra_query_scope;

typedef struct {
  size_t visited;
  bool limited;
} algebra_walk_state;

static bool algebra_query_begin(ixs_facts *facts, ixs_node *const *nodes,
                                size_t nnodes, const char *query,
                                bool outputs_ok, const char *output_error,
                                algebra_query_scope *scope) {
  size_t i;
  memset(scope, 0, sizeof(*scope));
  if (!facts_bind(facts, &scope->binding, &scope->ctx))
    return false;
  scope->facts = facts;
  scope->bound = true;
  if (!facts_ready(facts)) {
    ixs_ctx_push_error(scope->ctx, "%s: fact set is unusable", query);
    goto fail;
  }
  if (!outputs_ok) {
    ixs_ctx_push_error(scope->ctx, "%s: %s", query, output_error);
    goto fail;
  }
  for (i = 0; i < nnodes; i++) {
    if (!facts_query_node_ok(scope->ctx, nodes[i], query))
      goto fail;
  }
  if (ixs_bounds_has_empty(&facts->bounds))
    goto fail;
  return true;

fail:
  ixs_session_unbind(&scope->binding);
  scope->bound = false;
  return false;
}

static void algebra_query_start(algebra_query_scope *scope) {
  scope->scratch_mark = ixs_arena_save(&scope->ctx->scratch);
  scope->diag_mark = ixs_arena_save(&scope->ctx->diag);
  scope->saved_errors = scope->ctx->errors;
  scope->saved_nerrors = scope->ctx->nerrors;
  scope->saved_errors_cap = scope->ctx->errors_cap;
  scope->old_oom = scope->facts->bounds.oom;
  scope->active = true;
}

static bool algebra_query_finish(algebra_query_scope *scope, bool success) {
  if (scope->active) {
    if (!scope->old_oom && scope->facts->bounds.oom) {
      bounds_cache_clear(&scope->facts->bounds);
      success = false;
    }
    scope->facts->bounds.oom = scope->old_oom;
    ixs_arena_restore(&scope->ctx->scratch, scope->scratch_mark);
    ixs_arena_restore(&scope->ctx->diag, scope->diag_mark);
    scope->ctx->errors = scope->saved_errors;
    scope->ctx->nerrors = scope->saved_nerrors;
    scope->ctx->errors_cap = scope->saved_errors_cap;
  }
  if (scope->bound)
    ixs_session_unbind(&scope->binding);
  return success;
}

static ixs_node *algebra_query_normalize(algebra_query_scope *scope,
                                         ixs_node *expr) {
  expr = simp_simplify_bounds(scope->ctx, expr, &scope->facts->bounds);
  if (!expr || ixs_node_is_sentinel(expr))
    return NULL;
  expr = expand_impl(scope->ctx, expr);
  if (!expr || ixs_node_is_sentinel(expr))
    return NULL;
  expr = simp_simplify_bounds(scope->ctx, expr, &scope->facts->bounds);
  if (!expr || ixs_node_is_sentinel(expr))
    return NULL;
  return expr;
}

static bool algebra_contains_node(ixs_node *root, ixs_node *target,
                                  algebra_walk_state *state, bool *contains) {
  defined_depth_frame stack[ALGEBRA_QUERY_STACK_LIMIT];
  size_t depth = 0;
  uint32_t nchildren;
  *contains = false;
  if (!root || !target || state->limited ||
      state->visited >= ALGEBRA_QUERY_VISIT_LIMIT) {
    state->limited = true;
    return false;
  }
  state->visited++;
  if (root == target) {
    *contains = true;
    return true;
  }
  if (!defined_child_count(root, &nchildren))
    return false;
  if (nchildren == 0)
    return true;
  stack[depth].node = root;
  stack[depth].next_child = 0;
  stack[depth].nchildren = nchildren;
  depth++;

  while (depth > 0) {
    defined_depth_frame *frame = &stack[depth - 1u];
    ixs_node *child;
    if (frame->next_child >= frame->nchildren) {
      depth--;
      continue;
    }
    child = defined_child_at(frame->node, frame->next_child++);
    if (!child || state->visited >= ALGEBRA_QUERY_VISIT_LIMIT) {
      state->limited = true;
      return false;
    }
    state->visited++;
    if (child == target) {
      *contains = true;
      return true;
    }
    if (!defined_child_count(child, &nchildren))
      return false;
    if (nchildren == 0)
      continue;
    if (depth >= ALGEBRA_QUERY_STACK_LIMIT) {
      state->limited = true;
      return false;
    }
    stack[depth].node = child;
    stack[depth].next_child = 0;
    stack[depth].nchildren = nchildren;
    depth++;
  }
  return true;
}

static bool algebra_scalar_symbol(ixs_ctx *ctx, ixs_node *expr,
                                  ixs_node *symbol, ixs_node **coefficient) {
  if (expr == symbol) {
    *coefficient = ctx->node_one;
    return true;
  }
  if (expr->tag == IXS_MUL && expr->u.mul.nfactors == 1 &&
      expr->u.mul.factors[0].base == symbol &&
      expr->u.mul.factors[0].exp == 1) {
    *coefficient = expr->u.mul.coeff;
    return true;
  }
  return false;
}

static bool algebra_affine_extract(ixs_ctx *ctx, ixs_node *expr,
                                   ixs_node *symbol, ixs_node **coefficient,
                                   ixs_node **residual) {
  algebra_walk_state walk = {0, false};
  ixs_node *symbol_coeff;
  bool contains;
  uint32_t i;

  if (algebra_scalar_symbol(ctx, expr, symbol, &symbol_coeff)) {
    *coefficient = symbol_coeff;
    *residual = ctx->node_zero;
    return true;
  }
  if (expr->tag != IXS_ADD) {
    if (!algebra_contains_node(expr, symbol, &walk, &contains) || contains)
      return false;
    *coefficient = ctx->node_zero;
    *residual = expr;
    return true;
  }

  *coefficient = ctx->node_zero;
  *residual = expr->u.add.coeff;
  for (i = 0; i < expr->u.add.nterms; i++) {
    ixs_node *term = expr->u.add.terms[i].term;
    ixs_node *term_coeff = expr->u.add.terms[i].coeff;
    ixs_node *scaled;
    if (algebra_scalar_symbol(ctx, term, symbol, &symbol_coeff)) {
      scaled = simp_mul(ctx, term_coeff, symbol_coeff);
      if (!scaled || ixs_node_is_sentinel(scaled))
        return false;
      *coefficient = simp_add(ctx, *coefficient, scaled);
      if (!*coefficient || ixs_node_is_sentinel(*coefficient))
        return false;
      continue;
    }
    if (!algebra_contains_node(term, symbol, &walk, &contains) || contains)
      return false;
    scaled = simp_mul(ctx, term_coeff, term);
    if (!scaled || ixs_node_is_sentinel(scaled))
      return false;
    *residual = simp_add(ctx, *residual, scaled);
    if (!*residual || ixs_node_is_sentinel(*residual))
      return false;
  }
  return ixs_node_is_const(*coefficient);
}

bool ixs_constant_difference_facts(ixs_facts *facts, ixs_node *lhs,
                                   ixs_node *rhs, int64_t *delta) {
  algebra_query_scope scope;
  ixs_node *nodes[2] = {lhs, rhs};
  ixs_node *difference;
  int64_t result = 0;
  bool ok = false;
  if (delta)
    *delta = 0;
  if (!algebra_query_begin(facts, nodes, 2, "constant difference",
                           delta != NULL, "NULL output", &scope))
    return false;
  algebra_query_start(&scope);
  if (ixs_bounds_check_defined(&facts->bounds, lhs) != IXS_CHECK_TRUE ||
      ixs_bounds_check_defined(&facts->bounds, rhs) != IXS_CHECK_TRUE)
    goto cleanup;
  difference = simp_sub(scope.ctx, lhs, rhs);
  if (!difference || ixs_node_is_sentinel(difference))
    goto cleanup;
  difference = algebra_query_normalize(&scope, difference);
  if (!difference)
    goto cleanup;
  ok = bounds_exact_integer_difference(&facts->bounds, difference, &result);

cleanup:
  ok = algebra_query_finish(&scope, ok);
  if (ok)
    *delta = result;
  return ok;
}

bool ixs_affine_decompose_facts(ixs_facts *facts, ixs_node *expr,
                                ixs_node *symbol, ixs_node **coefficient,
                                ixs_node **residual) {
  algebra_query_scope scope;
  ixs_node *nodes[2] = {expr, symbol};
  ixs_node *result_coefficient = NULL;
  ixs_node *result_residual = NULL;
  bool outputs_ok = coefficient && residual && coefficient != residual;
  bool ok = false;
  if (coefficient)
    *coefficient = NULL;
  if (residual)
    *residual = NULL;
  if (!algebra_query_begin(facts, nodes, 2, "affine decomposition", outputs_ok,
                           "outputs must be non-NULL and distinct", &scope))
    return false;
  if (symbol->tag != IXS_SYM) {
    ixs_ctx_push_error(scope.ctx,
                       "affine decomposition: expression must be a symbol");
    return algebra_query_finish(&scope, false);
  }
  algebra_query_start(&scope);
  if (ixs_bounds_check_defined(&facts->bounds, expr) != IXS_CHECK_TRUE)
    goto cleanup;
  expr = algebra_query_normalize(&scope, expr);
  if (!expr)
    goto cleanup;
  ok = algebra_affine_extract(scope.ctx, expr, symbol, &result_coefficient,
                              &result_residual);

cleanup:
  ok = algebra_query_finish(&scope, ok);
  if (ok) {
    *coefficient = result_coefficient;
    *residual = result_residual;
  }
  return ok;
}

bool ixs_decompose_exact_quotient_facts(ixs_facts *facts, ixs_node *expr,
                                        ixs_node **numerator,
                                        ixs_node **denominator) {
  algebra_query_scope scope;
  ixs_node *nodes[1] = {expr};
  ixs_node *result_numerator = NULL;
  ixs_node *result_denominator = NULL;
  bool outputs_ok = numerator && denominator && numerator != denominator;
  bool ok = false;
  if (numerator)
    *numerator = NULL;
  if (denominator)
    *denominator = NULL;
  if (!algebra_query_begin(facts, nodes, 1, "exact quotient decomposition",
                           outputs_ok, "outputs must be non-NULL and distinct",
                           &scope))
    return false;
  algebra_query_start(&scope);
  expr = simp_simplify_bounds(scope.ctx, expr, &facts->bounds);
  if (!expr || ixs_node_is_sentinel(expr))
    goto cleanup;
  ok = simp_decompose_exact_quotient(scope.ctx, expr, &result_numerator,
                                     &result_denominator);

cleanup:
  ok = algebra_query_finish(&scope, ok);
  if (ok) {
    *numerator = result_numerator;
    *denominator = result_denominator;
  }
  return ok;
}

bool ixs_finite_difference_facts(ixs_facts *facts, ixs_node *expr,
                                 ixs_node *symbol, ixs_node *step,
                                 ixs_node **difference) {
  algebra_query_scope scope;
  algebra_walk_state walk = {0, false};
  ixs_node *nodes[3] = {expr, symbol, step};
  ixs_node *shifted_symbol;
  ixs_node *shifted_expr;
  ixs_node *result = NULL;
  bool contains;
  bool ok = false;
  if (difference)
    *difference = NULL;
  if (!algebra_query_begin(facts, nodes, 3, "finite difference",
                           difference != NULL, "NULL output", &scope))
    return false;
  if (symbol->tag != IXS_SYM) {
    ixs_ctx_push_error(scope.ctx,
                       "finite difference: expression must be a symbol");
    return algebra_query_finish(&scope, false);
  }
  algebra_query_start(&scope);
  if (ixs_bounds_check_defined(&facts->bounds, expr) != IXS_CHECK_TRUE ||
      ixs_bounds_check_defined(&facts->bounds, step) != IXS_CHECK_TRUE)
    goto cleanup;
  if (!algebra_contains_node(step, symbol, &walk, &contains) || contains)
    goto cleanup;
  shifted_symbol = simp_add(scope.ctx, symbol, step);
  if (!shifted_symbol || ixs_node_is_sentinel(shifted_symbol))
    goto cleanup;
  shifted_expr = simp_subs(scope.ctx, expr, symbol, shifted_symbol);
  if (!shifted_expr || ixs_node_is_sentinel(shifted_expr) ||
      ixs_bounds_check_defined(&facts->bounds, shifted_expr) != IXS_CHECK_TRUE)
    goto cleanup;
  result = simp_sub(scope.ctx, shifted_expr, expr);
  if (!result || ixs_node_is_sentinel(result))
    goto cleanup;
  result = algebra_query_normalize(&scope, result);
  ok = result != NULL;

cleanup:
  ok = algebra_query_finish(&scope, ok);
  if (ok)
    *difference = result;
  return ok;
}

static ixs_node *algebra_add_without_constant(ixs_ctx *ctx, ixs_node *expr) {
  ixs_node *residual = ctx->node_zero;
  uint32_t i;
  for (i = 0; i < expr->u.add.nterms; i++) {
    ixs_node *term =
        simp_mul(ctx, expr->u.add.terms[i].coeff, expr->u.add.terms[i].term);
    if (!term || ixs_node_is_sentinel(term))
      return NULL;
    residual = simp_add(ctx, residual, term);
    if (!residual || ixs_node_is_sentinel(residual))
      return NULL;
  }
  return residual;
}

bool ixs_split_additive_constant_facts(ixs_facts *facts, ixs_node *expr,
                                       ixs_node **residual, int64_t *constant) {
  algebra_query_scope scope;
  ixs_node *nodes[1] = {expr};
  ixs_node *result_residual = NULL;
  int64_t result_constant = 0;
  int64_t q;
  bool outputs_ok = residual && constant;
  bool ok = false;
  if (residual)
    *residual = NULL;
  if (constant)
    *constant = 0;
  if (!algebra_query_begin(facts, nodes, 1, "additive constant", outputs_ok,
                           "outputs must be non-NULL", &scope))
    return false;
  algebra_query_start(&scope);
  if (ixs_bounds_check_defined(&facts->bounds, expr) != IXS_CHECK_TRUE)
    goto cleanup;
  expr = algebra_query_normalize(&scope, expr);
  if (!expr)
    goto cleanup;
  if (ixs_node_is_const(expr)) {
    ixs_node_get_rat(expr, &result_constant, &q);
    if (q != 1)
      goto cleanup;
    result_residual = scope.ctx->node_zero;
  } else if (expr->tag == IXS_ADD) {
    ixs_node_get_rat(expr->u.add.coeff, &result_constant, &q);
    if (q != 1)
      goto cleanup;
    result_residual = algebra_add_without_constant(scope.ctx, expr);
    if (!result_residual)
      goto cleanup;
  } else {
    result_residual = expr;
  }
  ok = true;

cleanup:
  ok = algebra_query_finish(&scope, ok);
  if (ok) {
    *residual = result_residual;
    *constant = result_constant;
  }
  return ok;
}

ixs_check_result ixs_check_facts(ixs_facts *facts, ixs_node *expr) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  if (!facts_bind(facts, &binding, &ctx))
    return IXS_CHECK_UNKNOWN;
  if (facts_ready(facts) && facts_node_ok(ctx, expr))
    result = ixs_bounds_check(&facts->bounds, expr);
  ixs_session_unbind(&binding);
  return result;
}

ixs_check_result ixs_check_integer_valued_facts(ixs_facts *facts,
                                                ixs_node *expr) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  if (!facts_bind(facts, &binding, &ctx))
    return IXS_CHECK_UNKNOWN;
  if (facts_ready(facts) && facts_node_ok(ctx, expr))
    result = ixs_bounds_check_integer_valued(&facts->bounds, expr);
  ixs_session_unbind(&binding);
  return result;
}

ixs_check_result ixs_check_defined_facts(ixs_facts *facts, ixs_node *expr) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  if (!facts_bind(facts, &binding, &ctx))
    return IXS_CHECK_UNKNOWN;
  if (facts_ready(facts) && facts_node_ok(ctx, expr))
    result = ixs_bounds_check_defined(&facts->bounds, expr);
  ixs_session_unbind(&binding);
  return result;
}

ixs_check_result ixs_check_divisible_facts(ixs_facts *facts, ixs_node *expr,
                                           int64_t modulus) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  if (!facts_bind(facts, &binding, &ctx))
    return IXS_CHECK_UNKNOWN;
  if (!facts_ready(facts))
    goto cleanup;
  if (modulus == 0) {
    ixs_ctx_push_error(ctx, "divisibility: modulus must be nonzero");
    goto cleanup;
  }
  if (facts_node_ok(ctx, expr))
    result = ixs_bounds_check_divisible(&facts->bounds, expr, modulus);

cleanup:
  ixs_session_unbind(&binding);
  return result;
}

static ixs_exact_divide_result
exact_divide_result(ixs_exact_divide_status status, ixs_node *quotient) {
  ixs_exact_divide_result result;
  result.status = status;
  result.quotient = quotient;
  return result;
}

static ixs_exact_divide_result exact_divide_error(ixs_ctx *ctx,
                                                  const char *message) {
  if (ctx && message)
    ixs_ctx_push_error(ctx, "exact divide: %s", message);
  return exact_divide_result(IXS_EXACT_DIVIDE_ERROR, NULL);
}

static ixs_node *exact_divide_simplify_facts(ixs_facts *facts, ixs_ctx *ctx,
                                             ixs_node *expr, bool *oom) {
  /* Fact simplification is a proof probe; discard scratch and diagnostics. */
  ixs_arena_mark scratch_mark = ixs_arena_save(&ctx->scratch);
  ixs_arena_mark diag_mark = ixs_arena_save(&ctx->diag);
  const char **saved_errors = ctx->errors;
  size_t saved_nerrors = ctx->nerrors;
  size_t saved_errors_cap = ctx->errors_cap;
  bool old_oom = facts->bounds.oom;
  ixs_node *result = simp_simplify_bounds(ctx, expr, &facts->bounds);

  *oom = !result || (!old_oom && facts->bounds.oom);
  if (*oom)
    bounds_cache_clear(&facts->bounds);
  facts->bounds.oom = old_oom;
  ixs_arena_restore(&ctx->scratch, scratch_mark);
  ixs_arena_restore(&ctx->diag, diag_mark);
  ctx->errors = saved_errors;
  ctx->nerrors = saved_nerrors;
  ctx->errors_cap = saved_errors_cap;
  return result && !ixs_node_is_sentinel(result) ? result : expr;
}

ixs_exact_divide_result
ixs_try_exact_divide_facts(ixs_facts *facts, ixs_node *expr, int64_t divisor) {
  ixs_session_binding binding;
  ixs_check_result proof;
  ixs_node *input_expr;
  ixs_node *divisor_node;
  ixs_node *quotient;
  ixs_ctx *ctx;
  bool old_bounds_oom;
  bool defined_oom;
  bool oom;

  if (!facts_bind(facts, &binding, &ctx))
    return exact_divide_result(IXS_EXACT_DIVIDE_ERROR, NULL);
  if (!facts_ready(facts)) {
    ixs_exact_divide_result result =
        exact_divide_error(ctx, "fact set is unusable");
    ixs_session_unbind(&binding);
    return result;
  }
  if (!expr) {
    ixs_exact_divide_result result = exact_divide_error(ctx, "NULL expression");
    ixs_session_unbind(&binding);
    return result;
  }
  if (ixs_node_is_sentinel(expr)) {
    ixs_exact_divide_result result =
        exact_divide_error(ctx, "sentinel expression is not accepted");
    ixs_session_unbind(&binding);
    return result;
  }
  if (!ixs_ctx_owns_node(ctx, expr)) {
    ixs_exact_divide_result result =
        exact_divide_error(ctx, "expression belongs to a different context");
    ixs_session_unbind(&binding);
    return result;
  }
  if (divisor == 0) {
    ixs_exact_divide_result result =
        exact_divide_error(ctx, "divisor must be nonzero");
    ixs_session_unbind(&binding);
    return result;
  }

  input_expr = expr;
  expr = exact_divide_simplify_facts(facts, ctx, expr, &oom);
  if (oom) {
    ixs_exact_divide_result result = exact_divide_error(ctx, "out of memory");
    ixs_session_unbind(&binding);
    return result;
  }
  old_bounds_oom = facts->bounds.oom;
  proof = ixs_bounds_check_divisible(&facts->bounds, expr, divisor);
  if (facts->bounds.oom) {
    if (!old_bounds_oom)
      bounds_cache_clear(&facts->bounds);
    facts->bounds.oom = old_bounds_oom;
    ixs_exact_divide_result result = exact_divide_error(ctx, "out of memory");
    ixs_session_unbind(&binding);
    return result;
  }
  if (proof == IXS_CHECK_UNKNOWN) {
    ixs_session_unbind(&binding);
    return exact_divide_result(IXS_EXACT_DIVIDE_UNKNOWN, NULL);
  }
  if (!ixs_node_is_known_total(input_expr)) {
    ixs_check_result defined =
        bounds_check_defined_status(&facts->bounds, input_expr, &defined_oom);
    if (defined_oom) {
      if (!old_bounds_oom && facts->bounds.oom) {
        bounds_cache_clear(&facts->bounds);
        facts->bounds.oom = old_bounds_oom;
      }
      ixs_exact_divide_result result = exact_divide_error(ctx, "out of memory");
      ixs_session_unbind(&binding);
      return result;
    }
    if (defined != IXS_CHECK_TRUE) {
      ixs_session_unbind(&binding);
      return exact_divide_result(IXS_EXACT_DIVIDE_UNKNOWN, NULL);
    }
  }
  if (proof == IXS_CHECK_FALSE) {
    ixs_session_unbind(&binding);
    return exact_divide_result(IXS_EXACT_DIVIDE_NOT_EXACT, NULL);
  }

  divisor_node = ixs_node_int(ctx, divisor);
  if (!divisor_node) {
    ixs_exact_divide_result result = exact_divide_error(ctx, "out of memory");
    ixs_session_unbind(&binding);
    return result;
  }
  quotient = simp_div(ctx, expr, divisor_node);
  if (!quotient) {
    ixs_exact_divide_result result = exact_divide_error(ctx, "out of memory");
    ixs_session_unbind(&binding);
    return result;
  }
  if (ixs_node_is_sentinel(quotient)) {
    ixs_exact_divide_result result =
        exact_divide_error(ctx, "quotient is not representable");
    ixs_session_unbind(&binding);
    return result;
  }
  quotient = expand_impl(ctx, quotient);
  if (!quotient) {
    ixs_exact_divide_result result = exact_divide_error(ctx, "out of memory");
    ixs_session_unbind(&binding);
    return result;
  }
  if (ixs_node_is_sentinel(quotient)) {
    ixs_exact_divide_result result =
        exact_divide_error(ctx, "quotient expansion failed");
    ixs_session_unbind(&binding);
    return result;
  }

  ixs_session_unbind(&binding);
  return exact_divide_result(IXS_EXACT_DIVIDE_PROVEN, quotient);
}

static ixs_pow2_fact bounds_pow2_fact_from_int64(int64_t value) {
  uint64_t u;
  if (value == 0)
    return IXS_POW2_OR_ZERO;
  if (value < 0)
    return IXS_POW2_UNKNOWN;
  u = (uint64_t)value;
  return (u & (u - 1u)) == 0 ? IXS_POW2_POSITIVE : IXS_POW2_UNKNOWN;
}

ixs_pow2_fact ixs_get_pow2_fact_facts(ixs_facts *facts, ixs_node *expr) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_bitfacts bits;
  ixs_interval iv;
  int64_t exact;
  ixs_pow2_fact result = IXS_POW2_UNKNOWN;
  if (!facts_bind(facts, &binding, &ctx))
    return IXS_POW2_UNKNOWN;
  if (!facts_ready(facts) || !facts_node_ok(ctx, expr) ||
      ixs_bounds_has_empty(&facts->bounds))
    goto cleanup;
  if (ixs_bounds_get_bitfacts(&facts->bounds, expr, &bits))
    result = bits.pow2;
  if (result == IXS_POW2_UNKNOWN) {
    iv = ixs_bounds_get(&facts->bounds, expr);
    if (ixs_interval_is_point_int(iv, &exact))
      result = bounds_pow2_fact_from_int64(exact);
  }

cleanup:
  ixs_session_unbind(&binding);
  return result;
}

bool ixs_get_known_bits_facts(ixs_facts *facts, ixs_node *expr,
                              ixs_known_bits *out) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_bitfacts bits;
  bool ok = false;
  if (out) {
    out->known_zero = 0;
    out->known_one = 0;
    out->pow2 = IXS_POW2_UNKNOWN;
  }
  if (!facts_bind(facts, &binding, &ctx))
    return false;
  if (!out) {
    ixs_ctx_push_error(ctx, "known bits: NULL output");
    goto cleanup;
  }
  if (!facts_ready(facts)) {
    ixs_ctx_push_error(ctx, "known bits: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, expr, "known bits") ||
      ixs_bounds_has_empty(&facts->bounds))
    goto cleanup;

  bitfacts_unknown(&bits);
  if (ixs_bounds_check_integer_valued(&facts->bounds, expr) == IXS_CHECK_TRUE)
    (void)ixs_bounds_get_bitfacts(&facts->bounds, expr, &bits);
  if (facts->bounds.oom) {
    ixs_ctx_push_error(ctx, "known bits: out of memory");
    goto cleanup;
  }
  out->known_zero = bits.known_zero;
  out->known_one = bits.known_one;
  out->pow2 = bits.pow2;
  ok = true;

cleanup:
  ixs_session_unbind(&binding);
  return ok;
}

bool ixs_get_symbol_congruence_facts(ixs_facts *facts, ixs_node *symbol,
                                     int64_t *modulus, int64_t *residue) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  int64_t stored_modulus;
  int64_t stored_residue;
  bool ok = false;
  if (modulus)
    *modulus = 0;
  if (residue)
    *residue = 0;
  if (!facts_bind(facts, &binding, &ctx))
    return false;
  if (!modulus || !residue || modulus == residue) {
    ixs_ctx_push_error(
        ctx, "symbol congruence: outputs must be non-NULL and distinct");
    goto cleanup;
  }
  if (!facts_ready(facts)) {
    ixs_ctx_push_error(ctx, "symbol congruence: fact set is unusable");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, symbol, "symbol congruence") ||
      ixs_bounds_has_empty(&facts->bounds))
    goto cleanup;
  if (symbol->tag != IXS_SYM) {
    ixs_ctx_push_error(ctx, "symbol congruence: expression must be a symbol");
    goto cleanup;
  }
  if (!ixs_bounds_get_modrem(&facts->bounds, symbol->u.name, &stored_modulus,
                             &stored_residue))
    goto cleanup;
  *modulus = stored_modulus;
  *residue = stored_residue;
  ok = true;

cleanup:
  ixs_session_unbind(&binding);
  return ok;
}

ixs_check_result ixs_check_congruent_facts(ixs_facts *facts, ixs_node *expr,
                                           int64_t modulus, int64_t residue) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_check_result result = IXS_CHECK_UNKNOWN;
  if (!facts_bind(facts, &binding, &ctx))
    return IXS_CHECK_UNKNOWN;
  if (!facts_ready(facts)) {
    ixs_ctx_push_error(ctx, "congruence: fact set is unusable");
    goto cleanup;
  }
  if (modulus == 0) {
    ixs_ctx_push_error(ctx, "congruence: modulus must be nonzero");
    goto cleanup;
  }
  if (!facts_query_node_ok(ctx, expr, "congruence") ||
      ixs_bounds_has_empty(&facts->bounds))
    goto cleanup;
  result = ixs_bounds_check_congruent(&facts->bounds, expr, modulus, residue);
  if (facts->bounds.oom) {
    ixs_ctx_push_error(ctx, "congruence: out of memory");
    result = IXS_CHECK_UNKNOWN;
  }

cleanup:
  ixs_session_unbind(&binding);
  return result;
}

bool ixs_range_facts(ixs_facts *facts, ixs_node *expr, ixs_range_result *out) {
  ixs_session_binding binding;
  ixs_ctx *ctx;
  ixs_interval iv;
  bool ok = false;
  if (!out)
    return false;
  out->has_lower = false;
  out->has_upper = false;
  out->lower_p = 0;
  out->lower_q = 1;
  out->upper_p = 0;
  out->upper_q = 1;
  if (!facts_bind(facts, &binding, &ctx))
    return false;
  if (!facts_ready(facts) || !facts_node_ok(ctx, expr) ||
      ixs_bounds_has_empty(&facts->bounds))
    goto cleanup;
  iv = ixs_bounds_get(&facts->bounds, expr);
  if (!iv.valid || ixs_interval_is_empty(iv))
    goto cleanup;
  interval_to_range_result(iv, out);
  ok = true;

cleanup:
  ixs_session_unbind(&binding);
  return ok;
}

IXS_STATIC bool ixs_bounds_get_modrem(ixs_bounds *b, const char *name,
                                      int64_t *mod, int64_t *rem) {
  ixs_var_bound *v;
  if (!mod || !rem)
    return false;
  v = find_var(b, name);
  if (!v || v->modulus <= 0)
    return false;
  *mod = v->modulus;
  *rem = v->remainder;
  return true;
}
