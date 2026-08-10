/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "bounds_store.h"
#include "bounds_query.h"
#include "bounds_range.h"
#include "bounds_relation.h"
#include "hash.h"
#include <assert.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>

#define BOUNDS_VAR_INDEX_INIT_CAP 8u
#define BOUNDS_EXPR_INDEX_INIT_CAP 8u
#define BOUNDS_NONZERO_INLINE_COUNT 4u
#define BOUNDS_NONZERO_INDEX_INIT_CAP 8u
#define BOUNDS_INIT_CAP 16u

IXS_STATIC bool bounds_store_init(ixs_bounds *b, ixs_arena *scratch) {
  b->ctx = NULL;
  b->store_ctx = NULL;
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
  b->mod_inverse_heads = NULL;
  b->mod_inverse_head_cap = 0;
  b->mod_inverse_watchers = NULL;
  b->nmod_inverse_watchers = 0;
  b->mod_inverse_watcher_cap = 0;
  b->mod_inverse_watch_visits = 0;
  b->nonzero = NULL;
  b->nonzero_index = NULL;
  b->nnonzero = 0;
  b->nonzero_cap = 0;
  b->nonzero_index_cap = 0;
  b->has_modrem = false;
  b->contradiction = false;
  b->semantic_changed = NULL;
  return b->vars != NULL;
}

IXS_STATIC void bounds_store_bind(ixs_bounds *b, ixs_ctx *ctx,
                                  ixs_arena *scratch) {
  b->ctx = ctx;
  b->store_ctx = ctx;
  b->scratch = scratch;
}

IXS_STATIC void bounds_store_retarget_scratch(ixs_bounds *b,
                                              ixs_arena *scratch) {
  b->scratch = scratch;
}

IXS_STATIC ixs_ctx *bounds_store_swap_active_context(ixs_bounds *b,
                                                     ixs_ctx *ctx) {
  ixs_ctx *old = b->ctx;
  b->ctx = ctx;
  return old;
}

IXS_STATIC bool *bounds_store_swap_change_observer(ixs_bounds *b,
                                                   bool *observer) {
  bool *old = b->semantic_changed;
  b->semantic_changed = observer;
  return old;
}

IXS_STATIC bool bounds_store_fork_begin(ixs_bounds *dst,
                                        const ixs_bounds *src) {
  dst->ctx = src->ctx;
  dst->store_ctx = src->store_ctx;
  dst->scratch = src->scratch;
  dst->nvars = src->nvars;
  dst->cap = src->nvars ? src->nvars : 1u;
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
  dst->mod_inverse_heads = NULL;
  dst->mod_inverse_head_cap = src->mod_inverse_head_cap;
  dst->mod_inverse_watchers = NULL;
  dst->nmod_inverse_watchers = src->nmod_inverse_watchers;
  dst->mod_inverse_watcher_cap = src->nmod_inverse_watchers;
  dst->mod_inverse_watch_visits = 0;
  dst->nnonzero = src->nnonzero;
  dst->nonzero_cap = src->nnonzero;
  dst->nonzero = NULL;
  dst->nonzero_index = NULL;
  dst->nonzero_index_cap =
      src->nnonzero > BOUNDS_NONZERO_INLINE_COUNT ? src->nonzero_index_cap : 0;
  dst->has_modrem = src->has_modrem;
  dst->contradiction = src->contradiction;
  dst->semantic_changed = NULL;
  return true;
}

IXS_STATIC bool bounds_store_fork_var_index(ixs_bounds *dst,
                                            const ixs_bounds *src) {
  if (!src->nvars)
    return true;
  if (!src->var_index || !src->var_index_cap ||
      src->var_index_cap > SIZE_MAX / sizeof(*dst->var_index))
    return false;
  dst->var_index = ixs_arena_alloc(dst->scratch,
                                   src->var_index_cap * sizeof(*dst->var_index),
                                   sizeof(void *));
  if (!dst->var_index)
    return false;
  memcpy(dst->var_index, src->var_index,
         src->var_index_cap * sizeof(*src->var_index));
  return true;
}

IXS_STATIC bool bounds_store_fork_mod_inverse(ixs_bounds *dst,
                                              const ixs_bounds *src) {
  if (src->mod_inverse_head_cap) {
    if (!src->mod_inverse_heads ||
        src->mod_inverse_head_cap > SIZE_MAX / sizeof(*dst->mod_inverse_heads))
      return false;
    dst->mod_inverse_heads = ixs_arena_alloc(
        dst->scratch,
        src->mod_inverse_head_cap * sizeof(*dst->mod_inverse_heads),
        sizeof(void *));
    if (!dst->mod_inverse_heads)
      return false;
    memcpy(dst->mod_inverse_heads, src->mod_inverse_heads,
           src->mod_inverse_head_cap * sizeof(*src->mod_inverse_heads));
  }
  if (src->nmod_inverse_watchers) {
    if (!src->mod_inverse_watchers ||
        src->nmod_inverse_watchers >
            SIZE_MAX / sizeof(*dst->mod_inverse_watchers))
      return false;
    dst->mod_inverse_watchers = ixs_arena_alloc(
        dst->scratch,
        src->nmod_inverse_watchers * sizeof(*dst->mod_inverse_watchers),
        sizeof(void *));
    if (!dst->mod_inverse_watchers)
      return false;
    memcpy(dst->mod_inverse_watchers, src->mod_inverse_watchers,
           src->nmod_inverse_watchers * sizeof(*src->mod_inverse_watchers));
  }
  return true;
}

IXS_STATIC bool bounds_store_fork_expr(ixs_bounds *dst, const ixs_bounds *src) {
  if (!src->nexprs)
    return true;
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
  return true;
}

IXS_STATIC bool bounds_store_fork_nonzero(ixs_bounds *dst,
                                          const ixs_bounds *src) {
  if (!src->nnonzero)
    return true;
  dst->nonzero = ixs_arena_alloc(
      dst->scratch, dst->nonzero_cap * sizeof(*dst->nonzero), sizeof(void *));
  if (!dst->nonzero)
    return false;
  memcpy(dst->nonzero, src->nonzero, src->nnonzero * sizeof(*src->nonzero));
  if (src->nnonzero <= BOUNDS_NONZERO_INLINE_COUNT)
    return true;
  assert(src->nonzero_index != NULL && src->nonzero_index_cap != 0);
  dst->nonzero_index = ixs_arena_alloc(
      dst->scratch, dst->nonzero_index_cap * sizeof(*dst->nonzero_index),
      sizeof(void *));
  if (!dst->nonzero_index)
    return false;
  memcpy(dst->nonzero_index, src->nonzero_index,
         dst->nonzero_index_cap * sizeof(*src->nonzero_index));
  return true;
}

IXS_STATIC void bounds_store_mark_semantic_changed(ixs_bounds *b) {
  if (b && b->semantic_changed)
    *b->semantic_changed = true;
}

IXS_STATIC void bounds_store_mark_contradiction(ixs_bounds *b) {
  if (!b->contradiction)
    bounds_store_mark_semantic_changed(b);
  b->contradiction = true;
  bounds_range_invalidate_empty(b);
}

IXS_STATIC void bounds_store_invalidate_reads(ixs_bounds *b) {
  bounds_query_refresh_owner(b);
  bounds_range_invalidate_all(b);
  bounds_relation_projection_invalidate(b);
}

IXS_STATIC void
bounds_store_publish_relation_status(ixs_bounds *b,
                                     ixs_relation_status status) {
  assert(b != NULL);
  switch (status) {
  case IXS_RELATION_STATUS_ADDED:
    bounds_store_mark_semantic_changed(b);
    bounds_store_invalidate_reads(b);
    return;
  case IXS_RELATION_STATUS_OK:
  case IXS_RELATION_STATUS_UNCHANGED:
    return;
  case IXS_RELATION_STATUS_CONFLICT:
    bounds_store_mark_contradiction(b);
    return;
  case IXS_RELATION_STATUS_OOM:
    b->oom = true;
    return;
  case IXS_RELATION_STATUS_UNREPRESENTABLE:
    assert(!"invalid exact-relation insertion result");
    abort();
  }
  assert(!"unknown exact-relation insertion result");
  abort();
}

static size_t bounds_var_index_slot(const size_t *index, size_t capacity,
                                    const ixs_var_bound *vars,
                                    const char *name) {
  size_t slot = ixs_hash_ptr(name) & (capacity - 1u);
  while (index[slot] && vars[index[slot] - 1u].name != name)
    slot = (slot + 1u) & (capacity - 1u);
  return slot;
}

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

IXS_STATIC ixs_var_bound *bounds_store_find_var(ixs_bounds *b,
                                                const char *name) {
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

IXS_STATIC bool bounds_store_get_or_create_var_index(ixs_bounds *b,
                                                     const char *name,
                                                     size_t *index) {
  ixs_var_bound *v = bounds_store_find_var(b, name);
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
  bounds_range_invalidate_empty(b);
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
  bounds_store_mark_semantic_changed(b);
  return true;
}

IXS_STATIC ixs_var_bound *bounds_store_get_or_create_var(ixs_bounds *b,
                                                         const char *name) {
  size_t index;
  if (!bounds_store_get_or_create_var_index(b, name, &index))
    return NULL;
  return &b->vars[index];
}

IXS_STATIC void bounds_store_import_var(ixs_bounds *b,
                                        ixs_var_bound *destination,
                                        const ixs_var_bound *source) {
  *destination = *source;
  if (source->modulus > 0)
    b->has_modrem = true;
}

IXS_STATIC bool bounds_store_set_var_interval(ixs_bounds *b, ixs_var_bound *var,
                                              ixs_interval interval) {
  if (ixs_interval_equal(var->iv, interval))
    return false;
  var->iv = interval;
  bounds_store_mark_semantic_changed(b);
  return true;
}

static unsigned bit_popcount64(uint64_t v) {
  unsigned n = 0;
  while (v) {
    n += (unsigned)(v & 1u);
    v >>= 1;
  }
  return n;
}

static bool bitfacts_conflict(const ixs_bitfacts *bits) {
  if ((bits->known_zero & bits->known_one) != 0)
    return true;
  if ((bits->pow2 == IXS_POW2_OR_ZERO || bits->pow2 == IXS_POW2_POSITIVE) &&
      bit_popcount64(bits->known_one) > 1)
    return true;
  return false;
}

static bool bounds_store_interval_upper_less_than(const ixs_interval *iv,
                                                  int64_t p, int64_t q) {
  return iv->valid && !iv->hi_inf && ixs_rat_cmp(iv->hi_p, iv->hi_q, p, q) < 0;
}

IXS_STATIC void bounds_store_refine_var_bits(ixs_bounds *b, ixs_var_bound *v) {
  int64_t exact;
  if (!v)
    return;
  bounds_range_invalidate_empty(b);
  if (v->bits.pow2 == IXS_POW2_OR_ZERO &&
      ixs_interval_lower_at_least(&v->iv, 1, 1)) {
    v->bits.pow2 = IXS_POW2_POSITIVE;
    bounds_store_mark_semantic_changed(b);
  }
  if ((v->bits.pow2 == IXS_POW2_OR_ZERO &&
       bounds_store_interval_upper_less_than(&v->iv, 0, 1)) ||
      (v->bits.pow2 == IXS_POW2_POSITIVE &&
       bounds_store_interval_upper_less_than(&v->iv, 1, 1)))
    bounds_store_mark_contradiction(b);
  if (ixs_interval_is_point_int(v->iv, &exact)) {
    uint64_t u = (uint64_t)exact;
    if ((v->bits.known_zero & u) != 0 || (v->bits.known_one & ~u) != 0)
      bounds_store_mark_contradiction(b);
    if ((v->bits.pow2 == IXS_POW2_OR_ZERO ||
         v->bits.pow2 == IXS_POW2_POSITIVE) &&
        exact != 0 && !ixs_int64_is_positive_pow2(exact))
      bounds_store_mark_contradiction(b);
    if (v->bits.pow2 == IXS_POW2_POSITIVE && exact == 0)
      bounds_store_mark_contradiction(b);
  }
  if (v->modulus > 0 &&
      !ixs_interval_has_congruent_integer(&v->iv, v->modulus, v->remainder))
    bounds_store_mark_contradiction(b);
  if (bitfacts_conflict(&v->bits))
    bounds_store_mark_contradiction(b);
}

IXS_STATIC void bounds_store_apply_var_known_bits(ixs_bounds *b,
                                                  ixs_var_bound *v,
                                                  uint64_t known_zero,
                                                  uint64_t known_one) {
  uint64_t old_zero;
  uint64_t old_one;
  if (!v)
    return;
  old_zero = v->bits.known_zero;
  old_one = v->bits.known_one;
  v->bits.known_zero |= known_zero;
  v->bits.known_one |= known_one;
  if (old_zero != v->bits.known_zero || old_one != v->bits.known_one)
    bounds_store_mark_semantic_changed(b);
  bounds_store_refine_var_bits(b, v);
}

IXS_STATIC void bounds_store_apply_known_bits(ixs_bounds *b, const char *name,
                                              uint64_t known_zero,
                                              uint64_t known_one) {
  ixs_var_bound *v = bounds_store_get_or_create_var(b, name);
  bounds_store_apply_var_known_bits(b, v, known_zero, known_one);
}

IXS_STATIC void bounds_store_apply_pow2(ixs_bounds *b, ixs_var_bound *v,
                                        ixs_pow2_fact pow2) {
  if (!v)
    return;
  if (pow2 == IXS_POW2_POSITIVE) {
    if (v->bits.pow2 == IXS_POW2_UNKNOWN || v->bits.pow2 == IXS_POW2_OR_ZERO) {
      v->bits.pow2 = IXS_POW2_POSITIVE;
      bounds_store_mark_semantic_changed(b);
    }
  } else if (pow2 == IXS_POW2_OR_ZERO && v->bits.pow2 == IXS_POW2_UNKNOWN) {
    v->bits.pow2 = IXS_POW2_OR_ZERO;
    bounds_store_mark_semantic_changed(b);
  }
  bounds_store_refine_var_bits(b, v);
}

IXS_STATIC void bounds_store_apply_exact_int_bits(ixs_bounds *b,
                                                  ixs_var_bound *v,
                                                  int64_t val) {
  uint64_t u = (uint64_t)val;
  if (!v)
    return;
  bounds_store_apply_var_known_bits(b, v, ~u, u);
  if (val == 0) {
    if (v->bits.pow2 == IXS_POW2_POSITIVE)
      bounds_store_mark_contradiction(b);
    else if (v->bits.pow2 != IXS_POW2_OR_ZERO) {
      v->bits.pow2 = IXS_POW2_OR_ZERO;
      bounds_store_mark_semantic_changed(b);
    }
  } else if (ixs_int64_is_positive_pow2(val)) {
    if (v->bits.pow2 != IXS_POW2_POSITIVE) {
      v->bits.pow2 = IXS_POW2_POSITIVE;
      bounds_store_mark_semantic_changed(b);
    }
  } else if (v->bits.pow2 == IXS_POW2_OR_ZERO ||
             v->bits.pow2 == IXS_POW2_POSITIVE) {
    bounds_store_mark_contradiction(b);
  }
  bounds_store_refine_var_bits(b, v);
}

static void apply_congruence_known_bits(ixs_bounds *b, ixs_var_bound *v) {
  uint64_t mask, rem;
  if (!v || !ixs_int64_is_positive_pow2(v->modulus))
    return;
  mask = (uint64_t)v->modulus - 1u;
  rem = (uint64_t)v->remainder & mask;
  bounds_store_apply_var_known_bits(b, v, (~rem) & mask, rem & mask);
}

/* Merge sym == remainder (mod modulus).  The caller owns the directed-
 * difference propagation triggered by a changed congruence. */
IXS_STATIC bool bounds_store_merge_modrem(ixs_bounds *b, const char *name,
                                          int64_t modulus, int64_t remainder) {
  ixs_var_bound *v;
  int64_t g, new_mod, old_mod, step, reduced, difference;
  uint64_t inverse, k, merged;
  bool changed = false;
  if (modulus <= 0)
    return false;
  bounds_range_invalidate_empty(b);
  remainder =
      (int64_t)ixs_int64_normalize_residue(remainder, (uint64_t)modulus);
  v = bounds_store_get_or_create_var(b, name);
  if (!v)
    return false;
  b->has_modrem = true;
  if (v->modulus == 0) {
    v->modulus = modulus;
    v->remainder = remainder;
    bounds_store_mark_semantic_changed(b);
    apply_congruence_known_bits(b, v);
    return true;
  }
  old_mod = v->modulus;
  g = ixs_gcd(old_mod, modulus);
  difference = remainder - v->remainder;
  if (ixs_int64_normalize_residue(difference, (uint64_t)g) != 0) {
    bounds_store_mark_contradiction(b);
    return false;
  }
  if (old_mod > INT64_MAX / (modulus / g))
    return false;
  new_mod = old_mod / g * modulus;
  step = old_mod / g;
  reduced = modulus / g;
  if (reduced == 1) {
    k = 0;
  } else {
    uint64_t target =
        ixs_int64_normalize_residue(difference / g, (uint64_t)reduced);
    if (!ixs_u64_mod_inverse((uint64_t)step, (uint64_t)reduced, &inverse))
      return false;
    k = ixs_u64_mul_mod(target, inverse, (uint64_t)reduced);
  }
  merged = ixs_u64_mul_mod((uint64_t)old_mod, k, (uint64_t)new_mod);
  merged += (uint64_t)v->remainder;
  remainder = (int64_t)(merged % (uint64_t)new_mod);
  if (v->modulus != new_mod || v->remainder != remainder) {
    v->modulus = new_mod;
    v->remainder = remainder;
    bounds_store_mark_semantic_changed(b);
    changed = true;
  }
  apply_congruence_known_bits(b, v);
  return changed;
}

static size_t bounds_expr_index_slot(const size_t *index, size_t capacity,
                                     const ixs_expr_bound *exprs,
                                     const ixs_node *expr) {
  size_t slot = ixs_hash_ptr(expr) & (capacity - 1u);
  while (index[slot] && exprs[index[slot] - 1u].expr != expr)
    slot = (slot + 1u) & (capacity - 1u);
  return slot;
}

IXS_STATIC ixs_interval bounds_store_expr_interval(ixs_bounds *b,
                                                   ixs_node *expr) {
  size_t slot;
  if (!b || !expr || !b->expr_index || !b->expr_index_cap)
    return ixs_interval_unknown();
  slot =
      bounds_expr_index_slot(b->expr_index, b->expr_index_cap, b->exprs, expr);
  if (!b->expr_index[slot])
    return ixs_interval_unknown();
  return b->exprs[b->expr_index[slot] - 1u].iv;
}

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

static bool bounds_prepare_mod_inverse_heads(ixs_bounds *b, size_t count) {
  size_t capacity = b->mod_inverse_head_cap;
  size_t *grown;
  if (count <= capacity)
    return true;
  if (!capacity)
    capacity = BOUNDS_VAR_INDEX_INIT_CAP;
  while (capacity < count) {
    if (capacity > SIZE_MAX / 2u)
      return false;
    capacity *= 2u;
  }
  if (b->mod_inverse_head_cap > SIZE_MAX / sizeof(*grown) ||
      capacity > SIZE_MAX / sizeof(*grown))
    return false;
  grown =
      ixs_arena_grow(b->scratch, b->mod_inverse_heads,
                     b->mod_inverse_head_cap * sizeof(*b->mod_inverse_heads),
                     capacity * sizeof(*b->mod_inverse_heads), sizeof(void *));
  if (!grown)
    return false;
  memset(grown + b->mod_inverse_head_cap, 0,
         (capacity - b->mod_inverse_head_cap) * sizeof(*grown));
  b->mod_inverse_heads = grown;
  b->mod_inverse_head_cap = capacity;
  return true;
}

static bool bounds_grow_mod_inverse_watchers(ixs_bounds *b) {
  size_t capacity = b->mod_inverse_watcher_cap ? b->mod_inverse_watcher_cap * 2u
                                               : BOUNDS_EXPR_INDEX_INIT_CAP;
  ixs_mod_inverse_watcher *grown;
  if (capacity <= b->mod_inverse_watcher_cap ||
      b->mod_inverse_watcher_cap > SIZE_MAX / sizeof(*grown) ||
      capacity > SIZE_MAX / sizeof(*grown))
    return false;
  grown = ixs_arena_grow(
      b->scratch, b->mod_inverse_watchers,
      b->mod_inverse_watcher_cap * sizeof(*b->mod_inverse_watchers),
      capacity * sizeof(*b->mod_inverse_watchers), sizeof(void *));
  if (!grown)
    return false;
  b->mod_inverse_watchers = grown;
  b->mod_inverse_watcher_cap = capacity;
  return true;
}

static bool bounds_register_mod_inverse_watcher(ixs_bounds *b,
                                                size_t expr_index) {
  ixs_node *expr;
  size_t var_index;
  ixs_mod_inverse_watcher *watcher;
  if (expr_index >= b->nexprs)
    return false;
  expr = b->exprs[expr_index].expr;
  if (expr->tag != IXS_MOD || expr->u.binary.lhs->tag != IXS_SYM ||
      expr->u.binary.rhs->tag != IXS_INT || expr->u.binary.rhs->u.ival <= 0)
    return true;
  if (!bounds_store_get_or_create_var_index(b, expr->u.binary.lhs->u.name,
                                            &var_index) ||
      !bounds_prepare_mod_inverse_heads(b, b->nvars) ||
      (b->nmod_inverse_watchers >= b->mod_inverse_watcher_cap &&
       !bounds_grow_mod_inverse_watchers(b)))
    return false;
  watcher = &b->mod_inverse_watchers[b->nmod_inverse_watchers];
  watcher->expr_index = expr_index;
  watcher->next = b->mod_inverse_heads[var_index];
  b->mod_inverse_heads[var_index] = b->nmod_inverse_watchers + 1u;
  b->nmod_inverse_watchers++;
  return true;
}

IXS_STATIC void bounds_store_add_expr_raw(ixs_bounds *b, ixs_node *expr,
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
        if (!ixs_interval_equal(bound->iv, refined)) {
          bound->iv = refined;
          bounds_store_mark_semantic_changed(b);
        }
      }
      bounds_store_invalidate_reads(b);
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
  if (!bounds_register_mod_inverse_watcher(b, b->nexprs - 1u)) {
    b->oom = true;
    return;
  }
  bounds_store_mark_semantic_changed(b);
  bounds_store_invalidate_reads(b);
}

static size_t bounds_nonzero_index_slot(const size_t *index, size_t capacity,
                                        ixs_node *const *values,
                                        const ixs_node *expr) {
  size_t slot = ixs_hash_ptr(expr) & (capacity - 1u);
  while (index[slot] && values[index[slot] - 1u] != expr)
    slot = (slot + 1u) & (capacity - 1u);
  return slot;
}

static size_t *bounds_nonzero_build_index(ixs_bounds *b, size_t capacity) {
  size_t *index =
      ixs_arena_alloc(b->scratch, capacity * sizeof(*index), sizeof(void *));
  size_t i;
  if (!index)
    return NULL;
  memset(index, 0, capacity * sizeof(*index));
  for (i = 0; i < b->nnonzero; i++) {
    size_t slot =
        bounds_nonzero_index_slot(index, capacity, b->nonzero, b->nonzero[i]);
    index[slot] = i + 1u;
  }
  return index;
}

static bool bounds_nonzero_prepare_index(ixs_bounds *b, size_t count,
                                         size_t **result,
                                         size_t *result_capacity) {
  size_t capacity = b->nonzero_index_cap;
  *result = b->nonzero_index;
  *result_capacity = capacity;
  if (count <= BOUNDS_NONZERO_INLINE_COUNT ||
      (capacity && count <= capacity - capacity / 4u))
    return true;
  capacity = capacity ? capacity * 2u : BOUNDS_NONZERO_INDEX_INIT_CAP;
  if (capacity <= b->nonzero_index_cap ||
      capacity > SIZE_MAX / sizeof(**result))
    return false;
  *result = bounds_nonzero_build_index(b, capacity);
  if (!*result)
    return false;
  *result_capacity = capacity;
  return true;
}

static bool bounds_nonzero_prepare_values(ixs_bounds *b, size_t count,
                                          ixs_node ***result,
                                          size_t *result_capacity) {
  size_t capacity = b->nonzero_cap;
  *result = b->nonzero;
  *result_capacity = capacity;
  if (count <= capacity)
    return true;
  capacity = capacity ? capacity * 2u : BOUNDS_NONZERO_INLINE_COUNT;
  if (capacity <= b->nonzero_cap || capacity > SIZE_MAX / sizeof(**result))
    return false;
  *result =
      ixs_arena_alloc(b->scratch, capacity * sizeof(**result), sizeof(void *));
  if (!*result)
    return false;
  if (b->nnonzero)
    memcpy(*result, b->nonzero, b->nnonzero * sizeof(**result));
  *result_capacity = capacity;
  return true;
}

IXS_STATIC bool bounds_store_contains_nonzero(const ixs_bounds *b,
                                              const ixs_node *expr) {
  size_t i;
  size_t slot;
  if (!b || !expr)
    return false;
  if (b->nnonzero <= BOUNDS_NONZERO_INLINE_COUNT) {
    for (i = 0; i < b->nnonzero; i++) {
      if (b->nonzero[i] == expr)
        return true;
    }
    return false;
  }
  assert(b->nonzero_index != NULL && b->nonzero_index_cap != 0);
  slot = bounds_nonzero_index_slot(b->nonzero_index, b->nonzero_index_cap,
                                   b->nonzero, expr);
  return b->nonzero_index[slot] != 0;
}

IXS_STATIC bool bounds_store_add_nonzero(ixs_bounds *b, ixs_node *expr) {
  ixs_node **values;
  size_t *index;
  size_t count;
  size_t index_capacity;
  size_t value_capacity;
  size_t slot;
  if (!b || !expr || b->oom || bounds_store_contains_nonzero(b, expr))
    return false;
  bounds_range_invalidate_empty(b);
  if (b->nnonzero == SIZE_MAX) {
    b->oom = true;
    return false;
  }
  count = b->nnonzero + 1u;
  if (!bounds_nonzero_prepare_index(b, count, &index, &index_capacity) ||
      !bounds_nonzero_prepare_values(b, count, &values, &value_capacity)) {
    b->oom = true;
    return false;
  }
  values[b->nnonzero] = expr;
  if (count > BOUNDS_NONZERO_INLINE_COUNT) {
    slot = bounds_nonzero_index_slot(index, index_capacity, values, expr);
    assert(index[slot] == 0);
    index[slot] = count;
  }
  b->nonzero = values;
  b->nonzero_cap = value_capacity;
  b->nonzero_index = index;
  b->nonzero_index_cap = index_capacity;
  b->nnonzero = count;
  bounds_store_mark_semantic_changed(b);
  return true;
}

IXS_STATIC void bounds_store_note_mod_inverse_visit(ixs_bounds *b) {
  if (b->mod_inverse_watch_visits != SIZE_MAX)
    b->mod_inverse_watch_visits++;
}

IXS_STATIC bool bounds_store_get_modrem(ixs_bounds *b, const char *name,
                                        int64_t *mod, int64_t *rem) {
  ixs_var_bound *v;
  if (!mod || !rem)
    return false;
  v = bounds_store_find_var(b, name);
  if (!v || v->modulus <= 0)
    return false;
  *mod = v->modulus;
  *rem = v->remainder;
  return true;
}
