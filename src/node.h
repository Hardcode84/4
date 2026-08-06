/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_NODE_H
#define IXS_NODE_H

#include "internal.h"

#include "arena.h"
#include "rational.h"
#include <ixsimpl.h>
#include <string.h>

/* --- Internal node struct --- */

typedef struct ixs_addterm {
  ixs_node *term;
  ixs_node *coeff; /* IXS_INT or IXS_RAT, nonzero */
} ixs_addterm;

typedef struct ixs_mulfactor {
  ixs_node *base;
  int32_t exp; /* nonzero */
} ixs_mulfactor;

typedef struct ixs_pwcase {
  ixs_node *value;
  ixs_node *cond;
} ixs_pwcase;

typedef struct ixs_session_impl {
  ixs_ctx *ctx;
  uint64_t epoch;
  ixs_arena scratch;
  ixs_arena diag;
  const char **errors;
  size_t nerrors;
  size_t errors_cap;
  ixs_arena_mark base_mark;
} ixs_session_impl;

typedef enum {
  IXS_NODE_TRANSFORM_EXPAND,
  IXS_NODE_TRANSFORM_ADD_WITHOUT_CONST,
  IXS_NODE_TRANSFORM_PROPORTIONAL_PRIMITIVE,
  IXS_NODE_TRANSFORM_BOUNDS_CANONICAL,
  IXS_NODE_TRANSFORM_COUNT
} ixs_node_transform_kind;

typedef struct {
  ixs_node *source;
  ixs_node *results[IXS_NODE_TRANSFORM_COUNT];
  unsigned expand_depth_plus_one;
} ixs_node_transform_cache_entry;

#define IXS_NODE_PROPERTY_VALID 1u
#define IXS_NODE_PROPERTY_INTEGER 2u
#define IXS_NODE_PROPERTY_BOOL 4u
#define IXS_NODE_PROPERTY_TOTAL 8u
#define IXS_NODE_PROPERTY_ROUNDING 16u
#define IXS_NODE_PROPERTY_PIECEWISE 32u
#define IXS_NODE_PROPERTY_NESTED_PIECEWISE 64u

/* Only pre-intern builders and unpublished stack probes spell this tag. */
struct ixs_node_impl {
  uint16_t tag;
  uint8_t properties;
  uint8_t reserved;
  uint32_t hash;
  union ixs_node_data {
    int64_t ival; /* IXS_INT */
    struct {
      int64_t p, q;
    } rat;            /* IXS_RAT */
    const char *name; /* IXS_SYM */
    struct {          /* IXS_ADD */
      ixs_node *coeff;
      uint32_t nterms;
      const ixs_addterm *terms;
    } add;
    struct { /* IXS_MUL */
      ixs_node *coeff;
      uint32_t nfactors;
      const ixs_mulfactor *factors;
    } mul;
    struct { /* IXS_FLOOR, IXS_CEIL */
      ixs_node *arg;
    } unary;
    struct { /* IXS_MOD, IXS_CMP */
      ixs_node *lhs;
      ixs_node *rhs;
      ixs_cmp_op cmp_op;
    } binary;
    struct { /* IXS_PIECEWISE */
      uint32_t ncases;
      const ixs_pwcase *cases;
    } pw;
    struct { /* IXS_MAX, IXS_MIN, IXS_XOR, IXS_AND, IXS_OR */
      uint32_t nargs;
      ixs_node *const *args;
    } assoc;
    struct { /* IXS_NOT */
      ixs_node *arg;
    } unary_bool;
  } u;
};

static inline bool ixs_node_contains_rounding(const ixs_node *node) {
  return node && (node->properties & IXS_NODE_PROPERTY_VALID) != 0 &&
         (node->properties & IXS_NODE_PROPERTY_ROUNDING) != 0;
}

static inline bool ixs_node_contains_piecewise(const ixs_node *node) {
  return node && (node->properties & IXS_NODE_PROPERTY_VALID) != 0 &&
         (node->properties & IXS_NODE_PROPERTY_PIECEWISE) != 0;
}

static inline bool ixs_node_contains_nested_piecewise(const ixs_node *node) {
  return node && (node->properties & IXS_NODE_PROPERTY_VALID) != 0 &&
         (node->properties & IXS_NODE_PROPERTY_NESTED_PIECEWISE) != 0;
}

/* --- Rule-hit statistics (compile with -DIXS_STATS to enable) --- */

#ifdef IXS_STATS
#define IXS_STATS_CAP 128
typedef struct {
  const char *name; /* rule name pointer from __func__; NULL = empty slot */
  uint64_t count;
} ixs_stat_entry;

static inline void ixs_stat_hit(ixs_stat_entry *stats, const char *fn) {
  size_t mask = IXS_STATS_CAP - 1;
  size_t idx = ((uintptr_t)fn >> 3) & mask;
  size_t probes;
  for (probes = 0; probes < IXS_STATS_CAP; probes++) {
    if (!stats[idx].name) {
      stats[idx].name = fn;
      stats[idx].count = 1;
      return;
    }
    if (stats[idx].name == fn) {
      stats[idx].count++;
      return;
    }
    idx = (idx + 1) & mask;
  }
}
#define IXS_STAT_HIT(ctx) ixs_stat_hit((ctx)->stats, __func__)
#else
#define IXS_STAT_HIT(ctx) ((void)(ctx))
#endif

/* --- Internal context --- */

struct ixs_ctx {
  ixs_arena arena;

  /* Hash-consing table (open addressing, linear probing) */
  ixs_node **htab;
  size_t htab_cap;
  size_t htab_used;

  /* Successful structural transforms, keyed by source node identity. */
  ixs_node_transform_cache_entry *transform_cache;
  size_t transform_cache_cap;
  size_t transform_cache_used;

  /* Lazily allocated, context-lifetime workspace for bounds proof queries. */
  void *bounds_query_state;
  /* Bound session mirrors. Session-owned state is copied in on entry to
   * session-taking APIs and copied back out on return. */
  ixs_arena scratch;
  ixs_arena diag;
  const char **errors;
  size_t nerrors;
  size_t errors_cap;
  ixs_session_impl *active_session;
  size_t active_session_depth;
  uint64_t next_session_epoch;

  /* Singletons */
  ixs_node *sentinel_error;
  ixs_node *sentinel_parse_error;
  ixs_node *node_true;
  ixs_node *node_false;
  ixs_node *node_zero;
  ixs_node *node_one;

#ifdef IXS_STATS
  ixs_stat_entry *stats;
#endif
};

/* --- Hash-consing --- */

#define IXS_HTAB_INIT_CAP 1024
#define IXS_HTAB_LOAD_NUM 7
#define IXS_HTAB_LOAD_DEN 10

/* Initialize/destroy the hash table (malloc-managed). */
IXS_STATIC bool ixs_htab_init(ixs_ctx *ctx);
IXS_STATIC void ixs_htab_destroy(ixs_ctx *ctx);

/* Context-local memo for deterministic transforms of immutable nodes. */
IXS_STATIC ixs_node *
ixs_node_transform_cache_lookup(const ixs_ctx *ctx, const ixs_node *source,
                                ixs_node_transform_kind kind);
IXS_STATIC void ixs_node_transform_cache_store(ixs_ctx *ctx, ixs_node *source,
                                               ixs_node_transform_kind kind,
                                               ixs_node *result);
IXS_STATIC ixs_node *ixs_node_expand_cache_lookup(const ixs_ctx *ctx,
                                                  const ixs_node *source,
                                                  unsigned depth);
IXS_STATIC void ixs_node_expand_cache_store(ixs_ctx *ctx, ixs_node *source,
                                            ixs_node *result, unsigned depth);
IXS_STATIC void ixs_node_transform_cache_clear(ixs_ctx *ctx);

/*
 * Intern a node: if an equal node already exists, return it;
 * otherwise insert this one. The node must already be arena-allocated
 * with hash computed. Returns NULL on OOM (rehash failure).
 */
IXS_STATIC ixs_node *ixs_htab_intern(ixs_ctx *ctx, struct ixs_node_impl *node);

/* --- Raw node constructors (no simplification) --- */

IXS_STATIC ixs_node *ixs_node_int(ixs_ctx *ctx, int64_t val);
IXS_STATIC ixs_node *ixs_node_rat(ixs_ctx *ctx, int64_t p, int64_t q);
IXS_STATIC ixs_node *ixs_node_sym(ixs_ctx *ctx, const char *name, size_t len);
IXS_STATIC ixs_node *ixs_node_add(ixs_ctx *ctx, ixs_node *coeff,
                                  uint32_t nterms, const ixs_addterm *terms);
IXS_STATIC ixs_node *ixs_node_mul(ixs_ctx *ctx, ixs_node *coeff,
                                  uint32_t nfactors,
                                  const ixs_mulfactor *factors);
IXS_STATIC ixs_node *ixs_node_floor(ixs_ctx *ctx, ixs_node *arg);
IXS_STATIC ixs_node *ixs_node_ceil(ixs_ctx *ctx, ixs_node *arg);
IXS_STATIC ixs_node *ixs_node_binary(ixs_ctx *ctx, ixs_tag tag, ixs_node *lhs,
                                     ixs_node *rhs, ixs_cmp_op op);
IXS_STATIC ixs_node *ixs_node_pw(ixs_ctx *ctx, uint32_t ncases,
                                 const ixs_pwcase *cases);
IXS_STATIC ixs_node *ixs_node_assoc(ixs_ctx *ctx, ixs_tag tag, uint32_t nargs,
                                    ixs_node *const *args);
IXS_STATIC ixs_node *ixs_node_not(ixs_ctx *ctx, ixs_node *arg);

/* --- Node comparison (total order for canonical sorting) --- */

#define IXS_NODE_CMP_OOM 2
IXS_STATIC int ixs_node_cmp(ixs_ctx *ctx, const ixs_node *a, const ixs_node *b);
IXS_STATIC bool ixs_node_equal(const ixs_node *a, const ixs_node *b);

/* --- Utility --- */

IXS_STATIC bool ixs_node_is_const(const ixs_node *n);
IXS_STATIC bool ixs_node_is_zero(const ixs_node *n);
IXS_STATIC bool ixs_node_is_one(const ixs_node *n);
IXS_STATIC bool ixs_node_is_known_false(const ixs_node *n);
IXS_STATIC bool ixs_node_is_known_true(const ixs_node *n);
IXS_STATIC void ixs_node_get_rat(const ixs_node *n, int64_t *p, int64_t *q);
IXS_STATIC bool ixs_node_is_sentinel(const ixs_node *n);
IXS_STATIC bool ixs_node_is_expr_kind(const ixs_node *n);
IXS_STATIC bool ixs_node_is_pred_kind(const ixs_node *n);
IXS_STATIC bool ixs_node_is_bool_valued(const ixs_node *n);
IXS_STATIC bool ixs_node_is_known_total(const ixs_node *n);

typedef enum {
  IXS_MOD_DIVISOR_UNKNOWN,
  IXS_MOD_DIVISOR_POSITIVE,
  IXS_MOD_DIVISOR_ZERO,
  IXS_MOD_DIVISOR_NEGATIVE
} ixs_mod_divisor_class;

/* Classify only exact numeric constants.  Non-constant divisors are UNKNOWN. */
IXS_STATIC ixs_mod_divisor_class
ixs_node_classify_mod_divisor(const ixs_node *n);

/* Error list helpers. fmt is printf-style. */
IXS_STATIC void ixs_ctx_push_error(ixs_ctx *ctx, const char *fmt, ...);

/* NULL/sentinel propagation for binary ops. Returns the propagated
 * sentinel if either arg is NULL/sentinel, or NULL if both are clean. */
IXS_STATIC ixs_node *ixs_propagate2(ixs_node *a, ixs_node *b);

/* Same for unary. */
IXS_STATIC ixs_node *ixs_propagate1(ixs_node *a);

static inline ixs_session_impl *ixs_session_get(ixs_session *s) {
  ixs_arena_chunk *chunk = (ixs_arena_chunk *)(void *)s->storage;
  return (ixs_session_impl *)(void *)chunk->base;
}

static inline const ixs_session_impl *ixs_session_cget(const ixs_session *s) {
  const ixs_arena_chunk *chunk =
      (const ixs_arena_chunk *)(const void *)s->storage;
  return (const ixs_session_impl *)(const void *)chunk->base;
}

static inline ixs_ctx *ixs_session_ctx(ixs_session *s) {
  return ixs_session_get(s)->ctx;
}

static inline const ixs_ctx *ixs_session_cctx(const ixs_session *s) {
  return ixs_session_cget(s)->ctx;
}

/* All valid store nodes are interned.  Probe by the node's stored hash and
 * compare pointer identity, which is defined across allocations and expected
 * O(1) at the hash table's bounded load factor.  The caller still owns the
 * responsibility of passing a live ixs_node pointer. */
static inline bool ixs_ctx_owns_node(const ixs_ctx *ctx, const ixs_node *node) {
  size_t index;
  size_t mask;
  size_t probes;

  if (!ctx || !node || !ctx->htab || ctx->htab_cap == 0)
    return false;

  mask = ctx->htab_cap - 1u;
  index = node->hash & mask;
  for (probes = 0; probes < ctx->htab_cap; probes++) {
    ixs_node *candidate = ctx->htab[index];
    if (!candidate)
      return false;
    if (candidate == node)
      return true;
    index = (index + 1u) & mask;
  }
  return false;
}

typedef struct {
  ixs_ctx *ctx;
  ixs_session_impl *impl;
  ixs_arena prev_scratch;
  ixs_arena prev_diag;
  const char **prev_errors;
  size_t prev_nerrors;
  size_t prev_errors_cap;
  ixs_session_impl *prev_active_session;
  size_t prev_active_session_depth;
  bool swapped;
} ixs_session_binding;

static inline bool ixs_session_is_active(const ixs_session_impl *impl) {
  return impl && impl->ctx && impl->ctx->active_session == impl;
}

/*
 * Public entry points still call ctx-based internals. Bind the session-owned
 * scratch/diagnostic state onto the context on outermost entry, but allow
 * same-session reentry without replaying stale state over the live scratch.
 */
static inline ixs_ctx *ixs_session_bind_impl(ixs_session_binding *binding,
                                             ixs_session_impl *impl) {
  ixs_ctx *ctx = impl->ctx;

  memset(binding, 0, sizeof(*binding));
  binding->ctx = ctx;
  binding->impl = impl;
  binding->prev_active_session = ctx->active_session;
  binding->prev_active_session_depth = ctx->active_session_depth;
  binding->swapped = false;

  if (ctx->active_session == impl) {
    ctx->active_session_depth++;
    return ctx;
  }

  binding->prev_scratch = ctx->scratch;
  binding->prev_diag = ctx->diag;
  binding->prev_errors = ctx->errors;
  binding->prev_nerrors = ctx->nerrors;
  binding->prev_errors_cap = ctx->errors_cap;

  ctx->scratch = impl->scratch;
  ctx->diag = impl->diag;
  ctx->errors = impl->errors;
  ctx->nerrors = impl->nerrors;
  ctx->errors_cap = impl->errors_cap;
  ctx->active_session = impl;
  ctx->active_session_depth = 1;
  binding->swapped = true;
  return ctx;
}

static inline ixs_ctx *ixs_session_bind(ixs_session_binding *binding,
                                        ixs_session *s) {
  return ixs_session_bind_impl(binding, ixs_session_get(s));
}

static inline void ixs_session_unbind(ixs_session_binding *binding) {
  if (!binding->swapped) {
    if (binding->ctx->active_session_depth > 0)
      binding->ctx->active_session_depth--;
    return;
  }

  binding->impl->scratch = binding->ctx->scratch;
  binding->impl->diag = binding->ctx->diag;
  binding->impl->errors = binding->ctx->errors;
  binding->impl->nerrors = binding->ctx->nerrors;
  binding->impl->errors_cap = binding->ctx->errors_cap;

  binding->ctx->scratch = binding->prev_scratch;
  binding->ctx->diag = binding->prev_diag;
  binding->ctx->errors = binding->prev_errors;
  binding->ctx->nerrors = binding->prev_nerrors;
  binding->ctx->errors_cap = binding->prev_errors_cap;
  binding->ctx->active_session = binding->prev_active_session;
  binding->ctx->active_session_depth = binding->prev_active_session_depth;
}

#endif /* IXS_NODE_H */
