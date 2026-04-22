/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "expand.h"
#include "node.h"
#include "parser.h"
#include "print.h"
#include "simplify.h"
#include <stdlib.h>
#include <string.h>

#define IXS_ALIGN_UP_CONST(val, align)                                         \
  (((val) + (align) - 1u) & ~((align) - 1u))

typedef char ixs_session_storage_must_fit_impl
    [(IXS_SESSION_BYTES >= IXS_ALIGN_UP_CONST(sizeof(ixs_arena_chunk), 16u) +
                               sizeof(ixs_session_impl))
         ? 1
         : -1];

static void session_clear_errors_state(ixs_arena *diag, const char ***errors,
                                       size_t *nerrors, size_t *errors_cap) {
  ixs_arena_destroy(diag);
  ixs_arena_init(diag, IXS_ARENA_DEFAULT_SIZE);
  *errors = NULL;
  *nerrors = 0;
  *errors_cap = 0;
}

static ixs_arena *session_scratch(ixs_session_impl *impl) {
  if (ixs_session_is_active(impl))
    return &impl->ctx->scratch;
  return &impl->scratch;
}

static ixs_arena *session_diag(ixs_session_impl *impl) {
  if (ixs_session_is_active(impl))
    return &impl->ctx->diag;
  return &impl->diag;
}

static const char ***session_errors(ixs_session_impl *impl) {
  if (ixs_session_is_active(impl))
    return &impl->ctx->errors;
  return &impl->errors;
}

static size_t *session_nerrors(ixs_session_impl *impl) {
  if (ixs_session_is_active(impl))
    return &impl->ctx->nerrors;
  return &impl->nerrors;
}

static size_t *session_errors_cap(ixs_session_impl *impl) {
  if (ixs_session_is_active(impl))
    return &impl->ctx->errors_cap;
  return &impl->errors_cap;
}

static void session_clear_errors_impl(ixs_session_impl *impl) {
  session_clear_errors_state(session_diag(impl), session_errors(impl),
                             session_nerrors(impl), session_errors_cap(impl));
}

static ixs_node *ctx_err(ixs_ctx *ctx, const char *msg) {
  ixs_ctx_push_error(ctx, "%s", msg);
  return ctx->sentinel_error;
}

/* ------------------------------------------------------------------ */
/*  Singleton creation                                                */
/* ------------------------------------------------------------------ */

static ixs_node *make_singleton(ixs_ctx *ctx, ixs_tag tag, uint32_t seed) {
  ixs_node *n = ixs_arena_alloc(&ctx->arena, sizeof(ixs_node), sizeof(void *));
  if (!n)
    return NULL;
  memset(n, 0, sizeof(*n));
  n->tag = tag;
  n->hash = (uint32_t)tag * 2654435761u;
  n->hash ^= seed;
  n->hash *= 0x9e3779b9u;
  /* Insert into hash table. */
  return ixs_htab_intern(ctx, n);
}

/* ------------------------------------------------------------------ */
/*  Context lifecycle                                                 */
/* ------------------------------------------------------------------ */

ixs_ctx *ixs_ctx_create(void) {
  ixs_ctx tmp;
  ixs_ctx *ctx;
  memset(&tmp, 0, sizeof(tmp));

  ixs_arena_init(&tmp.arena, IXS_ARENA_DEFAULT_SIZE);

  if (!ixs_htab_init(&tmp))
    return NULL;

  /* Create singletons. */
  tmp.sentinel_error = make_singleton(&tmp, IXS_ERROR, 0xDEAD);
  tmp.sentinel_parse_error = make_singleton(&tmp, IXS_PARSE_ERROR, 0xBEEF);
  tmp.node_true = make_singleton(&tmp, IXS_TRUE, 1);
  tmp.node_false = make_singleton(&tmp, IXS_FALSE, 0);

  if (!tmp.sentinel_error || !tmp.sentinel_parse_error || !tmp.node_true ||
      !tmp.node_false)
    goto fail;

  tmp.node_zero = ixs_node_int(&tmp, 0);
  tmp.node_one = ixs_node_int(&tmp, 1);

  if (!tmp.node_zero || !tmp.node_one)
    goto fail;

#ifdef IXS_STATS
  tmp.stats = ixs_arena_alloc(
      &tmp.arena, IXS_STATS_CAP * sizeof(ixs_stat_entry), sizeof(void *));
  if (!tmp.stats)
    goto fail;
  memset(tmp.stats, 0, IXS_STATS_CAP * sizeof(ixs_stat_entry));
#endif

  /* Emplace ctx into its own arena — one fewer heap allocation. */
  ctx = ixs_arena_alloc(&tmp.arena, sizeof(ixs_ctx), sizeof(void *));
  if (!ctx)
    goto fail;
  memcpy(ctx, &tmp, sizeof(ixs_ctx));
  return ctx;

fail:
  ixs_htab_destroy(&tmp);
  ixs_arena_destroy(&tmp.arena);
  return NULL;
}

void ixs_ctx_destroy(ixs_ctx *ctx) {
  if (!ctx)
    return;
  ixs_htab_destroy(ctx);
  /* ctx itself lives inside the main arena; snapshot before freeing. */
  ixs_arena arena = ctx->arena;
  ixs_arena_destroy(&arena);
}

/* ------------------------------------------------------------------ */
/*  Session lifecycle                                                 */
/* ------------------------------------------------------------------ */

void ixs_session_init(ixs_session *s, ixs_ctx *ctx) {
  ixs_arena scratch;
  ixs_session_impl *impl;

  memset(s, 0, sizeof(*s));
  ixs_arena_init_inline(&scratch, s->storage, IXS_SESSION_BYTES,
                        IXS_ARENA_DEFAULT_SIZE);
  impl = ixs_arena_alloc(&scratch, sizeof(*impl), sizeof(void *));
  if (!impl)
    return;
  memset(impl, 0, sizeof(*impl));
  impl->ctx = ctx;
  impl->scratch = scratch;
  ixs_arena_init(&impl->diag, IXS_ARENA_DEFAULT_SIZE);
  impl->base_mark = ixs_arena_save(&impl->scratch);
}

void ixs_session_reset(ixs_session *s) {
  ixs_session_impl *impl = ixs_session_get(s);
  ixs_arena_restore(session_scratch(impl), impl->base_mark);
  session_clear_errors_impl(impl);
}

void ixs_session_destroy(ixs_session *s) {
  ixs_session_impl *impl = ixs_session_get(s);
  ixs_arena_destroy(&impl->diag);
  ixs_arena_destroy(&impl->scratch);
  memset(s, 0, sizeof(*s));
}

/* ------------------------------------------------------------------ */
/*  Error list                                                        */
/* ------------------------------------------------------------------ */

size_t ixs_session_nerrors(ixs_session *s) {
  ixs_session_impl *impl = ixs_session_get(s);
  return *session_nerrors(impl);
}

const char *ixs_session_error(ixs_session *s, size_t index) {
  ixs_session_impl *impl = ixs_session_get(s);
  const char **errors = *session_errors(impl);
  size_t nerrors = *session_nerrors(impl);
  if (index >= nerrors)
    return NULL;
  return errors[index];
}

void ixs_session_clear_errors(ixs_session *s) {
  session_clear_errors_impl(ixs_session_get(s));
}

/* ------------------------------------------------------------------ */
/*  Rule-hit statistics                                                */
/* ------------------------------------------------------------------ */

size_t ixs_ctx_nstats(ixs_ctx *ctx) {
#ifdef IXS_STATS
  size_t n = 0;
  size_t i;
  for (i = 0; i < IXS_STATS_CAP; i++) {
    if (ctx->stats[i].name)
      n++;
  }
  return n;
#else
  (void)ctx;
  return 0;
#endif
}

uint64_t ixs_ctx_stat(ixs_ctx *ctx, size_t index, const char **name) {
#ifdef IXS_STATS
  size_t seen = 0;
  size_t i;
  for (i = 0; i < IXS_STATS_CAP; i++) {
    if (ctx->stats[i].name) {
      if (seen == index) {
        if (name)
          *name = ctx->stats[i].name;
        return ctx->stats[i].count;
      }
      seen++;
    }
  }
#else
  (void)ctx;
  (void)index;
#endif
  if (name)
    *name = NULL;
  return 0;
}

void ixs_ctx_stats_reset(ixs_ctx *ctx) {
#ifdef IXS_STATS
  memset(ctx->stats, 0, IXS_STATS_CAP * sizeof(ixs_stat_entry));
#else
  (void)ctx;
#endif
}

/* ------------------------------------------------------------------ */
/*  Sentinel checks                                                   */
/* ------------------------------------------------------------------ */

bool ixs_is_error(ixs_node *node) {
  return node && (node->tag == IXS_ERROR || node->tag == IXS_PARSE_ERROR);
}

bool ixs_is_parse_error(ixs_node *node) {
  return node && node->tag == IXS_PARSE_ERROR;
}

bool ixs_is_domain_error(ixs_node *node) {
  return node && node->tag == IXS_ERROR;
}

bool ixs_node_is_expr(const ixs_node *node) {
  return ixs_node_is_expr_kind(node);
}

bool ixs_node_is_pred(const ixs_node *node) {
  return ixs_node_is_pred_kind(node);
}

/* ------------------------------------------------------------------ */
/*  Constructors (delegate to simplify.c)                             */
/* ------------------------------------------------------------------ */

ixs_node *ixs_int(ixs_session *s, int64_t val) {
  return ixs_node_int(ixs_session_ctx(s), val);
}

ixs_node *ixs_rat(ixs_session *s, int64_t p, int64_t q) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result;
  if (q == 0)
    result = ctx_err(ctx, "ixs_rat: denominator is zero");
  else {
    int64_t rp, rq;
    if (!ixs_rat_normalize(p, q, &rp, &rq))
      result = ctx_err(ctx, "ixs_rat: rational overflow");
    else
      result = ixs_node_rat(ctx, rp, rq);
  }
  ixs_session_unbind(&binding);
  return result;
}

ixs_node *ixs_sym(ixs_session *s, const char *name) {
  ixs_ctx *ctx = ixs_session_ctx(s);
  return ixs_node_sym(ctx, name, strlen(name));
}

ixs_node *ixs_add(ixs_session *s, ixs_node *a, ixs_node *b) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result = simp_add(ctx, a, b);
  ixs_session_unbind(&binding);
  return result;
}

ixs_node *ixs_mul(ixs_session *s, ixs_node *a, ixs_node *b) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result = simp_mul(ctx, a, b);
  ixs_session_unbind(&binding);
  return result;
}

ixs_node *ixs_neg(ixs_session *s, ixs_node *a) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result = simp_neg(ctx, a);
  ixs_session_unbind(&binding);
  return result;
}

ixs_node *ixs_sub(ixs_session *s, ixs_node *a, ixs_node *b) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result = simp_sub(ctx, a, b);
  ixs_session_unbind(&binding);
  return result;
}

ixs_node *ixs_div(ixs_session *s, ixs_node *a, ixs_node *b) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result = simp_div(ctx, a, b);
  ixs_session_unbind(&binding);
  return result;
}

ixs_node *ixs_floor(ixs_session *s, ixs_node *x) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result = simp_floor(ctx, x);
  ixs_session_unbind(&binding);
  return result;
}

ixs_node *ixs_ceil(ixs_session *s, ixs_node *x) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result = simp_ceil(ctx, x);
  ixs_session_unbind(&binding);
  return result;
}

ixs_node *ixs_mod(ixs_session *s, ixs_node *a, ixs_node *b) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result = simp_mod(ctx, a, b);
  ixs_session_unbind(&binding);
  return result;
}

ixs_node *ixs_max(ixs_session *s, ixs_node *a, ixs_node *b) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result = simp_max(ctx, a, b);
  ixs_session_unbind(&binding);
  return result;
}

ixs_node *ixs_min(ixs_session *s, ixs_node *a, ixs_node *b) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result = simp_min(ctx, a, b);
  ixs_session_unbind(&binding);
  return result;
}

ixs_node *ixs_xor(ixs_session *s, ixs_node *a, ixs_node *b) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result = simp_xor(ctx, a, b);
  ixs_session_unbind(&binding);
  return result;
}

ixs_node *ixs_pw(ixs_session *s, uint32_t n, ixs_node **values,
                 ixs_node **conds) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result = simp_pw(ctx, n, values, conds);
  ixs_session_unbind(&binding);
  return result;
}

ixs_node *ixs_cmp(ixs_session *s, ixs_node *a, ixs_cmp_op op, ixs_node *b) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result = simp_cmp(ctx, a, op, b);
  ixs_session_unbind(&binding);
  return result;
}

ixs_node *ixs_and(ixs_session *s, ixs_node *a, ixs_node *b) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result = simp_and(ctx, a, b);
  ixs_session_unbind(&binding);
  return result;
}

ixs_node *ixs_or(ixs_session *s, ixs_node *a, ixs_node *b) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result = simp_or(ctx, a, b);
  ixs_session_unbind(&binding);
  return result;
}

ixs_node *ixs_not(ixs_session *s, ixs_node *a) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result = simp_not(ctx, a);
  ixs_session_unbind(&binding);
  return result;
}

ixs_node *ixs_true(ixs_session *s) { return ixs_session_ctx(s)->node_true; }

ixs_node *ixs_false(ixs_session *s) { return ixs_session_ctx(s)->node_false; }

/* ------------------------------------------------------------------ */
/*  Parse                                                             */
/* ------------------------------------------------------------------ */

ixs_node *ixs_parse(ixs_session *s, const char *input, size_t len) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result;
  if (!input)
    result = ctx->sentinel_parse_error;
  else
    result = ixs_parse_impl(ctx, input, len);
  ixs_session_unbind(&binding);
  return result;
}

ixs_node *ixs_parse_expr(ixs_session *s, const char *input, size_t len) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result;
  if (!input)
    result = ctx->sentinel_parse_error;
  else
    result = ixs_parse_expr_impl(ctx, input, len);
  ixs_session_unbind(&binding);
  return result;
}

ixs_node *ixs_parse_pred(ixs_session *s, const char *input, size_t len) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result;
  if (!input)
    result = ctx->sentinel_parse_error;
  else
    result = ixs_parse_pred_impl(ctx, input, len);
  ixs_session_unbind(&binding);
  return result;
}

/* ------------------------------------------------------------------ */
/*  Simplification                                                    */
/* ------------------------------------------------------------------ */

ixs_node *ixs_expand(ixs_session *s, ixs_node *expr) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result = expand_impl(ctx, expr);
  ixs_session_unbind(&binding);
  return result;
}

ixs_node *ixs_simplify(ixs_session *s, ixs_node *expr,
                       ixs_node *const *assumptions, size_t n_assumptions) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result = simp_simplify(ctx, expr, assumptions, n_assumptions);
  ixs_session_unbind(&binding);
  return result;
}

void ixs_simplify_batch(ixs_session *s, ixs_node **exprs, size_t n,
                        ixs_node *const *assumptions, size_t n_assumptions) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  simp_simplify_batch(ctx, exprs, n, assumptions, n_assumptions);
  ixs_session_unbind(&binding);
}

/* ------------------------------------------------------------------ */
/*  Entailment checking                                               */
/* ------------------------------------------------------------------ */

ixs_check_result ixs_check(ixs_session *s, ixs_node *expr,
                           ixs_node *const *assumptions, size_t n_assumptions) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_check_result result = simp_check(ctx, expr, assumptions, n_assumptions);
  ixs_session_unbind(&binding);
  return result;
}

/* ------------------------------------------------------------------ */
/*  Comparison and substitution                                       */
/* ------------------------------------------------------------------ */

bool ixs_same_node(ixs_node *a, ixs_node *b) { return a == b; }

ixs_node *ixs_subs(ixs_session *s, ixs_node *expr, ixs_node *target,
                   ixs_node *replacement) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result = simp_subs(ctx, expr, target, replacement);
  ixs_session_unbind(&binding);
  return result;
}

ixs_node *ixs_subs_multi(ixs_session *s, ixs_node *expr, uint32_t nsubs,
                         ixs_node *const *targets,
                         ixs_node *const *replacements) {
  ixs_session_binding binding;
  ixs_ctx *ctx = ixs_session_bind(&binding, s);
  ixs_node *result = simp_subs_multi(ctx, expr, nsubs, targets, replacements);
  ixs_session_unbind(&binding);
  return result;
}

/* ------------------------------------------------------------------ */
/*  Output                                                            */
/* ------------------------------------------------------------------ */

size_t ixs_print(ixs_node *expr, char *buf, size_t bufsize) {
  return ixs_print_impl(expr, buf, bufsize);
}

size_t ixs_print_c(ixs_node *expr, char *buf, size_t bufsize) {
  return ixs_print_c_impl(expr, buf, bufsize);
}

/* ------------------------------------------------------------------ */
/*  Introspection                                                     */
/* ------------------------------------------------------------------ */

ixs_tag ixs_node_tag(ixs_node *node) { return node->tag; }

int64_t ixs_node_int_val(ixs_node *node) { return node->u.ival; }

uint32_t ixs_node_hash(ixs_node *node) { return node->hash; }
