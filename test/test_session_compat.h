/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef TEST_SESSION_COMPAT_H
#define TEST_SESSION_COMPAT_H

/*
 * The C API is migrating from ctx-owned scratch/errors to an explicit session.
 * Keep the existing test bodies readable by routing ctx-shaped calls through a
 * small per-translation-unit ctx->session table.
 */
#define IXS_TEST_SESSION_SLOTS 16

typedef struct {
  ixs_ctx *ctx;
  ixs_session session;
} ixs_test_session_slot;

static ixs_test_session_slot ixs_test_sessions[IXS_TEST_SESSION_SLOTS];

static inline ixs_test_session_slot *ixs_test_find_slot(ixs_ctx *ctx) {
  size_t i;
  if (!ctx)
    return NULL;
  for (i = 0; i < IXS_TEST_SESSION_SLOTS; i++) {
    if (ixs_test_sessions[i].ctx == ctx)
      return &ixs_test_sessions[i];
  }
  return NULL;
}

static inline ixs_session *ixs_test_session_for_ctx(ixs_ctx *ctx) {
  ixs_test_session_slot *slot = ixs_test_find_slot(ctx);
  return slot ? &slot->session : NULL;
}

static inline ixs_ctx *ixs_test_ctx_create(void) {
  size_t i;
  ixs_ctx *ctx = (ixs_ctx_create)();
  if (!ctx)
    return NULL;
  for (i = 0; i < IXS_TEST_SESSION_SLOTS; i++) {
    if (!ixs_test_sessions[i].ctx) {
      ixs_test_sessions[i].ctx = ctx;
      ixs_session_init(&ixs_test_sessions[i].session, ctx);
      return ctx;
    }
  }
  (ixs_ctx_destroy)(ctx);
  return NULL;
}

static inline void ixs_test_ctx_destroy(ixs_ctx *ctx) {
  ixs_test_session_slot *slot = ixs_test_find_slot(ctx);
  if (!ctx) {
    (ixs_ctx_destroy)(ctx);
    return;
  }
  if (slot) {
    ixs_session_destroy(&slot->session);
    slot->ctx = NULL;
  }
  (ixs_ctx_destroy)(ctx);
}

#define IXS_TEST_WITH_CTX(ctx, expr) ((void)(ctx), (expr))
#define IXS_TEST_SESSION(ctx) ixs_test_session_for_ctx((ctx))

#define ixs_ctx_create() ixs_test_ctx_create()
#define ixs_ctx_destroy(ctx) ixs_test_ctx_destroy((ctx))

#define ixs_ctx_nerrors(ctx)                                                   \
  IXS_TEST_WITH_CTX((ctx), (ixs_session_nerrors)(IXS_TEST_SESSION(ctx)))
#define ixs_ctx_error(ctx, index)                                              \
  IXS_TEST_WITH_CTX((ctx), (ixs_session_error)(IXS_TEST_SESSION(ctx), (index)))
#define ixs_ctx_clear_errors(ctx)                                              \
  IXS_TEST_WITH_CTX((ctx), (ixs_session_clear_errors)(IXS_TEST_SESSION(ctx)))

#define ixs_parse(ctx, input, len)                                             \
  IXS_TEST_WITH_CTX((ctx), (ixs_parse)(IXS_TEST_SESSION(ctx), (input), (len)))
#define ixs_parse_expr(ctx, input, len)                                        \
  IXS_TEST_WITH_CTX((ctx),                                                     \
                    (ixs_parse_expr)(IXS_TEST_SESSION(ctx), (input), (len)))
#define ixs_parse_pred(ctx, input, len)                                        \
  IXS_TEST_WITH_CTX((ctx),                                                     \
                    (ixs_parse_pred)(IXS_TEST_SESSION(ctx), (input), (len)))

#define ixs_int(ctx, val)                                                      \
  IXS_TEST_WITH_CTX((ctx), (ixs_int)(IXS_TEST_SESSION(ctx), (val)))
#define ixs_rat(ctx, p, q)                                                     \
  IXS_TEST_WITH_CTX((ctx), (ixs_rat)(IXS_TEST_SESSION(ctx), (p), (q)))
#define ixs_sym(ctx, name)                                                     \
  IXS_TEST_WITH_CTX((ctx), (ixs_sym)(IXS_TEST_SESSION(ctx), (name)))
#define ixs_add(ctx, a, b)                                                     \
  IXS_TEST_WITH_CTX((ctx), (ixs_add)(IXS_TEST_SESSION(ctx), (a), (b)))
#define ixs_mul(ctx, a, b)                                                     \
  IXS_TEST_WITH_CTX((ctx), (ixs_mul)(IXS_TEST_SESSION(ctx), (a), (b)))
#define ixs_neg(ctx, a)                                                        \
  IXS_TEST_WITH_CTX((ctx), (ixs_neg)(IXS_TEST_SESSION(ctx), (a)))
#define ixs_sub(ctx, a, b)                                                     \
  IXS_TEST_WITH_CTX((ctx), (ixs_sub)(IXS_TEST_SESSION(ctx), (a), (b)))
#define ixs_div(ctx, a, b)                                                     \
  IXS_TEST_WITH_CTX((ctx), (ixs_div)(IXS_TEST_SESSION(ctx), (a), (b)))
#define ixs_floor(ctx, x)                                                      \
  IXS_TEST_WITH_CTX((ctx), (ixs_floor)(IXS_TEST_SESSION(ctx), (x)))
#define ixs_ceil(ctx, x)                                                       \
  IXS_TEST_WITH_CTX((ctx), (ixs_ceil)(IXS_TEST_SESSION(ctx), (x)))
#define ixs_mod(ctx, a, b)                                                     \
  IXS_TEST_WITH_CTX((ctx), (ixs_mod)(IXS_TEST_SESSION(ctx), (a), (b)))
#define ixs_max(ctx, a, b)                                                     \
  IXS_TEST_WITH_CTX((ctx), (ixs_max)(IXS_TEST_SESSION(ctx), (a), (b)))
#define ixs_min(ctx, a, b)                                                     \
  IXS_TEST_WITH_CTX((ctx), (ixs_min)(IXS_TEST_SESSION(ctx), (a), (b)))
#define ixs_xor(ctx, a, b)                                                     \
  IXS_TEST_WITH_CTX((ctx), (ixs_xor)(IXS_TEST_SESSION(ctx), (a), (b)))
#define ixs_pw(ctx, n, values, conds)                                          \
  IXS_TEST_WITH_CTX((ctx),                                                     \
                    (ixs_pw)(IXS_TEST_SESSION(ctx), (n), (values), (conds)))
#define ixs_cmp(ctx, a, op, b)                                                 \
  IXS_TEST_WITH_CTX((ctx), (ixs_cmp)(IXS_TEST_SESSION(ctx), (a), (op), (b)))
#define ixs_and(ctx, a, b)                                                     \
  IXS_TEST_WITH_CTX((ctx), (ixs_and)(IXS_TEST_SESSION(ctx), (a), (b)))
#define ixs_or(ctx, a, b)                                                      \
  IXS_TEST_WITH_CTX((ctx), (ixs_or)(IXS_TEST_SESSION(ctx), (a), (b)))
#define ixs_not(ctx, a)                                                        \
  IXS_TEST_WITH_CTX((ctx), (ixs_not)(IXS_TEST_SESSION(ctx), (a)))
#define ixs_true(ctx)                                                          \
  IXS_TEST_WITH_CTX((ctx), (ixs_true)(IXS_TEST_SESSION(ctx)))
#define ixs_false(ctx)                                                         \
  IXS_TEST_WITH_CTX((ctx), (ixs_false)(IXS_TEST_SESSION(ctx)))

#define ixs_check(ctx, expr, assumptions, n_assumptions)                       \
  IXS_TEST_WITH_CTX((ctx), (ixs_check)(IXS_TEST_SESSION(ctx), (expr),          \
                                       (assumptions), (n_assumptions)))
#define ixs_simplify(ctx, expr, assumptions, n_assumptions)                    \
  IXS_TEST_WITH_CTX((ctx), (ixs_simplify)(IXS_TEST_SESSION(ctx), (expr),       \
                                          (assumptions), (n_assumptions)))
#define ixs_simplify_batch(ctx, exprs, n, assumptions, n_assumptions)          \
  IXS_TEST_WITH_CTX((ctx),                                                     \
                    (ixs_simplify_batch)(IXS_TEST_SESSION(ctx), (exprs), (n),  \
                                         (assumptions), (n_assumptions)))
#define ixs_expand(ctx, expr)                                                  \
  IXS_TEST_WITH_CTX((ctx), (ixs_expand)(IXS_TEST_SESSION(ctx), (expr)))
#define ixs_subs(ctx, expr, target, replacement)                               \
  IXS_TEST_WITH_CTX((ctx), (ixs_subs)(IXS_TEST_SESSION(ctx), (expr), (target), \
                                      (replacement)))
#define ixs_subs_multi(ctx, expr, nsubs, targets, replacements)                \
  IXS_TEST_WITH_CTX((ctx),                                                     \
                    (ixs_subs_multi)(IXS_TEST_SESSION(ctx), (expr), (nsubs),   \
                                     (targets), (replacements)))

#define ixs_walk_pre(ctx, root, fn, userdata)                                  \
  IXS_TEST_WITH_CTX(                                                           \
      (ctx), (ixs_walk_pre)(IXS_TEST_SESSION(ctx), (root), (fn), (userdata)))
#define ixs_walk_post(ctx, root, fn, userdata)                                 \
  IXS_TEST_WITH_CTX(                                                           \
      (ctx), (ixs_walk_post)(IXS_TEST_SESSION(ctx), (root), (fn), (userdata)))

#ifdef IXS_NODE_H
#define ixs_test_scratch(ctx) (&ixs_session_get(IXS_TEST_SESSION(ctx))->scratch)
#endif

#endif /* TEST_SESSION_COMPAT_H */
