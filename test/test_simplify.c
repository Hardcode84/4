/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include <inttypes.h>
#include <ixsimpl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "test_check.h"

static char buf[4096];

static const char *pr(ixs_node *n) {
  ixs_print(n, buf, sizeof(buf));
  return buf;
}

/* ---- Global context with stats accumulation ---- */

static ixs_ctx *g_ctx;

static ixs_ctx *ctx_create_or_die(void) {
  ixs_ctx *ctx = ixs_ctx_create();
  if (!ctx) {
    fprintf(stderr, "ixs_ctx_create failed\n");
    exit(1);
  }
  return ctx;
}

static void atexit_handler(void) {
  size_t i, j, n_fired, n_rules;
  size_t unhit = 0;

  if (!g_ctx)
    return;

  n_fired = ixs_ctx_nstats(g_ctx);
  n_rules = ixs_nrules();

  printf("\n--- rule hit stats (%zu / %zu rules fired) ---\n", n_fired,
         n_rules);
  for (i = 0; i < n_fired; i++) {
    const char *name;
    uint64_t count = ixs_ctx_stat(g_ctx, i, &name);
    printf("  %-30s %8" PRIu64 "\n", name, count);
  }

  for (j = 0; j < n_rules; j++) {
    const char *rule = ixs_rule_name(j);
    bool found = false;
    for (i = 0; i < n_fired; i++) {
      const char *name;
      ixs_ctx_stat(g_ctx, i, &name);
      if (strcmp(name, rule) == 0) {
        found = true;
        break;
      }
    }
    if (!found) {
      if (!unhit)
        printf("\n--- UNTESTED rules ---\n");
      printf("  %s\n", rule);
      unhit++;
    }
  }

  if (unhit) {
    fprintf(stderr, "%zu rule(s) never fired\n", unhit);
    ixs_ctx_destroy(g_ctx);
    g_ctx = NULL;
    _Exit(1);
  }

  printf("all %zu known rules exercised\n", n_rules);
  ixs_ctx_destroy(g_ctx);
  g_ctx = NULL;
}

static ixs_ctx *get_ctx(void) {
  if (!g_ctx) {
    g_ctx = ctx_create_or_die();
    atexit(atexit_handler);
  }
  return g_ctx;
}

static uint64_t stat_count(ixs_ctx *ctx, const char *wanted) {
  size_t i;
  for (i = 0; i < ixs_ctx_nstats(ctx); i++) {
    const char *name;
    uint64_t count = ixs_ctx_stat(ctx, i, &name);
    if (name && strcmp(name, wanted) == 0)
      return count;
  }
  return 0;
}

static void test_add_canonicalize(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");

  /* x + x -> 2*x */
  ixs_node *r = ixs_add(ctx, x, x);
  CHECK(strcmp(pr(r), "2*x") == 0);

  /* x + 0 -> x */
  r = ixs_add(ctx, x, ixs_int(ctx, 0));
  CHECK(r == x);

  /* 0 + x -> x */
  r = ixs_add(ctx, ixs_int(ctx, 0), x);
  CHECK(r == x);

  /* 3 + 4 -> 7 */
  r = ixs_add(ctx, ixs_int(ctx, 3), ixs_int(ctx, 4));
  CHECK(ixs_node_int_val(r) == 7);

  /* (x + y) + (x + y) -> 2*x + 2*y */
  ixs_node *xy = ixs_add(ctx, x, y);
  r = ixs_add(ctx, xy, xy);
  CHECK(r && !ixs_is_error(r));
}

static void test_mul_canonicalize(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");

  /* x * 1 -> x */
  ixs_node *r = ixs_mul(ctx, x, ixs_int(ctx, 1));
  CHECK(r == x);

  /* 1 * x -> x */
  r = ixs_mul(ctx, ixs_int(ctx, 1), x);
  CHECK(r == x);

  /* x * 0 -> 0 */
  r = ixs_mul(ctx, x, ixs_int(ctx, 0));
  CHECK(ixs_node_int_val(r) == 0);

  /* 3 * 4 -> 12 */
  r = ixs_mul(ctx, ixs_int(ctx, 3), ixs_int(ctx, 4));
  CHECK(ixs_node_int_val(r) == 12);

  /* x * x -> x**2 */
  r = ixs_mul(ctx, x, x);
  CHECK(r && !ixs_is_error(r));
}

static void test_hash_consing(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x1 = ixs_sym(ctx, "x");
  ixs_node *x2 = ixs_sym(ctx, "x");
  CHECK(x1 == x2);

  ixs_node *a = ixs_add(ctx, x1, ixs_int(ctx, 1));
  ixs_node *b = ixs_add(ctx, x2, ixs_int(ctx, 1));
  CHECK(a == b);
}

static void test_floor_rules(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");

  /* floor(5) -> 5 */
  CHECK(ixs_floor(ctx, ixs_int(ctx, 5)) == ixs_int(ctx, 5));

  /* floor(7/2) -> 3 */
  CHECK(ixs_node_int_val(ixs_floor(ctx, ixs_rat(ctx, 7, 2))) == 3);

  /* floor(floor(x)) -> floor(x) */
  ixs_node *fx = ixs_floor(ctx, x);
  CHECK(ixs_floor(ctx, fx) == fx);

  /* floor(ceil(x)) -> ceil(x) */
  ixs_node *cx = ixs_ceil(ctx, x);
  CHECK(ixs_floor(ctx, cx) == cx);

  /* floor(x + 3) -> floor(x) + 3 */
  ixs_node *xp3 = ixs_add(ctx, x, ixs_int(ctx, 3));
  ixs_node *fxp3 = ixs_floor(ctx, xp3);
  ixs_node *fxp3_expected = ixs_add(ctx, ixs_floor(ctx, x), ixs_int(ctx, 3));
  CHECK(fxp3 == fxp3_expected);

  /* floor(x + 1/2) -> x  (x is integer-valued: SYM) */
  CHECK(ixs_floor(ctx, ixs_add(ctx, x, ixs_rat(ctx, 1, 2))) == x);

  /* floor extraction from ADD: floor(2*floor(x/3) + y/2)
   * -> 2*floor(x/3) + floor(y/2) */
  {
    ixs_node *y = ixs_sym(ctx, "y");
    ixs_node *fx3 = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)));
    ixs_node *sum = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), fx3),
                            ixs_div(ctx, y, ixs_int(ctx, 2)));
    ixs_node *result = ixs_floor(ctx, sum);
    ixs_node *expected =
        ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), fx3),
                ixs_floor(ctx, ixs_div(ctx, y, ixs_int(ctx, 2))));
    CHECK(result == expected);
  }

  /* floor extraction from MUL*ADD:
   * floor((4*floor(x/3) + y) / 2) -> 2*floor(x/3) + floor(y/2) */
  {
    ixs_node *y = ixs_sym(ctx, "y");
    ixs_node *fx3 = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)));
    ixs_node *sum = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 4), fx3), y);
    ixs_node *result = ixs_floor(ctx, ixs_div(ctx, sum, ixs_int(ctx, 2)));
    ixs_node *expected =
        ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), fx3),
                ixs_floor(ctx, ixs_div(ctx, y, ixs_int(ctx, 2))));
    CHECK(result == expected);
  }

  /* floor extraction with symbolic denominator:
   * floor((6*K*floor(x/3) + y) / (2*K)) -> 3*floor(x/3) + floor(y/(2*K)) */
  {
    ixs_node *y = ixs_sym(ctx, "y");
    ixs_node *K = ixs_sym(ctx, "K");
    ixs_node *fx3 = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)));
    ixs_node *sum =
        ixs_add(ctx, ixs_mul(ctx, ixs_mul(ctx, ixs_int(ctx, 6), K), fx3), y);
    ixs_node *denom = ixs_mul(ctx, ixs_int(ctx, 2), K);
    ixs_node *result = ixs_floor(ctx, ixs_div(ctx, sum, denom));
    /* Build expected with decomposed form: (1/2)*K^(-1)*y */
    ixs_node *y_over_2K = ixs_mul(ctx, ixs_rat(ctx, 1, 2), ixs_div(ctx, y, K));
    ixs_node *expected = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 3), fx3),
                                 ixs_floor(ctx, y_over_2K));
    CHECK(result == expected);
  }

  /* ceil(x + 1/2) -> x + 1  (x is integer-valued: SYM) */
  CHECK(ixs_ceil(ctx, ixs_add(ctx, x, ixs_rat(ctx, 1, 2))) ==
        ixs_add(ctx, x, ixs_int(ctx, 1)));

  /* ceil extraction from MUL*ADD:
   * ceil((4*ceil(x/3) + y) / 2) -> 2*ceil(x/3) + ceil(y/2) */
  {
    ixs_node *y = ixs_sym(ctx, "y");
    ixs_node *cx3 = ixs_ceil(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)));
    ixs_node *sum = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 4), cx3), y);
    ixs_node *result = ixs_ceil(ctx, ixs_div(ctx, sum, ixs_int(ctx, 2)));
    ixs_node *expected =
        ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), cx3),
                ixs_ceil(ctx, ixs_div(ctx, y, ixs_int(ctx, 2))));
    CHECK(result == expected);
  }
}

static void test_mod_rules(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");

  /* Mod(floor(x), 1) -> 0 (only integer-valued args fold) */
  CHECK(ixs_node_int_val(ixs_mod(ctx, ixs_floor(ctx, x), ixs_int(ctx, 1))) ==
        0);

  /* Mod(17, 5) -> 2 */
  CHECK(ixs_node_int_val(ixs_mod(ctx, ixs_int(ctx, 17), ixs_int(ctx, 5))) == 2);

  /* Mod(Mod(x, 5), 5) -> Mod(x, 5) */
  ixs_node *mx5 = ixs_mod(ctx, x, ixs_int(ctx, 5));
  CHECK(ixs_mod(ctx, mx5, ixs_int(ctx, 5)) == mx5);

  /* Mod with non-integer argument must NOT fold to 0.
   * Mod(x*(x+1/3), 1) is NOT zero -- e.g. at x=2 it equals 2/3.
   * Regression: mod_bounds_elim called is_known_divisible without
   * checking integer-valuedness of the numerator. */
  {
    ixs_node *rat_prod = ixs_mul(ctx, x, ixs_add(ctx, x, ixs_rat(ctx, 1, 3)));
    ixs_node *m1 = ixs_mod(ctx, rat_prod, ixs_int(ctx, 1));
    ixs_node *neg = ixs_mul(ctx, ixs_int(ctx, -1), m1);
    ixs_node *fl = ixs_floor(ctx, neg);
    ixs_node *assumes[] = {
        ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
        ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 10)),
    };
    ixs_node *r = ixs_simplify(ctx, fl, assumes, 2);
    CHECK(r != ixs_int(ctx, 0));
  }

  /* Divisibility by one still requires an integer dividend.  An empty
   * low-bit mask must not prove Mod(x/2, 1) == 0 unless facts prove x even. */
  {
    ixs_node *y = ixs_sym(ctx, "mod_one_piecewise_y");
    ixs_node *half = ixs_div(ctx, x, ixs_int(ctx, 2));
    ixs_node *rem = ixs_mod(ctx, half, ixs_int(ctx, 1));
    ixs_node *cond = ixs_cmp(ctx, rem, IXS_CMP_EQ, ixs_int(ctx, 0));
    ixs_node *values[2] = {x, y};
    ixs_node *conditions[2] = {cond, ixs_true(ctx)};
    ixs_node *piecewise = ixs_pw(ctx, 2, values, conditions);
    ixs_node *x_even = ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 2)),
                               IXS_CMP_EQ, ixs_int(ctx, 0));

    CHECK(ixs_simplify(ctx, cond, NULL, 0) == cond);
    CHECK(ixs_simplify(ctx, piecewise, NULL, 0) == piecewise);
    CHECK(ixs_simplify(ctx, cond, &x_even, 1) == ixs_true(ctx));
    CHECK(ixs_simplify(ctx, piecewise, &x_even, 1) == x);
  }

  /* ceiling(Mod(-Mod(y/2, 1), 1)) must NOT fold to 0.
   * At y=1: Mod(1/2, 1)=1/2, -1/2, Mod(-1/2, 1)=1/2, ceil=1. */
  {
    ixs_node *y = ixs_sym(ctx, "y");
    ixs_node *m_inner =
        ixs_mod(ctx, ixs_div(ctx, y, ixs_int(ctx, 2)), ixs_int(ctx, 1));
    ixs_node *m_outer =
        ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, -1), m_inner), ixs_int(ctx, 1));
    ixs_node *ce = ixs_ceil(ctx, m_outer);
    ixs_node *assumes[] = {
        ixs_cmp(ctx, y, IXS_CMP_GE, ixs_int(ctx, 0)),
        ixs_cmp(ctx, y, IXS_CMP_LE, ixs_int(ctx, 10)),
    };
    ixs_node *r = ixs_simplify(ctx, ce, assumes, 2);
    CHECK(r != ixs_int(ctx, 0));
  }

  /* Non-integer Mod dividends must not feed divisibility bitfacts.
   * At x=1,z=0 this is ceil(1/4) == 1; the unsafe rewrite produced 1/4. */
  {
    ixs_node *z = ixs_sym(ctx, "z");
    ixs_node *m =
        ixs_mod(ctx, ixs_div(ctx, x, ixs_int(ctx, 2)), ixs_int(ctx, 1));
    ixs_node *expr =
        ixs_ceil(ctx, ixs_add(ctx, ixs_div(ctx, z, ixs_int(ctx, 3)),
                              ixs_mul(ctx, ixs_rat(ctx, 1, 2), m)));
    ixs_node *r = ixs_simplify(ctx, expr, NULL, 0);
    ixs_node *targets[] = {x, z};
    ixs_node *repls[] = {ixs_int(ctx, 1), ixs_int(ctx, 0)};
    ixs_node *raw_v = ixs_simplify(
        ctx, ixs_subs_multi(ctx, expr, 2, targets, repls), NULL, 0);
    ixs_node *simp_v =
        ixs_simplify(ctx, ixs_subs_multi(ctx, r, 2, targets, repls), NULL, 0);
    CHECK(raw_v == ixs_int(ctx, 1));
    CHECK(simp_v == raw_v);
  }

  /* Division with compound MUL divisor: a / (a/c) -> c */
  {
    ixs_node *K = ixs_sym(ctx, "K");
    ixs_node *K_over_32 = ixs_div(ctx, K, ixs_int(ctx, 32));

    /* K / (K/32) -> 32 */
    ixs_node *q1 = ixs_div(ctx, K, K_over_32);
    CHECK(ixs_node_int_val(q1) == 32);

    /* 8*K / (K/32) -> 256 */
    ixs_node *q2 = ixs_div(ctx, ixs_mul(ctx, ixs_int(ctx, 8), K), K_over_32);
    CHECK(ixs_node_int_val(q2) == 256);
  }

  /* Symbolic modulus: Mod(T0 + 8*K*T1, K/32) -> Mod(T0, K/32) */
  {
    ixs_node *K = ixs_sym(ctx, "K");
    ixs_node *t0 = ixs_sym(ctx, "t0");
    ixs_node *t1 = ixs_sym(ctx, "t1");
    ixs_node *t2 = ixs_sym(ctx, "t2");
    ixs_node *K32 = ixs_div(ctx, K, ixs_int(ctx, 32));
    ixs_node *eight_K_t1 = ixs_mul(ctx, ixs_int(ctx, 8), ixs_mul(ctx, K, t1));
    ixs_node *K_t2 = ixs_mul(ctx, K, t2);

    /* Single addend stripped */
    ixs_node *m1 = ixs_mod(ctx, ixs_add(ctx, t0, eight_K_t1), K32);
    CHECK(m1 == ixs_mod(ctx, t0, K32));

    /* Two addends stripped */
    ixs_node *sum = ixs_add(ctx, t0, ixs_add(ctx, eight_K_t1, K_t2));
    ixs_node *m2 = ixs_mod(ctx, sum, K32);
    CHECK(m2 == ixs_mod(ctx, t0, K32));

    /* Non-multiple addend preserved */
    ixs_node *m3 = ixs_mod(ctx, ixs_add(ctx, t0, t1), K32);
    CHECK(m3 != ixs_mod(ctx, t0, K32));
  }

  /* Scale factor extraction: Mod(16*a + 1, 128*d) -> 16*Mod(a, 8*d) + 1
   * The rule is bounds-gated, so it fires only during ixs_simplify. */
  {
    ixs_node *a = ixs_sym(ctx, "a");
    ixs_node *d = ixs_sym(ctx, "d");
    ixs_node *lhs = ixs_mod(
        ctx, ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 16), a), ixs_int(ctx, 1)),
        ixs_mul(ctx, ixs_int(ctx, 128), d));
    ixs_node *eight_d = ixs_mul(ctx, ixs_int(ctx, 8), d);
    ixs_node *expected =
        ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 16), ixs_mod(ctx, a, eight_d)),
                ixs_int(ctx, 1));
    ixs_node *simplified = ixs_simplify(ctx, lhs, NULL, 0);
    CHECK(simplified == expected);

    /* Zero remainder: Mod(16*a, 128*d) -> 16*Mod(a, 8*d) */
    ixs_node *lhs2 = ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, 16), a),
                             ixs_mul(ctx, ixs_int(ctx, 128), d));
    ixs_node *exp2 = ixs_mul(ctx, ixs_int(ctx, 16), ixs_mod(ctx, a, eight_d));
    ixs_node *simp2 = ixs_simplify(ctx, lhs2, NULL, 0);
    CHECK(simp2 == exp2);

    /* Coprime: Mod(3*a + 1, 7*d) -- gcd(3,7)=1, no extraction. */
    ixs_node *coprime = ixs_mod(
        ctx, ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 3), a), ixs_int(ctx, 1)),
        ixs_mul(ctx, ixs_int(ctx, 7), d));
    CHECK(ixs_node_tag(coprime) == IXS_MOD);
    CHECK(ixs_simplify(ctx, coprime, NULL, 0) == coprime);

    /* r >= g: Mod(16*a + 17, 128*d) -- r=17 >= gcd(16,128)=16. */
    ixs_node *big_r = ixs_mod(
        ctx, ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 16), a), ixs_int(ctx, 17)),
        ixs_mul(ctx, ixs_int(ctx, 128), d));
    CHECK(ixs_simplify(ctx, big_r, NULL, 0) == big_r);
  }

  /* Congruence-gated scale extraction for a symbolic modulus. */
  {
    ixs_node *a = ixs_sym(ctx, "scale_a");
    ixs_node *m = ixs_sym(ctx, "scale_m");
    ixs_node *lhs = ixs_mod(
        ctx, ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 16), a), ixs_int(ctx, 1)),
        m);
    ixs_node *divisible = ixs_cmp(ctx, ixs_mod(ctx, m, ixs_int(ctx, 16)),
                                  IXS_CMP_EQ, ixs_int(ctx, 0));
    ixs_node *positive = ixs_cmp(ctx, m, IXS_CMP_GE, ixs_int(ctx, 1));
    ixs_node *new_mod = ixs_div(ctx, m, ixs_int(ctx, 16));
    ixs_node *expected =
        ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 16), ixs_mod(ctx, a, new_mod)),
                ixs_int(ctx, 1));

    CHECK(ixs_simplify(ctx, lhs, &divisible, 1) == expected);
    CHECK(ixs_simplify(ctx, lhs, &positive, 1) == lhs);
  }

  /* Clear exact rational scales before Mod:
   * Mod((16*q + 4*r) / 4, 2) -> Mod(r, 2). */
  {
    ixs_node *q = ixs_sym(ctx, "q");
    ixs_node *r = ixs_sym(ctx, "r");
    ixs_node *inner = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 16), q),
                              ixs_mul(ctx, ixs_int(ctx, 4), r));
    ixs_node *scaled = ixs_div(ctx, inner, ixs_int(ctx, 4));
    ixs_node *result = ixs_mod(ctx, scaled, ixs_int(ctx, 2));
    CHECK(result == ixs_mod(ctx, r, ixs_int(ctx, 2)));

    inner = ixs_add(ctx, ixs_int(ctx, 64), inner);
    scaled = ixs_div(ctx, inner, ixs_int(ctx, 4));
    result = ixs_mod(ctx, scaled, ixs_int(ctx, 2));
    CHECK(result == ixs_mod(ctx, r, ixs_int(ctx, 2)));

    inner = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), q), r);
    scaled = ixs_div(ctx, inner, ixs_int(ctx, 4));
    result = ixs_mod(ctx, scaled, ixs_int(ctx, 2));
    CHECK(ixs_node_tag(result) == IXS_MOD);
    CHECK(ixs_node_binary_lhs(result) == scaled);
  }
}

static void test_mod_extract_constant_residue(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *lane = ixs_sym(ctx, "residue_lane");
  ixs_node *tile = ixs_sym(ctx, "residue_tile");
  ixs_node *modulus = ixs_int(ctx, INT64_C(4294967296));
  ixs_node *aligned =
      ixs_add(ctx, ixs_int(ctx, INT64_C(2147483712)),
              ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 128), lane),
                      ixs_mul(ctx, ixs_int(ctx, 256), tile)));
  ixs_node *aligned_mod = ixs_mod(ctx, aligned, modulus);
  ixs_node *grid_base =
      ixs_add(ctx, ixs_int(ctx, INT64_C(2147483648)),
              ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 128), lane),
                      ixs_mul(ctx, ixs_int(ctx, 256), tile)));
  ixs_node *grid_mod = ixs_mod(ctx, grid_base, modulus);
  int64_t residue;

  CHECK(aligned_mod == ixs_add(ctx, grid_mod, ixs_int(ctx, 64)));
  for (residue = 1; residue <= 3; residue++) {
    ixs_node *shifted = ixs_add(ctx, aligned, ixs_int(ctx, residue));
    ixs_node *expected = ixs_add(ctx, aligned_mod, ixs_int(ctx, residue));
    CHECK(ixs_mod(ctx, shifted, modulus) == expected);
  }

  /* The common grid is gcd(modulus, coefficients), even when a coefficient
   * does not itself divide the modulus. */
  {
    ixs_node *x = ixs_sym(ctx, "residue_gcd_x");
    ixs_node *shifted =
        ixs_add(ctx, ixs_int(ctx, 23), ixs_mul(ctx, ixs_int(ctx, 6), x));
    ixs_node *aligned_inner =
        ixs_add(ctx, ixs_int(ctx, 22), ixs_mul(ctx, ixs_int(ctx, 6), x));
    ixs_node *expected = ixs_add(ctx, ixs_int(ctx, 1),
                                 ixs_mod(ctx, aligned_inner, ixs_int(ctx, 16)));
    CHECK(ixs_mod(ctx, shifted, ixs_int(ctx, 16)) == expected);
  }

  /* No common grid and non-integer addends stay untouched.  Negative
   * constants use their Euclidean residue. */
  {
    ixs_node *x = ixs_sym(ctx, "residue_negative_x");
    ixs_node *coprime = ixs_mod(
        ctx, ixs_add(ctx, ixs_int(ctx, 23), ixs_mul(ctx, ixs_int(ctx, 5), x)),
        ixs_int(ctx, 16));
    ixs_node *noninteger = ixs_mod(
        ctx,
        ixs_add(ctx, ixs_int(ctx, 129), ixs_mul(ctx, ixs_rat(ctx, 1, 2), x)),
        ixs_int(ctx, 256));
    ixs_node *negative_constant = ixs_mod(
        ctx,
        ixs_add(ctx, ixs_int(ctx, INT64_MIN), ixs_mul(ctx, ixs_int(ctx, 6), x)),
        ixs_int(ctx, 9));
    CHECK(ixs_node_tag(coprime) == IXS_MOD);
    CHECK(ixs_node_tag(noninteger) == IXS_MOD);
    CHECK(strcmp(pr(negative_constant), "1 + Mod(6*residue_negative_x, 9)") ==
          0);
  }
}

static void test_mod_divisor_contract(void) {
  ixs_ctx *ctx = ctx_create_or_die();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *m = ixs_sym(ctx, "m");
  ixs_node *symbolic = ixs_mod(ctx, x, m);
  ixs_node *assumption;
  ixs_node *assumptions[2];
  ixs_node *result;

  CHECK(ixs_node_tag(ixs_mod(ctx, x, ixs_int(ctx, 3))) == IXS_MOD);
  CHECK(ixs_node_tag(ixs_mod(ctx, x, ixs_rat(ctx, 1, 2))) == IXS_MOD);
  CHECK(ixs_node_int_val(
            ixs_mod(ctx, ixs_int(ctx, INT64_MIN + 1), ixs_int(ctx, 2))) == 1);
  CHECK(symbolic && ixs_node_tag(symbolic) == IXS_MOD);

  result = ixs_mod(ctx, x, ixs_int(ctx, 0));
  CHECK(result && ixs_is_domain_error(result));
  CHECK(strstr(ixs_ctx_error(ctx, ixs_ctx_nerrors(ctx) - 1), "zero") != NULL);
  ixs_ctx_clear_errors(ctx);

  result = ixs_mod(ctx, x, ixs_int(ctx, -3));
  CHECK(result && ixs_is_domain_error(result));
  CHECK(strstr(ixs_ctx_error(ctx, ixs_ctx_nerrors(ctx) - 1), "negative") !=
        NULL);
  ixs_ctx_clear_errors(ctx);

  result = ixs_mod(ctx, x, ixs_rat(ctx, -1, 2));
  CHECK(result && ixs_is_domain_error(result));
  ixs_ctx_clear_errors(ctx);

  result = ixs_mod(ctx, x, ixs_int(ctx, INT64_MIN));
  CHECK(result && ixs_is_domain_error(result));
  ixs_ctx_clear_errors(ctx);

  assumption = ixs_cmp(ctx, m, IXS_CMP_GT, ixs_int(ctx, 0));
  result = ixs_simplify(ctx, symbolic, &assumption, 1);
  CHECK(result == symbolic);

  assumption = ixs_cmp(ctx, m, IXS_CMP_LT, ixs_int(ctx, 0));
  result = ixs_simplify(ctx, symbolic, &assumption, 1);
  CHECK(result && ixs_is_domain_error(result));
  CHECK(strstr(ixs_ctx_error(ctx, ixs_ctx_nerrors(ctx) - 1), "negative") !=
        NULL);
  ixs_ctx_clear_errors(ctx);

  assumption = ixs_cmp(ctx, m, IXS_CMP_LE, ixs_int(ctx, 0));
  result = ixs_simplify(ctx, symbolic, &assumption, 1);
  CHECK(result && ixs_is_domain_error(result));
  CHECK(strstr(ixs_ctx_error(ctx, ixs_ctx_nerrors(ctx) - 1), "not positive") !=
        NULL);
  ixs_ctx_clear_errors(ctx);

  assumption = ixs_cmp(ctx, m, IXS_CMP_EQ, ixs_int(ctx, 0));
  result = ixs_simplify(ctx, symbolic, &assumption, 1);
  CHECK(result && ixs_is_domain_error(result));
  CHECK(strstr(ixs_ctx_error(ctx, ixs_ctx_nerrors(ctx) - 1), "zero") != NULL);
  ixs_ctx_clear_errors(ctx);

  assumptions[0] = ixs_cmp(ctx, m, IXS_CMP_GT, ixs_int(ctx, 0));
  assumptions[1] = ixs_cmp(ctx, m, IXS_CMP_LT, ixs_int(ctx, 0));
  result = ixs_simplify(ctx, symbolic, assumptions, 2);
  CHECK(result && !ixs_is_error(result));

  result = ixs_subs(ctx, symbolic, m, ixs_int(ctx, -3));
  CHECK(result && ixs_is_domain_error(result));
  ixs_ctx_clear_errors(ctx);
  result = ixs_subs(ctx, symbolic, m, ixs_int(ctx, 3));
  CHECK(result && ixs_node_tag(result) == IXS_MOD);

  ixs_ctx_destroy(ctx);
}

static void test_boolean(void) {
  ixs_ctx *ctx = get_ctx();

  /* Boolean constants are integer 1/0. */
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *cmp = ixs_cmp(ctx, x, IXS_CMP_GT, ixs_int(ctx, 0));
  CHECK(ixs_node_tag(ixs_true(ctx)) == IXS_INT);
  CHECK(ixs_node_int_val(ixs_true(ctx)) == 1);
  CHECK(ixs_node_tag(ixs_false(ctx)) == IXS_INT);
  CHECK(ixs_node_int_val(ixs_false(ctx)) == 0);

  /* 1 & bool -> bool, but 1 & arbitrary integer stays bitwise. */
  CHECK(ixs_and(ctx, ixs_true(ctx), cmp) == cmp);
  CHECK(ixs_node_tag(ixs_and(ctx, ixs_true(ctx), x)) == IXS_AND);

  /* 0 & x -> 0 */
  CHECK(ixs_and(ctx, ixs_false(ctx), cmp) == ixs_false(ctx));

  /* 1 | bool -> 1, but 1 | arbitrary integer stays bitwise. */
  CHECK(ixs_or(ctx, ixs_true(ctx), cmp) == ixs_true(ctx));
  CHECK(ixs_node_tag(ixs_or(ctx, ixs_true(ctx), x)) == IXS_OR);

  /* Integer constants fold with bitwise semantics. */
  CHECK(ixs_node_int_val(ixs_and(ctx, ixs_int(ctx, 6), ixs_int(ctx, 3))) == 2);
  CHECK(ixs_node_int_val(ixs_or(ctx, ixs_int(ctx, 4), ixs_int(ctx, 1))) == 5);

  /* A proven non-integer operand is a domain error. */
  {
    ixs_node *bad = ixs_and(ctx, ixs_rat(ctx, 1, 2), x);
    CHECK(ixs_is_domain_error(bad));
    CHECK(ixs_floor(ctx, bad) == bad);
  }

  /* ~ is logical truthiness, not bitwise complement. */
  CHECK(ixs_not(ctx, ixs_true(ctx)) == ixs_false(ctx));
  CHECK(ixs_not(ctx, ixs_int(ctx, 42)) == ixs_false(ctx));

  /* ~~bool -> bool */
  CHECK(ixs_not(ctx, ixs_not(ctx, cmp)) == cmp);

  /* ~~arbitrary integer -> x != 0 */
  {
    ixs_node *nnx = ixs_not(ctx, ixs_not(ctx, x));
    CHECK(ixs_node_tag(nnx) == IXS_CMP);
    CHECK(ixs_node_cmp_op(nnx) == IXS_CMP_NE);
  }
}

static void test_boolean_piecewise(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "bool_piecewise_x");
  ixs_node *zero = ixs_false(ctx);
  ixs_node *one = ixs_true(ctx);
  ixs_node *condition = ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 4));
  ixs_node *values[] = {one, zero};
  ixs_node *conditions[] = {condition, one};
  ixs_node *selector = ixs_pw(ctx, 2, values, conditions);

  CHECK(selector == condition);
  CHECK(ixs_cmp(ctx, selector, IXS_CMP_NE, zero) == condition);
  CHECK(ixs_cmp(ctx, selector, IXS_CMP_EQ, zero) == ixs_not(ctx, condition));

  {
    ixs_node *nested_conditions[] = {selector, one};
    ixs_node *nested = ixs_pw(ctx, 2, values, nested_conditions);
    CHECK(nested == condition);
    CHECK(ixs_cmp(ctx, nested, IXS_CMP_NE, zero) == condition);
  }

  {
    ixs_node *inverted_values[] = {zero, one};
    CHECK(ixs_pw(ctx, 2, inverted_values, conditions) ==
          ixs_not(ctx, condition));
  }

  {
    ixs_node *non_boolean_values[] = {ixs_int(ctx, 2), zero};
    ixs_node *partial_values[] = {one};
    ixs_node *partial_conditions[] = {condition};
    ixs_node *non_boolean = ixs_pw(ctx, 2, non_boolean_values, conditions);
    ixs_node *partial = ixs_pw(ctx, 1, partial_values, partial_conditions);
    ixs_node *numeric_truth = ixs_cmp(ctx, x, IXS_CMP_NE, zero);

    CHECK(ixs_node_tag(non_boolean) == IXS_PIECEWISE);
    CHECK(ixs_node_tag(partial) == IXS_PIECEWISE);
    CHECK(ixs_node_tag(numeric_truth) == IXS_CMP);
    CHECK(numeric_truth != x);
  }
}

static bool assoc_has_arg(ixs_node *node, ixs_node *arg) {
  uint32_t i;
  for (i = 0; i < ixs_node_assoc_nargs(node); i++) {
    if (ixs_node_assoc_arg(node, i) == arg)
      return true;
  }
  return false;
}

static void check_flat_three(ixs_node *node, ixs_tag tag, ixs_node *a,
                             ixs_node *b, ixs_node *c) {
  uint32_t i;
  CHECK(ixs_node_tag(node) == tag);
  CHECK(ixs_node_assoc_nargs(node) == 3);
  CHECK(assoc_has_arg(node, a));
  CHECK(assoc_has_arg(node, b));
  CHECK(assoc_has_arg(node, c));
  for (i = 0; i < ixs_node_assoc_nargs(node); i++)
    CHECK(ixs_node_tag(ixs_node_assoc_arg(node, i)) != tag);
}

typedef const ixs_node *(*assoc_binary_fn)(ixs_session *, const ixs_node *,
                                           const ixs_node *);
typedef const ixs_node *(*assoc_many_fn)(ixs_session *, uint32_t,
                                         const ixs_node *const *);

static void check_all_three_associations(ixs_ctx *ctx, ixs_tag tag,
                                         assoc_binary_fn binary,
                                         assoc_many_fn many, ixs_node *a,
                                         ixs_node *b, ixs_node *c) {
  static const unsigned char permutations[6][3] = {
      {0, 1, 2}, {0, 2, 1}, {1, 0, 2}, {1, 2, 0}, {2, 0, 1}, {2, 1, 0},
  };
  ixs_node *operands[3] = {a, b, c};
  ixs_session *session = IXS_TEST_SESSION(ctx);
  ixs_node *expected = many(session, 3, operands);
  size_t i;

  check_flat_three(expected, tag, a, b, c);
  for (i = 0; i < 6; i++) {
    ixs_node *args[3] = {operands[permutations[i][0]],
                         operands[permutations[i][1]],
                         operands[permutations[i][2]]};
    ixs_node *left =
        binary(session, binary(session, args[0], args[1]), args[2]);
    ixs_node *right =
        binary(session, args[0], binary(session, args[1], args[2]));
    CHECK(many(session, 3, args) == expected);
    CHECK(left == expected);
    CHECK(right == expected);
  }
}

static void test_flat_associative_nodes(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *a = ixs_sym(ctx, "assoc_a");
  ixs_node *b = ixs_sym(ctx, "assoc_b");
  ixs_node *c = ixs_sym(ctx, "assoc_c");
  ixs_node *x = ixs_sym(ctx, "assoc_x");
  ixs_node *y = ixs_sym(ctx, "assoc_y");
  ixs_node *m = ixs_sym(ctx, "assoc_m");
  ixs_node *args[5];
  ixs_node *perm[3] = {c, a, b};
  ixs_node *saved[3] = {c, a, b};
  ixs_node *half = ixs_div(ctx, x, ixs_int(ctx, 2));
  ixs_node *partial = ixs_mod(ctx, x, m);

  /* Do not seed the shared rule-stats context with test-only pair nodes. */
  {
    ixs_ctx *permutation_ctx = ctx_create_or_die();
    ixs_node *pa = ixs_sym(permutation_ctx, "perm_a");
    ixs_node *pb = ixs_sym(permutation_ctx, "perm_b");
    ixs_node *pc = ixs_sym(permutation_ctx, "perm_c");
    check_all_three_associations(permutation_ctx, IXS_MAX, (ixs_max),
                                 (ixs_max_many), pa, pb, pc);
    check_all_three_associations(permutation_ctx, IXS_MIN, (ixs_min),
                                 (ixs_min_many), pa, pb, pc);
    check_all_three_associations(permutation_ctx, IXS_XOR, (ixs_xor),
                                 (ixs_xor_many), pa, pb, pc);
    check_all_three_associations(permutation_ctx, IXS_AND, (ixs_and),
                                 (ixs_and_many), pa, pb, pc);
    check_all_three_associations(permutation_ctx, IXS_OR, (ixs_or),
                                 (ixs_or_many), pa, pb, pc);
    ixs_ctx_destroy(permutation_ctx);
  }
  (void)ixs_or_many(ctx, 3, perm);
  CHECK(perm[0] == saved[0] && perm[1] == saved[1] && perm[2] == saved[2]);

  args[0] = x;
  args[1] = x;
  args[2] = ixs_int(ctx, 3);
  args[3] = ixs_int(ctx, 7);
  args[4] = ixs_int(ctx, 3);
  CHECK(ixs_max_many(ctx, 5, args) == ixs_max(ctx, x, ixs_int(ctx, 7)));
  CHECK(ixs_min_many(ctx, 5, args) == ixs_min(ctx, x, ixs_int(ctx, 3)));

  args[0] = x;
  args[1] = x;
  CHECK(ixs_xor_many(ctx, 2, args) == ixs_int(ctx, 0));
  args[2] = y;
  CHECK(ixs_xor_many(ctx, 3, args) == y);
  args[2] = x;
  CHECK(ixs_xor_many(ctx, 3, args) == x);

  args[0] = x;
  args[1] = x;
  args[2] = ixs_int(ctx, -1);
  CHECK(ixs_and_many(ctx, 3, args) == x);
  args[2] = ixs_int(ctx, 0);
  CHECK(ixs_or_many(ctx, 3, args) == x);

  CHECK(ixs_and_many(ctx, 0, NULL) == ixs_int(ctx, -1));
  CHECK(ixs_or_many(ctx, 0, NULL) == ixs_int(ctx, 0));
  CHECK(ixs_xor_many(ctx, 0, NULL) == ixs_int(ctx, 0));
  CHECK(ixs_is_domain_error(ixs_max_many(ctx, 0, NULL)));
  CHECK(ixs_is_domain_error(ixs_min_many(ctx, 0, NULL)));
  CHECK(ixs_max_many(ctx, 1, &x) == x);
  CHECK(ixs_min_many(ctx, 1, &x) == x);
  CHECK(ixs_xor_many(ctx, 1, &x) == x);
  CHECK(ixs_xor_many(ctx, 1, &partial) == partial);
  CHECK(ixs_and_many(ctx, 1, &partial) == partial);
  CHECK(ixs_or_many(ctx, 1, &partial) == partial);
  CHECK(ixs_node_tag(ixs_xor_many(ctx, 1, &half)) == IXS_XOR);
  CHECK(ixs_node_tag(ixs_and_many(ctx, 1, &half)) == IXS_AND);
  CHECK(ixs_node_tag(ixs_or_many(ctx, 1, &half)) == IXS_OR);

  args[0] = partial;
  args[1] = partial;
  args[2] = partial;
  args[3] = partial;
  CHECK(ixs_xor_many(ctx, 3, args) == ixs_xor_many(ctx, 1, &partial));
  CHECK(ixs_xor_many(ctx, 4, args) == ixs_xor_many(ctx, 2, args));

  CHECK(ixs_node_tag(ixs_and(ctx, ixs_int(ctx, 0), half)) == IXS_AND);
  CHECK(ixs_node_tag(ixs_or(ctx, ixs_int(ctx, -1), half)) == IXS_OR);
  CHECK(ixs_node_tag(ixs_xor(ctx, half, half)) == IXS_XOR);
  CHECK(ixs_node_tag(ixs_and(ctx, ixs_int(ctx, 0), partial)) == IXS_AND);
  CHECK(ixs_node_tag(ixs_or(ctx, ixs_int(ctx, -1), partial)) == IXS_OR);
  CHECK(ixs_node_tag(ixs_xor(ctx, partial, partial)) == IXS_XOR);
  {
    ixs_node *guard = ixs_and(ctx, ixs_int(ctx, 0), partial);
    ixs_node *self_eq = ixs_cmp(ctx, guard, IXS_CMP_EQ, guard);
    ixs_node *zero_eq = ixs_cmp(ctx, guard, IXS_CMP_EQ, ixs_int(ctx, 0));
    ixs_node *zero_target = m;
    ixs_node *zero_replacement = ixs_int(ctx, 0);
    ixs_node *three_replacement = ixs_int(ctx, 3);
    CHECK(ixs_node_tag(self_eq) == IXS_CMP);
    CHECK(ixs_node_tag(zero_eq) == IXS_CMP);
    CHECK(ixs_is_domain_error(
        ixs_subs(ctx, self_eq, zero_target, zero_replacement)));
    CHECK(ixs_is_domain_error(
        ixs_subs(ctx, zero_eq, zero_target, zero_replacement)));
    CHECK(ixs_subs(ctx, self_eq, zero_target, three_replacement) ==
          ixs_true(ctx));
    CHECK(ixs_subs(ctx, zero_eq, zero_target, three_replacement) ==
          ixs_true(ctx));
  }
  CHECK(ixs_and(ctx, ixs_and(ctx, ixs_int(ctx, 0), x), partial) ==
        ixs_and(ctx, ixs_int(ctx, 0), ixs_and(ctx, x, partial)));
  CHECK(ixs_xor(ctx, ixs_xor(ctx, partial, partial), x) ==
        ixs_xor(ctx, partial, ixs_xor(ctx, partial, x)));
  CHECK(ixs_or(ctx, ixs_int(ctx, -1), x) == ixs_int(ctx, -1));

  args[0] = ixs_int(ctx, INT64_MIN);
  args[1] = ixs_int(ctx, -1);
  args[2] = ixs_int(ctx, 1);
  CHECK(ixs_node_int_val(ixs_xor_many(ctx, 3, args)) == INT64_MAX - 1);
  args[2] = ixs_int(ctx, -2);
  CHECK(ixs_node_int_val(ixs_and_many(ctx, 3, args)) == INT64_MIN);
  args[1] = ixs_int(ctx, 0);
  args[2] = ixs_int(ctx, 1);
  CHECK(ixs_node_int_val(ixs_or_many(ctx, 3, args)) == INT64_MIN + 1);

  CHECK(ixs_is_domain_error(ixs_xor(ctx, ixs_rat(ctx, 1, 2), x)));
  CHECK(ixs_is_domain_error(ixs_and(ctx, ixs_rat(ctx, 1, 2), x)));
  CHECK(ixs_is_domain_error(ixs_or(ctx, ixs_rat(ctx, 1, 2), x)));

  {
    ixs_node *replacement = ixs_sym(ctx, "assoc_replacement");
    ixs_node *source_args[3] = {a, b, c};
    ixs_node *expected_args[3] = {a, b, replacement};
    CHECK(ixs_subs(ctx, ixs_max_many(ctx, 3, source_args), c, replacement) ==
          ixs_max_many(ctx, 3, expected_args));
    CHECK(ixs_subs(ctx, ixs_min_many(ctx, 3, source_args), c, replacement) ==
          ixs_min_many(ctx, 3, expected_args));
    CHECK(ixs_subs(ctx, ixs_xor_many(ctx, 3, source_args), c, replacement) ==
          ixs_xor_many(ctx, 3, expected_args));
    CHECK(ixs_subs(ctx, ixs_and_many(ctx, 3, source_args), c, replacement) ==
          ixs_and_many(ctx, 3, expected_args));
    CHECK(ixs_subs(ctx, ixs_or_many(ctx, 3, source_args), c, replacement) ==
          ixs_or_many(ctx, 3, expected_args));
  }

  {
    ixs_node *domain = ixs_div(ctx, ixs_int(ctx, 1), ixs_int(ctx, 0));
    ixs_node *parse = ixs_parse(ctx, "?", 1);
    ixs_node *mixed[3] = {domain, parse, x};
    CHECK(ixs_xor_many(ctx, 3, mixed) == parse);
    mixed[2] = NULL;
    CHECK(ixs_or_many(ctx, 3, mixed) == NULL);
  }
}

static void test_xor_known_bit_simplification(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *t0 = ixs_sym(ctx, "$T0");
  ixs_node *low = ixs_mod(ctx, t0, ixs_int(ctx, 8));
  ixs_node *quad = ixs_floor(
      ctx, ixs_div(ctx, ixs_mod(ctx, t0, ixs_int(ctx, 64)), ixs_int(ctx, 16)));
  ixs_node *shifted = ixs_mul(ctx, ixs_int(ctx, 8), quad);
  ixs_node *expr = ixs_xor(ctx, low, shifted);
  ixs_node *r = ixs_simplify(ctx, expr, NULL, 0);
  ixs_node *expected = ixs_simplify(ctx, ixs_add(ctx, low, shifted), NULL, 0);

  CHECK(r == expected);

  {
    ixs_node *x = ixs_sym(ctx, "xor_partial_x");
    ixs_node *m = ixs_sym(ctx, "xor_partial_m");
    ixs_node *selector = ixs_sym(ctx, "xor_partial_selector");
    ixs_node *partial = ixs_mod(ctx, x, m);
    ixs_node *guard = ixs_and(ctx, ixs_int(ctx, 0), partial);
    ixs_node *delta_expr = ixs_sub(
        ctx, ixs_xor(ctx, selector, ixs_add(ctx, guard, ixs_int(ctx, 2))),
        ixs_xor(ctx, selector, guard));
    CHECK(strstr(pr(delta_expr), "xor") != NULL);
    CHECK(ixs_check_defined(ctx, delta_expr, NULL, 0) == IXS_CHECK_UNKNOWN);
  }

  {
    ixs_node *delta_expr =
        ixs_add(ctx,
                ixs_mul(ctx, ixs_int(ctx, 16),
                        ixs_xor(ctx, low, ixs_add(ctx, quad, ixs_int(ctx, 4)))),
                ixs_mul(ctx, ixs_int(ctx, -16), ixs_xor(ctx, low, quad)));
    int v;

    r = ixs_simplify(ctx, delta_expr, NULL, 0);
    CHECK(strstr(pr(r), "xor") == NULL);

    for (v = 0; v < 64; v++) {
      ixs_node *replacement = ixs_int(ctx, v);
      ixs_node *raw_v = ixs_simplify(
          ctx, ixs_subs(ctx, delta_expr, t0, replacement), NULL, 0);
      ixs_node *simp_v =
          ixs_simplify(ctx, ixs_subs(ctx, r, t0, replacement), NULL, 0);
      CHECK(raw_v == simp_v);
    }
  }

  {
    ixs_node *x = ixs_sym(ctx, "x");
    ixs_node *a = ixs_sym(ctx, "a");
    ixs_node *base = ixs_and(ctx, x, ixs_int(ctx, 3));
    ixs_node *delta_expr =
        ixs_add(ctx,
                ixs_mul(ctx, ixs_int(ctx, 16),
                        ixs_xor(ctx, a, ixs_add(ctx, base, ixs_int(ctx, 5)))),
                ixs_mul(ctx, ixs_int(ctx, -16),
                        ixs_xor(ctx, a, ixs_add(ctx, base, ixs_int(ctx, 1)))));
    ixs_node *targets[] = {x, a};
    ixs_node *repls[] = {ixs_int(ctx, 3), ixs_int(ctx, 4)};
    ixs_node *raw_v = ixs_simplify(
        ctx, ixs_subs_multi(ctx, delta_expr, 2, targets, repls), NULL, 0);
    ixs_node *simp_v;

    r = ixs_simplify(ctx, delta_expr, NULL, 0);
    simp_v =
        ixs_simplify(ctx, ixs_subs_multi(ctx, r, 2, targets, repls), NULL, 0);
    CHECK(raw_v == ixs_int(ctx, 192));
    CHECK(simp_v == raw_v);
  }

  {
    int64_t big = (int64_t)1 << 62;
    ixs_node *y = ixs_sym(ctx, "y");
    ixs_node *base = ixs_and(ctx, y, ixs_int(ctx, 3));
    ixs_node *delta_expr = ixs_sub(
        ctx,
        ixs_xor(ctx, ixs_int(ctx, big), ixs_add(ctx, base, ixs_int(ctx, big))),
        ixs_xor(ctx, ixs_int(ctx, big), base));
    ixs_node *r = ixs_simplify(ctx, delta_expr, NULL, 0);
    int v;

    CHECK(r != NULL && !ixs_is_error(r));
    for (v = 0; v < 4; v++) {
      ixs_node *replacement = ixs_int(ctx, v);
      ixs_node *raw_v =
          ixs_simplify(ctx, ixs_subs(ctx, delta_expr, y, replacement), NULL, 0);
      ixs_node *simp_v =
          ixs_simplify(ctx, ixs_subs(ctx, r, y, replacement), NULL, 0);
      CHECK(raw_v == simp_v);
    }
  }

  {
    ixs_node *b = ixs_sym(ctx, "xor_add_b");
    ixs_node *c = ixs_sym(ctx, "xor_add_c");
    ixs_node *d = ixs_sym(ctx, "xor_add_d");
    ixs_node *assumes[] = {
        ixs_cmp(ctx, b, IXS_CMP_GE, ixs_int(ctx, 0)),
        ixs_cmp(ctx, b, IXS_CMP_LE, ixs_int(ctx, 1)),
        ixs_cmp(ctx, c, IXS_CMP_GE, ixs_int(ctx, 0)),
        ixs_cmp(ctx, c, IXS_CMP_LE, ixs_int(ctx, 1)),
        ixs_cmp(ctx, d, IXS_CMP_GE, ixs_int(ctx, 0)),
        ixs_cmp(ctx, d, IXS_CMP_LE, ixs_int(ctx, 1)),
    };
    ixs_node *four_b = ixs_mul(ctx, ixs_int(ctx, 4), b);
    ixs_node *eight_c = ixs_mul(ctx, ixs_int(ctx, 8), c);
    ixs_node *sixteen_d = ixs_mul(ctx, ixs_int(ctx, 16), d);
    ixs_node *inner0 =
        ixs_xor(ctx, ixs_add(ctx, ixs_int(ctx, 32), four_b), eight_c);
    ixs_node *inner1 =
        ixs_xor(ctx, ixs_add(ctx, ixs_int(ctx, 33), four_b), eight_c);
    ixs_node *nested0 = ixs_xor(ctx, sixteen_d, inner0);
    ixs_node *nested1 = ixs_xor(ctx, sixteen_d, inner1);
    ixs_node *expected0 =
        ixs_add(ctx, ixs_int(ctx, 32),
                ixs_add(ctx, four_b, ixs_add(ctx, eight_c, sixteen_d)));
    ixs_node *expected1 = ixs_add(ctx, expected0, ixs_int(ctx, 1));

    CHECK(ixs_simplify(ctx, nested0, assumes, 6) == expected0);
    CHECK(ixs_simplify(ctx, nested1, assumes, 6) == expected1);
    CHECK(ixs_simplify(ctx, ixs_sub(ctx, nested1, nested0), assumes, 6) ==
          ixs_int(ctx, 1));

    CHECK(ixs_node_tag(
              ixs_simplify(ctx,
                           ixs_xor(ctx, ixs_add(ctx, ixs_int(ctx, 32), four_b),
                                   ixs_mul(ctx, ixs_int(ctx, 4), c)),
                           assumes, 6)) == IXS_XOR);
    CHECK(ixs_node_tag(
              ixs_simplify(ctx,
                           ixs_xor(ctx, ixs_add(ctx, ixs_int(ctx, 4), four_b),
                                   ixs_int(ctx, 8)),
                           assumes, 6)) == IXS_XOR);
    CHECK(
        ixs_node_tag(ixs_simplify(
            ctx, ixs_xor(ctx, ixs_sub(ctx, ixs_int(ctx, 32), four_b), eight_c),
            assumes, 6)) == IXS_XOR);
  }
}

static void test_xor_nested_cancellation(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "xor_cancel_x");
  ixs_node *y = ixs_sym(ctx, "xor_cancel_y");
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *two = ixs_int(ctx, 2);
  ixs_node *uncancelled;

  CHECK(ixs_xor(ctx, one, ixs_xor(ctx, one, x)) == x);
  CHECK(ixs_xor(ctx, ixs_xor(ctx, x, one), one) == x);
  CHECK(ixs_xor(ctx, x, ixs_xor(ctx, y, x)) == y);

  uncancelled = ixs_xor(ctx, one, ixs_xor(ctx, two, x));
  CHECK(ixs_node_tag(uncancelled) == IXS_XOR);
  CHECK(uncancelled != x);
}

static void test_simplify_with_bounds(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *T0 = ixs_sym(ctx, "$T0");

  ixs_node *assumptions[] = {
      ixs_cmp(ctx, T0, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, T0, IXS_CMP_LT, ixs_int(ctx, 256)),
  };

  /* Mod($T0, 256) with 0 <= $T0 < 256 -> $T0 */
  ixs_node *expr = ixs_mod(ctx, T0, ixs_int(ctx, 256));
  ixs_node *simplified = ixs_simplify(ctx, expr, assumptions, 2);
  CHECK(simplified == T0);
}

static void test_substitution(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");

  /* x + 1 with x=5 -> 6 */
  ixs_node *expr = ixs_add(ctx, x, ixs_int(ctx, 1));
  ixs_node *result = ixs_subs(ctx, expr, x, ixs_int(ctx, 5));
  CHECK(result && ixs_node_int_val(result) == 6);

  /* floor(x/2) with x=7 -> 3 */
  expr = ixs_floor(ctx, ixs_mul(ctx, x, ixs_rat(ctx, 1, 2)));
  result = ixs_subs(ctx, expr, x, ixs_int(ctx, 7));
  CHECK(result && ixs_node_int_val(result) == 3);

  /* Subtree replacement: replace Mod(x,4) with y in a larger expression */
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *mod_x4 = ixs_mod(ctx, x, ixs_int(ctx, 4));
  expr = ixs_add(ctx, mod_x4, ixs_int(ctx, 10));
  result = ixs_subs(ctx, expr, mod_x4, y);
  CHECK(result && strcmp(pr(result), "10 + y") == 0);

  /* Replace constant: 2 -> 3 in 2*x + 2 */
  ixs_node *two = ixs_int(ctx, 2);
  ixs_node *three = ixs_int(ctx, 3);
  expr = ixs_add(ctx, ixs_mul(ctx, two, x), two);
  result = ixs_subs(ctx, expr, two, three);
  CHECK(result && strcmp(pr(result), "3 + 3*x") == 0);

  /* No match: target not present leaves expression unchanged */
  expr = ixs_add(ctx, x, ixs_int(ctx, 1));
  result = ixs_subs(ctx, expr, y, ixs_int(ctx, 99));
  CHECK(result && strcmp(pr(result), "1 + x") == 0);

  /* Multi-occurrence: Mod(x,4) + 2*Mod(x,4) with Mod(x,4)->y gives 3*y */
  expr = ixs_add(ctx, mod_x4, ixs_mul(ctx, ixs_int(ctx, 2), mod_x4));
  result = ixs_subs(ctx, expr, mod_x4, y);
  CHECK(result && strcmp(pr(result), "3*y") == 0);
}

static void test_subs_multi(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *z = ixs_sym(ctx, "z");

  /* Simultaneous: {x->y, y->x} in x+y gives y+x = x+y (swap, not collapse). */
  {
    ixs_node *targets[] = {x, y};
    ixs_node *repls[] = {y, x};
    ixs_node *expr = ixs_add(ctx, x, ixs_mul(ctx, ixs_int(ctx, 2), y));
    ixs_node *r = ixs_subs_multi(ctx, expr, 2, targets, repls);
    CHECK(r == ixs_add(ctx, y, ixs_mul(ctx, ixs_int(ctx, 2), x)));
  }

  /* Multiple constants: {x->3, y->5} in x*y -> 15. */
  {
    ixs_node *targets[] = {x, y};
    ixs_node *repls[] = {ixs_int(ctx, 3), ixs_int(ctx, 5)};
    ixs_node *expr = ixs_mul(ctx, x, y);
    ixs_node *r = ixs_subs_multi(ctx, expr, 2, targets, repls);
    CHECK(r == ixs_int(ctx, 15));
  }

  /* Three targets: {x->1, y->2, z->3} in x+y+z -> 6. */
  {
    ixs_node *targets[] = {x, y, z};
    ixs_node *repls[] = {ixs_int(ctx, 1), ixs_int(ctx, 2), ixs_int(ctx, 3)};
    ixs_node *expr = ixs_add(ctx, x, ixs_add(ctx, y, z));
    ixs_node *r = ixs_subs_multi(ctx, expr, 3, targets, repls);
    CHECK(r == ixs_int(ctx, 6));
  }

  /* nsubs=0 returns expr unchanged. */
  {
    ixs_node *expr = ixs_add(ctx, x, y);
    CHECK(ixs_subs_multi(ctx, expr, 0, NULL, NULL) == expr);
  }

  /* Piecewise: subs into both branches. */
  {
    ixs_node *c = ixs_cmp(ctx, z, IXS_CMP_GT, ixs_int(ctx, 0));
    ixs_node *vals[] = {x, y};
    ixs_node *conds[] = {c, ixs_true(ctx)};
    ixs_node *pw = ixs_pw(ctx, 2, vals, conds);
    ixs_node *targets[] = {x, y};
    ixs_node *repls[] = {ixs_int(ctx, 10), ixs_int(ctx, 10)};
    ixs_node *r = ixs_subs_multi(ctx, pw, 2, targets, repls);
    CHECK(r == ixs_int(ctx, 10));
  }

  /* Negative: sequential would differ from simultaneous.
   * {x->y, y->42} in x should give y, not 42. */
  {
    ixs_node *targets[] = {x, y};
    ixs_node *repls[] = {y, ixs_int(ctx, 42)};
    ixs_node *r = ixs_subs_multi(ctx, x, 2, targets, repls);
    CHECK(r == y);
  }
}

/* Local context: error/sentinel tests push domain errors and clear them,
 * which would pollute the shared context's error list. */
static void test_sentinel_propagation(void) {
  ixs_ctx *ctx = ctx_create_or_die();
  ixs_node *x = ixs_sym(ctx, "x");

  /* NULL propagation */
  CHECK(ixs_add(ctx, NULL, x) == NULL);
  CHECK(ixs_mul(ctx, x, NULL) == NULL);
  CHECK(ixs_neg(ctx, NULL) == NULL);
  CHECK(ixs_floor(ctx, NULL) == NULL);
  CHECK(ixs_ceil(ctx, NULL) == NULL);
  CHECK(ixs_not(ctx, NULL) == NULL);

  {
    ixs_node *values[2] = {ixs_int(ctx, 1), NULL};
    ixs_node *conds[2] = {ixs_true(ctx), ixs_true(ctx)};
    CHECK(ixs_pw(ctx, 1, NULL, conds) == NULL);
    CHECK(ixs_pw(ctx, 1, values, NULL) == NULL);
    CHECK(ixs_pw(ctx, 2, values, conds) == NULL);
  }

  /* Sentinel propagation */
  ixs_node *err = ixs_mod(ctx, x, ixs_int(ctx, 0));
  CHECK(ixs_is_domain_error(err));
  ixs_ctx_clear_errors(ctx);

  ixs_node *r = ixs_add(ctx, err, x);
  CHECK(ixs_is_domain_error(r));

  r = ixs_floor(ctx, err);
  CHECK(ixs_is_domain_error(r));

  {
    ixs_node *parse = ixs_parse(ctx, "?", 1);
    ixs_node *target = ixs_sym(ctx, "sentinel_target");
    ixs_node *targets[2] = {target, err};
    ixs_node *replacements[2] = {err, parse};
    CHECK(ixs_is_parse_error(parse));
    ixs_ctx_clear_errors(ctx);
    CHECK(ixs_subs(ctx, err, NULL, x) == NULL);
    CHECK(ixs_subs(ctx, err, parse, x) == parse);
    CHECK(ixs_subs(ctx, x, target, err) == err);
    CHECK(ixs_subs_multi(ctx, x, 1, NULL, replacements) == NULL);
    CHECK(ixs_subs_multi(ctx, x, 1, targets, NULL) == NULL);
    CHECK(ixs_subs_multi(ctx, x, 2, targets, replacements) == parse);
    targets[1] = NULL;
    CHECK(ixs_subs_multi(ctx, err, 2, targets, replacements) == NULL);
  }

  ixs_ctx_destroy(ctx);
}

static void test_floor_bounds_collapse(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");

  ixs_node *assumptions[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 64)),
  };

  /* floor(x/64) with 0 <= x < 64 -> 0 */
  ixs_node *expr = ixs_floor(ctx, ixs_mul(ctx, x, ixs_rat(ctx, 1, 64)));
  ixs_node *r = ixs_simplify(ctx, expr, assumptions, 2);
  CHECK(r && ixs_node_int_val(r) == 0);

  /* ceiling(x/64) with 0 <= x < 64: ceil(0/64)=0, ceil(63/64)=1 — NOT constant
   */
  expr = ixs_ceil(ctx, ixs_mul(ctx, x, ixs_rat(ctx, 1, 64)));
  r = ixs_simplify(ctx, expr, assumptions, 2);
  CHECK(r && !ixs_is_error(r));
  /* Should NOT fold to a constant (0 != 1). */
  CHECK(ixs_node_tag(r) != IXS_INT);

  /* floor(x/32) with 0 <= x < 32 -> 0 */
  ixs_node *a32[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 32)),
  };
  expr = ixs_floor(ctx, ixs_mul(ctx, x, ixs_rat(ctx, 1, 32)));
  r = ixs_simplify(ctx, expr, a32, 2);
  CHECK(r && ixs_node_int_val(r) == 0);

  /* ceiling(x/32) with 0 <= x < 1 (i.e. x=0 only) -> 0 */
  ixs_node *a01[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 1)),
  };
  expr = ixs_ceil(ctx, ixs_mul(ctx, x, ixs_rat(ctx, 1, 32)));
  r = ixs_simplify(ctx, expr, a01, 2);
  CHECK(r && ixs_node_int_val(r) == 0);

  /* sym > 5/2 with integer sym -> sym >= 3 (floor(5/2) + 1 = 3) */
  ixs_node *agt[] = {
      ixs_cmp(ctx, x, IXS_CMP_GT, ixs_rat(ctx, 5, 2)),
      ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 32)),
  };
  expr = ixs_mod(ctx, x, ixs_int(ctx, 32));
  r = ixs_simplify(ctx, expr, agt, 2);
  CHECK(r == x);

  /* sym < 7/3 with integer sym -> sym <= 1 (ceil(7/3) - 1 = 1) */
  ixs_node *alt[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, x, IXS_CMP_LT, ixs_rat(ctx, 7, 3)),
  };
  expr = ixs_mod(ctx, x, ixs_int(ctx, 16));
  r = ixs_simplify(ctx, expr, alt, 2);
  CHECK(r == x);

  /* 2*x >= 10 -> x >= 5; 2*x < 20 -> x < 10 -> x <= 9.
   * With x in [5, 9], Mod(x, 16) = x. */
  ixs_node *csym[] = {
      ixs_cmp(ctx, ixs_mul(ctx, ixs_int(ctx, 2), x), IXS_CMP_GE,
              ixs_int(ctx, 10)),
      ixs_cmp(ctx, ixs_mul(ctx, ixs_int(ctx, 2), x), IXS_CMP_LT,
              ixs_int(ctx, 20)),
  };
  expr = ixs_mod(ctx, x, ixs_int(ctx, 16));
  r = ixs_simplify(ctx, expr, csym, 2);
  CHECK(r == x);
}

static void test_mod_bounds_tighten(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");

  /* Mod(x, 16) with 0 <= x < 8 -> x (bounds tighter than [0,15]) */
  ixs_node *assumptions[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 8)),
  };
  ixs_node *expr = ixs_mod(ctx, x, ixs_int(ctx, 16));
  ixs_node *r = ixs_simplify(ctx, expr, assumptions, 2);
  CHECK(r == x);

  /* Mod(x, 100) with 0 <= x < 50 -> x */
  ixs_node *a50[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 50)),
  };
  expr = ixs_mod(ctx, x, ixs_int(ctx, 100));
  r = ixs_simplify(ctx, expr, a50, 2);
  CHECK(r == x);

  /* Relational upper bounds work when the positive modulus is symbolic. */
  {
    ixs_node *d = ixs_sym(ctx, "mod_rel_d");
    ixs_node *m = ixs_mul(ctx, ixs_int(ctx, 8), d);
    ixs_node *positive = ixs_cmp(ctx, d, IXS_CMP_GT, ixs_int(ctx, 0));
    ixs_node *lower = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
    ixs_node *upper = ixs_cmp(ctx, x, IXS_CMP_LT, m);
    ixs_node *relational[] = {positive, lower, upper};
    ixs_node *missing_positive[] = {lower, upper};
    ixs_node *missing_lower[] = {positive, upper};
    ixs_node *missing_upper[] = {positive, lower};
    ixs_node *boundary[] = {positive, lower, ixs_cmp(ctx, x, IXS_CMP_LE, m)};
    ixs_node *contradictory[] = {
        positive, ixs_cmp(ctx, d, IXS_CMP_LE, ixs_int(ctx, 0)), lower, upper};
    ixs_node *nonpositive[] = {ixs_cmp(ctx, d, IXS_CMP_LE, ixs_int(ctx, 0)),
                               lower, upper};
    ixs_node *mod_rel = ixs_mod(ctx, x, m);

    CHECK(ixs_simplify(ctx, mod_rel, relational, 3) == x);
    CHECK(ixs_simplify(ctx, mod_rel, missing_positive, 2) != x);
    CHECK(ixs_simplify(ctx, mod_rel, missing_lower, 2) != x);
    CHECK(ixs_simplify(ctx, mod_rel, missing_upper, 2) != x);
    CHECK(ixs_simplify(ctx, mod_rel, boundary, 3) != x);
    CHECK(ixs_simplify(ctx, mod_rel, contradictory, 4) != x);
    CHECK(ixs_simplify(ctx, mod_rel, nonpositive, 3) != x);
  }

  {
    ixs_node *two31 = ixs_int(ctx, INT64_C(2147483648));
    ixs_node *two32 = ixs_int(ctx, INT64_C(4294967296));
    ixs_node *scaled_mod =
        ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, 2), x), two32);
    ixs_node *quotient = ixs_div(ctx, scaled_mod, ixs_int(ctx, 2));
    ixs_node *expected = ixs_mod(ctx, x, two31);
    ixs_node *nonnegative[] = {
        ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
        ixs_cmp(ctx, x, IXS_CMP_LT, two31),
    };
    ixs_node *signed_range[] = {
        ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, INT32_MIN)),
        ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, INT32_MAX)),
    };
    ixs_node *negative = ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, -1));
    ixs_node *nondividing =
        ixs_div(ctx, ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, 3), x), two32),
                ixs_int(ctx, 3));
    ixs_node *nonintegral =
        ixs_div(ctx, ixs_mod(ctx, x, two32), ixs_int(ctx, 2));

    CHECK(ixs_simplify(ctx, quotient, NULL, 0) == expected);
    CHECK(ixs_simplify(ctx, quotient, nonnegative, 2) == x);
    CHECK(ixs_simplify(ctx, quotient, signed_range, 2) == expected);
    CHECK(ixs_simplify(ctx, quotient, &negative, 1) == ixs_int(ctx, INT32_MAX));
    CHECK(ixs_simplify(ctx, nondividing, NULL, 0) == nondividing);
    CHECK(ixs_simplify(ctx, nonintegral, NULL, 0) == nonintegral);
  }

  /* Mod(3/2*x, 1) must NOT get bounds [0,0] — dividend is not integer.
   * ceiling(Mod(3/2*x, 1)) must not collapse to 0. */
  ixs_node *half_x = ixs_div(ctx, x, ixs_int(ctx, 2));
  ixs_node *three_half_x = ixs_add(ctx, half_x, x);
  ixs_node *mod1 = ixs_mod(ctx, three_half_x, ixs_int(ctx, 1));
  ixs_node *ce = ixs_ceil(ctx, mod1);
  r = ixs_simplify(ctx, ce, NULL, 0);
  CHECK(r != ixs_int(ctx, 0));

  /* A symbolic positive modulus has the same remainder bounds as a literal
   * modulus.  Canonicalization commonly turns constants into SSA symbols
   * constrained by equality. */
  {
    ixs_node *m = ixs_sym(ctx, "m");
    ixs_node *mod_x_m = ixs_mod(ctx, x, m);
    ixs_node *bounded_m[] = {
        ixs_cmp(ctx, m, IXS_CMP_GE, ixs_int(ctx, 1)),
        ixs_cmp(ctx, m, IXS_CMP_LE, ixs_int(ctx, 16)),
    };
    ixs_node *nonnegative = ixs_cmp(ctx, mod_x_m, IXS_CMP_GE, ixs_int(ctx, 0));
    ixs_node *below_bound = ixs_cmp(ctx, mod_x_m, IXS_CMP_LT, ixs_int(ctx, 16));
    CHECK(ixs_simplify(ctx, nonnegative, bounded_m, 2) == ixs_true(ctx));
    CHECK(ixs_simplify(ctx, below_bound, bounded_m, 2) == ixs_true(ctx));

    /* Without a proof that the divisor is positive, neither bound applies. */
    CHECK(ixs_simplify(ctx, nonnegative, bounded_m + 1, 1) != ixs_true(ctx));
    CHECK(ixs_simplify(ctx, below_bound, NULL, 0) != ixs_true(ctx));

    /* Equality-constrained symbols preserve exact-modulus tightening. */
    {
      ixs_node *exact_m = ixs_cmp(ctx, m, IXS_CMP_EQ, ixs_int(ctx, 16));
      ixs_node *scaled = ixs_mul(ctx, ixs_int(ctx, 4), x);
      ixs_node *quotient = ixs_floor(
          ctx, ixs_div(ctx, ixs_mod(ctx, scaled, m), ixs_int(ctx, 13)));
      CHECK(ixs_simplify(ctx, quotient, &exact_m, 1) == ixs_int(ctx, 0));
    }
  }
}

static void test_mod_extract_constant(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");

  /* Mod(4*x + 3, 16) -> 3 + Mod(4*x, 16)
   * because |4| divides 16, x is integer-valued, and 3 < gcd(4)=4.
   * (floor(x) -> x since x is integer-valued.) */
  ixs_node *term = ixs_mul(ctx, ixs_int(ctx, 4), x);
  ixs_node *sum = ixs_add(ctx, term, ixs_int(ctx, 3));
  ixs_node *expr = ixs_mod(ctx, sum, ixs_int(ctx, 16));
  ixs_node *r = ixs_simplify(ctx, expr, NULL, 0);
  CHECK(strcmp(pr(r), "3 + Mod(4*x, 16)") == 0);

  /* Mod(8*x + 7, 16) -> 7 + Mod(8*x, 16) */
  term = ixs_mul(ctx, ixs_int(ctx, 8), x);
  sum = ixs_add(ctx, term, ixs_int(ctx, 7));
  expr = ixs_mod(ctx, sum, ixs_int(ctx, 16));
  r = ixs_simplify(ctx, expr, NULL, 0);
  CHECK(strcmp(pr(r), "7 + Mod(8*x, 16)") == 0);

  /* Mod(4*x + 4, 16): c=4 >= gcd(4)=4, extraction must NOT fire. */
  sum = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 4), x), ixs_int(ctx, 4));
  expr = ixs_mod(ctx, sum, ixs_int(ctx, 16));
  r = ixs_simplify(ctx, expr, NULL, 0);
  CHECK(r && !ixs_is_error(r));
  CHECK(strstr(pr(r), "4 + Mod(") == NULL);

  /* Mod(4*(x/2) + 3, 16) -> Mod(2*x + 3, 16).
   * 4*(1/2) collapses to 2, so gcd(2)=2, and 3 >= 2: no extraction. */
  ixs_node *xhalf = ixs_mul(ctx, x, ixs_rat(ctx, 1, 2));
  term = ixs_mul(ctx, ixs_int(ctx, 4), xhalf);
  sum = ixs_add(ctx, term, ixs_int(ctx, 3));
  expr = ixs_mod(ctx, sum, ixs_int(ctx, 16));
  r = ixs_simplify(ctx, expr, NULL, 0);
  CHECK(r && !ixs_is_error(r));
  CHECK(strstr(pr(r), "3 + Mod(") == NULL);

  /* Multi-term: Mod(4*x + 6*y + 3, 12).
   * gcd(4, 6) = 2, and 3 >= 2: extraction must NOT fire.
   * (Wave's original min(4,6)=4 would wrongly allow 3 < 4.) */
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *t1 = ixs_mul(ctx, ixs_int(ctx, 4), x);
  ixs_node *t2 = ixs_mul(ctx, ixs_int(ctx, 6), y);
  sum = ixs_add(ctx, ixs_add(ctx, t1, t2), ixs_int(ctx, 3));
  expr = ixs_mod(ctx, sum, ixs_int(ctx, 12));
  r = ixs_simplify(ctx, expr, NULL, 0);
  CHECK(r && !ixs_is_error(r));
  CHECK(strstr(pr(r), "3 + Mod(") == NULL);

  /* Multi-term positive: Mod(4*x + 6*y + 1, 12).
   * gcd(4, 6) = 2, and 1 < 2: extraction fires. */
  sum = ixs_add(ctx, ixs_add(ctx, t1, t2), ixs_int(ctx, 1));
  expr = ixs_mod(ctx, sum, ixs_int(ctx, 12));
  r = ixs_simplify(ctx, expr, NULL, 0);
  CHECK(strstr(pr(r), "1 + Mod(") != NULL);
}

static void test_floor_drop_small_rational(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");

  /* floor(floor(x)/3 + 1/6) with floor(x) >= 0 -> floor(floor(x)/3)
   * because floor(x) is non-neg integer, denom=3, r=1/6, 1/6 < 1/3. */
  ixs_node *assumptions[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
  };
  ixs_node *fx = ixs_floor(ctx, x);
  ixs_node *inner =
      ixs_add(ctx, ixs_mul(ctx, fx, ixs_rat(ctx, 1, 3)), ixs_rat(ctx, 1, 6));
  ixs_node *expr = ixs_floor(ctx, inner);
  ixs_node *r = ixs_simplify(ctx, expr, assumptions, 1);
  ixs_node *expected =
      ixs_simplify(ctx, ixs_floor(ctx, ixs_mul(ctx, fx, ixs_rat(ctx, 1, 3))),
                   assumptions, 1);
  CHECK(r == expected);

  /* floor(Mod(x, 8)/4 + 1/8) with 0 <= x -> floor(Mod(x,8)/4)
   * Mod(x, 8) ∈ [0,7] (non-negative integer), denom=4, r=1/8, 1/8 < 1/4. */
  ixs_node *mx8 = ixs_mod(ctx, x, ixs_int(ctx, 8));
  inner =
      ixs_add(ctx, ixs_mul(ctx, mx8, ixs_rat(ctx, 1, 4)), ixs_rat(ctx, 1, 8));
  expr = ixs_floor(ctx, inner);
  r = ixs_simplify(ctx, expr, assumptions, 1);
  expected =
      ixs_simplify(ctx, ixs_floor(ctx, ixs_mul(ctx, mx8, ixs_rat(ctx, 1, 4))),
                   assumptions, 1);
  CHECK(r == expected);

  /* Multi-term: floor(floor(x)/3 + Mod(x,8)/4 + 1/13) with x >= 0.
   * L = lcm(3, 4) = 12, r = 1/13, 1/13 < 1/12: rational is dropped. */
  ixs_node *assumptions2[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
  };
  inner = ixs_add(ctx,
                  ixs_add(ctx, ixs_mul(ctx, fx, ixs_rat(ctx, 1, 3)),
                          ixs_mul(ctx, mx8, ixs_rat(ctx, 1, 4))),
                  ixs_rat(ctx, 1, 13));
  expr = ixs_floor(ctx, inner);
  r = ixs_simplify(ctx, expr, assumptions2, 1);
  expected = ixs_simplify(
      ctx,
      ixs_floor(ctx, ixs_add(ctx, ixs_mul(ctx, fx, ixs_rat(ctx, 1, 3)),
                             ixs_mul(ctx, mx8, ixs_rat(ctx, 1, 4)))),
      assumptions2, 1);
  CHECK(r == expected);

  /* floor(floor(x)/3 + 1/3) should NOT drop: 1/3 is not < 1/3. */
  inner =
      ixs_add(ctx, ixs_mul(ctx, fx, ixs_rat(ctx, 1, 3)), ixs_rat(ctx, 1, 3));
  expr = ixs_floor(ctx, inner);
  r = ixs_simplify(ctx, expr, assumptions, 1);
  CHECK(r && !ixs_is_error(r));
  ixs_node *without_r =
      ixs_simplify(ctx, ixs_floor(ctx, ixs_mul(ctx, fx, ixs_rat(ctx, 1, 3))),
                   assumptions, 1);
  CHECK(!ixs_same_node(r, without_r));
}

static void test_floor_drop_small_bounded_term(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *assumptions[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 4)),
      ixs_cmp(ctx, y, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, y, IXS_CMP_LT, ixs_int(ctx, 4)),
  };

  ixs_node *base = ixs_div(ctx, x, ixs_int(ctx, 2));
  ixs_node *expr =
      ixs_floor(ctx, ixs_add(ctx, base, ixs_div(ctx, y, ixs_int(ctx, 16))));
  ixs_node *expected = ixs_simplify(ctx, ixs_floor(ctx, base), assumptions, 4);
  ixs_node *r = ixs_simplify(ctx, expr, assumptions, 4);
  CHECK(r == expected);

  expr = ixs_floor(ctx, ixs_add(ctx, base, ixs_div(ctx, y, ixs_int(ctx, 2))));
  r = ixs_simplify(ctx, expr, assumptions, 4);
  CHECK(r != expected);

  {
    ixs_node *wi = ixs_sym(ctx, "wi");
    ixs_node *wi_assumptions[] = {
        ixs_cmp(ctx, wi, IXS_CMP_GE, ixs_int(ctx, 0)),
        ixs_cmp(ctx, wi, IXS_CMP_LE, ixs_int(ctx, 511)),
    };
    ixs_node *q =
        ixs_mod(ctx, ixs_floor(ctx, ixs_div(ctx, wi, ixs_int(ctx, 64))),
                ixs_int(ctx, 4));
    ixs_node *low = ixs_mod(
        ctx, ixs_mod(ctx, ixs_mod(ctx, wi, ixs_int(ctx, 64)), ixs_int(ctx, 16)),
        ixs_int(ctx, 4));
    expr = ixs_floor(ctx, ixs_add(ctx, ixs_div(ctx, q, ixs_int(ctx, 2)),
                                  ixs_div(ctx, low, ixs_int(ctx, 8))));
    expected =
        ixs_simplify(ctx, ixs_floor(ctx, ixs_div(ctx, q, ixs_int(ctx, 2))),
                     wi_assumptions, 2);
    r = ixs_simplify(ctx, expr, wi_assumptions, 2);
    CHECK(r == expected);
  }
}

static void test_nested_floor_ceil(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");

  /* floor(floor(x/3) / 5) -> floor(x/15) */
  ixs_node *inner = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)));
  ixs_node *e = ixs_floor(ctx, ixs_div(ctx, inner, ixs_int(ctx, 5)));
  CHECK(e && strcmp(pr(e), "floor(1/15*x)") == 0);

  /* ceiling(ceiling(x/4) / 3) -> ceiling(x/12) */
  inner = ixs_ceil(ctx, ixs_div(ctx, x, ixs_int(ctx, 4)));
  e = ixs_ceil(ctx, ixs_div(ctx, inner, ixs_int(ctx, 3)));
  CHECK(e && strcmp(pr(e), "ceiling(1/12*x)") == 0);

  /* floor(floor(x/2) / 2) -> floor(x/4) */
  inner = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 2)));
  e = ixs_floor(ctx, ixs_div(ctx, inner, ixs_int(ctx, 2)));
  CHECK(e && strcmp(pr(e), "floor(1/4*x)") == 0);

  /* Negative: floor(2*floor(x/3) / 5) should NOT collapse */
  inner = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)));
  e = ixs_floor(ctx, ixs_mul(ctx, ixs_rat(ctx, 2, 5), inner));
  CHECK(e && strstr(pr(e), "floor") != NULL);

  /* Mod(a*floor(x/a), a) -> 0 */
  inner = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 4)));
  e = ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, 4), inner), ixs_int(ctx, 4));
  CHECK(e == ixs_int(ctx, 0));

  /* Mod(6*floor(x/3), 3) -> 0 (6 is multiple of 3) */
  inner = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)));
  e = ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, 6), inner), ixs_int(ctx, 3));
  CHECK(e == ixs_int(ctx, 0));

  /* Negative: Mod(3*floor(x/4), 4) should NOT simplify to 0 */
  inner = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 4)));
  e = ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, 3), inner), ixs_int(ctx, 4));
  CHECK(e != ixs_int(ctx, 0));

  /* Negative: ceiling(2*ceiling(x/4) / 3) should NOT collapse */
  inner = ixs_ceil(ctx, ixs_div(ctx, x, ixs_int(ctx, 4)));
  e = ixs_ceil(ctx, ixs_mul(ctx, ixs_rat(ctx, 2, 3), inner));
  CHECK(e && strstr(pr(e), "ceiling") != NULL);

  /* Negative: floor(floor(x/3) * 2) -> 2*floor(x/3) (integer, no nesting) */
  inner = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)));
  e = ixs_floor(ctx, ixs_mul(ctx, ixs_int(ctx, 2), inner));
  CHECK(e && strcmp(pr(e), "2*floor(1/3*x)") == 0);
}

static void test_same_node(void) {
  ixs_ctx *ctx = get_ctx();
  CHECK(ixs_same_node(NULL, NULL));
  CHECK(!ixs_same_node(ixs_int(ctx, 1), NULL));
  CHECK(ixs_same_node(ixs_int(ctx, 42), ixs_int(ctx, 42)));
}

static void test_print_roundtrip(void) {
  ixs_ctx *ctx = get_ctx();

  const char *exprs[] = {
      "x + y",     "3*x + 2",   "floor(x/2)", "ceiling(x + 1)",
      "Mod(x, 5)", "Max(x, y)", "Min(x, y)",  "xor(x, y)",
  };
  size_t i;
  for (i = 0; i < sizeof(exprs) / sizeof(exprs[0]); i++) {
    ixs_node *n = ixs_parse(ctx, exprs[i], strlen(exprs[i]));
    CHECK(n && !ixs_is_error(n));

    char out[1024];
    ixs_print(n, out, sizeof(out));

    /* Re-parse the printed output. */
    ixs_node *n2 = ixs_parse(ctx, out, strlen(out));
    CHECK(n2 && !ixs_is_error(n2));
    CHECK(ixs_same_node(n, n2));
  }
}

static void test_divisibility_assumptions(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *K = ixs_sym(ctx, "K");
  ixs_node *N = ixs_sym(ctx, "N");
  ixs_node *M = ixs_sym(ctx, "M");
  ixs_node *r;

  /* Assumption: Mod(K, 32) == 0  (K is divisible by 32) */
  ixs_node *div_K_32[] = {
      ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 32)), IXS_CMP_EQ,
              ixs_int(ctx, 0)),
  };

  /* floor(K/32) -> K/32 when 32 | K */
  ixs_node *e1 = ixs_floor(ctx, ixs_div(ctx, K, ixs_int(ctx, 32)));
  r = ixs_simplify(ctx, e1, div_K_32, 1);
  CHECK(strcmp(pr(r), "1/32*K") == 0);

  /* Mod(K, 32) -> 0 when 32 | K */
  ixs_node *e2 = ixs_mod(ctx, K, ixs_int(ctx, 32));
  r = ixs_simplify(ctx, e2, div_K_32, 1);
  CHECK(r == ixs_int(ctx, 0));

  /* floor(K/16) -> K/16 since 32 | K implies 16 | K */
  ixs_node *e3 = ixs_floor(ctx, ixs_div(ctx, K, ixs_int(ctx, 16)));
  r = ixs_simplify(ctx, e3, div_K_32, 1);
  CHECK(strcmp(pr(r), "1/16*K") == 0);

  /* Mod(K, 64) should NOT simplify to 0 (32 | K does not imply 64 | K) */
  ixs_node *e4 = ixs_mod(ctx, K, ixs_int(ctx, 64));
  r = ixs_simplify(ctx, e4, div_K_32, 1);
  CHECK(r != ixs_int(ctx, 0));

  /* Mod(3*K, 32) -> 0 when 32 | K */
  ixs_node *e5 =
      ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, 3), K), ixs_int(ctx, 32));
  r = ixs_simplify(ctx, e5, div_K_32, 1);
  CHECK(r == ixs_int(ctx, 0));

  /* Multiple assumptions: Mod(K, 32)==0 and Mod(N, 16)==0 */
  ixs_node *multi_div[] = {
      ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 32)), IXS_CMP_EQ,
              ixs_int(ctx, 0)),
      ixs_cmp(ctx, ixs_mod(ctx, N, ixs_int(ctx, 16)), IXS_CMP_EQ,
              ixs_int(ctx, 0)),
  };
  r = ixs_simplify(ctx, ixs_mod(ctx, K, ixs_int(ctx, 32)), multi_div, 2);
  CHECK(r == ixs_int(ctx, 0));
  r = ixs_simplify(ctx, ixs_mod(ctx, N, ixs_int(ctx, 16)), multi_div, 2);
  CHECK(r == ixs_int(ctx, 0));
  r = ixs_simplify(ctx, ixs_floor(ctx, ixs_div(ctx, N, ixs_int(ctx, 16))),
                   multi_div, 2);
  CHECK(strcmp(pr(r), "1/16*N") == 0);

  /* Mixed: floor(K/32) + Mod(K, 32) -> K/32 when 32 | K */
  ixs_node *e6 = ixs_add(ctx, ixs_floor(ctx, ixs_div(ctx, K, ixs_int(ctx, 32))),
                         ixs_mod(ctx, K, ixs_int(ctx, 32)));
  r = ixs_simplify(ctx, e6, div_K_32, 1);
  CHECK(strcmp(pr(r), "1/32*K") == 0);

  /* Stronger assumption implies weaker: Mod(M, 256)==0 with tile=128 */
  ixs_node *div_M_256[] = {
      ixs_cmp(ctx, ixs_mod(ctx, M, ixs_int(ctx, 256)), IXS_CMP_EQ,
              ixs_int(ctx, 0)),
  };
  r = ixs_simplify(ctx, ixs_mod(ctx, M, ixs_int(ctx, 128)), div_M_256, 1);
  CHECK(r == ixs_int(ctx, 0));
  r = ixs_simplify(ctx, ixs_floor(ctx, ixs_div(ctx, M, ixs_int(ctx, 128))),
                   div_M_256, 1);
  CHECK(strcmp(pr(r), "1/128*M") == 0);

  /* Negative: floor(K/64) with 32|K should NOT drop floor */
  ixs_node *e_neg = ixs_floor(ctx, ixs_div(ctx, K, ixs_int(ctx, 64)));
  r = ixs_simplify(ctx, e_neg, div_K_32, 1);
  CHECK(strstr(pr(r), "floor") != NULL);

  /* No assumptions: expressions pass through unchanged */
  ixs_node *e7 = ixs_floor(ctx, ixs_div(ctx, K, ixs_int(ctx, 32)));
  r = ixs_simplify(ctx, e7, NULL, 0);
  CHECK(strstr(pr(r), "floor") != NULL);

  /* ceiling(K/32) -> K/32 when 32 | K */
  ixs_node *e8 = ixs_ceil(ctx, ixs_div(ctx, K, ixs_int(ctx, 32)));
  r = ixs_simplify(ctx, e8, div_K_32, 1);
  CHECK(strcmp(pr(r), "1/32*K") == 0);

  /* Multi-factor: floor(K/2 * N) -> K/2 * N when 32|K and 16|N.
   * K/2*N = MUL(1/2, [K^1, N^1]); K absorbs the denominator 2. */
  {
    ixs_node *div_K32_N16[] = {
        ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 32)), IXS_CMP_EQ,
                ixs_int(ctx, 0)),
        ixs_cmp(ctx, ixs_mod(ctx, N, ixs_int(ctx, 16)), IXS_CMP_EQ,
                ixs_int(ctx, 0)),
    };
    ixs_node *prod = ixs_mul(ctx, ixs_div(ctx, K, ixs_int(ctx, 2)), N);
    r = ixs_simplify(ctx, ixs_floor(ctx, prod), div_K32_N16, 2);
    CHECK(strstr(pr(r), "floor") == NULL);

    /* Negative: floor(K/64 * N) with 32|K -- K not divisible by 64. */
    ixs_node *prod2 = ixs_mul(ctx, ixs_div(ctx, K, ixs_int(ctx, 64)), N);
    r = ixs_simplify(ctx, ixs_floor(ctx, prod2), div_K32_N16, 2);
    CHECK(strstr(pr(r), "floor") != NULL);
  }
}

static void test_large_expressions(void) {
  ixs_ctx *ctx = get_ctx();
  int i;

  /* ADD with >256 distinct terms. */
  {
    ixs_node *sum = ixs_int(ctx, 0);
    char name[16];
    for (i = 0; i < 300; i++) {
      snprintf(name, sizeof(name), "s%d", i);
      sum = ixs_add(ctx, sum, ixs_sym(ctx, name));
      CHECK(sum != NULL && !ixs_is_error(sum));
    }
    CHECK(ixs_node_tag(sum) == IXS_ADD);
  }

  /* MUL with >256 distinct factors. */
  {
    ixs_node *prod = ixs_int(ctx, 1);
    char name[16];
    for (i = 0; i < 300; i++) {
      snprintf(name, sizeof(name), "m%d", i);
      prod = ixs_mul(ctx, prod, ixs_sym(ctx, name));
      CHECK(prod != NULL && !ixs_is_error(prod));
    }
    CHECK(ixs_node_tag(prod) == IXS_MUL);
  }

  /* AND with >256 distinct args. */
  {
    ixs_node *conj = ixs_true(ctx);
    char name[16];
    for (i = 0; i < 300; i++) {
      snprintf(name, sizeof(name), "a%d", i);
      ixs_node *cmp =
          ixs_cmp(ctx, ixs_sym(ctx, name), IXS_CMP_GT, ixs_int(ctx, 0));
      conj = ixs_and(ctx, conj, cmp);
      CHECK(conj != NULL && !ixs_is_error(conj));
    }
    CHECK(ixs_node_tag(conj) == IXS_AND);
  }

  /* Deep binary predicate chain: is_pred must not recurse through it. */
  {
    ixs_node *conj = ixs_true(ctx);
    char name[16];
    for (i = 0; i < 5000; i++) {
      snprintf(name, sizeof(name), "bp%d", i);
      ixs_node *cmp =
          ixs_cmp(ctx, ixs_sym(ctx, name), IXS_CMP_GT, ixs_int(ctx, 0));
      conj = ixs_and(ctx, conj, cmp);
      CHECK(conj != NULL && !ixs_is_error(conj));
    }
    CHECK(ixs_node_is_pred(conj));
  }

  /* XOR parity across many distinct runs, isolated from shared rule stats. */
  {
    enum { XOR_RUNS = 2048, XOR_ARGS = 2 * XOR_RUNS };
    ixs_ctx *parity_ctx = ctx_create_or_die();
    ixs_node **parity = malloc(XOR_ARGS * sizeof(*parity));
    char name[16];
    CHECK(parity != NULL);
    if (parity) {
      for (i = 0; i < XOR_RUNS; i++) {
        snprintf(name, sizeof(name), "xp%d", i);
        parity[2 * i] = ixs_sym(parity_ctx, name);
        parity[2 * i + 1] = parity[2 * i];
      }
      CHECK(ixs_xor_many(parity_ctx, XOR_ARGS, parity) ==
            ixs_int(parity_ctx, 0));
      free(parity);
    }
    ixs_ctx_destroy(parity_ctx);
  }

  /* Piecewise with >256 cases. */
  {
    ixs_node **vals = malloc(300 * sizeof(*vals));
    ixs_node **conds = malloc(300 * sizeof(*conds));
    CHECK(vals != NULL && conds != NULL);
    char name[16];
    for (i = 0; i < 299; i++) {
      snprintf(name, sizeof(name), "p%d", i);
      vals[i] = ixs_sym(ctx, name);
      conds[i] = ixs_cmp(ctx, ixs_sym(ctx, name), IXS_CMP_GT, ixs_int(ctx, 0));
    }
    vals[299] = ixs_int(ctx, 0);
    conds[299] = ixs_true(ctx);
    ixs_node *pw = ixs_pw(ctx, 300, vals, conds);
    CHECK(pw != NULL && !ixs_is_error(pw));
    free(vals);
    free(conds);
  }
}

static void test_bounds_many_vars(void) {
  ixs_ctx *ctx = get_ctx();
  int i;

  /* Build 100 symbols each with bounds: 0 <= v_i < 256.
   * Then Mod(v_i, 256) should simplify to v_i for all of them. */
  ixs_node *assumptions[200];
  ixs_node *syms[100];
  char name[16];
  for (i = 0; i < 100; i++) {
    snprintf(name, sizeof(name), "v%d", i);
    syms[i] = ixs_sym(ctx, name);
    assumptions[2 * i] = ixs_cmp(ctx, syms[i], IXS_CMP_GE, ixs_int(ctx, 0));
    assumptions[2 * i + 1] =
        ixs_cmp(ctx, syms[i], IXS_CMP_LT, ixs_int(ctx, 256));
  }

  /* Simplify Mod(v_99, 256) — the 100th variable — to v_99. */
  ixs_node *expr = ixs_mod(ctx, syms[99], ixs_int(ctx, 256));
  ixs_node *r = ixs_simplify(ctx, expr, assumptions, 200);
  CHECK(r == syms[99]);

  /* Also check an early one. */
  expr = ixs_mod(ctx, syms[0], ixs_int(ctx, 256));
  r = ixs_simplify(ctx, expr, assumptions, 200);
  CHECK(r == syms[0]);
}

static void test_mod_floor_regression(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *K = ixs_sym(ctx, "K");

  /* Mod(x + k*d, d) -> Mod(x, d): constant multiple of modulus absorbed */
  CHECK(ixs_mod(ctx, ixs_add(ctx, x, ixs_int(ctx, 32)), ixs_int(ctx, 16)) ==
        ixs_mod(ctx, x, ixs_int(ctx, 16)));
  CHECK(ixs_mod(ctx, ixs_add(ctx, x, ixs_int(ctx, 48)), ixs_int(ctx, 16)) ==
        ixs_mod(ctx, x, ixs_int(ctx, 16)));

  /* Mod(n*x, n) -> 0 for integer-valued x */
  CHECK(ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, 16), x), ixs_int(ctx, 16)) ==
        ixs_int(ctx, 0));
  CHECK(ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, 32), x), ixs_int(ctx, 16)) ==
        ixs_int(ctx, 0));

  /* floor(Mod(x, n)) -> Mod(x, n): Mod of integers is integer-valued */
  ixs_node *mx16 = ixs_mod(ctx, x, ixs_int(ctx, 16));
  CHECK(ixs_floor(ctx, mx16) == mx16);

  /* ceiling(Mod(x, n)) -> Mod(x, n) */
  CHECK(ixs_ceil(ctx, mx16) == mx16);

  /* floor(Mod(x, 64)/16) stays as-is (mod-then-divide is the preferred form).
   */
  ixs_node *subfield = ixs_floor(
      ctx, ixs_div(ctx, ixs_mod(ctx, x, ixs_int(ctx, 64)), ixs_int(ctx, 16)));
  CHECK(ixs_node_tag(subfield) == IXS_FLOOR);

  /* floor(x + 1/2) -> x for integer-valued x (fractional part drops) */
  ixs_node *fhalf = ixs_floor(ctx, ixs_add(ctx, x, ixs_rat(ctx, 1, 2)));
  CHECK(fhalf == x);

  /* ceil(x + 1/2) -> x + 1 for integer-valued x */
  ixs_node *chalf = ixs_ceil(ctx, ixs_add(ctx, x, ixs_rat(ctx, 1, 2)));
  CHECK(chalf == ixs_add(ctx, x, ixs_int(ctx, 1)));

  /* floor((4*floor(x/3) + y) / 2) -> 2*floor(x/3) + floor(y/2)
   * MUL-over-ADD extraction with integer-valued product. */
  ixs_node *fx3 = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)));
  ixs_node *e = ixs_floor(
      ctx, ixs_div(ctx, ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 4), fx3), y),
                   ixs_int(ctx, 2)));
  ixs_node *expected =
      ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), fx3),
              ixs_floor(ctx, ixs_div(ctx, y, ixs_int(ctx, 2))));
  CHECK(e == expected);

  /* floor((6*K*floor(x/3) + y) / (2*K)) -> 3*floor(x/3) + floor(y/(2*K))
   * Symbolic denominator cancellation. */
  ixs_node *outer_num =
      ixs_add(ctx, ixs_mul(ctx, ixs_mul(ctx, ixs_int(ctx, 6), K), fx3), y);
  ixs_node *outer_den = ixs_mul(ctx, ixs_int(ctx, 2), K);
  e = ixs_floor(ctx, ixs_div(ctx, outer_num, outer_den));
  CHECK(strcmp(pr(e), "3*floor(1/3*x) + floor(1/2*1/K*y)") == 0);

  /* Mod(8*floor(x/4), 4) -> 0: coefficient is multiple of modulus */
  ixs_node *fx4 = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 4)));
  CHECK(ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, 8), fx4), ixs_int(ctx, 4)) ==
        ixs_int(ctx, 0));

  /* Mod(Mod(x, 32), 16): nested Mod where inner > outer.
   * Currently not collapsed; verify it doesn't crash or produce garbage. */
  ixs_node *nested =
      ixs_mod(ctx, ixs_mod(ctx, x, ixs_int(ctx, 32)), ixs_int(ctx, 16));
  CHECK(nested != NULL && !ixs_is_error(nested));
}

static void test_mod_recognition(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *cx = ixs_ceil(ctx, ixs_div(ctx, x, ixs_int(ctx, 8)));

  /* x - 32*floor(x/32) -> Mod(x, 32) */
  ixs_node *e =
      ixs_add(ctx, x,
              ixs_mul(ctx, ixs_int(ctx, -32),
                      ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 32)))));
  CHECK(e == ixs_mod(ctx, x, ixs_int(ctx, 32)));

  /* ceiling(x/8) - 32*floor(ceiling(x/8)/32) -> Mod(ceiling(x/8), 32) */
  e = ixs_add(ctx, cx,
              ixs_mul(ctx, ixs_int(ctx, -32),
                      ixs_floor(ctx, ixs_div(ctx, cx, ixs_int(ctx, 32)))));
  CHECK(e == ixs_mod(ctx, cx, ixs_int(ctx, 32)));

  /* With a scalar: 3*x - 96*floor(x/32) -> 3*Mod(x, 32)  (96 = 3*32) */
  e = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 3), x),
              ixs_mul(ctx, ixs_int(ctx, -96),
                      ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 32)))));
  CHECK(e == ixs_mul(ctx, ixs_int(ctx, 3), ixs_mod(ctx, x, ixs_int(ctx, 32))));

  /* Extra terms preserved: y + x - 32*floor(x/32) -> y + Mod(x, 32) */
  e = ixs_add(ctx, ixs_add(ctx, y, x),
              ixs_mul(ctx, ixs_int(ctx, -32),
                      ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 32)))));
  CHECK(e == ixs_add(ctx, y, ixs_mod(ctx, x, ixs_int(ctx, 32))));

  /* Constant offset preserved: 5 + x - 32*floor(x/32) -> 5 + Mod(x, 32) */
  e = ixs_add(ctx, ixs_add(ctx, ixs_int(ctx, 5), x),
              ixs_mul(ctx, ixs_int(ctx, -32),
                      ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 32)))));
  CHECK(e == ixs_add(ctx, ixs_int(ctx, 5), ixs_mod(ctx, x, ixs_int(ctx, 32))));

  /* No false match: 5*x - 32*floor(x/32) stays as is (5 != 1, 5*32 != 32) */
  e = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 5), x),
              ixs_mul(ctx, ixs_int(ctx, -32),
                      ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 32)))));
  CHECK(ixs_node_tag(e) == IXS_ADD);

  /* Ceiling padding: N*ceil(x/N) - x -> Mod(-x, N) */
  e = ixs_add(ctx,
              ixs_mul(ctx, ixs_int(ctx, 32),
                      ixs_ceil(ctx, ixs_div(ctx, x, ixs_int(ctx, 32)))),
              ixs_mul(ctx, ixs_int(ctx, -1), x));
  CHECK(e == ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, -1), x), ixs_int(ctx, 32)));

  /* Scaled ceiling: 3*32*ceil(x/32) - 3*x -> 3*Mod(-x, 32) */
  e = ixs_add(ctx,
              ixs_mul(ctx, ixs_int(ctx, 96),
                      ixs_ceil(ctx, ixs_div(ctx, x, ixs_int(ctx, 32)))),
              ixs_mul(ctx, ixs_int(ctx, -3), x));
  CHECK(e == ixs_mul(ctx, ixs_int(ctx, 3),
                     ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, -1), x),
                             ixs_int(ctx, 32))));

  /* Extra terms with ceiling: y + 4*ceil(x/4) - x -> y + Mod(-x, 4) */
  e = ixs_add(ctx,
              ixs_add(ctx, y,
                      ixs_mul(ctx, ixs_int(ctx, 4),
                              ixs_ceil(ctx, ixs_div(ctx, x, ixs_int(ctx, 4))))),
              ixs_mul(ctx, ixs_int(ctx, -1), x));
  CHECK(e == ixs_add(ctx, y,
                     ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, -1), x),
                             ixs_int(ctx, 4))));

  /* No false match: 32*ceil(x/32) - 5*x stays as is (5 != 1, 5*32 != 32) */
  e = ixs_add(ctx,
              ixs_mul(ctx, ixs_int(ctx, 32),
                      ixs_ceil(ctx, ixs_div(ctx, x, ixs_int(ctx, 32)))),
              ixs_mul(ctx, ixs_int(ctx, -5), x));
  CHECK(ixs_node_tag(e) == IXS_ADD);

  /* Symbolic divisor: E - G*floor(E/G) -> Mod(E, G) */
  {
    ixs_node *G = ixs_sym(ctx, "G");
    ixs_node *E = ixs_ceil(ctx, ixs_div(ctx, x, ixs_int(ctx, 192)));
    e = ixs_add(ctx, E,
                ixs_mul(ctx, ixs_int(ctx, -1),
                        ixs_mul(ctx, G, ixs_floor(ctx, ixs_div(ctx, E, G)))));
    CHECK(e == ixs_mod(ctx, E, G));
  }

  /* Scaled symbolic: 3*E - 3*G*floor(E/G) -> 3*Mod(E, G) */
  {
    ixs_node *G = ixs_sym(ctx, "G");
    ixs_node *E = ixs_ceil(ctx, ixs_div(ctx, x, ixs_int(ctx, 192)));
    e = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 3), E),
                ixs_mul(ctx, ixs_int(ctx, -3),
                        ixs_mul(ctx, G, ixs_floor(ctx, ixs_div(ctx, E, G)))));
    CHECK(e == ixs_mul(ctx, ixs_int(ctx, 3), ixs_mod(ctx, E, G)));
  }

  /* Symbolic ceil: G*ceil(x/G) - x -> Mod(-x, G) */
  {
    ixs_node *G = ixs_sym(ctx, "G");
    e = ixs_add(ctx, ixs_mul(ctx, G, ixs_ceil(ctx, ixs_div(ctx, x, G))),
                ixs_mul(ctx, ixs_int(ctx, -1), x));
    CHECK(e == ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, -1), x), G));
  }

  /* Negative: E - G*floor(x/G) stays (dividend mismatch) */
  {
    ixs_node *G = ixs_sym(ctx, "G");
    ixs_node *E = ixs_ceil(ctx, ixs_div(ctx, x, ixs_int(ctx, 192)));
    e = ixs_add(ctx, E,
                ixs_mul(ctx, ixs_int(ctx, -1),
                        ixs_mul(ctx, G, ixs_floor(ctx, ixs_div(ctx, x, G)))));
    CHECK(ixs_node_tag(e) == IXS_ADD);
  }
}

static void test_floor_mod_divisor(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");

  /* floor(Mod(x, 64) / 16) stays: the "mod-then-divide" form is the natural
   * hardware idiom for GPU thread index decomposition and maps directly to
   * two affine ops.  Rewriting to Mod(floor(x/16), 4) is complexity-neutral
   * and obscures the hardware mapping. */
  ixs_node *e = ixs_floor(
      ctx, ixs_div(ctx, ixs_mod(ctx, x, ixs_int(ctx, 64)), ixs_int(ctx, 16)));
  CHECK(ixs_node_tag(e) == IXS_FLOOR);

  /* floor(Mod(x, 32) / 32) -> 0 (range of Mod is [0, 31], divided by 32 < 1,
   * floor rounds to 0). */
  e = ixs_floor(
      ctx, ixs_div(ctx, ixs_mod(ctx, x, ixs_int(ctx, 32)), ixs_int(ctx, 32)));
  CHECK(e == ixs_int(ctx, 0));
}

/* A - PW((A+B, c), (A+C, ~c)) + PW((B, c), (C, ~c)) should fold to 0. */
static void test_pw_fold_in_add(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *c = ixs_cmp(ctx, x, IXS_CMP_GT, ixs_int(ctx, 0));
  ixs_node *A = ixs_mul(ctx, ixs_int(ctx, 128), y);
  ixs_node *B = ixs_mod(ctx, x, ixs_int(ctx, 16));
  ixs_node *C =
      ixs_mul(ctx, ixs_int(ctx, 4),
              ixs_floor(ctx, ixs_div(ctx, ixs_mod(ctx, x, ixs_int(ctx, 64)),
                                     ixs_int(ctx, 16))));

  ixs_node *v1[] = {ixs_add(ctx, A, B), ixs_add(ctx, A, C)};
  ixs_node *c1[] = {c, ixs_true(ctx)};
  ixs_node *pw1 = ixs_pw(ctx, 2, v1, c1);

  ixs_node *v2[] = {B, C};
  ixs_node *c2[] = {c, ixs_true(ctx)};
  ixs_node *pw2 = ixs_pw(ctx, 2, v2, c2);

  /* Verify conditions are pointer-equal (hash-consed). */
  CHECK(ixs_node_pw_cond(pw1, 0) == ixs_node_pw_cond(pw2, 0));
  CHECK(ixs_node_pw_cond(pw1, 1) == ixs_node_pw_cond(pw2, 1));

  /* A - pw1 + pw2 = 0 */
  ixs_node *expr = ixs_add(ctx, ixs_sub(ctx, A, pw1), pw2);
  CHECK(expr == ixs_int(ctx, 0));
  ixs_node *r = ixs_simplify(ctx, expr, NULL, 0);
  CHECK(r == ixs_int(ctx, 0));

  /* Also test via from_sympy-like path: sequential add */
  ixs_node *neg_pw1 = ixs_mul(ctx, ixs_int(ctx, -1), pw1);
  ixs_node *s1 = ixs_add(ctx, A, neg_pw1);
  ixs_node *s2 = ixs_add(ctx, s1, pw2);
  CHECK(s2 == ixs_int(ctx, 0));

  /* Negative: different conditions must NOT fold. */
  ixs_node *d = ixs_cmp(ctx, y, IXS_CMP_GT, ixs_int(ctx, 0));
  ixs_node *v3[] = {B, C};
  ixs_node *c3[] = {d, ixs_true(ctx)};
  ixs_node *pw3 = ixs_pw(ctx, 2, v3, c3);
  ixs_node *no_fold = ixs_add(ctx, ixs_sub(ctx, A, pw1), pw3);
  CHECK(no_fold != ixs_int(ctx, 0));

  /* Adjacent equal values merge conditions as truthiness predicates, not
   * bitwise OR.  The catch-all branch makes the whole Piecewise constant. */
  {
    ixs_node *five = ixs_int(ctx, 5);
    ixs_node *vals[] = {five, five, ixs_int(ctx, 0)};
    ixs_node *conds[] = {x, ixs_true(ctx), ixs_true(ctx)};
    CHECK(ixs_pw(ctx, 3, vals, conds) == five);
  }

  /* Same bug shape with a truthy rational condition: must not build a
   * bitwise-rational condition such as x | 1/2. */
  {
    ixs_node *five = ixs_int(ctx, 5);
    ixs_node *vals[] = {five, five, ixs_int(ctx, 0)};
    ixs_node *conds[] = {x, ixs_rat(ctx, 1, 2), ixs_true(ctx)};
    CHECK(ixs_pw(ctx, 3, vals, conds) == five);
  }
}

static void test_piecewise_branch_bounds(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *modx = ixs_mod(ctx, x, ixs_int(ctx, 32));

  /* Piecewise((Max(1, Mod(x,32)), Mod(x,32) > 0), (1, True))
   * With x >= 0 assumption, the first branch should collapse Max -> Mod. */
  ixs_node *cond = ixs_cmp(ctx, modx, IXS_CMP_GT, ixs_int(ctx, 0));
  ixs_node *v1 = ixs_max(ctx, ixs_int(ctx, 1), modx);
  ixs_node *v2 = ixs_int(ctx, 1);
  ixs_node *vals[] = {v1, v2};
  ixs_node *cds[] = {cond, ixs_true(ctx)};
  ixs_node *pw = ixs_pw(ctx, 2, vals, cds);

  ixs_node *assume = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *result = ixs_simplify(ctx, pw, &assume, 1);
  CHECK(result != NULL);

  /* Verify Max(1, ...) no longer appears in the result. */
  {
    char buf[512];
    ixs_print(result, buf, sizeof(buf));
    CHECK(strstr(buf, "Max(") == NULL);
  }

  {
    char buf[512];
    ixs_node *n = ixs_sym(ctx, "n");
    ixs_node *y = ixs_sym(ctx, "y");
    ixs_node *hidden_bounds =
        ixs_and(ctx, ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
                ixs_cmp(ctx, x, IXS_CMP_LE, n));
    ixs_node *nested_cond = ixs_and(
        ctx, hidden_bounds, ixs_cmp(ctx, y, IXS_CMP_GT, ixs_int(ctx, 0)));
    ixs_node *nested_vals[] = {ixs_max(ctx, x, ixs_int(ctx, 0)),
                               ixs_int(ctx, 7)};
    ixs_node *nested_cds[] = {nested_cond, ixs_true(ctx)};
    ixs_node *nested_pw = ixs_pw(ctx, 2, nested_vals, nested_cds);
    ixs_node *outer_assume = ixs_cmp(ctx, n, IXS_CMP_GE, ixs_int(ctx, 0));
    ixs_node *nested_result = ixs_simplify(ctx, nested_pw, &outer_assume, 1);
    CHECK(nested_result != NULL);
    ixs_print(nested_result, buf, sizeof(buf));
    CHECK(strstr(buf, "Max(") == NULL);
  }
}

static void test_product_zero_branch_collapse(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *N = ixs_sym(ctx, "N");
  ixs_node *M = ixs_sym(ctx, "M");
  ixs_node *C = ixs_ceil(ctx, ixs_div(ctx, N, ixs_int(ctx, 192)));
  ixs_node *CM = ixs_ceil(ctx, ixs_div(ctx, M, ixs_int(ctx, 256)));
  ixs_node *fc = ixs_floor(ctx, ixs_div(ctx, C, ixs_int(ctx, 32)));
  ixs_node *mc = ixs_mod(ctx, C, ixs_int(ctx, 32));

  /* Piecewise((floor(-32*floor(C/32)*ceil(M/256)/Mod(C,32)),
   *            Mod(C,32) > 0 & floor(C/32)*ceil(M/256) <= 0),
   *           (0, True))
   * Should collapse to 0: the guard pins floor(C/32) to 0, making
   * the branch value = floor(0) = 0 = default branch. */
  ixs_node *branch = ixs_floor(
      ctx,
      ixs_div(ctx, ixs_mul(ctx, ixs_int(ctx, -32), ixs_mul(ctx, fc, CM)), mc));
  ixs_node *guard =
      ixs_and(ctx, ixs_cmp(ctx, mc, IXS_CMP_GT, ixs_int(ctx, 0)),
              ixs_cmp(ctx, ixs_mul(ctx, fc, CM), IXS_CMP_LE, ixs_int(ctx, 0)));
  ixs_node *vals[] = {branch, ixs_int(ctx, 0)};
  ixs_node *cds[] = {guard, ixs_true(ctx)};
  ixs_node *pw = ixs_pw(ctx, 2, vals, cds);

  ixs_node *assumes[] = {
      ixs_cmp(ctx, N, IXS_CMP_GE, ixs_int(ctx, 1)),
      ixs_cmp(ctx, M, IXS_CMP_GE, ixs_int(ctx, 1)),
  };
  ixs_node *result = ixs_simplify(ctx, pw, assumes, 2);
  CHECK(result == ixs_int(ctx, 0));

  /* Negative: when both factors could be zero, decomposition must not
   * fire.  floor(x)*floor(y) <= 0 with x,y >= 0: either factor could
   * be zero, so we cannot pin one to 0. */
  {
    ixs_node *x = ixs_sym(ctx, "x");
    ixs_node *y = ixs_sym(ctx, "y");
    ixs_node *fx = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 32)));
    ixs_node *fy = ixs_floor(ctx, ixs_div(ctx, y, ixs_int(ctx, 32)));
    ixs_node *prod = ixs_mul(ctx, fx, fy);
    ixs_node *neg_branch = ixs_floor(ctx, ixs_div(ctx, prod, ixs_int(ctx, 7)));
    ixs_node *neg_guard = ixs_cmp(ctx, prod, IXS_CMP_LE, ixs_int(ctx, 0));
    ixs_node *neg_vals[] = {neg_branch, ixs_int(ctx, 0)};
    ixs_node *neg_cds[] = {neg_guard, ixs_true(ctx)};
    ixs_node *neg_pw = ixs_pw(ctx, 2, neg_vals, neg_cds);
    ixs_node *neg_assumes[] = {
        ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
        ixs_cmp(ctx, y, IXS_CMP_GE, ixs_int(ctx, 0)),
    };
    ixs_node *neg_result = ixs_simplify(ctx, neg_pw, neg_assumes, 2);
    CHECK(neg_result != ixs_int(ctx, 0));
  }
}

static void test_floor_symbolic_denom(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *K = ixs_sym(ctx, "K");

  /* floor(x / (128*K)) -> 0 when 0 <= x <= 127, K >= 1.
   * Bounds: x in [0,127], 128*K in [128, inf), so x/(128*K) in [0, 127/128). */
  ixs_node *e =
      ixs_floor(ctx, ixs_div(ctx, x, ixs_mul(ctx, ixs_int(ctx, 128), K)));
  ixs_node *assumes[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 127)),
      ixs_cmp(ctx, K, IXS_CMP_GE, ixs_int(ctx, 1)),
  };
  ixs_node *r = ixs_simplify(ctx, e, assumes, 3);
  CHECK(r == ixs_int(ctx, 0));

  /* floor(Mod(x, 16) / (128*K)) -> 0 with K >= 1 (Mod range [0,15]). */
  ixs_node *e2 = ixs_floor(ctx, ixs_div(ctx, ixs_mod(ctx, x, ixs_int(ctx, 16)),
                                        ixs_mul(ctx, ixs_int(ctx, 128), K)));
  ixs_node *assume_k = ixs_cmp(ctx, K, IXS_CMP_GE, ixs_int(ctx, 1));
  r = ixs_simplify(ctx, e2, &assume_k, 1);
  CHECK(r == ixs_int(ctx, 0));

  /* Difference: floor(A/D) - floor((A+1)/D) = 0 when A in [0,15], D >= 128. */
  ixs_node *A = ixs_mod(ctx, x, ixs_int(ctx, 16));
  ixs_node *D = ixs_mul(ctx, ixs_int(ctx, 128), K);
  ixs_node *diff = ixs_sub(
      ctx, ixs_floor(ctx, ixs_div(ctx, A, D)),
      ixs_floor(ctx, ixs_div(ctx, ixs_add(ctx, A, ixs_int(ctx, 1)), D)));
  r = ixs_simplify(ctx, diff, &assume_k, 1);
  CHECK(r == ixs_int(ctx, 0));

  /* Negative test: floor(x/K) with x in [0,127], K in [1,...] does NOT
   * collapse to 0 (127/1 = 127, floor could be up to 127). */
  ixs_node *e3 = ixs_floor(ctx, ixs_div(ctx, x, K));
  r = ixs_simplify(ctx, e3, assumes, 3);
  CHECK(r != ixs_int(ctx, 0));
}

static void test_floor_symbolic_denom_residue(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *a = ixs_sym(ctx, "floor_residue_a");
  ixs_node *d = ixs_sym(ctx, "floor_residue_d");
  ixs_node *one = ixs_int(ctx, 1);
  ixs_node *remainder = ixs_mod(ctx, a, d);
  ixs_node *base = ixs_floor(ctx, ixs_div(ctx, a, d));
  ixs_node *next = ixs_floor(ctx, ixs_div(ctx, ixs_add(ctx, a, one), d));
  ixs_node *previous = ixs_floor(ctx, ixs_div(ctx, ixs_sub(ctx, a, one), d));
  ixs_node *difference = ixs_sub(ctx, base, next);
  ixs_node *positive = ixs_cmp(ctx, d, IXS_CMP_GT, ixs_int(ctx, 0));
  ixs_node *no_upper_cross =
      ixs_cmp(ctx, ixs_add(ctx, remainder, one), IXS_CMP_LT, d);
  ixs_node *above_lower_boundary =
      ixs_cmp(ctx, remainder, IXS_CMP_GT, ixs_int(ctx, 0));
  ixs_node *safe[] = {positive, no_upper_cross};
  ixs_node *safe_negative[] = {positive, above_lower_boundary};
  ixs_node *boundary[] = {
      positive,
      ixs_cmp(ctx, remainder, IXS_CMP_EQ, ixs_sub(ctx, d, one)),
  };
  ixs_node *contradictory[] = {
      positive,
      ixs_cmp(ctx, d, IXS_CMP_LT, ixs_int(ctx, 0)),
      no_upper_cross,
  };
  ixs_node *overflow_left =
      ixs_floor(ctx, ixs_div(ctx, ixs_add(ctx, a, ixs_int(ctx, INT64_MAX)), d));
  ixs_node *overflow_right =
      ixs_floor(ctx, ixs_div(ctx, ixs_sub(ctx, a, one), d));
  ixs_node *overflow_difference = ixs_sub(ctx, overflow_left, overflow_right);
  ixs_node *overflow_result;

  CHECK(ixs_simplify(ctx, difference, safe, 2) == ixs_int(ctx, 0));
  CHECK(ixs_simplify(ctx,
                     ixs_sub(ctx, ixs_mul(ctx, ixs_int(ctx, 3), base),
                             ixs_mul(ctx, ixs_int(ctx, 3), next)),
                     safe, 2) == ixs_int(ctx, 0));
  CHECK(ixs_simplify(ctx, ixs_sub(ctx, base, previous), safe_negative, 2) ==
        ixs_int(ctx, 0));
  CHECK(ixs_simplify(ctx, difference, &positive, 1) != ixs_int(ctx, 0));
  CHECK(ixs_simplify(ctx, difference, &no_upper_cross, 1) != ixs_int(ctx, 0));
  CHECK(ixs_simplify(ctx, difference, boundary, 2) != ixs_int(ctx, 0));
  CHECK(ixs_simplify(ctx, difference, contradictory, 3) != ixs_int(ctx, 0));
  overflow_result = ixs_simplify(ctx, overflow_difference, &positive, 1);
  CHECK(overflow_result != NULL);
  CHECK(!ixs_is_error(overflow_result));
  CHECK(overflow_result != ixs_int(ctx, 0));
}

static void test_simplify_batch(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");

  ixs_node *exprs[3];
  exprs[0] = ixs_add(ctx, x, ixs_int(ctx, 0));
  exprs[1] = ixs_mul(ctx, ixs_int(ctx, 1), x);
  exprs[2] = ixs_floor(ctx, ixs_int(ctx, 7));

  ixs_node *assume = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_simplify_batch(ctx, exprs, 3, &assume, 1);

  CHECK(exprs[0] == x);
  CHECK(exprs[1] == x);
  CHECK(exprs[2] == ixs_int(ctx, 7));

  {
    ixs_node *y = ixs_sym(ctx, "batch_shared_y");
    ixs_node *shared = ixs_mod(ctx, x, ixs_int(ctx, 16));
    ixs_node *roots[] = {ixs_add(ctx, shared, y),
                         ixs_mul(ctx, ixs_int(ctx, 3), shared)};
    ixs_node *bounds[] = {
        ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
        ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 8)),
    };
    uint64_t before = stat_count(ctx, "mod_bounds_elim");
    ixs_simplify_batch(ctx, roots, 2, bounds, 2);
    CHECK(roots[0] == ixs_add(ctx, x, y));
    CHECK(roots[1] == ixs_mul(ctx, ixs_int(ctx, 3), x));
    CHECK(stat_count(ctx, "mod_bounds_elim") == before + 1);
    CHECK(ixs_simplify(ctx, shared, NULL, 0) == shared);
  }

  {
    enum { NROOTS = 260 };
    ixs_node *roots[NROOTS];
    ixs_node *expected[NROOTS];
    ixs_node *shared = ixs_mod(ctx, x, ixs_int(ctx, 32));
    ixs_node *bounds[] = {
        ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
        ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 16)),
    };
    uint64_t before;
    size_t i;
    for (i = 0; i < NROOTS; i++) {
      char name[32];
      ixs_node *symbol;
      snprintf(name, sizeof(name), "batch_growth_%zu", i);
      symbol = ixs_sym(ctx, name);
      roots[i] = ixs_add(ctx, shared, symbol);
      expected[i] = ixs_simplify(ctx, roots[i], bounds, 2);
    }
    before = stat_count(ctx, "mod_bounds_elim");
    ixs_simplify_batch(ctx, roots, NROOTS, bounds, 2);
    for (i = 0; i < NROOTS; i++)
      CHECK(roots[i] == expected[i]);
    CHECK(stat_count(ctx, "mod_bounds_elim") == before + 1);
  }

  {
    enum { NCASES = 100 };
    ixs_node *values[NCASES];
    ixs_node *conditions[NCASES];
    ixs_node *roots[2];
    ixs_node *expected[2];
    ixs_node *shared = ixs_mod(ctx, x, ixs_int(ctx, 64));
    ixs_node *bounds[] = {
        ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
        ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 32)),
    };
    size_t i;
    for (i = 0; i + 1u < NCASES; i++) {
      char name[40];
      snprintf(name, sizeof(name), "batch_nested_growth_%zu", i);
      values[i] = ixs_add(ctx, shared, ixs_int(ctx, (int64_t)i));
      conditions[i] =
          ixs_cmp(ctx, ixs_sym(ctx, name), IXS_CMP_GE, ixs_int(ctx, 0));
    }
    values[NCASES - 1u] = shared;
    conditions[NCASES - 1u] = ixs_true(ctx);
    roots[0] = ixs_pw(ctx, NCASES, values, conditions);
    roots[1] = ixs_add(ctx, shared, ixs_int(ctx, 101));
    expected[0] = ixs_simplify(ctx, roots[0], bounds, 2);
    expected[1] = ixs_simplify(ctx, roots[1], bounds, 2);
    ixs_simplify_batch(ctx, roots, 2, bounds, 2);
    CHECK(roots[0] == expected[0]);
    CHECK(roots[1] == expected[1]);
  }

  {
    ixs_node *shared = ixs_mod(ctx, x, ixs_int(ctx, 16));
    ixs_node *parent = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
    ixs_node *values[] = {shared, shared};
    ixs_node *conditions[] = {ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 8)),
                              ixs_true(ctx)};
    ixs_node *roots[] = {ixs_pw(ctx, 2, values, conditions), shared};
    ixs_node *expected[] = {ixs_simplify(ctx, roots[0], &parent, 1),
                            ixs_simplify(ctx, roots[1], &parent, 1)};
    ixs_simplify_batch(ctx, roots, 2, &parent, 1);
    CHECK(roots[0] == expected[0]);
    CHECK(roots[1] == expected[1]);
    CHECK(roots[1] == shared);
  }

  {
    ixs_node *shared = ixs_mod(ctx, x, ixs_int(ctx, 16));
    ixs_node *lo = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
    ixs_node *hi = ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 8));
    ixs_facts *bounded = ixs_facts_create(ctx);
    ixs_facts *empty = ixs_facts_create(ctx);
    ixs_node *bounded_batch[] = {ixs_add(ctx, shared, ixs_int(ctx, 1)),
                                 ixs_mul(ctx, ixs_int(ctx, 2), shared)};
    ixs_node *empty_batch[] = {shared};
    CHECK(ixs_facts_assume_pred(bounded, lo));
    CHECK(ixs_facts_assume_pred(bounded, hi));
    ixs_simplify_batch_facts(bounded, bounded_batch, 2);
    CHECK(bounded_batch[0] == ixs_add(ctx, x, ixs_int(ctx, 1)));
    CHECK(bounded_batch[1] == ixs_mul(ctx, ixs_int(ctx, 2), x));
    ixs_simplify_batch_facts(empty, empty_batch, 1);
    CHECK(empty_batch[0] == shared);
  }
}

static void test_fact_backed_simplification(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_ctx *other = ixs_ctx_create();
  ixs_node *x = ixs_sym(ctx, "facts_simplify_x");
  ixs_node *y = ixs_sym(ctx, "facts_simplify_y");
  ixs_node *lo = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *hi = ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 8));
  ixs_node *assumptions[2] = {lo, hi};
  ixs_node *mod = ixs_mod(ctx, x, ixs_int(ctx, 16));
  ixs_node *floor = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 8)));
  ixs_node *domain_error = ixs_mod(ctx, x, ixs_int(ctx, 0));
  ixs_node *parse_error = ixs_parse(ctx, "(", 1);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_node *legacy_batch[2] = {mod, floor};
  ixs_node *fact_batch[2] = {mod, floor};
  ixs_range_result range;

  CHECK(ixs_facts_assume_pred(facts, lo));
  CHECK(ixs_facts_assume_pred(facts, hi));
  CHECK(ixs_simplify_facts(facts, mod) ==
        ixs_simplify(ctx, mod, assumptions, 2));
  CHECK(ixs_simplify_facts(facts, mod) == x);
  CHECK(ixs_simplify_facts(facts, floor) == ixs_int(ctx, 0));
  CHECK(ixs_range_facts(facts, x, &range));
  CHECK(range.has_lower && range.lower_p == 0 && range.lower_q == 1);
  CHECK(range.has_upper && range.upper_p == 7 && range.upper_q == 1);

  ixs_simplify_batch(ctx, legacy_batch, 2, assumptions, 2);
  ixs_simplify_batch_facts(facts, fact_batch, 2);
  CHECK(fact_batch[0] == legacy_batch[0]);
  CHECK(fact_batch[1] == legacy_batch[1]);

  {
    ixs_facts *explicit_facts = ixs_facts_create(ctx);
    ixs_node *base = ixs_add(ctx, x, y);
    ixs_node *expr = ixs_floor(ctx, ixs_div(ctx, base, ixs_int(ctx, 16)));
    range.has_lower = true;
    range.has_upper = true;
    range.lower_p = 3;
    range.lower_q = 16;
    range.upper_p = 15;
    range.upper_q = 16;
    CHECK(ixs_facts_assume_range(explicit_facts, ixs_node_child(expr, 0),
                                 &range));
    CHECK(ixs_simplify_facts(explicit_facts, expr) == ixs_int(ctx, 0));
  }

  {
    ixs_facts *affine_facts = ixs_facts_create(ctx);
    ixs_node *base = ixs_sym(ctx, "facts_affine_base");
    ixs_node *derived =
        ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 3), base), ixs_int(ctx, 2));
    ixs_node *expr = ixs_floor(ctx, ixs_div(ctx, derived, ixs_int(ctx, 24)));
    range.has_lower = true;
    range.has_upper = true;
    range.lower_p = 4;
    range.lower_q = 1;
    range.upper_p = 7;
    range.upper_q = 1;
    CHECK(ixs_facts_assume_range(affine_facts, base, &range));
    CHECK(ixs_facts_derive_affine(affine_facts, base, 3, 2, derived));
    CHECK(ixs_simplify_facts(affine_facts, expr) == ixs_int(ctx, 0));
  }

  {
    ixs_facts *source = ixs_facts_create(ctx);
    ixs_facts *substituted = ixs_facts_create(ctx);
    ixs_node *base = ixs_sym(ctx, "facts_substitute_base");
    ixs_node *replacement = ixs_add(ctx, y, ixs_int(ctx, 1));
    ixs_node *source_expr = ixs_floor(ctx, ixs_div(ctx, base, ixs_int(ctx, 8)));
    ixs_node *expr = ixs_floor(ctx, ixs_div(ctx, replacement, ixs_int(ctx, 8)));
    range.has_lower = true;
    range.has_upper = true;
    range.lower_p = 0;
    range.lower_q = 1;
    range.upper_p = 7;
    range.upper_q = 8;
    CHECK(
        ixs_facts_assume_range(source, ixs_node_child(source_expr, 0), &range));
    CHECK(ixs_facts_substitute(substituted, source, base, replacement));
    CHECK(ixs_simplify_facts(substituted, expr) == ixs_int(ctx, 0));
  }

  {
    ixs_facts *source = ixs_facts_create(ctx);
    ixs_facts *substituted = ixs_facts_create(ctx);
    ixs_node *source_symbol = ixs_sym(ctx, "facts_multi_source");
    ixs_node *inner = ixs_sym(ctx, "facts_multi_inner");
    ixs_node *final = ixs_sym(ctx, "facts_multi_final");
    ixs_node *targets[2] = {source_symbol, inner};
    ixs_node *replacements[2] = {ixs_mul(ctx, ixs_int(ctx, 2), inner), final};
    ixs_node *mod4 = ixs_mod(ctx, inner, ixs_int(ctx, 4));
    ixs_node *mod8 = ixs_mod(ctx, inner, ixs_int(ctx, 8));
    ixs_node *final_mod4 = ixs_mod(ctx, final, ixs_int(ctx, 4));
    ixs_node *mod8_pred =
        ixs_cmp(ctx, ixs_mod(ctx, source_symbol, ixs_int(ctx, 8)), IXS_CMP_EQ,
                ixs_int(ctx, 0));

    CHECK(ixs_facts_assume_pred(source, mod8_pred));
    CHECK(ixs_facts_substitute_multi(substituted, source, 2, targets,
                                     replacements));
    CHECK(ixs_simplify_facts(substituted, mod4) == ixs_int(ctx, 0));
    CHECK(ixs_simplify_facts(substituted, mod8) == mod8);
    CHECK(ixs_simplify_facts(substituted, final_mod4) == final_mod4);
  }

  {
    ixs_facts *contradictory = ixs_facts_create(ctx);
    ixs_node *contradictory_floor =
        ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 100)));
    ixs_node *contradictory_batch[2] = {contradictory_floor, x};
    CHECK(ixs_facts_assume_pred(contradictory,
                                ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 10))));
    CHECK(ixs_facts_assume_pred(contradictory,
                                ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 5))));
    CHECK(ixs_simplify_facts(contradictory, x) == x);
    CHECK(ixs_simplify_facts(contradictory, contradictory_floor) ==
          contradictory_floor);
    ixs_simplify_batch_facts(contradictory, contradictory_batch, 2);
    CHECK(contradictory_batch[0] == contradictory_floor);
    CHECK(contradictory_batch[1] == x);
  }

  CHECK(ixs_simplify_facts(facts, domain_error) == domain_error);
  CHECK(ixs_simplify_facts(facts, parse_error) == parse_error);
  CHECK(ixs_is_domain_error(
      ixs_simplify_facts(facts, ixs_sym(other, "facts_simplify_x"))));

  fact_batch[0] = mod;
  fact_batch[1] = ixs_sym(other, "facts_simplify_y");
  ixs_simplify_batch_facts(facts, fact_batch, 2);
  CHECK(ixs_is_domain_error(fact_batch[0]));
  CHECK(ixs_is_domain_error(fact_batch[1]));

  fact_batch[0] = domain_error;
  fact_batch[1] = floor;
  ixs_simplify_batch_facts(facts, fact_batch, 2);
  CHECK(fact_batch[0] == domain_error);
  CHECK(fact_batch[1] == ixs_int(ctx, 0));

  {
    ixs_facts *rejected = ixs_facts_create(ctx);
    ixs_node *unsupported = ixs_or(ctx, lo, hi);
    CHECK(ixs_facts_assume_pred(rejected, lo));
    CHECK(!ixs_facts_assume_pred(rejected, unsupported));
    CHECK(ixs_is_domain_error(ixs_simplify_facts(rejected, mod)));
    CHECK(ixs_check_facts(rejected, lo) == IXS_CHECK_UNKNOWN);
  }

  ixs_ctx_destroy(other);
}

static void test_fact_backed_affine_truncating_remainder(void) {
  enum { TRUNCATING_LIMIT_CASES = 33 };
  ixs_ctx *ctx = get_ctx();
  ixs_node *a = ixs_sym(ctx, "glu_affine_a");
  ixs_node *threshold = ixs_int(ctx, INT64_C(2147483650));
  ixs_node *numerator = ixs_sub(ctx, a, threshold);
  ixs_node *argument =
      ixs_add(ctx, ixs_div(ctx, a, ixs_int(ctx, 3)), ixs_rat(ctx, 2, 3));
  ixs_node *floor_value =
      ixs_add(ctx, ixs_int(ctx, -715827884), ixs_floor(ctx, argument));
  ixs_node *ceil_value =
      ixs_add(ctx, ixs_int(ctx, -715827884), ixs_ceil(ctx, argument));
  ixs_node *guard = ixs_cmp(ctx, a, IXS_CMP_GE, threshold);
  ixs_node *values[2] = {floor_value, ceil_value};
  ixs_node *conditions[2] = {guard, ixs_true(ctx)};
  ixs_node *quotient = ixs_pw(ctx, 2, values, conditions);
  ixs_node *source =
      ixs_add(ctx, ixs_int(ctx, INT64_C(-18141941875200)),
              ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 8448), a),
                      ixs_mul(ctx, ixs_int(ctx, -25344), quotient)));
  ixs_node *optimized_source =
      ixs_add(ctx, ixs_int(ctx, INT64_C(-36283883750400)),
              ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 16896), a),
                      ixs_mul(ctx, ixs_int(ctx, -50688), quotient)));
  ixs_node *positive_mod = ixs_mod(ctx, numerator, ixs_int(ctx, 3));
  ixs_node *negative_mod =
      ixs_neg(ctx, ixs_mod(ctx, ixs_neg(ctx, numerator), ixs_int(ctx, 3)));
  ixs_node *remainder_values[2] = {positive_mod, negative_mod};
  ixs_node *remainder_conditions[2] = {
      ixs_cmp(ctx, numerator, IXS_CMP_GE, ixs_int(ctx, 0)), ixs_true(ctx)};
  ixs_node *signed_remainder =
      ixs_pw(ctx, 2, remainder_values, remainder_conditions);
  ixs_node *expected = ixs_mul(ctx, ixs_int(ctx, 8448), signed_remainder);
  ixs_node *optimized_expected =
      ixs_mul(ctx, ixs_int(ctx, 16896), signed_remainder);
  ixs_facts *crossing = ixs_facts_create(ctx);
  ixs_node *crossing_result;
  ixs_node *batch[2] = {source, optimized_source};
  ixs_node *bad_values[2];
  ixs_node *bad_conditions[2];
  ixs_node *bad_quotient;
  ixs_node *bad_source;
  ixs_facts *limited = ixs_facts_create(ctx);
  ixs_node *wide = ixs_int(ctx, 0);
  unsigned i;

  CHECK(ixs_facts_assume_pred(crossing,
                              ixs_cmp(ctx, a, IXS_CMP_GE, ixs_int(ctx, 2))));
  CHECK(ixs_facts_assume_pred(
      crossing,
      ixs_cmp(ctx, a, IXS_CMP_LE, ixs_int(ctx, INT64_C(4294967295)))));
  crossing_result = ixs_simplify_facts(crossing, source);
  CHECK(crossing_result == expected);
  CHECK(ixs_subs(ctx, crossing_result, a, ixs_int(ctx, INT64_C(2147483649))) ==
        ixs_int(ctx, -8448));
  CHECK(ixs_subs(ctx, crossing_result, a, ixs_int(ctx, INT64_C(2147483650))) ==
        ixs_int(ctx, 0));
  CHECK(ixs_subs(ctx, crossing_result, a, ixs_int(ctx, INT64_C(2147483651))) ==
        ixs_int(ctx, 8448));
  ixs_simplify_batch_facts(crossing, batch, 2);
  CHECK(batch[0] == expected);
  CHECK(batch[1] == optimized_expected);

  {
    ixs_node *raw = ixs_sym(ctx, "shared_truncating_raw");
    ixs_node *inner_argument =
        ixs_add(ctx, ixs_div(ctx, raw, ixs_int(ctx, 64)), ixs_rat(ctx, 63, 64));
    ixs_node *inner_values[2] = {ixs_floor(ctx, inner_argument),
                                 ixs_ceil(ctx, inner_argument)};
    ixs_node *inner_conditions[2] = {
        ixs_cmp(ctx, ixs_add(ctx, raw, ixs_int(ctx, 63)), IXS_CMP_GE,
                ixs_int(ctx, 0)),
        ixs_true(ctx)};
    ixs_node *inner = ixs_pw(ctx, 2, inner_values, inner_conditions);
    ixs_node *outer_numerator = ixs_sub(ctx, inner, ixs_int(ctx, 2));
    ixs_node *outer_argument =
        ixs_add(ctx, ixs_div(ctx, inner, ixs_int(ctx, 3)), ixs_rat(ctx, 1, 3));
    ixs_node *outer_values[2] = {
        ixs_add(ctx, ixs_int(ctx, -1), ixs_floor(ctx, outer_argument)),
        ixs_add(ctx, ixs_int(ctx, -1), ixs_ceil(ctx, outer_argument))};
    ixs_node *outer_conditions[2] = {
        ixs_cmp(ctx, outer_numerator, IXS_CMP_GE, ixs_int(ctx, 0)),
        ixs_true(ctx)};
    ixs_node *outer = ixs_pw(ctx, 2, outer_values, outer_conditions);
    ixs_node *shared_source =
        ixs_sub(ctx, outer_numerator, ixs_mul(ctx, ixs_int(ctx, 3), outer));
    ixs_node *shared_positive_mod =
        ixs_mod(ctx, outer_numerator, ixs_int(ctx, 3));
    ixs_node *shared_negative_mod = ixs_neg(
        ctx, ixs_mod(ctx, ixs_neg(ctx, outer_numerator), ixs_int(ctx, 3)));
    ixs_node *shared_remainder_values[2] = {shared_positive_mod,
                                            shared_negative_mod};
    ixs_node *shared_remainder_conditions[2] = {
        ixs_cmp(ctx, outer_numerator, IXS_CMP_GE, ixs_int(ctx, 0)),
        ixs_true(ctx)};
    ixs_node *shared_expected =
        ixs_pw(ctx, 2, shared_remainder_values, shared_remainder_conditions);
    ixs_facts *shared = ixs_facts_create(ctx);

    shared_expected = ixs_simplify_facts(shared, shared_expected);
    CHECK(ixs_simplify_facts(shared, shared_source) == shared_expected);
  }

  {
    ixs_node *n = ixs_sym(ctx, "affine_negative_divisor_n");
    ixs_node *d = ixs_sym(ctx, "affine_negative_divisor_d");
    ixs_node *shifted =
        ixs_div(ctx, ixs_sub(ctx, n, ixs_mul(ctx, ixs_int(ctx, 5), d)), d);
    ixs_node *negative_floor =
        ixs_add(ctx, ixs_int(ctx, 5), ixs_floor(ctx, shifted));
    ixs_node *negative_ceil =
        ixs_add(ctx, ixs_int(ctx, 5), ixs_ceil(ctx, shifted));
    ixs_node *same_sign =
        ixs_or(ctx,
               ixs_and(ctx, ixs_cmp(ctx, n, IXS_CMP_GE, ixs_int(ctx, 0)),
                       ixs_cmp(ctx, d, IXS_CMP_GT, ixs_int(ctx, 0))),
               ixs_and(ctx, ixs_cmp(ctx, n, IXS_CMP_LE, ixs_int(ctx, 0)),
                       ixs_cmp(ctx, d, IXS_CMP_LT, ixs_int(ctx, 0))));
    ixs_node *negative_values[2] = {negative_floor, negative_ceil};
    ixs_node *negative_conditions[2] = {same_sign, ixs_true(ctx)};
    ixs_node *negative_quotient =
        ixs_pw(ctx, 2, negative_values, negative_conditions);
    ixs_node *negative_source =
        ixs_sub(ctx, n, ixs_mul(ctx, d, negative_quotient));
    ixs_node *positive_modulus = ixs_neg(ctx, d);
    ixs_node *negative_positive_mod = ixs_mod(ctx, n, positive_modulus);
    ixs_node *negative_negative_mod =
        ixs_neg(ctx, ixs_mod(ctx, ixs_neg(ctx, n), positive_modulus));
    ixs_node *negative_remainder_values[2] = {negative_positive_mod,
                                              negative_negative_mod};
    ixs_node *negative_remainder_conditions[2] = {
        ixs_cmp(ctx, n, IXS_CMP_GE, ixs_int(ctx, 0)), ixs_true(ctx)};
    ixs_node *negative_expected = ixs_pw(ctx, 2, negative_remainder_values,
                                         negative_remainder_conditions);
    ixs_facts *negative_divisor = ixs_facts_create(ctx);
    ixs_node *negative_result;
    ixs_node *substituted;
    CHECK(ixs_facts_assume_pred(
        negative_divisor, ixs_cmp(ctx, n, IXS_CMP_GE, ixs_int(ctx, -20))));
    CHECK(ixs_facts_assume_pred(negative_divisor,
                                ixs_cmp(ctx, n, IXS_CMP_LE, ixs_int(ctx, 20))));
    CHECK(ixs_facts_assume_pred(negative_divisor,
                                ixs_cmp(ctx, d, IXS_CMP_EQ, ixs_int(ctx, -3))));
    negative_expected = ixs_simplify_facts(negative_divisor, negative_expected);
    negative_result = ixs_simplify_facts(negative_divisor, negative_source);
    CHECK(ixs_equivalent_facts(negative_divisor, negative_source,
                               negative_expected) == IXS_CHECK_TRUE);
    substituted = ixs_subs(ctx, negative_result, n, ixs_int(ctx, -4));
    CHECK(ixs_subs(ctx, substituted, d, ixs_int(ctx, -3)) == ixs_int(ctx, -1));
    substituted = ixs_subs(ctx, negative_result, n, ixs_int(ctx, 0));
    CHECK(ixs_subs(ctx, substituted, d, ixs_int(ctx, -3)) == ixs_int(ctx, 0));
    substituted = ixs_subs(ctx, negative_result, n, ixs_int(ctx, 4));
    CHECK(ixs_subs(ctx, substituted, d, ixs_int(ctx, -3)) == ixs_int(ctx, 1));
  }

  bad_values[0] = floor_value;
  bad_values[1] = ixs_add(ctx, ceil_value, ixs_int(ctx, 1));
  bad_conditions[0] = guard;
  bad_conditions[1] = ixs_true(ctx);
  bad_quotient = ixs_pw(ctx, 2, bad_values, bad_conditions);
  bad_source =
      ixs_add(ctx, ixs_int(ctx, INT64_C(-18141941875200)),
              ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 8448), a),
                      ixs_mul(ctx, ixs_int(ctx, -25344), bad_quotient)));
  CHECK(ixs_simplify_facts(crossing, bad_source) == bad_source);

  bad_values[1] = ceil_value;
  bad_conditions[0] =
      ixs_cmp(ctx, a, IXS_CMP_GE, ixs_int(ctx, INT64_C(2147483649)));
  bad_quotient = ixs_pw(ctx, 2, bad_values, bad_conditions);
  bad_source =
      ixs_add(ctx, ixs_int(ctx, INT64_C(-18141941875200)),
              ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 8448), a),
                      ixs_mul(ctx, ixs_int(ctx, -25344), bad_quotient)));
  CHECK(ixs_simplify_facts(crossing, bad_source) == bad_source);

  bad_values[0] = ixs_add(ctx, ixs_rat(ctx, 1, 2), ixs_floor(ctx, argument));
  bad_values[1] = ixs_add(ctx, ixs_rat(ctx, 1, 2), ixs_ceil(ctx, argument));
  bad_conditions[0] = guard;
  bad_quotient = ixs_pw(ctx, 2, bad_values, bad_conditions);
  CHECK(ixs_simplify_facts(crossing, bad_quotient) == bad_quotient);

  for (i = 0; i < TRUNCATING_LIMIT_CASES; i++) {
    char name[40];
    ixs_node *n;
    ixs_node *q;
    ixs_node *case_values[2];
    ixs_node *case_conditions[2];
    snprintf(name, sizeof(name), "truncating_limit_%u", i);
    n = ixs_sym(ctx, name);
    q = ixs_div(ctx, n, ixs_int(ctx, 3));
    case_values[0] = ixs_floor(ctx, q);
    case_values[1] = ixs_ceil(ctx, q);
    case_conditions[0] = ixs_cmp(ctx, n, IXS_CMP_GE, ixs_int(ctx, 0));
    case_conditions[1] = ixs_true(ctx);
    wide =
        ixs_add(ctx, wide,
                ixs_sub(ctx, n,
                        ixs_mul(ctx, ixs_int(ctx, 3),
                                ixs_pw(ctx, 2, case_values, case_conditions))));
  }
  CHECK(ixs_simplify_facts(limited, wide) == wide);
}

static void test_exact_divide_fact_piecewise(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *item = ixs_sym(ctx, "exact_pw_public_item");
  ixs_node *slot = ixs_sym(ctx, "exact_pw_public_slot");
  ixs_node *inner = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), item), slot);
  ixs_node *value = ixs_mul(ctx, ixs_int(ctx, 32), inner);
  ixs_node *condition = ixs_cmp(ctx, item, IXS_CMP_LT, ixs_int(ctx, 64));
  ixs_node *values[1] = {value};
  ixs_node *conditions[1] = {condition};
  ixs_node *piecewise = ixs_pw(ctx, 1, values, conditions);
  ixs_node *in_range =
      ixs_and(ctx, ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 0)),
              ixs_cmp(ctx, item, IXS_CMP_LE, ixs_int(ctx, 63)));
  ixs_node *outside = ixs_cmp(ctx, item, IXS_CMP_GE, ixs_int(ctx, 64));
  ixs_node *expected = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 8), item),
                               ixs_mul(ctx, ixs_int(ctx, 4), slot));
  ixs_facts *unknown = ixs_facts_create(ctx);
  ixs_facts *active = ixs_facts_create(ctx);
  ixs_facts *inactive = ixs_facts_create(ctx);
  ixs_exact_divide_result result;

  CHECK(ixs_facts_assume_pred(active, in_range));
  result = ixs_try_exact_divide_facts(active, piecewise, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_PROVEN);
  CHECK(ixs_same_node(result.quotient, expected));

  result = ixs_try_exact_divide_facts(unknown, piecewise, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_UNKNOWN);
  CHECK(result.quotient == NULL);

  CHECK(ixs_facts_assume_pred(inactive, outside));
  result = ixs_try_exact_divide_facts(inactive, piecewise, 8);
  CHECK(result.status == IXS_EXACT_DIVIDE_UNKNOWN);
  CHECK(result.quotient == NULL);
}

static void test_fact_rewrite_constant_power(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *large = ixs_sym(ctx, "fact_power_large");
  ixs_node *modulus = ixs_sym(ctx, "fact_power_modulus");
  ixs_node *raw0 = ixs_sym(ctx, "fact_power_raw0");
  ixs_node *raw1 = ixs_sym(ctx, "fact_power_raw1");
  ixs_node *raw7 = ixs_sym(ctx, "fact_power_raw7");
  ixs_node *unrelated = ixs_sym(ctx, "fact_power_unrelated");
  ixs_node *zero = ixs_sym(ctx, "fact_power_zero");
  ixs_node *square = ixs_mul(ctx, large, large);
  ixs_node *quotient = ixs_floor(ctx, ixs_div(ctx, raw0, raw7));
  ixs_node *expr = ixs_mod(ctx, quotient, raw1);
  ixs_node *undefined = ixs_div(ctx, raw0, zero);
  ixs_node *expected = ixs_floor(ctx, ixs_div(ctx, raw0, ixs_int(ctx, 128)));
  ixs_facts *large_facts = ixs_facts_create(ctx);
  ixs_facts *facts = ixs_facts_create(ctx);
  ixs_facts *zero_facts = ixs_facts_create(ctx);
  ixs_node *batch[] = {expr, quotient};
  ixs_node *large_batch[] = {square};
  ixs_node *mul;
  ixs_node *coeff;
  ixs_node *result;
  size_t errors;

  CHECK(ixs_facts_assume_pred(
      large_facts,
      ixs_cmp(ctx, large, IXS_CMP_EQ, ixs_int(ctx, (int64_t)1 << 40))));
  errors = ixs_ctx_nerrors(ctx);
  result = ixs_simplify_facts(large_facts, square);
  CHECK(result && !ixs_is_error(result));
  CHECK(ixs_ctx_nerrors(ctx) == errors);
  CHECK(ixs_node_tag(result) == IXS_MUL);
  CHECK(ixs_node_mul_nfactors(result) == 1);
  CHECK(ixs_node_tag(ixs_node_mul_factor_base(result, 0)) == IXS_INT);
  CHECK(ixs_node_int_val(ixs_node_mul_factor_base(result, 0)) ==
        ((int64_t)1 << 40));
  CHECK(ixs_node_mul_factor_exp(result, 0) == 2);
  ixs_simplify_batch_facts(large_facts, large_batch, 1);
  CHECK(large_batch[0] == result);
  CHECK(ixs_ctx_nerrors(ctx) == errors);
  result = ixs_add(ctx, ixs_mul(ctx, result, ixs_mod(ctx, raw0, modulus)),
                   unrelated);
  CHECK(result && !ixs_is_error(result));
  CHECK(ixs_ctx_nerrors(ctx) == errors);

  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, raw0, IXS_CMP_GE, ixs_int(ctx, 0))));
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, raw0, IXS_CMP_LE, ixs_int(ctx, 255))));
  CHECK(ixs_facts_assume_pred(facts,
                              ixs_cmp(ctx, raw1, IXS_CMP_EQ, ixs_int(ctx, 2))));
  CHECK(ixs_facts_assume_pred(
      facts, ixs_cmp(ctx, raw7, IXS_CMP_EQ, ixs_int(ctx, 128))));

  CHECK(ixs_simplify_facts(facts, expr) == expected);
  ixs_simplify_batch_facts(facts, batch, 2);
  CHECK(batch[0] == expected);
  CHECK(batch[1] == expected);

  /* Rewritten denominator belongs in MUL coefficient, not constant factor. */
  mul = ixs_node_unary_arg(expected);
  CHECK(ixs_node_tag(mul) == IXS_MUL);
  coeff = ixs_node_mul_coeff(mul);
  CHECK(ixs_node_tag(coeff) == IXS_RAT);
  CHECK(ixs_node_rat_num(coeff) == 1);
  CHECK(ixs_node_rat_den(coeff) == 128);
  CHECK(ixs_node_mul_nfactors(mul) == 1);
  CHECK(ixs_node_mul_factor_base(mul, 0) == raw0);
  CHECK(ixs_node_mul_factor_exp(mul, 0) == 1);

  {
    ixs_facts *wide = ixs_facts_create(ctx);
    ixs_range_result range = {true, true, 127, 1, 128, 1};
    CHECK(ixs_facts_assume_range(wide, raw7, &range));
    CHECK(ixs_simplify_facts(wide, quotient) == quotient);
  }

  CHECK(ixs_facts_assume_pred(zero_facts,
                              ixs_cmp(ctx, zero, IXS_CMP_EQ, ixs_int(ctx, 0))));
  errors = ixs_ctx_nerrors(ctx);
  result = ixs_simplify_facts(zero_facts, undefined);
  CHECK(result && ixs_is_domain_error(result));
  CHECK(ixs_ctx_nerrors(ctx) == errors + 1);
  CHECK(strstr(ixs_ctx_error(ctx, errors), "division by zero") != NULL);
}

static void test_compound_assumption_simplification(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "compound_x");
  ixs_node *lo = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0));
  ixs_node *hi = ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 32));
  ixs_node *both = ixs_and(ctx, lo, hi);
  ixs_node *either = ixs_or(ctx, lo, hi);
  ixs_node *mod = ixs_mod(ctx, x, ixs_int(ctx, 32));
  ixs_node *floor = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 32)));
  ixs_node *exprs[2];
  ixs_node *result;

  result = ixs_simplify(ctx, mod, &both, 1);
  CHECK(result == x);

  exprs[0] = mod;
  exprs[1] = floor;
  ixs_simplify_batch(ctx, exprs, 2, &both, 1);
  CHECK(exprs[0] == x);
  CHECK(exprs[1] == ixs_int(ctx, 0));

  ixs_ctx_clear_errors(ctx);
  result = ixs_simplify(ctx, mod, &either, 1);
  CHECK(ixs_is_domain_error(result));
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "OR") != NULL);

  exprs[0] = mod;
  exprs[1] = floor;
  ixs_ctx_clear_errors(ctx);
  ixs_simplify_batch(ctx, exprs, 2, &either, 1);
  CHECK(ixs_is_domain_error(exprs[0]));
  CHECK(ixs_is_domain_error(exprs[1]));
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  CHECK(strstr(ixs_ctx_error(ctx, 0), "OR") != NULL);
}

static void test_print_c(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");

  /* floor -> ixs_floor_i */
  ixs_node *fl = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 4)));
  ixs_print_c(fl, buf, sizeof(buf));
  CHECK(strstr(buf, "ixs_floor_i") != NULL);

  /* Mod -> ixs_mod_i */
  ixs_node *m = ixs_mod(ctx, x, ixs_int(ctx, 8));
  ixs_print_c(m, buf, sizeof(buf));
  CHECK(strstr(buf, "ixs_mod_i") != NULL);

  /* xor -> infix ^ */
  ixs_node *xr = ixs_xor(ctx, x, y);
  ixs_print_c(xr, buf, sizeof(buf));
  CHECK(strstr(buf, " ^ ") != NULL);

  /* integer */
  ixs_print_c(ixs_int(ctx, 42), buf, sizeof(buf));
  CHECK(strcmp(buf, "42") == 0);
}

static void test_floor_drop_fractional_const(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *fl_x = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)));

  /* floor(1/2 * floor(x/3) + 1/4)  ->  floor(1/2 * floor(x/3))
   * 1/4 < 1/2 = 1/lcm(denom) */
  ixs_node *a = ixs_floor(ctx, ixs_add(ctx, ixs_div(ctx, fl_x, ixs_int(ctx, 2)),
                                       ixs_rat(ctx, 1, 4)));
  ixs_node *expected = ixs_floor(ctx, ixs_div(ctx, fl_x, ixs_int(ctx, 2)));
  CHECK(a == expected);

  /* floor(1/2 * floor(x/3) + 15/32) also drops (15/32 < 1/2) */
  ixs_node *b = ixs_floor(ctx, ixs_add(ctx, ixs_div(ctx, fl_x, ixs_int(ctx, 2)),
                                       ixs_rat(ctx, 15, 32)));
  CHECK(b == expected);

  /* floor(1/2 * floor(x/3) + 1/2) does NOT drop (1/2 >= 1/2) */
  ixs_node *c = ixs_floor(ctx, ixs_add(ctx, ixs_div(ctx, fl_x, ixs_int(ctx, 2)),
                                       ixs_rat(ctx, 1, 2)));
  CHECK(c != expected);

  /* Multi-term: floor(1/2*fl_x + 1/3*fl_y + 1/7)
   * lcm(2,3)=6, 1/7 < 1/6 => drop constant */
  ixs_node *fl_y = ixs_floor(ctx, ixs_div(ctx, y, ixs_int(ctx, 5)));
  ixs_node *d =
      ixs_floor(ctx, ixs_add(ctx,
                             ixs_add(ctx, ixs_div(ctx, fl_x, ixs_int(ctx, 2)),
                                     ixs_div(ctx, fl_y, ixs_int(ctx, 3))),
                             ixs_rat(ctx, 1, 7)));
  ixs_node *d_exp =
      ixs_floor(ctx, ixs_add(ctx, ixs_div(ctx, fl_x, ixs_int(ctx, 2)),
                             ixs_div(ctx, fl_y, ixs_int(ctx, 3))));
  CHECK(d == d_exp);
}

static void test_round_extract_rat_split(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");

  /* floor(65/32 + 1/2*floor(x/16))  ->  2 + floor(1/32 + 1/2*floor(x/16))
   * then floor_drop_const fires on 1/32 < 1/2 => 2 + floor(1/2*floor(x/16))
   * i.e. overall result: 2 + floor(floor(x/16) / 2) */
  ixs_node *fl_x16 = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 16)));
  ixs_node *a = ixs_floor(ctx, ixs_add(ctx, ixs_rat(ctx, 65, 32),
                                       ixs_div(ctx, fl_x16, ixs_int(ctx, 2))));
  ixs_node *expected_a =
      ixs_add(ctx, ixs_int(ctx, 2),
              ixs_floor(ctx, ixs_div(ctx, fl_x16, ixs_int(ctx, 2))));
  CHECK(a == expected_a);

  /* floor(7/3 + floor(x/5) / 3) -> 2 + floor(1/3 + floor(x/5)/3)
   * 1/3 >= 1/3 so const is NOT dropped; verify integer part extracted. */
  ixs_node *fl_x5 = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 5)));
  ixs_node *b = ixs_floor(ctx, ixs_add(ctx, ixs_rat(ctx, 7, 3),
                                       ixs_div(ctx, fl_x5, ixs_int(ctx, 3))));
  /* Constant is 7/3=2+1/3. After split, integer 2 is extracted.
   * 1/3 is NOT dropped (1/3 >= 1/lcm where lcm=3).
   * Result: 2 + floor(1/3 + floor(x/5)/3) */
  ixs_node *inner =
      ixs_floor(ctx, ixs_add(ctx, ixs_rat(ctx, 1, 3),
                             ixs_div(ctx, fl_x5, ixs_int(ctx, 3))));
  ixs_node *expected_b = ixs_add(ctx, ixs_int(ctx, 2), inner);
  CHECK(b == expected_b);

  /* floor(1/32 + floor(x/16) / 2) -> floor(floor(x/16) / 2)
   * RAT coeff with fl==0: no split needed, const drops directly. */
  ixs_node *c = ixs_floor(ctx, ixs_add(ctx, ixs_rat(ctx, 1, 32),
                                       ixs_div(ctx, fl_x16, ixs_int(ctx, 2))));
  ixs_node *expected_c = ixs_floor(ctx, ixs_div(ctx, fl_x16, ixs_int(ctx, 2)));
  CHECK(c == expected_c);

  /* Negative: floor(-63/32 + floor(x/16)/2).
   * -63/32 splits as fl=-2, rem=1/32.  1/32 < 1/2 => const drops.
   * Result: -2 + floor(floor(x/16)/2). */
  ixs_node *d = ixs_floor(ctx, ixs_add(ctx, ixs_rat(ctx, -63, 32),
                                       ixs_div(ctx, fl_x16, ixs_int(ctx, 2))));
  ixs_node *expected_d =
      ixs_add(ctx, ixs_int(ctx, -2),
              ixs_floor(ctx, ixs_div(ctx, fl_x16, ixs_int(ctx, 2))));
  CHECK(d == expected_d);

  /* Negative: floor(-65/32 + floor(x/16)/2).
   * -65/32 splits as fl=-3, rem=31/32.  31/32 >= 1/2 => const NOT dropped.
   * Result: -3 + floor(31/32 + floor(x/16)/2). */
  ixs_node *e = ixs_floor(ctx, ixs_add(ctx, ixs_rat(ctx, -65, 32),
                                       ixs_div(ctx, fl_x16, ixs_int(ctx, 2))));
  ixs_node *inner_e =
      ixs_floor(ctx, ixs_add(ctx, ixs_rat(ctx, 31, 32),
                             ixs_div(ctx, fl_x16, ixs_int(ctx, 2))));
  ixs_node *expected_e = ixs_add(ctx, ixs_int(ctx, -3), inner_e);
  CHECK(e == expected_e);

  /* floor(INT64_MIN/3) is representable, but multiplying it by 3 is one below
   * INT64_MIN.  Leave the rounding node intact when that checked split cannot
   * be formed. */
  ixs_node *extreme = ixs_add(ctx, ixs_rat(ctx, INT64_MIN, 3),
                              ixs_div(ctx, x, ixs_int(ctx, 3)));
  ixs_node *extreme_ceil = ixs_ceil(ctx, extreme);
  CHECK(extreme_ceil && ixs_node_tag(extreme_ceil) == IXS_CEIL);
  CHECK(ixs_node_unary_arg(extreme_ceil) == extreme);
}

static void test_floor_drop_const_sym(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *D = ixs_sym(ctx, "D");
  ixs_node *dinv = ixs_div(ctx, ixs_int(ctx, 1), D);

  /* floor(x*D^{-1} + (1/32)*D^{-1}):
   * Both terms share D^{-1}. base: x has scaled num=32. const: num=1.
   * g_bases=32, lcm=32, gcd(32,32)=32, 1%32=1>0 => drop constant. */
  ixs_node *xD = ixs_mul(ctx, x, dinv);
  ixs_node *cD = ixs_mul(ctx, ixs_rat(ctx, 1, 32), dinv);
  ixs_node *e1 = ixs_floor(ctx, ixs_add(ctx, xD, cD));
  ixs_node *assume_d = ixs_cmp(ctx, D, IXS_CMP_GE, ixs_int(ctx, 1));
  ixs_node *expected1 = ixs_floor(ctx, xD);
  ixs_node *r1 = ixs_simplify(ctx, e1, &assume_d, 1);
  CHECK(r1 == expected1);

  /* floor(x*D^{-1} + 1*D^{-1}): const scaled=32, gcd(32,32)=32,
   * 32%32=0 => no fire (the 1/D matters). */
  ixs_node *e2 = ixs_floor(ctx, ixs_add(ctx, xD, dinv));
  ixs_node *r2 = ixs_simplify(ctx, e2, &assume_d, 1);
  CHECK(r2 == e2);

  /* floor(32*x*D^{-1} + (5/32)*D^{-1}):
   * base: scaled num = 32*32=1024. const: 5.
   * g_bases=1024, lcm=32, gcd(1024,32)=32, 5%32=5>0 => drop. */
  ixs_node *x32D = ixs_mul(ctx, ixs_mul(ctx, ixs_int(ctx, 32), x), dinv);
  ixs_node *c5D = ixs_mul(ctx, ixs_rat(ctx, 5, 32), dinv);
  ixs_node *e3 = ixs_floor(ctx, ixs_add(ctx, x32D, c5D));
  ixs_node *r3 = ixs_simplify(ctx, e3, &assume_d, 1);
  ixs_node *expected3 = ixs_floor(ctx, x32D);
  CHECK(r3 == expected3);

  /* floor(x*D^{-1} + (17/32)*D^{-1}): 17%32=17>0 => drop. */
  ixs_node *c17D = ixs_mul(ctx, ixs_rat(ctx, 17, 32), dinv);
  ixs_node *e4 = ixs_floor(ctx, ixs_add(ctx, xD, c17D));
  ixs_node *r4 = ixs_simplify(ctx, e4, &assume_d, 1);
  CHECK(r4 == expected1);

  /* Partial: floor(x*D^{-1} + (33/32)*D^{-1}).
   * const=33, gcd=32, 33%32=1>0 => reduce to floor(x/D + 1/D). */
  ixs_node *c33D = ixs_mul(ctx, ixs_rat(ctx, 33, 32), dinv);
  ixs_node *e5 = ixs_floor(ctx, ixs_add(ctx, xD, c33D));
  ixs_node *r5 = ixs_simplify(ctx, e5, &assume_d, 1);
  CHECK(r5 == e2);

  /* Construction-time path (no ixs_simplify, bnds=NULL):
   * floor_drop_const_sym has needs_bounds=false, so it fires from
   * simp_floor directly.  Same pattern as e1 above. */
  {
    ixs_node *ct = ixs_floor(ctx, ixs_add(ctx, xD, cD));
    CHECK(ct == expected1);
  }
}

static void test_add_flatten_neg(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");

  /* (x + y) - (x + y) = 0: negated ADD must flatten */
  ixs_node *s = ixs_add(ctx, x, y);
  CHECK(ixs_sub(ctx, s, s) == ixs_int(ctx, 0));

  /* (2*x + 3*y) - (2*x + 3*y) = 0 */
  ixs_node *s2 = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 2), x),
                         ixs_mul(ctx, ixs_int(ctx, 3), y));
  CHECK(ixs_sub(ctx, s2, s2) == ixs_int(ctx, 0));

  /* 2*(x + y) - (x + y) = x + y */
  CHECK(ixs_sub(ctx, ixs_mul(ctx, ixs_int(ctx, 2), s), s) == s);
}

static void test_floor_non_integer_min(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *r15 = ixs_rat(ctx, 1, 5);

  /* floor(-Min(1/5, x)) must NOT simplify to -Min(1/5, x).
   * At x=1: floor(-1/5) = -1, but -1/5 = -0.2.  */
  ixs_node *m = ixs_min(ctx, x, r15);
  ixs_node *neg_m = ixs_mul(ctx, ixs_int(ctx, -1), m);
  ixs_node *fl = ixs_floor(ctx, neg_m);
  ixs_node *s = ixs_simplify(ctx, fl, NULL, 0);
  CHECK(ixs_node_tag(s) == IXS_FLOOR);

  /* floor(Min(1/5, x)) also must not drop the floor. */
  ixs_node *fl2 = ixs_floor(ctx, m);
  ixs_node *s2 = ixs_simplify(ctx, fl2, NULL, 0);
  CHECK(ixs_node_tag(s2) == IXS_FLOOR);

  /* floor(-x) should still simplify to -x (x is integer). */
  ixs_node *neg_x = ixs_mul(ctx, ixs_int(ctx, -1), x);
  ixs_node *fl3 = ixs_floor(ctx, neg_x);
  ixs_node *s3 = ixs_simplify(ctx, fl3, NULL, 0);
  CHECK(s3 == neg_x);
}

static void test_modrem_congruence(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *r;

  /* Mod(x, 8) == 3  ⟹  Mod(x, 8) → 3 */
  ixs_node *cong_x_8_3[] = {
      ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 8)), IXS_CMP_EQ,
              ixs_int(ctx, 3)),
  };
  r = ixs_simplify(ctx, ixs_mod(ctx, x, ixs_int(ctx, 8)), cong_x_8_3, 1);
  CHECK(ixs_node_int_val(r) == 3);

  /* Mod(x, 4) → 3 (since 8 % 4 == 0, remainder 3 % 4 == 3) */
  r = ixs_simplify(ctx, ixs_mod(ctx, x, ixs_int(ctx, 4)), cong_x_8_3, 1);
  CHECK(ixs_node_int_val(r) == 3);

  /* Mod(x, 2) → 1 (since 8 % 2 == 0, remainder 3 % 2 == 1) */
  r = ixs_simplify(ctx, ixs_mod(ctx, x, ixs_int(ctx, 2)), cong_x_8_3, 1);
  CHECK(ixs_node_int_val(r) == 1);

  /* Mod(x, 16) cannot be resolved (8 % 16 != 0) */
  r = ixs_simplify(ctx, ixs_mod(ctx, x, ixs_int(ctx, 16)), cong_x_8_3, 1);
  CHECK(ixs_node_tag(r) == IXS_MOD);

  /* Mod(x, 3) cannot be resolved (8 % 3 != 0) */
  r = ixs_simplify(ctx, ixs_mod(ctx, x, ixs_int(ctx, 3)), cong_x_8_3, 1);
  CHECK(ixs_node_tag(r) == IXS_MOD);

  /* Divisibility still works: Mod(x, 8) == 0 ⟹ Mod(x, 4) → 0 */
  ixs_node *div_x_8[] = {
      ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 8)), IXS_CMP_EQ,
              ixs_int(ctx, 0)),
  };
  r = ixs_simplify(ctx, ixs_mod(ctx, x, ixs_int(ctx, 4)), div_x_8, 1);
  CHECK(ixs_node_int_val(r) == 0);

  /* floor(x/4) when x ≡ 0 (mod 8) still drops floor */
  r = ixs_simplify(ctx, ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 4))),
                   div_x_8, 1);
  CHECK(strcmp(pr(r), "1/4*x") == 0);

  /* x ≡ 4 (mod 8): x is divisible by 4 (4%4==0) but NOT by 8 */
  ixs_node *cong_x_8_4[] = {
      ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 8)), IXS_CMP_EQ,
              ixs_int(ctx, 4)),
  };
  r = ixs_simplify(ctx, ixs_mod(ctx, x, ixs_int(ctx, 4)), cong_x_8_4, 1);
  CHECK(ixs_node_int_val(r) == 0);
  r = ixs_simplify(ctx, ixs_mod(ctx, x, ixs_int(ctx, 8)), cong_x_8_4, 1);
  CHECK(ixs_node_int_val(r) == 4);
  r = ixs_simplify(ctx, ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 4))),
                   cong_x_8_4, 1);
  CHECK(strcmp(pr(r), "1/4*x") == 0);

  /* floor(x/8) should NOT drop when x ≡ 4 (mod 8) */
  r = ixs_simplify(ctx, ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 8))),
                   cong_x_8_4, 1);
  CHECK(strstr(pr(r), "floor") != NULL);

  /* CRT merge: Mod(y, 4)==1 and Mod(y, 6)==3 ⟹ y ≡ 9 (mod 12) */
  ixs_node *crt_ys[] = {
      ixs_cmp(ctx, ixs_mod(ctx, y, ixs_int(ctx, 4)), IXS_CMP_EQ,
              ixs_int(ctx, 1)),
      ixs_cmp(ctx, ixs_mod(ctx, y, ixs_int(ctx, 6)), IXS_CMP_EQ,
              ixs_int(ctx, 3)),
  };
  r = ixs_simplify(ctx, ixs_mod(ctx, y, ixs_int(ctx, 12)), crt_ys, 2);
  CHECK(ixs_node_int_val(r) == 9);
  r = ixs_simplify(ctx, ixs_mod(ctx, y, ixs_int(ctx, 4)), crt_ys, 2);
  CHECK(ixs_node_int_val(r) == 1);
  r = ixs_simplify(ctx, ixs_mod(ctx, y, ixs_int(ctx, 2)), crt_ys, 2);
  CHECK(ixs_node_int_val(r) == 1);
}

static void test_mod_difference_congruence(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "mod_diff_x");
  ixs_node *z = ixs_sym(ctx, "mod_diff_z");
  ixs_node *m16 = ixs_int(ctx, 16);
  ixs_node *lhs = ixs_mod(ctx, ixs_add(ctx, x, z), m16);
  ixs_node *rhs = ixs_mod(ctx, x, m16);
  ixs_node *difference = ixs_sub(ctx, lhs, rhs);
  ixs_node *divisible =
      ixs_cmp(ctx, ixs_mod(ctx, z, m16), IXS_CMP_EQ, ixs_int(ctx, 0));
  ixs_node *wrong_residue =
      ixs_cmp(ctx, ixs_mod(ctx, z, m16), IXS_CMP_EQ, ixs_int(ctx, 1));

  CHECK(ixs_simplify(ctx, difference, &divisible, 1) == ixs_int(ctx, 0));
  CHECK(ixs_simplify(ctx, ixs_add(ctx, ixs_int(ctx, 7), difference), &divisible,
                     1) == ixs_int(ctx, 7));
  CHECK(ixs_simplify(ctx, difference, &wrong_residue, 1) != ixs_int(ctx, 0));
  CHECK(ixs_simplify(ctx, ixs_sub(ctx, lhs, ixs_mod(ctx, x, ixs_int(ctx, 8))),
                     &divisible, 1) != ixs_int(ctx, 0));
  CHECK(ixs_simplify(ctx, difference, NULL, 0) != ixs_int(ctx, 0));
}

static void test_subs_power_overflow(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");

  /* x*x with x=0 -> 0 (constant power folding, base case) */
  ixs_node *x2 = ixs_mul(ctx, x, x);
  ixs_node *r = ixs_subs(ctx, x2, x, ixs_int(ctx, 0));
  CHECK(r && ixs_node_int_val(r) == 0);

  /* x*x with x=3 -> 9 */
  r = ixs_subs(ctx, x2, x, ixs_int(ctx, 3));
  CHECK(r && ixs_node_int_val(r) == 9);

  /* x*x with x=3/2 -> 9/4 (rational base folding) */
  r = ixs_subs(ctx, x2, x, ixs_rat(ctx, 3, 2));
  CHECK(r && ixs_node_tag(r) == IXS_RAT);
  CHECK(ixs_node_rat_num(r) == 9 && ixs_node_rat_den(r) == 4);

  /* x*x with x=2^40: (2^40)^2 overflows int64, must not error */
  int64_t big = (int64_t)1 << 40;
  r = ixs_subs(ctx, x2, x, ixs_int(ctx, big));
  CHECK(r != NULL && !ixs_is_error(r));

  /* x*x*x with x=2^30: (2^30)^3 = 2^90, overflows int64 */
  ixs_node *x3 = ixs_mul(ctx, x2, x);
  r = ixs_subs(ctx, x3, x, ixs_int(ctx, (int64_t)1 << 30));
  CHECK(r != NULL && !ixs_is_error(r));

  /* x*x with x=2^31: fits i64, (2^31)^2 = 2^62 fits too */
  r = ixs_subs(ctx, x2, x, ixs_int(ctx, (int64_t)1 << 31));
  CHECK(r && ixs_node_int_val(r) == ((int64_t)1 << 62));

  /* (3/2)^3 via substitution */
  r = ixs_subs(ctx, x3, x, ixs_rat(ctx, 3, 2));
  CHECK(r && ixs_node_tag(r) == IXS_RAT);
  CHECK(ixs_node_rat_num(r) == 27 && ixs_node_rat_den(r) == 8);
}

/* m*floor(E/m) + Mod(E, m) = E: integer and symbolic moduli. */
static void test_floor_mod_cancel(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");

  /* 4*floor(x/4) + Mod(x, 4) -> x */
  ixs_node *e =
      ixs_add(ctx,
              ixs_mul(ctx, ixs_int(ctx, 4),
                      ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 4)))),
              ixs_mod(ctx, x, ixs_int(ctx, 4)));
  CHECK(e == x);

  /* Scaled: 2*Mod(x, 4) + 8*floor(x/4) -> 2*x */
  e = ixs_add(ctx,
              ixs_mul(ctx, ixs_int(ctx, 2), ixs_mod(ctx, x, ixs_int(ctx, 4))),
              ixs_mul(ctx, ixs_int(ctx, 8),
                      ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 4)))));
  CHECK(e == ixs_mul(ctx, ixs_int(ctx, 2), x));

  /* Subtracted pair: -Mod(x, 4) - 4*floor(x/4) -> -x */
  e = ixs_add(ctx,
              ixs_mul(ctx, ixs_int(ctx, -1), ixs_mod(ctx, x, ixs_int(ctx, 4))),
              ixs_mul(ctx, ixs_int(ctx, -4),
                      ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 4)))));
  CHECK(e == ixs_mul(ctx, ixs_int(ctx, -1), x));

  /* Extra terms: y + 4*floor(x/4) + Mod(x, 4) -> y + x */
  e = ixs_add(ctx, y,
              ixs_add(ctx,
                      ixs_mul(ctx, ixs_int(ctx, 4),
                              ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 4)))),
                      ixs_mod(ctx, x, ixs_int(ctx, 4))));
  CHECK(e == ixs_add(ctx, x, y));

  /* Nested: 2*floor(floor(x/3)/2) + Mod(floor(x/3), 2) -> floor(x/3) */
  {
    ixs_node *fx3 = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)));
    e = ixs_add(ctx,
                ixs_mul(ctx, ixs_int(ctx, 2),
                        ixs_floor(ctx, ixs_div(ctx, fx3, ixs_int(ctx, 2)))),
                ixs_mod(ctx, fx3, ixs_int(ctx, 2)));
    CHECK(e == fx3);
  }

  /* No false match: 3*floor(x/4) + Mod(x, 4) should NOT cancel */
  e = ixs_add(ctx,
              ixs_mul(ctx, ixs_int(ctx, 3),
                      ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 4)))),
              ixs_mod(ctx, x, ixs_int(ctx, 4)));
  CHECK(ixs_node_tag(e) == IXS_ADD);

  /* No false match: Mod(x, 4) + 4*floor(y/4) - different lhs/arg */
  e = ixs_add(ctx, ixs_mod(ctx, x, ixs_int(ctx, 4)),
              ixs_mul(ctx, ixs_int(ctx, 4),
                      ixs_floor(ctx, ixs_div(ctx, y, ixs_int(ctx, 4)))));
  CHECK(ixs_node_tag(e) == IXS_ADD);
}

/* Floor-Mod cancellation with symbolic modulus: m*floor(E/m) + Mod(E, m). */
static void test_floor_mod_cancel_symbolic(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *K = ixs_sym(ctx, "K");
  ixs_node *L = ixs_sym(ctx, "L");
  ixs_node *M = ixs_sym(ctx, "M");
  ixs_node *half_K = ixs_div(ctx, K, ixs_int(ctx, 2));

  /* K/2 * floor(x / (K/2)) + Mod(x, K/2) -> x */
  ixs_node *fl = ixs_floor(ctx, ixs_div(ctx, x, half_K));
  ixs_node *e = ixs_add(ctx, ixs_mul(ctx, half_K, fl), ixs_mod(ctx, x, half_K));
  CHECK(e == x);

  /* With constant offset: K/2*floor((x+5)/(K/2)) + Mod(x+5, K/2) -> x+5 */
  {
    ixs_node *x5 = ixs_add(ctx, x, ixs_int(ctx, 5));
    ixs_node *fl5 = ixs_floor(ctx, ixs_div(ctx, x5, half_K));
    e = ixs_add(ctx, ixs_mul(ctx, half_K, fl5), ixs_mod(ctx, x5, half_K));
    CHECK(e == x5);
  }

  /* Difference of two pairs:
   * K/2*floor((x+A)/(K/2)) + Mod(x+A, K/2)
   * - K/2*floor((x+B)/(K/2)) - Mod(x+B, K/2) -> A - B */
  {
    ixs_node *xA = ixs_add(ctx, x, ixs_int(ctx, 100));
    ixs_node *xB = ixs_add(ctx, x, ixs_int(ctx, 60));
    ixs_node *pair_A = ixs_add(
        ctx, ixs_mul(ctx, half_K, ixs_floor(ctx, ixs_div(ctx, xA, half_K))),
        ixs_mod(ctx, xA, half_K));
    ixs_node *pair_B = ixs_add(
        ctx, ixs_mul(ctx, half_K, ixs_floor(ctx, ixs_div(ctx, xB, half_K))),
        ixs_mod(ctx, xB, half_K));
    e = ixs_sub(ctx, pair_A, pair_B);
    CHECK(e && ixs_node_tag(e) == IXS_INT && ixs_node_int_val(e) == 40);
  }

  /* 3*L*K*floor(x/K) + 3*L*Mod(x,K) -> 3*L*x */
  {
    ixs_node *flK = ixs_floor(ctx, ixs_div(ctx, x, K));
    ixs_node *outer = ixs_mul(ctx, ixs_int(ctx, 3), L);
    e = ixs_add(ctx, ixs_mul(ctx, ixs_mul(ctx, outer, K), flK),
                ixs_mul(ctx, outer, ixs_mod(ctx, x, K)));
    CHECK(e == ixs_mul(ctx, outer, x));
  }

  /* Wide ADDs defer the nested-factor scan to explicit simplification. */
  {
    ixs_node *flK = ixs_floor(ctx, ixs_div(ctx, x, K));
    ixs_node *outer = ixs_mul(ctx, ixs_int(ctx, 3), L);
    ixs_node *expected = ixs_add(ctx, M, ixs_mul(ctx, outer, x));
    e = ixs_add(ctx, M, ixs_mul(ctx, ixs_mul(ctx, outer, K), flK));
    e = ixs_add(ctx, e, ixs_mul(ctx, outer, ixs_mod(ctx, x, K)));
    CHECK(ixs_node_tag(e) == IXS_ADD);
    CHECK(ixs_simplify(ctx, e, NULL, 0) == expected);
  }

  /* 64*s*floor(x/256) + 32*s*Mod(floor(x/128),2)
   * -> 32*s*floor(x/128). */
  {
    ixs_node *x128 = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 128)));
    ixs_node *x256 = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 256)));
    ixs_node *expected = ixs_mul(ctx, ixs_int(ctx, 32), ixs_mul(ctx, L, x128));
    e = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 64), ixs_mul(ctx, L, x256)),
                ixs_mul(ctx, ixs_int(ctx, 32),
                        ixs_mul(ctx, L, ixs_mod(ctx, x128, ixs_int(ctx, 2)))));
    CHECK(e == expected);
  }

  /* Different outer factors must not cancel. */
  {
    ixs_node *flK = ixs_floor(ctx, ixs_div(ctx, x, K));
    e = ixs_add(ctx, ixs_mul(ctx, ixs_mul(ctx, L, K), flK),
                ixs_mul(ctx, M, ixs_mod(ctx, x, K)));
    CHECK(ixs_node_tag(e) == IXS_ADD);
  }

  /* Shared outer factor does not hide a wrong floor multiplier. */
  {
    ixs_node *flK = ixs_floor(ctx, ixs_div(ctx, x, K));
    e = ixs_add(
        ctx,
        ixs_mul(ctx, ixs_mul(ctx, ixs_int(ctx, 2), ixs_mul(ctx, L, K)), flK),
        ixs_mul(ctx, L, ixs_mod(ctx, x, K)));
    CHECK(ixs_node_tag(e) == IXS_ADD);
  }
}

static void test_floor_drop_const_divinfo(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *K = ixs_sym(ctx, "K");
  ixs_node *r;

  ixs_node *div_K_256[] = {
      ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 256)), IXS_CMP_EQ,
              ixs_int(ctx, 0)),
  };

  /* floor(7/8 + K/256) -> K/256 when 256 | K */
  {
    ixs_node *e = ixs_floor(
        ctx, ixs_add(ctx, ixs_div(ctx, ixs_int(ctx, 7), ixs_int(ctx, 8)),
                     ixs_div(ctx, K, ixs_int(ctx, 256))));
    r = ixs_simplify(ctx, e, div_K_256, 1);
    CHECK(strcmp(pr(r), "1/256*K") == 0);
  }

  /* floor(floor(K/32)/8 + 7/8) -> K/256 when 256 | K */
  {
    ixs_node *fk32 = ixs_floor(ctx, ixs_div(ctx, K, ixs_int(ctx, 32)));
    ixs_node *e =
        ixs_floor(ctx, ixs_add(ctx, ixs_div(ctx, fk32, ixs_int(ctx, 8)),
                               ixs_div(ctx, ixs_int(ctx, 7), ixs_int(ctx, 8))));
    r = ixs_simplify(ctx, e, div_K_256, 1);
    CHECK(strcmp(pr(r), "1/256*K") == 0);
  }

  /* floor(1/3 + K/6) -> K/6 when 6 | K */
  {
    ixs_node *div_K_6[] = {
        ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 6)), IXS_CMP_EQ,
                ixs_int(ctx, 0)),
    };
    ixs_node *e = ixs_floor(
        ctx, ixs_add(ctx, ixs_div(ctx, ixs_int(ctx, 1), ixs_int(ctx, 3)),
                     ixs_div(ctx, K, ixs_int(ctx, 6))));
    r = ixs_simplify(ctx, e, div_K_6, 1);
    CHECK(strcmp(pr(r), "1/6*K") == 0);
  }

  /* floor(1/2 + K/4) -> K/4 when 4|K: divisibility makes the grid
   * spacing 1 (not 1/4), so 1/2 < 1 and the constant drops. */
  {
    ixs_node *div_K_4[] = {
        ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 4)), IXS_CMP_EQ,
                ixs_int(ctx, 0)),
    };
    ixs_node *e = ixs_floor(
        ctx, ixs_add(ctx, ixs_div(ctx, ixs_int(ctx, 1), ixs_int(ctx, 2)),
                     ixs_div(ctx, K, ixs_int(ctx, 4))));
    r = ixs_simplify(ctx, e, div_K_4, 1);
    CHECK(strcmp(pr(r), "1/4*K") == 0);
  }

  /* floor(1/2 + K/3) -> K/3 when 3|K: same reasoning, different
   * modulus. Coefficient 1/3 has denom 3, absorbed by Mod(K,3)==0. */
  {
    ixs_node *div_K_3[] = {
        ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 3)), IXS_CMP_EQ,
                ixs_int(ctx, 0)),
    };
    ixs_node *e = ixs_floor(
        ctx, ixs_add(ctx, ixs_div(ctx, ixs_int(ctx, 1), ixs_int(ctx, 2)),
                     ixs_div(ctx, K, ixs_int(ctx, 3))));
    r = ixs_simplify(ctx, e, div_K_3, 1);
    CHECK(strcmp(pr(r), "1/3*K") == 0);
  }

  /* Negative: floor(1/2*x + 1/2*x*(x+1/2)) must NOT drop the floor
   * even with 2|x.  At x=2 the inner is 7/2, floor=3.
   * Regression: is_known_divisible declared x*(x+1/2) divisible by 2
   * because x is, without verifying (x+1/2) is integer-valued. */
  {
    ixs_node *x = ixs_sym(ctx, "x");
    ixs_node *div_x_2[] = {
        ixs_cmp(ctx, ixs_mod(ctx, x, ixs_int(ctx, 2)), IXS_CMP_EQ,
                ixs_int(ctx, 0)),
    };
    ixs_node *xph = ixs_add(ctx, x, ixs_rat(ctx, 1, 2));
    ixs_node *inner = ixs_add(ctx, x, ixs_mul(ctx, x, xph));
    ixs_node *e = ixs_floor(ctx, ixs_div(ctx, inner, ixs_int(ctx, 2)));
    r = ixs_simplify(ctx, e, div_x_2, 1);
    CHECK(strstr(pr(r), "floor(") != NULL);
  }
}

static void test_floor_extract_divinfo(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *K = ixs_sym(ctx, "K");
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *r;

  ixs_node *div_K_256[] = {
      ixs_cmp(ctx, ixs_mod(ctx, K, ixs_int(ctx, 256)), IXS_CMP_EQ,
              ixs_int(ctx, 0)),
  };

  /* floor(x/3 + K/32) -> 1/32*K + floor(1/3*x) when 32|K.
   * The rational addend K/32 is integer per congruence; extract it. */
  {
    ixs_node *e = ixs_floor(ctx, ixs_add(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)),
                                         ixs_div(ctx, K, ixs_int(ctx, 32))));
    r = ixs_simplify(ctx, e, div_K_256, 1);
    CHECK(strstr(pr(r), "1/32*K") != NULL);
    CHECK(strstr(pr(r), "floor(1/3*x)") != NULL);
    CHECK(strstr(pr(r), "floor(1/3*x + ") == NULL);
  }

  /* Same expression without bounds: floor keeps both terms inside. */
  {
    ixs_node *e = ixs_floor(ctx, ixs_add(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)),
                                         ixs_div(ctx, K, ixs_int(ctx, 32))));
    r = ixs_simplify(ctx, e, NULL, 0);
    CHECK(strstr(pr(r), "floor(") != NULL);
    CHECK(strstr(pr(r), "1/32*K") != NULL);
    CHECK(strstr(pr(r), "1/3*x") != NULL);
  }

  /* floor(x/5 + K/2) -> 1/2*K + floor(1/5*x) when 2|K. */
  {
    ixs_node *e = ixs_floor(ctx, ixs_add(ctx, ixs_div(ctx, x, ixs_int(ctx, 5)),
                                         ixs_div(ctx, K, ixs_int(ctx, 2))));
    r = ixs_simplify(ctx, e, div_K_256, 1);
    CHECK(strstr(pr(r), "1/2*K") != NULL);
    CHECK(strstr(pr(r), "floor(1/5*x)") != NULL);
  }

  /* Negative: floor(x/3 + K/257) stays fused -- 257 does not divide
   * K's known modulus 256. */
  {
    ixs_node *e = ixs_floor(ctx, ixs_add(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)),
                                         ixs_div(ctx, K, ixs_int(ctx, 257))));
    r = ixs_simplify(ctx, e, div_K_256, 1);
    CHECK(strstr(pr(r), "floor(") != NULL);
    CHECK(strstr(pr(r), "1/257*K") != NULL);
    CHECK(strstr(pr(r), "1/3*x") != NULL);
  }

  /* ceiling(x/3 + K/32) -> 1/32*K + ceiling(1/3*x) when 32|K.
   * Same path as floor; verify the ceiling branch works. */
  {
    ixs_node *e = ixs_ceil(ctx, ixs_add(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)),
                                        ixs_div(ctx, K, ixs_int(ctx, 32))));
    r = ixs_simplify(ctx, e, div_K_256, 1);
    CHECK(strstr(pr(r), "1/32*K") != NULL);
    CHECK(strstr(pr(r), "ceiling(1/3*x)") != NULL);
  }

  /* MUL*ADD path: floor((K + x) / 32) -> 1/32*K + floor(1/32*x) when 32|K.
   * round_extract_mul_add distributes 1/32 into the ADD, then
   * round_extract_add (with bounds) extracts the integer 1/32*K term. */
  {
    ixs_node *sum = ixs_add(ctx, K, x);
    ixs_node *e = ixs_floor(ctx, ixs_div(ctx, sum, ixs_int(ctx, 32)));
    r = ixs_simplify(ctx, e, div_K_256, 1);
    CHECK(strstr(pr(r), "1/32*K") != NULL);
    CHECK(strstr(pr(r), "floor(1/32*x)") != NULL);
  }

  /* Same MUL*ADD without bounds: both terms stay inside floor. */
  {
    ixs_node *sum = ixs_add(ctx, K, x);
    ixs_node *e = ixs_floor(ctx, ixs_div(ctx, sum, ixs_int(ctx, 32)));
    r = ixs_simplify(ctx, e, NULL, 0);
    CHECK(strcmp(pr(r), "floor(1/32*K + 1/32*x)") == 0);
  }

  /* MUL*ADD ceiling: ceiling((K + x) / 32) extracts K/32 when 32|K. */
  {
    ixs_node *sum = ixs_add(ctx, K, x);
    ixs_node *e = ixs_ceil(ctx, ixs_div(ctx, sum, ixs_int(ctx, 32)));
    r = ixs_simplify(ctx, e, div_K_256, 1);
    CHECK(strstr(pr(r), "1/32*K") != NULL);
    CHECK(strstr(pr(r), "ceiling(1/32*x)") != NULL);
  }

  /* Negative MUL*ADD: floor((K + x) / 257) stays fused -- 257 does
   * not divide K's known modulus 256. */
  {
    ixs_node *sum = ixs_add(ctx, K, x);
    ixs_node *e = ixs_floor(ctx, ixs_div(ctx, sum, ixs_int(ctx, 257)));
    r = ixs_simplify(ctx, e, div_K_256, 1);
    CHECK(strstr(pr(r), "floor(") != NULL);
    CHECK(strstr(pr(r), "1/257*K") != NULL);
    CHECK(strstr(pr(r), "1/257*x") != NULL);
  }
}

static void test_opposite_mul_add_cancel(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *K = ixs_sym(ctx, "K");
  ixs_node *pw = ixs_sym(ctx, "PW");
  ixs_node *e, *r;

  /* K*(PW + x) - K*(PW + 3) = K*(x - 3) */
  {
    ixs_node *a = ixs_mul(ctx, K, ixs_add(ctx, pw, x));
    ixs_node *b = ixs_mul(ctx, ixs_int(ctx, -1),
                          ixs_mul(ctx, K, ixs_add(ctx, pw, ixs_int(ctx, 3))));
    e = ixs_add(ctx, a, b);
    r = ixs_simplify(ctx, e, NULL, 0);
    CHECK(strcmp(pr(r), "K*(-3 + x)") == 0);
  }

  /* 2*K*(PW + x) - 2*K*(PW + x) = 0 */
  {
    ixs_node *t =
        ixs_mul(ctx, ixs_int(ctx, 2), ixs_mul(ctx, K, ixs_add(ctx, pw, x)));
    e = ixs_add(ctx, t, ixs_mul(ctx, ixs_int(ctx, -1), t));
    r = ixs_simplify(ctx, e, NULL, 0);
    CHECK(r == ixs_int(ctx, 0));
  }

  /* K*(PW + floor(a)) - K*(PW + floor(b)) = K*(floor(a) - floor(b)) */
  {
    ixs_node *y = ixs_sym(ctx, "y");
    ixs_node *fa = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)));
    ixs_node *fb = ixs_floor(ctx, ixs_div(ctx, y, ixs_int(ctx, 3)));
    ixs_node *a = ixs_mul(ctx, K, ixs_add(ctx, pw, fa));
    ixs_node *b =
        ixs_mul(ctx, ixs_int(ctx, -1), ixs_mul(ctx, K, ixs_add(ctx, pw, fb)));
    e = ixs_add(ctx, a, b);
    r = ixs_simplify(ctx, e, NULL, 0);
    CHECK(strcmp(pr(r), "K*(floor(1/3*x) - floor(1/3*y))") == 0);
  }
}

/* Flatten MUL-over-ADD exposes floor terms for cancel_floor_mod_pairs.
 * K*(floor(A/m) - floor(B/m)) + c*Mod(A,m) - c*Mod(B,m)
 * distributes to K*floor(A/m) - K*floor(B/m) + Mod terms,
 * then floor-Mod identity fires: c*Mod(X,m) + c*m*floor(X/m) = c*X. */
static void test_flatten_mul_add_floor_mod(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *K = ixs_sym(ctx, "K");
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *r;

  /* 4*Mod(x+192, K/128) - 4*Mod(x+64, K/128)
   * + K/32 * (floor((x+192)/(K/128)) - floor((x+64)/(K/128)))
   * = 4*(x+192) - 4*(x+64) = 512 */
  {
    ixs_node *m = ixs_div(ctx, K, ixs_int(ctx, 128));
    ixs_node *x64 = ixs_add(ctx, x, ixs_int(ctx, 64));
    ixs_node *x192 = ixs_add(ctx, x, ixs_int(ctx, 192));
    ixs_node *mod1 = ixs_mod(ctx, x64, m);
    ixs_node *mod2 = ixs_mod(ctx, x192, m);
    ixs_node *fl1 = ixs_floor(ctx, ixs_div(ctx, x64, m));
    ixs_node *fl2 = ixs_floor(ctx, ixs_div(ctx, x192, m));
    ixs_node *floor_diff =
        ixs_add(ctx, fl2, ixs_mul(ctx, ixs_int(ctx, -1), fl1));
    ixs_node *k32 = ixs_div(ctx, K, ixs_int(ctx, 32));
    ixs_node *e = ixs_add(ctx,
                          ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 4), mod2),
                                  ixs_mul(ctx, ixs_int(ctx, -4), mod1)),
                          ixs_mul(ctx, k32, floor_diff));
    r = ixs_simplify(ctx, e, NULL, 0);
    CHECK(r == ixs_int(ctx, 512));
  }

  /* Same with a single pair: Mod(A, m) + m*floor(A/m) = A,
   * but floor is inside K*floor(A/K) and Mod modulus is K. */
  {
    ixs_node *m = K;
    ixs_node *fl = ixs_floor(ctx, ixs_div(ctx, x, m));
    ixs_node *e = ixs_add(ctx, ixs_mod(ctx, x, m), ixs_mul(ctx, m, fl));
    r = ixs_simplify(ctx, e, NULL, 0);
    CHECK(r == x);
  }

  /* Negative: no Mod present, distribution should NOT fire,
   * keeping the factored form. */
  {
    ixs_node *fa = ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 3)));
    ixs_node *y = ixs_sym(ctx, "y");
    ixs_node *fb = ixs_floor(ctx, ixs_div(ctx, y, ixs_int(ctx, 3)));
    ixs_node *e =
        ixs_mul(ctx, K, ixs_add(ctx, fa, ixs_mul(ctx, ixs_int(ctx, -1), fb)));
    r = ixs_simplify(ctx, e, NULL, 0);
    CHECK(strcmp(pr(r), "K*(floor(1/3*x) - floor(1/3*y))") == 0);
  }
}

static void test_round_unwrap_inner(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *K = ixs_sym(ctx, "K");
  ixs_node *r;

  /* floor(floor(x)/3) -> floor(x/3) */
  {
    ixs_node *e =
        ixs_floor(ctx, ixs_div(ctx, ixs_floor(ctx, x), ixs_int(ctx, 3)));
    r = ixs_simplify(ctx, e, NULL, 0);
    CHECK(strcmp(pr(r), "floor(1/3*x)") == 0);
  }

  /* floor(floor(1/7*x + 1/7*K*y) / K) -> floor(1/7*x/K + 1/7*y)
   * Matches the corpus pattern: inner floor has non-integer coefficients
   * so round_extract_add doesn't split it; divisor is symbolic. */
  {
    ixs_node *y = ixs_sym(ctx, "y");
    ixs_node *inner =
        ixs_add(ctx, ixs_div(ctx, x, ixs_int(ctx, 7)),
                ixs_div(ctx, ixs_mul(ctx, K, y), ixs_int(ctx, 7)));
    ixs_node *e = ixs_floor(ctx, ixs_div(ctx, ixs_floor(ctx, inner), K));
    r = ixs_simplify(ctx, e, NULL, 0);
    CHECK(strstr(pr(r), "floor(floor(") == NULL);
  }

  /* Negative: floor(floor(x) * 3) must NOT unwrap (D=1/3, not integer). */
  {
    ixs_node *e = ixs_floor(
        ctx, ixs_mul(ctx, ixs_int(ctx, 3),
                     ixs_floor(ctx, ixs_div(ctx, x, ixs_int(ctx, 7)))));
    r = ixs_simplify(ctx, e, NULL, 0);
    CHECK(strstr(pr(r), "floor(1/7*x)") != NULL);
  }

  /* Negative: floor(floor(x) / (-3)) must NOT unwrap (D negative). */
  {
    ixs_node *neg3 = ixs_mul(ctx, ixs_int(ctx, -1), ixs_int(ctx, 3));
    ixs_node *e = ixs_floor(ctx, ixs_div(ctx, ixs_floor(ctx, x), neg3));
    r = ixs_simplify(ctx, e, NULL, 0);
    CHECK(strstr(pr(r), "floor(") != NULL);
  }

  /* ceiling(ceiling(x)/5) -> ceiling(x/5) */
  {
    ixs_node *e =
        ixs_ceil(ctx, ixs_div(ctx, ixs_ceil(ctx, x), ixs_int(ctx, 5)));
    r = ixs_simplify(ctx, e, NULL, 0);
    CHECK(strcmp(pr(r), "ceiling(1/5*x)") == 0);
  }
}

/* Bool A|~A = 1, A&~A = 0, and CMP complement pairs. */
static void test_complement_annihilation(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *zero = ixs_int(ctx, 0);

  /* NOT complement does not apply to arbitrary integer symbols. */
  CHECK(ixs_or(ctx, x, ixs_not(ctx, x)) != ixs_true(ctx));
  CHECK(ixs_or(ctx, ixs_not(ctx, x), x) != ixs_true(ctx));

  CHECK(ixs_and(ctx, x, ixs_not(ctx, x)) != ixs_false(ctx));
  CHECK(ixs_and(ctx, ixs_not(ctx, x), x) != ixs_false(ctx));

  /* CMP complement: (x > 0) | (x <= 0) = True */
  {
    ixs_node *gt = ixs_cmp(ctx, x, IXS_CMP_GT, zero);
    ixs_node *le = ixs_cmp(ctx, x, IXS_CMP_LE, zero);
    CHECK(ixs_or(ctx, gt, le) == ixs_true(ctx));
    CHECK(ixs_and(ctx, gt, le) == ixs_false(ctx));
  }

  /* CMP complement: (x == y) | (x != y) = True */
  {
    ixs_node *eq = ixs_cmp(ctx, x, IXS_CMP_EQ, y);
    ixs_node *ne = ixs_cmp(ctx, x, IXS_CMP_NE, y);
    CHECK(ixs_or(ctx, eq, ne) == ixs_true(ctx));
    CHECK(ixs_and(ctx, eq, ne) == ixs_false(ctx));
  }

  /* Piecewise((0, c), (0, ~c)) collapses to 0. */
  {
    ixs_node *c = ixs_cmp(ctx, x, IXS_CMP_GT, zero);
    ixs_node *nc = ixs_not(ctx, c);
    ixs_node *vals[] = {zero, zero};
    ixs_node *conds[] = {c, nc};
    ixs_node *pw = ixs_pw(ctx, 2, vals, conds);
    CHECK(pw == zero);
  }

  /* Negative: (x > 0) | (y <= 0) is NOT True (different operands). */
  {
    ixs_node *a = ixs_cmp(ctx, x, IXS_CMP_GT, zero);
    ixs_node *b = ixs_cmp(ctx, y, IXS_CMP_LE, zero);
    CHECK(ixs_or(ctx, a, b) != ixs_true(ctx));
  }
}

static void test_eq_substitution(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *bm = ixs_sym(ctx, "BLOCK_M");
  ixs_node *x = ixs_sym(ctx, "x");

  /* BLOCK_M == 256 => BLOCK_M + x becomes 256 + x */
  {
    ixs_node *assumptions[] = {ixs_cmp(ctx, bm, IXS_CMP_EQ, ixs_int(ctx, 256))};
    ixs_node *expr = ixs_add(ctx, bm, x);
    ixs_node *result = ixs_simplify(ctx, expr, assumptions, 1);
    ixs_node *expected =
        ixs_simplify(ctx, ixs_add(ctx, ixs_int(ctx, 256), x), NULL, 0);
    CHECK(result == expected);
  }

  /* Derived equality: x >= 5 && x <= 5 => x replaced by 5 */
  {
    ixs_node *assumptions[] = {
        ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 5)),
        ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 5)),
    };
    ixs_node *expr = ixs_add(ctx, x, ixs_int(ctx, 1));
    ixs_node *result = ixs_simplify(ctx, expr, assumptions, 2);
    CHECK(result == ixs_int(ctx, 6));
  }

  /* ceil(M / 256) with M == 256 collapses to 1 */
  {
    ixs_node *assumptions[] = {ixs_cmp(ctx, bm, IXS_CMP_EQ, ixs_int(ctx, 256))};
    ixs_node *expr = ixs_ceil(ctx, ixs_mul(ctx, bm, ixs_rat(ctx, 1, 256)));
    ixs_node *result = ixs_simplify(ctx, expr, assumptions, 1);
    CHECK(result == ixs_int(ctx, 1));
  }

  /* Negative: no equality => symbol stays */
  {
    ixs_node *assumptions[] = {ixs_cmp(ctx, bm, IXS_CMP_GE, ixs_int(ctx, 1))};
    ixs_node *expr = ixs_add(ctx, bm, ixs_int(ctx, 0));
    ixs_node *result = ixs_simplify(ctx, expr, assumptions, 1);
    CHECK(result == bm);
  }

  /* Batch: equality substitution applies to all exprs in batch */
  {
    ixs_node *assumptions[] = {ixs_cmp(ctx, bm, IXS_CMP_EQ, ixs_int(ctx, 256))};
    ixs_node *exprs[] = {
        ixs_add(ctx, bm, ixs_int(ctx, 1)),
        ixs_mul(ctx, bm, ixs_int(ctx, 2)),
    };
    ixs_simplify_batch(ctx, exprs, 2, assumptions, 1);
    CHECK(exprs[0] == ixs_int(ctx, 257));
    CHECK(exprs[1] == ixs_int(ctx, 512));
  }
}

/* Piecewise branches fork bounds; equality substitution should fire
 * independently per branch with each branch's augmented bounds. */
static void test_pw_branch_eq_substitution(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");

  /* Piecewise((x + 1, x == 5), (x + 2, True))
   * Branch 1 learns x == 5 => x + 1 becomes 6.
   * Default branch: x stays symbolic => x + 2 unchanged. */
  {
    ixs_node *vals[] = {ixs_add(ctx, x, ixs_int(ctx, 1)),
                        ixs_add(ctx, x, ixs_int(ctx, 2))};
    ixs_node *cds[] = {ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, 5)),
                       ixs_true(ctx)};
    ixs_node *pw = ixs_pw(ctx, 2, vals, cds);
    ixs_node *result = ixs_simplify(ctx, pw, NULL, 0);
    char buf[256];
    ixs_print(result, buf, sizeof(buf));
    CHECK(strcmp(buf, "Piecewise((6, -5 + x == 0), (2 + x, True))") == 0);
  }

  /* Two guarded branches with different equalities and distinct values:
   * Piecewise((x + 10, x == 3), (x + 20, x == 7), (x + 30, True))
   * Branch 1: x == 3 => 13, Branch 2: x == 7 => 27, default: x + 30. */
  {
    ixs_node *vals[] = {ixs_add(ctx, x, ixs_int(ctx, 10)),
                        ixs_add(ctx, x, ixs_int(ctx, 20)),
                        ixs_add(ctx, x, ixs_int(ctx, 30))};
    ixs_node *cds[] = {ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, 3)),
                       ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_int(ctx, 7)),
                       ixs_true(ctx)};
    ixs_node *pw = ixs_pw(ctx, 3, vals, cds);
    ixs_node *result = ixs_simplify(ctx, pw, NULL, 0);
    char buf[256];
    ixs_print(result, buf, sizeof(buf));
    CHECK(strcmp(buf, "Piecewise((13, -3 + x == 0), "
                      "(27, -7 + x == 0), (30 + x, True))") == 0);
  }
}

/* Inside a Piecewise branch whose condition implies x - y > 0,
 * Max(x - y, 1) should collapse to x - y. */
static void test_pw_max_bounds_collapse(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *one = ixs_int(ctx, 1);
  char buf[512];

  /* Piecewise((Max(x - y, 1), y - x < 0), (42, True))
   * with x >= 1, y >= 1.
   * Branch condition y - x < 0  =>  x - y > 0  =>  x - y >= 1.
   * So Max(x - y, 1) collapses to x - y. */
  {
    ixs_node *diff = ixs_add(ctx, x, ixs_mul(ctx, ixs_int(ctx, -1), y));
    ixs_node *neg_diff = ixs_add(ctx, y, ixs_mul(ctx, ixs_int(ctx, -1), x));
    ixs_node *cond = ixs_cmp(ctx, neg_diff, IXS_CMP_LT, ixs_int(ctx, 0));
    ixs_node *vals[] = {ixs_max(ctx, diff, one), ixs_int(ctx, 42)};
    ixs_node *cds[] = {cond, ixs_true(ctx)};
    ixs_node *pw = ixs_pw(ctx, 2, vals, cds);
    ixs_node *assumptions[] = {
        ixs_cmp(ctx, ixs_add(ctx, x, ixs_int(ctx, -1)), IXS_CMP_GE,
                ixs_int(ctx, 0)),
        ixs_cmp(ctx, ixs_add(ctx, y, ixs_int(ctx, -1)), IXS_CMP_GE,
                ixs_int(ctx, 0)),
    };
    ixs_node *result = ixs_simplify(ctx, pw, assumptions, 2);
    ixs_print(result, buf, sizeof(buf));
    CHECK(strstr(buf, "Max(") == NULL);
  }

  /* Standalone Max (no branch guard) — bounds alone don't prove x > y. */
  {
    ixs_node *diff = ixs_add(ctx, x, ixs_mul(ctx, ixs_int(ctx, -1), y));
    ixs_node *maxn = ixs_max(ctx, diff, one);
    ixs_node *assumptions[] = {
        ixs_cmp(ctx, ixs_add(ctx, x, ixs_int(ctx, -1)), IXS_CMP_GE,
                ixs_int(ctx, 0)),
        ixs_cmp(ctx, ixs_add(ctx, y, ixs_int(ctx, -1)), IXS_CMP_GE,
                ixs_int(ctx, 0)),
    };
    ixs_node *result = ixs_simplify(ctx, maxn, assumptions, 2);
    ixs_print(result, buf, sizeof(buf));
    CHECK(strstr(buf, "Max(") != NULL);
  }

  /* LE variant: condition y - x <= 0 => x - y >= 0.
   * Max(x - y, 0) should collapse to x - y. */
  {
    ixs_node *diff = ixs_add(ctx, x, ixs_mul(ctx, ixs_int(ctx, -1), y));
    ixs_node *neg_diff = ixs_add(ctx, y, ixs_mul(ctx, ixs_int(ctx, -1), x));
    ixs_node *cond = ixs_cmp(ctx, neg_diff, IXS_CMP_LE, ixs_int(ctx, 0));
    ixs_node *vals[] = {ixs_max(ctx, diff, ixs_int(ctx, 0)), ixs_int(ctx, 99)};
    ixs_node *cds[] = {cond, ixs_true(ctx)};
    ixs_node *pw = ixs_pw(ctx, 2, vals, cds);
    ixs_node *assumptions[] = {
        ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
        ixs_cmp(ctx, y, IXS_CMP_GE, ixs_int(ctx, 0)),
    };
    ixs_node *result = ixs_simplify(ctx, pw, assumptions, 2);
    ixs_print(result, buf, sizeof(buf));
    CHECK(strstr(buf, "Max(") == NULL);
  }
}

static void test_ceil_collapse_and_unwrap(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *r;

  /* ceil_collapse: ceil(x/32) with 1 <= x <= 32 -> 1
   * x/32 in [1/32, 1], ceil of both endpoints is 1. */
  ixs_node *a_ceil[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 1)),
      ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 32)),
  };
  r = ixs_simplify(ctx, ixs_ceil(ctx, ixs_div(ctx, x, ixs_int(ctx, 32))),
                   a_ceil, 2);
  CHECK(r && ixs_node_int_val(r) == 1);

  /* negative: ceil(x/32) with 1 <= x <= 64 should NOT collapse
   * (ceil(1/32)=1, ceil(64/32)=2). */
  ixs_node *a_wide[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 1)),
      ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 64)),
  };
  r = ixs_simplify(ctx, ixs_ceil(ctx, ixs_div(ctx, x, ixs_int(ctx, 32))),
                   a_wide, 2);
  CHECK(r && ixs_node_tag(r) != IXS_INT);

  /* ceil_unwrap_inner: ceil(ceil(A) / K) -> ceil(A / K)
   * Symbolic divisor forces nfactors > 1, bypassing round_pull_in_denom. */
  {
    ixs_node *K = ixs_sym(ctx, "K");
    ixs_node *y = ixs_sym(ctx, "y");
    ixs_node *inner_arg =
        ixs_add(ctx, ixs_div(ctx, x, ixs_int(ctx, 7)),
                ixs_div(ctx, ixs_mul(ctx, K, y), ixs_int(ctx, 7)));
    ixs_node *expr = ixs_ceil(ctx, ixs_div(ctx, ixs_ceil(ctx, inner_arg), K));
    r = ixs_simplify(ctx, expr, NULL, 0);
    CHECK(strstr(pr(r), "ceiling(ceiling(") == NULL);
  }
}

static void test_max_min_const_fold(void) {
  ixs_ctx *ctx = get_ctx();

  /* max_const_fold: Max(3, 7) -> 7 */
  CHECK(ixs_max(ctx, ixs_int(ctx, 3), ixs_int(ctx, 7)) == ixs_int(ctx, 7));

  /* Max(7, 3) -> 7 (reversed order) */
  CHECK(ixs_max(ctx, ixs_int(ctx, 7), ixs_int(ctx, 3)) == ixs_int(ctx, 7));

  /* Max with rationals: Max(1/3, 1/2) -> 1/2 */
  CHECK(ixs_max(ctx, ixs_rat(ctx, 1, 3), ixs_rat(ctx, 1, 2)) ==
        ixs_rat(ctx, 1, 2));

  /* min_const_fold: Min(3, 7) -> 3 */
  CHECK(ixs_min(ctx, ixs_int(ctx, 3), ixs_int(ctx, 7)) == ixs_int(ctx, 3));

  /* Min(7, 3) -> 3 */
  CHECK(ixs_min(ctx, ixs_int(ctx, 7), ixs_int(ctx, 3)) == ixs_int(ctx, 3));

  /* Min with rationals: Min(1/3, 1/2) -> 1/3 */
  CHECK(ixs_min(ctx, ixs_rat(ctx, 1, 3), ixs_rat(ctx, 1, 2)) ==
        ixs_rat(ctx, 1, 3));
}

static void test_min_bounds_collapse(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");

  /* Min(x, y) with 0 <= x <= 5 and 10 <= y <= 20 -> x
   * (x.hi=5 <= y.lo=10, so x is always smaller) */
  ixs_node *assumes[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 5)),
      ixs_cmp(ctx, y, IXS_CMP_GE, ixs_int(ctx, 10)),
      ixs_cmp(ctx, y, IXS_CMP_LE, ixs_int(ctx, 20)),
  };
  ixs_node *r = ixs_simplify(ctx, ixs_min(ctx, x, y), assumes, 4);
  CHECK(r == x);

  /* negative: overlapping ranges should NOT collapse */
  ixs_node *overlap[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 0)),
      ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 10)),
      ixs_cmp(ctx, y, IXS_CMP_GE, ixs_int(ctx, 5)),
      ixs_cmp(ctx, y, IXS_CMP_LE, ixs_int(ctx, 20)),
  };
  r = ixs_simplify(ctx, ixs_min(ctx, x, y), overlap, 4);
  CHECK(r && ixs_node_tag(r) != IXS_SYM);
}

static void test_cmp_const_fold(void) {
  ixs_ctx *ctx = get_ctx();

  /* 5 > 3 -> True */
  CHECK(ixs_cmp(ctx, ixs_int(ctx, 5), IXS_CMP_GT, ixs_int(ctx, 3)) ==
        ixs_true(ctx));

  /* 3 > 5 -> False */
  CHECK(ixs_cmp(ctx, ixs_int(ctx, 3), IXS_CMP_GT, ixs_int(ctx, 5)) ==
        ixs_false(ctx));

  /* 5 == 5 -> True */
  CHECK(ixs_cmp(ctx, ixs_int(ctx, 5), IXS_CMP_EQ, ixs_int(ctx, 5)) ==
        ixs_true(ctx));

  /* 5 != 5 -> False */
  CHECK(ixs_cmp(ctx, ixs_int(ctx, 5), IXS_CMP_NE, ixs_int(ctx, 5)) ==
        ixs_false(ctx));

  /* 1/3 < 1/2 -> True */
  CHECK(ixs_cmp(ctx, ixs_rat(ctx, 1, 3), IXS_CMP_LT, ixs_rat(ctx, 1, 2)) ==
        ixs_true(ctx));

  /* 1/2 <= 1/3 -> False */
  CHECK(ixs_cmp(ctx, ixs_rat(ctx, 1, 2), IXS_CMP_LE, ixs_rat(ctx, 1, 3)) ==
        ixs_false(ctx));
}

static void test_cmp_identity(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");

  /* x >= x -> True */
  CHECK(ixs_cmp(ctx, x, IXS_CMP_GE, x) == ixs_true(ctx));

  /* x <= x -> True */
  CHECK(ixs_cmp(ctx, x, IXS_CMP_LE, x) == ixs_true(ctx));

  /* x == x -> True */
  CHECK(ixs_cmp(ctx, x, IXS_CMP_EQ, x) == ixs_true(ctx));

  /* x > x -> False */
  CHECK(ixs_cmp(ctx, x, IXS_CMP_GT, x) == ixs_false(ctx));

  /* x < x -> False */
  CHECK(ixs_cmp(ctx, x, IXS_CMP_LT, x) == ixs_false(ctx));

  /* x != x -> False */
  CHECK(ixs_cmp(ctx, x, IXS_CMP_NE, x) == ixs_false(ctx));
}

static void test_cmp_normalization_overflow_fallback(void) {
  static const char wrap_text[] =
      "-9223372036854775808 + Mod(4+x,4294967296) + "
      "4294967296*Mod(2147483648+floor((4+x)/4294967296),4294967296)";
  ixs_ctx *ctx = ctx_create_or_die();
  ixs_node *x = ixs_sym(ctx, "x");
  ixs_node *y = ixs_sym(ctx, "y");
  ixs_node *wrap = ixs_parse_expr(ctx, wrap_text, strlen(wrap_text));
  ixs_node *domain_error;
  ixs_node *pred;
  ixs_node *normalized;

  CHECK(wrap && !ixs_is_error(wrap));
  CHECK(ixs_ctx_nerrors(ctx) == 0);

  /* Keep diagnostics that predate the optional normalization attempt. */
  domain_error = ixs_mod(ctx, x, ixs_int(ctx, 0));
  CHECK(domain_error && ixs_is_domain_error(domain_error));
  CHECK(ixs_ctx_nerrors(ctx) == 1);

  /* x-wrap needs +2^63 in its ADD constant, which is not representable. */
  pred = ixs_cmp(ctx, x, IXS_CMP_EQ, wrap);
  CHECK(pred && ixs_node_tag(pred) == IXS_CMP);
  CHECK(ixs_node_binary_lhs(pred) == x);
  CHECK(ixs_node_binary_rhs(pred) == wrap);
  CHECK(ixs_ctx_nerrors(ctx) == 1);

  /* Operand errors are propagated before normalization and are not erased. */
  CHECK(ixs_cmp(ctx, x, IXS_CMP_EQ, domain_error) == domain_error);
  CHECK(ixs_ctx_nerrors(ctx) == 1);
  ixs_ctx_clear_errors(ctx);

  /* A representable difference still takes the canonical zero-RHS path. */
  normalized = ixs_cmp(ctx, x, IXS_CMP_EQ, ixs_add(ctx, y, ixs_int(ctx, 4)));
  CHECK(normalized && ixs_node_tag(normalized) == IXS_CMP);
  CHECK(ixs_node_tag(ixs_node_binary_rhs(normalized)) == IXS_INT);
  CHECK(ixs_node_int_val(ixs_node_binary_rhs(normalized)) == 0);
  CHECK(ixs_node_binary_lhs(normalized) != x);
  CHECK(ixs_ctx_nerrors(ctx) == 0);

  ixs_ctx_destroy(ctx);
}

static void test_cmp_bounds_resolve(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *x = ixs_sym(ctx, "x");

  /* x >= 5 with 10 <= x <= 20 -> True */
  ixs_node *assumes[] = {
      ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 10)),
      ixs_cmp(ctx, x, IXS_CMP_LE, ixs_int(ctx, 20)),
  };
  ixs_node *ge5 = ixs_cmp(ctx, x, IXS_CMP_GE, ixs_int(ctx, 5));
  CHECK(ixs_simplify(ctx, ge5, assumes, 2) == ixs_true(ctx));

  /* x < 5 with 10 <= x <= 20 -> False */
  ixs_node *lt5 = ixs_cmp(ctx, x, IXS_CMP_LT, ixs_int(ctx, 5));
  CHECK(ixs_simplify(ctx, lt5, assumes, 2) == ixs_false(ctx));

  /* negative: x > 15 with 10 <= x <= 20 is indeterminate */
  ixs_node *gt15 = ixs_cmp(ctx, x, IXS_CMP_GT, ixs_int(ctx, 15));
  ixs_node *r = ixs_simplify(ctx, gt15, assumes, 2);
  CHECK(r != ixs_true(ctx) && r != ixs_false(ctx));
}

/* Mod bounds tightening via dividend step: upper bound is K - gcd(d, K)
 * where d is the gcd of top-level integer coefficients (MUL coeff or
 * ADD constant + term coefficients). */
static void test_mod_scaled_bounds(void) {
  ixs_ctx *ctx = get_ctx();
  ixs_node *a = ixs_sym(ctx, "a");

  /* floor(Mod(4*a + 3, 16) / 16) -> 0.
   * mod_extract_small_const rewrites to 3 + Mod(4*a, 16).  With the
   * tighter bound Mod(4*a, 16) <= 12, the argument of floor is in
   * [3/16, 15/16], which floors to 0. */
  ixs_node *expr = ixs_floor(
      ctx, ixs_div(ctx,
                   ixs_mod(ctx,
                           ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 4), a),
                                   ixs_int(ctx, 3)),
                           ixs_int(ctx, 16)),
                   ixs_int(ctx, 16)));
  CHECK(ixs_simplify(ctx, expr, NULL, 0) == ixs_int(ctx, 0));

  /* floor(Mod(8*a + 5, 16) / 16) -> 0.
   * Mod(8*a, 16) <= 8, so (5 + Mod(8*a, 16))/16 <= 13/16 < 1. */
  expr = ixs_floor(
      ctx, ixs_div(ctx,
                   ixs_mod(ctx,
                           ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 8), a),
                                   ixs_int(ctx, 5)),
                           ixs_int(ctx, 16)),
                   ixs_int(ctx, 16)));
  CHECK(ixs_simplify(ctx, expr, NULL, 0) == ixs_int(ctx, 0));

  /* Negative: floor((Mod(4*a, 16) + 13) / 16) stays as floor.
   * Even with tight bound Mod(4*a, 16) <= 12, range [13,25]/16 spans
   * two integers so the floor cannot collapse. */
  {
    ixs_node *mod4a =
        ixs_mod(ctx, ixs_mul(ctx, ixs_int(ctx, 4), a), ixs_int(ctx, 16));
    expr = ixs_floor(ctx, ixs_div(ctx, ixs_add(ctx, mod4a, ixs_int(ctx, 13)),
                                  ixs_int(ctx, 16)));
    ixs_node *r = ixs_simplify(ctx, expr, NULL, 0);
    CHECK(ixs_node_tag(r) == IXS_FLOOR);
  }

  /* Concrete modulus: Mod(16*a + 1, 128) -> 1 + 16*a with 0 <= a < 8.
   * mod_extract_small_const splits to 1 + Mod(16*a, 128), then
   * bounds [0, 112] < 128 collapse the Mod. */
  {
    ixs_node *assumes[] = {
        ixs_cmp(ctx, a, IXS_CMP_GE, ixs_int(ctx, 0)),
        ixs_cmp(ctx, a, IXS_CMP_LT, ixs_int(ctx, 8)),
    };
    ixs_node *e = ixs_mod(
        ctx, ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 16), a), ixs_int(ctx, 1)),
        ixs_int(ctx, 128));
    ixs_node *r = ixs_simplify(ctx, e, assumes, 2);
    CHECK(r ==
          ixs_add(ctx, ixs_int(ctx, 1), ixs_mul(ctx, ixs_int(ctx, 16), a)));
  }

  /* ADD case: Mod(6*a + 4*b, 12) <= 10 (gcd(6,4)=2, gcd(2,12)=2). */
  {
    ixs_node *b = ixs_sym(ctx, "b");
    ixs_node *inner = ixs_add(ctx, ixs_mul(ctx, ixs_int(ctx, 6), a),
                              ixs_mul(ctx, ixs_int(ctx, 4), b));
    expr = ixs_floor(ctx, ixs_div(ctx, ixs_mod(ctx, inner, ixs_int(ctx, 12)),
                                  ixs_int(ctx, 12)));
    CHECK(ixs_simplify(ctx, expr, NULL, 0) == ixs_int(ctx, 0));
  }
}

int main(void) {
  test_add_canonicalize();
  test_mul_canonicalize();
  test_hash_consing();
  test_floor_rules();
  test_mod_rules();
  test_mod_extract_constant_residue();
  test_mod_divisor_contract();
  test_boolean();
  test_boolean_piecewise();
  test_flat_associative_nodes();
  test_xor_nested_cancellation();
  test_xor_known_bit_simplification();
  test_simplify_with_bounds();
  test_eq_substitution();
  test_pw_branch_eq_substitution();
  test_floor_bounds_collapse();
  test_mod_bounds_tighten();
  test_mod_extract_constant();
  test_floor_drop_small_rational();
  test_floor_drop_small_bounded_term();
  test_substitution();
  test_subs_multi();
  test_sentinel_propagation();
  test_nested_floor_ceil();
  test_same_node();
  test_print_roundtrip();
  test_divisibility_assumptions();
  test_large_expressions();
  test_bounds_many_vars();
  test_mod_floor_regression();
  test_mod_recognition();
  test_floor_mod_divisor();
  test_pw_fold_in_add();
  test_piecewise_branch_bounds();
  test_product_zero_branch_collapse();
  test_pw_max_bounds_collapse();
  test_floor_symbolic_denom();
  test_floor_symbolic_denom_residue();
  test_simplify_batch();
  test_fact_backed_simplification();
  test_fact_backed_affine_truncating_remainder();
  test_exact_divide_fact_piecewise();
  test_fact_rewrite_constant_power();
  test_compound_assumption_simplification();
  test_print_c();
  test_floor_drop_fractional_const();
  test_round_extract_rat_split();
  test_floor_drop_const_sym();
  test_floor_non_integer_min();
  test_add_flatten_neg();
  test_modrem_congruence();
  test_mod_difference_congruence();
  test_subs_power_overflow();
  test_floor_mod_cancel();
  test_floor_mod_cancel_symbolic();
  test_floor_drop_const_divinfo();
  test_floor_extract_divinfo();
  test_opposite_mul_add_cancel();
  test_flatten_mul_add_floor_mod();
  test_round_unwrap_inner();
  test_complement_annihilation();
  test_ceil_collapse_and_unwrap();
  test_max_min_const_fold();
  test_min_bounds_collapse();
  test_cmp_const_fold();
  test_cmp_identity();
  test_cmp_normalization_overflow_fallback();
  test_cmp_bounds_resolve();
  test_mod_scaled_bounds();

  printf("test_simplify: %d/%d passed\n", tests_passed, tests_run);
  return tests_passed == tests_run ? 0 : 1;
}
