/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#include "interval.h"

IXS_STATIC void iv_endpoint_widen(int64_t ap, int64_t bp, int64_t *rp,
                                  int64_t *rq) {
  bool neg = (ap < 0) != ixs_rat_is_neg(bp);
  if (neg)
    ixs_interval_set_neg_inf(rp, rq);
  else
    ixs_interval_set_pos_inf(rp, rq);
}

static void iv_mul_endpoint(int64_t ap, int64_t aq, bool a_neg_inf,
                            bool a_pos_inf, int64_t bp, int64_t bq,
                            bool b_neg_inf, bool b_pos_inf, int64_t *rp,
                            int64_t *rq, bool *r_neg_inf, bool *r_pos_inf) {
  bool a_inf = a_neg_inf || a_pos_inf;
  bool b_inf = b_neg_inf || b_pos_inf;
  bool a_neg = a_neg_inf || (!a_pos_inf && ixs_rat_is_neg(ap));
  bool b_neg = b_neg_inf || (!b_pos_inf && ixs_rat_is_neg(bp));

  *r_neg_inf = false;
  *r_pos_inf = false;

  if ((a_inf && !b_inf && bp == 0) || (b_inf && !a_inf && ap == 0)) {
    *rp = 0;
    *rq = 1;
    return;
  }
  if (a_inf || b_inf) {
    if (a_neg != b_neg) {
      *r_neg_inf = true;
      ixs_interval_set_neg_inf(rp, rq);
    } else {
      *r_pos_inf = true;
      ixs_interval_set_pos_inf(rp, rq);
    }
    return;
  }

  if (!ixs_rat_mul(ap, aq, bp, bq, rp, rq)) {
    iv_endpoint_widen(ap, bp, rp, rq);
    if (ixs_interval_is_neg_inf(*rp, *rq))
      *r_neg_inf = true;
    else if (ixs_interval_is_pos_inf(*rp, *rq))
      *r_pos_inf = true;
  }
}

IXS_STATIC ixs_interval iv_add(ixs_interval a, ixs_interval b) {
  ixs_interval r;
  if (!a.valid || !b.valid)
    return ixs_interval_unknown();
  r.valid = true;
  r.lo_inf = false;
  r.hi_inf = false;
  if (a.lo_inf || b.lo_inf) {
    ixs_interval_set_lo_neg_inf(&r);
  } else if (!ixs_rat_add(a.lo_p, a.lo_q, b.lo_p, b.lo_q, &r.lo_p, &r.lo_q)) {
    if (ixs_rat_is_neg(a.lo_p) || ixs_rat_is_neg(b.lo_p))
      ixs_interval_set_lo_neg_inf(&r);
    else
      ixs_interval_set_pos_inf(&r.lo_p, &r.lo_q);
  }
  if (a.hi_inf || b.hi_inf) {
    ixs_interval_set_hi_pos_inf(&r);
  } else if (!ixs_rat_add(a.hi_p, a.hi_q, b.hi_p, b.hi_q, &r.hi_p, &r.hi_q)) {
    if (!ixs_rat_is_neg(a.hi_p) || !ixs_rat_is_neg(b.hi_p))
      ixs_interval_set_hi_pos_inf(&r);
    else
      ixs_interval_set_neg_inf(&r.hi_p, &r.hi_q);
  }
  return r;
}

IXS_STATIC ixs_interval iv_mul_const(ixs_interval a, int64_t cp, int64_t cq) {
  ixs_interval r;
  if (!a.valid)
    return ixs_interval_unknown();
  if (cp == 0)
    return ixs_interval_exact(0, 1);
  r.valid = true;
  r.lo_inf = false;
  r.hi_inf = false;
  {
    bool lo_neg_inf, lo_pos_inf, hi_neg_inf, hi_pos_inf;
    iv_mul_endpoint(a.lo_p, a.lo_q, a.lo_inf, false, cp, cq, false, false,
                    &r.lo_p, &r.lo_q, &lo_neg_inf, &lo_pos_inf);
    iv_mul_endpoint(a.hi_p, a.hi_q, false, a.hi_inf, cp, cq, false, false,
                    &r.hi_p, &r.hi_q, &hi_neg_inf, &hi_pos_inf);
    if (ixs_rat_is_neg(cp)) {
      int64_t tmp_p = r.lo_p, tmp_q = r.lo_q;
      r.lo_p = r.hi_p;
      r.lo_q = r.hi_q;
      r.lo_inf = hi_neg_inf;
      r.hi_p = tmp_p;
      r.hi_q = tmp_q;
      r.hi_inf = lo_pos_inf;
    } else {
      r.lo_inf = lo_neg_inf;
      r.hi_inf = hi_pos_inf;
    }
  }
  return r;
}

IXS_STATIC ixs_interval iv_mul(ixs_interval a, ixs_interval b) {
  ixs_interval r;
  int64_t ap[4], aq[4], bp[4], bq[4], rp[4], rq[4];
  bool a_neg_inf[4], a_pos_inf[4], b_neg_inf[4], b_pos_inf[4];
  bool r_neg_inf[4], r_pos_inf[4];
  uint32_t i;
  if (!a.valid || !b.valid)
    return ixs_interval_unknown();
  ap[0] = a.lo_p;
  aq[0] = a.lo_q;
  a_neg_inf[0] = a.lo_inf;
  a_pos_inf[0] = false;
  bp[0] = b.lo_p;
  bq[0] = b.lo_q;
  b_neg_inf[0] = b.lo_inf;
  b_pos_inf[0] = false;
  ap[1] = a.lo_p;
  aq[1] = a.lo_q;
  a_neg_inf[1] = a.lo_inf;
  a_pos_inf[1] = false;
  bp[1] = b.hi_p;
  bq[1] = b.hi_q;
  b_neg_inf[1] = false;
  b_pos_inf[1] = b.hi_inf;
  ap[2] = a.hi_p;
  aq[2] = a.hi_q;
  a_neg_inf[2] = false;
  a_pos_inf[2] = a.hi_inf;
  bp[2] = b.lo_p;
  bq[2] = b.lo_q;
  b_neg_inf[2] = b.lo_inf;
  b_pos_inf[2] = false;
  ap[3] = a.hi_p;
  aq[3] = a.hi_q;
  a_neg_inf[3] = false;
  a_pos_inf[3] = a.hi_inf;
  bp[3] = b.hi_p;
  bq[3] = b.hi_q;
  b_neg_inf[3] = false;
  b_pos_inf[3] = b.hi_inf;
  for (i = 0; i < 4; i++)
    iv_mul_endpoint(ap[i], aq[i], a_neg_inf[i], a_pos_inf[i], bp[i], bq[i],
                    b_neg_inf[i], b_pos_inf[i], &rp[i], &rq[i], &r_neg_inf[i],
                    &r_pos_inf[i]);
  r.valid = true;
  r.lo_inf = r_neg_inf[0];
  r.hi_inf = r_pos_inf[0];
  r.lo_p = rp[0];
  r.lo_q = rq[0];
  r.hi_p = rp[0];
  r.hi_q = rq[0];
  for (i = 1; i < 4; i++) {
    int cmp_lo = ixs_rat_cmp(rp[i], rq[i], r.lo_p, r.lo_q);
    int cmp_hi = ixs_rat_cmp(rp[i], rq[i], r.hi_p, r.hi_q);
    if (cmp_lo < 0 || (cmp_lo == 0 && r_neg_inf[i])) {
      r.lo_p = rp[i];
      r.lo_q = rq[i];
      r.lo_inf = r_neg_inf[i];
    }
    if (cmp_hi > 0 || (cmp_hi == 0 && r_pos_inf[i])) {
      r.hi_p = rp[i];
      r.hi_q = rq[i];
      r.hi_inf = r_pos_inf[i];
    }
  }
  return r;
}

static bool iv_rat_pow(int64_t p, int64_t q, uint32_t exp, int64_t *rp,
                       int64_t *rq) {
  int64_t base_p = p, base_q = q;
  int64_t result_p = 1, result_q = 1;

  while (exp != 0) {
    if ((exp & 1u) != 0u &&
        !ixs_rat_mul(result_p, result_q, base_p, base_q, &result_p, &result_q))
      return false;
    exp >>= 1;
    if (exp != 0 &&
        !ixs_rat_mul(base_p, base_q, base_p, base_q, &base_p, &base_q))
      return false;
  }
  *rp = result_p;
  *rq = result_q;
  return true;
}

static void iv_pow_lower(int64_t p, int64_t q, uint32_t exp, int64_t *rp,
                         int64_t *rq, bool *neg_inf) {
  *neg_inf = false;
  if (iv_rat_pow(p, q, exp, rp, rq))
    return;
  if (p < 0 && (exp & 1u) != 0u) {
    *neg_inf = true;
    ixs_interval_set_neg_inf(rp, rq);
  } else {
    *rp = 0;
    *rq = 1;
  }
}

static void iv_pow_upper(int64_t p, int64_t q, uint32_t exp, int64_t *rp,
                         int64_t *rq, bool *pos_inf) {
  *pos_inf = false;
  if (iv_rat_pow(p, q, exp, rp, rq))
    return;
  if (p >= 0 || (exp & 1u) == 0u) {
    *pos_inf = true;
    ixs_interval_set_pos_inf(rp, rq);
  } else {
    *rp = 0;
    *rq = 1;
  }
}

IXS_STATIC ixs_interval iv_pow(ixs_interval a, uint32_t exp) {
  ixs_interval r;
  int lo_cmp, hi_cmp;

  if (!a.valid)
    return ixs_interval_unknown();
  if (exp == 0)
    return ixs_interval_exact(1, 1);

  r.valid = true;
  r.lo_inf = false;
  r.hi_inf = false;
  lo_cmp = a.lo_inf ? -1 : ixs_rat_cmp(a.lo_p, a.lo_q, 0, 1);
  hi_cmp = a.hi_inf ? 1 : ixs_rat_cmp(a.hi_p, a.hi_q, 0, 1);

  if ((exp & 1u) != 0u) {
    if (a.lo_inf)
      ixs_interval_set_lo_neg_inf(&r);
    else
      iv_pow_lower(a.lo_p, a.lo_q, exp, &r.lo_p, &r.lo_q, &r.lo_inf);
    if (a.hi_inf)
      ixs_interval_set_hi_pos_inf(&r);
    else
      iv_pow_upper(a.hi_p, a.hi_q, exp, &r.hi_p, &r.hi_q, &r.hi_inf);
    return r;
  }

  if (lo_cmp >= 0) {
    iv_pow_lower(a.lo_p, a.lo_q, exp, &r.lo_p, &r.lo_q, &r.lo_inf);
    if (a.hi_inf)
      ixs_interval_set_hi_pos_inf(&r);
    else
      iv_pow_upper(a.hi_p, a.hi_q, exp, &r.hi_p, &r.hi_q, &r.hi_inf);
    return r;
  }

  if (hi_cmp <= 0) {
    iv_pow_lower(a.hi_p, a.hi_q, exp, &r.lo_p, &r.lo_q, &r.lo_inf);
    if (a.lo_inf)
      ixs_interval_set_hi_pos_inf(&r);
    else
      iv_pow_upper(a.lo_p, a.lo_q, exp, &r.hi_p, &r.hi_q, &r.hi_inf);
    return r;
  }

  r.lo_p = 0;
  r.lo_q = 1;
  if (a.lo_inf || a.hi_inf) {
    ixs_interval_set_hi_pos_inf(&r);
  } else {
    int64_t lp, lq, hp, hq;
    bool linf, hinf;
    iv_pow_upper(a.lo_p, a.lo_q, exp, &lp, &lq, &linf);
    iv_pow_upper(a.hi_p, a.hi_q, exp, &hp, &hq, &hinf);
    if (linf || hinf) {
      ixs_interval_set_hi_pos_inf(&r);
    } else if (ixs_rat_cmp(lp, lq, hp, hq) >= 0) {
      r.hi_p = lp;
      r.hi_q = lq;
    } else {
      r.hi_p = hp;
      r.hi_q = hq;
    }
  }
  return r;
}

static bool iv_recip_endpoint(int64_t p, int64_t q, int64_t *rp, int64_t *rq) {
  return ixs_rat_div(1, 1, p, q, rp, rq);
}

IXS_STATIC ixs_interval iv_recip(ixs_interval a) {
  ixs_interval r;
  bool positive, negative;

  if (!a.valid)
    return ixs_interval_unknown();
  positive = !a.lo_inf && ixs_rat_cmp(a.lo_p, a.lo_q, 0, 1) > 0;
  negative = !a.hi_inf && ixs_rat_cmp(a.hi_p, a.hi_q, 0, 1) < 0;
  if (!positive && !negative)
    return ixs_interval_unknown();

  r.valid = true;
  r.lo_inf = false;
  r.hi_inf = false;

  if (positive) {
    if (a.hi_inf) {
      r.lo_p = 0;
      r.lo_q = 1;
    } else if (!iv_recip_endpoint(a.hi_p, a.hi_q, &r.lo_p, &r.lo_q)) {
      r.lo_p = 0;
      r.lo_q = 1;
    }
    if (!iv_recip_endpoint(a.lo_p, a.lo_q, &r.hi_p, &r.hi_q))
      ixs_interval_set_hi_pos_inf(&r);
  } else {
    if (!iv_recip_endpoint(a.hi_p, a.hi_q, &r.lo_p, &r.lo_q))
      ixs_interval_set_lo_neg_inf(&r);
    if (a.lo_inf) {
      r.hi_p = 0;
      r.hi_q = 1;
    } else if (!iv_recip_endpoint(a.lo_p, a.lo_q, &r.hi_p, &r.hi_q)) {
      r.hi_p = 0;
      r.hi_q = 1;
    }
  }
  return r;
}

IXS_STATIC ixs_interval iv_intersect(ixs_interval a, ixs_interval b) {
  ixs_interval r;
  if (!a.valid)
    return b;
  if (!b.valid)
    return a;
  r.valid = true;
  r.lo_inf = false;
  r.hi_inf = false;
  if (a.lo_inf && !b.lo_inf) {
    r.lo_p = b.lo_p;
    r.lo_q = b.lo_q;
    r.lo_inf = false;
  } else if (!a.lo_inf && b.lo_inf) {
    r.lo_p = a.lo_p;
    r.lo_q = a.lo_q;
    r.lo_inf = false;
  } else if (ixs_rat_cmp(a.lo_p, a.lo_q, b.lo_p, b.lo_q) >= 0) {
    r.lo_p = a.lo_p;
    r.lo_q = a.lo_q;
    r.lo_inf = a.lo_inf;
  } else {
    r.lo_p = b.lo_p;
    r.lo_q = b.lo_q;
    r.lo_inf = b.lo_inf;
  }
  if (a.hi_inf && !b.hi_inf) {
    r.hi_p = b.hi_p;
    r.hi_q = b.hi_q;
    r.hi_inf = false;
  } else if (!a.hi_inf && b.hi_inf) {
    r.hi_p = a.hi_p;
    r.hi_q = a.hi_q;
    r.hi_inf = false;
  } else if (ixs_rat_cmp(a.hi_p, a.hi_q, b.hi_p, b.hi_q) <= 0) {
    r.hi_p = a.hi_p;
    r.hi_q = a.hi_q;
    r.hi_inf = a.hi_inf;
  } else {
    r.hi_p = b.hi_p;
    r.hi_q = b.hi_q;
    r.hi_inf = b.hi_inf;
  }
  if (!r.lo_inf && !r.hi_inf && ixs_rat_cmp(r.lo_p, r.lo_q, r.hi_p, r.hi_q) > 0)
    r.valid = false;
  return r;
}

IXS_STATIC ixs_interval iv_hull(ixs_interval a, ixs_interval b) {
  ixs_interval r;
  if (!a.valid || !b.valid)
    return ixs_interval_unknown();
  r.valid = true;
  r.lo_inf = false;
  r.hi_inf = false;
  if (a.lo_inf || b.lo_inf) {
    ixs_interval_set_lo_neg_inf(&r);
  } else if (ixs_rat_cmp(a.lo_p, a.lo_q, b.lo_p, b.lo_q) <= 0) {
    r.lo_p = a.lo_p;
    r.lo_q = a.lo_q;
  } else {
    r.lo_p = b.lo_p;
    r.lo_q = b.lo_q;
  }
  if (a.hi_inf || b.hi_inf) {
    ixs_interval_set_hi_pos_inf(&r);
  } else if (ixs_rat_cmp(a.hi_p, a.hi_q, b.hi_p, b.hi_q) >= 0) {
    r.hi_p = a.hi_p;
    r.hi_q = a.hi_q;
  } else {
    r.hi_p = b.hi_p;
    r.hi_q = b.hi_q;
  }
  return r;
}
