/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_INTERVAL_H
#define IXS_INTERVAL_H

#include "rational.h"
#include <stdbool.h>
#include <stdint.h>

typedef struct {
  int64_t lo_p, lo_q; /* lower bound (rational), inclusive */
  int64_t hi_p, hi_q; /* upper bound (rational), inclusive */
  bool valid;
} ixs_interval;

static inline ixs_interval ixs_interval_unknown(void) {
  ixs_interval iv;
  iv.valid = false;
  iv.lo_p = iv.lo_q = iv.hi_p = iv.hi_q = 0;
  return iv;
}

static inline ixs_interval ixs_interval_exact(int64_t p, int64_t q) {
  ixs_interval iv;
  iv.valid = true;
  iv.lo_p = iv.hi_p = p;
  iv.lo_q = iv.hi_q = q;
  return iv;
}

static inline ixs_interval ixs_interval_range(int64_t lo_p, int64_t lo_q,
                                              int64_t hi_p, int64_t hi_q) {
  ixs_interval iv;
  iv.valid = true;
  iv.lo_p = lo_p;
  iv.lo_q = lo_q;
  iv.hi_p = hi_p;
  iv.hi_q = hi_q;
  return iv;
}

/* Widen one endpoint to +/-infinity based on the sign of the product. */
void iv_endpoint_widen(int64_t ap, int64_t bp, int64_t *rp, int64_t *rq);

ixs_interval iv_add(ixs_interval a, ixs_interval b);
ixs_interval iv_mul_const(ixs_interval a, int64_t cp, int64_t cq);
ixs_interval iv_mul(ixs_interval a, ixs_interval b);

/* Reciprocal of a strictly positive interval. Returns unknown if
 * the interval contains zero or is invalid. */
ixs_interval iv_recip(ixs_interval a);

ixs_interval iv_intersect(ixs_interval a, ixs_interval b);

#endif /* IXS_INTERVAL_H */
