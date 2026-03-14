#ifndef IXS_BOUNDS_H
#define IXS_BOUNDS_H

#include "node.h"

/*
 * Lightweight interval analysis for bound-dependent rewrites.
 * Stores per-variable intervals extracted from comparison assumptions,
 * and propagates through expression structure.
 */

typedef struct {
  int64_t lo_p, lo_q; /* lower bound (rational), inclusive */
  int64_t hi_p, hi_q; /* upper bound (rational), inclusive */
  bool valid;
} ixs_interval;

#define IXS_BOUNDS_MAX_VARS 64

typedef struct {
  const char *name;
  ixs_interval iv;
} ixs_var_bound;

typedef struct {
  ixs_var_bound vars[IXS_BOUNDS_MAX_VARS];
  size_t nvars;
} ixs_bounds;

void ixs_bounds_init(ixs_bounds *b);
void ixs_bounds_destroy(ixs_bounds *b);

/* Extract variable bounds from an assumption (e.g., $T0 >= 0). */
void ixs_bounds_add_assumption(ixs_bounds *b, ixs_node *assumption);

/* Get the interval for an expression using propagation rules. */
ixs_interval ixs_bounds_get(ixs_bounds *b, ixs_node *expr);

/* An interval representing "no info". */
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

#endif /* IXS_BOUNDS_H */
