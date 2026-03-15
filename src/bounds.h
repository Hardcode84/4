/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXS_BOUNDS_H
#define IXS_BOUNDS_H

#include "node.h"

/*
 * Lightweight interval analysis for bound-dependent rewrites.
 * Stores per-variable intervals extracted from comparison assumptions,
 * and propagates through expression structure.
 *
 * The var table is a growable array on the scratch arena.  Lookup is
 * linear by pointer equality (symbol names are interned).  If this
 * ever becomes a bottleneck, swap the array for an open-addressing
 * hash map keyed on the interned name pointer -- the interface is
 * already designed to make that a drop-in replacement.
 */

typedef struct {
  int64_t lo_p, lo_q; /* lower bound (rational), inclusive */
  int64_t hi_p, hi_q; /* upper bound (rational), inclusive */
  bool valid;
} ixs_interval;

typedef struct {
  const char *name; /* interned pointer -- identity compare only */
  ixs_interval iv;
  int64_t divisor; /* known divisor (0 = no info, >0 = sym is multiple of d) */
} ixs_var_bound;

typedef struct {
  ixs_node *expr; /* expression pointer -- identity compare only */
  ixs_interval iv;
} ixs_expr_bound;

typedef struct {
  ixs_var_bound *vars; /* arena-allocated growable array */
  size_t nvars;
  size_t cap;
  ixs_expr_bound *exprs; /* per-expression overrides from branch conditions */
  size_t nexprs;
  size_t expr_cap;
  ixs_arena *scratch; /* borrowed; must outlive ixs_bounds */
} ixs_bounds;

/* Returns false on OOM (arena exhausted). */
bool ixs_bounds_init(ixs_bounds *b, ixs_arena *scratch);

/* No-op; bounds memory is reclaimed by scratch arena restore. */
void ixs_bounds_destroy(ixs_bounds *b);

/* Deep-copy bounds onto the scratch arena. Returns false on OOM. */
bool ixs_bounds_fork(ixs_bounds *dst, const ixs_bounds *src);

/* Extract variable bounds from an assumption (e.g., $T0 >= 0). */
void ixs_bounds_add_assumption(ixs_bounds *b, ixs_node *assumption);

/* Get the interval for an expression using propagation rules. */
ixs_interval ixs_bounds_get(ixs_bounds *b, ixs_node *expr);

/* Return the known divisor of a symbol (0 if none). */
int64_t ixs_bounds_get_divisor(ixs_bounds *b, const char *name);

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
