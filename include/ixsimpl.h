/*
 * ixsimpl.h -- public API for the index expression simplifier.
 *
 * All nodes are hash-consed and owned by their ixs_ctx.  Nodes from
 * different contexts must never be mixed in the same operation.
 *
 * Error model (three tiers, checked in this order):
 *   NULL         -- out of memory.  Propagates: any op receiving NULL
 *                   returns NULL.
 *   PARSE_ERROR  -- malformed input.  Propagates through arithmetic.
 *   ERROR        -- domain error (e.g. division by zero).  Same.
 * Check with ixs_is_error / ixs_is_parse_error / ixs_is_domain_error.
 * Human-readable messages accumulate in the context error list.
 */

#ifndef IXSIMPL_H
#define IXSIMPL_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef struct ixs_ctx ixs_ctx;
typedef struct ixs_node ixs_node;

typedef enum {
  IXS_CMP_GT,
  IXS_CMP_GE,
  IXS_CMP_LT,
  IXS_CMP_LE,
  IXS_CMP_EQ,
  IXS_CMP_NE
} ixs_cmp_op;

/* --- Context lifecycle ------------------------------------------------- */

/* Create a new context.  Returns NULL on allocation failure. */
ixs_ctx *ixs_ctx_create(void);

/* Destroy ctx and free all nodes allocated within it. */
void ixs_ctx_destroy(ixs_ctx *ctx);

/* --- Error list -------------------------------------------------------- */

/* Number of accumulated error messages. */
size_t ixs_ctx_nerrors(ixs_ctx *ctx);

/* Retrieve the i-th error message (0-based).  Pointer valid until next
 * mutating call on ctx. */
const char *ixs_ctx_error(ixs_ctx *ctx, size_t index);

/* Discard all accumulated errors. */
void ixs_ctx_clear_errors(ixs_ctx *ctx);

/* --- Sentinel checks --------------------------------------------------- */

/* True if node is any sentinel (PARSE_ERROR or ERROR). */
bool ixs_is_error(ixs_node *node);

/* True if node is specifically a parse error sentinel. */
bool ixs_is_parse_error(ixs_node *node);

/* True if node is specifically a domain error sentinel. */
bool ixs_is_domain_error(ixs_node *node);

/* --- Parse ------------------------------------------------------------- */

/* Parse a SymPy-style expression from input[0..len-1].
 * input must be NUL-terminated at or before input[len].
 * Returns the simplified AST, PARSE_ERROR on bad syntax, NULL on OOM. */
ixs_node *ixs_parse(ixs_ctx *ctx, const char *input, size_t len);

/* --- Constructors ------------------------------------------------------ */

/* All constructors return NULL on OOM.  Node arguments must belong to ctx. */

ixs_node *ixs_int(ixs_ctx *ctx, int64_t val);
ixs_node *ixs_rat(ixs_ctx *ctx, int64_t p, int64_t q);
ixs_node *ixs_sym(ixs_ctx *ctx, const char *name);

ixs_node *ixs_add(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_mul(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_neg(ixs_ctx *ctx, ixs_node *a);
ixs_node *ixs_sub(ixs_ctx *ctx, ixs_node *a, ixs_node *b);

/* Exact rational division: a/b where b != 0.  Returns ERROR on b == 0. */
ixs_node *ixs_div(ixs_ctx *ctx, ixs_node *a, ixs_node *b);

ixs_node *ixs_floor(ixs_ctx *ctx, ixs_node *x);
ixs_node *ixs_ceil(ixs_ctx *ctx, ixs_node *x);

/* Floored modulo (Python/SymPy semantics).  Returns ERROR on b == 0. */
ixs_node *ixs_mod(ixs_ctx *ctx, ixs_node *a, ixs_node *b);

ixs_node *ixs_max(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_min(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_xor(ixs_ctx *ctx, ixs_node *a, ixs_node *b);

/* Piecewise: n branches.  values[i] is returned when conds[i] is true;
 * last branch is the default (conds[n-1] should be ixs_true). */
ixs_node *ixs_pw(ixs_ctx *ctx, uint32_t n, ixs_node **values, ixs_node **conds);

ixs_node *ixs_cmp(ixs_ctx *ctx, ixs_node *a, ixs_cmp_op op, ixs_node *b);
ixs_node *ixs_and(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_or(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_not(ixs_ctx *ctx, ixs_node *a);
ixs_node *ixs_true(ixs_ctx *ctx);
ixs_node *ixs_false(ixs_ctx *ctx);

/* --- Simplification ---------------------------------------------------- */

/* Simplify expr under the given assumptions (array of CMP/AND/OR nodes).
 * Pass NULL/0 for no assumptions.  Returns simplified node, or sentinel. */
ixs_node *ixs_simplify(ixs_ctx *ctx, ixs_node *expr,
                       ixs_node *const *assumptions, size_t n_assumptions);

/* Simplify exprs[0..n-1] in place, sharing the same assumption set. */
void ixs_simplify_batch(ixs_ctx *ctx, ixs_node **exprs, size_t n,
                        ixs_node *const *assumptions, size_t n_assumptions);

/* --- Comparison and substitution --------------------------------------- */

/* Pointer equality on hash-consed nodes.  Safe to call with NULL. */
bool ixs_same_node(ixs_node *a, ixs_node *b);

/* Return expr with all occurrences of var replaced by replacement. */
ixs_node *ixs_subs(ixs_ctx *ctx, ixs_node *expr, const char *var,
                   ixs_node *replacement);

/* --- Output ------------------------------------------------------------ */

/* Print in SymPy-compatible syntax.  Returns bytes written (excl. NUL).
 * Output is truncated if bufsize is insufficient. */
size_t ixs_print(ixs_node *expr, char *buf, size_t bufsize);

/* Print in C syntax where possible; falls back to SymPy style. */
size_t ixs_print_c(ixs_node *expr, char *buf, size_t bufsize);

/* --- Introspection ----------------------------------------------------- */

typedef enum {
  IXS_INT,
  IXS_RAT,
  IXS_SYM,
  IXS_ADD,
  IXS_MUL,
  IXS_FLOOR,
  IXS_CEIL,
  IXS_MOD,
  IXS_PIECEWISE,
  IXS_MAX,
  IXS_MIN,
  IXS_XOR,
  IXS_CMP,
  IXS_AND,
  IXS_OR,
  IXS_NOT,
  IXS_TRUE,
  IXS_FALSE,
  IXS_ERROR,
  IXS_PARSE_ERROR
} ixs_tag;

/* Node type tag.  node must not be NULL. */
ixs_tag ixs_node_tag(ixs_node *node);

/* Extract integer value.  Only valid when tag is IXS_INT. */
int64_t ixs_node_int_val(ixs_node *node);

/* Structural hash (deterministic, not an address).  Useful for
 * external hash tables; not guaranteed stable across library versions. */
uint32_t ixs_node_hash(ixs_node *node);

#ifdef __cplusplus
}
#endif

#endif /* IXSIMPL_H */
