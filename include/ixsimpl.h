/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
/*
 * ixsimpl.h -- public API for the index expression simplifier.
 *
 * All nodes are hash-consed and owned by their ixs_ctx.  Nodes from
 * different contexts must never be mixed in the same operation; use
 * ixs_import_node/ixs_import_many as the sanctioned structural bridge,
 * and ixs_serialize_node/ixs_deserialize_node for durable binary
 * interchange.
 *
 * Error model (three tiers, checked in this order):
 *   NULL         -- out of memory.  Propagates: any op receiving NULL
 *                   returns NULL.
 *   PARSE_ERROR  -- malformed input.  Propagates through arithmetic.
 *   ERROR        -- domain error (e.g. division by zero).  Same.
 * Check with ixs_is_error / ixs_is_parse_error / ixs_is_domain_error.
 * Human-readable messages accumulate in the session error list.
 *
 * Node payloads are immutable after interning.  The ixs_node typedef is
 * const-qualified, so every ixs_node pointer is an immutable handle, including
 * constructor results, structural children, transform results, callbacks, and
 * pointer-array elements.
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
typedef const struct ixs_node_impl ixs_node;
typedef struct ixs_facts ixs_facts;

#define IXS_SESSION_BYTES 4096u

typedef union {
  void *ptr_align;
  unsigned char storage[IXS_SESSION_BYTES];
} ixs_session;

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

/* Destroy ctx and free all nodes allocated within it. NULL-safe.
 * Destroy all sessions bound to ctx before calling this. */
void ixs_ctx_destroy(ixs_ctx *ctx);

/* --- Session lifecycle ------------------------------------------------- */

/* `ixs_session` is a reusable workspace bound to exactly one ctx.
 * `s` and `ctx` must be non-NULL. The bound ctx must outlive s. Unless stated
 * otherwise, every API that takes `ixs_session *` requires a non-NULL
 * initialized session. */

/* Initialize a reusable workspace bound to ctx. */
void ixs_session_init(ixs_session *s, ixs_ctx *ctx);

/* Restore scratch to the post-init mark, release owned fact payloads, and
 * clear accumulated errors. Existing fact handles become invalid and fail
 * conservatively. Valid only after successful initialization. */
void ixs_session_reset(ixs_session *s);

/* Destroy s and release owned fact payloads and heap-grown session storage.
 * Existing fact handles become invalid and fail conservatively.
 * Valid only after successful initialization. */
void ixs_session_destroy(ixs_session *s);

/* --- Error list -------------------------------------------------------- */

/* Number of accumulated error messages. */
size_t ixs_session_nerrors(const ixs_session *s);

/* Retrieve the i-th error message (0-based).  Pointer valid until next
 * mutating call on s. */
const char *ixs_session_error(const ixs_session *s, size_t index);

/* Discard all accumulated errors. */
void ixs_session_clear_errors(ixs_session *s);

/* --- Sentinel checks --------------------------------------------------- */

/* True if node is any sentinel (PARSE_ERROR or ERROR). */
bool ixs_is_error(const ixs_node *node);

/* True if node is specifically a parse error sentinel. */
bool ixs_is_parse_error(const ixs_node *node);

/* True if node is specifically a domain error sentinel. */
bool ixs_is_domain_error(const ixs_node *node);

/* --- Parse ------------------------------------------------------------- */

/* Parse a SymPy-style expression from input[0..len-1].
 * input must be NUL-terminated at or before input[len].
 * Legacy convenience wrapper for ixs_parse_expr. Returns the simplified AST,
 * PARSE_ERROR on bad syntax, NULL on OOM. */
const ixs_node *ixs_parse(ixs_session *s, const char *input, size_t len);

/* Kind-aware parse entry points. Wrong top-level kind returns PARSE_ERROR and
 * appends a diagnostic. */
const ixs_node *ixs_parse_expr(ixs_session *s, const char *input, size_t len);
const ixs_node *ixs_parse_pred(ixs_session *s, const char *input, size_t len);

/* Expression/predicate classification for callers that distinguish the two.
 * Sentinels are neither. */
bool ixs_node_is_expr(const ixs_node *node);
bool ixs_node_is_pred(const ixs_node *node);
/* True when expr is structurally guaranteed to be integer-valued.  This
 * conservative query does not use assumptions or fact sets. */
bool ixs_node_is_integer_valued(const ixs_node *expr);

/* --- Constructors ------------------------------------------------------ */

/* All constructors return NULL on OOM.  Node arguments must belong to the
 * context bound to s. */

const ixs_node *ixs_int(ixs_session *s, int64_t val);
const ixs_node *ixs_rat(ixs_session *s, int64_t p, int64_t q);
const ixs_node *ixs_sym(ixs_session *s, const char *name);

const ixs_node *ixs_add(ixs_session *s, const ixs_node *a, const ixs_node *b);
const ixs_node *ixs_mul(ixs_session *s, const ixs_node *a, const ixs_node *b);
const ixs_node *ixs_neg(ixs_session *s, const ixs_node *a);
const ixs_node *ixs_sub(ixs_session *s, const ixs_node *a, const ixs_node *b);

/* Exact rational division: a/b where b != 0.  Returns ERROR on b == 0. */
const ixs_node *ixs_div(ixs_session *s, const ixs_node *a, const ixs_node *b);

const ixs_node *ixs_floor(ixs_session *s, const ixs_node *x);
const ixs_node *ixs_ceil(ixs_session *s, const ixs_node *x);
const ixs_node *ixs_trunc(ixs_session *s, const ixs_node *x);

/* Floored modulo a - b*floor(a/b), defined only for b > 0.
 * Returns ERROR when b is a known nonpositive constant.  A symbolic divisor
 * may be constructed without a positivity proof; assumption-aware
 * simplification returns ERROR when the supplied facts prove b <= 0. */
const ixs_node *ixs_mod(ixs_session *s, const ixs_node *a, const ixs_node *b);

const ixs_node *ixs_max(ixs_session *s, const ixs_node *a, const ixs_node *b);
const ixs_node *ixs_min(ixs_session *s, const ixs_node *a, const ixs_node *b);
const ixs_node *ixs_xor(ixs_session *s, const ixs_node *a, const ixs_node *b);
const ixs_node *ixs_max_many(ixs_session *s, uint32_t n,
                             const ixs_node *const *args);
const ixs_node *ixs_min_many(ixs_session *s, uint32_t n,
                             const ixs_node *const *args);
const ixs_node *ixs_xor_many(ixs_session *s, uint32_t n,
                             const ixs_node *const *args);

/* Piecewise: n branches.  values[i] is returned when conds[i] is true;
 * last branch is the default (conds[n-1] should be ixs_true). */
const ixs_node *ixs_pw(ixs_session *s, uint32_t n,
                       const ixs_node *const *values,
                       const ixs_node *const *conds);

const ixs_node *ixs_cmp(ixs_session *s, const ixs_node *a, ixs_cmp_op op,
                        const ixs_node *b);
const ixs_node *ixs_and(ixs_session *s, const ixs_node *a, const ixs_node *b);
const ixs_node *ixs_or(ixs_session *s, const ixs_node *a, const ixs_node *b);
const ixs_node *ixs_and_many(ixs_session *s, uint32_t n,
                             const ixs_node *const *args);
const ixs_node *ixs_or_many(ixs_session *s, uint32_t n,
                            const ixs_node *const *args);
const ixs_node *ixs_not(ixs_session *s, const ixs_node *a);
/* Convenience names for integer 1 and 0. */
const ixs_node *ixs_true(ixs_session *s);
const ixs_node *ixs_false(ixs_session *s);

/* --- Entailment checking ----------------------------------------------- */

typedef enum {
  IXS_CHECK_TRUE,
  IXS_CHECK_FALSE,
  IXS_CHECK_UNKNOWN
} ixs_check_result;

/* Resource and input status for reusable-fact queries.  COMPLETE means the
 * query ran to a semantic conclusion; its payload may still be UNKNOWN or
 * unavailable when the facts do not prove the requested property.  LIMITED
 * and OOM are retryable without changing the fact set.  INVALID is a hard
 * caller or internal-contract failure and carries a session diagnostic when a
 * live session is available. */
typedef enum {
  IXS_FACT_QUERY_COMPLETE,
  IXS_FACT_QUERY_LIMITED,
  IXS_FACT_QUERY_INVALID,
  IXS_FACT_QUERY_OOM
} ixs_fact_query_status;

typedef struct {
  ixs_fact_query_status status;
  ixs_check_result check;
} ixs_fact_check_result;

typedef struct {
  ixs_fact_query_status status;
  const ixs_node *value;
} ixs_simplify_result;

typedef struct {
  ixs_fact_query_status status;
  bool available;
  int64_t difference;
} ixs_constant_difference_result;

typedef enum {
  IXS_GROUP_UNION_COMPLETE,
  /* The caller-supplied work counter could not reserve the next unit. */
  IXS_GROUP_UNION_EXHAUSTED,
  /* A fixed internal proof traversal or saturation ceiling was reached. */
  IXS_GROUP_UNION_LIMITED,
  IXS_GROUP_UNION_INVALID,
  IXS_GROUP_UNION_OOM
} ixs_group_union_status;

typedef enum {
  IXS_GROUP_UNION_EQUIVALENT,
  IXS_GROUP_UNION_CONSTANT_DIFFERENCE,
  IXS_GROUP_UNION_FINITE_DOMAIN_EQUIVALENT,
  IXS_GROUP_UNION_FINITE_DOMAIN_CONSTANT_DIFFERENCE
} ixs_group_union_query_kind;

typedef struct {
  const ixs_node *const *predicates;
  size_t n_predicates;
} ixs_predicate_group;

typedef struct {
  size_t lhs_group;
  size_t rhs_group;
  ixs_group_union_query_kind kind;
  const ixs_node *lhs;
  const ixs_node *rhs;
} ixs_group_union_query;

typedef struct {
  ixs_check_result status;
  int64_t difference;
} ixs_group_union_result;

typedef enum {
  IXS_FINITE_DOMAIN_EQUIVALENCE,
  IXS_FINITE_DOMAIN_EXPR_RELATION,
  IXS_FINITE_DOMAIN_PRED_RELATION,
  IXS_FINITE_DOMAIN_EXPR_SYNTHESIS,
  IXS_FINITE_DOMAIN_PRED_SYNTHESIS
} ixs_finite_domain_query_kind;

typedef enum {
  IXS_FINITE_DOMAIN_COMPLETE,
  IXS_FINITE_DOMAIN_EXHAUSTED,
  IXS_FINITE_DOMAIN_LIMITED,
  IXS_FINITE_DOMAIN_INVALID,
  IXS_FINITE_DOMAIN_OOM
} ixs_finite_domain_status;

typedef struct {
  const ixs_node *lhs;
  const ixs_node *rhs;
} ixs_finite_domain_equivalence_query;

typedef struct {
  const ixs_node *symbol;
  const int64_t *points;
  const ixs_node *const *values;
  size_t npoints;
} ixs_finite_domain_synthesis_query;

typedef struct {
  const ixs_node *symbol;
  const int64_t *points;
  const ixs_node *const *values;
  size_t npoints;
  const ixs_node *candidate;
} ixs_finite_domain_relation_query;

typedef struct {
  ixs_finite_domain_query_kind kind;
  union {
    ixs_finite_domain_equivalence_query equivalence;
    ixs_finite_domain_relation_query relation;
    ixs_finite_domain_synthesis_query synthesis;
  } as;
} ixs_finite_domain_query;

typedef struct {
  ixs_finite_domain_status status;
  ixs_check_result check;
  const ixs_node *value;
} ixs_finite_domain_result;

/* One exact relation row for mapped scalar-expression synthesis and
 * verification.  Its equation is
 *
 *   expressions[expression_index](symbol := expression_point)
 *       == candidate(symbol := candidate_point) + additive_offset.
 */
typedef struct {
  size_t expression_index;
  int64_t expression_point;
  int64_t candidate_point;
  int64_t additive_offset;
} ixs_mapped_expression_row;

/* One exact scalar-difference row. Its output is
 *
 *   expressions[lhs_expression_index](symbol := lhs_point)
 *       - expressions[rhs_expression_index](symbol := rhs_point).
 */
typedef struct {
  size_t lhs_expression_index;
  int64_t lhs_point;
  size_t rhs_expression_index;
  int64_t rhs_point;
} ixs_mapped_difference_row;

/* One explicitly ordered integer-symbol domain for a finite batch query. */
typedef struct {
  const ixs_node *symbol;
  const int64_t *points;
  size_t npoints;
} ixs_finite_integer_domain;

typedef enum {
  IXS_FINITE_DOMAIN_PREDICATE_TRUE,
  IXS_FINITE_DOMAIN_DEFINED,
  IXS_FINITE_DOMAIN_INTEGER_VALUED
} ixs_finite_domain_batch_query_kind;

/* A typed logical property to check at every point in a Cartesian product.
 * PREDICATE_TRUE requires a predicate node. DEFINED and INTEGER_VALUED
 * accept every expression node, including predicate-valued expressions. */
typedef struct {
  ixs_finite_domain_batch_query_kind kind;
  const ixs_node *value;
} ixs_finite_domain_batch_query;

/* Universal result for one batch query. `witness` is the row-major ordinal of
 * the first point whose result was not TRUE, with the last domain varying
 * fastest. It is SIZE_MAX when every point returned TRUE. */
typedef struct {
  ixs_check_result check;
  size_t witness;
} ixs_finite_domain_batch_result;

/* Signedness of a fixed-width integer remainder. */
typedef enum {
  IXS_REMAINDER_SIGNED,
  IXS_REMAINDER_UNSIGNED
} ixs_remainder_signedness;

typedef enum {
  IXS_MODULO_RECURRENCE_PROVEN,
  IXS_MODULO_RECURRENCE_UNKNOWN,
  IXS_MODULO_RECURRENCE_LIMITED,
  IXS_MODULO_RECURRENCE_INVALID,
  IXS_MODULO_RECURRENCE_OOM
} ixs_modulo_recurrence_status;

/* A proved fixed-width modulo recurrence. `increment` is normalized to
 * [0, divisor), and `remainder` is the exact fixed-width remainder of the
 * supplied induction expression. Both payload fields are meaningful only for
 * PROVEN. */
typedef struct {
  ixs_modulo_recurrence_status status;
  uint64_t increment;
  const ixs_node *remainder;
} ixs_modulo_recurrence_result;

typedef enum {
  IXS_EXACT_DIVIDE_PROVEN,
  IXS_EXACT_DIVIDE_NOT_EXACT,
  IXS_EXACT_DIVIDE_UNKNOWN,
  IXS_EXACT_DIVIDE_LIMITED,
  IXS_EXACT_DIVIDE_INVALID,
  IXS_EXACT_DIVIDE_OOM
} ixs_exact_divide_status;

typedef struct {
  ixs_exact_divide_status status;
  const ixs_node *quotient;
} ixs_exact_divide_result;

typedef enum {
  IXS_POW2_UNKNOWN,
  IXS_POW2_OR_ZERO,
  IXS_POW2_POSITIVE
} ixs_pow2_fact;

/* Sound facts about the low 64 bits of an unbounded integer expression.
 * Zero in both masks is a valid result with no known bits. */
typedef struct {
  uint64_t known_zero;
  uint64_t known_one;
  ixs_pow2_fact pow2;
} ixs_known_bits;

typedef struct {
  ixs_fact_query_status status;
  ixs_pow2_fact fact;
} ixs_pow2_query_result;

typedef struct {
  ixs_fact_query_status status;
  ixs_known_bits bits;
} ixs_known_bits_query_result;

typedef struct {
  bool has_lower;
  bool has_upper;
  int64_t lower_p;
  int64_t lower_q;
  int64_t upper_p;
  int64_t upper_q;
} ixs_range_result;

typedef struct {
  bool has_lower;
  bool has_upper;
  int64_t lower;
  int64_t upper;
} ixs_integer_range_result;

typedef struct {
  ixs_fact_query_status status;
  bool available;
  ixs_range_result range;
} ixs_range_query_result;

typedef struct {
  ixs_fact_query_status status;
  bool available;
  ixs_integer_range_result range;
} ixs_integer_range_query_result;

typedef struct {
  ixs_fact_query_status status;
  bool available;
  int64_t modulus;
  int64_t residue;
} ixs_symbol_congruence_result;

/* Proven decomposition
 *   expr = residual + scale * Mod(symbol + phase, modulus).
 * scale and modulus are positive, modulus is greater than one, and ring is
 * their exactly representable product.  residual is invariant in symbol.
 * residual_bounded reports the additional proof 0 <= residual < scale. */
typedef struct {
  const ixs_node *residual;
  int64_t scale;
  int64_t modulus;
  int64_t phase;
  int64_t ring;
  bool residual_bounded;
} ixs_cyclic_decomposition;

typedef struct {
  ixs_fact_query_status status;
  bool available;
  const ixs_node *coefficient;
  const ixs_node *residual;
} ixs_affine_decomposition_result;

typedef struct {
  ixs_fact_query_status status;
  bool available;
  const ixs_node *numerator;
  const ixs_node *denominator;
} ixs_exact_quotient_result;

typedef struct {
  ixs_fact_query_status status;
  bool available;
  const ixs_node *difference;
} ixs_finite_difference_result;

typedef struct {
  ixs_fact_query_status status;
  bool available;
  ixs_cyclic_decomposition decomposition;
} ixs_cyclic_decomposition_result;

typedef struct {
  ixs_fact_query_status status;
  bool available;
  const ixs_node *residual;
  int64_t constant;
} ixs_additive_constant_result;

/* Exact rational materialization plan returned by the width query.  Numerator
 * and denominator are populated only when status is TRUE.  The denominator
 * is always positive, and the proof does not depend on canonical child order.
 */
typedef struct {
  ixs_fact_query_status status;
  ixs_check_result check;
  const ixs_node *numerator;
  int64_t denominator;
} ixs_rational_materialization_plan;

/* Assumption contract shared by simplify, simplify_batch, check,
 * check_integer_valued, check_defined, get_pow2_fact, range, integer_range, and
 * facts_assume_pred: each predicate root must be a CMP, a canonical true/false
 * node, or an AND tree whose leaves have those forms.  True contributes no
 * fact; false marks the set contradictory.  Trees are walked iteratively and
 * may contain at most 1024 visited nodes per root.  NULL, sentinel, malformed,
 * cross-context, OR, NOT, and other roots are rejected with an "assumptions:"
 * session diagnostic; no prefix of a rejected set is used.  A rejected set
 * makes simplify return the domain-error sentinel, makes simplify_batch set
 * every element to that sentinel, makes query APIs return unknown/no-result,
 * and leaves an existing fact set unchanged. */

/* Check whether a comparison is provably true or false given the
 * assumptions, using interval propagation, modular congruence facts, and
 * bitwise facts.  expr must be a CMP node in normalized form (lhs op 0), or
 * the canonical true/false node produced when a smart constructor resolves a
 * comparison.  CMP normalization is automatic through ixs_cmp().  Returns
 * UNKNOWN when bounds are insufficient, when expr has another form, or on
 * OOM.  Lighter than ixs_simplify: no rewriting, just bounds setup and
 * entailment checks. */
ixs_check_result ixs_check(ixs_session *s, const ixs_node *expr,
                           const ixs_node *const *assumptions,
                           size_t n_assumptions);

/* Prove whether expr is integer-valued under assumptions.  TRUE and FALSE are
 * returned only for universal proofs; insufficient information, invalid input,
 * contradictory assumptions, and OOM return UNKNOWN. */
ixs_check_result ixs_check_integer_valued(ixs_session *s, const ixs_node *expr,
                                          const ixs_node *const *assumptions,
                                          size_t n_assumptions);

/* Prove whether expr is defined over the full domain admitted by assumptions.
 * Negative powers require nonzero bases and Mod requires a positive divisor.
 * Piecewise uses first-match semantics and requires defined conditions and
 * complete coverage.  FALSE is returned only when every feasible valuation is
 * necessarily undefined; mixed domains, insufficient facts, invalid input,
 * contradictory assumptions, bounded-traversal limits, and OOM return
 * UNKNOWN. */
ixs_check_result ixs_check_defined(ixs_session *s, const ixs_node *expr,
                                   const ixs_node *const *assumptions,
                                   size_t n_assumptions);

/* Return the strongest known power-of-two fact for expr under assumptions.
 * POSITIVE means expr > 0 and exactly one bit is set.  OR_ZERO additionally
 * permits expr == 0.  UNKNOWN is returned when the fact is not provable, on
 * OOM, for NULL/sentinel expr, or for detected contradictory assumptions. */
ixs_pow2_fact ixs_get_pow2_fact(ixs_session *s, const ixs_node *expr,
                                const ixs_node *const *assumptions,
                                size_t n_assumptions);

/* Infer an inclusive rational range for expr under assumptions. Propagation
 * includes bounded integer powers, sound nonnegative XOR, and first-match
 * Piecewise branch hulls; unsupported domains remain unknown.
 * Returns false when the interval engine cannot derive a range, on OOM,
 * for NULL/sentinel expr, or when out is NULL.  Unbounded sides are reported
 * with has_lower/has_upper false; finite endpoints are exact p/q rationals. */
bool ixs_range(ixs_session *s, const ixs_node *expr,
               const ixs_node *const *assumptions, size_t n_assumptions,
               ixs_range_result *out);

/* Infer an inclusive integer range for expr under assumptions.  The query
 * first proves expr defined and integer-valued over the complete assumption
 * domain, then rounds rational interval bounds inward and applies any
 * structural congruence known by the bounds engine.  Unbounded sides are
 * reported with has_lower/has_upper false.  Failure leaves out initialized to
 * the no-information value. */
bool ixs_integer_range(ixs_session *s, const ixs_node *expr,
                       const ixs_node *const *assumptions, size_t n_assumptions,
                       ixs_integer_range_result *out);

/* --- Fact sets --------------------------------------------------------- */

/* Create a session-owned fact set.  The handle storage remains valid until
 * ctx destruction, but reset or destruction of its session invalidates the
 * proof payload.  Calls through an invalidated handle fail conservatively.
 * Fact sets are mutable and bound to the session/context that created them. */
ixs_facts *ixs_facts_create(ixs_session *s);

/* Create a fact set by directly ingesting one exact assumption domain.
 * Predicates do not simplify against earlier predicates. n_preds == 0 accepts
 * a NULL array. Invalid input or OOM returns NULL without exposing a partial
 * fact set. This low-level compatibility constructor is intentionally C-only;
 * C++ and Python Facts retain their sequential mutation contract. */
ixs_facts *ixs_facts_create_preds(ixs_session *s, const ixs_node *const *preds,
                                  size_t n_preds);

/* Every mutator returns false on rejection or failure and makes facts
 * unusable for subsequent proof queries.  The stored payload is committed
 * only after a complete successful mutation, so no partial weaker context is
 * observable. */

/* Import one closed predicate domain under one transaction. Every predicate
 * must be provably defined after batch saturation. n == 0 accepts NULL. */
bool ixs_facts_assume_preds(ixs_facts *facts, const ixs_node *const *preds,
                            size_t n_preds);

/* Import one predicate for incremental fact construction. Unlike the batch
 * form, this permits a later predicate to close the expression domain. */
bool ixs_facts_assume_pred(ixs_facts *facts, const ixs_node *pred);

/* Attach an explicit inclusive range to expr.  Missing endpoints are allowed;
 * finite endpoints are exact rationals from ixs_range_result. */
bool ixs_facts_assume_range(ixs_facts *facts, const ixs_node *expr,
                            const ixs_range_result *range);

/* Derive range(derived) from range(base) using derived = scale*base + offset.
 * The caller supplies the already-built derived expression node. */
bool ixs_facts_derive_affine(ixs_facts *facts, const ixs_node *base,
                             int64_t scale, int64_t offset,
                             const ixs_node *derived);

/* Merge facts from src into dst after one simultaneous substitution.  Facts
 * unrelated to target are preserved; facts about target are transferred only
 * when justified by replacement.  Both sets must belong to the same live
 * session. */
bool ixs_facts_substitute(ixs_facts *dst, const ixs_facts *src,
                          const ixs_node *target, const ixs_node *replacement);

/* Multi-target form of ixs_facts_substitute.  Substitution is simultaneous:
 * replacements are not recursively substituted.  When a target occurs more
 * than once, its first entry wins, matching ixs_subs_multi.  nsubs == 0 accepts
 * NULL arrays and merges src unchanged.  dst may equal src; in that case the
 * original facts remain as pre-existing destination facts and transformed
 * facts are added.  Any failure leaves dst's prior facts intact but marks dst
 * unusable, so callers can never observe a partially transferred set. */
bool ixs_facts_substitute_multi(ixs_facts *dst, const ixs_facts *src,
                                uint32_t nsubs, const ixs_node *const *targets,
                                const ixs_node *const *replacements);

/* Simplify directly against an existing fact set without rebuilding bounds.
 * value is populated only for COMPLETE.  A fixed internal work ceiling is
 * LIMITED, malformed or foreign input is INVALID, and allocation failure is
 * OOM. Detected contradictory facts return COMPLETE with expr unchanged. */
ixs_simplify_result ixs_simplify_facts(ixs_facts *facts, const ixs_node *expr);

/* Fact-backed batch simplification.  The operation is transactional: entries
 * are replaced only for COMPLETE and remain unchanged for LIMITED, INVALID,
 * or OOM.  NULL and sentinel entries are invalid input.  Detected
 * contradictory facts return COMPLETE with every entry unchanged. */
ixs_fact_query_status
ixs_simplify_batch_facts(ixs_facts *facts, const ixs_node **exprs, size_t n);

/* Reusable-fact form of ixs_check with the same CMP or canonical
 * true/false input contract. */
ixs_fact_check_result ixs_check_facts(ixs_facts *facts, const ixs_node *expr);
/* Check a predicate tree against an existing fact set.  AND, OR, and NOT use
 * conservative three-valued logic.  Numeric bitwise AND/OR expressions are
 * rejected because they are not predicate trees. */
ixs_fact_check_result ixs_check_predicate_facts(ixs_facts *facts,
                                                const ixs_node *predicate);
/* Report whether the reusable fact domain is nonempty.  TRUE means no
 * contradiction detectable by the fact engine, FALSE means a detected empty
 * domain, and UNKNOWN means the fact set is invalid, expired, or exhausted. */
ixs_fact_check_result ixs_check_consistent_facts(ixs_facts *facts);
/* Prove total equivalence over the full domain admitted by facts.  TRUE is
 * returned only after both operands are proved defined everywhere.  FALSE is
 * returned only for a universal proof of different values; insufficient
 * facts, contradictory facts, invalid input, and resource limits return
 * UNKNOWN. */
ixs_fact_check_result ixs_equivalent_facts(ixs_facts *facts,
                                           const ixs_node *lhs,
                                           const ixs_node *rhs);
/* Prove total equivalence modulo 2^bits.  Both operands must be defined and
 * integer-valued over the complete fact domain.  bits must be at most 63;
 * invalid widths emit a diagnostic and return UNKNOWN.  The proof propagates
 * only through operations that preserve the requested low bits. */
ixs_fact_check_result ixs_equivalent_modulo_pow2_facts(ixs_facts *facts,
                                                       const ixs_node *lhs,
                                                       const ixs_node *rhs,
                                                       unsigned bits);
/* Run one bounded finite-domain query. Equivalence first uses the ordinary
 * proof engine, then enumerates the finite integer ranges still present in
 * lhs-rhs. Relation queries exhaustively verify one typed candidate against an
 * ordered table over an explicit contiguous point domain. Synthesis accepts
 * any strictly increasing point table, including sparse and non-power-of-two
 * domains, and returns one typed expression or predicate that is exhaustively
 * proved equal to every supplied sample. Expression synthesis composes additive
 * and XOR base deltas with additive or XOR bit contributions, grouping doubled
 * coefficients into integer fields and extending coefficients across sparse
 * missing basis points. Dense power-of-two tables also use the legacy additive
 * integer-difference and GF(2) output-bit recognizers. Predicate synthesis
 * iteratively preserves CMP, NOT, AND, and OR shape. Unsupported tables return
 * COMPLETE with UNKNOWN and a NULL value. Expression modes treat every
 * predicate-valued node, including predicate-valued Piecewise, as its numeric
 * scalar 0/1 value; predicate modes additionally require and preserve the
 * predicate contract. Relation and synthesis queries never return FALSE. Scalar
 * headers (kind, handles, non-NULL arrays, count, and allocation size) are
 * checked before the budget. An
 * insufficient budget then returns EXHAUSTED without reading either table;
 * with enough budget, point ordering is checked before value handles. All
 * finite work is charged atomically to *remaining_work and failed reserved
 * work is not refunded. Direct equivalence proofs, invalid table headers, and
 * over-budget queries leave the budget unchanged. Synthesis reserves its top
 * table before query-state allocation or sample specialization; nested
 * predicate children reserve when their table is entered. Internal proof
 * ceilings return LIMITED; malformed input returns INVALID; allocation
 * failure returns OOM. `check` and `value` are meaningful only on COMPLETE.
 * Every non-COMPLETE result resets them to UNKNOWN and NULL. */
ixs_finite_domain_result
ixs_finite_domain_facts(ixs_facts *facts, const ixs_finite_domain_query *query,
                        size_t *remaining_work);
/* Synthesize one scalar candidate over an explicit candidate-point image from
 * mapped rows. `symbol` must be a symbol; every expression may be any scalar
 * expression, including a predicate-valued 0/1 expression. Candidate points
 * must be nonempty, strictly increasing, and unique. Rows must be nonempty but
 * may use any caller order; they are never reordered, and repeated candidate
 * points or identical redundant rows are accepted. Every row candidate point
 * must occur in candidate_points, and every candidate point must have at least
 * one row. The first row in caller order for each candidate point supplies
 * both its representative value and the direct symbolic candidate
 *
 *   expressions[expression_index](
 *       symbol := symbol + expression_point - candidate_point)
 *           - additive_offset.
 *
 * When those per-point candidates are equivalent under the facts and the
 * common candidate verifies every representative value, synthesis returns that
 * globally reparameterized expression. A complete direct attempt that does not
 * prove one first tries structural predicate synthesis when every
 * representative is predicate-valued, then falls back to ordinary scalar
 * finite-table synthesis if that predicate attempt completes without a
 * candidate. OOM, LIMITED, and nested EXHAUSTED propagate without fallback. The
 * remaining rows are intentionally not reverified here; use
 * ixs_verify_mapped_expression_facts for the universal relation proof.
 *
 * The mapped table reserves ncandidate_points + nrows before reading any input
 * array: one unit for every candidate representative and every caller row. This
 * is 2 * ncandidate_points when there is exactly one row per point, while each
 * accepted duplicate row is charged once. Structural predicate fallback may
 * then reserve another
 * 2 * ncandidate_points for every child table it enters; for example, a
 * comparison costs nrows + 5 * ncandidate_points in total, or 6 *
 * ncandidate_points with one row per point. Predicate fallback that completes
 * without a candidate continues to scalar finite-table synthesis without
 * another reservation, preserving numeric 0/1 behavior. Scalar handles,
 * pointers, counts, and checked base work size are validated before the base
 * reservation. An insufficient base budget returns EXHAUSTED without reading
 * any input array. With sufficient base work, arrays are fully validated before
 * it is atomically deducted, so INVALID and validation OOM leave the budget
 * unchanged. OOM, LIMITED, or nested EXHAUSTED after a reservation keeps all
 * work already deducted. COMPLETE with TRUE is the only result carrying a
 * non-NULL value; COMPLETE with UNKNOWN means synthesis was unsupported. */
ixs_finite_domain_result ixs_synthesize_mapped_expression_facts(
    ixs_facts *facts, const ixs_node *symbol,
    const ixs_node *const *expressions, size_t nexpressions,
    const int64_t *candidate_points, size_t ncandidate_points,
    const ixs_mapped_expression_row *rows, size_t nrows,
    size_t *remaining_work);
/* Universally verify every mapped row against one scalar candidate using the
 * equation documented on ixs_mapped_expression_row. Predicate-valued
 * expressions and candidates are numeric scalar 0/1 values. Rows are checked
 * in caller order without sorting. Work is exactly nrows with the same
 * precharge EXHAUSTED/INVALID and post-reservation OOM/LIMITED semantics. Every
 * row specializes both sides and proves them defined and equal. TRUE is
 * returned only when all rows are proved; a mismatch or insufficient facts is
 * COMPLETE with UNKNOWN. This query never returns FALSE or a value. */
ixs_finite_domain_result ixs_verify_mapped_expression_facts(
    ixs_facts *facts, const ixs_node *symbol,
    const ixs_node *const *expressions, size_t nexpressions,
    const ixs_mapped_expression_row *rows, size_t nrows,
    const ixs_node *candidate, size_t *remaining_work);
/* Prove one exactly representable signed integer constant difference for every
 * mapped row, preserving caller order. Every expression may be any scalar
 * expression, including a predicate-valued 0/1 expression. Work is exactly
 * nrows. Scalar handles, pointers, counts, and checked work size are validated
 * before the budget; an insufficient budget returns EXHAUSTED without reading
 * any input or output array. With enough work, all expression handles and row
 * indices are validated before work is deducted, so INVALID leaves the budget
 * and output untouched. OOM or LIMITED after reservation keeps the charge.
 *
 * COMPLETE with TRUE atomically copies all row differences to `differences`.
 * COMPLETE with UNKNOWN means at least one difference was not proved and
 * leaves the entire output array unchanged. Every non-COMPLETE result likewise
 * leaves output untouched, resets `check` to UNKNOWN, and carries no value. */
ixs_finite_domain_result ixs_mapped_constant_differences_facts(
    ixs_facts *facts, const ixs_node *symbol,
    const ixs_node *const *expressions, size_t nexpressions,
    const ixs_mapped_difference_row *rows, size_t nrows, int64_t *differences,
    size_t *remaining_work);
/* Check a typed batch of logical properties over one explicit Cartesian
 * product of ordered integer-symbol domains. Each domain point table must be
 * nonempty and strictly increasing, and domain symbols must be distinct. The
 * product is visited in row-major order with the last domain varying fastest.
 * Every query is evaluated under `facts` after simultaneous substitution of
 * the current point. Per-query truth is universal: FALSE dominates UNKNOWN,
 * and `witness` still records that query's first non-TRUE point.
 *
 * Work is the checked product of the Cartesian point count and query count.
 * Invalid scalar sizes and multiplication overflow are rejected before the
 * budget or arrays are accessed. Insufficient work returns EXHAUSTED without
 * reading point or query arrays. After complete validation, work is reserved
 * atomically before evaluation and is not refunded on OOM or an internal
 * traversal ceiling. Invalid input leaves the budget unchanged. Once a
 * non-NULL result array has a representable nonzero count, every payload is
 * initialized to UNKNOWN and SIZE_MAX before any remaining validation, and is
 * meaningful only on COMPLETE. A detected contradictory fact domain returns
 * COMPLETE with every check UNKNOWN and every witness SIZE_MAX; no point is
 * evaluated and no work is reserved. */
ixs_finite_domain_status ixs_finite_domain_batch_facts(
    ixs_facts *facts, const ixs_finite_integer_domain *domains, size_t ndomains,
    const ixs_finite_domain_batch_query *queries, size_t nqueries,
    ixs_finite_domain_batch_result *results, size_t *remaining_work);
/* Prove that lhs - rhs is an exactly representable integer constant.  The
 * operands must be defined over the complete fact domain. */
ixs_constant_difference_result
ixs_constant_difference_facts(ixs_facts *facts, const ixs_node *lhs,
                              const ixs_node *rhs);
/* Prove and construct one fixed-width modulo recurrence. `value`, `reference`,
 * and `induction` are scalar signed-view fixed-width integer expressions.
 * Predicate-valued nodes participate as their canonical integer 0/1 values.
 * The closed fact domain must prove all three defined and integer-valued.
 * Signed recurrence operands must additionally be nonnegative so their
 * truncating remainders agree with the normalized Euclidean carry. Unsigned
 * recurrence differences are interpreted after projecting each operand modulo
 * 2^width and must have one invariant residue modulo divisor over the complete
 * fact domain. A raw algebraic difference alone is insufficient unless
 * whole-width wraps have zero residue or their quotient difference is also
 * proved.
 *
 * width must be in [1, 64]. divisor must be a nonzero width-bit unsigned
 * value; for SIGNED it must also be representable as a positive signed
 * width-bit value. PROVEN is the only status carrying payload. Insufficient
 * facts or an unsupported proof return UNKNOWN. A retryable internal proof
 * stop returns LIMITED. Malformed/cross-context input returns INVALID and
 * appends a diagnostic when a live session is available; allocation failure
 * returns OOM. */
ixs_modulo_recurrence_result ixs_modulo_recurrence_facts(
    ixs_facts *facts, const ixs_node *value, const ixs_node *reference,
    const ixs_node *induction, ixs_remainder_signedness signedness,
    unsigned width, uint64_t divisor);
/* Answer many equivalence, finite-domain equivalence, and constant-difference
 * queries under exact unions of closed predicate groups. Query (i, j) has
 * precisely the batch-saturated set union of groups i and j: predicates from
 * every other group are absent. Operands must be scalar expressions;
 * predicate-valued nodes participate as their canonical integer 0/1 values.
 * Equivalence queries may return TRUE, FALSE, or UNKNOWN. Finite-domain
 * queries first use the corresponding exact proof and only spend the caller's
 * work budget enumerating selected-domain integer points when it is unknown.
 * Finite-domain constant difference requires the same signed int64 lhs-rhs
 * value at every point. Constant-difference queries return TRUE with
 * difference populated, or UNKNOWN; they never return FALSE. A contradictory
 * selected union returns UNKNOWN without contaminating any other union.
 *
 * The implementation shares the all-group intersection and each individual
 * group closure, then transiently saturates each distinct selected union.
 * There is no persistent fact domain per group pair. After complete input
 * validation, a nonempty query batch with zero budget returns EXHAUSTED before
 * planning or structural admission. Invalid input and validation OOM
 * therefore take precedence over zero-budget exhaustion.
 *
 * Before constructing closures, an uncharged structural scan estimates
 * nonlinear batch work. One iterative memo computes the expanded subtree cost
 * of every reachable node once, with extra weight for rounding and Piecewise;
 * each predicate root contributes once and every query operand use
 * contributes. Estimates at or below 65536 leave the ordinary work counter
 * authoritative.
 * Above that floor, an estimate exceeding *remaining_work, or one that cannot
 * be represented in size_t, returns EXHAUSTED, sets *remaining_work to zero,
 * and constructs no closure. Successful admission does not deduct the
 * estimate.
 *
 * Runtime work remains exact: one work unit is one predicate-root replay or
 * one internally bounded semantic query. Every runtime reservation is
 * deducted from *remaining_work before that work starts. Replay-support
 * scratch is allocated only after its reservation succeeds; a failed
 * allocation does not refund reserved work.
 * Insufficient work, an internal traversal limit, invalid input, and OOM are
 * reported as EXHAUSTED, LIMITED, INVALID, and OOM respectively. Results are
 * meaningful only on COMPLETE. After scalar array sizes are validated, every
 * non-COMPLETE return resets all results to UNKNOWN/zero. An unrepresentable
 * result count returns INVALID without touching the result pointer. A zero
 * count accepts a NULL array for its corresponding groups or queries/results.
 */
ixs_group_union_status
ixs_query_group_unions(ixs_session *s, const ixs_predicate_group *groups,
                       size_t n_groups, const ixs_group_union_query *queries,
                       size_t n_queries, ixs_group_union_result *results,
                       size_t *remaining_work);
/* Decompose expr as coefficient*symbol + residual.  The coefficient is an
 * exact rational constant and residual does not reference symbol. */
ixs_affine_decomposition_result
ixs_affine_decompose_facts(ixs_facts *facts, const ixs_node *expr,
                           const ixs_node *symbol);
/* Decompose a rational product or common-denominator sum exactly after
 * simplifying under facts.  This does not prove integer-valued parts or a
 * nonzero denominator. */
ixs_exact_quotient_result
ixs_decompose_exact_quotient_facts(ixs_facts *facts, const ixs_node *expr);
/* Construct expr[symbol -> symbol + step] - expr exactly.  The result may
 * still reference symbol; callers decide whether it is loop invariant. */
ixs_finite_difference_result ixs_finite_difference_facts(ixs_facts *facts,
                                                         const ixs_node *expr,
                                                         const ixs_node *symbol,
                                                         const ixs_node *step);
/* Prove expr[symbol -> symbol + step] == expr.  symbol must be a symbol.  A
 * step that references symbol is valid but unsupported and returns COMPLETE
 * with UNKNOWN.  The complete fact domain must prove expr, step, and the
 * shifted expression defined.  COMPLETE carries TRUE, FALSE, or UNKNOWN;
 * LIMITED and OOM are retryable and INVALID reports malformed or cross-context
 * input. */
ixs_fact_check_result
ixs_check_invariant_under_step_facts(ixs_facts *facts, const ixs_node *expr,
                                     const ixs_node *symbol,
                                     const ixs_node *step);
/* Recognize a direct Mod, a positive integral scalar multiple of Mod, or one
 * such term in an ADD.  The Mod dividend must be symbol plus an exactly
 * representable integer phase.  The exact residual must be defined,
 * integer-valued, and invariant in symbol over the complete fact domain.
 * residual_bounded is true only when facts also prove
 * 0 <= residual < scale.  Loop step and target carry policy are not part of
 * this query. */
ixs_cyclic_decomposition_result
ixs_decompose_cyclic_facts(ixs_facts *facts, const ixs_node *expr,
                           const ixs_node *symbol);
/* Split expr into residual + constant with an exactly representable integer
 * constant. */
ixs_additive_constant_result
ixs_split_additive_constant_facts(ixs_facts *facts, const ixs_node *expr);
ixs_fact_check_result ixs_check_integer_valued_facts(ixs_facts *facts,
                                                     const ixs_node *expr);
ixs_fact_check_result ixs_check_defined_facts(ixs_facts *facts,
                                              const ixs_node *expr);
/* Check divisibility by a nonzero signed modulus.  Negative moduli are
 * normalized by magnitude without overflowing INT64_MIN.  Modulus zero emits
 * a session diagnostic and returns UNKNOWN. */
ixs_fact_check_result ixs_check_divisible_facts(ixs_facts *facts,
                                                const ixs_node *expr,
                                                int64_t modulus);
/* Prove exact divisibility and construct the simplified quotient.  PROVEN is
 * the only status with a non-NULL quotient.  NOT_EXACT is a proof of
 * nondivisibility; UNKNOWN means facts are insufficient, contradictory, or do
 * not prove the input defined.  LIMITED is a retryable proof-resource stop;
 * invalid input, divisor zero, or an invalid constructed result returns
 * INVALID; allocation failure returns OOM.  INVALID and OOM append a
 * diagnostic to the fact set's session when one is available. */
ixs_exact_divide_result ixs_try_exact_divide_facts(ixs_facts *facts,
                                                   const ixs_node *expr,
                                                   int64_t divisor);
ixs_pow2_query_result ixs_get_pow2_fact_facts(ixs_facts *facts,
                                              const ixs_node *expr);
/* Return sound low-64-bit facts.  COMPLETE with zero masks means that the
 * query was valid but proved no bits.  LIMITED is a retryable proof-resource
 * stop.  INVALID and OOM return the no-information payload. */
ixs_known_bits_query_result ixs_get_known_bits_facts(ixs_facts *facts,
                                                     const ixs_node *expr);
/* Export the stored congruence record for a symbol.  Output pointers must be
 * non-NULL and distinct.  This deliberately does not synthesize a strongest
 * congruence for arbitrary expressions. */
ixs_symbol_congruence_result
ixs_get_symbol_congruence_facts(ixs_facts *facts, const ixs_node *symbol);
/* Prove expr == residue (mod modulus).  Negative moduli are normalized by
 * magnitude without overflowing INT64_MIN.  Modulus zero emits a diagnostic
 * and returns UNKNOWN. */
ixs_fact_check_result ixs_check_congruent_facts(ixs_facts *facts,
                                                const ixs_node *expr,
                                                int64_t modulus,
                                                int64_t residue);
ixs_range_query_result ixs_range_facts(ixs_facts *facts, const ixs_node *expr);
/* Reusable-fact form of ixs_integer_range. */
ixs_integer_range_query_result ixs_integer_range_facts(ixs_facts *facts,
                                                       const ixs_node *expr);

/* Prove that every arithmetic intermediate introduced while materializing the
 * rational islands of expr fits one machine word.  ADD and Piecewise choose
 * their full common denominator before scaling operands.  ADD and MUL then use
 * order-independent subset envelopes for partial sums and products, including
 * partial powers.  The query also checks Floor/Ceil/Trunc source numerators and
 * selected rounding biases, Piecewise conditions and value arms, and integral
 * Mod/bitwise operands. A static rounded denominator larger than the unsigned
 * word selects the compare/zero path and needs no bias; every other nonunit
 * denominator validates its denominator-minus-one bias. word_bits must be in
 * [2, 64]. For N < 64 the ordinary word domain is
 * [-2^(N-1), 2^N-1], while signed rounded intermediates additionally use
 * [-2^(N-1), 2^(N-1)-1].  N == 64 uses the exact signed-int64 domain because
 * public range endpoints are int64 values.  TRUE is a complete full-domain
 * proof.  FALSE is returned only for a conclusive out-of-range intermediate.
 * A semantic proof failure without such a witness returns COMPLETE with
 * UNKNOWN, including an inconclusive envelope, unsupported or malformed
 * structure, an unrepresentable exact denominator, missing
 * totality/integrality facts, or contradictory facts.  A detected cycle or
 * invalid internal relation returns INVALID; allocation-size overflow or OOM
 * returns OOM; a retryable proof-resource stop returns LIMITED.  Every
 * non-COMPLETE status clears the check payload to UNKNOWN.  The planner uses
 * growable arena-backed iterative state and imposes no fixed traversal depth,
 * visit count, Piecewise case count, or exponent cap. */
ixs_fact_check_result
ixs_check_rational_intermediates_facts(ixs_facts *facts, const ixs_node *expr,
                                       uint32_t word_bits);

/* Return the exact numerator and denominator authorized by the
 * order-independent width proof above.  TRUE is the only status with a
 * non-NULL numerator and positive denominator.  FALSE is a conclusive width
 * failure.  COMPLETE with UNKNOWN covers unsupported or malformed structure,
 * an unrepresentable exact denominator, and insufficient or contradictory
 * facts.  Invalid input or a detected cycle returns INVALID,
 * allocation-size overflow or OOM returns OOM, and a retryable proof-resource
 * stop returns LIMITED.  Every non-COMPLETE status clears the plan.  The
 * returned node belongs to the fact set's context. */
ixs_rational_materialization_plan
ixs_plan_rational_materialization_facts(ixs_facts *facts, const ixs_node *expr,
                                        uint32_t word_bits);

/* --- Simplification ---------------------------------------------------- */

/* Simplify expr under the shared assumption contract above.  Pass NULL/0 for
 * no assumptions.  Returns the simplified node, NULL on OOM, or the
 * domain-error sentinel for rejected assumptions. */
const ixs_node *ixs_simplify(ixs_session *s, const ixs_node *expr,
                             const ixs_node *const *assumptions,
                             size_t n_assumptions);

/* Simplify exprs[0..n-1] in place under the shared assumption contract,
 * sharing the same assumption set and rewritten-subtree cache.  Both are
 * scoped to this call and fact context.
 * Each element is replaced by its simplified form.  On OOM, all
 * elements are set to NULL.  NULL or sentinel entries are skipped.
 * Bounds are parsed from assumptions once and reused across all elements. */
void ixs_simplify_batch(ixs_session *s, const ixs_node **exprs, size_t n,
                        const ixs_node *const *assumptions,
                        size_t n_assumptions);

/* Distribute MUL over ADD (expand products of sums into sums of products).
 * Recurses into subexpressions (floor args, piecewise branches, etc.).
 * Positive powers use exponentiation by squaring. Negative powers retain their
 * exact signed int32 exponent. There is no traversal-depth or exponent cap.
 * NULL-safe. */
const ixs_node *ixs_expand(ixs_session *s, const ixs_node *expr);

/* --- Comparison and substitution --------------------------------------- */

/* Pointer equality on hash-consed nodes.  Safe to call with NULL. */
bool ixs_same_node(const ixs_node *a, const ixs_node *b);

/* Return expr with all occurrences of target replaced by replacement.
 * target can be any node (symbol, subexpression, constant, etc.).
 * Uses pointer equality (hash-consed), so matching is O(1) per node. */
const ixs_node *ixs_subs(ixs_session *s, const ixs_node *expr,
                         const ixs_node *target, const ixs_node *replacement);

/* Simultaneous multi-target substitution.  Replaces targets[i] with
 * replacements[i] in a single pass.  No replacement is recursed into,
 * so {A->B, B->C} applied to A+B yields B+C, not C+C.
 * Duplicate targets: first matching entry wins. */
const ixs_node *ixs_subs_multi(ixs_session *s, const ixs_node *expr,
                               uint32_t nsubs, const ixs_node *const *targets,
                               const ixs_node *const *replacements);

/* --- Structural import ------------------------------------------------- */

/* Import src structurally into the store bound to s.  Destination hash-consing
 * may reuse existing nodes, including for same-store input, but import always
 * follows the structural path.  Sentinels are mapped to the destination
 * store's sentinels.  Returns NULL on OOM or if src is NULL. */
const ixs_node *ixs_import_node(ixs_session *s, const ixs_node *src);

/* Import src[0..count-1] into the store bound to s.  count == 0 is a no-op
 * that returns true and permits src == NULL and out == NULL.  Otherwise NULL
 * src/out pointers or NULL elements fail.  If it returns false, out is left
 * unchanged, but nodes interned before the failure may remain in the
 * destination store. */
bool ixs_import_many(ixs_session *s, const ixs_node *const *src, size_t count,
                     const ixs_node **out);

/* --- Structural serialization ----------------------------------------- */

/* Writer/read callbacks are all-or-nothing: they must consume exactly len
 * bytes or report failure. */
typedef bool (*ixs_writer_write_fn)(void *userdata, const void *buf,
                                    size_t len);
typedef bool (*ixs_reader_read_fn)(void *userdata, void *buf, size_t len);
typedef size_t (*ixs_reader_remaining_fn)(void *userdata);

typedef struct {
  ixs_writer_write_fn write;
  void *userdata;
} ixs_writer;

typedef struct {
  ixs_reader_read_fn read;
  ixs_reader_remaining_fn remaining;
  void *userdata;
} ixs_reader;

/* Serialize root to w using a stable little-endian binary format.  s supplies
 * scratch only; root may belong to any context.  Returns false on writer
 * failure, OOM, or codec validation failure (for example NULL root or an
 * unencodable internal payload).  Validation failures append session
 * diagnostics; writer failure and OOM leave diagnostics unchanged. */
bool ixs_serialize_node(ixs_session *s, const ixs_node *root,
                        const ixs_writer *w);

/* Deserialize one node from r into the store bound to s.  r->remaining must
 * report the exact unread byte count.  Returns the node on success,
 * the destination store's IXS_PARSE_ERROR sentinel on malformed or unsupported
 * binary (including streams that exceed implementation resource limits), and
 * NULL on OOM.  Malformed input appends session diagnostics, is validated in
 * session scratch, and does not intern garbage into the destination store.
 * OOM leaves diagnostics unchanged but may occur after some validated nodes
 * have already been interned. */
const ixs_node *ixs_deserialize_node(ixs_session *s, const ixs_reader *r);

/* --- Output ------------------------------------------------------------ */

/* Print in SymPy-compatible syntax.  Returns bytes written (excl. NUL).
 * Output is truncated if bufsize is insufficient. */
size_t ixs_print(const ixs_node *expr, char *buf, size_t bufsize);

/* Print in C syntax where possible; falls back to SymPy style. */
size_t ixs_print_c(const ixs_node *expr, char *buf, size_t bufsize);

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
  IXS_ERROR,
  IXS_PARSE_ERROR,
  IXS_TRUNC
} ixs_tag;

/* All introspection functions require a non-NULL node. */

ixs_tag ixs_node_tag(const ixs_node *node);

/* Only valid when tag is IXS_INT. */
int64_t ixs_node_int_val(const ixs_node *node);

/* Structural hash (deterministic, not an address).  Useful for
 * external hash tables; not guaranteed stable across library versions. */
uint32_t ixs_node_hash(const ixs_node *node);

/* Only valid when tag is IXS_RAT. */
int64_t ixs_node_rat_num(const ixs_node *node);
int64_t ixs_node_rat_den(const ixs_node *node);

/* Only valid when tag is IXS_SYM.  Pointer valid for ctx lifetime. */
const char *ixs_node_sym_name(const ixs_node *node);

/* Only valid when tag is IXS_ADD.  i must be < nterms.
 * ADD = coeff + sum(term_coeff[i] * term[i]). */
const ixs_node *ixs_node_add_coeff(const ixs_node *node);
uint32_t ixs_node_add_nterms(const ixs_node *node);
const ixs_node *ixs_node_add_term(const ixs_node *node, uint32_t i);
const ixs_node *ixs_node_add_term_coeff(const ixs_node *node, uint32_t i);

/* Only valid when tag is IXS_MUL.  i must be < nfactors.
 * MUL = coeff * product(base[i] ^ exp[i]). */
const ixs_node *ixs_node_mul_coeff(const ixs_node *node);
uint32_t ixs_node_mul_nfactors(const ixs_node *node);
const ixs_node *ixs_node_mul_factor_base(const ixs_node *node, uint32_t i);
int32_t ixs_node_mul_factor_exp(const ixs_node *node, uint32_t i);

/* Only valid when tag is IXS_FLOOR, IXS_CEIL, IXS_TRUNC, or IXS_NOT. */
const ixs_node *ixs_node_unary_arg(const ixs_node *node);

/* Only valid when tag is IXS_MOD or IXS_CMP. */
const ixs_node *ixs_node_binary_lhs(const ixs_node *node);
const ixs_node *ixs_node_binary_rhs(const ixs_node *node);

/* Only valid when tag is IXS_CMP. */
ixs_cmp_op ixs_node_cmp_op(const ixs_node *node);

/* Only valid when tag is IXS_PIECEWISE.  i must be < ncases. */
uint32_t ixs_node_pw_ncases(const ixs_node *node);
const ixs_node *ixs_node_pw_value(const ixs_node *node, uint32_t i);
const ixs_node *ixs_node_pw_cond(const ixs_node *node, uint32_t i);

/* Only valid for MAX, MIN, XOR, AND, or OR. i must be < nargs. */
uint32_t ixs_node_assoc_nargs(const ixs_node *node);
const ixs_node *ixs_node_assoc_arg(const ixs_node *node, uint32_t i);

/* --- Generic child access ----------------------------------------------- */

/* Number of child node pointers.  Leaves return 0. */
uint32_t ixs_node_nchildren(const ixs_node *node);

/* i-th child node.  i must be < ixs_node_nchildren(node).
 * Child order matches the type-specific accessors:
 *   ADD: coeff, (term_coeff[0], term[0]), (term_coeff[1], term[1]), ...
 *   MUL: coeff, base[0], base[1], ...   (exponents are int32_t, not nodes)
 *   binary: lhs, rhs
 *   unary: arg
 *   PW:  (value[0], cond[0]), (value[1], cond[1]), ...
 *   associative: arg[0], arg[1], ... */
const ixs_node *ixs_node_child(const ixs_node *node, uint32_t i);

/* --- Rule-hit statistics (requires -DIXS_STATS at compile time) -------- */

/* Number of distinct rules that have fired.  Returns 0 if compiled
 * without IXS_STATS. */
size_t ixs_ctx_nstats(const ixs_ctx *ctx);

/* Retrieve the i-th stat entry (arbitrary order, 0-based).
 * Sets *name to the rule name and returns the hit count.
 * Returns 0 with *name = NULL for out-of-range indices. */
uint64_t ixs_ctx_stat(const ixs_ctx *ctx, size_t index, const char **name);

/* Reset all counters to zero. */
void ixs_ctx_stats_reset(ixs_ctx *ctx);

/* Total number of distinct rule/transform names registered in the
 * simplifier (rule tables + ad-hoc transforms).  Context-independent. */
size_t ixs_nrules(void);

/* The i-th rule name (0-based).  Returns NULL if out of range. */
const char *ixs_rule_name(size_t index);

/* --- Tree walk --------------------------------------------------------- */

typedef enum {
  IXS_WALK_CONTINUE,
  IXS_WALK_SKIP,
  IXS_WALK_STOP
} ixs_walk_action;

/* Callback must return exactly one of the three values above.
 * Any other return value is undefined behavior. */
typedef ixs_walk_action (*ixs_visit_fn)(const ixs_node *node, void *userdata);

/* Pre-order: visit node, then recurse into children.
 * Returns root on completion, the stopping node on STOP, NULL if root
 * is NULL or the explicit scratch-backed traversal stack cannot grow.
 * s must be non-NULL when root is non-NULL.
 * Sentinels (ERROR, PARSE_ERROR) are visited as leaves; the callback
 * must check ixs_node_tag before using type-specific accessors.
 * SKIP prevents descent into children. */
const ixs_node *ixs_walk_pre(ixs_session *s, const ixs_node *root,
                             ixs_visit_fn fn, void *userdata);

/* Post-order: recurse into children, then visit node.
 * Same return/NULL/sentinel semantics as ixs_walk_pre.
 * SKIP is a no-op in post-order (children already visited). */
const ixs_node *ixs_walk_post(ixs_session *s, const ixs_node *root,
                              ixs_visit_fn fn, void *userdata);

#ifdef __cplusplus
}
#endif

#endif /* IXSIMPL_H */
