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
/* Exact integer truncation toward zero. */
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

/* After NULL and error-sentinel propagation, returns ERROR when op is not one
 * of the six ixs_cmp_op enumerators. */
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

typedef enum {
  IXS_EXACT_DIVIDE_PROVEN,
  IXS_EXACT_DIVIDE_NOT_EXACT,
  IXS_EXACT_DIVIDE_UNKNOWN,
  IXS_EXACT_DIVIDE_ERROR
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
  bool has_lower;
  bool has_upper;
  int64_t lower_p;
  int64_t lower_q;
  int64_t upper_p;
  int64_t upper_q;
} ixs_range_result;

/* Assumption contract shared by simplify, simplify_batch, check,
 * check_integer_valued, check_defined, get_pow2_fact, range, and
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
 * assumptions, using interval propagation, modular congruence facts, bitwise
 * facts, and an exact equivalence fallback for unresolved EQ/NE predicates.
 * expr must be a CMP node in normalized form (lhs op 0), or the canonical
 * true/false node produced when a smart constructor resolves a comparison.
 * CMP normalization is automatic through ixs_cmp().  Returns UNKNOWN when
 * proof information is insufficient, when expr has another form, when a
 * bounded proof limit is reached, or on OOM. */
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

/* Return the strongest known power-of-two fact for every defined evaluation of
 * expr under assumptions; poison points impose no constraint.
 * POSITIVE means expr > 0 and exactly one bit is set.  OR_ZERO additionally
 * permits expr == 0.  UNKNOWN is returned when the fact is not provable, on
 * OOM, for NULL/sentinel expr, or for detected contradictory assumptions. */
ixs_pow2_fact ixs_get_pow2_fact(ixs_session *s, const ixs_node *expr,
                                const ixs_node *const *assumptions,
                                size_t n_assumptions);

/* Infer an inclusive rational range for every defined evaluation of expr under
 * assumptions; poison points impose no constraint. Propagation
 * includes bounded integer powers, sound nonnegative XOR, and first-match
 * Piecewise branch hulls; unsupported domains remain unknown.
 * Returns false when the interval engine cannot derive a range, on OOM,
 * for NULL/sentinel expr, or when out is NULL.  Unbounded sides are reported
 * with has_lower/has_upper false; finite endpoints are exact p/q rationals. */
bool ixs_range(ixs_session *s, const ixs_node *expr,
               const ixs_node *const *assumptions, size_t n_assumptions,
               ixs_range_result *out);

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
 * NULL reports OOM, a resource limit, or an expired/reset session.  Sentinel
 * input propagates; invalid live input returns the fact set context's
 * domain-error sentinel.  Detected contradictory facts return expr unchanged.
 * Live failures append a session diagnostic. */
const ixs_node *ixs_simplify_facts(ixs_facts *facts, const ixs_node *expr);

/* Fact-backed batch simplification.  On failure the operation is
 * transactional and leaves every entry unchanged.  NULL and sentinel entries
 * are invalid input.  Detected contradictory facts leave every entry
 * unchanged.  Live failures append a session diagnostic. */
void ixs_simplify_batch_facts(ixs_facts *facts, const ixs_node **exprs,
                              size_t n);

/* Reusable-fact form of ixs_check with the same CMP or canonical
 * true/false input contract. */
ixs_check_result ixs_check_facts(ixs_facts *facts, const ixs_node *expr);
/* Check a predicate tree against an existing fact set.  AND, OR, and NOT use
 * conservative three-valued logic.  Numeric bitwise AND/OR expressions are
 * rejected because they are not predicate trees. */
ixs_check_result ixs_check_predicate_facts(ixs_facts *facts,
                                           const ixs_node *predicate);
/* Prove refinement compatibility over the full domain admitted by facts. TRUE
 * proves equality wherever both operands are defined; poison valuations impose
 * no equality obligation. FALSE is returned only for a universal proof of
 * different defined values;
 * insufficient facts, contradictory facts, invalid input, and resource
 * limits return UNKNOWN. */
ixs_check_result ixs_equivalent_facts(ixs_facts *facts, const ixs_node *lhs,
                                      const ixs_node *rhs);
/* Decompose expr as coefficient*symbol + residual.  The coefficient is an
 * exact rational constant and residual does not reference symbol. */
bool ixs_affine_decompose_facts(ixs_facts *facts, const ixs_node *expr,
                                const ixs_node *symbol,
                                const ixs_node **coefficient,
                                const ixs_node **residual);
/* Split expr into residual + constant with an exactly representable integer
 * constant. */
bool ixs_split_additive_constant_facts(ixs_facts *facts, const ixs_node *expr,
                                       const ixs_node **residual,
                                       int64_t *constant);
ixs_check_result ixs_check_integer_valued_facts(ixs_facts *facts,
                                                const ixs_node *expr);
ixs_check_result ixs_check_defined_facts(ixs_facts *facts,
                                         const ixs_node *expr);
/* Check divisibility by a nonzero signed modulus.  Negative moduli are
 * normalized by magnitude without overflowing INT64_MIN.  Modulus zero emits
 * a session diagnostic and returns UNKNOWN. */
ixs_check_result ixs_check_divisible_facts(ixs_facts *facts,
                                           const ixs_node *expr,
                                           int64_t modulus);
/* Prove exact divisibility and construct the simplified quotient.  PROVEN is
 * the only status with a non-NULL quotient.  NOT_EXACT is a proof of
 * nondivisibility. The quotient agrees on every defined input evaluation and
 * may be more defined than a partial input. An input proved undefined
 * everywhere refines to canonical zero. UNKNOWN means facts are insufficient
 * or contradictory. Invalid input, divisor zero, unrepresentable results,
 * resource limits, and OOM return ERROR and append a diagnostic to the fact
 * set's session when one is available. */
ixs_exact_divide_result ixs_try_exact_divide_facts(ixs_facts *facts,
                                                   const ixs_node *expr,
                                                   int64_t divisor);
/* Return the strongest power-of-two fact for every defined evaluation. */
ixs_pow2_fact ixs_get_pow2_fact_facts(ixs_facts *facts, const ixs_node *expr);
/* Return sound low-64-bit facts for every defined evaluation. True with zero
 * masks means that the query was valid but proved no bits. Invalid input,
 * contradictory facts, resource limits, and OOM return false and leave out
 * initialized to the no-information value. Live failures append a session
 * diagnostic. */
bool ixs_get_known_bits_facts(ixs_facts *facts, const ixs_node *expr,
                              ixs_known_bits *out);
/* Export the stored congruence record for a symbol.  Output pointers must be
 * non-NULL and distinct.  This deliberately does not synthesize a strongest
 * congruence for arbitrary expressions. */
bool ixs_get_symbol_congruence_facts(ixs_facts *facts, const ixs_node *symbol,
                                     int64_t *modulus, int64_t *residue);
/* Prove expr == residue (mod modulus).  Negative moduli are normalized by
 * magnitude without overflowing INT64_MIN.  Modulus zero emits a diagnostic
 * and returns UNKNOWN. */
ixs_check_result ixs_check_congruent_facts(ixs_facts *facts,
                                           const ixs_node *expr,
                                           int64_t modulus, int64_t residue);
bool ixs_range_facts(ixs_facts *facts, const ixs_node *expr,
                     ixs_range_result *out);

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

/* Print in SymPy-compatible syntax. Returns bytes written (excl. NUL), or
 * SIZE_MAX if the private traversal arena cannot grow. Output is truncated if
 * bufsize is insufficient; traversal failure clears a nonempty buffer. */
size_t ixs_print(const ixs_node *expr, char *buf, size_t bufsize);

/* Print in C syntax where possible; falls back to SymPy style. The return and
 * failure contract is identical to ixs_print. */
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
