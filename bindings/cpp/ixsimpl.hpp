/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXSIMPL_HPP
#define IXSIMPL_HPP

#include <cstring>
#include <exception>
#include <initializer_list>
#include <iterator>
#include <ixsimpl.h>
#include <new>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace ixs {

class Expr;
class Facts;
struct ExactDivideResult;

class Context {
  ixs_ctx *ctx_;
  ixs_session session_;

public:
  Context() : ctx_(ixs_ctx_create()) {
    if (!ctx_)
      throw std::bad_alloc();
    ixs_session_init(&session_, ctx_);
  }
  ~Context() {
    ixs_session_destroy(&session_);
    ixs_ctx_destroy(ctx_);
  }
  Context(const Context &) = delete;
  Context &operator=(const Context &) = delete;
  ixs_ctx *raw() const { return ctx_; }
  ixs_session *session() { return &session_; }
  const ixs_session *session() const { return &session_; }

  size_t nerrors() const { return ixs_session_nerrors(&session_); }
  const char *error(size_t i) const { return ixs_session_error(&session_, i); }
  void clear_errors() { ixs_session_clear_errors(&session_); }
  Expr import_expr(const Expr &expr);
  /* Throws invalid_argument for null expr, rethrows sink write exceptions,
   * throws bad_alloc for core OOM, and runtime_error for codec validation
   * failures. */
  std::string serialize_expr(const Expr &expr);
  /* Parse errors return the Context's parse-error sentinel Expr; OOM throws
   * bad_alloc. */
  Expr deserialize_expr(std::string_view data);
  Facts facts();
};

class Expr {
  ixs_ctx *ctx_;
  ixs_session *session_;
  const ixs_node *node_;

public:
  Expr(ixs_ctx *ctx, ixs_session *session, const ixs_node *node)
      : ctx_(ctx), session_(session), node_(node) {}

  static Expr parse(Context &ctx, std::string_view input) {
    return Expr(ctx.raw(), ctx.session(),
                ixs_parse(ctx.session(), input.data(), input.size()));
  }
  static Expr parse_expr(Context &ctx, std::string_view input) {
    return Expr(ctx.raw(), ctx.session(),
                ixs_parse_expr(ctx.session(), input.data(), input.size()));
  }
  static Expr parse_pred(Context &ctx, std::string_view input) {
    return Expr(ctx.raw(), ctx.session(),
                ixs_parse_pred(ctx.session(), input.data(), input.size()));
  }
  static Expr sym(Context &ctx, const char *name) {
    return Expr(ctx.raw(), ctx.session(), ixs_sym(ctx.session(), name));
  }
  static Expr integer(Context &ctx, int64_t v) {
    return Expr(ctx.raw(), ctx.session(), ixs_int(ctx.session(), v));
  }
  static Expr rational(Context &ctx, int64_t p, int64_t q) {
    return Expr(ctx.raw(), ctx.session(), ixs_rat(ctx.session(), p, q));
  }

  /* Assumptions must be CMP/boolean roots or AND trees with those leaves.
   * Unsupported shapes produce an error Expr and a session diagnostic. */
  Expr simplify(const Expr *assumptions, size_t n) const {
    std::vector<const ixs_node *> raw(n);
    for (size_t i = 0; i < n; ++i)
      raw[i] = assumptions[i].raw();
    return Expr(session_ctx(), session_,
                ixs_simplify(session_, node_, raw.data(), n));
  }
  Expr simplify() const {
    return Expr(session_ctx(), session_,
                ixs_simplify(session_, node_, nullptr, 0));
  }
  Expr simplify(const Facts &facts) const;
  ixs_check_result check(const Expr *assumptions, size_t n) const {
    std::vector<const ixs_node *> raw(n);
    for (size_t i = 0; i < n; ++i)
      raw[i] = assumptions[i].raw();
    return ixs_check(session_, node_, raw.data(), n);
  }
  ixs_check_result check() const {
    return ixs_check(session_, node_, nullptr, 0);
  }
  ixs_check_result check_integer_valued(const Expr *assumptions,
                                        size_t n) const {
    std::vector<const ixs_node *> raw(n);
    for (size_t i = 0; i < n; ++i)
      raw[i] = assumptions[i].raw();
    return ixs_check_integer_valued(session_, node_, raw.data(), n);
  }
  ixs_check_result check_integer_valued() const {
    return ixs_check_integer_valued(session_, node_, nullptr, 0);
  }
  ixs_check_result check_defined(const Expr *assumptions, size_t n) const {
    std::vector<const ixs_node *> raw(n);
    for (size_t i = 0; i < n; ++i)
      raw[i] = assumptions[i].raw();
    return ixs_check_defined(session_, node_, raw.data(), n);
  }
  ixs_check_result check_defined() const {
    return ixs_check_defined(session_, node_, nullptr, 0);
  }
  ixs_pow2_fact get_pow2_fact(const Expr *assumptions, size_t n) const {
    std::vector<const ixs_node *> raw(n);
    for (size_t i = 0; i < n; ++i)
      raw[i] = assumptions[i].raw();
    return ixs_get_pow2_fact(session_, node_, raw.data(), n);
  }
  ixs_pow2_fact get_pow2_fact() const {
    return ixs_get_pow2_fact(session_, node_, nullptr, 0);
  }
  bool range(ixs_range_result &out, const Expr *assumptions, size_t n) const {
    std::vector<const ixs_node *> raw(n);
    for (size_t i = 0; i < n; ++i)
      raw[i] = assumptions[i].raw();
    return ixs_range(session_, node_, raw.data(), n, &out);
  }
  bool range(ixs_range_result &out) const {
    return ixs_range(session_, node_, nullptr, 0, &out);
  }
  bool integer_range(ixs_integer_range_result &out, const Expr *assumptions,
                     size_t n) const {
    std::vector<const ixs_node *> raw(n);
    for (size_t i = 0; i < n; ++i)
      raw[i] = assumptions[i].raw();
    return ixs_integer_range(session_, node_, raw.data(), n, &out);
  }
  bool integer_range(ixs_integer_range_result &out) const {
    return ixs_integer_range(session_, node_, nullptr, 0, &out);
  }
  Expr expand() const {
    return Expr(session_ctx(), session_, ixs_expand(session_, node_));
  }
  Expr subs(Expr target, Expr repl) const {
    return Expr(session_ctx(), session_,
                ixs_subs(session_, node_, target.node_, repl.node_));
  }
  Expr subs_multi(uint32_t n, const Expr *targets, const Expr *repls) const {
    std::vector<const ixs_node *> t(n), r(n);
    for (uint32_t i = 0; i < n; i++) {
      t[i] = targets[i].node_;
      r[i] = repls[i].node_;
    }
    return Expr(session_ctx(), session_,
                ixs_subs_multi(session_, node_, n, t.data(), r.data()));
  }

  Expr operator+(Expr rhs) const {
    return Expr(session_ctx(), session_, ixs_add(session_, node_, rhs.node_));
  }
  Expr operator*(Expr rhs) const {
    return Expr(session_ctx(), session_, ixs_mul(session_, node_, rhs.node_));
  }
  Expr operator-(Expr rhs) const {
    const ixs_node *neg = ixs_mul(session_, ixs_int(session_, -1), rhs.node_);
    return Expr(session_ctx(), session_, ixs_add(session_, node_, neg));
  }
  Expr operator-() const {
    return Expr(session_ctx(), session_,
                ixs_mul(session_, ixs_int(session_, -1), node_));
  }
  bool operator==(Expr rhs) const { return ixs_same_node(node_, rhs.node_); }

  Expr operator>=(Expr rhs) const {
    return Expr(session_ctx(), session_,
                ixs_cmp(session_, node_, IXS_CMP_GE, rhs.node_));
  }
  Expr operator>(Expr rhs) const {
    return Expr(session_ctx(), session_,
                ixs_cmp(session_, node_, IXS_CMP_GT, rhs.node_));
  }
  Expr operator<=(Expr rhs) const {
    return Expr(session_ctx(), session_,
                ixs_cmp(session_, node_, IXS_CMP_LE, rhs.node_));
  }
  Expr operator<(Expr rhs) const {
    return Expr(session_ctx(), session_,
                ixs_cmp(session_, node_, IXS_CMP_LT, rhs.node_));
  }

  std::string str() const {
    if (!node_)
      return std::string();
    size_t n = ixs_print(node_, nullptr, 0);
    std::string s(n + 1, '\0');
    ixs_print(node_, s.data(), n + 1);
    s.resize(n);
    return s;
  }
  std::string to_c() const {
    if (!node_)
      return std::string();
    size_t n = ixs_print_c(node_, nullptr, 0);
    std::string s(n + 1, '\0');
    ixs_print_c(node_, s.data(), n + 1);
    s.resize(n);
    return s;
  }

  bool is_null() const { return node_ == nullptr; }
  bool is_error() const { return node_ && ixs_is_error(node_); }
  bool is_parse_error() const { return node_ && ixs_is_parse_error(node_); }
  bool is_domain_error() const { return node_ && ixs_is_domain_error(node_); }
  bool is_expr() const { return node_ && ixs_node_is_expr(node_); }
  bool is_pred() const { return node_ && ixs_node_is_pred(node_); }
  bool is_integer_valued() const {
    return node_ && ixs_node_is_integer_valued(node_);
  }
  explicit operator bool() const {
    return node_ != nullptr && !ixs_is_error(node_);
  }

  const ixs_node *raw() const { return node_; }
  const ixs_node *raw_const() const { return node_; }
  ixs_ctx *raw_ctx() const { return ctx_; }
  ixs_session *raw_session() const { return session_; }

private:
  ixs_ctx *session_ctx() const { return ctx_; }
};

struct ExactDivideResult {
  ixs_exact_divide_status status;
  Expr quotient;
};

struct RationalMaterializationPlan {
  ixs_fact_query_status status;
  ixs_check_result check;
  Expr numerator;
  int64_t denominator;
};

struct FiniteDomainResult {
  ixs_finite_domain_status status;
  ixs_check_result check;
  Expr value;
};

struct FiniteIntegerDomain {
  Expr symbol;
  std::vector<int64_t> points;
};

struct FiniteDomainBatchQuery {
  ixs_finite_domain_batch_query_kind kind;
  Expr value;
};

struct FiniteDomainBatchResult {
  ixs_check_result check;
  size_t witness;
};

struct ModuloRecurrenceResult {
  ixs_modulo_recurrence_status status;
  uint64_t increment;
  Expr remainder;
};

struct CyclicDecomposition {
  Expr residual;
  int64_t scale;
  int64_t modulus;
  int64_t phase;
  int64_t ring;
  bool residual_bounded;
};

struct GroupUnionQuery {
  size_t lhs_group;
  size_t rhs_group;
  ixs_group_union_query_kind kind;
  Expr lhs;
  Expr rhs;
};

struct GroupUnionResult {
  ixs_check_result status;
  int64_t difference;
};

inline ixs_group_union_status
query_group_unions(Context &ctx, const std::vector<std::vector<Expr>> &groups,
                   const std::vector<GroupUnionQuery> &queries,
                   std::vector<GroupUnionResult> &results,
                   size_t &remaining_work) {
  std::vector<std::vector<const ixs_node *>> raw_predicates(groups.size());
  std::vector<ixs_predicate_group> raw_groups(groups.size());
  std::vector<ixs_group_union_query> raw_queries;
  std::vector<ixs_group_union_result> raw_results(queries.size());

  for (size_t group_index = 0; group_index < groups.size(); ++group_index) {
    raw_predicates[group_index].reserve(groups[group_index].size());
    for (const Expr &predicate : groups[group_index])
      raw_predicates[group_index].push_back(predicate.raw());
    raw_groups[group_index] = {raw_predicates[group_index].data(),
                               raw_predicates[group_index].size()};
  }
  raw_queries.reserve(queries.size());
  for (const GroupUnionQuery &query : queries)
    raw_queries.push_back({query.lhs_group, query.rhs_group, query.kind,
                           query.lhs.raw(), query.rhs.raw()});
  ixs_group_union_status status = ixs_query_group_unions(
      ctx.session(), raw_groups.data(), raw_groups.size(), raw_queries.data(),
      raw_queries.size(), raw_results.data(), &remaining_work);
  results.resize(raw_results.size());
  for (size_t index = 0; index < raw_results.size(); ++index)
    results[index] = {raw_results[index].status, raw_results[index].difference};
  return status;
}

class Facts {
  ixs_ctx *ctx_;
  ixs_session *session_;
  ixs_facts *facts_;

  void require_complete(ixs_fact_query_status status,
                        const char *operation) const {
    if (status == IXS_FACT_QUERY_COMPLETE)
      return;
    if (status == IXS_FACT_QUERY_OOM)
      throw std::bad_alloc();
    std::string message = std::string("ixsimpl: ") + operation;
    size_t count = ixs_session_nerrors(session_);
    if (count != 0u) {
      const char *detail = ixs_session_error(session_, count - 1u);
      if (detail && *detail)
        message = detail;
    }
    if (status == IXS_FACT_QUERY_INVALID)
      throw std::invalid_argument(message);
    throw std::runtime_error(message + ": proof resource limit reached");
  }

public:
  explicit Facts(Context &ctx)
      : ctx_(ctx.raw()), session_(ctx.session()),
        facts_(ixs_facts_create(ctx.session())) {
    if (!facts_)
      throw std::bad_alloc();
  }

  bool assume(const Expr &pred) {
    return ixs_facts_assume_pred(facts_, pred.raw());
  }
  bool assume_many(const std::vector<Expr> &predicates) {
    std::vector<const ixs_node *> raw;
    raw.reserve(predicates.size());
    for (const Expr &predicate : predicates)
      raw.push_back(predicate.raw());
    return ixs_facts_assume_preds(facts_, raw.data(), raw.size());
  }
  bool assume_range(const Expr &expr, const ixs_range_result &range) {
    return ixs_facts_assume_range(facts_, expr.raw(), &range);
  }
  bool derive_affine(const Expr &base, int64_t scale, int64_t offset,
                     const Expr &derived) {
    return ixs_facts_derive_affine(facts_, base.raw(), scale, offset,
                                   derived.raw());
  }
  Expr simplify(const Expr &expr) const {
    ixs_simplify_result result = ixs_simplify_facts(facts_, expr.raw());
    require_complete(result.status, "simplify");
    return Expr(ctx_, session_, result.value);
  }
  void simplify_batch(std::vector<Expr> &exprs) const {
    std::vector<const ixs_node *> raw;
    raw.reserve(exprs.size());
    for (const Expr &expr : exprs)
      raw.push_back(expr.raw());
    ixs_fact_query_status status =
        ixs_simplify_batch_facts(facts_, raw.data(), raw.size());
    require_complete(status, "simplify batch");
    for (size_t i = 0; i < exprs.size(); ++i)
      exprs[i] = Expr(ctx_, session_, raw[i]);
  }
  ixs_check_result check(const Expr &expr) const {
    ixs_fact_check_result result = ixs_check_facts(facts_, expr.raw());
    require_complete(result.status, "check");
    return result.check;
  }
  ixs_check_result check_integer_valued(const Expr &expr) const {
    ixs_fact_check_result result =
        ixs_check_integer_valued_facts(facts_, expr.raw());
    require_complete(result.status, "integer-valued check");
    return result.check;
  }
  ixs_check_result check_defined(const Expr &expr) const {
    ixs_fact_check_result result = ixs_check_defined_facts(facts_, expr.raw());
    require_complete(result.status, "definedness check");
    return result.check;
  }
  ixs_check_result check_predicate(const Expr &predicate) const {
    ixs_fact_check_result result =
        ixs_check_predicate_facts(facts_, predicate.raw());
    require_complete(result.status, "predicate check");
    return result.check;
  }
  ixs_check_result check_consistent() const {
    ixs_fact_check_result result = ixs_check_consistent_facts(facts_);
    require_complete(result.status, "consistency check");
    return result.check;
  }
  ixs_check_result equivalent(const Expr &lhs, const Expr &rhs) const {
    ixs_fact_check_result result =
        ixs_equivalent_facts(facts_, lhs.raw(), rhs.raw());
    require_complete(result.status, "equivalence");
    return result.check;
  }
  ixs_check_result equivalent_modulo_pow2(const Expr &lhs, const Expr &rhs,
                                          unsigned bits) const {
    ixs_fact_check_result result =
        ixs_equivalent_modulo_pow2_facts(facts_, lhs.raw(), rhs.raw(), bits);
    require_complete(result.status, "modulo power-of-two equivalence");
    return result.check;
  }
  FiniteDomainResult equivalent_finite_domain(const Expr &lhs, const Expr &rhs,
                                              size_t &remaining_work) const {
    ixs_finite_domain_query query{};
    query.kind = IXS_FINITE_DOMAIN_EQUIVALENCE;
    query.as.equivalence = {lhs.raw(), rhs.raw()};
    ixs_finite_domain_result result =
        ixs_finite_domain_facts(facts_, &query, &remaining_work);
    return {result.status, result.check, Expr(ctx_, session_, result.value)};
  }
  FiniteDomainResult synthesize_finite_expression(
      const Expr &symbol, const std::vector<int64_t> &points,
      const std::vector<Expr> &values, size_t &remaining_work) const {
    std::vector<const ixs_node *> raw;
    ixs_finite_domain_query query{};
    if (points.size() != values.size())
      return {IXS_FINITE_DOMAIN_INVALID, IXS_CHECK_UNKNOWN,
              Expr(ctx_, session_, nullptr)};
    raw.reserve(values.size());
    for (const Expr &value : values)
      raw.push_back(value.raw());
    query.kind = IXS_FINITE_DOMAIN_EXPR_SYNTHESIS;
    query.as.synthesis = {symbol.raw(), points.data(), raw.data(), raw.size()};
    ixs_finite_domain_result result =
        ixs_finite_domain_facts(facts_, &query, &remaining_work);
    return {result.status, result.check, Expr(ctx_, session_, result.value)};
  }
  FiniteDomainResult synthesize_finite_predicate(
      const Expr &symbol, const std::vector<int64_t> &points,
      const std::vector<Expr> &values, size_t &remaining_work) const {
    std::vector<const ixs_node *> raw;
    ixs_finite_domain_query query{};
    if (points.size() != values.size())
      return {IXS_FINITE_DOMAIN_INVALID, IXS_CHECK_UNKNOWN,
              Expr(ctx_, session_, nullptr)};
    raw.reserve(values.size());
    for (const Expr &value : values)
      raw.push_back(value.raw());
    query.kind = IXS_FINITE_DOMAIN_PRED_SYNTHESIS;
    query.as.synthesis = {symbol.raw(), points.data(), raw.data(), raw.size()};
    ixs_finite_domain_result result =
        ixs_finite_domain_facts(facts_, &query, &remaining_work);
    return {result.status, result.check, Expr(ctx_, session_, result.value)};
  }
  FiniteDomainResult verify_finite_expression(
      const Expr &symbol, const std::vector<int64_t> &points,
      const std::vector<Expr> &values, const Expr &candidate,
      size_t &remaining_work) const {
    return verify_finite_relation(IXS_FINITE_DOMAIN_EXPR_RELATION, symbol,
                                  points, values, candidate, remaining_work);
  }
  FiniteDomainResult verify_finite_predicate(const Expr &symbol,
                                             const std::vector<int64_t> &points,
                                             const std::vector<Expr> &values,
                                             const Expr &candidate,
                                             size_t &remaining_work) const {
    return verify_finite_relation(IXS_FINITE_DOMAIN_PRED_RELATION, symbol,
                                  points, values, candidate, remaining_work);
  }
  ixs_finite_domain_status
  check_finite_domain_batch(const std::vector<FiniteIntegerDomain> &domains,
                            const std::vector<FiniteDomainBatchQuery> &queries,
                            std::vector<FiniteDomainBatchResult> &results,
                            size_t &remaining_work) const {
    std::vector<ixs_finite_integer_domain> raw_domains;
    std::vector<ixs_finite_domain_batch_query> raw_queries;
    std::vector<ixs_finite_domain_batch_result> raw_results(
        queries.size(), {IXS_CHECK_UNKNOWN, SIZE_MAX});
    raw_domains.reserve(domains.size());
    for (const FiniteIntegerDomain &domain : domains)
      raw_domains.push_back(
          {domain.symbol.raw(), domain.points.data(), domain.points.size()});
    raw_queries.reserve(queries.size());
    for (const FiniteDomainBatchQuery &query : queries)
      raw_queries.push_back({query.kind, query.value.raw()});
    ixs_finite_domain_status status = ixs_finite_domain_batch_facts(
        facts_, raw_domains.data(), raw_domains.size(), raw_queries.data(),
        raw_queries.size(), raw_results.data(), &remaining_work);
    results.resize(raw_results.size());
    for (size_t index = 0; index < raw_results.size(); ++index)
      results[index] = {raw_results[index].check, raw_results[index].witness};
    return status;
  }
  bool constant_difference(const Expr &lhs, const Expr &rhs,
                           int64_t &delta) const {
    ixs_constant_difference_result result =
        ixs_constant_difference_facts(facts_, lhs.raw(), rhs.raw());
    require_complete(result.status, "constant difference");
    if (result.available)
      delta = result.difference;
    return result.available;
  }
  ModuloRecurrenceResult
  modulo_recurrence(const Expr &value, const Expr &reference,
                    const Expr &induction, ixs_remainder_signedness signedness,
                    unsigned width, uint64_t divisor) const {
    ixs_modulo_recurrence_result result = ixs_modulo_recurrence_facts(
        facts_, value.raw(), reference.raw(), induction.raw(), signedness,
        width, divisor);
    return {result.status, result.increment,
            Expr(ctx_, session_, result.remainder)};
  }
  bool affine_decompose(const Expr &expr, const Expr &symbol, Expr &coefficient,
                        Expr &residual) const {
    ixs_affine_decomposition_result result =
        ixs_affine_decompose_facts(facts_, expr.raw(), symbol.raw());
    require_complete(result.status, "affine decomposition");
    if (!result.available)
      return false;
    coefficient = Expr(ctx_, session_, result.coefficient);
    residual = Expr(ctx_, session_, result.residual);
    return true;
  }
  bool decompose_exact_quotient(const Expr &expr, Expr &numerator,
                                Expr &denominator) const {
    ixs_exact_quotient_result result =
        ixs_decompose_exact_quotient_facts(facts_, expr.raw());
    require_complete(result.status, "exact quotient decomposition");
    if (!result.available)
      return false;
    numerator = Expr(ctx_, session_, result.numerator);
    denominator = Expr(ctx_, session_, result.denominator);
    return true;
  }
  bool finite_difference(const Expr &expr, const Expr &symbol, const Expr &step,
                         Expr &difference) const {
    ixs_finite_difference_result result =
        ixs_finite_difference_facts(facts_, expr.raw(), symbol.raw(), step.raw());
    require_complete(result.status, "finite difference");
    if (!result.available)
      return false;
    difference = Expr(ctx_, session_, result.difference);
    return true;
  }
  bool decompose_cyclic(const Expr &expr, const Expr &symbol,
                        CyclicDecomposition &out) const {
    ixs_cyclic_decomposition_result result =
        ixs_decompose_cyclic_facts(facts_, expr.raw(), symbol.raw());
    require_complete(result.status, "cyclic decomposition");
    if (!result.available)
      return false;
    const ixs_cyclic_decomposition &raw = result.decomposition;
    out = CyclicDecomposition{Expr(ctx_, session_, raw.residual), raw.scale,
                              raw.modulus, raw.phase, raw.ring,
                              raw.residual_bounded};
    return true;
  }
  bool split_additive_constant(const Expr &expr, Expr &residual,
                               int64_t &constant) const {
    ixs_additive_constant_result result =
        ixs_split_additive_constant_facts(facts_, expr.raw());
    require_complete(result.status, "additive constant split");
    if (!result.available)
      return false;
    residual = Expr(ctx_, session_, result.residual);
    constant = result.constant;
    return true;
  }
  ixs_check_result check_divisible(const Expr &expr, int64_t modulus) const {
    ixs_fact_check_result result =
        ixs_check_divisible_facts(facts_, expr.raw(), modulus);
    require_complete(result.status, "divisibility check");
    return result.check;
  }
  bool get_known_bits(const Expr &expr, ixs_known_bits &out) const {
    ixs_known_bits_query_result result =
        ixs_get_known_bits_facts(facts_, expr.raw());
    require_complete(result.status, "known bits");
    out = result.bits;
    return true;
  }
  bool get_symbol_congruence(const Expr &symbol, int64_t &modulus,
                             int64_t &residue) const {
    ixs_symbol_congruence_result result =
        ixs_get_symbol_congruence_facts(facts_, symbol.raw());
    require_complete(result.status, "symbol congruence");
    if (result.available) {
      modulus = result.modulus;
      residue = result.residue;
    }
    return result.available;
  }
  ixs_check_result check_congruent(const Expr &expr, int64_t modulus,
                                   int64_t residue) const {
    ixs_fact_check_result result =
        ixs_check_congruent_facts(facts_, expr.raw(), modulus, residue);
    require_complete(result.status, "congruence check");
    return result.check;
  }
  ixs_pow2_fact get_pow2_fact(const Expr &expr) const {
    ixs_pow2_query_result result = ixs_get_pow2_fact_facts(facts_, expr.raw());
    require_complete(result.status, "power-of-two fact");
    return result.fact;
  }
  bool range(const Expr &expr, ixs_range_result &out) const {
    ixs_range_query_result result = ixs_range_facts(facts_, expr.raw());
    require_complete(result.status, "range");
    if (result.available)
      out = result.range;
    return result.available;
  }
  bool integer_range(const Expr &expr, ixs_integer_range_result &out) const {
    ixs_integer_range_query_result result =
        ixs_integer_range_facts(facts_, expr.raw());
    require_complete(result.status, "integer range");
    if (result.available)
      out = result.range;
    return result.available;
  }
  ixs_check_result rational_intermediates_fit(const Expr &expr,
                                              uint32_t word_bits) const {
    ixs_fact_check_result result =
        ixs_check_rational_intermediates_facts(facts_, expr.raw(), word_bits);
    require_complete(result.status, "rational intermediate width");
    return result.check;
  }
  RationalMaterializationPlan
  plan_rational_materialization(const Expr &expr, uint32_t word_bits) const {
    ixs_rational_materialization_plan result =
        ixs_plan_rational_materialization_facts(facts_, expr.raw(), word_bits);
    return {result.status, result.check, Expr(ctx_, session_, result.numerator),
            result.denominator};
  }
  bool substitute(const Facts &source, const Expr &target,
                  const Expr &replacement) {
    return ixs_facts_substitute(facts_, source.raw(), target.raw(),
                                replacement.raw());
  }
  bool substitute_multi(const Facts &source, const std::vector<Expr> &targets,
                        const std::vector<Expr> &replacements) {
    std::vector<const ixs_node *> raw_targets;
    std::vector<const ixs_node *> raw_replacements;
    size_t i;
    if (targets.size() != replacements.size() ||
        targets.size() > static_cast<size_t>(UINT32_MAX))
      return false;
    raw_targets.reserve(targets.size());
    raw_replacements.reserve(replacements.size());
    for (i = 0; i < targets.size(); ++i) {
      raw_targets.push_back(targets[i].raw());
      raw_replacements.push_back(replacements[i].raw());
    }
    return ixs_facts_substitute_multi(
        facts_, source.raw(), static_cast<uint32_t>(targets.size()),
        raw_targets.empty() ? nullptr : raw_targets.data(),
        raw_replacements.empty() ? nullptr : raw_replacements.data());
  }
  ExactDivideResult try_exact_divide(const Expr &expr, int64_t divisor) const {
    ixs_exact_divide_result result =
        ixs_try_exact_divide_facts(facts_, expr.raw(), divisor);
    return {result.status, Expr(ctx_, session_, result.quotient)};
  }
  ixs_facts *raw() const { return facts_; }
  ixs_ctx *raw_ctx() const { return ctx_; }

private:
  FiniteDomainResult verify_finite_relation(ixs_finite_domain_query_kind kind,
                                            const Expr &symbol,
                                            const std::vector<int64_t> &points,
                                            const std::vector<Expr> &values,
                                            const Expr &candidate,
                                            size_t &remaining_work) const {
    std::vector<const ixs_node *> raw;
    ixs_finite_domain_query query{};
    if (points.size() != values.size())
      return {IXS_FINITE_DOMAIN_INVALID, IXS_CHECK_UNKNOWN,
              Expr(ctx_, session_, nullptr)};
    raw.reserve(values.size());
    for (const Expr &value : values)
      raw.push_back(value.raw());
    query.kind = kind;
    query.as.relation = {symbol.raw(), points.data(), raw.data(), raw.size(),
                         candidate.raw()};
    ixs_finite_domain_result result =
        ixs_finite_domain_facts(facts_, &query, &remaining_work);
    return {result.status, result.check, Expr(ctx_, session_, result.value)};
  }
};

inline Expr Expr::simplify(const Facts &facts) const {
  return facts.simplify(*this);
}

inline Facts Context::facts() { return Facts(*this); }

inline Expr Context::import_expr(const Expr &expr) {
  if (!expr.raw())
    throw std::invalid_argument("ixsimpl: null expression");
  const ixs_node *node = ixs_import_node(session(), expr.raw());
  if (!node)
    throw std::bad_alloc();
  return Expr(raw(), session(), node);
}

inline std::string Context::serialize_expr(const Expr &expr) {
  struct StringWriter {
    std::string bytes;
    std::exception_ptr failure;

    static bool write(void *userdata, const void *buf, size_t len) {
      StringWriter *self = static_cast<StringWriter *>(userdata);
      try {
        self->bytes.append(static_cast<const char *>(buf), len);
      } catch (...) {
        self->failure = std::current_exception();
        return false;
      }
      return true;
    }
  };
  size_t before_nerrors;
  size_t after_nerrors;

  if (!expr.raw())
    throw std::invalid_argument("ixsimpl: null expression");

  before_nerrors = nerrors();
  StringWriter sink;
  const ixs_writer writer = {&StringWriter::write, &sink};
  if (!ixs_serialize_node(session(), expr.raw(), &writer)) {
    if (sink.failure)
      std::rethrow_exception(sink.failure);
    after_nerrors = nerrors();
    if (after_nerrors > before_nerrors)
      throw std::runtime_error(error(before_nerrors));
    throw std::bad_alloc();
  }
  return sink.bytes;
}

inline Expr Context::deserialize_expr(std::string_view data) {
  struct StringReader {
    const char *data;
    size_t len;
    size_t pos;

    static bool read(void *userdata, void *buf, size_t len) {
      StringReader *self = static_cast<StringReader *>(userdata);
      if (self->pos > self->len)
        return false;
      if (len > self->len - self->pos)
        return false;
      std::memcpy(buf, self->data + self->pos, len);
      self->pos += len;
      return true;
    }

    static size_t remaining(void *userdata) {
      StringReader *self = static_cast<StringReader *>(userdata);
      if (self->pos > self->len)
        return 0;
      return self->len - self->pos;
    }
  };

  StringReader source = {data.data(), data.size(), 0};
  const ixs_reader reader = {&StringReader::read, &StringReader::remaining,
                             &source};
  const ixs_node *node = ixs_deserialize_node(session(), &reader);
  if (!node)
    throw std::bad_alloc();
  return Expr(raw(), session(), node);
}

inline Expr floor(Expr x) {
  return Expr(x.raw_ctx(), x.raw_session(),
              ixs_floor(x.raw_session(), x.raw()));
}
inline Expr ceil(Expr x) {
  return Expr(x.raw_ctx(), x.raw_session(), ixs_ceil(x.raw_session(), x.raw()));
}
inline Expr trunc(Expr x) {
  return Expr(x.raw_ctx(), x.raw_session(),
              ixs_trunc(x.raw_session(), x.raw()));
}
inline Expr mod(Expr a, Expr b) {
  return Expr(a.raw_ctx(), a.raw_session(),
              ixs_mod(a.raw_session(), a.raw(), b.raw()));
}
inline Expr max(Expr a, Expr b) {
  return Expr(a.raw_ctx(), a.raw_session(),
              ixs_max(a.raw_session(), a.raw(), b.raw()));
}
inline Expr min(Expr a, Expr b) {
  return Expr(a.raw_ctx(), a.raw_session(),
              ixs_min(a.raw_session(), a.raw(), b.raw()));
}
inline Expr xor_(Expr a, Expr b) {
  return Expr(a.raw_ctx(), a.raw_session(),
              ixs_xor(a.raw_session(), a.raw(), b.raw()));
}
inline Expr and_(Expr a, Expr b) {
  return Expr(a.raw_ctx(), a.raw_session(),
              ixs_and(a.raw_session(), a.raw(), b.raw()));
}
inline Expr or_(Expr a, Expr b) {
  return Expr(a.raw_ctx(), a.raw_session(),
              ixs_or(a.raw_session(), a.raw(), b.raw()));
}

using AssocManyFn = const ixs_node *(*)(ixs_session *, uint32_t,
                                        const ixs_node *const *);

template <typename Range>
inline Expr assoc_many(const Range &values, AssocManyFn fn,
                       const char *empty_error) {
  auto first = std::begin(values);
  auto last = std::end(values);
  if (first == last)
    throw std::invalid_argument(empty_error);
  ixs_ctx *ctx = first->raw_ctx();
  ixs_session *session = first->raw_session();
  std::vector<const ixs_node *> raw;
  for (auto it = first; it != last; ++it) {
    if (it->raw_ctx() != ctx)
      throw std::invalid_argument(
          "associative operands belong to different contexts");
    if (raw.size() == UINT32_MAX)
      throw std::length_error("too many associative operands");
    raw.push_back(it->raw());
  }
  return Expr(ctx, session,
              fn(session, static_cast<uint32_t>(raw.size()), raw.data()));
}

template <typename Range> inline Expr max(const Range &values) {
  return assoc_many(values, ixs_max_many, "max requires an operand");
}
template <typename Range> inline Expr min(const Range &values) {
  return assoc_many(values, ixs_min_many, "min requires an operand");
}
template <typename Range> inline Expr xor_(const Range &values) {
  return assoc_many(values, ixs_xor_many, "xor requires an operand");
}
template <typename Range> inline Expr and_(const Range &values) {
  return assoc_many(values, ixs_and_many, "and requires an operand");
}
template <typename Range> inline Expr or_(const Range &values) {
  return assoc_many(values, ixs_or_many, "or requires an operand");
}

inline Expr max(std::initializer_list<Expr> values) {
  return assoc_many(values, ixs_max_many, "max requires an operand");
}
inline Expr min(std::initializer_list<Expr> values) {
  return assoc_many(values, ixs_min_many, "min requires an operand");
}
inline Expr xor_(std::initializer_list<Expr> values) {
  return assoc_many(values, ixs_xor_many, "xor requires an operand");
}
inline Expr and_(std::initializer_list<Expr> values) {
  return assoc_many(values, ixs_and_many, "and requires an operand");
}
inline Expr or_(std::initializer_list<Expr> values) {
  return assoc_many(values, ixs_or_many, "or requires an operand");
}

inline Expr pw(std::initializer_list<std::pair<Expr, Expr>> branches) {
  if (branches.size() == 0)
    throw std::invalid_argument("pw requires at least one branch");
  ixs_ctx *ctx = branches.begin()->first.raw_ctx();
  std::vector<const ixs_node *> vals, conds;
  vals.reserve(branches.size());
  conds.reserve(branches.size());
  for (auto &b : branches) {
    vals.push_back(b.first.raw());
    conds.push_back(b.second.raw());
  }
  ixs_session *session = branches.begin()->first.raw_session();
  return Expr(ctx, session,
              ixs_pw(session, static_cast<uint32_t>(vals.size()), vals.data(),
                     conds.data()));
}

} // namespace ixs

#endif /* IXSIMPL_HPP */
