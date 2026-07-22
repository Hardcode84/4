/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXSIMPL_HPP
#define IXSIMPL_HPP

#include <cstring>
#include <exception>
#include <initializer_list>
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

  size_t nerrors() const {
    return ixs_session_nerrors(const_cast<ixs_session *>(&session_));
  }
  const char *error(size_t i) const {
    return ixs_session_error(const_cast<ixs_session *>(&session_), i);
  }
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
  ixs_node *node_;

public:
  Expr(ixs_ctx *ctx, ixs_session *session, ixs_node *node)
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
    std::vector<ixs_node *> raw(n);
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
  ixs_check_result check_integer_valued(const Expr *assumptions,
                                        size_t n) const {
    std::vector<ixs_node *> raw(n);
    for (size_t i = 0; i < n; ++i)
      raw[i] = assumptions[i].raw();
    return ixs_check_integer_valued(session_, node_, raw.data(), n);
  }
  ixs_check_result check_integer_valued() const {
    return ixs_check_integer_valued(session_, node_, nullptr, 0);
  }
  ixs_check_result check_defined(const Expr *assumptions, size_t n) const {
    std::vector<ixs_node *> raw(n);
    for (size_t i = 0; i < n; ++i)
      raw[i] = assumptions[i].raw();
    return ixs_check_defined(session_, node_, raw.data(), n);
  }
  ixs_check_result check_defined() const {
    return ixs_check_defined(session_, node_, nullptr, 0);
  }
  Expr subs(Expr target, Expr repl) const {
    return Expr(session_ctx(), session_,
                ixs_subs(session_, node_, target.node_, repl.node_));
  }
  Expr subs_multi(uint32_t n, const Expr *targets, const Expr *repls) const {
    std::vector<ixs_node *> t(n), r(n);
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
    ixs_node *neg = ixs_mul(session_, ixs_int(session_, -1), rhs.node_);
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

  ixs_node *raw() const { return node_; }
  ixs_ctx *raw_ctx() const { return ctx_; }
  ixs_session *raw_session() const { return session_; }

private:
  ixs_ctx *session_ctx() const { return ctx_; }
};

struct ExactDivideResult {
  ixs_exact_divide_status status;
  Expr quotient;
};

class Facts {
  ixs_ctx *ctx_;
  ixs_session *session_;
  ixs_facts *facts_;

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
  Expr simplify(const Expr &expr) const {
    return Expr(ctx_, session_, ixs_simplify_facts(facts_, expr.raw()));
  }
  void simplify_batch(std::vector<Expr> &exprs) const {
    std::vector<ixs_node *> raw;
    raw.reserve(exprs.size());
    for (const Expr &expr : exprs)
      raw.push_back(expr.raw());
    ixs_simplify_batch_facts(facts_, raw.data(), raw.size());
    for (size_t i = 0; i < exprs.size(); ++i)
      exprs[i] = Expr(ctx_, session_, raw[i]);
  }
  ixs_check_result check_integer_valued(const Expr &expr) const {
    return ixs_check_integer_valued_facts(facts_, expr.raw());
  }
  ixs_check_result check_defined(const Expr &expr) const {
    return ixs_check_defined_facts(facts_, expr.raw());
  }
  ixs_check_result check_predicate(const Expr &predicate) const {
    return ixs_check_predicate_facts(facts_, predicate.raw());
  }
  ixs_check_result equivalent(const Expr &lhs, const Expr &rhs) const {
    return ixs_equivalent_facts(facts_, lhs.raw(), rhs.raw());
  }
  bool constant_difference(const Expr &lhs, const Expr &rhs,
                           int64_t &delta) const {
    return ixs_constant_difference_facts(facts_, lhs.raw(), rhs.raw(), &delta);
  }
  bool affine_decompose(const Expr &expr, const Expr &symbol, Expr &coefficient,
                        Expr &residual) const {
    ixs_node *raw_coefficient = nullptr;
    ixs_node *raw_residual = nullptr;
    if (!ixs_affine_decompose_facts(facts_, expr.raw(), symbol.raw(),
                                    &raw_coefficient, &raw_residual))
      return false;
    coefficient = Expr(ctx_, session_, raw_coefficient);
    residual = Expr(ctx_, session_, raw_residual);
    return true;
  }
  bool finite_difference(const Expr &expr, const Expr &symbol, const Expr &step,
                         Expr &difference) const {
    ixs_node *raw_difference = nullptr;
    if (!ixs_finite_difference_facts(facts_, expr.raw(), symbol.raw(),
                                     step.raw(), &raw_difference))
      return false;
    difference = Expr(ctx_, session_, raw_difference);
    return true;
  }
  bool split_additive_constant(const Expr &expr, Expr &residual,
                               int64_t &constant) const {
    ixs_node *raw_residual = nullptr;
    if (!ixs_split_additive_constant_facts(facts_, expr.raw(), &raw_residual,
                                           &constant))
      return false;
    residual = Expr(ctx_, session_, raw_residual);
    return true;
  }
  ixs_check_result check_divisible(const Expr &expr, int64_t modulus) const {
    return ixs_check_divisible_facts(facts_, expr.raw(), modulus);
  }
  bool get_known_bits(const Expr &expr, ixs_known_bits &out) const {
    return ixs_get_known_bits_facts(facts_, expr.raw(), &out);
  }
  bool get_symbol_congruence(const Expr &symbol, int64_t &modulus,
                             int64_t &residue) const {
    return ixs_get_symbol_congruence_facts(facts_, symbol.raw(), &modulus,
                                           &residue);
  }
  ixs_check_result check_congruent(const Expr &expr, int64_t modulus,
                                   int64_t residue) const {
    return ixs_check_congruent_facts(facts_, expr.raw(), modulus, residue);
  }
  bool substitute(const Facts &source, const Expr &target,
                  const Expr &replacement) {
    return ixs_facts_substitute(facts_, source.raw(), target.raw(),
                                replacement.raw());
  }
  bool substitute_multi(const Facts &source, const std::vector<Expr> &targets,
                        const std::vector<Expr> &replacements) {
    std::vector<ixs_node *> raw_targets;
    std::vector<ixs_node *> raw_replacements;
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
};

inline Expr Expr::simplify(const Facts &facts) const {
  return facts.simplify(*this);
}

inline Facts Context::facts() { return Facts(*this); }

inline Expr Context::import_expr(const Expr &expr) {
  if (!expr.raw())
    throw std::invalid_argument("ixsimpl: null expression");
  ixs_node *node = ixs_import_node(session(), expr.raw());
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
  ixs_writer writer = {&StringWriter::write, &sink};
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
  ixs_reader reader = {&StringReader::read, &StringReader::remaining, &source};
  ixs_node *node = ixs_deserialize_node(session(), &reader);
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

inline Expr pw(std::initializer_list<std::pair<Expr, Expr>> branches) {
  if (branches.size() == 0)
    throw std::invalid_argument("pw requires at least one branch");
  ixs_ctx *ctx = branches.begin()->first.raw_ctx();
  std::vector<ixs_node *> vals, conds;
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
