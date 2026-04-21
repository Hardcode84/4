/* SPDX-FileCopyrightText: 2026 ixsimpl contributors
 * SPDX-License-Identifier: Apache-2.0
 */
#ifndef IXSIMPL_HPP
#define IXSIMPL_HPP

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
  static Expr sym(Context &ctx, const char *name) {
    return Expr(ctx.raw(), ctx.session(), ixs_sym(ctx.session(), name));
  }
  static Expr integer(Context &ctx, int64_t v) {
    return Expr(ctx.raw(), ctx.session(), ixs_int(ctx.session(), v));
  }
  static Expr rational(Context &ctx, int64_t p, int64_t q) {
    return Expr(ctx.raw(), ctx.session(), ixs_rat(ctx.session(), p, q));
  }

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
  explicit operator bool() const {
    return node_ != nullptr && !ixs_is_error(node_);
  }

  ixs_node *raw() const { return node_; }
  ixs_ctx *raw_ctx() const { return ctx_; }
  ixs_session *raw_session() const { return session_; }

private:
  ixs_ctx *session_ctx() const { return ctx_; }
};

inline Expr Context::import_expr(const Expr &expr) {
  if (!expr.raw())
    throw std::invalid_argument("ixsimpl: null expression");
  ixs_node *node = ixs_import_node(session(), expr.raw());
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
