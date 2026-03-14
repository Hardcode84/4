#ifndef IXSIMPL_HPP
#define IXSIMPL_HPP

#include <ixsimpl.h>
#include <stdexcept>
#include <string>
#include <string_view>
#include <vector>

namespace ixs {

class Context {
  ixs_ctx *ctx_;

public:
  Context() : ctx_(ixs_ctx_create()) {
    if (!ctx_)
      throw std::bad_alloc();
  }
  ~Context() { ixs_ctx_destroy(ctx_); }
  Context(const Context &) = delete;
  Context &operator=(const Context &) = delete;
  ixs_ctx *raw() const { return ctx_; }

  size_t nerrors() const { return ixs_ctx_nerrors(ctx_); }
  const char *error(size_t i) const { return ixs_ctx_error(ctx_, i); }
  void clear_errors() { ixs_ctx_clear_errors(ctx_); }
};

class Expr {
  ixs_ctx *ctx_;
  ixs_node *node_;

public:
  Expr(ixs_ctx *ctx, ixs_node *node) : ctx_(ctx), node_(node) {}

  static Expr parse(Context &ctx, std::string_view input) {
    return Expr(ctx.raw(), ixs_parse(ctx.raw(), input.data(), input.size()));
  }
  static Expr sym(Context &ctx, const char *name) {
    return Expr(ctx.raw(), ixs_sym(ctx.raw(), name));
  }
  static Expr integer(Context &ctx, int64_t v) {
    return Expr(ctx.raw(), ixs_int(ctx.raw(), v));
  }
  static Expr rational(Context &ctx, int64_t p, int64_t q) {
    return Expr(ctx.raw(), ixs_rat(ctx.raw(), p, q));
  }

  Expr simplify(const Expr *assumptions, size_t n) const {
    std::vector<ixs_node *> raw(n);
    for (size_t i = 0; i < n; ++i)
      raw[i] = assumptions[i].raw();
    return Expr(ctx_, ixs_simplify(ctx_, node_, raw.data(), n));
  }
  Expr simplify() const {
    return Expr(ctx_, ixs_simplify(ctx_, node_, nullptr, 0));
  }
  Expr subs(Expr target, Expr repl) const {
    return Expr(ctx_, ixs_subs(ctx_, node_, target.node_, repl.node_));
  }

  Expr operator+(Expr rhs) const {
    return Expr(ctx_, ixs_add(ctx_, node_, rhs.node_));
  }
  Expr operator*(Expr rhs) const {
    return Expr(ctx_, ixs_mul(ctx_, node_, rhs.node_));
  }
  Expr operator-(Expr rhs) const {
    ixs_node *neg = ixs_mul(ctx_, ixs_int(ctx_, -1), rhs.node_);
    return Expr(ctx_, ixs_add(ctx_, node_, neg));
  }
  Expr operator-() const {
    return Expr(ctx_, ixs_mul(ctx_, ixs_int(ctx_, -1), node_));
  }
  bool operator==(Expr rhs) const { return ixs_same_node(node_, rhs.node_); }

  Expr operator>=(Expr rhs) const {
    return Expr(ctx_, ixs_cmp(ctx_, node_, IXS_CMP_GE, rhs.node_));
  }
  Expr operator>(Expr rhs) const {
    return Expr(ctx_, ixs_cmp(ctx_, node_, IXS_CMP_GT, rhs.node_));
  }
  Expr operator<=(Expr rhs) const {
    return Expr(ctx_, ixs_cmp(ctx_, node_, IXS_CMP_LE, rhs.node_));
  }
  Expr operator<(Expr rhs) const {
    return Expr(ctx_, ixs_cmp(ctx_, node_, IXS_CMP_LT, rhs.node_));
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
};

inline Expr floor(Expr x) {
  return Expr(x.raw_ctx(), ixs_floor(x.raw_ctx(), x.raw()));
}
inline Expr ceil(Expr x) {
  return Expr(x.raw_ctx(), ixs_ceil(x.raw_ctx(), x.raw()));
}
inline Expr mod(Expr a, Expr b) {
  return Expr(a.raw_ctx(), ixs_mod(a.raw_ctx(), a.raw(), b.raw()));
}
inline Expr max(Expr a, Expr b) {
  return Expr(a.raw_ctx(), ixs_max(a.raw_ctx(), a.raw(), b.raw()));
}
inline Expr min(Expr a, Expr b) {
  return Expr(a.raw_ctx(), ixs_min(a.raw_ctx(), a.raw(), b.raw()));
}
inline Expr xor_(Expr a, Expr b) {
  return Expr(a.raw_ctx(), ixs_xor(a.raw_ctx(), a.raw(), b.raw()));
}

} // namespace ixs

#endif /* IXSIMPL_HPP */
