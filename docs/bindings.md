# Language Bindings

[Design index](DESIGN.md)

The binding sketches below mirror the current session-based API. `Context`
owns the long-lived store plus an embedded reusable session, and node-producing
operations route through that session. The code blocks are illustrative
subsets, not exhaustive dumps of the shipped wrapper surface; consult
`bindings/cpp/ixsimpl.hpp` and the Python stubs for the full API.

## C++ Binding — `ixsimpl.hpp`

A thin header-only RAII wrapper over the C API. No additional runtime cost.

```cpp
namespace ixs {

class Context {
    ixs_ctx *ctx_;
    ixs_session session_;
public:
    Context() : ctx_(ixs_ctx_create()) {
        if (!ctx_) throw std::bad_alloc();
        ixs_session_init(&session_, ctx_);
    }
    ~Context() {
        ixs_session_destroy(&session_);
        ixs_ctx_destroy(ctx_);
    }
    Context(const Context&) = delete;
    Context& operator=(const Context&) = delete;

    ixs_ctx *raw() const { return ctx_; }
    ixs_session *session() { return &session_; }
    const ixs_session *session() const { return &session_; }

    size_t nerrors() const { return ixs_session_nerrors(&session_); }
    const char *error(size_t i) const { return ixs_session_error(&session_, i); }
    void clear_errors() { ixs_session_clear_errors(&session_); }
};

class Expr {
    ixs_ctx *ctx_;
    ixs_session *session_;
    const ixs_node *node_;
public:
    Expr(ixs_ctx *ctx, ixs_session *session, const ixs_node *node)
        : ctx_(ctx), session_(session), node_(node) {}

    static Expr parse(Context &ctx, std::string_view input) {
        return {ctx.raw(), ctx.session(),
                ixs_parse(ctx.session(), input.data(), input.size())};
    }
    static Expr parse_expr(Context &ctx, std::string_view input) {
        return {ctx.raw(), ctx.session(),
                ixs_parse_expr(ctx.session(), input.data(), input.size())};
    }
    static Expr parse_pred(Context &ctx, std::string_view input) {
        return {ctx.raw(), ctx.session(),
                ixs_parse_pred(ctx.session(), input.data(), input.size())};
    }
    static Expr sym(Context &ctx, const char *name) {
        return {ctx.raw(), ctx.session(), ixs_sym(ctx.session(), name)};
    }
    static Expr integer(Context &ctx, int64_t v) {
        return {ctx.raw(), ctx.session(), ixs_int(ctx.session(), v)};
    }

    Expr simplify(const Expr *assumptions, size_t n_assumptions) const {
        std::vector<const ixs_node*> raw(n_assumptions);
        for (size_t i = 0; i < n_assumptions; i++)
            raw[i] = assumptions[i].raw();
        return {ctx_, session_,
                ixs_simplify(session_, node_, raw.data(), raw.size())};
    }
    Expr simplify() const {
        return {ctx_, session_, ixs_simplify(session_, node_, nullptr, 0)};
    }
    Expr subs(Expr target, Expr repl) const {
        return {ctx_, session_,
                ixs_subs(session_, node_, target.node_, repl.node_)};
    }

    Expr operator+(Expr rhs) const {
        return {ctx_, session_, ixs_add(session_, node_, rhs.node_)};
    }
    Expr operator-(Expr rhs) const {
        const ixs_node *neg =
            ixs_mul(session_, ixs_int(session_, -1), rhs.node_);
        return {ctx_, session_, ixs_add(session_, node_, neg)};
    }
    Expr operator*(Expr rhs) const {
        return {ctx_, session_, ixs_mul(session_, node_, rhs.node_)};
    }
    Expr operator-() const {
        return {ctx_, session_,
                ixs_mul(session_, ixs_int(session_, -1), node_)};
    }
    bool operator==(Expr rhs) const { return node_ == rhs.node_; }

    std::string str() const {
        if (!node_) return {};
        size_t n = ixs_print(node_, nullptr, 0);
        if (n == SIZE_MAX) throw std::bad_alloc();
        std::string s(n + 1, '\0');
        if (ixs_print(node_, s.data(), n + 1) == SIZE_MAX)
            throw std::bad_alloc();
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
    explicit operator bool() const { return node_ && !ixs_is_error(node_); }

    const ixs_node *raw() const { return node_; }
    ixs_ctx *raw_ctx() const { return ctx_; }
    ixs_session *raw_session() const { return session_; }
};

} // namespace ixs
```

Key properties:
- `Context` owns both the long-lived store and one embedded reusable session.
  RAII cleans up both on destruction. Constructor throws `std::bad_alloc` on
  OOM.
- `Expr` is a lightweight value type (three pointers: store, session, node).
  Cheap to copy. **`Expr` must not outlive its `Context`** — destroying a
  `Context` invalidates all `Expr` values created from it (dangling pointers).
- `operator bool()` returns `true` only for valid, non-error expressions.
  `is_null()` checks OOM, `is_parse_error()`/`is_domain_error()` check
  specific sentinels, `is_error()` checks either.
- `parse_expr()` and `parse_pred()` expose the kind-aware parse surface;
  `parse()` remains the backward-compatible expression parser.
- `Expr::is_integer_valued()` exposes structural classification, while
  `Expr::check()`, `check_integer_valued()`, `check_defined()`,
  `get_pow2_fact()`, and `range()` consume an optional assumption array.
  `Expr::expand()` exposes distribution. `Context::facts()` returns a
  lightweight session-owned `Facts` wrapper whose `assume_range()` and
  `derive_affine()` expose explicit range ingestion and whose `simplify()`,
  `simplify_batch()`, `check()`, `check_integer_valued()`, `check_defined()`,
  `check_divisible()`, `get_pow2_fact()`, and `range()` expose every
  fact-backed transform and core proof query.
  `get_known_bits()`, `get_symbol_congruence()`, and `check_congruent()` expose
  the low-64 and query-specific modular interfaces without adding wrapper-side
  reasoning. `Facts::substitute()` and `Facts::substitute_multi()` mutate a
  destination wrapper from a source fact set and mirror the transactional C
  transfer contract.
  `Expr::simplify(const Facts&)` is the expression-oriented spelling.
  `Facts::try_exact_divide()` returns an `ExactDivideResult` containing the
  four-way status and a nullable `Expr` quotient; errors remain available
  through the owning `Context` diagnostics.
  `Facts::affine_decompose()` and `split_additive_constant()` mirror the narrow
  fact-backed C helpers and fill their output references only on success.
  Constant and finite differences use ordinary `Expr` subtraction,
  substitution, optional expansion, and `Facts::simplify()`.
- `Expr::raw()` returns `const ixs_node *`. `Expr::raw_const()` remains as a
  compatibility alias, but neither method offers a mutable node handle.
- Operator overloading for natural expression building.
- Range overloads for MAX/MIN/XOR/AND/OR use one temporary contiguous buffer
  and call one `*_many` function; binary operators allocate no wrapper storage.
- Simplification adds no C++-side heap allocation. (`str()` and range
  construction allocate their result/temporary buffers.)
- NULL and sentinel propagate through operators (same as C API).
- **Cross-context contract** applies: all `Expr` values passed to an
  operation (including assumptions in `simplify()`) must belong to the
  same `Context`. Mixing contexts is undefined behavior.

## Python Binding — `_ixsimpl.c`

A CPython C extension module (no pybind11/ctypes dependency). Exposes three
Python types: `Context`, `Expr`, and `Facts`.

```python
import ixsimpl

ctx = ixsimpl.Context()

T0 = ctx.sym("$T0")
M  = ctx.sym("M")
assumptions = [T0 >= 0, T0 < 256, M >= 1]

expr = ctx.parse("128*floor($T0/64) + 4*floor(Mod($T0, 64)/16)")
result = expr.simplify(assumptions=assumptions)
print(result)              # SymPy-compatible string
print(result.to_c())       # C code string

facts = ctx.facts()
for assumption in assumptions:
    facts.assume(assumption)
result = expr.simplify(facts=facts)
batch = [expr, x % 16]
ctx.simplify_batch(batch, facts=facts)

# Programmatic construction
x = ctx.sym("x")
y = ctx.sym("y")
e = ixsimpl.floor(x + y) + 3
print(e.simplify(assumptions=assumptions))

# Module-level convenience functions
e2 = x % 4                  # equivalent to ixsimpl.mod(x, 4)
e3 = ixsimpl.max_(x, y)   # trailing _ avoids shadowing builtin max
e4 = ixsimpl.min_(x, y)
e5 = ixsimpl.pw((x, x >= 0), (-x, ctx.true_()))  # piecewise
cond = ixsimpl.and_(x >= 0, y >= 0)               # bitwise on 0/1 predicates
cond2 = ixsimpl.or_(x >= 0, y >= 0)
mask = x & 3                  # equivalent to ixsimpl.and_(x, 3)
flags = x | y                 # equivalent to ixsimpl.or_(x, y)
cond3 = ixsimpl.not_(x >= 0)
e5 = ixsimpl.ceil(x / 4)

# Batch
exprs = [ctx.parse(line) for line in lines]
ctx.simplify_batch(exprs, assumptions=assumptions)

# First-class expression range facts
facts = ctx.facts()
orig = ctx.sym("orig")
A = ctx.sym("A")
B = ctx.sym("B")
facts.assume_range(orig, 0, 1073741815)
facts.derive_affine(orig, 2, 0, 2*orig)
subst_facts = facts.subs(orig, A + 8*B)
print(ctx.range(2*A + 16*B, facts=subst_facts))  # (0, 2147483630)

# Mapping form is simultaneous: the replacement A is not rewritten to B.
multi_facts = facts.subs({orig: A, A: B})
```

Implementation:
- `_ixsimpl.c` is a single-file CPython extension module written in plain C.
- `Context` Python object owns both `ixs_ctx*` and an embedded `ixs_session`;
  destructor destroys the session and then the store.
- `Expr` Python object holds a reference to its `Context` (preventing
  premature GC) and wraps `ixs_node*`.
- `__repr__` and `__str__` call `ixs_print`. Sentinel prints as `"<error>"`;
  traversal-arena OOM raises `MemoryError`.
- `__int__` returns the integer value if the node is `IXS_INT`; raises
  `TypeError` otherwise. Used by `eval_ixs` for numerical evaluation.
- `__eq__` is pointer comparison (O(1) via hash-consing).
- `__hash__` returns the node's precomputed hash.
- `Expr.is_error` property — `True` for either sentinel.
- `Expr.is_parse_error` / `Expr.is_domain_error` — specific checks.
- `Expr.is_expr` / `Expr.is_pred` — root-kind checks. Predicate values are also
  expressions; `is_pred` means the node is known to produce only `0` or `1`.
- `Expr.is_integer_valued` — conservative structural integrality, without
  assumptions or facts.
- `Expr.node_ptr` — raw `ixs_node*` address exposed as a Python `int`.
  This is for identity/debug/FFI plumbing only.  It is not a stable semantic
  ID, and it is only meaningful while the owning `Context` is alive.
- `Context.errors` property — returns list of error strings; `Context.clear_errors()` resets.
- `Context.parse()` remains the backward-compatible expression parser.
  `Context.parse_expr()` and `Context.parse_pred()` expose the kind-aware parse
  entry points.
- `Context.check(expr, assumptions=[...])` returns `True`, `False`, or `None`
  for interval and modular-congruence entailment checks.  `Context.range(expr,
  assumptions=[...])` returns `(lower, upper)` from the same interval engine,
  or `None` when unknown.  Endpoints are Python `int`,
  `fractions.Fraction`, or `None` for an unbounded side.
- `Context.integer_valued(expr, assumptions=[...])` and the alternative
  `facts=...` form expose tri-state integrality. `Context.divisible(expr,
  modulus, facts)` exposes fact-backed tri-state divisibility and raises
  `ValueError` for modulus zero.
- `Context.known_bits(expr, facts)` returns
  `(known_zero, known_one, pow2)` for a valid query, including `(0, 0, None)`
  when nothing is known. `Context.symbol_congruence(symbol, facts)` returns the
  stored `(modulus, residue)` or `None`. `Context.congruent(expr, modulus,
  residue, facts)` returns tri-state `True`, `False`, or `None`; modulus zero
  raises `ValueError`.
- `Context.try_exact_divide(expr, divisor, facts)` returns
  `("proven", quotient)`, `("not_exact", None)`, or `("unknown", None)`.
  Core `ERROR` results raise `ValueError` for domain/representation failures
  and `MemoryError` for OOM while preserving the session diagnostic.
- `Context.affine_decompose(expr, symbol, facts)` returns
  `(coefficient, residual)` or `None`;
  `Context.split_additive_constant(...)`
  returns `(residual, constant)` or `None`. Invalid contexts, sentinels, and
  non-symbol affine targets raise `ValueError`; valid but unmatched queries do
  not add diagnostics. Constant and finite differences are composed from
  `Expr` subtraction, `subs()`, `expand()`, and fact-backed `simplify()`.
- `Context.check_predicate(predicate, facts)` and
  `Context.equivalent(lhs, rhs, facts)` expose conservative tri-state results
  as `True`, `False`, or `None`.
- `Context.facts()` creates a session-owned `Facts` object.  `Facts.assume()`
  imports predicates, `Facts.assume_range()` attaches direct expression
  ranges, `Facts.derive_affine()` transfers ranges through
  `scale*base + offset`, and `Facts.subs()` accepts either one pair or a
  simultaneous substitution dictionary. It transfers ranges and only the
  congruence, known-bit, and power-of-two facts justified by each replacement.
  `Context.check`, `Context.range`,
  `Context.integer_valued`, and `Context.pow2_fact` accept `facts=...` as an
  alternative to `assumptions=[...]`; `Context.divisible` requires a fact set.
- Every Python `assumptions=[...]` entry and `Facts.assume()` predicate must be
  a CMP, a canonical boolean constant, or an AND tree with those leaves.
  Unsupported or malformed predicate shapes raise `ValueError`; a failed
  `Facts.assume()` leaves prior facts unchanged.
- Operator overloading: `__add__`, `__mul__`, `__sub__`, `__mod__`, `__and__`,
  `__or__`, `__neg__`, `__ge__`, `__gt__`, `__le__`, `__lt__`, `__eq__`
  (comparisons return
  `Expr` nodes, not Python `bool`, so they can be used as assumptions).
- `Context.int_(val)` creates an `IXS_INT` node (wraps `ixs_int`).
- NULL (OOM) raises `MemoryError`. Sentinel propagates as a regular Expr.
- Module-level functions: `ixsimpl.floor()`, `ixsimpl.ceil()`,
  `ixsimpl.mod()`, variadic `ixsimpl.max_()`, `ixsimpl.min_()`,
  `ixsimpl.xor_()`, `ixsimpl.and_()`, `ixsimpl.or_()`, `ixsimpl.not_()`,
  `ixsimpl.pw((val, cond), ...)`.
  Trailing underscore on `max_`/`min_`/`xor_`/`and_`/`or_`/`not_` avoids
  shadowing Python builtins.
- Variadic associative functions validate one context and issue one `*_many`
  call; they do not left-fold through Python operators.
- `pyproject.toml` builds the extension; no runtime dependencies.

This binding adds ~800 lines of C and is the primary interface for testing
against SymPy (run both, compare outputs).
