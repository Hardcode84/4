# Validation and Project Evolution

[Design index](DESIGN.md)

## Implementation Plan

The flat associative transition is one focused change:

1. Replace the binary/logic payloads with `u.assoc` and add the five `*_many`
   constructors plus shared flatten/sort support.
2. Make MAX/MIN, XOR, AND, and OR reductions operate on complete arrays.
3. Move hashing, equality, traversal, proofs, printing, import, rewrite,
   substitution, and bindings to the common associative accessors.
4. Emit version 2 counted lists and reject every other wire version.
5. Regenerate the amalgamation and run C, Python, fuzz, corpus, and benchmark
   gates.

The phase list below describes the engine as implemented today. The
session/store section above is an API and lifetime refactor over the same core,
not a restart from Phase 1.

### Phase 1: Foundation

- Arena allocator
- Rational arithmetic with full test coverage (floored division/Mod)
- Node types, hash-consing table, symbol interning
- Canonical Add/Mul construction with flattening and term collection
- Basic constant folding
- SymPy-format printer
- Seed `test/corpus_expected.txt` by running SymPy on all 615 corpus
  expressions (one-time script `scripts/gen_expected.py`, checked in). The
  script reads `corpus.txt` and `corpus_assumptions.txt`, applies the
  `Mod(p, q, evaluate=False)` workaround (see SymPy #28744 section), and
  writes one simplified expression per line. The SymPy version is pinned in
  `scripts/requirements-gen.txt` (e.g., `sympy==1.14.0`). Audited canonical
  refinements may update individual checked-in lines when SymPy retains an
  equivalent expression or does not model poison refinement.

**Milestone**: Can construct `3*x + 2*x + 1` and get `5*x + 1`. Corpus
expected outputs are available for comparison.

### Phase 2: Parser + Floor/Ceil/Mod

- Recursive descent parser for the full grammar
- `floor()`, `ceiling()` constructors with basic rules
- `Mod()` constructor with basic rules
- `Max()`, `Min()`, `xor()` constructors

**Milestone**: Can parse and round-trip all 615 expressions. Simplification of
constant subexpressions works.

### Phase 3: Piecewise + Boolean

- Piecewise node type with condition simplification
- Boolean algebra (And/Or/Not) with basic simplification
- Comparison normalization
- Piecewise propagation through arithmetic

**Milestone**: Expressions with Piecewise are simplified correctly. Many
expressions in the corpus should already simplify significantly.

### Phase 4: Advanced Rules + Bound Analysis

- Bound tracking infrastructure
- Domain-aware floor/ceil/Mod rules
- Batch simplification mode
- Full test against corpus
- Benchmark against SymPy baseline

**Milestone**: All 615 expressions produce correct results. Performance target
met (< 50ms total).

The corpus runner also reports how many expressions simplify to the canonical
integer constants 0 or 1. This zero/one residual count is a quality metric:
lower counts expose lost simplification even when every result remains
semantically correct.

### Phase 5: Bindings

- C++ header-only wrapper (`ixsimpl.hpp`)
- CPython extension module (`_ixsimpl.c`)
- Python test suite comparing output against SymPy
- `pyproject.toml` for pip-installable package

**Milestone**: `pip install .` works; Python tests pass against SymPy oracle.

### Phase 6: Hardening

- Fuzz testing (generate random expressions, verify against SymPy)
- Edge cases: overflow, division by zero, degenerate Piecewise
- C code output mode
- Documentation

## Testing Strategy

1. **Unit tests**: Each rule in isolation (test_rational, test_simplify).
2. **Corpus test**: Parse all 615 expressions, simplify, and verify the exact
   checked-in canonical outputs. The initial outputs come from SymPy; audited
   poison refinements and branch-local proofs may be more canonical.

   **Corpus file format** — `corpus.txt` uses one expression per non-blank
   line, prefixed with timing info: `simplify time: X.XXXXs: <expression>`.
   The loader strips the prefix up to and including the second `: ` to extract
   the raw expression. Blank lines are skipped.
   `corpus_expected.txt` contains one simplified expression per line,
   aligned 1:1 with the non-blank lines of `corpus.txt` (same count, same
   order). Lines that SymPy cannot simplify are copied verbatim.

   **Corpus assumptions** — The corpus test uses the following fixed
   assumption set (matching the kernel's known variable ranges):

   ```
   $T0 >= 0, $T0 < 256
   $T1 >= 0, $T1 < 4
   $T2 >= 0
   $WG0 >= 0, $WG1 >= 0
   $GPR_NUM >= 0
   M >= 1, N >= 1, K >= 1
   _M_div_32 >= 0, _N_div_32 >= 0, _K_div_256 >= 0
   $ARGK >= 0
   $MMA_ACC >= 0, $MMA_LHS_SCALE >= 0, $MMA_RHS_SCALE >= 0
   $MMA_SCALE_FP4 >= 0
   $index0 >= 0, $index1 >= 0
   _aligned >= 0
   ```

   These are stored in `test/corpus_assumptions.txt` (one assumption per
   line, same syntax as the parser accepts) and loaded by the corpus test
   and the `corpus_expected.txt` generation script. Using a shared
   assumption file ensures SymPy and ixsimpl see identical constraints.
3. **Equivalence oracle**: For any simplified expression `s` from input `e`,
   substitute random values for all variables and check equality wherever `e`
   is defined. This catches bugs without requiring exact output matching.
4. **Negative/error-path tests**: Verify correct behavior for invalid inputs:
   - Parse errors: `"foo bar +"` → `IXS_PARSE_ERROR`
   - Depth limit: deeply nested input → `IXS_PARSE_ERROR`
   - Domain error in parsed input: `"1/0 + x"` → `IXS_ERROR`
   - Division by zero via API: `ixs_mod(s, x, zero)` → `IXS_ERROR`
   - Integer literal overflow: `"99999999999999999999"` → `IXS_ERROR`
   - `ixs_rat(s, 1, 0)` → `IXS_ERROR`
   - NULL propagation: `ixs_add(s, NULL, x)` → NULL
   - Sentinel propagation: `ixs_floor(s, sentinel)` → same sentinel, no new error
   - Piecewise sentinel in dead branch: drops cleanly
   - `ixs_is_error` true for both, `ixs_is_parse_error` / `ixs_is_domain_error` specific
5. **Associative tests**: Every permutation and parenthesization of
   MAX/MIN/XOR/AND/OR has the same pointer; XOR parity, AND/OR idempotence,
   poison refinement, and version rejection are covered directly.
6. **Fuzz testing**: Hypothesis-based (see below).
7. **Benchmark**: Time all 615 expressions, compare against SymPy baseline.
   `bench_corpus --batch` measures shared-cache batch simplification;
   no argument measures independent calls.
   Track regressions in CI.  `bench/bench_sympy.py` runs ixsimpl vs
   `sympy.simplify` and `sympy.cancel` on the full corpus.  Typical
   results: ixsimpl ~23 ms total vs sympy.cancel ~25 s (~1000x) and
   sympy.simplify ~1000 s (~45000x).

### Fuzz Testing with Hypothesis

Property-based fuzz testing uses Python's
[Hypothesis](https://hypothesis.readthedocs.io/) library to generate random
expressions within the grammar, simplify them with both ixsimpl and SymPy,
and verify equivalence via numerical evaluation.

Proof-specific generators also build small, complete integer domains rather
than relying on sampled points. The combined symbolic-proof property mixes
bounded related and unrelated nested `Mod` chains, signed integer and rational
coefficients, floor partitions, congruent and incongruent radix
reconstructions, and arithmetic at both int64 boundaries. Every reported range
must contain every reachable value, and every successful equality or predicate
proof must hold throughout the domain. One-shot assumptions and reusable facts
are queried against the same semantic oracle.

```python
import random
from hypothesis import given, strategies as st, settings, assume
import sympy
import ixsimpl

# Strategy: generate random expression trees within the grammar
sym_names = st.sampled_from(["x", "y", "z", "w"])
small_ints = st.integers(min_value=-64, max_value=64)
pos_ints = st.integers(min_value=1, max_value=32)

@st.composite
def expressions(draw, max_depth=4):
    if max_depth <= 0 or draw(st.booleans()):
        return draw(st.one_of(sym_names, small_ints))
    ops = _OPS_WITH_PW if include_piecewise else _OPS_BASE
    op = draw(st.sampled_from(ops))
    a = draw(expressions(max_depth=max_depth - 1))
    if op in ("floor", "ceiling"):
        return (op, a)
    b = draw(expressions(max_depth=max_depth - 1))
    if op == "mod":
        b = draw(pos_ints)  # modulus must be positive
    if op == "div":
        b = draw(pos_ints)  # divisor must be nonzero
    if op == "piecewise":
        cond = draw(conditions(max_depth=max_depth - 1))
        default = draw(expressions(max_depth=max_depth - 1))
        return ("piecewise", a, cond, default)
    return (op, a, b)

@st.composite
def conditions(draw, max_depth=2):
    if max_depth <= 0 or draw(st.booleans()):
        a = draw(expressions(max_depth=2))
        b = draw(expressions(max_depth=2))
        op = draw(st.sampled_from([">=", ">", "<=", "<", "==", "!="]))
        return ("cmp", op, a, b)
    combiner = draw(st.sampled_from(["and", "or", "not"]))
    c1 = draw(conditions(max_depth=max_depth - 1))
    if combiner == "not":
        return ("not", c1)
    c2 = draw(conditions(max_depth=max_depth - 1))
    return (combiner, c1, c2)

def to_sympy(tree):
    """Convert expression tree to SymPy expression."""
    ...

def to_ixsimpl(ctx, tree):
    """Convert expression tree to ixsimpl expression."""
    ...

def eval_expr(tree, env):
    """Evaluate expression tree numerically using Python arithmetic.
    Raises ZeroDivisionError/ValueError on undefined operations."""
    ...

def eval_ixs(expr, ctx, env):
    """Evaluate ixsimpl Expr by substituting all variables via subs,
    then reading the resulting integer constant.
    Returns int or raises ValueError if result is not a constant/integer."""
    result = expr.subs({name: ctx.int_(val) for name, val in env.items()})
    if result.is_error:
        raise ValueError("sentinel")
    # Expr.__int__ returns IXS_INT value; raises TypeError for non-INT nodes
    # (including IXS_RAT — valid index expressions always reduce to integers)
    try:
        return int(result)
    except TypeError:
        raise ValueError(f"result is not an integer constant: {result}")

_VARS = ["x", "y", "z", "w"]

def _env_st(lo=1, hi=100):
    return st.fixed_dictionaries({v: st.integers(lo, hi) for v in _VARS})

@given(expr=expressions(), envs=st.lists(_env_st(0, 100), min_size=1, max_size=10))
@settings(max_examples=10000)
def test_simplify_matches_numerical(expr, envs):
    """Simplification preserves semantics: evaluate original and simplified
    at random points, check they agree."""
    ctx = ixsimpl.Context()
    ixs_expr = to_ixsimpl(ctx, expr)
    assume(not ixs_expr.is_error)  # skip if construction hit domain error
    ixs_simplified = ixs_expr.simplify()
    assume(not ixs_simplified.is_error)  # skip if simplification hit error

    for env in envs:
        try:
            orig = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError):
            continue  # skip points where original is undefined
        simp = eval_ixs(ixs_simplified, ctx, env)
        assert orig == simp, f"Mismatch: {orig} != {simp} at {env}"

@given(expr=expressions(), envs=st.lists(_env_st(), min_size=1, max_size=10))
@settings(max_examples=5000)
def test_matches_sympy(expr, envs):
    """Cross-check against SymPy: both should produce numerically
    equivalent results."""
    ctx = ixsimpl.Context()
    ixs_result = to_ixsimpl(ctx, expr).simplify()
    assume(not ixs_result.is_error)

    sp_expr = to_sympy(expr)
    sp_result = sympy.simplify(sp_expr)

    for env in envs:
        try:
            ixs_val = eval_ixs(ixs_result, ctx, env)
            sp_val = int(sp_result.subs({sympy.Symbol(k): v for k, v in env.items()}))
        except (ZeroDivisionError, ValueError, TypeError):
            continue
        assert ixs_val == sp_val, f"Divergence at {env}"
```

**Known SymPy bug to work around**: SymPy issue
[#28744](https://github.com/sympy/sympy/issues/28744) — `Mod` incorrectly
squares inner `Mod` subexpressions when the variable has `integer=True`
assumption. The bug is in `sympy/core/mod.py` lines 166-172: factors of type
`Mod` are duplicated into both `mod_l` and `non_mod_l`, causing them to
appear squared. The fix (merged to `master` in Dec 2025) has not been included
in any SymPy release yet (latest release is 1.14.0, April 2025).

Concrete workarounds for the fuzz test oracle:

1. **Reconstruct Mod with `evaluate=False`** when using SymPy as oracle.
   The bug is in SymPy's auto-evaluation of `Mod()` — when `integer=True`
   symbols are present, `Mod(k*Mod(x,n), m)` silently squares the inner
   Mod factor. The fix (from IREE Wave's `_bounds_simplify_once`) is to
   rebuild Mod nodes with `sympy.Mod(p, q, evaluate=False)` after
   simplifying their arguments, bypassing the buggy code path. This lets
   us keep `integer=True` on symbols (which is needed for other SymPy
   rewrites to fire) while avoiding the specific Mod bug. Non-Mod nodes
   are reconstructed normally via `expr.func(*simplified_args)`.
2. **Primary oracle is numerical evaluation**, not SymPy's symbolic output.
   For each test case, substitute 10+ random integer values into both the
   original and simplified expressions and check equality. This catches bugs
   in both SymPy and ixsimpl independently.
3. **Pin SymPy version** for `corpus_expected.txt` generation and document it.
   When a new SymPy release includes the fix, re-generate and note the
   version.
4. **Hypothesis `@example` decorators** for the specific pattern from #28744:
   `Mod(2*Mod(x, 3), 5)` — ensure this is always tested and known to
   diverge from buggy SymPy.

## Risks and Mitigations

| Risk | Impact | Mitigation |
|---|---|---|
| Simplification produces wrong results | Critical | Numerical equivalence oracle; fuzz testing |
| 64-bit rational overflow | Medium | Checked arithmetic plus portable emulated 128-bit compare fallback; constructors still return sentinel + error list on overflow |
| New expression patterns in future workloads | Medium | Grammar is extensible; add new node types as needed |
| Hash-consing table becomes bottleneck | Low | Linear probing with power-of-2 sizing; rehash threshold 70% |
| Simplification rules interact badly (infinite loops) | Medium | Fixed-point iteration limit (64); monotonically size-reducing rules |

## Future Ideas

- **Arena-backed hash table.** Replace the `calloc`/`free`-managed hash
  table with arena-allocated non-contiguous blocks (sizes S, S, 2S, 4S,
  8S, ...).  Old blocks remain live after resize (total capacity doubles by
  appending one new block), so there is zero arena waste.  Linear index
  decomposition to (block, offset) is O(1) via highest-bit.  Trade-off:
  extra indirection per probe and cross-block cache misses on long chains.
  Enables a fully `malloc`-free library where `ixs_ctx_destroy` is just
  two `ixs_arena_destroy` calls.

## Non-Goals

- General symbolic algebra (polynomial factoring, GCD, etc.)
- Floating-point arithmetic
- Calculus (differentiation, integration, series)
- Trigonometric or transcendental functions
- Matrix operations
- Equation solving
- Bindings beyond C++ and Python
