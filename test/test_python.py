# SPDX-FileCopyrightText: 2026 ixsimpl contributors
# SPDX-License-Identifier: Apache-2.0
"""
Fuzz tests for ixsimpl using Hypothesis.

Properties tested:
1. Self-consistency: simplification preserves numerical semantics.
2. Cross-check: ixsimpl agrees with SymPy on random expressions.
3. Divisibility: simplification with Mod(sym, d)==0 preserves semantics
   at evaluation points satisfying the assumption.
4. to_sympy semantics: ixsimpl.sympy_conv.to_sympy produces SymPy
   expressions that agree numerically with ixsimpl evaluation.
5. from_sympy semantics: ixsimpl.sympy_conv.from_sympy produces ixsimpl
   expressions that agree numerically with the original tree.
6. Roundtrip: ixsimpl -> to_sympy -> from_sympy -> ixsimpl preserves
   numerical semantics.
"""

from __future__ import annotations

import math
import warnings
from fractions import Fraction
from typing import Any

import ixsimpl
import sympy
from hypothesis import assume, example, given
from hypothesis import strategies as st
from ixsimpl.sympy_conv import from_sympy as conv_from_sympy
from ixsimpl.sympy_conv import to_sympy as conv_to_sympy

ExprTree = str | int | tuple[Any, ...]
CondTree = tuple[Any, ...]
Env = dict[str, int]

_VARS = ["x", "y", "z", "w", "a", "b", "c", "d"]


def _env_st(lo: int = 1, hi: int = 100) -> st.SearchStrategy[Env]:
    return st.fixed_dictionaries({v: st.integers(lo, hi) for v in _VARS})


def _wide_env_st() -> st.SearchStrategy[Env]:
    """Env strategy mixing negative, zero, and positive values."""
    return st.fixed_dictionaries(
        {v: st.one_of(st.integers(-100, -1), st.just(0), st.integers(1, 100)) for v in _VARS}
    )


# ---------------------------------------------------------------------------
#  Expression tree strategies
# ---------------------------------------------------------------------------

sym_names = st.sampled_from(_VARS)
small_ints = st.integers(min_value=-64, max_value=64)
pos_ints = st.integers(min_value=1, max_value=32)
small_rats = st.tuples(st.integers(min_value=-64, max_value=64), pos_ints).map(
    lambda pq: ("rat", pq[0], pq[1])
)


_OPS_BASE = ["add", "sub", "mul", "neg", "div", "floor", "ceiling", "mod", "max", "min", "xor"]
_OPS_WITH_PW = [*_OPS_BASE, "piecewise"]


@st.composite
def expressions(draw: st.DrawFn, max_depth: int = 6, include_piecewise: bool = True) -> ExprTree:
    # 30% early exit at depth>3, 50% at depth<=3.  Keeps deep trees possible
    # without dominating runtime: expression generation is the bottleneck at
    # depth 6 (65% of wall time at 50/50), and 30/70 cuts it roughly in half.
    if max_depth <= 0 or draw(
        st.sampled_from([True] * 3 + [False] * 7 if max_depth > 3 else [True, False])
    ):
        return draw(st.one_of(sym_names, small_ints, small_rats))
    ops = _OPS_WITH_PW if include_piecewise else _OPS_BASE
    op = draw(st.sampled_from(ops))
    a = draw(expressions(max_depth=max_depth - 1, include_piecewise=include_piecewise))
    if op in ("floor", "ceiling"):
        choice = draw(st.sampled_from(["div", "rat_add", "plain"]))
        if choice == "div":
            d = draw(pos_ints)
            return (op, ("div", a, d))
        if choice == "rat_add":
            rat_leaf = draw(small_rats)
            return (op, ("add", rat_leaf, a))
        return (op, a)
    if op == "neg":
        return (op, a)
    if op == "piecewise":
        cond = draw(conditions(max_depth=2))
        default = draw(expressions(max_depth=max_depth - 1, include_piecewise=include_piecewise))
        if draw(st.booleans()):
            b = draw(expressions(max_depth=max_depth - 1, include_piecewise=include_piecewise))
            cond2 = draw(conditions(max_depth=2))
            return (op, a, cond, b, cond2, default)
        return (op, a, cond, default)
    b = draw(expressions(max_depth=max_depth - 1, include_piecewise=include_piecewise))
    if op == "mod":
        b = draw(pos_ints)
    if op == "div":
        b = draw(pos_ints)
    if op == "xor":
        a = draw(st.integers(min_value=0, max_value=255))
        b = draw(st.integers(min_value=0, max_value=255))
    return (op, a, b)


@st.composite
def conditions(draw: st.DrawFn, max_depth: int = 2) -> CondTree:
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


# ---------------------------------------------------------------------------
#  Tree -> SymPy
# ---------------------------------------------------------------------------

_sp_syms = {n: sympy.Symbol(n, integer=True) for n in _VARS}


def to_sympy(tree: ExprTree) -> Any:
    if isinstance(tree, str):
        return _sp_syms[tree]
    if isinstance(tree, int):
        return sympy.Integer(tree)
    op = tree[0]
    if op == "rat":
        return sympy.Rational(tree[1], tree[2])
    if op == "add":
        return to_sympy(tree[1]) + to_sympy(tree[2])
    if op == "sub":
        return to_sympy(tree[1]) - to_sympy(tree[2])
    if op == "neg":
        return -to_sympy(tree[1])
    if op == "mul":
        return to_sympy(tree[1]) * to_sympy(tree[2])
    if op == "div":
        a, b = to_sympy(tree[1]), to_sympy(tree[2])
        return sympy.Rational(1, int(b)) * a if isinstance(b, sympy.Integer) else a / b
    if op == "floor":
        return sympy.floor(to_sympy(tree[1]))
    if op == "ceiling":
        return sympy.ceiling(to_sympy(tree[1]))
    if op == "mod":
        # evaluate=False avoids SymPy Mod bugs (e.g. #28744) that silently
        # produce wrong results for certain inputs.
        return sympy.Mod(to_sympy(tree[1]), to_sympy(tree[2]), evaluate=False)
    if op == "max":
        return sympy.Max(to_sympy(tree[1]), to_sympy(tree[2]))
    if op == "min":
        return sympy.Min(to_sympy(tree[1]), to_sympy(tree[2]))
    if op == "xor":
        raise ValueError("xor not supported in SymPy conversion")
    if op == "piecewise":
        ncases = (len(tree) - 2) // 2
        cases = [(to_sympy(tree[1 + 2 * i]), to_sympy_cond(tree[2 + 2 * i])) for i in range(ncases)]
        cases.append((to_sympy(tree[-1]), True))
        return sympy.Piecewise(*cases)
    raise ValueError(f"unknown op: {op}")


def to_sympy_cond(tree: CondTree) -> Any:
    op = tree[0]
    if op == "cmp":
        _, cmp_op, a, b = tree
        sa, sb = to_sympy(a), to_sympy(b)
        ops = {
            ">=": sympy.Ge,
            ">": sympy.Gt,
            "<=": sympy.Le,
            "<": sympy.Lt,
            "==": sympy.Eq,
            "!=": sympy.Ne,
        }
        return ops[cmp_op](sa, sb)
    if op == "not":
        return ~to_sympy_cond(tree[1])
    if op == "and":
        return to_sympy_cond(tree[1]) & to_sympy_cond(tree[2])
    if op == "or":
        return to_sympy_cond(tree[1]) | to_sympy_cond(tree[2])
    raise ValueError(f"unknown cond op: {op}")


# ---------------------------------------------------------------------------
#  Tree -> ixsimpl
# ---------------------------------------------------------------------------


def to_ixsimpl(ctx: ixsimpl.Context, tree: ExprTree) -> ixsimpl.Expr:
    if isinstance(tree, str):
        return ctx.sym(tree)
    if isinstance(tree, int):
        return ctx.int_(tree)
    op = tree[0]
    if op == "rat":
        return ctx.rat(tree[1], tree[2])
    if op == "add":
        return to_ixsimpl(ctx, tree[1]) + to_ixsimpl(ctx, tree[2])
    if op == "sub":
        return to_ixsimpl(ctx, tree[1]) - to_ixsimpl(ctx, tree[2])
    if op == "neg":
        return -to_ixsimpl(ctx, tree[1])
    if op == "mul":
        return to_ixsimpl(ctx, tree[1]) * to_ixsimpl(ctx, tree[2])
    if op == "div":
        return to_ixsimpl(ctx, tree[1]) / to_ixsimpl(ctx, tree[2])
    if op == "floor":
        return ixsimpl.floor(to_ixsimpl(ctx, tree[1]))
    if op == "ceiling":
        return ixsimpl.ceil(to_ixsimpl(ctx, tree[1]))
    if op == "mod":
        return ixsimpl.mod(to_ixsimpl(ctx, tree[1]), to_ixsimpl(ctx, tree[2]))
    if op == "max":
        return ixsimpl.max_(to_ixsimpl(ctx, tree[1]), to_ixsimpl(ctx, tree[2]))
    if op == "min":
        return ixsimpl.min_(to_ixsimpl(ctx, tree[1]), to_ixsimpl(ctx, tree[2]))
    if op == "xor":
        return ixsimpl.xor_(to_ixsimpl(ctx, tree[1]), to_ixsimpl(ctx, tree[2]))
    if op == "piecewise":
        ncases = (len(tree) - 2) // 2
        cases = [
            (to_ixsimpl(ctx, tree[1 + 2 * i]), to_ixsimpl_cond(ctx, tree[2 + 2 * i]))
            for i in range(ncases)
        ]
        cases.append((to_ixsimpl(ctx, tree[-1]), ctx.true_()))
        return ixsimpl.pw(*cases)
    raise ValueError(f"unknown op: {op}")


def to_ixsimpl_cond(ctx: ixsimpl.Context, tree: CondTree) -> ixsimpl.Expr:
    """Convert condition tree to ixsimpl Expr."""
    op = tree[0]
    if op == "cmp":
        _, cmp_op, a, b = tree
        ia, ib = to_ixsimpl(ctx, a), to_ixsimpl(ctx, b)
        if cmp_op == ">=":
            return ia >= ib
        if cmp_op == ">":
            return ia > ib
        if cmp_op == "<=":
            return ia <= ib
        if cmp_op == "<":
            return ia < ib
        if cmp_op == "==":
            return ctx.eq(ia, ib)
        if cmp_op == "!=":
            return ctx.ne(ia, ib)
        raise ValueError(f"unknown cmp_op: {cmp_op}")
    if op == "not":
        return ixsimpl.not_(to_ixsimpl_cond(ctx, tree[1]))
    if op == "and":
        return ixsimpl.and_(to_ixsimpl_cond(ctx, tree[1]), to_ixsimpl_cond(ctx, tree[2]))
    if op == "or":
        return ixsimpl.or_(to_ixsimpl_cond(ctx, tree[1]), to_ixsimpl_cond(ctx, tree[2]))
    raise ValueError(f"unknown cond op: {op}")


# ---------------------------------------------------------------------------
#  Numerical evaluation
# ---------------------------------------------------------------------------


def _floored_mod(a: Any, b: Any) -> Any:
    if b == 0:
        raise ZeroDivisionError
    return a % b


def eval_expr(tree: ExprTree, env: Env) -> Any:
    """Evaluate expression tree numerically using Python arithmetic."""
    if isinstance(tree, str):
        return env[tree]
    if isinstance(tree, int):
        return tree
    op = tree[0]
    if op == "rat":
        return Fraction(tree[1], tree[2])
    if op == "add":
        return eval_expr(tree[1], env) + eval_expr(tree[2], env)
    if op == "sub":
        return eval_expr(tree[1], env) - eval_expr(tree[2], env)
    if op == "neg":
        return -eval_expr(tree[1], env)
    if op == "mul":
        return eval_expr(tree[1], env) * eval_expr(tree[2], env)
    if op == "div":
        a, b = eval_expr(tree[1], env), eval_expr(tree[2], env)
        if b == 0:
            raise ZeroDivisionError
        return Fraction(a, b)
    if op == "floor":
        v = eval_expr(tree[1], env)
        return math.floor(v)
    if op == "ceiling":
        v = eval_expr(tree[1], env)
        return math.ceil(v)
    if op == "mod":
        return _floored_mod(eval_expr(tree[1], env), eval_expr(tree[2], env))
    if op == "max":
        return max(eval_expr(tree[1], env), eval_expr(tree[2], env))
    if op == "min":
        return min(eval_expr(tree[1], env), eval_expr(tree[2], env))
    if op == "xor":
        return int(eval_expr(tree[1], env)) ^ int(eval_expr(tree[2], env))
    if op == "piecewise":
        ncases = (len(tree) - 2) // 2
        for i in range(ncases):
            if eval_cond(tree[2 + 2 * i], env):
                return eval_expr(tree[1 + 2 * i], env)
        return eval_expr(tree[-1], env)
    raise ValueError(f"unknown op: {op}")


def eval_cond(tree: CondTree, env: Env) -> Any:
    """Evaluate condition tree to a bool."""
    op = tree[0]
    if op == "cmp":
        _, cmp_op, a, b = tree
        va, vb = eval_expr(a, env), eval_expr(b, env)
        if cmp_op == ">=":
            return va >= vb
        if cmp_op == ">":
            return va > vb
        if cmp_op == "<=":
            return va <= vb
        if cmp_op == "<":
            return va < vb
        if cmp_op == "==":
            return va == vb
        if cmp_op == "!=":
            return va != vb
        raise ValueError(f"unknown cmp_op: {cmp_op}")
    if op == "not":
        return not eval_cond(tree[1], env)
    if op == "and":
        return eval_cond(tree[1], env) and eval_cond(tree[2], env)
    if op == "or":
        return eval_cond(tree[1], env) or eval_cond(tree[2], env)
    raise ValueError(f"unknown cond op: {op}")


def _as_int(val: Any) -> int | None:
    """Coerce eval_expr result to int, or None if non-integer."""
    if isinstance(val, int):
        return val
    if isinstance(val, Fraction):
        return int(val) if val.denominator == 1 else None
    return None


def eval_ixs(expr: ixsimpl.Expr, ctx: ixsimpl.Context, env: Env) -> int:
    """Evaluate ixsimpl Expr by substituting all variables."""
    result = expr
    for name, val in env.items():
        result = result.subs(name, ctx.int_(val))
    if result.is_error:
        raise ValueError("sentinel")
    try:
        return int(result)
    except TypeError as e:
        raise ValueError(f"result is not an integer constant: {result}") from e


# ---------------------------------------------------------------------------
#  Fuzz tests
# ---------------------------------------------------------------------------


def test_expand_basic() -> None:
    """expand() distributes MUL over ADD."""
    ctx = ixsimpl.Context()
    e = ctx.parse("2*(a + b)")
    expanded = e.expand()
    s = str(expanded)
    assert "2*a" in s
    assert "2*b" in s
    assert "+" in s

    e2 = ctx.parse("(a + b)*(c + d)")
    s2 = str(e2.expand())
    for term in ("a*d", "c*a", "c*b", "d*b"):
        assert term in s2, f"missing {term} in {s2}"


@given(
    expr=expressions(),
    envs=st.lists(st.one_of(_env_st(0, 100), _wide_env_st()), min_size=1, max_size=10),
)
def test_simplify_self_consistency(expr: ExprTree, envs: list[Env]) -> None:
    """Simplification preserves semantics: evaluate original and simplified
    at random points, check they agree."""
    ctx = ixsimpl.Context()
    try:
        ixs_expr = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not ixs_expr.is_error)
    ixs_simplified = ixs_expr.simplify()
    assume(not ixs_simplified.is_error)

    checked = 0
    for env in envs:
        try:
            raw = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError):
            continue
        orig = _as_int(raw)
        if orig is None:
            continue
        simp = eval_ixs(ixs_simplified, ctx, env)
        assert orig == simp, f"Mismatch: {orig} != {simp} at {env}, expr={expr}"
        checked += 1
    assume(checked > 0)


@given(
    expr=expressions(include_piecewise=False),
    envs=st.lists(_env_st(), min_size=1, max_size=10),
)
@example(
    expr=("mod", ("mul", 2, ("mod", "x", 3)), 5),
    envs=[{v: 50 for v in _VARS}],
)
def test_matches_sympy(expr: ExprTree, envs: list[Env]) -> None:
    """Cross-check against SymPy: both should produce numerically
    equivalent results. Uses Python eval_expr as ground truth to avoid
    SymPy Mod bug #28744 with evaluate=False."""
    ctx = ixsimpl.Context()
    try:
        ixs_result = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not ixs_result.is_error)
    ixs_simplified = ixs_result.simplify()
    assume(not ixs_simplified.is_error)

    try:
        sp_expr = to_sympy(expr)
    except (ValueError, TypeError):
        assume(False)

    checked = 0
    for env in envs:
        try:
            raw = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError):
            continue
        ground_truth = _as_int(raw)
        if ground_truth is None:
            continue
        ixs_val = eval_ixs(ixs_simplified, ctx, env)
        assert ground_truth == ixs_val, (
            f"ixsimpl diverges from ground truth at {env}: "
            f"expected={ground_truth}, got={ixs_val}, expr={expr}"
        )
        try:
            sp_env = {sympy.Symbol(k, integer=True): v for k, v in env.items()}
            sp_val = sp_expr.subs(sp_env)
            if sp_val.is_number and sp_val.is_integer:
                sp_int = int(sp_val)
                # Non-fatal: SymPy 1.14 has Mod evaluate=False bugs (#28744)
                # that cause wrong results for nested Mod expressions.
                if sp_int != ground_truth:
                    warnings.warn(
                        f"SymPy disagrees with ground truth at {env}: "
                        f"sympy={sp_int}, expected={ground_truth}, expr={expr}",
                        stacklevel=1,
                    )
        except (ZeroDivisionError, ValueError, TypeError, OverflowError):
            pass
        checked += 1
    assume(checked > 0)


@given(
    expr=expressions(),
    div_sym=st.sampled_from(_VARS),
    divisor=st.integers(min_value=2, max_value=64),
    env_mults=st.lists(
        st.tuples(_env_st(1, 50), st.integers(-25, 25)),
        min_size=1,
        max_size=10,
    ),
)
def test_simplify_with_divisibility(
    expr: ExprTree,
    div_sym: str,
    divisor: int,
    env_mults: list[tuple[Env, int]],
) -> None:
    """Simplification with a divisibility assumption preserves semantics
    when evaluated at points satisfying the assumption."""
    ctx = ixsimpl.Context()
    try:
        ixs_expr = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not ixs_expr.is_error)

    sym_node = ctx.sym(div_sym)
    assumption = ctx.eq(ixsimpl.mod(sym_node, ctx.int_(divisor)), ctx.int_(0))
    ixs_simplified = ixs_expr.simplify(assumptions=[assumption])
    assume(not ixs_simplified.is_error)

    checked = 0
    for base_env, mult in env_mults:
        env = {**base_env, div_sym: mult * divisor}
        try:
            raw = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError):
            continue
        orig = _as_int(raw)
        if orig is None:
            continue
        simp = eval_ixs(ixs_simplified, ctx, env)
        assert orig == simp, (
            f"Divisibility mismatch: {orig} != {simp} at {env}, "
            f"expr={expr}, assumption=Mod({div_sym},{divisor})==0"
        )
        checked += 1
    assume(checked > 0)


@given(
    expr=expressions(include_piecewise=False),
    envs=st.lists(_env_st(), min_size=1, max_size=10),
)
def test_to_sympy_semantics(expr: ExprTree, envs: list[Env]) -> None:
    """ixsimpl.sympy_conv.to_sympy produces a SymPy expression that
    evaluates identically to the ixsimpl expression at random points."""
    ctx = ixsimpl.Context()
    try:
        ixs_expr = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not ixs_expr.is_error)

    # SymPy Max/Min reject unevaluated Mod nodes as "not comparable".
    try:
        sp_converted = conv_to_sympy(ixs_expr)
    except (ValueError, TypeError):
        assume(False)

    checked = 0
    for env in envs:
        try:
            ixs_val = eval_ixs(ixs_expr, ctx, env)
        except (ValueError, TypeError):
            continue
        try:
            # xreplace avoids SymPy 1.14 .subs() bug with nested Mod.
            sp_env = {sympy.Symbol(k, integer=True): sympy.Integer(v) for k, v in env.items()}
            sp_val = sp_converted.xreplace(sp_env)
            if not sp_val.is_number:
                continue
            assert int(sp_val) == ixs_val, (
                f"to_sympy mismatch at {env}: "
                f"ixsimpl={ixs_val}, sympy={int(sp_val)}, expr={expr}"
            )
            checked += 1
        except (ZeroDivisionError, ValueError, TypeError, OverflowError):
            continue
    assume(checked > 0)


@given(
    expr=expressions(include_piecewise=False),
    envs=st.lists(_env_st(), min_size=1, max_size=10),
)
def test_from_sympy_semantics(expr: ExprTree, envs: list[Env]) -> None:
    """ixsimpl.sympy_conv.from_sympy produces an ixsimpl expression that
    evaluates identically to the original tree at random points."""
    try:
        sp_expr = to_sympy(expr)
    except (ValueError, TypeError):
        assume(False)

    ctx = ixsimpl.Context()
    try:
        ixs_converted = conv_from_sympy(ctx, sp_expr)
    except (ValueError, TypeError):
        assume(False)
    assume(not ixs_converted.is_error)

    checked = 0
    for env in envs:
        try:
            ground_truth = eval_expr(expr, env)
            if not isinstance(ground_truth, int):
                ground_truth = int(ground_truth)
        except (ZeroDivisionError, ValueError, TypeError, OverflowError):
            continue
        try:
            ixs_val = eval_ixs(ixs_converted, ctx, env)
        except (ValueError, TypeError):
            continue
        assert ixs_val == ground_truth, (
            f"from_sympy mismatch at {env}: "
            f"expected={ground_truth}, ixsimpl={ixs_val}, expr={expr}"
        )
        checked += 1
    assume(checked > 0)


@given(
    expr=expressions(include_piecewise=False),
    envs=st.lists(_env_st(), min_size=1, max_size=10),
)
def test_sympy_roundtrip_semantics(expr: ExprTree, envs: list[Env]) -> None:
    """ixsimpl -> to_sympy -> from_sympy -> ixsimpl preserves numerical
    semantics at random integer points."""
    ctx = ixsimpl.Context()
    try:
        original = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not original.is_error)

    # SymPy Max/Min reject unevaluated Mod nodes as "not comparable".
    try:
        sp_expr = conv_to_sympy(original)
    except (ValueError, TypeError):
        assume(False)
    try:
        roundtripped = conv_from_sympy(ctx, sp_expr)
    except (ValueError, TypeError):
        assume(False)
    assume(not roundtripped.is_error)

    checked = 0
    for env in envs:
        try:
            orig_val = eval_ixs(original, ctx, env)
        except (ValueError, TypeError, OverflowError):
            continue
        try:
            rt_val = eval_ixs(roundtripped, ctx, env)
        except (ValueError, TypeError, OverflowError):
            continue
        assert orig_val == rt_val, (
            f"roundtrip mismatch at {env}: "
            f"original={orig_val}, roundtripped={rt_val}, expr={expr}"
        )
        checked += 1
    assume(checked > 0)


@given(
    expr=expressions(),
    bound_sym=st.sampled_from(_VARS),
    lo=st.integers(min_value=0, max_value=50),
    hi=st.integers(min_value=51, max_value=200),
    envs=st.lists(
        st.fixed_dictionaries({v: st.integers(0, 200) for v in _VARS}),
        min_size=1,
        max_size=10,
    ),
)
def test_simplify_with_bounds(
    expr: ExprTree,
    bound_sym: str,
    lo: int,
    hi: int,
    envs: list[Env],
) -> None:
    """Simplification with bound assumptions (lo <= sym < hi) preserves
    semantics when evaluated at points satisfying the bounds."""
    ctx = ixsimpl.Context()
    try:
        ixs_expr = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not ixs_expr.is_error)

    sym_node = ctx.sym(bound_sym)
    assumptions = [sym_node >= ctx.int_(lo), sym_node < ctx.int_(hi)]
    ixs_simplified = ixs_expr.simplify(assumptions=assumptions)
    assume(not ixs_simplified.is_error)

    checked = 0
    for base_env in envs:
        env = {**base_env, bound_sym: max(lo, min(hi - 1, base_env[bound_sym]))}
        try:
            raw = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError):
            continue
        orig = _as_int(raw)
        if orig is None:
            continue
        simp = eval_ixs(ixs_simplified, ctx, env)
        assert orig == simp, (
            f"Bounds mismatch: {orig} != {simp} at {env}, "
            f"expr={expr}, bounds={lo} <= {bound_sym} < {hi}"
        )
        checked += 1
    assume(checked > 0)


_LARGE_VALS_MUL = [-(1 << 30), -(1 << 30) + 1, -1, 0, 1, (1 << 30) - 1, (1 << 30)]
_LARGE_VALS_I64 = [
    -(1 << 62),
    -(1 << 62) + 1,
    -(1 << 31),
    -(1 << 31) + 1,
    -1,
    0,
    1,
    (1 << 31) - 1,
    (1 << 31),
    (1 << 62) - 1,
    (1 << 62),
]


@given(
    expr=expressions(max_depth=3, include_piecewise=False),
    envs=st.lists(
        st.fixed_dictionaries(
            {
                v: st.one_of(
                    st.sampled_from(_LARGE_VALS_MUL),
                    st.sampled_from(_LARGE_VALS_I64),
                    st.integers(-10, 10),
                )
                for v in _VARS
            }
        ),
        min_size=1,
        max_size=5,
    ),
)
def test_simplify_near_overflow(expr: ExprTree, envs: list[Env]) -> None:
    """Simplification with values near int64 overflow boundaries.

    Two tiers: +/-2^30 (safe for x*x), +/-2^62 (near int64 boundary).
    When the result fits in int64, it must match Python arbitrary-precision
    arithmetic.  int64 overflow in ixsimpl is expected and skipped.
    """
    ctx = ixsimpl.Context()
    try:
        ixs_expr = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not ixs_expr.is_error)
    ixs_simplified = ixs_expr.simplify()
    assume(not ixs_simplified.is_error)

    checked = 0
    for env in envs:
        try:
            orig = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError, OverflowError):
            continue
        if isinstance(orig, Fraction):
            if orig.denominator != 1:
                continue
            orig = int(orig)
        if not (-(1 << 62) <= orig <= (1 << 62)):
            continue
        try:
            simp = eval_ixs(ixs_simplified, ctx, env)
        except (ValueError, TypeError):
            continue
        assert orig == simp, f"Near-overflow mismatch: {orig} != {simp} at {env}, expr={expr}"
        checked += 1
    assume(checked > 0)


@given(
    div_sym=st.sampled_from(_VARS),
    divisor=st.integers(min_value=2, max_value=64),
    other=expressions(max_depth=3),
    pattern=st.sampled_from(["floor_div", "ceil_div", "mod", "compound"]),
    env_mults=st.lists(
        st.tuples(_env_st(1, 50), st.integers(-25, 25)),
        min_size=1,
        max_size=10,
    ),
)
def test_divisibility_targeted(
    div_sym: str,
    divisor: int,
    other: ExprTree,
    pattern: str,
    env_mults: list[tuple[Env, int]],
) -> None:
    """Targeted: divisibility assumption with expressions that exercise it."""
    if pattern == "floor_div":
        expr: ExprTree = ("floor", ("div", div_sym, divisor))
    elif pattern == "ceil_div":
        expr = ("ceiling", ("div", div_sym, divisor))
    elif pattern == "mod":
        expr = ("mod", div_sym, divisor)
    else:
        expr = ("floor", ("div", ("add", div_sym, other), divisor))

    ctx = ixsimpl.Context()
    try:
        ixs_expr = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not ixs_expr.is_error)

    sym_node = ctx.sym(div_sym)
    assumption = ctx.eq(ixsimpl.mod(sym_node, ctx.int_(divisor)), ctx.int_(0))
    ixs_simplified = ixs_expr.simplify(assumptions=[assumption])
    assume(not ixs_simplified.is_error)

    checked = 0
    for base_env, mult in env_mults:
        env = {**base_env, div_sym: mult * divisor}
        try:
            orig = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError):
            continue
        simp = eval_ixs(ixs_simplified, ctx, env)
        assert orig == simp, (
            f"Targeted divisibility mismatch: {orig} != {simp} at {env}, "
            f"expr={expr}, assumption=Mod({div_sym},{divisor})==0"
        )
        checked += 1
    assume(checked > 0)


@given(
    bound_sym=st.sampled_from(_VARS),
    lo=st.integers(min_value=0, max_value=50),
    hi=st.integers(min_value=51, max_value=200),
    pattern=st.sampled_from(["max_lo", "min_hi", "floor_div", "mod"]),
    envs=st.lists(
        st.fixed_dictionaries({v: st.integers(0, 200) for v in _VARS}),
        min_size=1,
        max_size=10,
    ),
)
def test_bounds_targeted(
    bound_sym: str,
    lo: int,
    hi: int,
    pattern: str,
    envs: list[Env],
) -> None:
    """Targeted: bound assumptions with expressions that exercise them."""
    if pattern == "max_lo":
        expr: ExprTree = ("max", bound_sym, lo)
    elif pattern == "min_hi":
        expr = ("min", bound_sym, hi - 1)
    elif pattern == "floor_div":
        d = max(1, hi - lo)
        expr = ("floor", ("div", bound_sym, d))
    else:
        m = max(1, hi - lo)
        expr = ("mod", bound_sym, m)

    ctx = ixsimpl.Context()
    try:
        ixs_expr = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not ixs_expr.is_error)

    sym_node = ctx.sym(bound_sym)
    assumptions = [sym_node >= ctx.int_(lo), sym_node < ctx.int_(hi)]
    ixs_simplified = ixs_expr.simplify(assumptions=assumptions)
    assume(not ixs_simplified.is_error)

    checked = 0
    for base_env in envs:
        env = {**base_env, bound_sym: max(lo, min(hi - 1, base_env[bound_sym]))}
        try:
            orig = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError):
            continue
        simp = eval_ixs(ixs_simplified, ctx, env)
        assert orig == simp, (
            f"Targeted bounds mismatch: {orig} != {simp} at {env}, "
            f"expr={expr}, bounds={lo} <= {bound_sym} < {hi}"
        )
        checked += 1
    assume(checked > 0)
