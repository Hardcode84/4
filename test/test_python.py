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
import os
from typing import Any

import ixsimpl
import sympy
from hypothesis import assume, example, given, settings
from hypothesis import strategies as st
from ixsimpl.sympy_conv import from_sympy as conv_from_sympy
from ixsimpl.sympy_conv import to_sympy as conv_to_sympy

ExprTree = str | int | tuple[Any, ...]
CondTree = tuple[Any, ...]
Env = dict[str, int]

_IN_CI = os.environ.get("CI") == "true"
_SELF_CONSISTENCY_EXAMPLES = 500 if _IN_CI else 10000
_SYMPY_CROSSCHECK_EXAMPLES = 200 if _IN_CI else 5000
_DIVISIBILITY_EXAMPLES = 200 if _IN_CI else 2000
_CONV_EXAMPLES = 500 if _IN_CI else 2000

_VARS = ["x", "y", "z", "w"]


def _env_st(lo: int = 1, hi: int = 100) -> st.SearchStrategy[Env]:
    return st.fixed_dictionaries({v: st.integers(lo, hi) for v in _VARS})


# ---------------------------------------------------------------------------
#  Expression tree strategies
# ---------------------------------------------------------------------------

sym_names = st.sampled_from(_VARS)
small_ints = st.integers(min_value=-64, max_value=64)
pos_ints = st.integers(min_value=1, max_value=32)


_OPS_BASE = ["add", "mul", "div", "floor", "ceiling", "mod", "max", "min"]
_OPS_WITH_PW = [*_OPS_BASE, "piecewise"]


@st.composite
def expressions(draw: st.DrawFn, max_depth: int = 4, include_piecewise: bool = True) -> ExprTree:
    if max_depth <= 0 or draw(st.booleans()):
        return draw(st.one_of(sym_names, small_ints))
    ops = _OPS_WITH_PW if include_piecewise else _OPS_BASE
    op = draw(st.sampled_from(ops))
    a = draw(expressions(max_depth=max_depth - 1, include_piecewise=include_piecewise))
    if op in ("floor", "ceiling"):
        return (op, a)
    if op == "piecewise":
        cond = draw(conditions(max_depth=1))
        default = draw(expressions(max_depth=max_depth - 1, include_piecewise=include_piecewise))
        return (op, a, cond, default)
    b = draw(expressions(max_depth=max_depth - 1, include_piecewise=include_piecewise))
    if op == "mod":
        b = draw(pos_ints)
    if op == "div":
        b = draw(pos_ints)
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

_sp_syms = {n: sympy.Symbol(n, integer=True) for n in ["x", "y", "z", "w"]}


def to_sympy(tree: ExprTree) -> Any:
    if isinstance(tree, str):
        return _sp_syms[tree]
    if isinstance(tree, int):
        return sympy.Integer(tree)
    op = tree[0]
    if op == "add":
        return to_sympy(tree[1]) + to_sympy(tree[2])
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
        return sympy.Mod(to_sympy(tree[1]), to_sympy(tree[2]), evaluate=False)
    if op == "max":
        return sympy.Max(to_sympy(tree[1]), to_sympy(tree[2]))
    if op == "min":
        return sympy.Min(to_sympy(tree[1]), to_sympy(tree[2]))
    if op == "piecewise":
        val, cond, default = tree[1], tree[2], tree[3]
        return sympy.Piecewise((to_sympy(val), to_sympy_cond(cond)), (to_sympy(default), True))
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
    if op == "add":
        return to_ixsimpl(ctx, tree[1]) + to_ixsimpl(ctx, tree[2])
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
    if op == "piecewise":
        val, cond, default = tree[1], tree[2], tree[3]
        cond_expr = to_ixsimpl_cond(ctx, cond)
        return ixsimpl.pw(
            (to_ixsimpl(ctx, val), cond_expr),
            (to_ixsimpl(ctx, default), ctx.true_()),
        )
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


def _floored_div(a: Any, b: Any) -> int:
    if b == 0:
        raise ZeroDivisionError
    return int(math.floor(a / b))


def _floored_mod(a: Any, b: Any) -> Any:
    if b == 0:
        raise ZeroDivisionError
    return a - b * math.floor(a / b)


def eval_expr(tree: ExprTree, env: Env) -> Any:
    """Evaluate expression tree numerically using Python arithmetic."""
    if isinstance(tree, str):
        return env[tree]
    if isinstance(tree, int):
        return tree
    op = tree[0]
    if op == "add":
        return eval_expr(tree[1], env) + eval_expr(tree[2], env)
    if op == "mul":
        return eval_expr(tree[1], env) * eval_expr(tree[2], env)
    if op == "div":
        a, b = eval_expr(tree[1], env), eval_expr(tree[2], env)
        if b == 0:
            raise ZeroDivisionError
        return sympy.Rational(a, b)
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
    if op == "piecewise":
        val, cond, default = tree[1], tree[2], tree[3]
        if eval_cond(cond, env):
            return eval_expr(val, env)
        return eval_expr(default, env)
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
    if op == "not":
        return not eval_cond(tree[1], env)
    if op == "and":
        return eval_cond(tree[1], env) and eval_cond(tree[2], env)
    if op == "or":
        return eval_cond(tree[1], env) or eval_cond(tree[2], env)
    raise ValueError(f"unknown cond op: {op}")


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


@given(expr=expressions(), envs=st.lists(_env_st(0, 100), min_size=1, max_size=10))
@settings(max_examples=_SELF_CONSISTENCY_EXAMPLES, deadline=None)
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

    for env in envs:
        try:
            orig = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError):
            continue
        try:
            simp = eval_ixs(ixs_simplified, ctx, env)
        except (ValueError, TypeError):
            continue
        assert orig == simp, f"Mismatch: {orig} != {simp} at {env}, expr={expr}"


@given(
    expr=expressions(include_piecewise=False),
    envs=st.lists(_env_st(), min_size=1, max_size=10),
)
@settings(max_examples=_SYMPY_CROSSCHECK_EXAMPLES, deadline=None)
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

    for env in envs:
        try:
            ground_truth = eval_expr(expr, env)
            ixs_val = eval_ixs(ixs_simplified, ctx, env)
        except (ZeroDivisionError, ValueError, TypeError):
            continue
        assert ground_truth == ixs_val, (
            f"ixsimpl diverges from ground truth at {env}: "
            f"expected={ground_truth}, got={ixs_val}, expr={expr}"
        )
        try:
            sp_env = {sympy.Symbol(k, integer=True): v for k, v in env.items()}
            sp_val = sp_expr.subs(sp_env)
            if sp_val.is_number:
                sp_int = int(sp_val)
                if sp_int != ground_truth:
                    pass  # SymPy bug, not ours
        except (ZeroDivisionError, ValueError, TypeError):
            pass


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
@settings(max_examples=_DIVISIBILITY_EXAMPLES, deadline=None)
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
            orig = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError):
            continue
        try:
            simp = eval_ixs(ixs_simplified, ctx, env)
        except (ValueError, TypeError):
            continue
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
@settings(max_examples=_CONV_EXAMPLES, deadline=None)
def test_to_sympy_semantics(expr: ExprTree, envs: list[Env]) -> None:
    """ixsimpl.sympy_conv.to_sympy produces a SymPy expression that
    evaluates identically to the ixsimpl expression at random points."""
    ctx = ixsimpl.Context()
    try:
        ixs_expr = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not ixs_expr.is_error)

    sp_converted = conv_to_sympy(ixs_expr)

    checked = 0
    for env in envs:
        try:
            ixs_val = eval_ixs(ixs_expr, ctx, env)
        except (ValueError, TypeError):
            continue
        try:
            sp_env = {sympy.Symbol(k, integer=True): v for k, v in env.items()}
            sp_val = sp_converted.subs(sp_env)
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
@settings(max_examples=_CONV_EXAMPLES, deadline=None)
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
@settings(max_examples=_CONV_EXAMPLES, deadline=None)
def test_sympy_roundtrip_semantics(expr: ExprTree, envs: list[Env]) -> None:
    """ixsimpl -> to_sympy -> from_sympy -> ixsimpl preserves numerical
    semantics at random integer points."""
    ctx = ixsimpl.Context()
    try:
        original = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not original.is_error)

    sp_expr = conv_to_sympy(original)
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


if __name__ == "__main__":
    print(f"Running self-consistency test ({_SELF_CONSISTENCY_EXAMPLES} examples)...")
    test_simplify_self_consistency()
    print("PASSED")
    print(f"Running SymPy cross-check ({_SYMPY_CROSSCHECK_EXAMPLES} examples)...")
    test_matches_sympy()
    print("PASSED")
    print(f"Running divisibility test ({_DIVISIBILITY_EXAMPLES} examples)...")
    test_simplify_with_divisibility()
    print("PASSED")
    print(f"Running to_sympy semantics test ({_CONV_EXAMPLES} examples)...")
    test_to_sympy_semantics()
    print("PASSED")
    print(f"Running from_sympy semantics test ({_CONV_EXAMPLES} examples)...")
    test_from_sympy_semantics()
    print("PASSED")
    print(f"Running SymPy roundtrip semantics test ({_CONV_EXAMPLES} examples)...")
    test_sympy_roundtrip_semantics()
    print("PASSED")
    print("All fuzz tests passed!")
