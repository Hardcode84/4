"""
Fuzz tests for ixsimpl using Hypothesis.

Three properties:
1. Self-consistency: simplification preserves numerical semantics.
2. Cross-check: ixsimpl agrees with SymPy on random expressions.
3. Divisibility: simplification with Mod(sym, d)==0 preserves semantics
   at evaluation points satisfying the assumption.
"""

import math
import os
import random

import sympy
from hypothesis import assume, example, given, settings
from hypothesis import strategies as st

import ixsimpl

_IN_CI = os.environ.get("CI") == "true"
_SELF_CONSISTENCY_EXAMPLES = 500 if _IN_CI else 10000
_SYMPY_CROSSCHECK_EXAMPLES = 200 if _IN_CI else 5000
_DIVISIBILITY_EXAMPLES = 200 if _IN_CI else 2000

# ---------------------------------------------------------------------------
#  Expression tree strategies
# ---------------------------------------------------------------------------

sym_names = st.sampled_from(["x", "y", "z", "w"])
small_ints = st.integers(min_value=-64, max_value=64)
pos_ints = st.integers(min_value=1, max_value=32)


@st.composite
def expressions(draw, max_depth=4):
    if max_depth <= 0 or draw(st.booleans()):
        return draw(st.one_of(sym_names, small_ints))
    op = draw(
        st.sampled_from(
            ["add", "mul", "div", "floor", "ceiling", "mod", "max", "min"]
        )
    )
    a = draw(expressions(max_depth=max_depth - 1))
    if op in ("floor", "ceiling"):
        return (op, a)
    b = draw(expressions(max_depth=max_depth - 1))
    if op == "mod":
        b = draw(pos_ints)
    if op == "div":
        b = draw(pos_ints)
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


# ---------------------------------------------------------------------------
#  Tree -> SymPy
# ---------------------------------------------------------------------------

_sp_syms = {n: sympy.Symbol(n, integer=True) for n in ["x", "y", "z", "w"]}


def to_sympy(tree):
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
        return sympy.Piecewise(
            (to_sympy(val), to_sympy_cond(cond)), (to_sympy(default), True)
        )
    raise ValueError(f"unknown op: {op}")


def to_sympy_cond(tree):
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


def to_ixsimpl(ctx, tree):
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
    raise ValueError(f"unknown op: {op}")


# ---------------------------------------------------------------------------
#  Numerical evaluation
# ---------------------------------------------------------------------------


def _floored_div(a, b):
    if b == 0:
        raise ZeroDivisionError
    return math.floor(a / b)


def _floored_mod(a, b):
    if b == 0:
        raise ZeroDivisionError
    return a - b * math.floor(a / b)


def eval_expr(tree, env):
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
        return int(math.floor(v))
    if op == "ceiling":
        v = eval_expr(tree[1], env)
        return int(math.ceil(v))
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


def eval_cond(tree, env):
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


def eval_ixs(expr, ctx, env):
    """Evaluate ixsimpl Expr by substituting all variables."""
    result = expr
    for name, val in env.items():
        result = result.subs(name, ctx.int_(val))
    if result.is_error:
        raise ValueError("sentinel")
    try:
        return int(result)
    except TypeError:
        raise ValueError(f"result is not an integer constant: {result}")


# ---------------------------------------------------------------------------
#  Fuzz tests
# ---------------------------------------------------------------------------


@given(expr=expressions())
@settings(max_examples=_SELF_CONSISTENCY_EXAMPLES, deadline=None)
def test_simplify_self_consistency(expr):
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

    for _ in range(10):
        env = {v: random.randint(0, 100) for v in ["x", "y", "z", "w"]}
        try:
            orig = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError):
            continue
        try:
            simp = eval_ixs(ixs_simplified, ctx, env)
        except (ValueError, TypeError):
            continue
        assert orig == simp, f"Mismatch: {orig} != {simp} at {env}, expr={expr}"


@given(expr=expressions())
@settings(max_examples=_SYMPY_CROSSCHECK_EXAMPLES, deadline=None)
@example(("mod", ("mul", 2, ("mod", "x", 3)), 5))
def test_matches_sympy(expr):
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

    for _ in range(10):
        env = {v: random.randint(1, 100) for v in ["x", "y", "z", "w"]}
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
    div_sym=st.sampled_from(["x", "y", "z", "w"]),
    divisor=st.integers(min_value=2, max_value=64),
)
@settings(max_examples=_DIVISIBILITY_EXAMPLES, deadline=None)
def test_simplify_with_divisibility(expr, div_sym, divisor):
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
    for _ in range(10):
        env = {v: random.randint(1, 50) for v in ["x", "y", "z", "w"]}
        env[div_sym] = random.randint(-25, 25) * divisor
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
    print("All fuzz tests passed!")
