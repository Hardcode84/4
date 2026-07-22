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
7. Range API soundness: reported bounds contain sampled evaluations that
   satisfy the input assumptions.
8. Entailment API soundness: proven modular, mask, and power-of-two
   comparisons agree with sampled evaluations satisfying the input assumptions.
9. Invalid deserialize fuzzing: garbage and byte-flipped payloads do not
   crash the forked test subprocess.
"""

from __future__ import annotations

import math
import warnings
from fractions import Fraction
from typing import Any

import ixsimpl
import pytest
import sympy
from hypothesis import assume, example, given
from hypothesis import strategies as st
from ixsimpl.sympy_conv import from_sympy as conv_from_sympy
from ixsimpl.sympy_conv import to_sympy as conv_to_sympy

ExprTree = str | int | tuple[Any, ...]
CondTree = tuple[Any, ...]
Env = dict[str, int]
RangeBounds = dict[str, tuple[int, int]]
ModSymbolCase = tuple[str, int, int, int, int, str]
ModCompositeCase = tuple[str, str, int, int, int, int, int, int, int, str, str]
BitMaskCase = tuple[str, str, int, int, int, int, str]
Pow2Case = tuple[str, bool, str, int, str]

_VARS = ["x", "y", "z", "w", "a", "b", "c", "d"]
_SERIAL_MAGIC = b"IXSB"


def _env_from_val(val_st: st.SearchStrategy[int]) -> st.SearchStrategy[Env]:
    """Build an env strategy that draws each variable from val_st."""
    return st.fixed_dictionaries({v: val_st for v in _VARS})


def _signed(base: st.SearchStrategy[int]) -> st.SearchStrategy[int]:
    """Draw from base or its negation with equal probability."""
    return st.one_of(base, base.map(lambda x: -x))


def _env_st(lo: int = 1, hi: int = 100) -> st.SearchStrategy[Env]:
    """Env with each variable uniform in [lo, hi]."""
    return _env_from_val(st.integers(lo, hi))


def _wide_env_st() -> st.SearchStrategy[Env]:
    """Env mixing negative, zero, and positive values."""
    return _env_from_val(st.one_of(st.integers(-100, -1), st.just(0), st.integers(1, 100)))


_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 127, 251, 509, 1021]
_POW2 = [1 << k for k in range(1, 16)]
_POW2_OR_ZERO = [0] + [1 << k for k in range(0, 16)]
_POW2_ADJ = [v + d for v in _POW2 for d in (-1, 1)]
_POW2_FACT_VALUES = sorted(set([0, *_POW2, *_POW2_ADJ, -8, -1, 3, 5, 6, 9, 12, 17]))
_INTERESTING = sorted(set(_PRIMES + _POW2 + _POW2_ADJ + [0, 1, -1]))


def _spicy_env_st() -> st.SearchStrategy[Env]:
    """Env with primes, powers of 2, pow2 +/- 1, 0, and +/-1."""
    return _env_from_val(_signed(st.sampled_from(_INTERESTING)))


def _prime_env_st() -> st.SearchStrategy[Env]:
    """Env biased toward primes (with optional negation)."""
    return _env_from_val(_signed(st.sampled_from(_PRIMES)))


def _pow2_env_st() -> st.SearchStrategy[Env]:
    """Env biased toward powers of 2 and pow2 +/- 1."""
    return _env_from_val(_signed(st.sampled_from(sorted(set(_POW2 + _POW2_ADJ)))))


def _mixed_env_st() -> st.SearchStrategy[Env]:
    """Env blending uniform [0, 100], wide, and spicy values."""
    return st.one_of(_env_st(0, 100), _wide_env_st(), _spicy_env_st())


@st.composite
def _range_bounds_st(draw: st.DrawFn) -> RangeBounds:
    """Satisfiable per-symbol integer intervals for range-query fuzzing."""
    names = draw(st.lists(sym_names, min_size=0, max_size=4, unique=True))
    bounds: RangeBounds = {}
    for name in names:
        lo = draw(st.integers(min_value=-64, max_value=64))
        width = draw(st.integers(min_value=0, max_value=128))
        bounds[name] = (lo, lo + width)
    return bounds


@st.composite
def _mod_symbol_case_st(draw: st.DrawFn) -> ModSymbolCase:
    """Satisfiable Mod(sym, M)==R assumption plus a provable query."""
    sym = draw(sym_names)
    assume_mod = draw(st.integers(min_value=2, max_value=64))
    rem = draw(st.integers(min_value=0, max_value=assume_mod - 1))
    query_mod = draw(st.sampled_from([d for d in range(2, assume_mod + 1) if assume_mod % d == 0]))
    actual = rem % query_mod
    targets = [actual, -1, query_mod, actual + query_mod]
    if query_mod > 1:
        targets.append((actual + 1) % query_mod)
    target = draw(st.sampled_from(targets))
    cmp_op = draw(st.sampled_from(["==", "!="]))
    return sym, assume_mod, rem, query_mod, target, cmp_op


@st.composite
def _mod_composite_case_st(draw: st.DrawFn) -> ModCompositeCase:
    """Composite expression that is divisible by query_mod under assumptions."""
    names = draw(st.lists(sym_names, min_size=2, max_size=2, unique=True))
    query_mod = draw(st.integers(min_value=2, max_value=64))
    coeffs = [c for c in range(-8, 9) if c != 0 and c % query_mod != 0]
    coeff_a = draw(st.sampled_from(coeffs))
    coeff_b = draw(st.sampled_from(coeffs))
    mod_a = query_mod
    mod_b = query_mod
    const = query_mod * draw(st.integers(min_value=-8, max_value=8))
    target = draw(st.sampled_from([0, -1, query_mod]))
    cmp_op = draw(st.sampled_from(["==", "!="]))
    pattern = draw(st.sampled_from(["mul", "add"]))
    return (
        names[0],
        names[1],
        query_mod,
        coeff_a,
        coeff_b,
        mod_a,
        mod_b,
        const,
        target,
        cmp_op,
        pattern,
    )


@st.composite
def _bit_mask_case_st(draw: st.DrawFn) -> BitMaskCase:
    """Satisfiable bit-mask assumption plus a mask equality query."""
    sym = draw(sym_names)
    pattern = draw(st.sampled_from(["and_eq", "or_eq", "or_self", "and_self"]))
    mask = draw(st.integers(min_value=0, max_value=255))

    if pattern == "and_eq":
        assume_value = draw(st.integers(min_value=0, max_value=255)) & mask
    elif pattern == "or_eq":
        assume_value = draw(st.integers(min_value=0, max_value=255)) | mask
    else:
        assume_value = 0

    query_mask = draw(st.integers(min_value=0, max_value=255))
    query_known_one, query_known_zero = _bit_mask_known_bits(pattern, mask, assume_value)
    known = (query_known_one | query_known_zero) & query_mask
    known_value = query_known_one & query_mask
    mismatch = 1 if query_mask == 0 else known_value ^ (query_mask & -query_mask)
    targets = [known_value, mismatch, query_mask + 1, -1]
    if known != query_mask:
        targets.append(draw(st.integers(min_value=0, max_value=255)))
    target = draw(st.sampled_from(targets))
    cmp_op = draw(st.sampled_from(["==", "!="]))
    return sym, pattern, mask, assume_value, query_mask, target, cmp_op


@st.composite
def _pow2_case_st(draw: st.DrawFn) -> Pow2Case:
    """Power-of-two-or-zero assumption plus a query check."""
    sym = draw(sym_names)
    positive = draw(st.booleans())
    query_kind = draw(st.sampled_from(["pow2_expr", "lower_bound"]))
    if query_kind == "pow2_expr":
        target = draw(st.sampled_from([0, -1, 1, 2, 4, 8]))
        cmp_op = draw(st.sampled_from(["==", "!="]))
    else:
        target = draw(st.sampled_from([-1, 0, 1, 2]))
        cmp_op = draw(st.sampled_from([">=", "<"]))
    return sym, positive, query_kind, target, cmp_op


# ---------------------------------------------------------------------------
#  Expression tree strategies
# ---------------------------------------------------------------------------

sym_names = st.sampled_from(_VARS)
small_ints = st.integers(min_value=-64, max_value=64)
pos_ints = st.integers(min_value=1, max_value=32)
small_rats = st.tuples(st.integers(min_value=-64, max_value=64), pos_ints).map(
    lambda pq: ("rat", pq[0], pq[1])
)


_OPS_BASE = [
    "add",
    "sub",
    "mul",
    "neg",
    "div",
    "floor",
    "ceiling",
    "mod",
    "max",
    "min",
    "xor",
    "bitand",
    "bitor",
]
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
        choice = draw(st.sampled_from(["div", "rat_add", "mul", "sub", "add", "plain"]))
        if choice == "div":
            d = draw(pos_ints)
            return (op, ("div", a, d))
        if choice == "rat_add":
            rat_leaf = draw(small_rats)
            return (op, ("add", rat_leaf, a))
        if choice == "mul":
            b = draw(expressions(max_depth=max_depth - 1, include_piecewise=include_piecewise))
            return (op, ("mul", a, b))
        if choice == "sub":
            b = draw(expressions(max_depth=max_depth - 1, include_piecewise=include_piecewise))
            return (op, ("sub", a, b))
        if choice == "add":
            b = draw(expressions(max_depth=max_depth - 1, include_piecewise=include_piecewise))
            return (op, ("add", a, b))
        return (op, a)
    if op == "neg":
        return (op, a)
    if op == "piecewise":
        # Piecewise tuple layout: ("piecewise", val1, cond1, ..., valN, condN, default)
        # ncases = (len - 2) // 2; default is always tree[-1].
        cond_depth = draw(st.integers(min_value=1, max_value=3))
        cond = draw(conditions(max_depth=cond_depth))
        default = draw(expressions(max_depth=max_depth - 1, include_piecewise=include_piecewise))
        if draw(st.booleans()):
            b = draw(expressions(max_depth=max_depth - 1, include_piecewise=include_piecewise))
            cond2 = draw(conditions(max_depth=cond_depth))
            return (op, a, cond, b, cond2, default)
        return (op, a, cond, default)
    if op == "mod" or op == "div":
        b = draw(pos_ints)
    elif op in ("xor", "bitand", "bitor"):
        if draw(st.integers(min_value=0, max_value=3)) == 0:
            a = draw(st.one_of(sym_names, small_ints))
            b = draw(st.one_of(sym_names, small_ints))
        else:
            a = draw(st.integers(min_value=0, max_value=255))
            b = draw(st.integers(min_value=0, max_value=255))
    else:
        b = draw(expressions(max_depth=max_depth - 1, include_piecewise=include_piecewise))
    return (op, a, b)


@st.composite
def conditions(draw: st.DrawFn, max_depth: int = 2) -> CondTree:
    if max_depth <= 0 or draw(st.booleans()):
        a = draw(expressions(max_depth=4))
        b = draw(expressions(max_depth=4))
        op = draw(st.sampled_from([">=", ">", "<=", "<", "==", "!="]))
        return ("cmp", op, a, b)
    combiner = draw(st.sampled_from(["and", "or", "not"]))
    c1 = draw(conditions(max_depth=max_depth - 1))
    if combiner == "not":
        return ("not", c1)
    c2 = draw(conditions(max_depth=max_depth - 1))
    return (combiner, c1, c2)


@st.composite
def garbage_serialized_blobs(draw: st.DrawFn, max_size: int = 256) -> bytes:
    data = bytearray(draw(st.binary(min_size=0, max_size=max_size)))
    if len(data) >= len(_SERIAL_MAGIC) and data[: len(_SERIAL_MAGIC)] == _SERIAL_MAGIC:
        data[0] ^= 0x80
    return bytes(data)


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
        # evaluate=False: SymPy incorrectly reports is_integer=True for
        # some rational expressions (e.g. y*(2*x+2*y)/30) and drops floor.
        return sympy.floor(to_sympy(tree[1]), evaluate=False)
    if op == "ceiling":
        return sympy.ceiling(to_sympy(tree[1]), evaluate=False)
    if op == "mod":
        # evaluate=False avoids SymPy Mod bugs (e.g. #28744) that silently
        # produce wrong results for certain inputs.
        return sympy.Mod(to_sympy(tree[1]), to_sympy(tree[2]), evaluate=False)
    if op == "max":
        # evaluate=False avoids wrong eager collapse of some nested Max/Min trees.
        return sympy.Max(to_sympy(tree[1]), to_sympy(tree[2]), evaluate=False)
    if op == "min":
        return sympy.Min(to_sympy(tree[1]), to_sympy(tree[2]), evaluate=False)
    if op == "xor":
        raise ValueError("xor not supported in SymPy conversion")
    if op == "bitand":
        return sympy.Function("bitand")(to_sympy(tree[1]), to_sympy(tree[2]))
    if op == "bitor":
        return sympy.Function("bitor")(to_sympy(tree[1]), to_sympy(tree[2]))
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
    if op == "bitand":
        return to_ixsimpl(ctx, tree[1]) & to_ixsimpl(ctx, tree[2])
    if op == "bitor":
        return to_ixsimpl(ctx, tree[1]) | to_ixsimpl(ctx, tree[2])
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
    """Floored modulo with the ixsimpl-required positive divisor.

    Uses Python's built-in % which is exact for integers — an earlier
    version using math.floor(a/b) lost precision for large values."""
    if b <= 0:
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
    if op == "bitand":
        return int(eval_expr(tree[1], env)) & int(eval_expr(tree[2], env))
    if op == "bitor":
        return int(eval_expr(tree[1], env)) | int(eval_expr(tree[2], env))
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


def _subs_all(expr: ixsimpl.Expr, ctx: ixsimpl.Context, env: Env) -> ixsimpl.Expr:
    """Substitute all variables; return the raw ixsimpl expression."""
    result = expr
    for name, val in env.items():
        result = result.subs(name, ctx.int_(val))
    return result


def _assert_sentinel_on_py_error(
    ixs_expr: ixsimpl.Expr,
    ctx: ixsimpl.Context,
    env: Env,
    tree: ExprTree,
) -> None:
    """When Python eval raised an error, verify ixsimpl is consistent.

    Must produce either a sentinel (both agree it's undefined) or a
    concrete integer (simplifier legitimately eliminated the undefined
    subexpression, e.g. 0*(1/0) -> 0).  A non-integer symbolic residue
    would indicate a bug.
    """
    try:
        result = _subs_all(ixs_expr, ctx, env)
    except OverflowError:
        return
    if result.is_error:
        return
    try:
        int(result)
    except (TypeError, ValueError):
        raise AssertionError(
            f"Python eval errored but ixsimpl returned non-integer "
            f"non-sentinel: {result} at {env}, expr={tree}"
        ) from None


def eval_ixs(expr: ixsimpl.Expr, ctx: ixsimpl.Context, env: Env) -> int:
    """Evaluate ixsimpl Expr by substituting all variables."""
    result = _subs_all(expr, ctx, env)
    if result.is_error:
        raise ValueError("sentinel")
    try:
        return int(result)
    except TypeError as e:
        raise ValueError(f"result is not an integer constant: {result}") from e


def _range_assumptions(ctx: ixsimpl.Context, bounds: RangeBounds) -> list[ixsimpl.Expr]:
    assumptions = []
    for name, (lo, hi) in bounds.items():
        sym = ctx.sym(name)
        assumptions.append(sym >= lo)
        assumptions.append(sym <= hi)
    return assumptions


def _env_within_bounds(env: Env, bounds: RangeBounds) -> Env:
    bounded = dict(env)
    for name, (lo, hi) in bounds.items():
        bounded[name] = max(lo, min(hi, bounded[name]))
    return bounded


def _bit_mask_known_bits(pattern: str, mask: int, assume_value: int) -> tuple[int, int]:
    tracked = (1 << 64) - 1
    if pattern == "and_eq":
        return assume_value & mask, (~assume_value) & mask & tracked
    if pattern == "or_eq":
        return assume_value & ~mask & tracked, ~assume_value & tracked
    if pattern == "or_self":
        return mask & tracked, 0
    if pattern == "and_self":
        return 0, ~mask & tracked
    raise ValueError(f"unknown bit mask pattern: {pattern}")


def _bit_mask_assumption(
    ctx: ixsimpl.Context,
    sym: ixsimpl.Expr,
    pattern: str,
    mask: int,
    assume_value: int,
) -> ixsimpl.Expr:
    if pattern == "and_eq":
        return ctx.eq(sym & mask, assume_value)
    if pattern == "or_eq":
        return ctx.eq(sym | mask, assume_value)
    if pattern == "or_self":
        return ctx.eq(sym | mask, sym)
    if pattern == "and_self":
        return ctx.eq(sym & mask, sym)
    raise ValueError(f"unknown bit mask pattern: {pattern}")


def _bit_mask_sample_value(pattern: str, mask: int, assume_value: int, base: int) -> int:
    if pattern == "and_eq":
        return assume_value | (base & ~mask)
    if pattern == "or_eq":
        return (assume_value & ~mask) | (base & mask)
    if pattern == "or_self":
        return base | mask
    if pattern == "and_self":
        return base & mask
    raise ValueError(f"unknown bit mask pattern: {pattern}")


def _bit_mask_sample_satisfies(pattern: str, mask: int, assume_value: int, value: int) -> bool:
    if pattern == "and_eq":
        return (value & mask) == assume_value
    if pattern == "or_eq":
        return (value | mask) == assume_value
    if pattern == "or_self":
        return (value | mask) == value
    if pattern == "and_self":
        return (value & mask) == value
    raise ValueError(f"unknown bit mask pattern: {pattern}")


def _is_positive_pow2(value: int) -> bool:
    return value > 0 and (value & (value - 1)) == 0


def _expected_pow2_fact(value: int) -> str | None:
    if value == 0:
        return "or_zero"
    if _is_positive_pow2(value):
        return "positive"
    return None


# ---------------------------------------------------------------------------
#  Fuzz tests
# ---------------------------------------------------------------------------


def test_expand_basic() -> None:
    """expand() distributes MUL over ADD."""
    ctx = ixsimpl.Context()
    e = ctx.parse_expr("2*(a + b)")
    expanded = e.expand()
    s = str(expanded)
    assert "2*a" in s
    assert "2*b" in s
    assert "+" in s

    e2 = ctx.parse_expr("(a + b)*(c + d)")
    s2 = str(e2.expand())
    for term in ("a*c", "a*d", "b*c", "b*d"):
        assert term in s2, f"missing {term} in {s2}"


def _check_simplify_consistency(
    expr: ExprTree,
    envs: list[Env],
    *,
    with_trivial_bounds: bool = False,
) -> None:
    """Simplification preserves semantics: evaluate original and simplified
    at random points, check they agree.  When with_trivial_bounds is True,
    all symbols get wide bounds so that bnds is non-NULL and Piecewise
    branch forking / bounds-gated rules are exercised."""
    ctx = ixsimpl.Context()
    try:
        ixs_expr = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not ixs_expr.is_error)
    if with_trivial_bounds:
        assumptions = []
        for v in _VARS:
            s = ctx.sym(v)
            assumptions.append(s >= ctx.int_(-1000000))
            assumptions.append(s < ctx.int_(1000001))
        ixs_simplified = ixs_expr.simplify(assumptions=assumptions)
    else:
        ixs_simplified = ixs_expr.simplify()
    assume(not ixs_simplified.is_error)

    checked = 0
    for env in envs:
        try:
            raw = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError):
            _assert_sentinel_on_py_error(ixs_simplified, ctx, env, expr)
            continue
        orig = _as_int(raw)
        if orig is None:
            continue
        try:
            simp = eval_ixs(ixs_simplified, ctx, env)
        except (ValueError, TypeError):
            continue
        assert orig == simp, f"Mismatch: {orig} != {simp} at {env}, expr={expr}"
        checked += 1
    assume(checked > 0)


@given(expr=expressions(), envs=st.lists(_env_st(0, 100), min_size=1, max_size=10))
def test_simplify_consistency_uniform(expr: ExprTree, envs: list[Env]) -> None:
    """Simplification preserves semantics with uniform env [0, 100]."""
    _check_simplify_consistency(expr, envs)


@given(expr=expressions(), envs=st.lists(_wide_env_st(), min_size=1, max_size=10))
def test_simplify_consistency_wide(expr: ExprTree, envs: list[Env]) -> None:
    """Simplification preserves semantics with negative/zero/positive env."""
    _check_simplify_consistency(expr, envs)


@given(expr=expressions(), envs=st.lists(_prime_env_st(), min_size=1, max_size=10))
def test_simplify_consistency_primes(expr: ExprTree, envs: list[Env]) -> None:
    """Simplification preserves semantics with prime-biased env."""
    _check_simplify_consistency(expr, envs)


@given(expr=expressions(), envs=st.lists(_pow2_env_st(), min_size=1, max_size=10))
def test_simplify_consistency_pow2(expr: ExprTree, envs: list[Env]) -> None:
    """Simplification preserves semantics with pow2-biased env."""
    _check_simplify_consistency(expr, envs)


@given(expr=expressions(), envs=st.lists(_spicy_env_st(), min_size=1, max_size=10))
def test_simplify_consistency_spicy(expr: ExprTree, envs: list[Env]) -> None:
    """Simplification preserves semantics with mixed interesting values."""
    _check_simplify_consistency(expr, envs)


@given(expr=expressions(), envs=st.lists(_mixed_env_st(), min_size=1, max_size=10))
def test_simplify_consistency_mixed(expr: ExprTree, envs: list[Env]) -> None:
    """Simplification preserves semantics with blended uniform/wide/spicy env."""
    _check_simplify_consistency(expr, envs)


@given(expr=expressions(), envs=st.lists(_env_st(0, 100), min_size=1, max_size=10))
def test_simplify_bounds_aware_uniform(expr: ExprTree, envs: list[Env]) -> None:
    """Bounds-aware simplification preserves semantics (uniform env).
    Trivial bounds activate Piecewise branch forking, Max/Min collapse,
    and other bounds-gated rules that are dead code without assumptions."""
    _check_simplify_consistency(expr, envs, with_trivial_bounds=True)


@given(expr=expressions(), envs=st.lists(_wide_env_st(), min_size=1, max_size=10))
def test_simplify_bounds_aware_wide(expr: ExprTree, envs: list[Env]) -> None:
    """Bounds-aware simplification with negative/zero/positive env."""
    _check_simplify_consistency(expr, envs, with_trivial_bounds=True)


@given(expr=expressions(), envs=st.lists(_spicy_env_st(), min_size=1, max_size=10))
def test_simplify_bounds_aware_spicy(expr: ExprTree, envs: list[Env]) -> None:
    """Bounds-aware simplification with interesting values."""
    _check_simplify_consistency(expr, envs, with_trivial_bounds=True)


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
    equivalent results.  Python eval_expr is the ground truth; ixsimpl
    must match it exactly.  SymPy is advisory — disagreements are
    reported as warnings (not assertions) because SymPy 1.14's Mod
    with evaluate=False has known bugs (#28744) that produce wrong
    results for nested Mod expressions."""
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
            _assert_sentinel_on_py_error(ixs_simplified, ctx, env, expr)
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
                        f"sympy={sp_int}, expected={ground_truth}, "
                        f"ixsimpl={ixs_result}, sympy={sp_expr}, "
                        f"ixsimpl_simpl={ixs_simplified}",
                        stacklevel=1,
                    )
        except (ZeroDivisionError, ValueError, TypeError, OverflowError):
            pass
        checked += 1
    assume(checked > 0)  # reject vacuous passes (all envs skipped)


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
            _assert_sentinel_on_py_error(ixs_simplified, ctx, env, expr)
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
    assume(checked > 0)  # reject vacuous passes (all envs skipped)


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
        sp_converted = conv_to_sympy(ixs_expr, xor_fn=sympy.Function("xor"))
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
            assert (
                int(sp_val) == ixs_val
            ), f"to_sympy mismatch at {env}: ixsimpl={ixs_val}, sympy={int(sp_val)}, expr={expr}"
            checked += 1
        except (ZeroDivisionError, ValueError, TypeError, OverflowError):
            continue
    assume(checked > 0)  # reject vacuous passes (all envs skipped)


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
            raw = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError, OverflowError):
            _assert_sentinel_on_py_error(ixs_converted, ctx, env, expr)
            continue
        ground_truth = _as_int(raw)
        if ground_truth is None:
            continue
        try:
            ixs_val = eval_ixs(ixs_converted, ctx, env)
        except (ValueError, TypeError):
            continue
        assert (
            ixs_val == ground_truth
        ), f"from_sympy mismatch at {env}: expected={ground_truth}, ixsimpl={ixs_val}, expr={expr}"
        checked += 1
    assume(checked > 0)  # reject vacuous passes (all envs skipped)


@given(
    expr=expressions(include_piecewise=False),
    envs=st.lists(_env_st(), min_size=1, max_size=10),
)
def test_sympy_roundtrip_semantics(expr: ExprTree, envs: list[Env]) -> None:
    """ixsimpl -> to_sympy -> from_sympy -> ixsimpl preserves numerical
    semantics at random integer points.

    Structural equality is intentionally not checked: SymPy may simplify
    expressions (e.g. Max(0, x**2) -> x**2 for integer x) and the
    roundtripped form can differ structurally while remaining equivalent."""
    ctx = ixsimpl.Context()
    try:
        original = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not original.is_error)

    # SymPy conversion can fail: Max/Min reject unevaluated Mod nodes
    # as "not comparable", and some ixsimpl constructs have no SymPy
    # equivalent.  Skip rather than fail.
    try:
        sp_expr = conv_to_sympy(original, xor_fn=sympy.Function("xor"))
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
        assert (
            orig_val == rt_val
        ), f"roundtrip mismatch at {env}: original={orig_val}, roundtripped={rt_val}, expr={expr}"
        checked += 1
    assume(checked > 0)  # reject vacuous passes (all envs skipped)


@given(expr=expressions(max_depth=4))
def test_import_roundtrip_same_node(expr: ExprTree) -> None:
    """Importing into another context and back preserves canonical identity."""
    ctx1 = ixsimpl.Context()
    ctx2 = ixsimpl.Context()
    try:
        original = to_ixsimpl(ctx1, expr)
    except ValueError:
        assume(False)
    assume(not original.is_error)

    imported = ctx2.import_(original)
    imported_again = ctx2.import_(original)
    roundtripped = ctx1.import_(imported)

    assert ixsimpl.same_node(imported, imported_again)
    assert ixsimpl.same_node(roundtripped, original)


@given(expr=expressions(max_depth=4))
def test_serialize_roundtrip_same_node(expr: ExprTree) -> None:
    """Serializing into another context and back preserves canonical identity."""
    ctx1 = ixsimpl.Context()
    ctx2 = ixsimpl.Context()
    try:
        original = to_ixsimpl(ctx1, expr)
    except ValueError:
        assume(False)
    assume(not original.is_error)

    data = ctx1.serialize(original)
    decoded = ctx2.deserialize(data)
    decoded_again = ctx2.deserialize(data)
    roundtrip_data = ctx2.serialize(decoded)
    roundtripped = ctx1.deserialize(roundtrip_data)

    assert ixsimpl.same_node(decoded, decoded_again)
    assert roundtrip_data == data
    assert ixsimpl.same_node(roundtripped, original)


def test_node_ptr_exposes_canonical_node_address() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    x_again = ctx.sym("x")
    y = ctx.sym("y")

    assert isinstance(x.node_ptr, int)
    assert x.node_ptr != 0
    assert x_again.node_ptr == x.node_ptr
    assert y.node_ptr != x.node_ptr
    node_as_any: Any = x
    with pytest.raises(AttributeError):
        node_as_any.node_ptr = 0


@pytest.mark.forked
@pytest.mark.filterwarnings(
    r"ignore:This process \(pid=.*\) is multi-threaded, use of fork\(\) may lead "
    r"to deadlocks in the child\.:DeprecationWarning"
)
@given(data=garbage_serialized_blobs())
def test_deserialize_garbage_does_not_crash(data: bytes) -> None:
    """Total garbage rejects cleanly instead of taking the process with it."""
    ctx = ixsimpl.Context()
    ctx.deserialize(data)


@pytest.mark.forked
@pytest.mark.filterwarnings(
    r"ignore:This process \(pid=.*\) is multi-threaded, use of fork\(\) may lead "
    r"to deadlocks in the child\.:DeprecationWarning"
)
@given(expr=expressions(max_depth=4), data=st.data())
def test_deserialize_flipped_bytes_does_not_crash(expr: ExprTree, data: st.DataObject) -> None:
    """A few random byte flips must not crash even if they hit valid framing."""
    ctx = ixsimpl.Context()
    try:
        original = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not original.is_error)

    payload = bytearray(ctx.serialize(original))
    assume(len(payload) > 0)
    positions = data.draw(
        st.lists(
            st.integers(min_value=0, max_value=len(payload) - 1),
            min_size=1,
            max_size=min(4, len(payload)),
            unique=True,
        ),
        label="positions",
    )
    for pos in positions:
        payload[pos] ^= data.draw(st.integers(min_value=1, max_value=255), label=f"mask_{pos}")

    # Some mutations still land on another valid stream. The property here is
    # limited on purpose: deserialization itself must not crash the subprocess.
    ctx.deserialize(bytes(payload))


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
            _assert_sentinel_on_py_error(ixs_simplified, ctx, env, expr)
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
    assume(checked > 0)  # reject vacuous passes (all envs skipped)


@given(
    expr=expressions(max_depth=4, include_piecewise=False),
    bounds=_range_bounds_st(),
    envs=st.lists(_mixed_env_st(), min_size=1, max_size=8),
)
def test_range_soundness(expr: ExprTree, bounds: RangeBounds, envs: list[Env]) -> None:
    """Reported ranges must contain evaluations satisfying the assumptions."""
    ctx = ixsimpl.Context()
    try:
        ixs_expr = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not ixs_expr.is_error)

    range_result = ctx.range(ixs_expr, assumptions=_range_assumptions(ctx, bounds))
    if range_result is None:
        return
    lo, hi = range_result
    if lo is not None and hi is not None:
        assert lo <= hi, f"inverted range {range_result} for expr={expr}, bounds={bounds}"

    checked = 0
    for base_env in envs:
        env = _env_within_bounds(base_env, bounds)
        try:
            raw = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError, OverflowError):
            continue
        if lo is not None:
            assert lo <= raw, (
                f"range lower bound excludes value: range={range_result}, "
                f"value={raw}, env={env}, expr={expr}, bounds={bounds}"
            )
        if hi is not None:
            assert raw <= hi, (
                f"range upper bound excludes value: range={range_result}, "
                f"value={raw}, env={env}, expr={expr}, bounds={bounds}"
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
            raw = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError, OverflowError):
            _assert_sentinel_on_py_error(ixs_simplified, ctx, env, expr)
            continue
        orig = _as_int(raw)
        if orig is None:
            continue
        if not (-(1 << 62) <= orig <= (1 << 62)):
            continue
        try:
            simp = eval_ixs(ixs_simplified, ctx, env)
        except (ValueError, TypeError):
            # ixsimpl uses int64 internally; simplification may reorganize
            # subexpressions so intermediates overflow even when the final
            # Python result fits.  Skip rather than fail.
            continue
        assert orig == simp, f"Near-overflow mismatch: {orig} != {simp} at {env}, expr={expr}"
        checked += 1
    assume(checked > 0)  # reject vacuous passes (all envs skipped)


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
            raw = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError):
            _assert_sentinel_on_py_error(ixs_simplified, ctx, env, expr)
            continue
        orig = _as_int(raw)
        if orig is None:
            continue
        simp = eval_ixs(ixs_simplified, ctx, env)
        assert orig == simp, (
            f"Targeted divisibility mismatch: {orig} != {simp} at {env}, "
            f"expr={expr}, assumption=Mod({div_sym},{divisor})==0"
        )
        checked += 1
    assume(checked > 0)  # reject vacuous passes (all envs skipped)


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
            raw = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError):
            _assert_sentinel_on_py_error(ixs_simplified, ctx, env, expr)
            continue
        orig = _as_int(raw)
        if orig is None:
            continue
        simp = eval_ixs(ixs_simplified, ctx, env)
        assert orig == simp, (
            f"Targeted bounds mismatch: {orig} != {simp} at {env}, "
            f"expr={expr}, bounds={lo} <= {bound_sym} < {hi}"
        )
        checked += 1
    assume(checked > 0)  # reject vacuous passes (all envs skipped)


# --- Priority 1: cheap, high-ROI fuzz tests ---


@given(
    expr=expressions(),
    envs=st.lists(_mixed_env_st(), min_size=1, max_size=10),
)
def test_expand_semantics(expr: ExprTree, envs: list[Env]) -> None:
    """expand() preserves numerical semantics."""
    ctx = ixsimpl.Context()
    try:
        ixs_expr = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not ixs_expr.is_error)
    expanded = ixs_expr.expand()
    assume(not expanded.is_error)

    checked = 0
    for env in envs:
        try:
            orig = eval_ixs(ixs_expr, ctx, env)
        except (ValueError, TypeError):
            continue
        exp_val = eval_ixs(expanded, ctx, env)
        assert orig == exp_val, f"expand mismatch: {orig} != {exp_val} at {env}, expr={expr}"
        checked += 1
    assume(checked > 0)


@given(
    exprs=st.lists(expressions(max_depth=4), min_size=1, max_size=5),
    envs=st.lists(_env_st(0, 100), min_size=1, max_size=5),
)
def test_simplify_batch_matches_individual(exprs: list[ExprTree], envs: list[Env]) -> None:
    """simplify_batch produces the same results as individual simplify calls."""
    ctx = ixsimpl.Context()
    ixs_exprs = []
    for tree in exprs:
        try:
            ixs_exprs.append(to_ixsimpl(ctx, tree))
        except ValueError:
            assume(False)
    assume(all(not e.is_error for e in ixs_exprs))

    individual = [e.simplify() for e in ixs_exprs]
    batch_copy = list(ixs_exprs)
    ctx.simplify_batch(batch_copy)

    checked = 0
    for env in envs:
        for j in range(len(ixs_exprs)):
            if individual[j].is_error or batch_copy[j].is_error:
                continue
            try:
                ind_val = eval_ixs(individual[j], ctx, env)
            except (ValueError, TypeError):
                continue
            try:
                bat_val = eval_ixs(batch_copy[j], ctx, env)
            except (ValueError, TypeError):
                continue
            assert ind_val == bat_val, (
                f"batch vs individual mismatch: {ind_val} != {bat_val} "
                f"at {env}, expr[{j}]={exprs[j]}"
            )
            checked += 1
    assume(checked > 0)


@given(
    expr=expressions(max_depth=4),
    sub_sym=st.sampled_from(_VARS),
    sub_val=st.integers(min_value=-50, max_value=50),
    envs=st.lists(_env_st(1, 50), min_size=1, max_size=10),
)
def test_subs_correctness(
    expr: ExprTree,
    sub_sym: str,
    sub_val: int,
    envs: list[Env],
) -> None:
    """subs(sym, val) then eval == eval with sym=val in the environment."""
    ctx = ixsimpl.Context()
    try:
        ixs_expr = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not ixs_expr.is_error)

    substituted = ixs_expr.subs(sub_sym, ctx.int_(sub_val))
    assume(not substituted.is_error)

    checked = 0
    for base_env in envs:
        full_env = {**base_env, sub_sym: sub_val}
        try:
            expected = eval_expr(expr, full_env)
        except (ZeroDivisionError, ValueError, TypeError):
            _assert_sentinel_on_py_error(substituted, ctx, full_env, expr)
            continue
        exp_int = _as_int(expected)
        if exp_int is None:
            continue
        try:
            got = eval_ixs(substituted, ctx, full_env)
        except (ValueError, TypeError):
            continue
        assert exp_int == got, (
            f"subs mismatch: {exp_int} != {got} at {full_env}, "
            f"expr={expr}, subs({sub_sym}={sub_val})"
        )
        checked += 1
    assume(checked > 0)


@given(
    expr=expressions(),
    div_sym=st.sampled_from(_VARS),
    divisor=st.integers(min_value=2, max_value=64),
    bound_sym=st.sampled_from(_VARS),
    lo=st.integers(min_value=0, max_value=50),
    hi=st.integers(min_value=51, max_value=200),
    env_mults=st.lists(
        st.tuples(_env_st(1, 50), st.integers(0, 25)),
        min_size=1,
        max_size=10,
    ),
)
def test_combined_divisibility_and_bounds(
    expr: ExprTree,
    div_sym: str,
    divisor: int,
    bound_sym: str,
    lo: int,
    hi: int,
    env_mults: list[tuple[Env, int]],
) -> None:
    """Simplification with both divisibility and bound assumptions."""
    assume(div_sym != bound_sym)
    ctx = ixsimpl.Context()
    try:
        ixs_expr = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not ixs_expr.is_error)

    sym_d = ctx.sym(div_sym)
    sym_b = ctx.sym(bound_sym)
    assumptions = [
        ctx.eq(ixsimpl.mod(sym_d, ctx.int_(divisor)), ctx.int_(0)),
        sym_b >= ctx.int_(lo),
        sym_b < ctx.int_(hi),
    ]
    ixs_simplified = ixs_expr.simplify(assumptions=assumptions)
    assume(not ixs_simplified.is_error)

    checked = 0
    for base_env, mult in env_mults:
        env = {**base_env, div_sym: mult * divisor}
        env[bound_sym] = max(lo, min(hi - 1, env[bound_sym]))
        try:
            raw = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError):
            _assert_sentinel_on_py_error(ixs_simplified, ctx, env, expr)
            continue
        orig = _as_int(raw)
        if orig is None:
            continue
        simp = eval_ixs(ixs_simplified, ctx, env)
        assert orig == simp, (
            f"Combined mismatch: {orig} != {simp} at {env}, expr={expr}, "
            f"Mod({div_sym},{divisor})==0, {lo}<={bound_sym}<{hi}"
        )
        checked += 1
    assume(checked > 0)


# --- Priority 2: targeted rule-exercising tests ---


@given(
    sym=st.sampled_from(_VARS),
    N=st.integers(min_value=2, max_value=32),
    envs=st.lists(_env_st(1, 100), min_size=1, max_size=10),
)
def test_recognize_mod_targeted(
    sym: str,
    N: int,
    envs: list[Env],
) -> None:
    """x + (-N)*floor(x/N) should simplify to Mod(x, N)."""
    expr: ExprTree = ("add", sym, ("mul", ("neg", N), ("floor", ("div", sym, N))))

    ctx = ixsimpl.Context()
    try:
        ixs_expr = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not ixs_expr.is_error)
    simplified = ixs_expr.simplify()
    assume(not simplified.is_error)

    s = str(simplified)
    assert "floor" not in s, f"recognize_mod should have fired: {s}"

    checked = 0
    for env in envs:
        try:
            raw = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError):
            _assert_sentinel_on_py_error(simplified, ctx, env, expr)
            continue
        orig = _as_int(raw)
        if orig is None:
            continue
        simp = eval_ixs(simplified, ctx, env)
        assert orig == simp, f"recognize_mod mismatch: {orig} != {simp} at {env}"
        checked += 1
    assume(checked > 0)


@given(
    sym=st.sampled_from(_VARS),
    m=st.integers(min_value=2, max_value=32),
    envs=st.lists(_env_st(1, 100), min_size=1, max_size=10),
)
def test_cancel_floor_mod_pairs_targeted(
    sym: str,
    m: int,
    envs: list[Env],
) -> None:
    """m*floor(x/m) + Mod(x, m) should simplify to x."""
    expr: ExprTree = ("add", ("mul", m, ("floor", ("div", sym, m))), ("mod", sym, m))

    ctx = ixsimpl.Context()
    try:
        ixs_expr = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not ixs_expr.is_error)
    simplified = ixs_expr.simplify()
    assume(not simplified.is_error)

    assert str(simplified) == sym, f"Expected {sym}, got {simplified}"

    checked = 0
    for env in envs:
        try:
            raw = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError):
            _assert_sentinel_on_py_error(simplified, ctx, env, expr)
            continue
        orig = _as_int(raw)
        if orig is None:
            continue
        simp = eval_ixs(simplified, ctx, env)
        assert orig == simp
        checked += 1
    assume(checked > 0)


@given(
    other_sym=st.sampled_from(_VARS),
    c=st.integers(min_value=1, max_value=15),
    K_val=st.integers(min_value=16, max_value=50),
    envs=st.lists(_env_st(0, 100), min_size=1, max_size=10),
)
def test_floor_drop_const_sym_targeted(
    other_sym: str,
    c: int,
    K_val: int,
    envs: list[Env],
) -> None:
    """floor((other + c) / K) with 0 <= c < K: exercises floor_drop_const."""
    assume(c < K_val)
    expr: ExprTree = ("floor", ("div", ("add", other_sym, c), K_val))

    ctx = ixsimpl.Context()
    try:
        ixs_expr = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not ixs_expr.is_error)
    simplified = ixs_expr.simplify()
    assume(not simplified.is_error)

    checked = 0
    for env in envs:
        try:
            raw = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError):
            _assert_sentinel_on_py_error(simplified, ctx, env, expr)
            continue
        orig = _as_int(raw)
        if orig is None:
            continue
        simp = eval_ixs(simplified, ctx, env)
        assert orig == simp, f"floor_drop_const_sym mismatch: {orig} != {simp}"
        checked += 1
    assume(checked > 0)


def test_check_entailment_basic() -> None:
    """Mirrors the Wave evaluate_with_assumptions use case."""
    ctx = ixsimpl.Context()
    M = ctx.sym("M")

    assume_lt64 = M < 64

    assert ctx.check(M > 70, assumptions=[assume_lt64]) is False
    assert ctx.check(M < 70, assumptions=[assume_lt64]) is True
    assert ctx.check(M < 32, assumptions=[assume_lt64]) is None

    assert ctx.check(ctx.eq(M, 5), assumptions=[ctx.eq(M, 5)]) is True
    assert ctx.check(ctx.eq(M, 3), assumptions=[ctx.eq(M, 5)]) is False


def test_check_two_sided_bounds() -> None:
    ctx = ixsimpl.Context()
    N = ctx.sym("N")
    assumes = [N >= 0, N <= 10]

    assert ctx.check(ctx.ne(N, 20), assumptions=assumes) is True
    assert ctx.check(N >= 0, assumptions=assumes) is True
    assert ctx.check(N < 0, assumptions=assumes) is False
    assert ctx.check(N > 5, assumptions=assumes) is None


def test_check_modular_entailment() -> None:
    ctx = ixsimpl.Context()
    K = ctx.sym("K")
    N = ctx.sym("N")

    assume_k_256 = [ctx.eq(K % 256, 0)]
    assert ctx.check(ctx.eq(K % 32, 0), assumptions=assume_k_256) is True
    assert ctx.check(ctx.ne(K % 32, 0), assumptions=assume_k_256) is False
    assert ctx.check(ctx.eq(K % 32, 1), assumptions=assume_k_256) is False
    assert ctx.check(ctx.ne(K % 32, 1), assumptions=assume_k_256) is True
    assert ctx.check(ctx.eq(K % 512, 0), assumptions=assume_k_256) is None

    assume_k_rem = [ctx.eq(K % 8, 3)]
    assert ctx.check(ctx.eq(K % 4, 3), assumptions=assume_k_rem) is True
    assert ctx.check(ctx.eq(K % 4, 1), assumptions=assume_k_rem) is False
    assert ctx.check(ctx.eq(K % 4, 7), assumptions=assume_k_rem) is False
    assert ctx.check(ctx.ne(K % 4, 7), assumptions=assume_k_rem) is True

    assumes = [ctx.eq(K % 32, 0), ctx.eq(N % 16, 0)]
    assert ctx.check(ctx.eq((3 * K) % 32, 0), assumptions=assumes) is True
    assert ctx.check(ctx.eq((K + N) % 16, 0), assumptions=assumes) is True


def test_check_bitwise_fact_entailment() -> None:
    ctx = ixsimpl.Context()
    d = ctx.sym("d")
    x = ctx.sym("x")

    assert ctx.pow2_fact(ctx.int_(0)) == "or_zero"
    assert ctx.pow2_fact(ctx.int_(8)) == "positive"
    assert ctx.pow2_fact(ctx.int_(6)) is None

    pow2_expr = d & (d - 1)
    pow2_assume = ctx.eq(pow2_expr, 0)
    assert ctx.pow2_fact(d, assumptions=[pow2_assume]) == "or_zero"
    assert ctx.pow2_fact(d, assumptions=[pow2_assume, d > 0]) == "positive"
    assert ctx.pow2_fact(x + 1, assumptions=[ctx.eq(x, 7)]) == "positive"
    assert ctx.pow2_fact(x + 1, assumptions=[ctx.eq(x, -1)]) == "or_zero"
    assert ctx.check(ctx.eq(pow2_expr, 0), assumptions=[pow2_assume]) is True
    assert ctx.check(ctx.ne(pow2_expr, 0), assumptions=[pow2_assume]) is False
    assert ctx.check(ctx.eq(pow2_expr, 4), assumptions=[pow2_assume]) is False
    assert ctx.check(d >= 0, assumptions=[pow2_assume]) is True
    assert ctx.range(d, assumptions=[pow2_assume]) == (0, None)

    mask_assume = ctx.eq(x & 15, 5)
    assert ctx.check(ctx.eq(x & 7, 5), assumptions=[mask_assume]) is True
    assert ctx.check(ctx.eq(x & 7, 1), assumptions=[mask_assume]) is False
    assert ctx.check(ctx.eq(x & 16, 0), assumptions=[mask_assume]) is None


def test_check_contradictory_assumptions_unknown() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("x")

    assert ctx.check(x >= 0, assumptions=[x >= 10, x <= 5]) is None
    assert ctx.pow2_fact(x, assumptions=[x >= 10, x <= 5]) is None


def test_integrality_queries_structural_assumption_and_facts() -> None:
    ctx = ixsimpl.Context()
    x, k = ctx.sym("x"), ctx.sym("K")
    reciprocal = 1 / x
    scaled = k / 32
    total = x + scaled
    half = ctx.rat(1, 2)
    congruence = ctx.eq(k % 32, 0)

    assert x.is_integer_valued
    assert not reciprocal.is_integer_valued
    assert not scaled.is_integer_valued
    assert not total.is_integer_valued
    assert not half.is_integer_valued

    assert ctx.integer_valued(reciprocal) is None
    assert ctx.integer_valued(scaled) is None
    assert ctx.integer_valued(total) is None
    assert ctx.integer_valued(half) is False
    assert ctx.integer_valued(scaled, assumptions=[congruence]) is True
    assert ctx.integer_valued(total, assumptions=[congruence]) is True

    facts = ctx.facts()
    facts.assume(congruence)
    piecewise = ixsimpl.pw((scaled, x > 0), (x, ctx.true_()))
    assert not piecewise.is_integer_valued
    assert ctx.integer_valued(piecewise, facts=facts) is True
    assert ctx.divisible(k, 32, facts) is True
    assert ctx.divisible(k, -32, facts) is True
    assert ctx.divisible(k, 64, facts) is None


def test_integrality_and_divisibility_invalid_inputs() -> None:
    ctx = ixsimpl.Context()
    other = ixsimpl.Context()
    x = ctx.sym("x")
    facts = ctx.facts()
    contradictory = ctx.facts()
    contradictory.assume(x >= 10)
    contradictory.assume(x <= 5)
    sentinel = ctx.parse_expr("(")

    assert ctx.integer_valued(x, facts=contradictory) is None
    assert ctx.divisible(ctx.int_(64), 32, contradictory) is None
    assert not sentinel.is_integer_valued
    assert ctx.integer_valued(sentinel) is None
    assert ctx.divisible(sentinel, 8, facts) is None

    with pytest.raises(ValueError, match="different context"):
        ctx.integer_valued(other.sym("x"))
    with pytest.raises(ValueError, match="different context"):
        ctx.divisible(other.sym("x"), 8, facts)
    with pytest.raises(ValueError, match="different context"):
        ctx.divisible(x, 8, other.facts())
    with pytest.raises(ValueError, match="modulus must be nonzero"):
        ctx.divisible(x, 0, facts)


def test_fact_backed_exact_divide() -> None:
    ctx = ixsimpl.Context()
    item, slot, k = ctx.sym("item"), ctx.sym("slot"), ctx.sym("K")
    facts = ctx.facts()
    expr = 64 * item + 32 * slot

    status, quotient = ctx.try_exact_divide(expr, 8, facts)
    assert status == "proven"
    assert quotient is not None
    assert ixsimpl.same_node(quotient, 8 * item + 4 * slot)

    status, quotient = ctx.try_exact_divide(expr, -8, facts)
    assert status == "proven"
    assert quotient is not None
    assert ixsimpl.same_node(quotient, -8 * item - 4 * slot)

    assert ctx.try_exact_divide(item + 1, 8, facts) == ("unknown", None)
    assert ctx.try_exact_divide(ctx.int_(65), 8, facts) == ("not_exact", None)
    assert ctx.try_exact_divide(1 / item, 1, facts) == ("unknown", None)

    facts.assume(ctx.eq(k % 32, 0))
    status, quotient = ctx.try_exact_divide(k, 32, facts)
    assert status == "proven"
    assert quotient is not None
    assert ixsimpl.same_node(quotient, k / 32)

    contradictory = ctx.facts()
    contradictory.assume(item >= 10)
    contradictory.assume(item <= 5)
    assert ctx.try_exact_divide(expr, 8, contradictory) == ("unknown", None)

    with pytest.raises(ValueError, match="divisor must be nonzero"):
        ctx.try_exact_divide(expr, 0, facts)


def test_exact_divide_binding_rejects_cross_context_inputs() -> None:
    ctx = ixsimpl.Context()
    other = ixsimpl.Context()
    x = ctx.sym("x")
    facts = ctx.facts()

    with pytest.raises(ValueError, match="different context"):
        ctx.try_exact_divide(other.sym("x"), 8, facts)
    with pytest.raises(ValueError, match="different context"):
        ctx.try_exact_divide(x, 8, other.facts())


@example(value=-(1 << 63), modulus=-(1 << 63))
@example(value=(1 << 63) - 1, modulus=-(1 << 63))
@given(
    value=st.integers(min_value=-(1 << 63), max_value=(1 << 63) - 1),
    modulus=st.integers(min_value=-(1 << 63), max_value=(1 << 63) - 1).filter(
        lambda value: value != 0
    ),
)
def test_exact_integer_divisibility_query(value: int, modulus: int) -> None:
    ctx = ixsimpl.Context()
    facts = ctx.facts()

    assert ctx.divisible(ctx.int_(value), modulus, facts) is (value % modulus == 0)
    if value == -(1 << 63) and modulus == -1:
        with pytest.raises(ValueError, match="rational overflow in division"):
            ctx.try_exact_divide(ctx.int_(value), modulus, facts)
        return

    status, quotient = ctx.try_exact_divide(ctx.int_(value), modulus, facts)
    if value % modulus == 0:
        assert status == "proven"
        assert quotient is not None
        assert int(quotient) == value // modulus
    else:
        assert status == "not_exact"
        assert quotient is None


@given(
    case=_mod_symbol_case_st(),
    env_mults=st.lists(
        st.tuples(_mixed_env_st(), st.integers(min_value=-32, max_value=32)),
        min_size=1,
        max_size=8,
    ),
)
def test_check_modular_symbol_entailment_soundness(
    case: ModSymbolCase,
    env_mults: list[tuple[Env, int]],
) -> None:
    """Proven symbol congruence checks agree with satisfying samples."""
    sym, assume_mod, rem, query_mod, target, cmp_op = case
    ctx = ixsimpl.Context()
    sym_node = ctx.sym(sym)
    assumption = ctx.eq(sym_node % assume_mod, rem)
    lhs = sym_node % query_mod
    query = ctx.eq(lhs, target) if cmp_op == "==" else ctx.ne(lhs, target)
    result = ctx.check(query, assumptions=[assumption])
    assert result is not None, f"unexpected unknown for case={case}"

    checked = 0
    for base_env, mult in env_mults:
        env = {**base_env, sym: rem + assume_mod * mult}
        expected = env[sym] % query_mod == target
        if cmp_op == "!=":
            expected = not expected
        assert result is expected, f"check={result}, expected={expected}, env={env}, case={case}"
        checked += 1
    assume(checked > 0)


@given(
    case=_mod_composite_case_st(),
    env_mults=st.lists(
        st.tuples(_mixed_env_st(), st.integers(min_value=-32, max_value=32), st.integers(-32, 32)),
        min_size=1,
        max_size=8,
    ),
)
def test_check_modular_composite_entailment_soundness(
    case: ModCompositeCase,
    env_mults: list[tuple[Env, int, int]],
) -> None:
    """Proven composite divisibility checks agree with satisfying samples."""
    sym_a, sym_b, query_mod, coeff_a, coeff_b, mod_a, mod_b, const, target, cmp_op, pattern = case
    ctx = ixsimpl.Context()
    a = ctx.sym(sym_a)
    b = ctx.sym(sym_b)
    assumptions = [ctx.eq(a % mod_a, 0)]
    if pattern == "mul":
        expr = coeff_a * a
    else:
        assumptions.append(ctx.eq(b % mod_b, 0))
        expr = coeff_a * a + coeff_b * b + const

    lhs = expr % query_mod
    query = ctx.eq(lhs, target) if cmp_op == "==" else ctx.ne(lhs, target)
    result = ctx.check(query, assumptions=assumptions)
    assert result is not None, f"unexpected unknown for case={case}"

    checked = 0
    for base_env, mult_a, mult_b in env_mults:
        env = {**base_env, sym_a: mod_a * mult_a}
        if pattern == "mul":
            raw = coeff_a * env[sym_a]
        else:
            env[sym_b] = mod_b * mult_b
            raw = coeff_a * env[sym_a] + coeff_b * env[sym_b] + const
        expected = raw % query_mod == target
        if cmp_op == "!=":
            expected = not expected
        assert result is expected, f"check={result}, expected={expected}, env={env}, case={case}"
        checked += 1
    assume(checked > 0)


@given(
    case=_bit_mask_case_st(),
    base_values=st.lists(st.integers(min_value=0, max_value=1023), min_size=1, max_size=8),
)
def test_check_bit_mask_entailment_soundness(
    case: BitMaskCase,
    base_values: list[int],
) -> None:
    """Proven mask checks agree with satisfying samples."""
    sym, pattern, mask, assume_value, query_mask, target, cmp_op = case
    ctx = ixsimpl.Context()
    sym_node = ctx.sym(sym)
    assumption = _bit_mask_assumption(ctx, sym_node, pattern, mask, assume_value)
    lhs = sym_node & query_mask
    query = ctx.eq(lhs, target) if cmp_op == "==" else ctx.ne(lhs, target)
    result = ctx.check(query, assumptions=[assumption])
    if result is None:
        return

    checked = 0
    for base in base_values:
        value = _bit_mask_sample_value(pattern, mask, assume_value, base)
        assert _bit_mask_sample_satisfies(pattern, mask, assume_value, value)
        env = {sym: value}
        expected = (value & query_mask) == target
        if cmp_op == "!=":
            expected = not expected
        assert result is expected, f"check={result}, expected={expected}, env={env}, case={case}"
        checked += 1
    assume(checked > 0)


@given(
    case=_pow2_case_st(),
    values=st.lists(st.sampled_from(_POW2_OR_ZERO), min_size=1, max_size=8),
)
def test_check_pow2_entailment_soundness(
    case: Pow2Case,
    values: list[int],
) -> None:
    """Proven power-of-two checks agree with satisfying samples."""
    sym, positive, query_kind, target, cmp_op = case
    ctx = ixsimpl.Context()
    sym_node = ctx.sym(sym)
    pow2_expr = sym_node & (sym_node - 1)
    assumptions = [ctx.eq(pow2_expr, 0)]
    if positive:
        assumptions.append(sym_node > 0)

    fact = ctx.pow2_fact(sym_node, assumptions=assumptions)
    assert fact == ("positive" if positive else "or_zero")

    if query_kind == "pow2_expr":
        query = ctx.eq(pow2_expr, target) if cmp_op == "==" else ctx.ne(pow2_expr, target)
    else:
        query = sym_node >= target if cmp_op == ">=" else sym_node < target
    result = ctx.check(query, assumptions=assumptions)
    if result is None:
        return

    checked = 0
    for raw in values:
        value = 1 if positive and raw == 0 else raw
        env = {sym: value}
        if fact == "positive":
            assert _is_positive_pow2(value), f"fact={fact}, env={env}, case={case}"
        elif fact == "or_zero":
            assert value == 0 or _is_positive_pow2(value), f"fact={fact}, env={env}, case={case}"
        if query_kind == "pow2_expr":
            expected = (value & (value - 1)) == target
            if cmp_op == "!=":
                expected = not expected
        elif cmp_op == ">=":
            expected = value >= target
        else:
            expected = value < target
        assert result is expected, f"check={result}, expected={expected}, env={env}, case={case}"
        checked += 1
    assume(checked > 0)


@given(
    value=st.sampled_from(_POW2_FACT_VALUES),
    offset=st.integers(min_value=-16, max_value=16),
)
def test_pow2_fact_exact_arithmetic_soundness(value: int, offset: int) -> None:
    """Exact arithmetic ranges feed the public power-of-two fact query."""
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    expr = x + offset

    assert ctx.pow2_fact(expr, assumptions=[ctx.eq(x, value - offset)]) == _expected_pow2_fact(
        value
    )


@given(t0_values=st.lists(st.integers(min_value=0, max_value=255), min_size=1, max_size=16))
def test_xor_delta_simplification_soundness(t0_values: list[int]) -> None:
    """The corpus-shaped xor(a,b+4)-xor(a,b) rewrite preserves values."""
    ctx = ixsimpl.Context()
    t0 = ctx.sym("$T0")
    low = t0 % 8
    quad = ixsimpl.floor((t0 % 64) / 16)
    expr = 16 * ixsimpl.xor_(low, quad + 4) - 16 * ixsimpl.xor_(low, quad)
    simplified = expr.simplify()

    assert "xor" not in str(simplified)
    for value in t0_values:
        env = {"$T0": value}
        assert expr.eval(env) == simplified.eval(env)


def test_xor_delta_requires_actual_offset_operand() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    a = ctx.sym("a")
    base = x & 3
    expr = 16 * ixsimpl.xor_(a, base + 5) - 16 * ixsimpl.xor_(a, base + 1)
    simplified = expr.simplify()

    env = {"x": 3, "a": 4}
    assert expr.eval(env) == 192
    assert simplified.eval(env) == expr.eval(env)


def test_xor_delta_large_pow2_does_not_overflow() -> None:
    ctx = ixsimpl.Context()
    y = ctx.sym("y")
    big = 1 << 62
    expr = ixsimpl.xor_(ctx.int_(big), (y & 3) + big) - ixsimpl.xor_(ctx.int_(big), y & 3)
    simplified = expr.simplify()

    assert not simplified.is_error
    for value in range(4):
        env = {"y": value}
        assert simplified.eval(env) == expr.eval(env)


def test_noninteger_mod_does_not_feed_divisibility_rewrite() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    z = ctx.sym("z")
    expr = ixsimpl.ceil(z / 3 + ((x / 2) % 1) / 2)
    simplified = expr.simplify()

    env = {"x": 1, "z": 0}
    assert expr.eval(env) == 1
    assert simplified.eval(env) == expr.eval(env)


def test_fractional_mul_does_not_feed_divisibility_check() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    y = ctx.sym("y")
    expr = 2 * (y + x / 4)

    assert ctx.check(ctx.eq(expr % 2, 0)) is None


def test_check_no_assumptions() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    assert ctx.check(x > 0) is None
    assert ctx.check(x < 0) is None


def test_check_non_cmp_returns_none() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    assert ctx.check(x) is None
    assert ctx.check(x + 1) is None


def test_range_basic() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    assumptions = [x >= 0, x < 16]
    int64_min = -(2**63)
    int64_max = 2**63 - 1

    assert ctx.range(x + 5, assumptions=assumptions) == (5, 20)
    assert ctx.range(x, assumptions=[x >= 0]) == (0, None)
    assert ctx.range(x / 2, assumptions=[x >= 1, x <= 3]) == (
        Fraction(1, 2),
        Fraction(3, 2),
    )
    assert ctx.range(x % 8) == (0, 7)
    assert ctx.range(x) is None
    assert ctx.range(x, assumptions=[x >= 10, x <= 5]) is None
    assert ctx.range(-x, assumptions=[x >= 10, x <= 5]) is None
    assert ctx.range(ctx.int_(int64_min)) == (int64_min, int64_min)
    assert ctx.range(ctx.int_(int64_max)) == (int64_max, int64_max)


def test_range_composite_predicate_fact() -> None:
    ctx = ixsimpl.Context()
    a, b = ctx.sym("A"), ctx.sym("B")
    expr = 2 * a + 16 * b
    factored = 2 * (a + 8 * b)
    assumptions = [expr >= 0, -2147483630 + expr <= 0]

    assert ctx.range(expr, assumptions=assumptions) == (0, 2147483630)
    assert ctx.range(factored, assumptions=assumptions) == (0, 2147483630)
    assert ctx.check(factored <= 2147483630, assumptions=assumptions) is True


def test_facts_range_transfer_and_substitution() -> None:
    ctx = ixsimpl.Context()
    orig = ctx.sym("orig")
    a, b = ctx.sym("A"), ctx.sym("B")
    replacement = a + 8 * b
    facts = ctx.facts()
    facts.assume_range(orig, 0, 1073741815)
    facts.derive_affine(orig, 2, 0, 2 * orig)

    assert ctx.range(2 * orig, facts=facts) == (0, 2147483630)

    subst = facts.subs(orig, replacement)
    assert ctx.range(replacement, facts=subst) == (0, 1073741815)
    assert ctx.range(2 * (a + 8 * b), facts=subst) == (0, 2147483630)
    assert ctx.range(2 * a + 16 * b, facts=subst) == (0, 2147483630)


def test_facts_assume_decomposes_conjunction() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    facts = ctx.facts()

    facts.assume(ixsimpl.and_(x >= 0, x <= 10))
    assert ctx.range(x, facts=facts) == (0, 10)

    with pytest.raises(ValueError):
        facts.assume(ixsimpl.or_(x >= 0, x <= 10))


def test_compound_assumption_ingestion_parity() -> None:
    ctx = ixsimpl.Context()
    x, d = ctx.sym("x"), ctx.sym("d")
    range_pred = ixsimpl.and_(x >= 0, x < 32)
    pow2_pred = ixsimpl.and_(ctx.eq(d & (d - 1), 0), d > 0)
    pred = ixsimpl.and_(range_pred, pow2_pred)
    query = x <= 31
    exprs = [x % 32, ixsimpl.floor(x / 32)]

    assert (x % 32).simplify(assumptions=[pred]) == x
    ctx.simplify_batch(exprs, assumptions=[pred])
    assert exprs == [x, ctx.int_(0)]
    assert ctx.check(query, assumptions=[pred]) is True
    assert ctx.pow2_fact(d, assumptions=[pred]) == "positive"
    assert ctx.range(x, assumptions=[pred]) == (0, 31)

    facts = ctx.facts()
    facts.assume(pred)
    assert ctx.check(query, facts=facts) is True
    assert ctx.pow2_fact(d, facts=facts) == "positive"
    assert ctx.range(x, facts=facts) == (0, 31)


def test_compound_assumption_rejection_is_atomic() -> None:
    ctx = ixsimpl.Context()
    x, y = ctx.sym("x"), ctx.sym("y")
    ge0, le10 = x >= 0, x <= 10
    either = ixsimpl.or_(ge0, le10)
    negated = ixsimpl.not_(ixsimpl.and_(ge0, le10))
    mod = x % 32

    with pytest.raises(ValueError, match="OR predicates"):
        mod.simplify(assumptions=[either])
    with pytest.raises(ValueError, match="OR predicates"):
        ctx.simplify_batch([mod], assumptions=[either])
    with pytest.raises(ValueError, match="OR predicates"):
        ctx.check(x >= 0, assumptions=[either])
    with pytest.raises(ValueError, match="OR predicates"):
        ctx.pow2_fact(x, assumptions=[either])
    with pytest.raises(ValueError, match="OR predicates"):
        ctx.range(x, assumptions=[either])
    with pytest.raises(ValueError, match="NOT predicates"):
        ctx.range(x, assumptions=[negated])

    facts = ctx.facts()
    facts.assume(ge0)
    with pytest.raises(ValueError, match="OR predicates"):
        facts.assume(ixsimpl.and_(y >= 5, either))
    assert ctx.range(x, facts=facts) == (0, None)
    assert ctx.range(y, facts=facts) is None


def test_facts_assume_deep_conjunction() -> None:
    ctx = ixsimpl.Context()
    facts = ctx.facts()
    symbols = [ctx.sym(f"d{i}") for i in range(300)]
    pred = symbols[0] >= 0

    for i, sym in enumerate(symbols[1:], start=1):
        pred = ixsimpl.and_(pred, sym >= i)

    facts.assume(pred)
    assert ctx.range(symbols[-1], assumptions=[pred]) == (299, None)
    assert ctx.range(symbols[0], facts=facts) == (0, None)
    assert ctx.range(symbols[-1], facts=facts) == (299, None)


def test_facts_canonical_expansion_does_not_record_errors() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    x65 = x
    facts = ctx.facts()

    for _ in range(64):
        x65 = x65 * x

    ctx.clear_errors()
    facts.assume_range(x65, 5, None)
    assert ctx.errors == []
    assert ctx.range(x65, facts=facts) == (5, None)
    assert ctx.errors == []


@given(
    lo=st.integers(min_value=-128, max_value=128),
    width=st.integers(min_value=0, max_value=256),
    scale=st.integers(min_value=-8, max_value=8),
    offset=st.integers(min_value=-128, max_value=128),
)
def test_facts_affine_transfer_fuzz(lo: int, width: int, scale: int, offset: int) -> None:
    ctx = ixsimpl.Context()
    orig = ctx.sym("orig")
    hi = lo + width
    derived = scale * orig + offset
    expected = sorted((scale * lo + offset, scale * hi + offset))
    facts = ctx.facts()

    facts.assume_range(orig, lo, hi)
    facts.derive_affine(orig, scale, offset, derived)

    assert ctx.range(derived, facts=facts) == (expected[0], expected[1])


@given(
    lo=st.integers(min_value=-128, max_value=128),
    width=st.integers(min_value=0, max_value=256),
    scale=st.integers(min_value=-8, max_value=8).filter(lambda x: x != 0),
    stride=st.integers(min_value=-8, max_value=8).filter(lambda x: x != 0),
    offset=st.integers(min_value=-64, max_value=64),
)
def test_facts_canonical_affine_spelling_fuzz(
    lo: int,
    width: int,
    scale: int,
    stride: int,
    offset: int,
) -> None:
    ctx = ixsimpl.Context()
    a, b = ctx.sym("A"), ctx.sym("B")
    hi = lo + width
    expanded = scale * a + (scale * stride) * b + offset
    factored = scale * (a + stride * b) + offset
    facts = ctx.facts()

    facts.assume_range(expanded, lo, hi)

    assert ctx.range(factored, facts=facts) == (lo, hi)


def test_has_basic() -> None:
    ctx = ixsimpl.Context()
    x, y, z = ctx.sym("x"), ctx.sym("y"), ctx.sym("z")
    expr = x + 2 * y
    assert expr.has(x)
    assert expr.has(y)
    assert not expr.has(z)
    assert x.has(x)
    assert not ctx.int_(42).has(x)


def test_abs_simplifies_under_bounds() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    a = ixsimpl.abs_(x)
    assert a.tag == ixsimpl.PIECEWISE

    pos = a.simplify(assumptions=[x >= 0])
    assert str(pos) == "x"

    neg = a.simplify(assumptions=[x < 0])
    assert str(neg) == "-x"


def test_abs_constant() -> None:
    ctx = ixsimpl.Context()
    assert str(ixsimpl.abs_(ctx.int_(5))) == "5"
    assert str(ixsimpl.abs_(ctx.int_(-3))) == "3"


# ---------------------------------------------------------------------------
#  Expr.eval and lambdify
# ---------------------------------------------------------------------------


def test_eval_basic() -> None:
    ctx = ixsimpl.Context()
    x, y = ctx.sym("x"), ctx.sym("y")
    expr = x + 2 * y
    assert expr.eval({"x": 3, "y": 4}) == 11
    assert expr.eval({"x": 0, "y": 0}) == 0
    assert expr.eval({"x": -1, "y": 5}) == 9


def test_eval_constant() -> None:
    ctx = ixsimpl.Context()
    assert ctx.int_(42).eval({}) == 42


def test_eval_with_expr_keys() -> None:
    ctx = ixsimpl.Context()
    x, y = ctx.sym("x"), ctx.sym("y")
    expr = x * y
    assert expr.eval({x: 7, y: 6}) == 42


def test_eval_raises_on_unbound() -> None:
    ctx = ixsimpl.Context()
    x, y = ctx.sym("x"), ctx.sym("y")
    expr = x + y
    import pytest

    with pytest.raises(TypeError):
        expr.eval({"x": 1})


def test_eval_floor_mod() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    expr = ixsimpl.floor(x / 3)
    assert expr.eval({"x": 10}) == 3
    assert expr.eval({"x": 9}) == 3
    assert expr.eval({"x": 8}) == 2

    expr2 = ixsimpl.mod(x, 4)
    assert expr2.eval({"x": 10}) == 2
    assert expr2.eval({"x": 8}) == 0


@given(
    dividend=st.integers(min_value=-(1 << 63), max_value=(1 << 63) - 1),
    divisor=st.integers(min_value=1, max_value=(1 << 63) - 1),
)
def test_mod_positive_literal_contract(dividend: int, divisor: int) -> None:
    ctx = ixsimpl.Context()
    result = ixsimpl.mod(ctx.int_(dividend), ctx.int_(divisor))
    assert not result.is_error
    assert result.eval({}) == dividend % divisor


@given(divisor=st.integers(min_value=-(1 << 63), max_value=0))
def test_mod_rejects_nonpositive_literal(divisor: int) -> None:
    ctx = ixsimpl.Context()
    result = ixsimpl.mod(ctx.sym("x"), ctx.int_(divisor))
    assert result.is_domain_error
    assert any("divisor" in error for error in ctx.errors)


def test_mod_symbolic_divisor_contract() -> None:
    ctx = ixsimpl.Context()
    x, m = ctx.sym("x"), ctx.sym("m")
    expr = ixsimpl.mod(x, m)

    assert not expr.is_error
    assert ixsimpl.same_node(expr.simplify(assumptions=[m > 0]), expr)
    assert expr.simplify(assumptions=[m < 0]).is_domain_error
    assert expr.simplify(assumptions=[m <= 0]).is_domain_error
    assert expr.simplify(assumptions=[ctx.eq(m, 0)]).is_domain_error
    assert expr.eval({"x": -7, "m": 3}) == 2
    with pytest.raises(TypeError):
        expr.eval({"x": -7, "m": -3})

    assert ixsimpl.mod(x, ctx.rat(-1, 2)).is_domain_error


def test_percent_operator_builds_mod() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("x")

    assert ixsimpl.same_node(x % 4, ixsimpl.mod(x, 4))
    assert ixsimpl.same_node(17 % x, ixsimpl.mod(ctx.int_(17), x))
    assert (x % 4).eval({"x": -7}) == 1


def test_bitwise_operators_build_and_or() -> None:
    ctx = ixsimpl.Context()
    x, y = ctx.sym("x"), ctx.sym("y")

    assert ixsimpl.same_node(x & y, ixsimpl.and_(x, y))
    assert ixsimpl.same_node(x | y, ixsimpl.or_(x, y))
    assert ixsimpl.same_node(x & 3, ixsimpl.and_(x, 3))
    assert ixsimpl.same_node(3 & x, ixsimpl.and_(ctx.int_(3), x))
    assert ixsimpl.same_node(x | 1, ixsimpl.or_(x, 1))
    assert ixsimpl.same_node(1 | x, ixsimpl.or_(ctx.int_(1), x))
    assert (x & 3).eval({"x": 6}) == 2
    assert (x | 1).eval({"x": 6}) == 7
    assert ixsimpl.same_node(ctx.parse_expr("x & 3"), x & 3)
    assert ixsimpl.same_node(ctx.parse_expr("x | y"), x | y)
    assert ixsimpl.same_node(ctx.parse_expr("1 | x & 3"), ctx.int_(1) | (x & 3))
    assert ixsimpl.same_node(ctx.parse_pred("x & 3 == 1"), ctx.eq(x & 3, 1))
    assert ixsimpl.same_node(ctx.parse_pred("(x & 3) == 1"), ctx.eq(x & 3, 1))
    assert ixsimpl.same_node(ctx.parse_pred("(x | y) == 0"), ctx.eq(x | y, 0))
    assert str(ctx.parse_pred("x & y")) == "x != 0 & y != 0"
    assert str(ctx.parse_pred("x & y == 0")) == "y == 0 & x != 0"
    assert str(ctx.parse_pred("x | y == 0")) == "y == 0 | x != 0"
    assert str(ctx.parse_pred("x > 0 | y > 0")) == "x > 0 | y > 0"

    simplified = ixsimpl.xor_(x & 7, x & 24).simplify()
    assert "xor" not in str(simplified)
    for value in range(32):
        env = {"x": value}
        assert ixsimpl.xor_(x & 7, x & 24).eval(env) == simplified.eval(env)


def test_lambdify_single_expr() -> None:
    ctx = ixsimpl.Context()
    x, y = ctx.sym("x"), ctx.sym("y")
    f = ixsimpl.lambdify([x, y], x + 2 * y)
    assert f(3, 4) == 11
    assert f(0, 0) == 0
    assert f(-1, 5) == 9


def test_lambdify_scalar_symbol() -> None:
    """Single symbol (not a list) is accepted."""
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    f = ixsimpl.lambdify(x, x * x)
    assert f(5) == 25
    assert f(-3) == 9


def test_lambdify_multi_expr() -> None:
    ctx = ixsimpl.Context()
    x, y = ctx.sym("x"), ctx.sym("y")
    f = ixsimpl.lambdify([x, y], [x + y, x - y, x * y])
    assert f(10, 3) == [13, 7, 30]
    assert f(0, 0) == [0, 0, 0]


def test_lambdify_constant() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    f = ixsimpl.lambdify([x], ctx.int_(7))
    assert f(999) == 7


def test_lambdify_string_symbols() -> None:
    """String symbol names work too."""
    ctx = ixsimpl.Context()
    x, y = ctx.sym("x"), ctx.sym("y")
    f = ixsimpl.lambdify(["x", "y"], x * y + 1)
    assert f(6, 7) == 43


@given(
    expr=expressions(max_depth=3),
    envs=st.lists(_env_st(1, 50), min_size=1, max_size=10),
)
def test_eval_matches_subs(expr: ExprTree, envs: list[Env]) -> None:
    """Expr.eval agrees with manual subs for integer results."""
    ctx = ixsimpl.Context()
    try:
        ixs_expr = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not ixs_expr.is_error)
    simplified = ixs_expr.simplify()
    assume(not simplified.is_error)

    for env in envs:
        try:
            via_subs = eval_ixs(simplified, ctx, env)
        except (ValueError, TypeError):
            continue
        via_eval = simplified.eval(env)
        assert via_subs == via_eval, f"eval vs subs mismatch: {via_subs} != {via_eval} at {env}"


@given(
    expr=expressions(max_depth=3),
    envs=st.lists(_env_st(1, 50), min_size=1, max_size=10),
)
def test_lambdify_matches_eval(expr: ExprTree, envs: list[Env]) -> None:
    """lambdify callable agrees with Expr.eval."""
    ctx = ixsimpl.Context()
    try:
        ixs_expr = to_ixsimpl(ctx, expr)
    except ValueError:
        assume(False)
    assume(not ixs_expr.is_error)
    simplified = ixs_expr.simplify()
    assume(not simplified.is_error)

    syms = sorted(simplified.free_symbols, key=lambda s: s.sym_name)
    if not syms:
        assume(False)
    f = ixsimpl.lambdify(syms, simplified)

    checked = 0
    for env in envs:
        args = [env[s.sym_name] for s in syms]
        try:
            via_eval = simplified.eval(env)
        except (TypeError, ValueError):
            continue
        via_lam = f(*args)
        assert via_eval == via_lam, f"lambdify vs eval mismatch: {via_eval} != {via_lam} at {env}"
        checked += 1
    assume(checked > 0)
