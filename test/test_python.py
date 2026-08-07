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
    """Composite modular proof case, including fact-integral denominators."""
    names = draw(st.lists(sym_names, min_size=2, max_size=2, unique=True))
    query_mod = draw(st.integers(min_value=2, max_value=64))
    coeffs = [c for c in range(-8, 9) if c != 0 and c % query_mod != 0]
    coeff_a = draw(st.sampled_from(coeffs))
    coeff_b = draw(st.sampled_from(coeffs))
    mod_a = query_mod
    mod_b = query_mod
    const = query_mod * draw(st.integers(min_value=-8, max_value=8))
    pattern = draw(st.sampled_from(["mul", "add", "reciprocal"]))
    if pattern == "reciprocal":
        target = 0
        cmp_op = "=="
    else:
        target = draw(st.sampled_from([0, -1, query_mod]))
        cmp_op = draw(st.sampled_from(["==", "!="]))
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
    if op in ("xor", "bitand", "bitor"):
        nargs = draw(st.integers(min_value=2, max_value=5))
        if draw(st.integers(min_value=0, max_value=3)) == 0:
            args = draw(
                st.lists(
                    st.one_of(sym_names, small_ints),
                    min_size=nargs,
                    max_size=nargs,
                )
            )
        else:
            args = draw(
                st.lists(
                    st.integers(min_value=0, max_value=255),
                    min_size=nargs,
                    max_size=nargs,
                )
            )
        return (op, *args)
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
    elif op in ("max", "min"):
        rest = draw(
            st.lists(
                st.one_of(sym_names, small_ints, small_rats),
                min_size=1,
                max_size=4,
            )
        )
        return (op, a, *rest)
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
    rest = draw(
        st.lists(
            conditions(max_depth=max_depth - 2),
            min_size=1,
            max_size=3,
        )
    )
    return (combiner, c1, *rest)


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
        return sympy.Max(*(to_sympy(arg) for arg in tree[1:]), evaluate=False)
    if op == "min":
        return sympy.Min(*(to_sympy(arg) for arg in tree[1:]), evaluate=False)
    if op == "xor":
        raise ValueError("xor not supported in SymPy conversion")
    if op == "bitand":
        return sympy.Function("bitand")(*(to_sympy(arg) for arg in tree[1:]))
    if op == "bitor":
        return sympy.Function("bitor")(*(to_sympy(arg) for arg in tree[1:]))
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
        return sympy.And(*(to_sympy_cond(arg) for arg in tree[1:]))
    if op == "or":
        return sympy.Or(*(to_sympy_cond(arg) for arg in tree[1:]))
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
        return ixsimpl.max_(*(to_ixsimpl(ctx, arg) for arg in tree[1:]))
    if op == "min":
        return ixsimpl.min_(*(to_ixsimpl(ctx, arg) for arg in tree[1:]))
    if op == "xor":
        return ixsimpl.xor_(*(to_ixsimpl(ctx, arg) for arg in tree[1:]))
    if op == "bitand":
        return ixsimpl.and_(*(to_ixsimpl(ctx, arg) for arg in tree[1:]))
    if op == "bitor":
        return ixsimpl.or_(*(to_ixsimpl(ctx, arg) for arg in tree[1:]))
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
        return ixsimpl.and_(*(to_ixsimpl_cond(ctx, arg) for arg in tree[1:]))
    if op == "or":
        return ixsimpl.or_(*(to_ixsimpl_cond(ctx, arg) for arg in tree[1:]))
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
        return max(eval_expr(arg, env) for arg in tree[1:])
    if op == "min":
        return min(eval_expr(arg, env) for arg in tree[1:])
    if op in ("xor", "bitand", "bitor"):
        values = [int(eval_expr(arg, env)) for arg in tree[1:]]
        result = values[0]
        for value in values[1:]:
            if op == "xor":
                result ^= value
            elif op == "bitand":
                result &= value
            else:
                result |= value
        return result
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
        return all([eval_cond(arg, env) for arg in tree[1:]])
    if op == "or":
        return any([eval_cond(arg, env) for arg in tree[1:]])
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


@given(
    op=st.sampled_from(["max", "min", "xor", "bitand", "bitor"]),
    leaves=st.lists(st.one_of(sym_names, small_ints), min_size=2, max_size=8),
    env=_wide_env_st(),
)
def test_associative_many_grouping_fuzz(op: str, leaves: list[str | int], env: Env) -> None:
    """Flat, regrouped, and permuted construction interns one result."""
    assume(any(isinstance(leaf, str) for leaf in leaves))
    ctx = ixsimpl.Context()
    args = [to_ixsimpl(ctx, leaf) for leaf in leaves]
    ctor = {
        "max": ixsimpl.max_,
        "min": ixsimpl.min_,
        "xor": ixsimpl.xor_,
        "bitand": ixsimpl.and_,
        "bitor": ixsimpl.or_,
    }[op]

    flat = ctor(*args)
    midpoint = len(args) // 2
    lhs = args[0] if midpoint == 1 else ctor(*args[:midpoint])
    rhs_args = args[midpoint:]
    rhs = rhs_args[0] if len(rhs_args) == 1 else ctor(*rhs_args)
    grouped = ctor(lhs, rhs)
    permuted = ctor(*reversed(args))

    assert ixsimpl.same_node(flat, grouped)
    assert ixsimpl.same_node(flat, permuted)
    assert eval_ixs(flat, ctx, env) == eval_expr((op, *leaves), env)


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


def test_serialized_bytes_are_stable_and_outlive_the_source_context() -> None:
    source = ixsimpl.Context()
    expr = 4 * source.sym("x") + source.sym("y")
    data = source.serialize(expr)

    foreign = ixsimpl.Context()

    del expr
    del source
    decoded = foreign.deserialize(data)
    assert str(decoded) == "4*x + y"
    assert foreign.serialize(decoded) == data


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


@given(
    lo=st.integers(min_value=-64, max_value=32),
    width=st.integers(min_value=0, max_value=64),
    known_modulus=st.integers(min_value=2, max_value=16),
    remainder=st.integers(min_value=0, max_value=15),
    query_modulus=st.integers(min_value=2, max_value=16),
)
def test_mod_range_intersects_interval_and_congruence(
    lo: int,
    width: int,
    known_modulus: int,
    remainder: int,
    query_modulus: int,
) -> None:
    """Mod ranges equal reachable residue extrema on small finite domains."""
    remainder %= known_modulus
    hi = lo + width
    ctx = ixsimpl.Context()
    x = ctx.sym("mod_intersection_x")
    facts = ctx.facts()
    facts.assume_range(x, lo, hi)
    facts.assume(ctx.eq(x % known_modulus, remainder))
    reachable = [
        value % query_modulus for value in range(lo, hi + 1) if value % known_modulus == remainder
    ]

    result = ctx.range(x % query_modulus, facts=facts)
    if not reachable:
        assert result is None
    else:
        assert result == (min(reachable), max(reachable))


@given(delta=st.integers(min_value=-8, max_value=8).filter(bool))
def test_symbolic_floor_difference_uses_remainder_proof(delta: int) -> None:
    """A proved remainder shift keeps symbolic quotients in one bucket."""
    ctx = ixsimpl.Context()
    a, d = ctx.sym("floor_a"), ctx.sym("floor_d")
    remainder = a % d
    expr = ixsimpl.floor(a / d) - ixsimpl.floor((a + delta) / d)
    assumptions = [d > 0]
    if delta > 0:
        assumptions.append(remainder + delta < d)
    else:
        assumptions.append(remainder + delta >= 0)
    assert expr.simplify(assumptions=assumptions) == ctx.int_(0)


def test_relational_symbolic_mod_elimination() -> None:
    ctx = ixsimpl.Context()
    x, d = ctx.sym("rel_mod_x"), ctx.sym("rel_mod_d")
    modulus = 8 * d
    expr = x % modulus

    assert expr.simplify(assumptions=[d > 0, x >= 0, x < modulus]) == x
    assert expr.simplify(assumptions=[x >= 0, x < modulus]) != x
    assert expr.simplify(assumptions=[d > 0, x < modulus]) != x
    assert expr.simplify(assumptions=[d > 0, x >= 0]) != x
    assert expr.simplify(assumptions=[d > 0, x >= 0, x <= modulus]) != x
    assert expr.simplify(assumptions=[d <= 0, x >= 0, x < modulus]) != x
    assert expr.simplify(assumptions=[d > 0, d <= 0, x >= 0, x < modulus]) != x


def test_equal_mod_difference_uses_congruence() -> None:
    ctx = ixsimpl.Context()
    x, z = ctx.sym("mod_diff_x"), ctx.sym("mod_diff_z")
    expr = (x + z) % 16 - x % 16

    assert expr.simplify(assumptions=[ctx.eq(z % 16, 0)]) == ctx.int_(0)
    assert expr.simplify(assumptions=[ctx.eq(z % 16, 1)]) != ctx.int_(0)


@given(value=st.integers(min_value=-(1 << 31), max_value=(1 << 31)))
def test_scaled_mod_division_preserves_wrap(value: int) -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("scaled_mod_x")
    expr = ((2 * x) % (1 << 32)) / 2

    simplified = expr.simplify(assumptions=[ctx.eq(x, value)])
    assert simplified == ctx.int_(value % (1 << 31))


def _assert_range_contains(
    result: tuple[int | Fraction | None, int | Fraction | None] | None,
    value: int | Fraction,
) -> None:
    assert result is not None
    lo, hi = result
    if lo is not None:
        assert lo <= value
    if hi is not None:
        assert value <= hi


@given(
    lo=st.integers(min_value=-8, max_value=8),
    width=st.integers(min_value=0, max_value=8),
    exponent=st.sampled_from([-4, -3, -2, 2, 3, 4]),
)
def test_power_range_soundness(lo: int, width: int, exponent: int) -> None:
    """Power bounds contain every integer-domain evaluation."""
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    hi = lo + width
    magnitude = abs(exponent)
    positive_power = x
    for _ in range(magnitude - 1):
        positive_power = positive_power * x
    expr = positive_power if exponent > 0 else ctx.int_(1) / positive_power
    result = ctx.range(expr, assumptions=[x >= lo, x <= hi])

    if exponent < 0 and lo <= 0 <= hi:
        assert result is None
        return
    assert result is not None
    for value in range(lo, hi + 1):
        actual = value**exponent if exponent > 0 else Fraction(1, value**magnitude)
        _assert_range_contains(result, actual)


@given(
    x_lo=st.integers(min_value=0, max_value=63),
    x_width=st.integers(min_value=0, max_value=6),
    y_lo=st.integers(min_value=0, max_value=63),
    y_width=st.integers(min_value=0, max_value=6),
)
def test_xor_range_soundness(x_lo: int, x_width: int, y_lo: int, y_width: int) -> None:
    """Nonnegative XOR bounds contain all values in the input rectangle."""
    ctx = ixsimpl.Context()
    x, y = ctx.sym("x"), ctx.sym("y")
    x_hi = x_lo + x_width
    y_hi = y_lo + y_width
    result = ctx.range(
        ixsimpl.xor_(x, y),
        assumptions=[x >= x_lo, x <= x_hi, y >= y_lo, y <= y_hi],
    )

    assert result is not None
    for x_value in range(x_lo, x_hi + 1):
        for y_value in range(y_lo, y_hi + 1):
            _assert_range_contains(result, x_value ^ y_value)


@given(
    lo=st.integers(min_value=-16, max_value=16),
    width=st.integers(min_value=0, max_value=12),
    split_delta=st.integers(min_value=-2, max_value=14),
    left_offset=st.integers(min_value=-16, max_value=16),
    right_offset=st.integers(min_value=-16, max_value=16),
)
def test_piecewise_range_soundness(
    lo: int,
    width: int,
    split_delta: int,
    left_offset: int,
    right_offset: int,
) -> None:
    """First-match branch hulls contain the selected branch evaluations."""
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    hi = lo + width
    split = lo + split_delta
    dead_value = ctx.int_(1) / (x - (split - 2))
    expr = ixsimpl.pw(
        (x + left_offset, x < split),
        (dead_value, x < split - 1),
        (right_offset - x, ctx.true_()),
    )
    result = ctx.range(expr, assumptions=[x >= lo, x <= hi])

    assert result is not None
    for value in range(lo, hi + 1):
        actual = value + left_offset if value < split else right_offset - value
        _assert_range_contains(result, actual)


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


def test_cancel_floor_mod_pairs_shared_outer() -> None:
    ctx = ixsimpl.Context()
    x, k, outer, unrelated = (
        ctx.sym("outer_x"),
        ctx.sym("outer_k"),
        ctx.sym("outer_scale"),
        ctx.sym("outer_unrelated"),
    )
    floor_term = 3 * outer * k * ixsimpl.floor(x / k)
    mod_term = 3 * outer * (x % k)
    expected = 3 * outer * x

    assert ixsimpl.same_node(floor_term + mod_term, expected)

    wide = unrelated + floor_term + mod_term
    assert ixsimpl.same_node(wide.simplify(), unrelated + expected)


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


def test_integrality_query_propagates_through_nested_mod() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("nested_mod_x")
    k, d = ctx.sym("nested_mod_k"), ctx.sym("nested_mod_d")
    inner = k % 1024
    scaled = inner / 8
    nested = scaled % 2
    wave_scaled = ((8 * x) % 1024) / 8
    wave_nested = wave_scaled % 2
    dynamic = scaled % (d / 2)
    k_multiple = ctx.eq(k % 8, 0)
    d_even = ctx.eq(d % 2, 0)

    assert not scaled.is_integer_valued
    assert not nested.is_integer_valued
    assert not wave_scaled.is_integer_valued
    assert not wave_nested.is_integer_valued
    assert not dynamic.is_integer_valued
    assert ctx.integer_valued(nested) is None
    assert ctx.integer_valued(wave_scaled) is True
    assert ctx.integer_valued(wave_nested) is True
    assert ctx.integer_valued(nested, assumptions=[ctx.eq(k % 4, 0)]) is None
    assert ctx.integer_valued(nested, assumptions=[k_multiple]) is True
    assert ctx.integer_valued(dynamic, assumptions=[k_multiple]) is None
    assert ctx.integer_valued(dynamic, assumptions=[k_multiple, d_even]) is True

    facts = ctx.facts()
    facts.assume(k_multiple)
    facts.assume(d_even)
    assert ctx.integer_valued(scaled, facts=facts) is True
    assert ctx.integer_valued(nested, facts=facts) is True
    assert ctx.integer_valued(dynamic, facts=facts) is True
    assert ctx.defined(dynamic, facts=facts) is None

    range_only = ctx.facts()
    range_only.assume(k_multiple)
    range_only.assume(d_even)
    range_only.assume_range(dynamic, 0, 7)
    assert ctx.integer_valued(dynamic, facts=range_only) is True
    assert ctx.defined(dynamic, facts=range_only) is None

    closed = ctx.facts()
    closed.assume(k_multiple)
    closed.assume(d_even)
    closed.assume(d >= 2)
    assert ctx.defined(dynamic, facts=closed) is True


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
    with pytest.raises(ValueError, match="sentinel"):
        ctx.divisible(sentinel, 8, facts)

    with pytest.raises(ValueError, match="different context"):
        ctx.integer_valued(other.sym("x"))
    with pytest.raises(ValueError, match="different context"):
        ctx.divisible(other.sym("x"), 8, facts)
    with pytest.raises(ValueError, match="different context"):
        ctx.divisible(x, 8, other.facts())
    with pytest.raises(ValueError, match="modulus must be nonzero"):
        ctx.divisible(x, 0, facts)


def test_known_bits_and_congruence_bindings() -> None:
    ctx = ixsimpl.Context()
    item = ctx.sym("binding_item")
    slot = ctx.sym("binding_slot")
    k = ctx.sym("binding_k")
    facts = ctx.facts()
    facts.assume(ixsimpl.and_(slot >= 0, slot <= 15))
    facts.assume(ctx.eq(k % 15, 4))

    assert ctx.known_bits(item, facts) == (0, 0, None)
    slot_zero, slot_one, slot_pow2 = ctx.known_bits(slot, facts) or (0, 0, None)
    assert slot_zero & ~15 == ((1 << 64) - 1) & ~15
    assert slot_one & 15 == 0
    assert slot_pow2 is None

    scaled_zero, scaled_one, _ = ctx.known_bits(16 * item, facts) or (0, 0, None)
    assert scaled_zero & 15 == 15
    assert scaled_one & 15 == 0

    assert ctx.symbol_congruence(k, facts) == (15, 4)
    assert ctx.symbol_congruence(item, facts) is None
    assert ctx.congruent(k, 15, 4, facts) is True
    assert ctx.congruent(k, -15, -11, facts) is True
    assert ctx.congruent(k, 15, 5, facts) is False
    assert ctx.congruent(k, 30, 4, facts) is None
    assert ctx.congruent(3 * k + 2, 15, 14, facts) is True
    assert ctx.congruent(6 * item + 2, 3, 2, facts) is True
    assert ctx.congruent(ctx.int_(-(1 << 63)), -(1 << 63), 0, facts) is True
    assert ctx.congruent(ctx.int_((1 << 63) - 1), -(1 << 63), -1, facts) is True


def test_known_bits_and_congruence_binding_failures() -> None:
    ctx = ixsimpl.Context()
    other = ixsimpl.Context()
    x = ctx.sym("binding_invalid_x")
    facts = ctx.facts()
    contradictory = ctx.facts()
    contradictory.assume(x >= 10)
    contradictory.assume(x <= 5)
    sentinel = ctx.parse_expr("(")

    assert ctx.known_bits(x, contradictory) == (0, 0, None)
    assert ctx.symbol_congruence(x, contradictory) is None
    assert ctx.congruent(ctx.int_(1), 2, 1, contradictory) is None

    with pytest.raises(ValueError, match="must be a symbol"):
        ctx.symbol_congruence(x + 1, facts)
    with pytest.raises(ValueError, match="modulus must be nonzero"):
        ctx.congruent(x, 0, 0, facts)
    with pytest.raises(ValueError, match="different context"):
        ctx.known_bits(other.sym("x"), facts)
    with pytest.raises(ValueError, match="different context"):
        ctx.congruent(x, 8, 0, other.facts())
    with pytest.raises(ValueError, match="sentinel"):
        ctx.known_bits(sentinel, facts)
    with pytest.raises(ValueError, match="sentinel"):
        ctx.congruent(sentinel, 8, 0, facts)


def test_predicate_tree_and_total_equivalence_bindings() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("binding_equiv_x")
    y = ctx.sym("binding_equiv_y")
    z = ctx.sym("binding_equiv_z")
    k = ctx.sym("binding_equiv_k")
    p, q, r = x >= 0, y < 4, ctx.ne(z, 0)
    lhs = ixsimpl.and_(ixsimpl.and_(p, q), r)
    rhs = ixsimpl.and_(p, ixsimpl.and_(r, q))
    facts = ctx.facts()

    assert ctx.check_predicate(lhs, facts) is None
    facts.assume(p)
    facts.assume(q)
    facts.assume(r)
    assert ctx.check_predicate(lhs, facts) is True
    assert ctx.check_predicate(ixsimpl.not_(lhs), facts) is False
    assert ctx.equivalent(lhs, rhs, facts) is True

    empty = ctx.facts()
    polynomial = (x + 1) * (x + 1)
    expanded = x * x + 2 * x + 1
    reciprocal = 1 / x
    reciprocal_lhs = (x + 1) / x
    reciprocal_rhs = 1 + reciprocal
    assert ctx.equivalent(polynomial, expanded, empty) is True
    assert ctx.equivalent(reciprocal, reciprocal, empty) is None
    assert ctx.equivalent(reciprocal_lhs, reciprocal_rhs, empty) is None

    nonzero = ctx.facts()
    nonzero.assume(ctx.ne(x, 0))
    assert ctx.equivalent(reciprocal, reciprocal, nonzero) is True
    assert ctx.equivalent(reciprocal_lhs, reciprocal_rhs, nonzero) is True

    modular = ctx.facts()
    modular.assume(ctx.eq(k % 16, 0))
    mod_lhs = x % 16 < 8
    mod_rhs = (x + k) % 16 < 8
    assert ctx.equivalent(mod_lhs, mod_rhs, modular) is True
    assert ctx.equivalent(x < 8, x + k < 8, modular) is None
    grid = ctx.facts()
    grid.assume(ctx.eq(x % 16, 0))
    assert ctx.equivalent(ctx.eq(x, 0), ctx.eq(x % 16, 0), grid) is None

    assert ctx.equivalent(x < 8, x <= 7, empty) is True
    assert ctx.equivalent(x >= 8, x > 7, empty) is True
    assert ctx.equivalent(x < (1 << 63) - 1, x <= (1 << 63) - 2, empty) is True
    aligned = ctx.facts()
    aligned.assume(ctx.eq(x % 16, 0))
    assert ctx.equivalent(x < 8, x < 9, aligned) is True
    reachable = ctx.facts()
    reachable.assume(ctx.eq(x % 8, 0))
    assert ctx.equivalent(x < 8, x < 9, reachable) is None
    assert ctx.equivalent(x < 8, x >= 9, empty) is None
    assert ctx.equivalent(x / 2 < 8, x / 2 <= 7, empty) is None

    divisor = ctx.sym("binding_equiv_divisor")
    mod_safe = ctx.facts()
    mod_safe.assume(ctx.eq(x % 16, 3))
    mod_safe.assume(ctx.eq(divisor % 16, 0))
    mod_safe.assume(divisor > 0)
    assert ctx.equivalent((x + 1) % divisor, x % divisor + 1, mod_safe) is True
    assert ctx.equivalent((x - 2) % divisor, x % divisor - 2, mod_safe) is True
    assert ctx.equivalent(x % divisor + 1, (x + 1) % divisor, mod_safe) is True
    assert ctx.equivalent((x - 4) % divisor, x % divisor - 4, mod_safe) is None
    boundary = ctx.facts()
    boundary.assume(ctx.eq(x % 16, 15))
    boundary.assume(ctx.eq(divisor % 16, 0))
    boundary.assume(divisor > 0)
    assert ctx.equivalent((x + 1) % divisor, x % divisor + 1, boundary) is None
    no_positive = ctx.facts()
    no_positive.assume(ctx.eq(x % 16, 3))
    no_positive.assume(ctx.eq(divisor % 16, 0))
    assert ctx.equivalent((x + 1) % divisor, x % divisor + 1, no_positive) is None
    negative_divisor = ctx.facts()
    negative_divisor.assume(ctx.eq(x % 16, 3))
    negative_divisor.assume(ctx.eq(divisor % 16, 0))
    negative_divisor.assume(divisor < 0)
    assert ctx.equivalent((x + 1) % divisor, x % divisor + 1, negative_divisor) is None
    no_divisibility = ctx.facts()
    no_divisibility.assume(ctx.eq(x % 16, 3))
    no_divisibility.assume(divisor > 0)
    assert ctx.equivalent((x + 1) % divisor, x % divisor + 1, no_divisibility) is None
    noninteger = ctx.facts()
    noninteger.assume(ctx.eq(divisor % 16, 0))
    noninteger.assume(divisor > 0)
    half = x / 2
    assert ctx.equivalent((half + 1) % divisor, half % divisor + 1, noninteger) is None

    with pytest.raises(ValueError, match="not a predicate tree"):
        ctx.check_predicate(x & 7, empty)
    with pytest.raises(ValueError, match="not a predicate tree"):
        ctx.check_predicate(ixsimpl.or_(x, y), empty)


def test_ordered_equivalence_uses_full_tree_congruence() -> None:
    ctx = ixsimpl.Context()
    base = ctx.sym("python_ordered_base")
    limit = ctx.sym("python_ordered_limit")
    toggle = ctx.sym("python_ordered_toggle")
    residual = base + 4 * toggle - limit
    facts = ctx.facts()
    facts.assume_many([ctx.eq(base % 16, 0), ctx.eq(limit % 16, 0), toggle >= 0, toggle <= 1])

    assert ctx.equivalent(residual < 0, residual + 8 < 0, facts) is True
    assert ctx.equivalent(residual >= 0, residual + 8 >= 0, facts) is True
    assert ctx.equivalent(residual + 4 <= 0, residual + 12 <= 0, facts) is True
    assert ctx.equivalent(residual + 4 > 0, residual + 12 > 0, facts) is True
    assert ctx.equivalent(residual < 0, residual + 16 < 0, facts) is None

    coarse = ctx.facts()
    coarse.assume_many([ctx.eq(base % 8, 0), ctx.eq(limit % 8, 0), toggle >= 0, toggle <= 1])
    assert ctx.equivalent(residual < 0, residual + 8 < 0, coarse) is None

    wide_toggle = ctx.facts()
    wide_toggle.assume_many([ctx.eq(base % 16, 0), ctx.eq(limit % 16, 0), toggle >= 0, toggle <= 2])
    assert ctx.equivalent(residual < 0, residual + 8 < 0, wide_toggle) is None


def test_wrapped_xor_ordered_equivalence_and_mod_residue_split() -> None:
    ctx = ixsimpl.Context()
    lane = ctx.sym("python_ordered_lane")
    tile = ctx.sym("python_ordered_tile")
    limit = ctx.sym("python_ordered_wrap_limit")
    modulus = 1 << 32
    aligned_dividend = (1 << 31) + 64 + 128 * lane + 256 * tile
    aligned_mod = aligned_dividend % modulus

    for offset in (1, 2, 3):
        shifted_mod = (aligned_dividend + offset) % modulus
        assert ixsimpl.same_node(shifted_mod, aligned_mod + offset)

    facts = ctx.facts()
    facts.assume_many([lane >= 0, lane <= 31, ctx.eq(limit % 4, 0)])

    def predicate(offset: int) -> ixsimpl.Expr:
        lane_bits = ixsimpl.xor_(ctx.int_(64 + offset), 128 * lane)
        wrapped = ((1 << 31) + 256 * tile + lane_bits) % modulus - (1 << 31)
        return wrapped - limit < 0

    assert ctx.equivalent(predicate(0), predicate(1), facts) is True
    assert ctx.equivalent(predicate(0), predicate(2), facts) is True
    assert ctx.equivalent(predicate(0), predicate(3), facts) is True
    assert ctx.equivalent(predicate(0), predicate(4), facts) is None

    no_lane_range = ctx.facts()
    no_lane_range.assume(ctx.eq(limit % 4, 0))
    assert ctx.equivalent(predicate(0), predicate(1), no_lane_range) is None

    no_limit_grid = ctx.facts()
    no_limit_grid.assume_many([lane >= 0, lane <= 31])
    assert ctx.equivalent(predicate(0), predicate(1), no_limit_grid) is None


@given(
    modulus=st.integers(min_value=2, max_value=32),
    residue_seed=st.integers(min_value=0, max_value=255),
    threshold=st.integers(min_value=-128, max_value=128),
    width=st.integers(min_value=1, max_value=32),
    shift_seed=st.integers(min_value=-64, max_value=64),
)
def test_total_equivalence_discrete_cut_and_mod_shift_property(
    modulus: int,
    residue_seed: int,
    threshold: int,
    width: int,
    shift_seed: int,
) -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("equiv_property_x")
    divisor = ctx.sym("equiv_property_divisor")
    residue = residue_seed % modulus
    shift = shift_seed % (2 * modulus + 1) - modulus
    aligned = ctx.facts()
    aligned.assume(ctx.eq(x % modulus, residue))

    reachable = any(
        (value - residue) % modulus == 0 for value in range(threshold, threshold + width)
    )
    upper = ctx.equivalent(x < threshold, x < threshold + width, aligned)
    lower = ctx.equivalent(x >= threshold + width, x >= threshold, aligned)
    expected = None if reachable else True
    assert upper is expected
    assert lower is expected

    mod_facts = ctx.facts()
    mod_facts.assume(ctx.eq(x % modulus, residue))
    mod_facts.assume(ctx.eq(divisor % modulus, 0))
    mod_facts.assume(divisor > 0)
    result = ctx.equivalent((x + shift) % divisor, x % divisor + shift, mod_facts)
    assert result is (True if 0 <= residue + shift < modulus else None)


def test_truncating_remainder_equivalence_projection() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    d = ctx.sym("d")
    scaled_zero = ctx.parse_expr(
        "16*x - 16*d*Piecewise((floor(x/d), "
        "(x >= 0 & d > 0) | (x <= 0 & d < 0)), "
        "(ceiling(x/d), True))"
    )
    scaled_next = ctx.parse_expr(
        "16 + 16*x - 16*d*Piecewise((floor((1 + x)/d), "
        "((1 + x) >= 0 & d > 0) | ((1 + x) <= 0 & d < 0)), "
        "(ceiling((1 + x)/d), True))"
    )
    wave_negative_zero = ctx.parse_expr(
        "16*x - 16*d*Piecewise((floor(x/d), x <= 0 & d < 0), " "(ceiling(x/d), True))"
    )
    wave_negative_next = ctx.parse_expr(
        "16 + 16*x - 16*d*Piecewise((floor((1 + x)/d), "
        "(1 + x) <= 0 & d < 0), (ceiling((1 + x)/d), True))"
    )
    floor_quotient = ctx.parse_expr("floor(x/d)")
    ceiling_quotient = ctx.parse_expr("ceiling(x/d)")
    positive_remainder_quotient = ctx.parse_expr("(x - Mod(x, 4))/d")
    negative_remainder_quotient = ctx.parse_expr("(x + Mod(-x, 4))/d")

    positive = ctx.facts()
    positive.assume_many([x >= 0, x <= 2**30 - 2, ctx.eq(d, 4), ctx.eq(x % 2, 0)])
    assert ctx.equivalent(scaled_next, scaled_zero + 16, positive) is True
    assert ctx.constant_difference(scaled_next, scaled_zero, positive) == 16
    assert ctx.equivalent(floor_quotient, positive_remainder_quotient, positive) is True
    assert ctx.equivalent(ceiling_quotient, positive_remainder_quotient, positive) is not True

    dynamic_positive = ctx.facts()
    dynamic_positive.assume_many(
        [
            x >= 0,
            x <= 2**30 - 2,
            ctx.eq(x % 2, 0),
            d >= 4,
            d <= 2**30,
            ctx.eq(d % 4, 0),
        ]
    )
    assert ctx.equivalent(scaled_next, scaled_zero + 16, dynamic_positive) is True
    assert ctx.constant_difference(scaled_next, scaled_zero, dynamic_positive) == 16

    negative_divisor = ctx.facts()
    negative_divisor.assume_many([x >= 0, x <= 2**30 - 2, ctx.eq(d, -4), ctx.eq(x % 2, 0)])
    assert ctx.equivalent(wave_negative_next, wave_negative_zero + 16, negative_divisor) is True
    assert ctx.constant_difference(wave_negative_next, wave_negative_zero, negative_divisor) == 16
    assert ctx.equivalent(ceiling_quotient, positive_remainder_quotient, negative_divisor) is True
    assert ctx.equivalent(floor_quotient, positive_remainder_quotient, negative_divisor) is not True

    at_zero = ctx.facts()
    at_zero.assume_many([ctx.eq(x, 0), ctx.eq(d, -4)])
    assert ctx.equivalent(wave_negative_next, wave_negative_zero + 16, at_zero) is True

    for divisor in (4, -4):
        negative = ctx.facts()
        negative.assume_many([x >= -100, x <= -2, ctx.eq(d, divisor), ctx.eq(x % 4, 2)])
        assert ctx.equivalent(scaled_next, scaled_zero + 16, negative) is True
        rounded = ceiling_quotient if divisor > 0 else floor_quotient
        wrong_round = floor_quotient if divisor > 0 else ceiling_quotient
        assert ctx.equivalent(rounded, negative_remainder_quotient, negative) is True
        assert ctx.equivalent(wrong_round, negative_remainder_quotient, negative) is not True

    positive_wrap = ctx.facts()
    positive_wrap.assume_many([ctx.eq(x, 3), ctx.eq(d, 4)])
    assert ctx.equivalent(scaled_next, scaled_zero + 16, positive_wrap) is not True
    negative_wrap = ctx.facts()
    negative_wrap.assume_many([ctx.eq(x, -4), ctx.eq(d, -4)])
    assert ctx.equivalent(scaled_next, scaled_zero + 16, negative_wrap) is not True


def test_truncating_remainder_projection_rejects_partial_semantics() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    d = ctx.sym("d")

    def pair(condition: str, fallback: str = "True") -> tuple[ixsimpl.Expr, ixsimpl.Expr]:
        zero = ctx.parse_expr(
            f"16*x - 16*d*Piecewise((floor(x/d), {condition}), " f"(ceiling(x/d), {fallback}))"
        )
        next_condition = condition.replace("x", "(1 + x)")
        next_fallback = fallback.replace("x", "(1 + x)")
        next_ = ctx.parse_expr(
            "16 + 16*x - 16*d*Piecewise((floor((1 + x)/d), "
            f"{next_condition}), (ceiling((1 + x)/d), {next_fallback}))"
        )
        return zero, next_

    facts = ctx.facts()
    facts.assume_many([x >= 0, x <= 100, ctx.eq(d, -4), ctx.eq(x % 2, 0)])

    wrong_zero, wrong_next = pair("x < 0 & d < 0")
    assert ctx.equivalent(wrong_next, wrong_zero + 16, facts) is None
    overlap_zero, overlap_next = pair("(x <= 0 & d < 0) | x == 1")
    assert ctx.equivalent(overlap_next, overlap_zero + 16, facts) is None
    uncovered_zero, uncovered_next = pair("x <= 0 & d < 0", "x >= 0")
    assert ctx.equivalent(uncovered_next, uncovered_zero + 16, facts) is None

    zero_divisor = ctx.facts()
    zero_divisor.assume_many([x >= 0, ctx.eq(d, 0)])
    assert ctx.equivalent(wrong_next, wrong_zero + 16, zero_divisor) is None
    assert ctx.constant_difference(wrong_next, wrong_zero, zero_divisor) is None

    unknown_divisor = ctx.facts()
    unknown_divisor.assume_many([x >= 0, ctx.ne(d, 0), ctx.eq(x % 2, 0)])
    exact_zero, exact_next = pair("(x >= 0 & d > 0) | (x <= 0 & d < 0)")
    assert ctx.equivalent(exact_next, exact_zero + 16, unknown_divisor) is None

    nonintegral_zero = ctx.parse_expr(
        "16*Max(x/2, 0) - 16*d*Piecewise((floor(Max(x/2, 0)/d), "
        "(Max(x/2, 0) >= 0 & d > 0) | (Max(x/2, 0) <= 0 & d < 0)), "
        "(ceiling(Max(x/2, 0)/d), True))"
    )
    nonintegral_next = ctx.parse_expr(
        "16 + 16*Max(x/2, 0) - 16*d*Piecewise("
        "(floor((1 + Max(x/2, 0))/d), "
        "((1 + Max(x/2, 0)) >= 0 & d > 0) | "
        "((1 + Max(x/2, 0)) <= 0 & d < 0)), "
        "(ceiling((1 + Max(x/2, 0))/d), True))"
    )
    nonintegral = ctx.facts()
    nonintegral.assume_many([x >= 0, x <= 100, ctx.eq(d, -4)])
    assert ctx.equivalent(nonintegral_next, nonintegral_zero + 16, nonintegral) is None


def test_equivalence_binding_invalid_inputs() -> None:
    ctx = ixsimpl.Context()
    other = ixsimpl.Context()
    x = ctx.sym("binding_equiv_invalid_x")
    facts = ctx.facts()
    sentinel = ctx.parse_expr("(")

    with pytest.raises(ValueError, match="different context"):
        ctx.equivalent(x, other.sym("x"), facts)
    with pytest.raises(ValueError, match="different context"):
        ctx.equivalent(x, x, other.facts())
    with pytest.raises(ValueError, match="sentinel"):
        ctx.equivalent(sentinel, sentinel, facts)
    with pytest.raises(ValueError, match="sentinel"):
        ctx.check_predicate(sentinel, facts)


def test_modular_projection_proves_wave_wrapping_xor_packet() -> None:
    ctx = ixsimpl.Context()
    tile, lane, limit = (
        ctx.sym(name)
        for name in (
            "modular_projection_tile",
            "modular_projection_lane",
            "modular_projection_limit",
        )
    )
    bias = 2**31
    modulus = 2**32
    inner = (bias + 256 * tile) % modulus
    value0 = (inner + ixsimpl.xor_(ctx.int_(64), 128 * lane)) % modulus - bias
    value1 = (inner + ixsimpl.xor_(ctx.int_(65), 128 * lane)) % modulus - bias
    facts = ctx.facts()
    facts.assume_range(tile, -(2**31), 2**31 - 1)
    facts.assume_range(lane, 0, 31)
    facts.assume_range(limit, -(2**31), 2**31 - 1)
    facts.assume(ctx.eq(limit % 4, 0))

    assert ctx.constant_difference(value1, value0, facts) == 1
    assert ctx.equivalent(value0 - limit < 0, value1 - limit < 0, facts) is True


def test_modular_projection_requires_one_representable_delta() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("modular_projection_boundary_x")
    wrapped0 = (x + 8) % 16 - 8
    wrapped1 = (x + 9) % 16 - 8
    wrapped2 = (x + 10) % 16 - 8

    negative = ctx.facts()
    negative.assume(ctx.eq(x % 4, 0))
    assert ctx.constant_difference(wrapped1, wrapped0, negative) == 1
    assert ctx.constant_difference(16 * wrapped1, 16 * wrapped0, negative) == 16
    assert ctx.constant_difference((2**63 - 1) * wrapped2, (2**63 - 1) * wrapped0, negative) is None
    assert (
        ctx.constant_difference(wrapped1 + 8 + (-(2**63)), wrapped0 + 8, negative) == -(2**63) + 1
    )

    ambiguous = ctx.facts()
    assert ctx.constant_difference(wrapped1, wrapped0, ambiguous) is None
    assert ctx.equivalent(wrapped0 < 0, wrapped1 < 0, ambiguous) is None

    boundary = ctx.facts()
    boundary.assume_range(x, 7, 8)
    assert ctx.constant_difference(wrapped1, wrapped0, boundary) is None

    partial = ctx.facts()
    partial.assume_range(wrapped0 + 8, 8, 15)
    assert ctx.constant_difference(wrapped1, wrapped0, partial) is None


def test_modular_projection_proves_dynamic_unsigned_remainder_packet() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("dynamic_modular_projection_x")
    d = ctx.sym("dynamic_modular_projection_d")
    bias = 2**31
    modulus = 2**32

    def value(offset: int) -> ixsimpl.Expr:
        remainder = ((x + offset) % modulus) % (d % modulus)
        return (bias + remainder) % modulus - bias

    pair = ctx.facts()
    pair.assume_range(x, 0, 1073741822)
    pair.assume_range(d, 4, 1073741824)
    pair.assume(ctx.eq(x % 2, 0))
    pair.assume(ctx.eq(d % 4, 0))
    assert ctx.constant_difference(value(1), value(0), pair) == 1
    assert ctx.equivalent(value(1), value(0) + 1, pair) is True

    vector = ctx.facts()
    vector.assume_range(x, 0, 1073741816)
    vector.assume_range(d, 16, 1073741824)
    vector.assume(ctx.eq(x % 8, 0))
    vector.assume(ctx.eq(d % 16, 0))
    for offset in range(1, 8):
        assert ctx.constant_difference(value(offset), value(0), vector) == offset
        assert ctx.equivalent(value(offset), value(0) + offset, vector) is True
        assert ctx.constant_difference(value(0), value(offset), vector) == -offset
        assert ctx.equivalent(value(0), value(offset) - offset, vector) is True
    assert ctx.constant_difference(value(8), value(0), vector) is None
    assert ctx.constant_difference(value(0), value(8), vector) is None
    assert ctx.equivalent(value(8), value(0) + 8, vector) is None
    assert ctx.equivalent(value(0), value(8) - 8, vector) is None

    direct0 = x % d
    direct1 = (x + 1) % d
    zero_denominator = ctx.facts()
    zero_denominator.assume_range(x, 0, 1073741822)
    zero_denominator.assume_range(d, 0, 0)
    assert ctx.constant_difference(direct1, direct0, zero_denominator) is None
    assert ctx.equivalent(direct1, direct0 + 1, zero_denominator) is None

    negative_denominator = ctx.facts()
    negative_denominator.assume_range(x, 0, 1073741822)
    negative_denominator.assume_range(d, -16, -4)
    assert ctx.constant_difference(direct1, direct0, negative_denominator) is None
    assert ctx.equivalent(direct1, direct0 + 1, negative_denominator) is None


def test_fact_backed_algebra_helpers() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("algebra_binding_x")
    i = ctx.sym("algebra_binding_i")
    base = ctx.sym("algebra_binding_base")
    facts = ctx.facts()

    assert ctx.constant_difference(4 * x + 4, 4 * x + 1, facts) == 3
    assert ctx.constant_difference(4 * (x + 1), 4 * x + 1, facts) == 3
    assert ctx.constant_difference(ctx.int_(2**63 - 1), ctx.int_(-1), facts) is None

    affine = ctx.affine_decompose(8 * i + base, i, facts)
    assert affine is not None
    coefficient, residual = affine
    assert ixsimpl.same_node(coefficient, ctx.int_(8))
    assert ixsimpl.same_node(residual, base)

    factored = ctx.affine_decompose(8 * (i + base), i, facts)
    assert factored is not None
    coefficient, residual = factored
    assert ixsimpl.same_node(coefficient, ctx.int_(8))
    assert ixsimpl.same_node(residual, 8 * base)

    rational = ctx.affine_decompose(i / 2, i, facts)
    assert rational is not None
    coefficient, residual = rational
    assert ixsimpl.same_node(coefficient, ctx.rat(1, 2))
    assert ixsimpl.same_node(residual, ctx.int_(0))
    assert ctx.affine_decompose(i * i, i, facts) is None
    assert ctx.affine_decompose(base * i, i, facts) is None
    assert ctx.affine_decompose(i % 8, i, facts) is None

    linear_difference = ctx.finite_difference(8 * i + base, i, ctx.int_(1), facts)
    assert linear_difference is not None
    assert ixsimpl.same_node(linear_difference, ctx.int_(8))
    quadratic_difference = ctx.finite_difference(i * i, i, ctx.int_(1), facts)
    assert quadratic_difference is not None
    assert ixsimpl.same_node(quadratic_difference, 2 * i + 1)
    assert ctx.finite_difference(i, i, i, facts) is None
    with pytest.raises(ValueError, match="invalid internal relation state"):
        ctx.finite_difference(i + 1, i, ctx.int_(2**63 - 1), facts)

    split = ctx.split_additive_constant(base + 96, facts)
    assert split is not None
    residual, constant = split
    assert ixsimpl.same_node(residual, base)
    assert constant == 96
    for limit in (-(2**63), 2**63 - 1):
        split = ctx.split_additive_constant(base + limit, facts)
        assert split is not None
        residual, constant = split
        assert ixsimpl.same_node(residual, base)
        assert constant == limit
    assert ctx.split_additive_constant(base + ctx.rat(1, 2), facts) is None


def test_fact_backed_algebra_helpers_use_domain_facts() -> None:
    ctx = ixsimpl.Context()
    i = ctx.sym("algebra_domain_i")
    base = ctx.sym("algebra_domain_base")
    empty = ctx.facts()
    condition = i >= 0
    piecewise = ixsimpl.pw((8 * i + base, condition), (base, ctx.true_()))

    assert ctx.affine_decompose(piecewise, i, empty) is None
    nonnegative = ctx.facts()
    nonnegative.assume(condition)
    affine = ctx.affine_decompose(piecewise, i, nonnegative)
    assert affine is not None
    coefficient, residual = affine
    assert ixsimpl.same_node(coefficient, ctx.int_(8))
    assert ixsimpl.same_node(residual, base)

    reciprocal = 1 / i
    assert ctx.constant_difference(reciprocal, reciprocal, empty) is None
    nonzero = ctx.facts()
    nonzero.assume(ctx.ne(i, 0))
    assert ctx.constant_difference(reciprocal, reciprocal, nonzero) == 0

    contradictory = ctx.facts()
    contradictory.assume(i >= 10)
    contradictory.assume(i <= 5)
    assert ctx.constant_difference(i, i, contradictory) is None
    assert ctx.affine_decompose(i, i, contradictory) is None


def test_fact_backed_algebra_helper_binding_failures() -> None:
    ctx = ixsimpl.Context()
    other = ixsimpl.Context()
    x = ctx.sym("algebra_invalid_x")
    facts = ctx.facts()
    sentinel = ctx.parse_expr("(")

    with pytest.raises(ValueError, match="different context"):
        ctx.constant_difference(x, other.sym("x"), facts)
    with pytest.raises(ValueError, match="different context"):
        ctx.affine_decompose(x, other.sym("x"), facts)
    with pytest.raises(ValueError, match="different context"):
        ctx.finite_difference(x, x, other.sym("step"), facts)
    with pytest.raises(ValueError, match="different context"):
        ctx.split_additive_constant(other.sym("x"), facts)
    with pytest.raises(ValueError, match="must be a symbol"):
        ctx.affine_decompose(x, x + 1, facts)
    with pytest.raises(ValueError, match="sentinel"):
        ctx.constant_difference(sentinel, x, facts)
    with pytest.raises(ValueError, match="sentinel"):
        ctx.affine_decompose(sentinel, x, facts)
    with pytest.raises(ValueError, match="sentinel"):
        ctx.finite_difference(sentinel, x, ctx.int_(1), facts)
    with pytest.raises(ValueError, match="sentinel"):
        ctx.split_additive_constant(sentinel, facts)


@given(
    a=st.integers(min_value=-64, max_value=64),
    b=st.integers(min_value=-64, max_value=64),
    c=st.integers(min_value=-64, max_value=64),
    d=st.integers(min_value=-64, max_value=64),
    step=st.integers(min_value=-8, max_value=8),
)
def test_fact_backed_algebra_helper_affine_property(
    a: int, b: int, c: int, d: int, step: int
) -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("algebra_property_x")
    y = ctx.sym("algebra_property_y")
    facts = ctx.facts()
    expr = a * x + b * y + c

    assert ctx.constant_difference(expr, a * x + b * y + d, facts) == c - d
    affine = ctx.affine_decompose(expr, x, facts)
    assert affine is not None
    coefficient, residual = affine
    assert ixsimpl.same_node(coefficient, ctx.int_(a))
    assert ixsimpl.same_node(residual, b * y + c)
    difference = ctx.finite_difference(expr, x, ctx.int_(step), facts)
    assert difference is not None
    assert ixsimpl.same_node(difference, ctx.int_(a * step))
    split = ctx.split_additive_constant(expr, facts)
    assert split is not None
    residual, constant = split
    assert ixsimpl.same_node(residual, a * x + b * y)
    assert constant == c


def test_definedness_queries_assumptions_facts_and_piecewise() -> None:
    ctx = ixsimpl.Context()
    x, m = ctx.sym("defined_x"), ctx.sym("defined_m")
    reciprocal = 1 / x

    assert ctx.defined(reciprocal) is None
    assert ctx.defined(reciprocal, assumptions=[x > 0]) is True
    assert ctx.defined(reciprocal, assumptions=[x < 0]) is True
    assert ctx.defined(reciprocal, assumptions=[ctx.ne(x, 0)]) is True
    assert ctx.defined(reciprocal, assumptions=[ctx.eq(x, 0)]) is False
    assert ctx.defined(reciprocal, assumptions=[x >= -1, x <= 1]) is None

    symbolic_mod = x % m
    assert ctx.defined(symbolic_mod) is None
    assert ctx.defined(symbolic_mod, assumptions=[m > 0]) is True
    assert ctx.defined(symbolic_mod, assumptions=[m < 0]) is False
    assert ctx.defined(symbolic_mod, assumptions=[ctx.eq(m, 0)]) is False
    assert ctx.defined(symbolic_mod, assumptions=[ctx.ne(m, 0)]) is None

    branch_local = ixsimpl.pw((reciprocal, x > 0), (reciprocal + 1, x < 0), (1, ctx.true_()))
    assert ctx.defined(branch_local) is True
    nonzero_branch = ixsimpl.pw((reciprocal, ctx.ne(x, 0)), (1, ctx.true_()))
    assert ctx.defined(nonzero_branch) is True

    no_default = ixsimpl.pw((1, x < 16))
    assert ctx.defined(no_default, assumptions=[x < 16]) is True
    assert ctx.defined(no_default) is None
    assert ctx.defined(no_default, assumptions=[x >= 16]) is False

    undefined_condition = ixsimpl.pw((1, reciprocal > 0), (0, ctx.true_()))
    assert ctx.defined(undefined_condition, assumptions=[ctx.eq(x, 0)]) is False
    assert ctx.defined(undefined_condition, assumptions=[x > 0]) is True

    facts = ctx.facts()
    facts.assume(x > 0)
    assert ctx.defined(reciprocal, facts=facts) is True


def test_definedness_expression_facts_do_not_close_domain() -> None:
    ctx = ixsimpl.Context()
    x, d = ctx.sym("defined_range_x"), ctx.sym("defined_range_d")
    floored = ixsimpl.floor(x / d)
    equality = ctx.eq(floored, 0)
    divisor_nonzero = ctx.ne(d, 0)

    range_only = ctx.facts()
    range_only.assume_range(floored, 0, 7)
    assert ctx.defined(floored, facts=range_only) is None

    range_closed = ctx.facts()
    range_closed.assume_range(floored, 0, 7)
    range_closed.assume(divisor_nonzero)
    assert ctx.defined(floored, facts=range_closed) is True

    equality_only = ctx.facts()
    equality_only.assume(equality)
    assert ctx.defined(floored, facts=equality_only) is None

    equality_closed = ctx.facts()
    equality_closed.assume(equality)
    equality_closed.assume(divisor_nonzero)
    assert ctx.defined(floored, facts=equality_closed) is True

    assert ctx.defined(floored, assumptions=[equality]) is None
    assert ctx.defined(floored, assumptions=[equality, divisor_nonzero]) is True


def test_definedness_invalid_inputs() -> None:
    ctx = ixsimpl.Context()
    other = ixsimpl.Context()
    sentinel = ctx.parse_expr("(")

    assert ctx.defined(sentinel) is None
    with pytest.raises(ValueError, match="different context"):
        ctx.defined(other.sym("x"))
    with pytest.raises(ValueError, match="different context"):
        ctx.defined(ctx.sym("x"), facts=other.facts())


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


def test_fact_backed_exact_divide_piecewise() -> None:
    ctx = ixsimpl.Context()
    item, slot = ctx.sym("exact_pw_item"), ctx.sym("exact_pw_slot")
    k = ctx.sym("exact_pw_k")
    value = 32 * (2 * item + slot)
    piecewise = ixsimpl.pw((value, item < 64))
    expected = 8 * item + 4 * slot

    active = ctx.facts()
    active.assume_many([item >= 0, item <= 63])
    status, quotient = ctx.try_exact_divide(piecewise, 8, active)
    assert status == "proven"
    assert quotient is not None
    assert ixsimpl.same_node(quotient, expected)

    assert ctx.try_exact_divide(piecewise, 8, ctx.facts()) == ("unknown", None)

    inactive = ctx.facts()
    inactive.assume(item >= 64)
    assert ctx.try_exact_divide(piecewise, 8, inactive) == ("unknown", None)

    fact_integer = ixsimpl.pw((k / 2, item > 0))
    product = 16 * fact_integer
    partial = ctx.facts()
    partial.assume(ctx.eq(k % 2, 0))
    assert ctx.integer_valued(fact_integer, facts=partial) is True
    assert ctx.defined(fact_integer, facts=partial) is None
    assert ctx.try_exact_divide(product, 8, partial) == ("unknown", None)

    covered = ctx.facts()
    covered.assume_many([ctx.eq(k % 2, 0), item > 0])
    status, quotient = ctx.try_exact_divide(product, 8, covered)
    assert status == "proven"
    assert quotient is not None
    assert ixsimpl.same_node(quotient, k)


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
    elif pattern == "add":
        assumptions.append(ctx.eq(b % mod_b, 0))
        expr = coeff_a * a + coeff_b * b + const
    else:
        assumptions.extend([a >= mod_a, b >= 1])
        expr = query_mod / ixsimpl.max_(b, a / mod_a)

    lhs = expr % query_mod
    query = ctx.eq(lhs, target) if cmp_op == "==" else ctx.ne(lhs, target)
    result = ctx.check(query, assumptions=assumptions)
    if pattern == "reciprocal":
        assert result is None, f"unexpected proof for case={case}"
        return
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


def test_carry_free_add_nested_xor_queries() -> None:
    ctx = ixsimpl.Context()
    b, c, d = ctx.sym("b"), ctx.sym("c"), ctx.sym("d")
    base, limit = ctx.sym("base"), ctx.sym("limit")
    facts = ctx.facts()
    for bit in (b, c, d):
        facts.assume(bit >= 0)
        facts.assume(bit <= 1)

    inner0 = ixsimpl.xor_(32 + 4 * b, 8 * c)
    inner1 = ixsimpl.xor_(33 + 4 * b, 8 * c)
    nested0 = ixsimpl.xor_(16 * d, inner0)
    nested1 = ixsimpl.xor_(16 * d, inner1)
    expected0 = 32 + 4 * b + 8 * c + 16 * d

    assert ctx.equivalent(inner0, 32 + 4 * b + 8 * c, facts) is True
    assert ctx.equivalent(nested0, expected0, facts) is True
    assert ctx.equivalent(nested0 + 1, nested1, facts) is True

    active0 = ixsimpl.and_(base >= 0, 16 * base + nested0 < 16 * limit)
    active1 = ixsimpl.and_(base >= 0, 16 * base + nested1 < 16 * limit)
    assert ctx.equivalent(active0, active1, facts) is True

    overlap = ixsimpl.xor_(32 + 4 * b, 4 * c)
    carry = ixsimpl.xor_(4 + 4 * b, 8)
    negative = ixsimpl.xor_(32 - 4 * b, 8 * c)
    assert "xor" in str(overlap.simplify(facts=facts))
    assert "xor" in str(carry.simplify(facts=facts))
    assert "xor" in str(negative.simplify(facts=facts))
    assert ctx.equivalent(overlap, 32 + 4 * b + 4 * c, facts) is None
    assert ctx.equivalent(carry, 12 + 4 * b, facts) is None


@given(
    positions=st.lists(
        st.integers(min_value=0, max_value=30),
        min_size=4,
        max_size=4,
        unique=True,
    )
)
def test_carry_free_add_known_bits_property(positions: list[int]) -> None:
    ctx = ixsimpl.Context()
    x, y, z = ctx.sym("x"), ctx.sym("y"), ctx.sym("z")
    facts = ctx.facts()
    for bit in (x, y, z):
        facts.assume(bit >= 0)
        facts.assume(bit <= 1)

    constant_bit, x_bit, y_bit, z_bit = (1 << position for position in positions)
    lhs = constant_bit + x_bit * x + y_bit * y
    expr = ixsimpl.xor_(lhs, z_bit * z)
    expected = lhs + z_bit * z
    known_zero, known_one, _ = ctx.known_bits(lhs, facts) or (0, 0, None)
    possible = (~known_zero) & ((1 << 64) - 1)

    assert possible == constant_bit | x_bit | y_bit
    assert known_one == constant_bit
    assert ctx.equivalent(expr, expected, facts) is True
    for xv in (0, 1):
        for yv in (0, 1):
            for zv in (0, 1):
                env = {"x": xv, "y": yv, "z": zv}
                assert expr.eval(env) == expected.eval(env)


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
    bounded_integer = ctx.facts()
    bounded_integer.assume_range(x, Fraction(1, 2), Fraction(19, 2))
    assert ctx.range(x, facts=bounded_integer) == (1, 9)
    empty_integer = ctx.facts()
    empty_integer.assume_range(x, Fraction(1, 4), Fraction(3, 4))
    assert ctx.range(x, facts=empty_integer) is None
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


def test_facts_simultaneous_substitution_and_inverse_facts() -> None:
    ctx = ixsimpl.Context()
    x, y, z = (ctx.sym(name) for name in ("multi_x", "multi_y", "multi_z"))
    ranged = ctx.facts()
    ranged.assume_range(x, 0, 15)
    ranged.assume_range(y, 20, 30)

    simultaneous = ranged.subs({x: y, y: z})
    assert ctx.range(y, facts=simultaneous) == (0, 15)
    assert ctx.range(z, facts=simultaneous) == (20, 30)
    assert ctx.range(x, facts=simultaneous) is None
    unchanged = ranged.subs({})
    assert ctx.range(x, facts=unchanged) == (0, 15)
    assert ctx.range(y, facts=unchanged) == (20, 30)

    k = ctx.sym("multi_k")
    modular = ctx.facts()
    modular.assume(
        ixsimpl.and_(
            ctx.eq(y % 8, 0),
            ixsimpl.and_(ctx.eq(y & (y - 1), 0), y > 0),
        )
    )
    transferred = modular.subs({y: 2 * k, k: z})
    assert ctx.congruent(k, 4, 0, transferred) is True
    assert ctx.congruent(k, 8, 0, transferred) is None
    assert ctx.congruent(z, 4, 0, transferred) is None
    known_zero, known_one, _ = ctx.known_bits(k, transferred) or (0, 0, None)
    assert known_zero & 3 == 3
    assert known_one & 3 == 0
    assert ctx.pow2_fact(k, facts=transferred) == "positive"

    nonlinear = modular.subs(y, k * z)
    assert ctx.congruent(k, 4, 0, nonlinear) is None
    assert ctx.pow2_fact(k, facts=nonlinear) is None


def test_facts_assume_decomposes_conjunction() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    facts = ctx.facts()

    facts.assume(ixsimpl.and_(x >= 0, x <= 10))
    assert ctx.range(x, facts=facts) == (0, 10)

    with pytest.raises(ValueError):
        facts.assume(ixsimpl.or_(x >= 0, x <= 10))


def test_facts_assume_many_is_atomic() -> None:
    ctx = ixsimpl.Context()
    x, y = ctx.sym("batch_x"), ctx.sym("batch_y")
    facts = ctx.facts()

    facts.assume_many([x >= 0, x <= 10])
    facts.assume_many([])
    assert ctx.range(x, facts=facts) == (0, 10)

    wrong_type = ctx.facts()
    wrong_type.assume(x >= 0)
    invalid_predicate: Any = 1
    with pytest.raises(TypeError):
        wrong_type.assume_many([y >= 5, invalid_predicate])
    assert ctx.range(x, facts=wrong_type) == (0, None)

    other = ixsimpl.Context()
    foreign = other.sym("batch_x")
    wrong_context = ctx.facts()
    wrong_context.assume(x >= 0)
    with pytest.raises(ValueError, match="different context"):
        wrong_context.assume_many([x <= 10, foreign >= 0])
    assert ctx.range(x, facts=wrong_context) == (0, None)

    rejected = ctx.facts()
    rejected.assume(x >= 0)
    with pytest.raises(ValueError, match="OR predicates"):
        rejected.assume_many([y >= 5, ixsimpl.or_(x >= 0, x <= 10)])
    assert ctx.range(x, facts=rejected) is None


def test_facts_assume_many_uses_prefix_closure() -> None:
    ctx = ixsimpl.Context()
    x, y = ctx.sym("batch_closure_x"), ctx.sym("batch_closure_y")
    facts = ctx.facts()

    facts.assume_many([ctx.eq(x, 0), x + y >= 0])
    assert ctx.check(y >= 0, facts=facts) is True


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


def test_fact_check_nested_xor_cancellation_parity() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("xor_check_x")
    one, two = ctx.int_(1), ctx.int_(2)
    pred = ixsimpl.and_(x >= 0, x <= 31)
    nested = ixsimpl.xor_(one, ixsimpl.xor_(one, x))
    query = ctx.eq(nested, x)
    different = ixsimpl.xor_(one, ixsimpl.xor_(two, x))
    nonmatching = ctx.eq(different, x)

    assert nested == x
    assert ctx.check(query, assumptions=[pred]) is True

    facts = ctx.facts()
    facts.assume(pred)
    assert ctx.check(query, facts=facts) is True
    assert ctx.check_predicate(query, facts) is True
    assert ctx.equivalent(nested, x, facts) is True

    assert different != x
    assert ctx.check(nonmatching, assumptions=[pred]) is None
    assert ctx.check(nonmatching, facts=facts) is None


def test_fact_backed_simplification() -> None:
    ctx = ixsimpl.Context()
    x, y = ctx.sym("fact_simplify_x"), ctx.sym("fact_simplify_y")
    assumptions = [x >= 0, x < 8]
    facts = ctx.facts()
    facts.assume(ixsimpl.and_(*assumptions))

    expr = x % 16
    assert expr.simplify(facts=facts) == expr.simplify(assumptions=assumptions)
    assert expr.simplify(facts=facts) == x
    assert expr.simplify(facts=facts) == x
    assert ctx.range(x, facts=facts) == (0, 7)

    batch = [expr, ixsimpl.floor(x / 8)]
    ctx.simplify_batch(batch, facts=facts)
    assert batch == [x, ctx.int_(0)]

    explicit = ctx.facts()
    base = x + y
    bounded = ixsimpl.floor(base / 16)
    explicit.assume_range(bounded.child(0), Fraction(3, 16), Fraction(15, 16))
    assert bounded.simplify(facts=explicit) == ctx.int_(0)

    affine = ctx.facts()
    affine_base = ctx.sym("fact_affine_base")
    derived = 3 * affine_base + 2
    affine.assume_range(affine_base, 4, 7)
    affine.derive_affine(affine_base, 3, 2, derived)
    assert ixsimpl.floor(derived / 24).simplify(facts=affine) == ctx.int_(0)

    source = ctx.facts()
    source_base = ctx.sym("fact_substitute_base")
    replacement = y + 1
    source_expr = ixsimpl.floor(source_base / 8)
    source.assume_range(source_expr.child(0), 0, Fraction(7, 8))
    substituted = source.subs(source_base, replacement)
    assert ixsimpl.floor(replacement / 8).simplify(facts=substituted) == ctx.int_(0)

    contradictory = ctx.facts()
    contradictory.assume(x >= 10)
    contradictory.assume(x <= 5)
    assert x.simplify(facts=contradictory) == x
    contradictory_floor = ixsimpl.floor(x / 100)
    assert contradictory_floor.simplify(facts=contradictory) == contradictory_floor

    sentinel = ctx.parse_expr("(")
    assert sentinel.simplify(facts=facts).is_parse_error

    other = ixsimpl.Context()
    with pytest.raises(ValueError, match="expression from different context"):
        ctx.simplify_batch([other.sym("x")], facts=facts)
    with pytest.raises(ValueError, match="facts from different context"):
        x.simplify(facts=other.facts())
    with pytest.raises(ValueError, match="either assumptions or facts"):
        x.simplify(assumptions=assumptions, facts=facts)
    with pytest.raises(ValueError, match="either assumptions or facts"):
        ctx.simplify_batch([x], assumptions=assumptions, facts=facts)


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
    assert ctx.range(x, facts=facts) is None
    assert ctx.range(y, facts=facts) is None
    with pytest.raises(ValueError, match="fact set is unusable"):
        mod.simplify(facts=facts)


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

    modulus = abs(scale)
    aligned_lo = lo + (offset - lo) % modulus
    aligned_hi = hi - (hi - offset) % modulus
    expected = None if aligned_lo > aligned_hi else (aligned_lo, aligned_hi)
    assert ctx.range(expanded, facts=facts) == expected
    assert ctx.range(factored, facts=facts) == expected


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
