# SPDX-FileCopyrightText: 2026 ixsimpl contributors
# SPDX-License-Identifier: Apache-2.0
"""Structural converters between ixsimpl Expr trees and SymPy expressions."""

from __future__ import annotations

from collections.abc import Callable
from typing import Any

import sympy

import ixsimpl

_MAX_POW_EXPONENT = 1000

_CMP_TO_SYMPY: dict[int, type[sympy.core.relational.Relational]] = {
    ixsimpl.CMP_GT: sympy.Gt,
    ixsimpl.CMP_GE: sympy.Ge,
    ixsimpl.CMP_LT: sympy.Lt,
    ixsimpl.CMP_LE: sympy.Le,
    ixsimpl.CMP_EQ: sympy.Eq,
    ixsimpl.CMP_NE: sympy.Ne,
}


class bitand(sympy.Function):  # type: ignore[misc]
    @classmethod
    def eval(cls, *args: Any) -> sympy.Integer | None:
        if args and all(isinstance(arg, sympy.Integer) for arg in args):
            result = int(args[0])
            for arg in args[1:]:
                result &= int(arg)
            return sympy.Integer(result)
        return None


class bitor(sympy.Function):  # type: ignore[misc]
    @classmethod
    def eval(cls, *args: Any) -> sympy.Integer | None:
        if args and all(isinstance(arg, sympy.Integer) for arg in args):
            result = int(args[0])
            for arg in args[1:]:
                result |= int(arg)
            return sympy.Integer(result)
        return None


class Trunc(sympy.Function):  # type: ignore[misc]
    """SymPy representation of integer truncation toward zero."""

    nargs = 1

    @classmethod
    def eval(cls, arg: sympy.Basic) -> sympy.Basic | None:
        if isinstance(arg, sympy.Integer):
            return arg
        if arg.is_number is True:
            if arg.is_nonnegative is True:
                return sympy.floor(arg)
            if arg.is_nonpositive is True:
                return sympy.ceiling(arg)
        return None


def to_sympy(
    expr: ixsimpl.Expr,
    *,
    symbols: dict[str, sympy.Symbol] | None = None,
    xor_fn: Callable[..., sympy.Basic] | None = None,
) -> sympy.Basic:
    """Convert an ixsimpl Expr to an equivalent sympy expression.

    Walks the ixsimpl node tree structurally and builds the SymPy
    counterpart.  No simplification is performed on the SymPy side.

    Parameters
    ----------
    symbols:
        Optional mapping from symbol name to a pre-built ``sympy.Symbol``.
        Use this to preserve SymPy assumptions (``integer``, ``nonnegative``,
        etc.) that ixsimpl does not track.  Symbols not in the map fall back
        to ``sympy.Symbol(name, integer=True)``.
    xor_fn:
        Callable used for ``IXS_XOR`` nodes.  Defaults to ``sympy.Xor``
        (boolean XOR).  Pass a custom ``sympy.Function`` subclass for
        integer bitwise XOR instead.
    """

    def _convert(node: ixsimpl.Expr) -> sympy.Basic:
        return to_sympy(node, symbols=symbols, xor_fn=xor_fn)

    def _convert_cond(node: ixsimpl.Expr) -> sympy.Basic:
        if node.tag == ixsimpl.INT:
            return sympy.false if int(node) == 0 else sympy.true
        if node.tag == ixsimpl.RAT:
            return sympy.false if node.rat_num == 0 else sympy.true
        converted = _convert(node)
        if isinstance(
            converted,
            (
                sympy.logic.boolalg.BooleanAtom,
                sympy.logic.boolalg.BooleanFunction,
                sympy.core.relational.Relational,
            ),
        ):
            return converted
        return sympy.Ne(converted, 0)

    def _convert_bitwise_arg(node: ixsimpl.Expr) -> sympy.Basic:
        converted = _convert(node)
        if isinstance(
            converted,
            (
                sympy.logic.boolalg.BooleanAtom,
                sympy.logic.boolalg.BooleanFunction,
                sympy.core.relational.Relational,
            ),
        ):
            return sympy.Piecewise((sympy.Integer(1), converted), (sympy.Integer(0), True))
        return converted

    tag = expr.tag

    if tag == ixsimpl.INT:
        return sympy.Integer(int(expr))

    if tag == ixsimpl.RAT:
        return sympy.Rational(expr.rat_num, expr.rat_den)

    if tag == ixsimpl.SYM:
        name = expr.sym_name
        if symbols and name in symbols:
            return symbols[name]
        return sympy.Symbol(name, integer=True)

    if tag == ixsimpl.ADD:
        result: sympy.Basic = _convert(expr.add_coeff)
        for i in range(expr.add_nterms):
            result = result + _convert(expr.add_term_coeff(i)) * _convert(expr.add_term(i))
        return result

    if tag == ixsimpl.MUL:
        result = _convert(expr.mul_coeff)
        for i in range(expr.mul_nfactors):
            base = _convert(expr.mul_factor_base(i))
            exp = expr.mul_factor_exp(i)
            result = result * base ** sympy.Integer(exp)
        return result

    if tag == ixsimpl.FLOOR:
        # evaluate=False: SymPy incorrectly drops floor() on some
        # Max/Min-containing arguments, e.g. floor(Max(0, 2*x)/6) -> Max(0, 2*x)/6.
        return sympy.floor(_convert(expr.child(0)), evaluate=False)

    if tag == ixsimpl.CEIL:
        # Same SymPy evaluation bug as floor; see above.
        return sympy.ceiling(_convert(expr.child(0)), evaluate=False)

    if tag == ixsimpl.TRUNC:
        return Trunc(_convert(expr.child(0)), evaluate=False)

    if tag == ixsimpl.MOD:
        # evaluate=False: SymPy 1.14 Mod evaluation is buggy on some
        # factored forms, e.g. Mod(x*(2*x+2*y), 6) -> 0.
        return sympy.Mod(_convert(expr.child(0)), _convert(expr.child(1)), evaluate=False)

    if tag == ixsimpl.MAX:
        # evaluate=False: SymPy can wrongly collapse nested integer Max/Min
        # expressions, e.g. Max(-1, Min(0, Max(x, Min(y, Max(1, 2*x))))) -> -1.
        args = [_convert(expr.child(i)) for i in range(expr.nchildren)]
        return sympy.Max(*args, evaluate=False)

    if tag == ixsimpl.MIN:
        args = [_convert(expr.child(i)) for i in range(expr.nchildren)]
        return sympy.Min(*args, evaluate=False)

    if tag == ixsimpl.XOR:
        fn = xor_fn if xor_fn is not None else sympy.Xor
        args = [_convert(expr.child(i)) for i in range(expr.nchildren)]
        return fn(*args)

    if tag == ixsimpl.CMP:
        rel = _CMP_TO_SYMPY.get(expr.cmp_op)
        if rel is None:
            raise ValueError(f"unsupported cmp_op: {expr.cmp_op}")
        return rel(_convert(expr.child(0)), _convert(expr.child(1)))

    if tag == ixsimpl.AND:
        args = [_convert_bitwise_arg(expr.child(i)) for i in range(expr.nchildren)]
        return bitand(*args)

    if tag == ixsimpl.OR:
        args = [_convert_bitwise_arg(expr.child(i)) for i in range(expr.nchildren)]
        return bitor(*args)

    if tag == ixsimpl.NOT:
        child = expr.child(0)
        if child.is_pred:
            return sympy.Not(_convert_cond(child))
        return sympy.Eq(_convert(child), 0)

    if tag == ixsimpl.PIECEWISE:
        pieces: list[tuple[Any, Any]] = []
        for i in range(expr.pw_ncases):
            val = _convert(expr.pw_value(i))
            cond = _convert_cond(expr.pw_cond(i))
            pieces.append((val, cond))
        return sympy.Piecewise(*pieces)

    raise ValueError(f"unsupported ixsimpl tag: {tag}")


def from_sympy(ctx: ixsimpl.Context, expr: sympy.Basic) -> ixsimpl.Expr:
    """Convert a SymPy expression to an ixsimpl Expr.

    Walks the SymPy tree and builds ixsimpl nodes using the Python API.
    Only the integer-arithmetic subset supported by ixsimpl is handled.
    """
    if isinstance(expr, sympy.Integer):
        return ctx.int_(int(expr))

    if isinstance(expr, sympy.Rational):
        return ctx.rat(int(expr.p), int(expr.q))

    if isinstance(expr, sympy.Symbol):
        return ctx.sym(str(expr))

    if isinstance(expr, sympy.Add):
        if not expr.args:
            return ctx.int_(0)
        result: ixsimpl.Expr = from_sympy(ctx, expr.args[0])
        for arg in expr.args[1:]:
            result = result + from_sympy(ctx, arg)
        return result

    if isinstance(expr, sympy.Mul):
        if not expr.args:
            return ctx.int_(1)
        result = from_sympy(ctx, expr.args[0])
        for arg in expr.args[1:]:
            result = result * from_sympy(ctx, arg)
        return result

    if isinstance(expr, sympy.Pow):
        base = from_sympy(ctx, expr.args[0])
        exp = expr.args[1]
        if not isinstance(exp, sympy.Integer):
            raise ValueError(f"non-integer exponent: {exp}")
        e = int(exp)
        if abs(e) > _MAX_POW_EXPONENT:
            raise ValueError(f"exponent too large: {e}")
        if e == 0:
            return ctx.int_(1)
        if e > 0:
            result = base
            for _ in range(e - 1):
                result = result * base
            return result
        pos = base
        for _ in range(-e - 1):
            pos = pos * base
        return ctx.int_(1) / pos

    if isinstance(expr, sympy.floor):
        return ixsimpl.floor(from_sympy(ctx, expr.args[0]))

    if isinstance(expr, sympy.ceiling):
        return ixsimpl.ceil(from_sympy(ctx, expr.args[0]))

    if isinstance(expr, Trunc):
        return ixsimpl.trunc(from_sympy(ctx, expr.args[0]))

    if isinstance(expr, sympy.Mod):
        return ixsimpl.mod(from_sympy(ctx, expr.args[0]), from_sympy(ctx, expr.args[1]))

    if isinstance(expr, sympy.Max):
        args = [from_sympy(ctx, arg) for arg in expr.args]
        return ixsimpl.max_(*args)

    if isinstance(expr, sympy.Min):
        args = [from_sympy(ctx, arg) for arg in expr.args]
        return ixsimpl.min_(*args)

    if isinstance(expr, sympy.Xor):
        args = [from_sympy(ctx, arg) for arg in expr.args]
        return ixsimpl.xor_(*args)

    if isinstance(expr, sympy.Piecewise):
        branches: list[tuple[ixsimpl.Expr, ixsimpl.Expr]] = []
        for val, cond in expr.args:
            branches.append((from_sympy(ctx, val), from_sympy(ctx, cond)))
        return ixsimpl.pw(*branches)

    if isinstance(expr, sympy.Ge):
        return from_sympy(ctx, expr.args[0]) >= from_sympy(ctx, expr.args[1])

    if isinstance(expr, sympy.Gt):
        return from_sympy(ctx, expr.args[0]) > from_sympy(ctx, expr.args[1])

    if isinstance(expr, sympy.Le):
        return from_sympy(ctx, expr.args[0]) <= from_sympy(ctx, expr.args[1])

    if isinstance(expr, sympy.Lt):
        return from_sympy(ctx, expr.args[0]) < from_sympy(ctx, expr.args[1])

    if isinstance(expr, sympy.Eq):
        return ctx.eq(from_sympy(ctx, expr.args[0]), from_sympy(ctx, expr.args[1]))

    if isinstance(expr, sympy.Ne):
        return ctx.ne(from_sympy(ctx, expr.args[0]), from_sympy(ctx, expr.args[1]))

    if isinstance(expr, sympy.And):
        args = [from_sympy(ctx, arg) for arg in expr.args]
        return ixsimpl.and_(*args)

    if isinstance(expr, sympy.Or):
        args = [from_sympy(ctx, arg) for arg in expr.args]
        return ixsimpl.or_(*args)

    if isinstance(expr, sympy.Not):
        return ixsimpl.not_(from_sympy(ctx, expr.args[0]))

    if expr is sympy.true:
        return ctx.true_()

    if expr is sympy.false:
        return ctx.false_()

    # Custom sympy.Function subclasses matched by name.
    if isinstance(expr, sympy.Function):
        name = type(expr).__name__
        if name == "Trunc":
            if len(expr.args) != 1:
                raise ValueError(f"Trunc requires exactly 1 argument, got {len(expr.args)}")
            return ixsimpl.trunc(from_sympy(ctx, expr.args[0]))
        if name == "xor":
            args = [from_sympy(ctx, a) for a in expr.args]
            if len(args) < 2:
                raise ValueError(f"xor requires at least 2 arguments, got {len(args)}")
            return ixsimpl.xor_(*args)
        if name in {"bitand", "bitor"}:
            args = [from_sympy(ctx, a) for a in expr.args]
            if len(args) < 2:
                raise ValueError(f"{name} requires at least 2 arguments, got {len(args)}")
            op = ixsimpl.and_ if name == "bitand" else ixsimpl.or_
            return op(*args)

    raise ValueError(f"unsupported sympy expression type: {type(expr).__name__}: {expr}")


def extract_assumptions(
    ctx: ixsimpl.Context,
    expr: sympy.Basic,
) -> list[ixsimpl.Expr]:
    """Extract ixsimpl assumption nodes from SymPy symbol properties.

    Walks *expr*, finds every ``sympy.Symbol``, and converts its SymPy
    assumption flags into ixsimpl comparison nodes suitable for passing
    to ``Expr.simplify(assumptions=...)``.

    Recognized flags (checked via ``sym.is_<flag>``):

    * ``nonnegative`` -- emits ``sym >= 0``
    * ``positive``    -- emits ``sym >= 1`` (symbols are integer-valued)
    * ``nonpositive`` -- emits ``sym <= 0``
    * ``negative``    -- emits ``sym <= -1``

    Symbols without any of these flags produce no assumptions.
    """
    seen: set[str] = set()
    result: list[ixsimpl.Expr] = []
    for sym in expr.free_symbols:
        if not isinstance(sym, sympy.Symbol):
            continue
        name = sym.name
        if name in seen:
            continue
        seen.add(name)
        ix = ctx.sym(name)
        if sym.is_positive:
            result.append(ix >= 1)
        elif sym.is_nonnegative:
            result.append(ix >= 0)
        if sym.is_negative:
            result.append(ix <= ctx.int_(-1))
        elif sym.is_nonpositive:
            result.append(ix <= 0)
    return result
