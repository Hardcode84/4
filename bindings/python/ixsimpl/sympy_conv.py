"""Structural converters between ixsimpl Expr trees and SymPy expressions."""

from __future__ import annotations

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


def to_sympy(expr: ixsimpl.Expr) -> sympy.Basic:
    """Convert an ixsimpl Expr to an equivalent sympy expression.

    Walks the ixsimpl node tree structurally and builds the SymPy
    counterpart.  No simplification is performed on the SymPy side.
    """
    tag = expr.tag

    if tag == ixsimpl.INT:
        return sympy.Integer(int(expr))

    if tag == ixsimpl.RAT:
        return sympy.Rational(expr.rat_num, expr.rat_den)

    if tag == ixsimpl.SYM:
        return sympy.Symbol(expr.sym_name, integer=True)

    if tag == ixsimpl.ADD:
        result: sympy.Basic = to_sympy(expr.add_coeff)
        for i in range(expr.add_nterms):
            result = result + to_sympy(expr.add_term_coeff(i)) * to_sympy(expr.add_term(i))
        return result

    if tag == ixsimpl.MUL:
        result = to_sympy(expr.mul_coeff)
        for i in range(expr.mul_nfactors):
            base = to_sympy(expr.mul_factor_base(i))
            exp = expr.mul_factor_exp(i)
            result = result * base ** sympy.Integer(exp)
        return result

    if tag == ixsimpl.FLOOR:
        return sympy.floor(to_sympy(expr.child(0)))

    if tag == ixsimpl.CEIL:
        return sympy.ceiling(to_sympy(expr.child(0)))

    if tag == ixsimpl.MOD:
        return sympy.Mod(to_sympy(expr.child(0)), to_sympy(expr.child(1)), evaluate=False)

    if tag == ixsimpl.MAX:
        return sympy.Max(to_sympy(expr.child(0)), to_sympy(expr.child(1)))

    if tag == ixsimpl.MIN:
        return sympy.Min(to_sympy(expr.child(0)), to_sympy(expr.child(1)))

    if tag == ixsimpl.XOR:
        return sympy.Xor(to_sympy(expr.child(0)), to_sympy(expr.child(1)))

    if tag == ixsimpl.CMP:
        rel = _CMP_TO_SYMPY.get(expr.cmp_op)
        if rel is None:
            raise ValueError(f"unsupported cmp_op: {expr.cmp_op}")
        return rel(to_sympy(expr.child(0)), to_sympy(expr.child(1)))

    if tag == ixsimpl.AND:
        args = [to_sympy(expr.child(i)) for i in range(expr.nchildren)]
        return sympy.And(*args)

    if tag == ixsimpl.OR:
        args = [to_sympy(expr.child(i)) for i in range(expr.nchildren)]
        return sympy.Or(*args)

    if tag == ixsimpl.NOT:
        return sympy.Not(to_sympy(expr.child(0)))

    if tag == ixsimpl.PIECEWISE:
        pieces: list[tuple[Any, Any]] = []
        for i in range(expr.pw_ncases):
            val = to_sympy(expr.pw_value(i))
            cond = to_sympy(expr.pw_cond(i))
            pieces.append((val, cond))
        return sympy.Piecewise(*pieces)

    if tag == ixsimpl.TRUE:
        return sympy.true

    if tag == ixsimpl.FALSE:
        return sympy.false

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

    if isinstance(expr, sympy.Mod):
        return ixsimpl.mod(from_sympy(ctx, expr.args[0]), from_sympy(ctx, expr.args[1]))

    if isinstance(expr, sympy.Max):
        result = from_sympy(ctx, expr.args[0])
        for arg in expr.args[1:]:
            result = ixsimpl.max_(result, from_sympy(ctx, arg))
        return result

    if isinstance(expr, sympy.Min):
        result = from_sympy(ctx, expr.args[0])
        for arg in expr.args[1:]:
            result = ixsimpl.min_(result, from_sympy(ctx, arg))
        return result

    if isinstance(expr, sympy.Xor):
        result = from_sympy(ctx, expr.args[0])
        for arg in expr.args[1:]:
            result = ixsimpl.xor_(result, from_sympy(ctx, arg))
        return result

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
        result = from_sympy(ctx, expr.args[0])
        for arg in expr.args[1:]:
            result = ixsimpl.and_(result, from_sympy(ctx, arg))
        return result

    if isinstance(expr, sympy.Or):
        result = from_sympy(ctx, expr.args[0])
        for arg in expr.args[1:]:
            result = ixsimpl.or_(result, from_sympy(ctx, arg))
        return result

    if isinstance(expr, sympy.Not):
        return ixsimpl.not_(from_sympy(ctx, expr.args[0]))

    if expr is sympy.true:
        return ctx.true_()

    if expr is sympy.false:
        return ctx.false_()

    raise ValueError(f"unsupported sympy expression type: {type(expr).__name__}: {expr}")
