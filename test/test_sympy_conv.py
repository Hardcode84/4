# SPDX-FileCopyrightText: 2026 ixsimpl contributors
# SPDX-License-Identifier: Apache-2.0
"""Tests for ixsimpl.sympy_conv: to_sympy / from_sympy roundtrip."""

from __future__ import annotations

import ixsimpl
import pytest
import sympy
from ixsimpl.sympy_conv import from_sympy, to_sympy


@pytest.fixture()
def ctx() -> ixsimpl.Context:
    return ixsimpl.Context()


@pytest.fixture()
def syms(ctx: ixsimpl.Context) -> dict[str, ixsimpl.Expr]:
    return {name: ctx.sym(name) for name in ("x", "y", "z")}


@pytest.fixture()
def sp_syms() -> dict[str, sympy.Symbol]:
    return {name: sympy.Symbol(name, integer=True) for name in ("x", "y", "z")}


# ---------------------------------------------------------------------------
#  to_sympy tests
# ---------------------------------------------------------------------------


def test_to_sympy_int(ctx: ixsimpl.Context) -> None:
    assert to_sympy(ctx.int_(42)) == sympy.Integer(42)
    assert to_sympy(ctx.int_(-7)) == sympy.Integer(-7)
    assert to_sympy(ctx.int_(0)) == sympy.Integer(0)


def test_to_sympy_rat(ctx: ixsimpl.Context) -> None:
    assert to_sympy(ctx.rat(3, 7)) == sympy.Rational(3, 7)
    assert to_sympy(ctx.rat(-5, 3)) == sympy.Rational(-5, 3)


def test_to_sympy_sym(ctx: ixsimpl.Context) -> None:
    sp = to_sympy(ctx.sym("x"))
    assert isinstance(sp, sympy.Symbol)
    assert sp.name == "x"


def test_to_sympy_add(
    ctx: ixsimpl.Context, syms: dict[str, ixsimpl.Expr], sp_syms: dict[str, sympy.Symbol]
) -> None:
    e = syms["x"] + syms["y"] + 3
    sp = to_sympy(e)
    expected = sp_syms["x"] + sp_syms["y"] + 3
    assert sympy.simplify(sp - expected) == 0


def test_to_sympy_mul(
    ctx: ixsimpl.Context, syms: dict[str, ixsimpl.Expr], sp_syms: dict[str, sympy.Symbol]
) -> None:
    e = syms["x"] * syms["y"]
    sp = to_sympy(e)
    expected = sp_syms["x"] * sp_syms["y"]
    assert sympy.simplify(sp - expected) == 0


def test_to_sympy_div(
    ctx: ixsimpl.Context, syms: dict[str, ixsimpl.Expr], sp_syms: dict[str, sympy.Symbol]
) -> None:
    e = syms["x"] / 3
    sp = to_sympy(e)
    expected = sp_syms["x"] / 3
    assert sympy.simplify(sp - expected) == 0


def test_to_sympy_floor_ceil(
    ctx: ixsimpl.Context, syms: dict[str, ixsimpl.Expr], sp_syms: dict[str, sympy.Symbol]
) -> None:
    assert to_sympy(ixsimpl.floor(syms["x"])) == sympy.floor(sp_syms["x"])
    assert to_sympy(ixsimpl.ceil(syms["x"])) == sympy.ceiling(sp_syms["x"])


def test_to_sympy_mod(
    ctx: ixsimpl.Context, syms: dict[str, ixsimpl.Expr], sp_syms: dict[str, sympy.Symbol]
) -> None:
    sp = to_sympy(ixsimpl.mod(syms["x"], syms["y"]))
    assert sp == sympy.Mod(sp_syms["x"], sp_syms["y"], evaluate=False)


def test_to_sympy_max_min(
    ctx: ixsimpl.Context, syms: dict[str, ixsimpl.Expr], sp_syms: dict[str, sympy.Symbol]
) -> None:
    assert to_sympy(ixsimpl.max_(syms["x"], syms["y"])) == sympy.Max(sp_syms["x"], sp_syms["y"])
    assert to_sympy(ixsimpl.min_(syms["x"], syms["y"])) == sympy.Min(sp_syms["x"], sp_syms["y"])


def test_to_sympy_cmp(
    ctx: ixsimpl.Context, syms: dict[str, ixsimpl.Expr], sp_syms: dict[str, sympy.Symbol]
) -> None:
    x, y = syms["x"], syms["y"]
    sx, sy = sp_syms["x"], sp_syms["y"]
    assert to_sympy(x >= y) == sympy.Ge(sx - sy, 0)
    assert to_sympy(x > y) == sympy.Gt(sx - sy, 0)
    assert to_sympy(x <= y) == sympy.Le(sx - sy, 0)
    assert to_sympy(x < y) == sympy.Lt(sx - sy, 0)
    assert to_sympy(ctx.eq(x, y)) == sympy.Eq(sx - sy, 0)
    assert to_sympy(ctx.ne(x, y)) == sympy.Ne(sx - sy, 0)


def test_to_sympy_piecewise(
    ctx: ixsimpl.Context, syms: dict[str, ixsimpl.Expr], sp_syms: dict[str, sympy.Symbol]
) -> None:
    pw = ixsimpl.pw((syms["x"], syms["x"] > syms["y"]), (syms["y"], ctx.true_()))
    sp = to_sympy(pw)
    assert isinstance(sp, sympy.Piecewise)
    assert len(sp.args) == 2


def test_to_sympy_bool(ctx: ixsimpl.Context) -> None:
    assert to_sympy(ctx.true_()) is sympy.true
    assert to_sympy(ctx.false_()) is sympy.false


# ---------------------------------------------------------------------------
#  from_sympy tests
# ---------------------------------------------------------------------------


def test_from_sympy_int(ctx: ixsimpl.Context) -> None:
    e = from_sympy(ctx, sympy.Integer(42))
    assert e.tag == ixsimpl.INT
    assert int(e) == 42


def test_from_sympy_rat(ctx: ixsimpl.Context) -> None:
    e = from_sympy(ctx, sympy.Rational(3, 7))
    assert e.tag == ixsimpl.RAT
    assert e.rat_num == 3
    assert e.rat_den == 7


def test_from_sympy_sym(ctx: ixsimpl.Context) -> None:
    e = from_sympy(ctx, sympy.Symbol("x", integer=True))
    assert e.tag == ixsimpl.SYM
    assert e.sym_name == "x"


def test_from_sympy_add(ctx: ixsimpl.Context, sp_syms: dict[str, sympy.Symbol]) -> None:
    sp = sp_syms["x"] + sp_syms["y"] + 3
    e = from_sympy(ctx, sp)
    assert e.tag == ixsimpl.ADD


def test_from_sympy_mul(ctx: ixsimpl.Context, sp_syms: dict[str, sympy.Symbol]) -> None:
    sp = 3 * sp_syms["x"]
    e = from_sympy(ctx, sp)
    assert e.tag == ixsimpl.MUL


def test_from_sympy_pow(ctx: ixsimpl.Context, sp_syms: dict[str, sympy.Symbol]) -> None:
    sp = sp_syms["x"] ** 3
    e = from_sympy(ctx, sp)
    assert e.tag == ixsimpl.MUL


def test_from_sympy_neg_pow(ctx: ixsimpl.Context, sp_syms: dict[str, sympy.Symbol]) -> None:
    sp = sp_syms["x"] ** sympy.Integer(-1)
    e = from_sympy(ctx, sp)
    assert e.tag == ixsimpl.MUL


def test_from_sympy_floor_ceil(ctx: ixsimpl.Context, sp_syms: dict[str, sympy.Symbol]) -> None:
    e_fl = from_sympy(ctx, sympy.floor(sp_syms["x"] / 3))
    assert e_fl.tag == ixsimpl.FLOOR
    e_ce = from_sympy(ctx, sympy.ceiling(sp_syms["x"] / 3))
    assert e_ce.tag == ixsimpl.CEIL


def test_from_sympy_mod(ctx: ixsimpl.Context, sp_syms: dict[str, sympy.Symbol]) -> None:
    e = from_sympy(ctx, sympy.Mod(sp_syms["x"], sp_syms["y"], evaluate=False))
    assert e.tag == ixsimpl.MOD


def test_from_sympy_piecewise(ctx: ixsimpl.Context, sp_syms: dict[str, sympy.Symbol]) -> None:
    sp = sympy.Piecewise((sp_syms["x"], sp_syms["x"] > 0), (sp_syms["y"], True))
    e = from_sympy(ctx, sp)
    assert e.tag == ixsimpl.PIECEWISE


def test_from_sympy_relational(ctx: ixsimpl.Context, sp_syms: dict[str, sympy.Symbol]) -> None:
    sx, sy = sp_syms["x"], sp_syms["y"]
    assert from_sympy(ctx, sympy.Ge(sx, sy)).tag == ixsimpl.CMP
    assert from_sympy(ctx, sympy.Gt(sx, sy)).tag == ixsimpl.CMP
    assert from_sympy(ctx, sympy.Le(sx, sy)).tag == ixsimpl.CMP
    assert from_sympy(ctx, sympy.Lt(sx, sy)).tag == ixsimpl.CMP
    assert from_sympy(ctx, sympy.Eq(sx, sy)).tag == ixsimpl.CMP
    assert from_sympy(ctx, sympy.Ne(sx, sy)).tag == ixsimpl.CMP


def test_from_sympy_logic(ctx: ixsimpl.Context, sp_syms: dict[str, sympy.Symbol]) -> None:
    cond = sympy.Gt(sp_syms["x"], 0)
    a = from_sympy(ctx, sympy.And(cond, sympy.Gt(sp_syms["y"], 0)))
    assert a.tag == ixsimpl.AND
    o = from_sympy(ctx, sympy.Or(cond, sympy.Gt(sp_syms["y"], 0)))
    assert o.tag == ixsimpl.OR


def test_from_sympy_bool(ctx: ixsimpl.Context) -> None:
    assert from_sympy(ctx, sympy.true).tag == ixsimpl.TRUE
    assert from_sympy(ctx, sympy.false).tag == ixsimpl.FALSE


def test_from_sympy_huge_exponent(ctx: ixsimpl.Context, sp_syms: dict[str, sympy.Symbol]) -> None:
    huge = sympy.Pow(sp_syms["x"], sympy.Integer(10**9), evaluate=False)
    with pytest.raises(ValueError, match="exponent too large"):
        from_sympy(ctx, huge)


def test_from_sympy_custom_xor(ctx: ixsimpl.Context, sp_syms: dict[str, sympy.Symbol]) -> None:
    """Custom sympy.Function subclass named 'xor' maps to ixsimpl.xor_."""

    class xor(sympy.Function):  # type: ignore[misc]
        pass

    e = from_sympy(ctx, xor(sp_syms["x"], sp_syms["y"]))
    assert e.tag == ixsimpl.XOR


def test_from_sympy_unsupported(ctx: ixsimpl.Context) -> None:
    with pytest.raises(ValueError, match="unsupported"):
        from_sympy(ctx, sympy.sin(sympy.Symbol("x")))


# ---------------------------------------------------------------------------
#  Roundtrip tests
# ---------------------------------------------------------------------------


def test_roundtrip_arithmetic(ctx: ixsimpl.Context, syms: dict[str, ixsimpl.Expr]) -> None:
    x, y = syms["x"], syms["y"]
    e = (x * 3 + y + 1).simplify()
    sp = to_sympy(e)
    e2 = from_sympy(ctx, sp).simplify()
    sp2 = to_sympy(e2)
    assert sympy.simplify(sp - sp2) == 0


def test_roundtrip_floor(ctx: ixsimpl.Context, syms: dict[str, ixsimpl.Expr]) -> None:
    e = ixsimpl.floor((syms["x"] + syms["y"]) / 3)
    sp = to_sympy(e)
    e2 = from_sympy(ctx, sp)
    sp2 = to_sympy(e2)
    assert sympy.simplify(sp - sp2) == 0


def test_roundtrip_piecewise(ctx: ixsimpl.Context, syms: dict[str, ixsimpl.Expr]) -> None:
    pw_expr = ixsimpl.pw((syms["x"], syms["x"] > syms["y"]), (syms["y"], ctx.true_()))
    sp = to_sympy(pw_expr)
    e2 = from_sympy(ctx, sp)
    assert e2.tag == ixsimpl.PIECEWISE
