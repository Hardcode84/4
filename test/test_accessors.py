# SPDX-FileCopyrightText: 2026 ixsimpl contributors
# SPDX-License-Identifier: Apache-2.0
"""Unit tests for ixsimpl type-specific accessors and constants."""

from __future__ import annotations

import ixsimpl
import pytest


def test_sym_name() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    assert x.tag == ixsimpl.SYM
    assert x.sym_name == "x"

    dollar = ctx.sym("$T0")
    assert dollar.sym_name == "$T0"


def test_sym_name_wrong_type() -> None:
    ctx = ixsimpl.Context()
    with pytest.raises(TypeError):
        _ = ctx.int_(5).sym_name


def test_rat_num_den() -> None:
    ctx = ixsimpl.Context()
    r = ctx.rat(3, 7)
    assert r.tag == ixsimpl.RAT
    assert r.rat_num == 3
    assert r.rat_den == 7

    r2 = ctx.rat(-5, 3)
    assert r2.rat_num == -5
    assert r2.rat_den == 3


def test_rat_wrong_type() -> None:
    ctx = ixsimpl.Context()
    with pytest.raises(TypeError):
        _ = ctx.sym("x").rat_num
    with pytest.raises(TypeError):
        _ = ctx.sym("x").rat_den


def test_mul_nfactors_and_exp() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    y = ctx.sym("y")
    m = x * y
    assert m.tag == ixsimpl.MUL
    assert m.mul_nfactors == 2
    for i in range(m.mul_nfactors):
        assert m.mul_factor_exp(i) == 1


def test_mul_wrong_type() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("x")
    with pytest.raises(TypeError):
        _ = x.mul_nfactors
    with pytest.raises(TypeError):
        x.mul_factor_exp(0)


def test_mul_factor_exp_out_of_range() -> None:
    ctx = ixsimpl.Context()
    m = ctx.sym("x") * ctx.sym("y")
    with pytest.raises(IndexError):
        m.mul_factor_exp(99)


def test_cmp_op() -> None:
    ctx = ixsimpl.Context()
    x, y = ctx.sym("x"), ctx.sym("y")

    assert (x >= y).cmp_op == ixsimpl.CMP_GE
    assert (x > y).cmp_op == ixsimpl.CMP_GT
    assert (x <= y).cmp_op == ixsimpl.CMP_LE
    assert (x < y).cmp_op == ixsimpl.CMP_LT
    assert ctx.eq(x, y).cmp_op == ixsimpl.CMP_EQ
    assert ctx.ne(x, y).cmp_op == ixsimpl.CMP_NE


def test_cmp_op_wrong_type() -> None:
    ctx = ixsimpl.Context()
    with pytest.raises(TypeError):
        _ = ctx.sym("x").cmp_op


def test_cmp_constants_distinct() -> None:
    vals = [
        ixsimpl.CMP_GT,
        ixsimpl.CMP_GE,
        ixsimpl.CMP_LT,
        ixsimpl.CMP_LE,
        ixsimpl.CMP_EQ,
        ixsimpl.CMP_NE,
    ]
    assert len(vals) == len(set(vals))


def test_int_value() -> None:
    ctx = ixsimpl.Context()
    assert int(ctx.int_(42)) == 42
    assert int(ctx.int_(-7)) == -7
    assert int(ctx.int_(0)) == 0


def test_cross_context_simplify() -> None:
    ctx1 = ixsimpl.Context()
    ctx2 = ixsimpl.Context()
    x1 = ctx1.sym("x")
    x2 = ctx2.sym("x")
    with pytest.raises(ValueError):
        x1.simplify(assumptions=[x2 >= 0])


def test_cross_context_batch() -> None:
    ctx1 = ixsimpl.Context()
    ctx2 = ixsimpl.Context()
    x1 = ctx1.sym("x")
    x2 = ctx2.sym("x")
    with pytest.raises(ValueError):
        ctx1.simplify_batch([x1, x2])


def test_parse_error_sentinel() -> None:
    ctx = ixsimpl.Context()
    e = ctx.parse("???")
    assert e.is_error
    assert e.is_parse_error
    assert e.tag == ixsimpl.PARSE_ERROR


def test_error_propagation() -> None:
    ctx = ixsimpl.Context()
    err = ctx.parse("???")
    x = ctx.sym("x")
    assert (err + x).is_error
    assert (x + err).is_error
    assert (err * x).is_error
    assert (x - err).is_error


def test_is_error_on_valid() -> None:
    ctx = ixsimpl.Context()
    assert not ctx.int_(5).is_error
    assert not ctx.sym("x").is_error
    assert not (ctx.sym("x") + ctx.int_(1)).is_error
