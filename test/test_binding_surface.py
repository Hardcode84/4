# SPDX-FileCopyrightText: 2026 ixsimpl contributors
# SPDX-License-Identifier: Apache-2.0
"""Runtime and static-shape checks for the migration binding surface."""

from __future__ import annotations

from typing import Any, Literal

import ixsimpl
import pytest
from ixsimpl import _ixsimpl


def test_migration_binding_surface_is_discoverable() -> None:
    context_methods = {
        "affine_decompose",
        "check",
        "check_finite_domain",
        "check_predicate",
        "congruent",
        "constant_difference",
        "decompose_exact_quotient",
        "defined",
        "divisible",
        "equivalent",
        "equivalent_modulo_pow2",
        "equivalent_finite_domain",
        "finite_difference",
        "invariant_under_step",
        "integer_range",
        "integer_valued",
        "known_bits",
        "mapped_constant_differences",
        "modulo_recurrence",
        "pow2_fact",
        "range",
        "simplify_batch",
        "split_additive_constant",
        "symbol_congruence",
        "try_exact_divide",
    }
    facts_methods = {
        "assume",
        "assume_many",
        "assume_range",
        "derive_affine",
        "subs",
    }
    expr_members = {"expand", "is_integer_valued", "node_ptr", "simplify", "subs"}

    assert context_methods <= set(dir(ixsimpl.Context))
    assert facts_methods <= set(dir(ixsimpl.Facts))
    assert expr_members <= set(dir(ixsimpl.Expr))
    assert {"Context", "Expr", "Facts"} <= set(ixsimpl.__all__)
    assert {"TRUNC", "trunc"} <= set(ixsimpl.__all__)
    assert hasattr(_ixsimpl, "TRUNC") and hasattr(_ixsimpl, "trunc")


def test_finite_domain_status_transport_and_retry() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("binding_status_x")
    facts = ctx.facts()
    finite = ctx.parse_expr(
        "Piecewise((1, binding_status_x*(binding_status_x - 1)*"
        "(binding_status_x - 2)*(binding_status_x - 3) == 0), (2, True))"
    )
    one = ctx.int_(1)
    facts.assume(x >= 0)
    facts.assume(x <= 3)

    exhausted = ctx.equivalent_finite_domain(finite, one, facts, 3)
    assert exhausted == ("exhausted", None, 3)
    assert tuple(type(item) for item in exhausted) == (str, type(None), int)

    complete = ctx.equivalent_finite_domain(finite, one, facts, 4)
    assert complete == ("complete", True, 0)
    assert tuple(type(item) for item in complete) == (str, bool, int)

    queries: list[tuple[Literal["defined", "integer"], ixsimpl.Expr]] = [
        ("defined", finite),
        ("integer", finite),
    ]
    batch_exhausted = ctx.check_finite_domain([(x, [0, 1, 2, 3])], queries, facts, 7)
    assert batch_exhausted == (
        "exhausted",
        [(None, None), (None, None)],
        7,
    )
    assert type(batch_exhausted[0]) is str
    assert all(
        type(check) is type(None) and type(witness) is type(None)
        for check, witness in batch_exhausted[1]
    )
    assert type(batch_exhausted[2]) is int

    batch_complete = ctx.check_finite_domain([(x, [0, 1, 2, 3])], queries, facts, 8)
    assert batch_complete == (
        "complete",
        [(True, None), (True, None)],
        0,
    )


def test_finite_domain_invalid_status_raises_and_retry_succeeds() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("binding_invalid_retry_x")
    facts = ctx.facts()
    sentinel = ctx.parse_expr("(")

    with pytest.raises(ValueError, match=r"finite domain equivalence:.*sentinel"):
        ctx.equivalent_finite_domain(sentinel, x, facts, 1)
    assert ctx.equivalent_finite_domain(x, x, facts, 0) == (
        "complete",
        True,
        0,
    )

    with pytest.raises(ValueError, match="points are not ordered"):
        ctx.check_finite_domain([(x, [1, 1])], [("defined", x)], facts, 2)
    assert ctx.check_finite_domain([(x, [0])], [("defined", x)], facts, 1) == (
        "complete",
        [(True, None)],
        0,
    )


def test_mapped_constant_differences_preserve_rows_and_budget() -> None:
    ctx = ixsimpl.Context()
    item = ctx.sym("binding_mapped_item")
    base = ctx.sym("binding_mapped_base")
    other = ctx.sym("binding_mapped_other")
    predicate = item >= 1
    expressions = [base + 4 * item + 7, base + 4 * item - 3, predicate, base, other]
    rows = [(0, 2, 1, 0), (2, 0, 2, 1), (0, 2, 1, 0)]
    facts = ctx.facts()

    assert ctx.mapped_constant_differences(item, expressions, rows, facts, 2) == (
        "exhausted",
        None,
        2,
    )
    complete = ctx.mapped_constant_differences(item, expressions, rows, facts, 3)
    assert complete == ("complete", [18, -1, 18], 0)
    assert tuple(type(value) for value in complete) == (str, list, int)

    unknown_rows = [(0, 2, 1, 0), (3, 0, 4, 0)]
    assert ctx.mapped_constant_differences(item, expressions, unknown_rows, facts, 2) == (
        "complete",
        None,
        0,
    )

    with pytest.raises(ValueError, match="index is out of range"):
        ctx.mapped_constant_differences(item, expressions, [(5, 0, 0, 0)], facts, 1)
    assert ctx.mapped_constant_differences(item, expressions, rows[:1], facts, 1) == (
        "complete",
        [18],
        0,
    )


def test_mapped_constant_differences_partial_and_python_validation() -> None:
    ctx = ixsimpl.Context()
    item = ctx.sym("binding_mapped_partial_item")
    base = ctx.sym("binding_mapped_partial_base")
    guard = ctx.sym("binding_mapped_partial_guard")
    partial = ixsimpl.pw((base, guard >= 0))
    expressions = [partial, base]
    rows = [(0, 0, 1, 0)]
    weak = ctx.facts()
    strong = ctx.facts()
    strong.assume(guard >= 0)

    assert ctx.mapped_constant_differences(item, expressions, rows, weak, 1) == (
        "complete",
        None,
        0,
    )
    assert ctx.mapped_constant_differences(item, expressions, rows, strong, 1) == (
        "complete",
        [0],
        0,
    )

    malformed_rows: Any = [(0, 0, 1)]
    with pytest.raises(ValueError, match="four integers"):
        ctx.mapped_constant_differences(item, expressions, malformed_rows, weak, 1)
    with pytest.raises((OverflowError, ValueError)):
        ctx.mapped_constant_differences(item, expressions, [(-1, 0, 1, 0)], weak, 1)
    foreign = ixsimpl.Context()
    with pytest.raises(ValueError, match="different context"):
        ctx.mapped_constant_differences(
            item, [foreign.sym("binding_mapped_foreign")], [(0, 0, 0, 0)], weak, 1
        )


def test_predicate_values_follow_unified_scalar_contract() -> None:
    ctx = ixsimpl.Context()
    x = ctx.sym("binding_predicate_scalar_x")
    facts = ctx.facts()
    predicate = ctx.eq(x, 0)
    queries: list[tuple[Literal["predicate", "defined", "integer"], ixsimpl.Expr]] = [
        ("predicate", predicate),
        ("defined", predicate),
        ("integer", predicate),
    ]

    assert predicate.is_expr and predicate.is_pred
    assert ctx.equivalent_finite_domain(predicate, predicate, facts, 0) == (
        "complete",
        True,
        0,
    )
    assert ctx.check_finite_domain(
        [(x, [0, 1])],
        queries,
        facts,
        6,
    ) == (
        "complete",
        [(False, 1), (True, None), (True, None)],
        0,
    )

    recurrence = ctx.modulo_recurrence(predicate, predicate, predicate, "unsigned", 1, 1, facts)
    assert recurrence is not None
    increment, remainder = recurrence
    assert type(increment) is int and increment == 0
    assert isinstance(remainder, ixsimpl.Expr)
    assert ctx.equivalent(remainder, ctx.int_(0), facts) is True


def _typecheck_package_surface(
    ctx: ixsimpl.Context, expr: ixsimpl.Expr, facts: ixsimpl.Facts
) -> None:
    tri: bool | None = ctx.check_predicate(expr, facts)
    equivalent: bool | None = ctx.equivalent(expr, expr, facts)
    equivalent_modulo: bool | None = ctx.equivalent_modulo_pow2(expr, expr, 32, facts)
    finite_equivalent: tuple[Literal["complete", "exhausted", "limited"], bool | None, int] = (
        ctx.equivalent_finite_domain(expr, expr, facts, 0)
    )
    limited_status: bool = finite_equivalent[0] == "limited"
    finite_checks: tuple[
        Literal["complete", "exhausted", "limited"],
        list[tuple[bool | None, int | None]],
        int,
    ] = ctx.check_finite_domain([(expr, [0])], [("defined", expr)], facts, 1)
    predicate: ixsimpl.Expr = ctx.eq(expr, 0)
    predicate_finite: tuple[Literal["complete", "exhausted", "limited"], bool | None, int] = (
        ctx.equivalent_finite_domain(predicate, predicate, facts, 0)
    )
    predicate_checks = ctx.check_finite_domain(
        [(expr, [0])], [("predicate", predicate), ("defined", predicate)], facts, 2
    )
    mapped_differences: tuple[
        Literal["complete", "exhausted", "limited"], list[int] | None, int
    ] = ctx.mapped_constant_differences(expr, [expr], [(0, 0, 0, 0)], facts, 1)
    predicate_recurrence: tuple[int, ixsimpl.Expr] | None = ctx.modulo_recurrence(
        predicate, predicate, predicate, "unsigned", 1, 1, facts
    )
    difference: int | None = ctx.constant_difference(expr, expr, facts)
    recurrence: tuple[int, ixsimpl.Expr] | None = ctx.modulo_recurrence(
        expr, expr, expr, "unsigned", 32, 5, facts
    )
    integer_range: tuple[int | None, int | None] | None
    integer_range = ctx.integer_range(expr, facts=facts)
    quotient: tuple[ixsimpl.Expr, ixsimpl.Expr] | None
    quotient = ctx.decompose_exact_quotient(expr, facts)
    truncated: ixsimpl.Expr = ixsimpl.trunc(expr)
    pointer: int = expr.node_ptr
    exact: tuple[Literal["proven", "not_exact", "unknown"], ixsimpl.Expr | None]
    exact = ctx.try_exact_divide(expr, 1, facts)
    batch = [expr]
    ctx.simplify_batch(batch, facts=facts)
    facts.assume_many(batch)
    transferred: ixsimpl.Facts = facts.subs({expr: expr})
    _ = (
        tri,
        equivalent,
        equivalent_modulo,
        finite_equivalent,
        limited_status,
        finite_checks,
        predicate_finite,
        predicate_checks,
        mapped_differences,
        predicate_recurrence,
        difference,
        recurrence,
        integer_range,
        quotient,
        truncated,
        pointer,
        exact,
        transferred,
    )


def _typecheck_extension_surface(
    ctx: _ixsimpl.Context, expr: _ixsimpl._Expr, facts: _ixsimpl.Facts
) -> None:
    tri: bool | None = ctx.check_predicate(expr, facts)
    equivalent: bool | None = ctx.equivalent(expr, expr, facts)
    equivalent_modulo: bool | None = ctx.equivalent_modulo_pow2(expr, expr, 32, facts)
    finite_equivalent: tuple[Literal["complete", "exhausted", "limited"], bool | None, int] = (
        ctx.equivalent_finite_domain(expr, expr, facts, 0)
    )
    limited_status: bool = finite_equivalent[0] == "limited"
    finite_checks: tuple[
        Literal["complete", "exhausted", "limited"],
        list[tuple[bool | None, int | None]],
        int,
    ] = ctx.check_finite_domain([(expr, [0])], [("defined", expr)], facts, 1)
    predicate: _ixsimpl._Expr = ctx.eq(expr, 0)
    predicate_finite: tuple[Literal["complete", "exhausted", "limited"], bool | None, int] = (
        ctx.equivalent_finite_domain(predicate, predicate, facts, 0)
    )
    predicate_checks = ctx.check_finite_domain(
        [(expr, [0])], [("predicate", predicate), ("defined", predicate)], facts, 2
    )
    mapped_differences: tuple[
        Literal["complete", "exhausted", "limited"], list[int] | None, int
    ] = ctx.mapped_constant_differences(expr, [expr], [(0, 0, 0, 0)], facts, 1)
    predicate_recurrence: tuple[int, _ixsimpl._Expr] | None = ctx.modulo_recurrence(
        predicate, predicate, predicate, "unsigned", 1, 1, facts
    )
    recurrence: tuple[int, _ixsimpl._Expr] | None = ctx.modulo_recurrence(
        expr, expr, expr, "unsigned", 32, 5, facts
    )
    integer_range: tuple[int | None, int | None] | None
    integer_range = ctx.integer_range(expr, facts=facts)
    quotient: tuple[_ixsimpl._Expr, _ixsimpl._Expr] | None
    quotient = ctx.decompose_exact_quotient(expr, facts)
    truncated: _ixsimpl._Expr = _ixsimpl.trunc(expr)
    pointer: int = expr.node_ptr
    batch = [expr]
    ctx.simplify_batch(batch, facts=facts)
    facts.assume_many(batch)
    _ = (
        tri,
        equivalent,
        equivalent_modulo,
        finite_equivalent,
        limited_status,
        finite_checks,
        predicate_finite,
        predicate_checks,
        mapped_differences,
        predicate_recurrence,
        recurrence,
        integer_range,
        quotient,
        truncated,
        pointer,
    )
