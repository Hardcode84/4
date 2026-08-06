# SPDX-FileCopyrightText: 2026 ixsimpl contributors
# SPDX-License-Identifier: Apache-2.0
"""Runtime and static-shape checks for the migration binding surface."""

from __future__ import annotations

from typing import Literal

import ixsimpl
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
        "integer_range",
        "integer_valued",
        "known_bits",
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
    expr_members = {"expand", "is_integer_valued", "simplify", "subs"}

    assert context_methods <= set(dir(ixsimpl.Context))
    assert facts_methods <= set(dir(ixsimpl.Facts))
    assert expr_members <= set(dir(ixsimpl.Expr))
    assert {"Context", "Expr", "Facts"} <= set(ixsimpl.__all__)
    assert {"TRUNC", "trunc"} <= set(ixsimpl.__all__)
    assert hasattr(_ixsimpl, "TRUNC") and hasattr(_ixsimpl, "trunc")


def _typecheck_package_surface(
    ctx: ixsimpl.Context, expr: ixsimpl.Expr, facts: ixsimpl.Facts
) -> None:
    tri: bool | None = ctx.check_predicate(expr, facts)
    equivalent: bool | None = ctx.equivalent(expr, expr, facts)
    equivalent_modulo: bool | None = ctx.equivalent_modulo_pow2(expr, expr, 32, facts)
    finite_equivalent: tuple[Literal["complete", "exhausted"], bool | None, int] = (
        ctx.equivalent_finite_domain(expr, expr, facts, 0)
    )
    finite_checks: tuple[
        Literal["complete", "exhausted"], list[tuple[bool | None, int | None]], int
    ] = ctx.check_finite_domain([(expr, [0])], [("defined", expr)], facts, 1)
    difference: int | None = ctx.constant_difference(expr, expr, facts)
    recurrence: tuple[int, ixsimpl.Expr] | None = ctx.modulo_recurrence(
        expr, expr, expr, "unsigned", 32, 5, facts
    )
    integer_range: tuple[int | None, int | None] | None
    integer_range = ctx.integer_range(expr, facts=facts)
    quotient: tuple[ixsimpl.Expr, ixsimpl.Expr] | None
    quotient = ctx.decompose_exact_quotient(expr, facts)
    truncated: ixsimpl.Expr = ixsimpl.trunc(expr)
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
        finite_checks,
        difference,
        recurrence,
        integer_range,
        quotient,
        truncated,
        exact,
        transferred,
    )


def _typecheck_extension_surface(
    ctx: _ixsimpl.Context, expr: _ixsimpl._Expr, facts: _ixsimpl.Facts
) -> None:
    tri: bool | None = ctx.check_predicate(expr, facts)
    equivalent: bool | None = ctx.equivalent(expr, expr, facts)
    equivalent_modulo: bool | None = ctx.equivalent_modulo_pow2(expr, expr, 32, facts)
    finite_equivalent: tuple[Literal["complete", "exhausted"], bool | None, int] = (
        ctx.equivalent_finite_domain(expr, expr, facts, 0)
    )
    finite_checks: tuple[
        Literal["complete", "exhausted"], list[tuple[bool | None, int | None]], int
    ] = ctx.check_finite_domain([(expr, [0])], [("defined", expr)], facts, 1)
    recurrence: tuple[int, _ixsimpl._Expr] | None = ctx.modulo_recurrence(
        expr, expr, expr, "unsigned", 32, 5, facts
    )
    integer_range: tuple[int | None, int | None] | None
    integer_range = ctx.integer_range(expr, facts=facts)
    quotient: tuple[_ixsimpl._Expr, _ixsimpl._Expr] | None
    quotient = ctx.decompose_exact_quotient(expr, facts)
    truncated: _ixsimpl._Expr = _ixsimpl.trunc(expr)
    batch = [expr]
    ctx.simplify_batch(batch, facts=facts)
    facts.assume_many(batch)
    _ = (
        tri,
        equivalent,
        equivalent_modulo,
        finite_equivalent,
        finite_checks,
        recurrence,
        integer_range,
        quotient,
        truncated,
    )
