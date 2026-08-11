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
        "check_predicate",
        "congruent",
        "defined",
        "divisible",
        "equivalent",
        "integer_valued",
        "known_bits",
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
    removed_query_methods = {
        "constant_difference",
        "decompose_exact_quotient",
        "equivalent_finite_domain",
        "finite_difference",
        "integer_range",
    }
    assert removed_query_methods.isdisjoint(dir(ixsimpl.Context))
    assert removed_query_methods.isdisjoint(dir(_ixsimpl.Context))
    retained_module_members = {"TRUNC", "trunc"}
    assert retained_module_members <= set(ixsimpl.__all__)
    assert retained_module_members <= set(dir(ixsimpl))
    assert retained_module_members <= set(dir(_ixsimpl))


def _typecheck_package_surface(
    ctx: ixsimpl.Context, expr: ixsimpl.Expr, facts: ixsimpl.Facts
) -> None:
    tri: bool | None = ctx.check_predicate(expr, facts)
    equivalent: bool | None = ctx.equivalent(expr, expr, facts)
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
        pointer,
        exact,
        transferred,
    )


def _typecheck_extension_surface(
    ctx: _ixsimpl.Context, expr: _ixsimpl._Expr, facts: _ixsimpl.Facts
) -> None:
    tri: bool | None = ctx.check_predicate(expr, facts)
    equivalent: bool | None = ctx.equivalent(expr, expr, facts)
    pointer: int = expr.node_ptr
    batch = [expr]
    ctx.simplify_batch(batch, facts=facts)
    facts.assume_many(batch)
    _ = (
        tri,
        equivalent,
        pointer,
    )
