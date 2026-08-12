# SPDX-FileCopyrightText: 2026 ixsimpl contributors
# SPDX-License-Identifier: Apache-2.0

import ixsimpl

RELATIONAL_CONTRACT_CHAIN_EDGES = 300


def _difference(lhs: ixsimpl.Expr, rhs: ixsimpl.Expr, facts: ixsimpl.Facts) -> int | None:
    value = (lhs - rhs).simplify(facts=facts)
    try:
        return int(value)
    except TypeError:
        return None


def test_relational_negative_cycle_contract() -> None:
    ctx = ixsimpl.Context()
    x, y, z, a = (
        ctx.sym(name)
        for name in (
            "relation_binding_cycle_x",
            "relation_binding_cycle_y",
            "relation_binding_cycle_z",
            "relation_binding_cycle_unrelated",
        )
    )
    capability = ctx.facts()
    capability.assume(x - y <= 0)
    capability.assume(y <= 0)
    relation_support = ctx.check(x <= 0, facts=capability)
    assert relation_support is True

    cycle = ctx.facts()
    cycle.assume(x - y <= -1)
    cycle.assume(y - z <= 0)
    cycle.assume(z - x <= 0)
    cycle.assume(a >= 0)

    assert ctx.check(a >= 0, facts=cycle) is None
    assert ctx.range(a, facts=cycle) is None
    assert ctx.equivalent(a, a, cycle) is None

    zero_cycle = ctx.facts()
    zero_cycle.assume(x - y <= -1)
    zero_cycle.assume(y - z <= 0)
    zero_cycle.assume(z - x <= 1)
    zero_cycle.assume(a >= 0)
    assert ctx.check(a >= 0, facts=zero_cycle) is True


def test_relational_chain_insertion_order_contract() -> None:
    ctx = ixsimpl.Context()
    nodes = [
        ctx.sym(f"relation_binding_chain_{i}") for i in range(RELATIONAL_CONTRACT_CHAIN_EDGES + 1)
    ]
    late_anchor = ctx.facts()
    early_anchor = ctx.facts()

    for i in range(RELATIONAL_CONTRACT_CHAIN_EDGES):
        late_anchor.assume(nodes[i] - nodes[i + 1] <= 0)
    late_anchor.assume(nodes[-1] <= 0)

    early_anchor.assume(nodes[-1] <= 0)
    for i in range(RELATIONAL_CONTRACT_CHAIN_EDGES, 0, -1):
        early_anchor.assume(nodes[i - 1] - nodes[i] <= 0)

    late_check = ctx.check(nodes[0] <= 0, facts=late_anchor)
    early_check = ctx.check(nodes[0] <= 0, facts=early_anchor)
    assert late_check is True
    assert early_check is True
    assert ctx.range(nodes[0], facts=late_anchor) == ctx.range(nodes[0], facts=early_anchor)
    assert ctx.range(nodes[0], facts=late_anchor) == (None, 0)


def test_relational_exact_equality_noise_contract() -> None:
    ctx = ixsimpl.Context()
    x, y, z = (
        ctx.sym(name)
        for name in (
            "relation_binding_exact_x",
            "relation_binding_exact_y",
            "relation_binding_exact_z",
        )
    )
    base = ctx.facts()
    loaded = ctx.facts()
    for facts in (base, loaded):
        facts.assume(ctx.eq(x, y))
        facts.assume(ctx.eq(y, z))
    for i in range(RELATIONAL_CONTRACT_CHAIN_EDGES):
        noise = ctx.sym(f"relation_binding_noise_{i}")
        loaded.assume(y - noise <= i + 1)

    assert ctx.equivalent(x, z, base) is True
    assert ctx.equivalent(x, z, loaded) is True
    assert _difference(x, z, base) == 0
    assert _difference(x, z, loaded) == 0
    assert ctx.range(x - z, facts=base) == (0, 0)
    assert ctx.range(x - z, facts=loaded) == (0, 0)


def test_relational_exact_equality_api_contract() -> None:
    ctx = ixsimpl.Context()
    x, y, z = (
        ctx.sym(name)
        for name in (
            "relation_binding_api_x",
            "relation_binding_api_y",
            "relation_binding_api_z",
        )
    )

    direct = ctx.facts()
    direct.assume(ctx.eq(y, x + 4))
    assert ctx.range(y - (x + 4), facts=direct) == (0, 0)
    assert ctx.equivalent(y, x + 4, direct) is True
    assert _difference(y, x, direct) == 4

    complementary = ctx.facts()
    complementary.assume(x - y <= 4)
    complementary.assume(y - x <= -4)
    assert ctx.range(x - y, facts=complementary) == (4, 4)
    assert ctx.equivalent(x, y + 4, complementary) is True
    assert _difference(x, y, complementary) == 4

    nonaffine = ctx.facts()
    nonaffine.assume(ctx.eq(x % 7, y % 5 + 4))
    assert ctx.range(x % 7 - y % 5, facts=nonaffine) == (4, 4)
    assert ctx.equivalent(x % 7, y % 5 + 4, nonaffine) is True
    assert _difference(x % 7, y % 5, nonaffine) == 4

    offset = ctx.facts()
    offset.assume(ctx.eq(x, y + 3))
    offset.assume(ctx.eq(y, z + 4))
    assert ctx.range(x - z, facts=offset) == (7, 7)
    assert ctx.equivalent(x, z + 7, offset) is True
    assert _difference(x, z, offset) == 7

    substituted = direct.subs({x: z})
    assert ctx.range(y - (z + 4), facts=substituted) == (0, 0)
    assert ctx.equivalent(y, z + 4, substituted) is True
    assert _difference(y, z, substituted) == 4

    one_sided = ctx.facts()
    one_sided.assume(x <= y + 4)
    assert ctx.equivalent(x, y + 4, one_sided) is None
    assert _difference(x, y, one_sided) is None

    scaled = ctx.facts()
    scaled.assume(ctx.eq(2 * x, y))
    assert ctx.equivalent(2 * x, y, scaled) is True
    assert _difference(x, y, scaled) is None

    overflow = ctx.facts()
    overflow.assume(ctx.eq(x, y + (2**63 - 1)))
    overflow.assume(ctx.eq(y, z + 1))
    # One representable definition edge exposes y = z + 1; the retained wide
    # relation then proves x and z unequal without narrowing their full delta.
    assert ctx.equivalent(x, z, overflow) is False
    assert _difference(x, z, overflow) is None


def test_relational_loop_bound_production_witness() -> None:
    ctx = ixsimpl.Context()
    iv = ctx.sym("relation_binding_loop_iv")
    trip = ctx.sym("relation_binding_loop_trip")
    capability = ctx.facts()
    capability.assume(iv - trip <= 0)
    capability.assume(trip <= 0)
    relation_support = ctx.check(iv <= 0, facts=capability)
    assert relation_support is True

    facts = ctx.facts()
    facts.assume(iv - trip <= -1)
    facts.assume(iv >= 0)
    facts.assume(trip >= -(2**31))
    facts.assume(trip <= 2**31 - 1)
    result = ctx.range(iv, facts=facts)
    assert result is not None
    assert result[0] == 0
    assert result[1] == 2**31 - 2
