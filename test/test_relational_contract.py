# SPDX-FileCopyrightText: 2026 ixsimpl contributors
# SPDX-License-Identifier: Apache-2.0

import ixsimpl

RELATIONAL_CONTRACT_CHAIN_EDGES = 300


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
    assert relation_support is not False

    cycle = ctx.facts()
    cycle.assume(x - y <= -1)
    cycle.assume(y - z <= 0)
    cycle.assume(z - x <= 0)
    cycle.assume(a >= 0)

    # Relational projection owns feasibility once it claims the first proof.
    if relation_support is True:
        assert ctx.check(a >= 0, facts=cycle) is None
        assert ctx.range(a, facts=cycle) is None
        assert ctx.equivalent(a, a, cycle) is None
        assert ctx.constant_difference(a, a, cycle) is None


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
    assert late_check is not False
    assert early_check is not False
    assert late_check is early_check
    assert ctx.range(nodes[0], facts=late_anchor) == ctx.range(nodes[0], facts=early_anchor)


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
        loaded.assume(x - noise <= 0)

    assert ctx.equivalent(x, z, base) is ctx.equivalent(x, z, loaded)
    assert ctx.constant_difference(x, z, base) == ctx.constant_difference(x, z, loaded)
    assert ctx.range(x - z, facts=base) == ctx.range(x - z, facts=loaded)


def test_relational_loop_bound_production_witness() -> None:
    ctx = ixsimpl.Context()
    iv = ctx.sym("relation_binding_loop_iv")
    trip = ctx.sym("relation_binding_loop_trip")
    capability = ctx.facts()
    capability.assume(iv - trip <= 0)
    capability.assume(trip <= 0)
    relation_support = ctx.check(iv <= 0, facts=capability)
    assert relation_support is not False

    facts = ctx.facts()
    facts.assume(iv - trip <= -1)
    facts.assume(iv >= 0)
    facts.assume(trip >= -(2**31))
    facts.assume(trip <= 2**31 - 1)
    result = ctx.range(iv, facts=facts)
    assert result is not None
    assert result[0] == 0
    if relation_support is True:
        assert result[1] == 2**31 - 2
