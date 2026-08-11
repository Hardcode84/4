# Bounds and Proof Services

[Design index](DESIGN.md)

Many simplification rules require knowing whether a subexpression is
non-negative, positive, or bounded. A lightweight interval analysis pass:

`bounds_store.c` owns retained variable records, expression ranges, nonzero
facts, name and expression indexes, modular-inverse watchers, and their raw
mutation operations. `bounds_assume.c` owns predicate validation and iterative
AND flattening, comparison fact recognition, nonzero publication, affine and
proportional range publication, and modular-inverse watcher refinement. It
validates a complete predicate tree before publishing any leaf. General
comparisons retain their bounded definedness and range rechecks inside the
current query hold; invalid input, proof limits, contradiction, and allocation
failure keep their existing result channels. `bounds_difference.c` owns the
directed constraint graph,
its index, feasibility potentials, and interval-propagation worklists. It calls
only store, exact-relation, and neutral arithmetic APIs; it does not re-enter
bounds proof or simplification policy. `bounds_relation.c` owns exact-component
cursor traversal, equality projection, and the projection-cache lifecycle.
`bounds_bitfacts.c` owns structural known-bit and power-of-two queries.
`bounds_defined.c` owns iterative domain proofs, Piecewise partition coverage,
depth-safe range subqueries, and definedness projection-cache publication.
`bounds_integer.c` owns the compound integer, divisibility, and residue
scheduler plus exact integer and divisibility transitions. `bounds_proof.h`
owns its internal obligation, frame, and memo representation.
`bounds_predicate.c` owns iterative tri-state predicate evaluation, bounded
implication branches, and finite-domain enumeration over range/nonzero atoms.
It does not call equivalence. The facts-facing query boundary applies the
equivalence-owned EQ/NE fallback only after structural predicate evaluation is
inconclusive; equivalence may use predicate truth as a lower proof service.
`facts_store.c` owns reusable fact-set session/epoch identity, transaction
fork/commit/poison, fact transfer, dependency closure, its bounded retained
cache, and the create/assume/derive/substitute mutation APIs. Predicate branches
borrow its one-root closure entry point. `facts_query.c` owns fact-set read
validation and query transactions, scalar and batch simplification, exact
division, metadata queries, and the public read API. `bounds_equivalence.c`
owns equivalence query policy, exact EQ/NE fallback, ordered-congruence, and
Piecewise selector proofs. `bounds_modular.c` owns normalized exact-integer
projection, paired-Mod exact-delta search, wide signed arithmetic, dynamic
no-wrap lifts, and its growable progress stack.
`bounds_residue.c` owns target-modulus residue transitions, including
proof-independent rational cancellation and branch-sensitive Piecewise
evaluation. It does not start a second proof driver. `bounds_stride.c` owns
phase-free stride queries and coefficient scaling.
`bounds_assume.c` owns canonical alias creation and passes canonical nodes or
trusted symbols to the leaf owners.
`bounds_range.c` owns relation endpoint admission, direct interval caching and
transfer, structural and Piecewise ranges, equality-component range projection, integral
and congruence refinement, truncating-remainder ranges, emptiness, and interval
comparison entailment. Full store invalidation refreshes the central query
owner, clears range caches, then clears relation projections; each leaf
component writes only its owned fields.

`bounds_lifecycle.c` orchestrates aggregate initialization, fork, and
destruction through typed store, query, difference, relation, and range
operations. Leaf owners do not depend on lifecycle coordination.
Initialization performs allocation-free query ownership setup, initializes
dense variable storage, then performs allocation-free difference initialization
before relation state and the direct range cache. Fork query ownership
initialization and inheritance are also allocation-free. Fork payload
allocations occur in this order: dense variables, the variable index, the
difference edge index, the difference variable table, modular-inverse heads and
watchers, the relation clone, expression storage and its index, then nonzero
facts. Difference fork inheritance is allocation-free; its clone stage copies
the mutable index and variable arrays while their incident lists retain
immutable edges in the common scratch-arena lifetime. Each stage consumes state
published by its predecessors, and a failed fork is discarded as one
aggregate.

The former `bounds.c` monolith is fully deleted. Lizard function counts at the
successive extraction checkpoints account for all 709 original residents:
709 -> 708 -> 706 -> 672 -> 621 -> 570 -> 509 -> 445 -> 394 -> 308 -> 252 ->
189 -> 122 -> 86 -> 9 -> 0. Each step either moved a body to the named owner
above, folded it into that owner's typed operation, or deleted an impossible or
duplicate state. The move-only checkpoints changed production C/H from 34,410
to 34,605 CLOC; final coordination placement reduces that cumulative growth to
192 CLOC. Later correctness and proof changes are accounted separately.

Pure integer congruence residue, alignment, and interval-intersection helpers
live with interval arithmetic in `interval.c`. `rational.c` owns exact
rational arithmetic plus checked unsigned modular multiplication and inverse.
The header-only `hash.h` pointer mixer is shared by hot identity indexes; table
layout, load factor, and allocation remain consumer-owned.

- **Variable storage**: Per-variable bounds live in a growable array on the
  scratch arena (starts at 16 slots, doubles on overflow). An open-addressed
  dense-index table keyed by interned name pointer provides expected O(1)
  lookup and insertion. The index grows at 75% load, so rehashing is amortized
  O(1); a failed growth does not publish a partial variable or index.
- **Interval bounds**: `$T0 >= 0`, `$T0 < 256`, etc. — the simplifier
  extracts interval bounds from comparison assumptions automatically
- **Range queries**: The iterative interval walker uses the shared query driver
  and the central owner/generation cache. Direct expression entries use the
  fixed range cache, while equality projection reserves and publishes a whole
  admitted component before completing its columns. Mod, truncating division,
  extrema, bitwise, and first-match Piecewise transfer stay inside the range
  owner. Comparison checks consume those intervals without re-entering
  simplification policy.
- **Expression range facts**: explicit or derived facts of the form
  `range(expr) = [lo, hi]` are stored in the same bounds context as
  symbol intervals. A dense unique-expression array retains iteration order;
  an open-addressed pointer index provides expected O(1) lookup and insertion.
  Repeated facts intersect into the existing entry, and an empty intersection
  remains contradictory. Facts are keyed by hash-consed expression node and by
  an expanded, fact-free-simplified canonical alias, so
  `2*(A + 8*B)` and `2*A + 16*B` can prove the same range when both normalize
  to the same form.  Comparison
  assumptions over integer-valued expressions also materialize expression
  range facts; for example `-C + expr <= 0` records `expr <= C`. ADD facts and
  queries additionally normalize to `offset + scale * primitive`: the offset
  is removed and every term coefficient is divided by the first canonical
  term coefficient. The primitive is transform-cached, and its range is stored
  in the existing pointer index. This lets a fact on `64*u+w` bound both
  `128+64*u+w` and `128+2*(64*u+w)` without requiring independent ranges for
  `u` and `w`. Rational overflow or an unrepresentable inverse conservatively
  skips the proportional alias.
- **Nonzero facts**: normalized `expr != 0` assumptions are retained in dense
  insertion order. Up to four entries use a bounded inline scan. The fifth
  creates an 8-slot open-addressed pointer index, which doubles before
  exceeding 75% load for expected O(1) membership. Index preparation precedes
  vector growth, and neither publishes on failure. Bounds forks copy the dense
  vector and then
  its index, and fact substitution retains the same order. Reciprocal guards
  can therefore use incoming disequalities and branch-local conditions. A
  direct zero range for the same expression is a detected contradiction.
- **Contradiction cache**: the detected-empty result is cached until any bound,
  congruence, bit, nonzero, or expression-range mutation. Query hits are O(1);
  a miss scans unique variables, expressions, and exclusions once.
- **Modular congruence**: `Mod(K, 32) == R` — the simplifier tracks
  `K ≡ R (mod 32)`.  Multiple assumptions on the same symbol merge via CRT
  (Chinese Remainder Theorem).  Pure divisibility (`R == 0`) is the common
  special case; `Mod(K, 256) == 0` implies `Mod(K, 32) == 0`.
- **Congruent range intersection**: finite symbol interval endpoints round
  inward to the nearest value satisfying the stored congruence before range
  propagation. Unrepresentable aligned endpoints retain the original bound.
- **Modular entailment**: `ixs_check` uses the same congruence facts for
  `Mod(expr, m) == r` and `Mod(expr, m) != r` queries.  It proves exact
  symbol remainders when the stored modulus is a multiple of the query
  modulus, and proves zero remainders for composite expressions through
  the same sufficient divisibility predicate used by simplification rules.
- **Atomic predicate checks**: `ixs_check` and `ixs_check_facts` accept a
  normalized comparison or the canonical integer `1`/`0` produced when a
  smart constructor resolves one. A comparison whose right-hand side cannot
  be moved to zero without overflowing remains unknown under this atomic
  contract; the general predicate query can still check it directly. Other
  non-comparison expressions remain unknown. Contradictory fact domains never
  prove even a constant predicate. Both entry points run the same scalar proof
  contract: one query generation spans the fast interval, congruence, and bit
  checks plus the exact fallback for an unresolved `EQ` or `NE` and the
  early ordered Euclidean-split check for an unresolved zero-RHS ordered
  comparison, plus the bounded radix fallback for an unresolved zero-RHS
  `GE`. Exact proofs require total operands. Cycles,
  bounded subproof exhaustion, and allocation failure return unknown without
  poisoning the reusable session or fact set.

  The radix fallback is the private `src/radix_algebra.c` component. It borrows
  one canonical `ADD` row with integral term coefficients and views its
  coefficients in the comparison's orientation; orientation rejects
  `INT64_MIN` instead of constructing a negated expression. The early ordered
  path has a bounded syntactic admission requiring a positive dividend
  coefficient and a negative `Mod` coefficient for that same dividend, so pure
  floor certificates and their range queries remain on the late `GE` path. The
  proof first handles literal positive divisors in admitted
  `floor(base / divisor)` terms. It repeatedly substitutes
  `base = divisor*floor(base/divisor) + Mod(base, divisor)` into a positive
  parent coefficient. The omitted remainder is nonnegative. When an existing
  `Mod(base, d)` term has positive `d` dividing the transferred radix, the
  proof may retain that tighter lower bound because
  `Mod(base, radix) >= Mod(base, d)`. A certificate succeeds only when every
  residual coefficient is nonnegative and an ordinary range query proves each
  remaining positive term nonnegative. After all literal floor transfers, the
  same row may cancel `k = min(c, -r)` from a positive `c*x` term and a
  negative `r*Mod(x,m)` term. This drops the nonnegative Euclidean split
  `k*(x - Mod(x,m))` when `x` is integer and nonnegative and the possibly
  dynamic modulus `m` is strictly positive; it never materializes a symbolic
  floor or coefficient. One fixed stack proof row has 16 slots, admits at most
  eight initial terms, and rejects a certificate that reaches the 16-transfer
  ceiling. For `T <= 8` input terms, `N <= 16` slots, and `K < 16` transfers,
  intrinsic row bookkeeping is `O(T*N + K*N^2 + N^2)` in a fixed 16-slot row.
  Mod cancellation makes at most `3*N` inherited domain-oracle calls, followed
  by at most `N` ordinary range-oracle calls; there is no context-wide scan.
  The transfer ceiling is an explicit local limit and does not poison other
  proof strategies. Checked coefficient overflow, an unsupported shape,
  missing bounds, contradiction, or dirty nested-query transport is an
  ordinary `UNKNOWN`; nested range-query allocation failure is reported as
  OOM.

  Complete literal mixed-radix reconstructions are canonical simplifier input,
  not a separate equality tactic. After equivalence proves both operands
  defined, fact simplification uses any proved carrier integrality and reduces a
  complete digit row to its direct `Mod(A,R)` form. Pointer equality then closes
  the proof. The exact row shape, bounded O(T^2) recognition, and negative-case
  contracts are specified in [Simplification](simplification.md).
- **Bitwise facts**: Power-of-two and mask assumptions use a small
  bitfact domain stored alongside per-symbol bounds:

  ```c
  typedef enum {
      IXS_POW2_UNKNOWN,
      IXS_POW2_OR_ZERO,
      IXS_POW2_POSITIVE
  } ixs_pow2_fact;

  typedef struct {
      uint64_t known_zero;      /* low 64 bits known to be zero */
      uint64_t known_one;       /* low 64 bits known to be one */
      ixs_pow2_fact pow2;
  } ixs_bitfacts;
  ```

  `known_zero` and `known_one` are a low-64-bit KnownBits-style abstraction.
  They are intentionally finite even though expression semantics are unbounded:
  this is enough for `int64_t` constants, masks, tile sizes, and power-of-two
  divisibility checks without turning the core engine into a fixed-width
  bit-vector solver. `pow2` is separate because "zero or exactly one bit set"
  is a cardinality fact, not expressible as independent known-zero/known-one
  bits unless the bit position is already known.

  Initial storage is symbol-level in `ixs_var_bound`. `bounds_bitfacts.c`
  computes expression-level facts on demand for constants, symbols, comparisons,
  logical NOT, `ADD`, restricted `MUL`/`FLOOR`/`MOD`, and `AND`/`OR`/`XOR`.
  Iterative bounds queries use the private structural stack in `query_walk.c`.
  Typed frames keep the expression pointer first; storage starts at the
  consumer's configured capacity, doubles with checked arena growth at pointer
  alignment, and is zeroed before the expression is published. Bitfacts,
  stride, residue, and interval queries start at 16 frames. The compound exact
  proof query keeps 16 integer/divisibility frames inline; its residue pool
  starts at 16 scratch frames. Both typed pools share one active-frame
  discriminator and driver while retaining their previous frame sizes and
  growth cutoffs.
  Definedness, predicate, and AND-assumption walks start at 32 frames.

  The structural driver owns push/pop, growth, and optional LIFO abort. Its
  `run` entry owns one scratch mark; memo-first consumers use the mark-free
  seeded driver inside a caller-owned mark. Definedness, predicate, and
  AND-assumption walks allocate a per-query node-identity memo before their
  stack. The compound proof query keeps an inline 32-entry memo over
  `(bounds owner, node, obligation, modulus)`. It memoizes integer and
  divisibility obligations, and proof-independent residue obligations, for one
  scratch lifetime. Ordinary residue frames retain the central `bounds_query`
  cache because their results belong to the active environment; exact
  subobligations remain in the local compound memo. Local identity and compound
  memos share the stack's caller-owned mark and die at its restore. The central
  cache is generation-scoped and owner-keyed; forks share its query state while
  the local bounds-owner key prevents branch results from aliasing.

  `bounds_residue.c` keeps the requested modulus in each typed frame. Rational
  ADD coefficients use one synthetic scaled-residue obligation inside the same
  graph; equal representatives are grouped in scratch storage after required
  integrality obligations are discharged. MUL proves every factor integer
  before a zero coefficient or reduced modulus of one can finish the residue.
  Reachable Piecewise branches run in bounds forks. Proof-independent mode
  consults only structural and stored facts.
  `bounds_stride.c` joins ADD and Piecewise operands with gcd, scales linear
  products without overflowing the retained stride, and maps literal `Mod`
  through the gcd of dividend stride and modulus.

  `bounds_query.c` owns that opaque central state and its lifecycle. Interval,
  bitfacts, residue, and stride entries use keys containing the kind, bounds
  owner, expression, integer argument, and equality-disabled mode. A tracked
  outer hold starts one generation; nested holds share it. The active-key stack
  starts at 16 entries and doubles. The open-addressed cache starts at 256
  entries and grows before exceeding 75% load, giving expected O(1) lookup.
  Invalid state, OOM, and limits poison the generation in that precedence
  order.

  Context-backed bounds allocate central state lazily in the context arena.
  Contextless bounds retain one state and its geometrically grown key/cache
  arrays in `query_state_arena`, bounded by the largest single query.
  `query_arena` holds operation-bounded proof storage and projection storage
  for forks and contextless bounds. Persistent facts allocate their projection
  table in the context arena and reuse that allocation across reads and
  commits. Projection entries carry a separate nonzero `uint32_t` generation;
  lookup and growth consider only the current generation. Ordinary
  invalidation clears the live count and advances the generation in O(1).
  Generation wrap clears the retained table and resumes at one. `facts_commit`
  retains the destination allocation and generation, then invalidates it once.
  A fork under an active hold borrows central state with a distinct owner. Its
  embedded arenas start empty, and `query_state_arena` stays empty while state
  is borrowed. Direct range and relation-projection caches remain separate.
  `bounds_store.c` refreshes the central query owner, then asks
  `bounds_range.c` and `bounds_relation.c` to invalidate their caches. The query
  component does not initiate store invalidation.

  Consumers own transfer values, cache finish policy, mapping typed transport
  into result status, and final publication. Bitfacts allocates its per-child
  result arrays while preparing supported nodes. Query-stack push/pop is
  amortized O(1) and uses O(depth) scratch. Memoized walkers visit shared
  structural obligations once; consumer transfer and cache policy determine
  their remaining work. No walker stack imposes a fixed depth ceiling; consumer
  query budgets still apply. Branch-local facts are copied by `ixs_bounds_fork`,
  so `Piecewise` branch assumptions remain isolated.
- `floor(x)`: if `lo <= x <= hi`, then `floor(lo) <= floor(x) <= floor(hi)`
- `Mod(x, m)`: result in `[0, m-1]` when `m > 0` and `x` is integer-valued
- `ceiling(x/m)`: result >= 0 when `x >= 0` and `m > 0`

**Compound assumption ingestion**: All predicate-bearing entry points use one
bounded iterative walker: `ixs_simplify`, `ixs_simplify_batch`, `ixs_check`,
`ixs_check_integer_valued`, `ixs_check_defined`, `ixs_get_pow2_fact`,
`ixs_range`, `ixs_facts_create_preds`, `ixs_facts_assume_pred`, and
`ixs_facts_assume_preds`. Each predicate root may be a CMP, a canonical
true/false node, or an AND tree whose leaves have those forms. True
contributes no fact; false marks the bounds as contradictory. Supporting these
constants preserves predicates that simplify before ingestion, such as
`(x & 0) == 0`. The iterative walker has no semantic depth ceiling and does not
consume one C call frame per nested conjunction.

OR, NOT, other node kinds, NULL or sentinel nodes, malformed CMP/AND nodes, and
nodes from another context are rejected with an `assumptions:` diagnostic.
Legacy array ingestion discards the whole temporary bound context when any
entry is rejected or fails; it never queries a partially ingested prefix.
Individual CMP and true/false roots validate without allocating an AND-cycle
worklist. Only an AND root takes the bounded iterative walker path. A fresh
bounds build also keeps its empty interval-result cache detached during
ingestion, because no published query result exists to invalidate yet.
`ixs_facts_create_preds` uses the same direct one-shot builder. It imports one
exact assumption domain without simplifying predicates against earlier
entries. Invalid input or OOM returns NULL without exposing a partial fact set.
This compatibility surface is intentionally C-only: C++ and Python `Facts`
keep the sequential closure semantics of their mutation APIs instead of
offering two constructors whose predicates have different meanings.
`facts_store.c` applies `ixs_facts_assume_preds` to one fork and commits only
after every tree succeeds. It validates the full array and ingests each
original predicate once before fact-conditioned simplification. This preserves
exact expression identities that a rewrite may otherwise replace. It then
saturates the batch with a dependency worklist. Every first-position unique
predicate is queued once; a semantic refinement requeues only predicates that
share a syntactic symbol with the predicate that produced it. Simplification
cannot introduce a symbol absent from the original predicate, so an unrelated
predicate cannot observe that refinement. A symbol-free refinement
conservatively requeues the whole batch. Closure ends when the queue is empty;
there is no batch-size or round-count limit. Bounds domains are monotone, and a
queue entry can create more work only when it strictly refines a fact.

The dependency index uses iterative DAG traversal, a per-predicate node set,
and an open-addressed interned-symbol table. Pointer-identical predicates are
filtered in expected O(n), preserving each first input position. Hash tables
are kept at no more than half load. For `v` input DAG nodes counted once per
unique predicate and `e` predicate-symbol incidences, index construction is
expected O(n + v + e). Reprocessing cost is proportional to dequeued
predicates plus the symbol adjacency lists scheduled by actual refinements;
independent predicates are not rescanned after another component changes.
All queue, deduplication, traversal, and index storage lives in an
input-scoped temporary arena and is released before return, including on a
successful commit. Allocation failure fails the transaction. Store
hash-consing makes structurally equal live nodes pointer-identical. Distinct
pointers, including noncanonical predicates that later normalize to the same
node, remain separate inputs and participate independently in closure.

Fresh empty-domain mutations also admit an exact context-lifetime closure
cache. Its direct-mapped 32-slot key is the full ordered predicate-pointer
array; a hash match is verified by count and pointer-by-pointer comparison.
The cold worklist records every first-position-unique original predicate,
followed by each simplified root whose ingestion strictly refined the semantic
domain. A hit replays that exact sequence into the transaction fork without
rebuilding the dependency index or sharing mutable bounds storage. The
caller's closed-domain validation remains separate: a closed batch is stored
only after validation succeeds, and every hit is validated again. Nonempty
incoming domains always use the worklist.

Each cache slot has one 3 KiB combined key-and-replay budget. There is no
separate input-count or derived-root limit: a sequence that does not fit is not
truncated and completes through the ordinary worklist path. Slots are
allocated lazily and collision replacement reuses their storage, bounding all
cache objects below 128 KiB per context. Cache allocation failure is an
optimization miss, while any allocation or validation failure during closure
construction or replay retains the normal transaction-poisoning contract.
Cached nodes are context-owned and immutable, so entries survive session reset
and are released with the context. Lookup is O(n) in explicit batch size;
replay is O(u + r) for `u` unique originals and `r` recorded refinements. Both
bounds are independent of total context state.

A reusable fact set retains its owning session implementation, context, epoch,
usability latch, and committed bounds payload. Every mutation binds the current
session epoch before touching that payload. The candidate fork borrows active
scratch only for the transaction; commit resets both query workspaces before
publishing the aggregate and preserves only context-owned semantic storage.
Failure discards the candidate and poisons the destination, so no borrowed
query state, temporary arena storage, or partial publication survives return.

Each public fact read binds the current session, snapshots query transport and
diagnostics, and restores bounds-local OOM state before unbinding. Invalid,
limited, and OOM outcomes invalidate speculative read caches and retain their
distinct diagnostics. Failed batch simplification restores every input root;
semantic poison is a completed simplification result and remains published;
scalar metadata calls initialize output parameters before validation. The read
service owns that publication policy while lower bounds services return typed
algebra status without writing public outputs.

Speculative read and algebra adapters share one query-transaction primitive.
It independently snapshots optional scratch, diagnostics, bounds-local OOM,
and query transport, then returns raw new-OOM, limited, and invalid
observations. It does not rank those observations or publish result roots.
Constant-difference proof keeps its local OOM-before-invalid ordering, while a
public fact read publishes invalid before OOM. A forced public read snapshots
the old OOM latch before entering its hold and transport after entry, so hold
allocation failure remains visible without treating the new generation as an
invalid query.

Scalar `ixs_simplify` has a separate session-local reuse path for its direct
assumption array. The first nonempty array containing at most 64 roots retains
its prepared semantic bounds domain. Later calls reuse it only after an exact
ordered pointer comparison; a different key builds ordinary temporary bounds
and never replaces the retained entry. The cache therefore grows with at most
one explicit input domain, not with call count or context state. OOM or a proof
limit clears query results before the domain is reused, and a rejected build is
never published. Cache-storage OOM falls through to the ordinary temporary
builder. Retained semantic storage uses a separate session-owned arena, so it
does not move parser or rewrite temporaries past the ordinary scratch mark;
read-query temporaries still use ordinary session scratch. Session reset and
destroy release both cache arenas. This changes no assumption semantics and
does not apply the reusable-facts closure algorithm.

`ixs_facts_assume_pred` is its one-element form.
Python `Facts.assume_many` and C++ `Facts::assume_many` expose the same batch.
Rejection or OOM leaves the stored payload unchanged but poisons the fact set,
so no caller can continue proving from a partial or silently weaker context.
Every fact mutator follows this rule. Rejection
returns the domain-error sentinel from `ixs_simplify`, fills an entire batch
with that sentinel, returns unknown/no-result from the query APIs, and returns
false from either fact assumption API. Structurally valid but contradictory
conjunctions retain the existing unknown/no-result behavior.

**Conflicting assumptions**: User-assumption validation and error reporting are
**best-effort**. Direct contradictions are detected where the local domains can
see them: empty interval intersections, eagerly merged expression bounds, and
bitfact conflicts such as a bit known both zero and one. Query APIs treat
detected contradictions as unknown/no-result rather than manufacturing a
concrete answer. Simplification may return `IXS_ERROR` and append a diagnostic
when the reporting path has enough context, but callers must not rely on every
contradictory assumption set producing an error string.

The bounds payload connects normalized integer expressions of the form
`c + x - y` through directed constraints `x - y <= k`. Finite upper endpoints
flow with the edge and finite lower endpoints flow against it. Each source
endpoint is first intersected with its symbol expression override and aligned
to its congruence, so projected bounds retain the existing interval and
modular-domain precision. Non-unit coefficients remain expression facts and
do not enter this graph.

**Relational-facts acceptance contract**: Once unit-difference projection is
enabled, every admitted constraint `x - y <= c` participates in one complete
fact domain with these properties:

- Feasibility is part of mutation, not a query-time option. A negative cycle
  marks the candidate contradictory before commit. Range, predicate,
  equivalence, definedness, integrality, divisibility, known-bit, congruence,
  simplification, and algebra queries must then follow their existing
  contradictory-domain result contract; an unrelated direct fact cannot leak
  a concrete answer from the empty domain.
- Arbitrarily long transitive chains are supported subject only to allocation
  and checked-size failures. There is no semantic edge, node, round, or queue
  limit. The same conjunction has the same closure in every insertion order.
  Allocation or size failure makes the mutator fail and poisons the fact set;
  it cannot truncate propagation and report success.
- Exact `x = y + c` relations are independent of one-sided graph fan-out.
  Adding inequalities that do not alter the equality component cannot change
  range, equivalence, or exact-value answers for that component.
- Fork, transaction rollback, substitution, and OOM paths preserve the whole
  relational payload or none of it. No graph edge may outlive the arena or
  refer to a variable slot from another payload generation.

The production witness is a compiler loop fact set with `0 <= iv`,
`iv < trip`, and signed-32-bit bounds on `trip`. Relational projection must
derive `iv <= 2147483646`; the derived upper bound proves that scaled index
expressions cannot overflow their target address width. The 300-edge chain,
the three-edge negative cycle, and exact equality hidden behind 300 one-sided
edges are adversarial contract witnesses, not substitutes for this loop case.

Exact additive relations are owned by the private
`src/relation_algebra.c` component. One pointer-keyed endpoint registry and
one direct-edge index serve two deliberately different weighted closures:

- The **asserted closure** contains every accepted `lhs - rhs == offset`
  relation. Its immutable incident-edge lists let bounds queries validate a
  complete path before projecting range, integrality, or definedness. Union
  connectivity alone is insufficient: a path through `floor(x/d)` remains
  conditional until that intermediate expression is proven defined.
- The **total closure** contains only relations certified between total symbol
  endpoints by complementary unit-difference constraints. It is a compact,
  path-compressed forest keyed through the shared endpoint registry, so exact
  symbol differences remain independent of one-sided inequality fan-out.

`bounds_relation.c` exposes asserted components through a typed pull cursor,
not a proof callback. `bounds_range.c` proves the root defined before `begin`,
so a failed root proof performs no component allocation. The cursor grows its
entry array before its seen index, returns each unseen original endpoint before
adding or recording the pending edge offset, and waits for the caller to prove
that endpoint with equality projection disabled. Rejecting an endpoint skips
only that edge. The relation algebra remains immutable until cursor destroy
because the cursor borrows an incident-edge pointer.

A tracked successful walk reserves projection rows for the complete admitted
component before publishing any row. The cache stores separate component
offset, range, integer, and definedness completion columns. Range collection
stages each intrinsic interval, then projects and completes the column with one
row lookup. Integer and component-definedness publication is allocation-free
after the whole-component reserve; an independent scalar definedness result
may reserve one row. Consumers retain proof admission and transport mapping,
while the relation owner retains row layout, completion bits, and generation.

Both closures use the same iterative weighted-union/find implementation but
retain separate offset policies. Asserted links use two-limb signed magnitude
so reversing an `INT64_MIN` edge and composing representable graph-sized
chains cannot overflow. Total links preserve the previous checked `int64_t`
admission contract: an unrepresentable composition leaves that closure
unchanged and makes only the exact-symbol query unavailable. Adding an
asserted edge and certifying it total are separate operations because a later
reverse inequality may promote an edge that the asserted index already owns.

Endpoint and direct-edge lookup are expected O(1), insertion and table growth
are amortized O(1), and weighted operations are amortized inverse-Ackermann in
their participating endpoints. Defined asserted-component projection and
arena cloning are O(V+E). A clone deep-copies and relinks every retained edge;
no fact generation refers to edge storage owned by another arena. The
component reports added, unchanged, conflict, representability miss, invalid
topology, and allocation failure distinctly. Store mutation policy maps
insertion outcomes to contradiction, cache invalidation, and allocation state;
bounds query policy maps an invalid retained topology into active-query poison.
The component scans no context or arena state, uses no callbacks, and has no
recursive call edge.

`bounds_difference.c` owns the directed difference graph separately from the
exact relation algebra. It depends one-way on store mutation and exact-relation
APIs; neither owner calls back into difference processing. The graph stores
one-sided constraints and its own expected-O(1) directed-edge index.
Complementary symbol constraints remain in that graph for feasibility and also
certify the relation algebra's total closure; exact queries therefore do not
walk inequality adjacency. Arbitrary asserted equalities live only in the
relation algebra because their endpoints are not graph variables. Both owners
are fact-local and arena-owned. Incremental graph processing visits only the
affected difference component, never the context or arena.

The directed graph uses immutable arena-owned edge records, separate incoming
and outgoing adjacency heads, and append-stable variable indices. Adjacency,
feasibility, and worklist state live in a lazily allocated parallel table, so a
fact set without relational constraints retains no graph-variable payload.
Forks copy the variable and graph-variable tables plus the directed-edge hash
index while sharing only the immutable edge records; a new edge changes heads
and feasibility potentials in the candidate generation alone. Substitution
rebuilds graph constraints from the substituted expression facts, then
transfers symbol endpoints and congruences through the rebuilt graph. Thus no
edge contains a pointer to a variable slot from another generation.

Each graph variable carries a feasible potential for the constraints already
committed. Inserting an edge that violates those potentials starts an
incremental shortest-path worklist. All resulting improvements contain the new
edge; an improving path with at least as many edges as graph variables repeats
a vertex and therefore proves a negative cycle. The candidate is marked
contradictory before commit. There is no iteration or queue cap. The common
case of an already satisfied edge is O(1); otherwise feasibility and endpoint
closure are Bellman-Ford-like over the affected relation component, O(VE) in
the worst case, with O(V) operation-scoped scratch. Exact-edge index growth is
amortized O(1), and retained graph storage is O(V + E). Here `V` and `E` are
the variables and edges owned by one fact set, not total context or arena
state. Monotonic per-fact epochs mark queue membership, so starting a worklist
does not clear all `V` variable slots. Temporary work is restored before
return.

Checked overflow while composing a feasibility potential is a representation
failure: the public mutator rolls back, poisons the fact set, and returns
false. Endpoint projection is conservative at an unrepresentable `int64_t`
boundary, matching interval widening; other queued vertices are still
processed. Exact-forest offset overflow is distinct: the graph mutation is
representable and remains committed, while only the unrepresentable exact
composition returns unknown. Allocation and checked-size failures follow the
transactional rollback contract. A contradiction is semantic rather than
operational: it is committed and all queries return their established
unknown/no-result form.

`bench_relational_facts` measures the production witness through public APIs
and keeps every generated fact set alive so peak RSS exposes retained storage.
`--chain-edges N` batches a late-anchored N-edge chain and defaults to 100
retained fact sets, making the 300-to-600-edge CPU and RSS ratios reproducible.
The raw `my/facts-fix@106bbfd` result is the controlled baseline. A candidate is
a no-go if its median release CPU time or retained-RSS slope is more than 25%
above that baseline, or if doubling a late-anchored chain from 300 to 600 edges
uses more than 2.2x memory or 2.5x CPU. Correctness failures are an unconditional
no-go; a green build cannot override any contract witness.

This enables rules like:

- **Equality substitution**: when a symbol's bounds collapse to a point
  interval `[c, c]` (from `sym == c` assumption, or derived via
  `sym >= c` ∧ `sym <= c`), the rewriter replaces the symbol with integer
  `c` throughout the expression tree. This cascades through constant
  folding, collapsing `ceiling(M/256)` to `1` when `M == 256`, etc. Constant
  powers created by substitution fold into the product coefficient, so
  `floor(x/d)` with `d == 128` contains rational coefficient `1/128`, not a
  constant-base factor that only prints like the same rational. If the folded
  rational is not representable, simplification keeps the structural power
  without emitting an error. A zero base with negative exponent remains a
  domain error.
- `Mod(x, 32)` where `0 <= x < 32` → `x`
- `floor(x/64)` where `0 <= x < 64` → `0`
- `floor(x)` → constant when `floor(lo) == floor(hi)` (same for ceiling)
- `Mod(x, m)` bounds tightened to dividend's bounds when `0 <= x < m`
- `Mod(x, m)` → `x` when symbolic relations prove `m > 0`, `x >= 0`,
  and `x < m`
- `Mod(x, m)` upper bound tightened to `m - gcd(d, m)` when `x` is
  integer-valued and `d` is the gcd of its top-level integer coefficients
  (e.g. `Mod(4*a, 16)` in `[0, 12]` instead of `[0, 15]`).  The implementation
  computes `gcd(d, m)` directly, so an `INT64_MIN` coefficient never requires
  representing its `2^63` magnitude in `int64_t`.
- A symbol's finite interval and congruence narrow literal-`Mod` bounds to the
  extrema of reachable residues. Empty intersections are contradictions.
- `Max(1, expr)` where `expr >= 1` → `expr`

**Congruence-gated rewrites** (requires `Mod(sym, M) == R` assumption):

- `Mod(sym, m)` → `R % m` when `M % m == 0` (generalizes divisibility to
  nonzero remainders; for `R == 0` this gives `→ 0`)
- `floor(sym / m)` → `sym / m` when `M % m == 0` and `R % m == 0`
  (divisibility: the known congruence absorbs `m`)
- `Mod(c*sym, m)` → `0` when `m` divides `c * divisor(sym)`
- `floor(expr)` / `ceiling(expr)` → `expr` when `expr` is provably
  integer-valued using congruence (e.g., `floor(K/32)` → `K/32`
  when `Mod(K, 32) == 0`)
- `floor(a + (p/q)*sym + rest)` → `(p/q)*sym + floor(a + rest)` when
  `q/gcd(|p|,q)` divides sym's known modulus (the rational addend is
  integer per congruence and can be extracted from the floor)
- `c*Mod(A,m) - c*Mod(B,m)` → `0` when both original Mod operations are
  defined, their shared modulus is positive, and the cached exact-delta proof
  establishes `A == B`. Positive literal moduli additionally retain the
  congruence fallback for `A-B ≡ 0 (mod m)`.
- Opposite-coefficient `floor` or `ceiling` quotients with one positive integer
  denominator cancel when a bounded integer numerator shift stays in the same
  quotient bucket. One modular oracle checks the existing lower and upper
  boundary witnesses for `Mod(n,d) + delta` inside `[0,d)`. Its fallback uses
  `n == r (mod m)`, `m | d`, and the complete shift interval
  `-r <= delta < m-r`; `ceiling` uses the exact `-n`, `-delta` dual.
  Sign-proven `trunc` reaches the same machinery through its canonical `floor`
  or `ceiling` form. The oracle performs a fixed number of cached integer,
  range, residue, and divisibility queries, constructs no expressions, and
  cannot re-enter simplification.

**Bitwise-fact extraction and consumers**:

- `(sym & (sym - 1)) == 0` records `pow2_or_zero(sym)` and the interval fact
  `sym >= 0`. Combined with `sym > 0` or `sym >= 1`, this upgrades to
  `pow2_positive(sym)`.
- `(sym & mask) == 0`, where `mask` is an integer constant, marks all mask bits
  as known zero in `sym`.
- `(sym & mask) == mask` and `(sym | mask) == sym` mark all mask bits as known
  one in `sym`.
- `(sym | mask) == mask` marks all tracked low bits outside `mask` as known
  zero in `sym`.
- `sym ≡ r (mod 2^k)` reduces to exact known low `k` bits; conversely,
  contiguous known low zero bits imply divisibility by `2^k`.
- `ixs_check` uses these facts to prove mask equalities/inequalities and
  power-of-two predicates. Simplification should consume them only through
  conservative helpers such as `ixs_bounds_get_bitfacts` and
  `ixs_bounds_is_known_divisible`.

**Algebraic rewrites** (no bounds needed):

- `Mod(c1*t1 + ... + c, q)` → `Mod(c1*t1 + ... + c-r, q) + r`, where
  `g = gcd(q, |c1|, ...)`, `r` is the Euclidean residue of `c` modulo `g`,
  every `ti` is integer-valued, and `0 < r < g`. Including `q` in the gcd
  handles coefficients that do not individually divide the modulus.

**Bounds-gated algebraic rewrites**:

- `floor(c1*t1 + ... + r)` → `floor(c1*t1 + ...)` when each `ti` is a
  non-negative integer (verified via bounds), `0 < r < 1/lcm(denoms)`,
  so `r` is too small to shift the floor past an integer boundary.

**Interval propagation through powers, XOR, and Piecewise**:

The bounds engine propagates intervals through `IXS_MUL` nodes with
arbitrary numbers of factors and negative exponents (division by symbolic
expressions).  This enables proving `floor(A/D) = 0` when `A` has a
concrete upper bound and `D` has a symbolic lower bound that guarantees
`A/D < 1`.

- **Interval multiplication** (`iv_mul`): computes the tightest enclosing
  interval for `[a,b] * [c,d]` by evaluating all four corner products
  `{a*c, a*d, b*c, b*d}` and selecting the min/max.  Handles mixed-sign
  intervals correctly.
- **Integer powers** (`iv_pow`): positive exponents use checked
  exponentiation by squaring. Odd powers preserve endpoint order. Even powers
  select the nearer endpoint for the lower bound and the larger endpoint
  magnitude for the upper bound, with lower bound zero when the input crosses
  zero. `IXS_MUL` propagation accepts exponent magnitudes through 64; larger
  or zero exponents report unknown.
- **Interval reciprocal** (`iv_recip`): for a strictly positive or strictly
  negative interval `[a,b]`, returns `[1/b, 1/a]`. An infinite endpoint maps
  to zero on the corresponding side. An interval containing or touching zero
  reports unknown, including every negative power whose powered base interval
  crosses zero.
- **Bitwise XOR**: propagation requires every operand to be provably integer
  and nonnegative. Finite upper bounds determine the possible high-bit span;
  operand known bits then tighten the result's required and possible bits. If
  any nonnegative operand is unbounded above, the result is `[0,+inf)`.
  A negative or sign-unknown operand reports unknown. Low-64-bit facts never
  impose a signed or unsigned machine width on the expression.
- **Piecewise**: propagation follows first-match semantics. Each reachable
  branch is evaluated in a fork containing its condition and the negations of
  all earlier conditions; dead and shadowed branches are ignored. All
  reachable conditions and values must be proven defined, every feasible
  input must be covered, and every reachable value must have a range. The
  result is the hull of those branch ranges. Otherwise the query reports
  unknown. Nested range partitioning is capped at 32 Piecewise levels and
  1024 cases per node.
- **Overflow widening** (`iv_endpoint_widen`): when `ixs_rat_mul` overflows
  during interval arithmetic, the endpoint is widened to `INT64_MIN` or
  `INT64_MAX` (representing −∞ or +∞) based on the sign of the factors.
  Actual interval endpoints also carry explicit infinity flags, so finite
  values equal to `INT64_MIN` or `INT64_MAX` remain distinguishable from
  unbounded sides.
  Power and reciprocal endpoints use the same directional rule: a failed
  lower endpoint widens down, while a failed upper endpoint widens up. This
  trades precision for soundness: the interval remains an over-approximation.
- **Public range query** (`ixs_range`, Python `Context.range`): exposes the
  same bounds-only interval query used by entailment checks.  It returns
  exact rational endpoints for the inferred inclusive interval, with
  unbounded sides represented explicitly.  This is not a general optimizer or
  constraint solver: if propagation cannot derive an interval, the query
  reports unknown; if independent intervals lose correlations, the returned
  interval is conservative rather than the mathematical image of the full
  assumption set. Integer-coefficient positive-literal `Mod` chains in one
  `ADD` are grouped by their exact structurally total integer representative.
  Each subgroup interval is intersected with its proven gcd congruence before
  independent groups are summed; fractional coefficients, partial or
  noninteger representatives, symbolic moduli, and distinct representatives
  stay independent. The grouping pass is expected O(n) in `ADD` terms and
  uses O(k) query-local scratch for k candidate terms. It never scans retained
  context state. There is no parallel integer-range contract. Consumers
  combine this canonical range with the definedness and integer-valued proof
  queries; internal exact proofs refine the same interval representation
  rather than materializing a second result type.
- **Public predicate and equivalence queries** (`ixs_check_predicate_facts`,
  `ixs_equivalent_facts`): equivalence owns one public proof contract. General
  predicate checking may inspect at most 4096 nodes and enumerate at most 64
  Cartesian points across at most 8 finite-range symbols. Those fixed limits
  bound one private fallback; there is no caller-budgeted finite-domain query
  contract.
- **Public power-of-two query** (`ixs_get_pow2_fact`, Python
  `Context.pow2_fact`): exposes the semantic pow2 lattice (`unknown`,
  `or_zero`, `positive`). It uses both direct bitfacts and exact integer
  intervals inferred for arithmetic expressions. Detected contradictory
  assumptions return unknown.
- **Public known-bit query** (`ixs_get_known_bits_facts`, Python
  `Context.known_bits`, C++ `Facts::get_known_bits`): exposes the sound low-64
  `known_zero`, `known_one`, and pow2 facts from a reusable fact set. A valid
  query with no information returns true with zero masks; invalid input,
  contradictory facts, or OOM returns false and initializes the output to that
  same no-information value. The query first proves the expression integer-
  valued, so a rational interval cannot be misread as integer bits. Interval,
  `ADD`, positive power-of-two `MUL`, floor division, `Mod`, and bitwise
  propagation never infer anything about source bits above bit 63.
- **Public congruence queries** (`ixs_get_symbol_congruence_facts`,
  `ixs_check_congruent_facts`, Python `Context.symbol_congruence` and
  `Context.congruent`, C++ `Facts::get_symbol_congruence` and
  `Facts::check_congruent`): the first API exports only the stored positive
  modulus and normalized residue for a symbol. It does not compute a strongest
  congruence for arbitrary expressions. The second answers one requested
  modulus/residue query using exact intervals, known low bits, stored symbol
  facts, and bounded `ADD`/`MUL` propagation at that modulus. Negative moduli
  and residues normalize without signed negation, including the `2^63`
  magnitude of `INT64_MIN`; modulus zero emits a diagnostic and returns
  `UNKNOWN`. Known conflicting residues return `FALSE`, incomplete evidence
  returns `UNKNOWN`, and contradictory facts never establish a result.
- **Public predicate-tree checking** (`ixs_check_predicate_facts`, Python
  `Context.check_predicate`, C++ `Facts::check_predicate`): accepts only nodes
  classified by `ixs_node_is_pred`. It simplifies once against the reusable
  facts, then passes the rewritten root to the same caller-layer projector used
  by scalar and batch fact simplification. The projector evaluates `AND`, `OR`,
  and `NOT` with conservative tri-state truth tables, then applies the bounded
  finite-domain fallback only when the root remains unknown. It never re-enters
  per-node simplification. `AND` is true only when every child is true and false
  when any child is false; `OR` is true when any child is true and false only
  when every child is false; `NOT` inverts true and false. Predicate-valued
  `Piecewise` nodes that do not collapse during fact-backed simplification
  remain unknown. Numeric bitwise `AND`/`OR` nodes are rejected with a
  `predicate:` diagnostic rather than interpreted as boolean trees. The
  evaluator is iterative and memoized over the predicate DAG using query-arena
  storage; allocation failure returns unknown.

  Fact simplification replaces a projected root with canonical `0` or `1` only
  when every enumerated source valuation agrees. A varying result, a partial
  eager operand, transport failure, or a domain beyond the fixed finite limits
  leaves the rewritten predicate intact. Scalar and batch simplification use
  the same one-shot root operation.

  An otherwise unknown binary `OR` also admits one bounded implication step.
  An explicit `NOT(A)` disjunct supplies `A`; a comparison disjunct supplies
  its complementary comparison, covering the canonical form of `NOT(CMP)`
  for all six comparison operators. The query first proves the complete `OR`
  defined and integer-valued because the operators are eager. It then forks
  the current facts, ingests the antecedent without publishing its local
  closure, and evaluates the other disjunct once without recursively invoking
  implication. A binary `OR` therefore creates at most two local forks. Each
  fork is linear in the retained fact state, shares the enclosing query guard
  and failure transport, and is discarded before returning. Unsupported or
  partial antecedents, insufficient facts, a contradictory public fact set,
  allocation failure, and proof-limit exhaustion return `UNKNOWN`; local
  assumption diagnostics do not escape the query.
- **Total fact-backed equivalence** (`ixs_equivalent_facts`, Python
  `Context.equivalent`, C++ `Facts::equivalent`): requires both operands to be
  defined over every valuation admitted by the incoming facts before pointer
  identity can prove equality. It then tries fact-backed simplification of the
  difference, expansion followed by simplification under the shared fact
  environment, flattened order-independent matching of predicate `AND`/`OR`
  terms. Aligned ordered comparisons normalize to integer residual cuts
  against zero. Equal cut thresholds prove equality;
  unequal thresholds prove equality only when the intervening integer gap is
  unreachable by the residual's range or congruence. This includes strict to
  non-strict normalization such as `x < 8` versus `x <= 7` without assuming a
  machine width. If that single-residue proof is insufficient, the query walks
  only the two residual expression DAGs and collects the congruence moduli
  attached to their symbols. For each candidate `d > 1`, `< 0` and `>= 0` use
  the exact `floor(residual/d)` form, while `<= 0` and `> 0` use
  `ceiling(residual/d)`. Fact-backed simplification can then canonicalize a
  bounded union of reachable residue classes. The iterative walk visits each
  query node once and uses growable, expected-O(1) candidate and node sets; it
  has no semantic depth, visit, or candidate-count cutoff and never scans
  unrelated context state. After those ordered proofs miss, comparisons with
  the same canonical operator and right operand are equal when normalized
  exact-value projection proves their numeric residual delta is zero. Any
  nonzero or unproved delta remains unknown because unequal
  residuals can still induce the same predicate over a restricted fact domain.

  A predicate equality whose normalized zero-sum ADD
  contains a non-unit scaled Mod first partitions that ADD into exact positive
  and negative sides. One with a single unit Piecewise term instead isolates
  that term and rebuilds its peer once, without distributing into the arms.
  Both paths use O(T) work and O(T) query scratch before running the same
  ordinary equivalence proof. Other predicate equalities retain their existing
  entry path.

  Equivalence composes those exact proofs through a narrow set of canonical
  numeric contexts. Entry is restricted to canonical two-term `floor`/`Mod`
  groups and production-backed binary XORs. A query-local iterative worklist
  pairs `ADD`, `MUL`, `floor`, and `ceil` DAG nodes with expected O(N)
  insertion and lookup work and O(N) query state; invoked child proof rules
  retain their own documented bounds. Canonical ADDs with different arity use
  exact relation partitioning only when removing common terms strictly reduces
  the relation. Affine `floor` and `ceil` contexts may move residuals into their
  arguments only when each residual is proven integer-valued.

  Immediate canonical additive-row mechanics are owned by the private
  `src/additive_row.c` component. Allocation-free recognizers recover a single
  unit equation or two opposite unit terms. The cached constant-drop transform
  rebuilds only the immediate sorted terms. A shared affine-round split finds
  one coefficient-one `floor` or `ceil` term and constructs its exact residual;
  both signed division recognition and affine context equivalence use that
  operation. Exact relation partitioning first constructs `lhs-rhs`, then
  separates its positive and negative coefficients without disturbing
  canonical term order; an `INT64_MIN` constant reverses the endpoints so its
  stored offset remains representable. Arithmetic that cannot be represented
  has an explicit `UNREPRESENTABLE` result, allocation failure is OOM, and no
  component operation performs a bounds query or changes definedness policy.
  The same component owns the neutral Euclidean row view used by simplification
  and proof algebra. It borrows canonical ADD terms, extracts one exponent-one
  `floor`, `ceil`, or `Mod` atom with its exact scale, and partitions exact
  quotient products into numerator and denominator. It performs no positivity,
  integer-domain, totality, poison, or signed-truncation admission; those remain
  caller policy.
  Recognition and cache hits are O(1), while constant-drop cache misses,
  affine-round splitting, Euclidean product partitioning, and relation sign
  partitioning are O(T).
  Constructing the relation residual inherits the simplifier's O(T^2) worst
  case; partitioning uses O(T) query scratch.

  Signed truncating division is implemented by the private
  `src/division_algebra.c` component around the exact relation `N = D*Q + R`.
  Its exact quotient-parts parser is the neutral `additive_row.c` operation
  shared with positive-divisor quotient algebra and reports representability
  misses separately from allocation.
  A certificate admits direct `trunc(N/D)`, a `floor` or `ceil` whose argument
  sign makes it truncation, or the canonical two-arm `floor`/`ceil` Piecewise
  protocol. The Piecewise matcher accepts only the complete same-sign guard or
  the exact clause selected by a proven denominator sign. Rational scaling of
  a zero comparison is removed before matching; strict numerator cuts and
  extra, overlapping, or non-exhaustive predicates remain unsupported. Guard
  matching is finite and structural and adds no equivalence recursion edge.

  Every certificate proves the original round, quotient argument, numerator,
  and denominator defined, and proves `N` and `D` integer-valued. Proof
  projection also receives the pre-normalized source roots and requires those
  roots defined over the complete incoming fact domain. A normalized root may
  therefore expose a relation for simplification, but cannot erase a source
  partiality obligation. An independently partial sibling blocks an otherwise
  valid local certificate; the projector does not weaken this to per-candidate
  definedness. For known signs the component constructs only the needed branch
  of the signed remainder; otherwise it uses
  `Piecewise((Mod(N,abs(D)), N >= 0), (-Mod(-N,abs(D)), True))`. Optional
  unrepresentable construction is a local candidate miss; if no candidate
  matches, the aggregate result reports that miss to the caller. Invalid
  state, proof limits, and OOM retain distinct query outcomes.

  Projection discovers candidates with an iterative, growable reachable-DAG
  walk. Outermost multi-substitution then removes every candidate nested below
  another candidate; this global filter is required for shared diamonds because
  replacement expressions are not recursively substituted. Candidate storage
  has no semantic cap. Fact simplification accepts a projected form only when
  its reachable node count strictly decreases. Certificate construction adds
  no rounding operator and removes the selected outer round, while nested
  rounds already present in `N` or `D` remain shared. The immediate
  remainder-range path admits one direct `trunc` or canonical truncating
  Piecewise atom in an ADD, reconstructs its exact integer shift once, and
  intersects the signed radius implied by `D`.
  Candidate discovery, descendant filtering, and cost walks are expected
  O(N + E + C) for distinct nodes, edges, and candidates. Substitution lookup
  and DAG traversal have the same bound, while canonical ADD/MUL reconstruction
  retains the simplifier's O(children^2) worst case. The 1050-candidate proof
  regression guards the growable path and absence of a semantic cap. Immediate
  range shape recognition is O(T + F); its one exact-shift reconstruction
  inherits the simplifier's O(T^2) worst case before the documented bounds
  queries. No operation scans retained context state or uses expression-depth
  recursion.

  Positive-divisor quotient/remainder equality is implemented by the private
  `src/quotient_algebra.c` component. It constructs and simplifies `lhs-rhs`
  once, then borrows a canonical `ADD` as a sorted sparse row; a non-`ADD`
  operand is a synthetic one-term row. An eligible row term contains exactly
  one direct `Mod` or `floor(n/d)` factor with exponent one. Removing that
  factor structurally produces its exact scale without dividing by the atom
  and therefore without inventing a nonzero precondition. Rational pivot
  scales divide the row by scaling its existing coefficients in one rebuild,
  preserving sparse form without internal expansion. Row borrowing, atom
  extraction, scale construction, and exact quotient partitioning come from
  the neutral additive-row plan; quotient algebra retains every proof and
  status decision.

  Every admitted atom requires `n` and `d` to be defined and integer-valued
  and `d > 0`. Isolating `Mod(n,d) = r` succeeds only when `r` is the unique
  Euclidean remainder: `r` is defined and integer-valued, `0 <= r < d`, and
  `n-r` is divisible by `d`. Isolating `floor(n/d) = q` instead requires `q`
  integer-valued and `n-d*q` in `[0,d)`. Exact closure may replace all direct
  floor atoms in one row by `(n-Mod(n,d))/d`. Congruence closure may replace a
  direct `c*Mod(n,m)` by `c*n` modulo a target `d` only after proving
  `(c*m)/d` integer-valued; unchecked nested occurrences remain opaque.

  Fact-backed simplification applies the same integer-ring law to a genuine
  product under a positive literal modulus. It first proves the coefficient
  and every factor integer-valued and every factor defined, then reduces each
  factor independently and rebuilds only when a residue becomes simpler.
  Inside an additive residue, `c*Mod(n,m)` becomes `c*n` modulo `d` when
  `d/gcd(m,d)` divides `c`; this avoids forming the potentially overflowing
  product `c*m`. Single-factor sign and scale carriers keep their established
  normal forms. Equivalence invokes this fact-backed simplifier, so ordinary
  simplification and proof queries share the same product reduction rather
  than recognizing a particular subtraction or modulus.

  Canonical mixed-radix ranges use the same row. Each positive integer digit
  `c*Mod(n,m)` contributes `[0,c*(m-1)]`; the ordinary interval engine bounds
  the residual once, and the symbolic upper bound is simplified as
  `upper-d < 0`. The shared modular bucket oracle checks those already-built
  lower and upper witnesses, so quotient algebra no longer owns a second
  `[0,d)` policy. Thus the rule is not keyed to a particular radix, literal
  divisor, or term count. A separate `floor(expr/d) == 0` fact remains an
  independent algebraic certificate when interval correlation is
  insufficient. This proves, for example,
  `Mod(4*x+Mod(seed,4),32) == 4*Mod(x,8)+Mod(seed,4)` when the required domain
  and range facts hold, while a missing upper bound remains unknown.

  One solve invocation tries Mod pivots before floor pivots and admits at most
  four isolated row equations. Projection, congruence reduction, and radix
  transfer have independent four-item caps. Canonical order may therefore
  return `UNKNOWN` when a useful atom is fifth; no cap can establish equality.
  With `T` immediate row terms, the component's intrinsic row passes are O(T)
  with a fixed pass count. It invokes no expansion, adds no recursive call
  edge, scans no retained context state, and never solves a projected row.
  Existing simplification, substitution, and bounds oracles retain their
  documented reachable-DAG costs; the inherited rewrite follows expression
  depth recursively. Combined scratch is O(N+T) for reachable DAG size `N`.
  Exhausted work, proof-cycle or
  nested-query limits, and unrepresentable optional arithmetic are a local
  `UNKNOWN` and do not suppress independent context or low-bit proofs; invalid
  input and OOM remain query failures. Truncation, Piecewise selection, context
  composition, predicate logic, and power-of-two low-bit normalization remain
  separate systems with their own contracts.

  Production-backed binary numeric XOR nodes pair pointer-identical arguments
  first, then use bounded semantic child proofs. The matcher is O(A^2) in its
  admitted arity A=2; wider canonical XORs retain the existing exact and
  low-bit strategies instead of starting quadratic semantic matching. Only
  complete child proofs establish the outer equality; failed children, cycles,
  exhausted child-proof depth, partial expressions, and allocation failure
  remain `UNKNOWN`. This is not generic congruence for extrema, Piecewise,
  truncation, or predicates. Boolean AND/OR keep their dedicated predicate-tree
  matcher.

  After all existing arithmetic, projection, expansion, and low-bit strategies
  miss, equivalence has one bounded Piecewise fallback. Exactly one simplified
  operand must be a root Piecewise with at most 16 arms; the peer and each
  reachable arm must be complete Piecewise-free DAGs of at most 64 nodes. One
  affine integer-symbol selector must have a complete incoming interval and
  congruence domain of at most 64 points. A fixed 64-bit mask applies affine
  guards in first-match order, so repeated equality guards do not count twice
  and distinct exclusions can prove that a finite congruent domain is
  exhausted. Each reachable arm must select exactly one remaining point. The
  proof substitutes that selector point into only the arm and peer, then uses
  one existing bounded child proof; it never substitutes a Piecewise through a
  containing operand or forks the fact table. Equality is `TRUE` only when all
  reachable arms prove equal and no selector point remains uncovered.

  For `C <= 16` arms, `P <= 64` selector points, and admitted operand size
  `N <= 64`, guard partitioning is O(C*P), the fixed-stack admission walk is
  O(N^2), and at most C bounded arm proofs operate on the admitted DAGs.
  Wider domains, multi-point arms, nested or non-root Piecewise structure,
  non-affine or overflowing guards, duplicate coverage gaps, partial
  expressions, uncovered points, child-proof exhaustion, and allocation
  failure remain `UNKNOWN`. This is a local first-match proof, not generic
  finite-domain equivalence, and it adds no context-wide scan.

  `bounds_modular.c` implements the following exact strategy.
  Its quotient-bucket oracle consumes existing lower and upper boundary
  witnesses. It performs no construction or simplification and returns only
  match, no-match, OOM, or query-limit status. Both ADD cancellation and
  quotient algebra use this boundary, while exact paired-Mod projection shares
  its stride/residue window calculation.

  Constant-difference and equivalence queries pair equally scaled,
  opposite-sign `Mod(A, D)` terms in a normalized residual. They first prove
  the exact difference between the two dividends. For a positive literal `D`,
  each Mod result gets a finite integer enclosure tightened to its structural
  congruence; the projection succeeds only when the dividend difference's
  residue class has exactly one representable member in the result-difference
  enclosure. For a shared dynamic `D`, the existing stride-bucket proof makes
  the Mod difference equal to the dividend difference when positivity and
  no-wrap evidence are available. The scaled Mod delta and the remaining
  residual are then combined with checked `int64_t` arithmetic. This models
  mathematical Mod composition used by fixed-width wrappers; it does not add
  machine-overflow semantics.

  The ADD simplifier calls the same cached modular query for
  opposite-coefficient outer Mod nodes. The query checks definedness on both
  original operations, proves the shared modulus positive, and asks the exact
  delta engine whether the dividends are equal. A positive literal modulus may
  also use the established congruence fallback for a nonzero exact delta. This
  path performs no general simplification and preserves central
  invalid/OOM/limited transport.

  Paired-Mod projection uses a growable query-local proof stack. Every child
  enters a Mod dividend or removes one matched Mod pair from a canonical ADD,
  so progress is structural and there is no separate 32-level, 4096-visit, or
  fixed-term semantic cutoff. Allocation or checked-size failure returns
  unknown. For `T` terms at one level, candidate matching is O(T^2) in the
  worst case and residual construction is O(T); it visits only the queried
  expression DAG and exact residuals use the weighted equality forest rather
  than inequality adjacency or context-wide scans.

  After those exact strategies miss, the shared `src/low_bits_algebra.c`
  component handles two original outer `Mod` nodes with the same positive,
  representable power-of-two literal modulus. The bounds adapter proves the
  original outer operations and both original dividends defined and
  integer-valued over the complete fact domain; normalized roots never replace
  those source obligations. The component then projects the dividends through
  the typed ring `Z/(2^k)`. In equality mode it propagates through
  integer-coefficient `ADD`, integer-coefficient `MUL` with only positive
  powers, numeric `XOR`/`AND`/`OR`, and a nested literal `Mod` whose modulus is
  divisible by the outer modulus.
  Every supported node and immediate child is independently re-proved total
  and integer-valued, and the adapter re-proves both projected roots. Other
  nodes, including rounding,
  `Piecewise`, extrema, predicates, rational coefficients, reciprocal powers,
  and dynamic or incompatible `Mod`, remain opaque. Pointer-identical opaque
  subtrees can still participate in a successful exact proof. The rule sees
  the original pair because fact-backed simplification can remove only one of
  the matching outer operations.

  The Mod simplifier uses the same engine in residue mode. Only XOR/AND/OR
  propagate in that mode; the caller maps every other proven-integer subtree
  to its residue, then uses the ordinary canonical constructors to rebuild.
  Equality and simplification therefore share admission, traversal, memo,
  cycle detection, and transport behavior rather than maintaining separate
  bit algebras.

  Low-bit normalization is iterative and uses a growable query-local,
  expected-O(1) pointer memo whose temporary parent links replace a recursive
  stack. It visits each supported DAG node once, with expected O(nodes + edges)
  walk work and no context-wide scan or semantic node/depth cutoff. Rebuilding
  is scoped to one supported parent: every immediate child, including an
  unchanged opaque child, is a substitution target. A hash-consed inner `Mod`
  therefore cannot leak through an opaque occurrence elsewhere in the DAG.
  Canonical rebuilding inherits the simplifier's O(children^2) worst case.
  Query limits and OOM remain distinct transport statuses; invalid bounds
  state and diagnostic constructor overflow remain `INVALID`. The total
  projector itself has no representability miss. Failed sufficient proofs
  return `UNKNOWN`. The rule can establish only `TRUE`; it never derives
  `FALSE` from low-bit normalization.

  Congruence is deliberately not a generic equality rule: a divisible
  residual delta does not prove arbitrary comparisons or `x == 0`. A nonzero
  exact difference or predicates with opposite proven truth values return
  `FALSE`. An exact zero range for the normalized difference, including one
  obtained from the weighted equality forest, returns `TRUE`; other failed
  sufficient proofs return `UNKNOWN`. Contradictory facts never prove
  equivalence. Recursive predicate-shape comparison has
  depth 32, 4096 proof visits, and at most 1024 flattened terms; stride
  inference uses the congruence depth limit and makes one structural pass over
  the visited expression. Limits reached after a proof strategy starts and
  allocation failures remain live query failures with diagnostics. This API
  is not an unbounded theorem prover.
- **Generic exact-integer projection**: fact-backed rewriting asks the bounds
  solver whether each normalized result has one exact `int64_t` value. The
  lower query consumes normalized nodes and never calls the simplifier. It
  combines exact point ranges, complete low-64 bitfacts, additive rows over the
  weighted relation forest, and paired-Mod projection. Complete bitfacts are
  converted to signed two's-complement values without implementation-defined
  unsigned-to-signed casts. The rewrite memo projects each input DAG node once,
  while interval and bitfacts work reuse the active central query cache. Scalar
  and batch simplification use the same path. A successful projection is a
  poison refinement, so it need only agree where the source is defined.
  Contradictory fact domains still bypass rewriting rather than proving values
  vacuously. OOM, invalid internal state, query limits, and unrepresentable
  integer results remain distinct failures.
- **Narrow fact-backed algebra helpers** (`ixs_affine_decompose_facts` and
  `ixs_split_additive_constant_facts`): prove definedness over the complete
  incoming fact domain, then simplify, expand, and simplify again in that same
  environment. Additive constants must fit `int64_t`; affine coefficients may
  be exact rational nodes. Affine
  decomposition accepts only one symbol and rejects any nonlinear occurrence
  or residual reference to it. A finite difference is ordinary composition:
  substitute `symbol + step`, subtract the source, expand when desired, then
  simplify with the same facts. Unsupported shapes, undefined partitions,
  contradictory facts, representation overflow, and bounded-walk or expansion
  limits fail conservatively. These helpers do not add relational, polyhedral,
  or SMT reasoning.
- **Public integrality queries**: `ixs_node_is_integer_valued` is a
  conservative structural test. It rejects negative powers and rational
  coefficients without consulting facts. `ixs_check_integer_valued` and
  `ixs_check_integer_valued_facts` add interval and congruence reasoning, so
  `K/32` is proven integral under `Mod(K, 32) == 0`. A `Piecewise` is proven
  integral only when every branch not proven unreachable has an integral
  value. `Mod(A, D)` applies the same fact-backed proof to both
  operands, so a structurally rational but proven-integral dividend remains
  integral through nested remainders. This says nothing about the operation's
  domain: positivity of `D` is still a separate definedness obligation. `TRUE`
  and `FALSE` are universal proofs; a failed sufficient proof is `UNKNOWN`,
  while an exact noninteger rational point may return `FALSE`.
- **Public definedness queries** (`ixs_check_defined`,
  `ixs_check_defined_facts`, Python `Context.defined`, C++
  `Expr::check_defined` and `Facts::check_defined`): prove domain safety for
  the complete incoming fact domain. Arithmetic and predicate nodes require
  every evaluated child to be defined. A negative `MUL` exponent additionally
  requires its base to be nonzero, and `Mod(a, b)` requires `b > 0`, matching
  the constructor contract. `TRUE` means every feasible valuation is defined;
  `FALSE` means every feasible valuation is necessarily undefined; mixed
  domains, insufficient facts, unsupported reasoning, invalid input, detected
  contradiction, and OOM return `UNKNOWN`.

  Expression ranges, including point ranges derived from equality assumptions,
  constrain values only where their expression is defined. They never prove
  definedness by themselves or bypass structural child and operation-domain
  checks. Thus a range for `floor(x/d)` does not discharge the required proof
  that `d != 0`; an independent divisor fact is still required.

  `Piecewise` follows first-match semantics. Conditions are checked before
  their values. Branch `i` is evaluated in a fork containing its condition and
  the negations of all earlier conditions, while the sibling continuation is
  refined only by the new negated condition. Infeasible branches are ignored.
  A final true condition covers the remaining domain; otherwise a feasible
  remainder is an undefined partition. Defined and undefined partitions mix to
  `UNKNOWN`, so an undefined dead or shadowed branch cannot poison the result
  and a partially uncovered expression cannot be reported as `FALSE` unless
  the whole feasible domain is uncovered.

  Ordinary nodes use per-environment memoized iterative walks with a query-wide
  budget of 8192 node visits, a 1024-frame explicit stack, and a 16384-slot
  memo table. Piecewise fact environments nest at most 32 levels and share the
  same visit budget. Interval guard queries are attempted only for subgraphs
  within 64 levels and 4096 local walk steps. Their temporary interval cache is
  the smallest power-of-two table from 32 through 8192 with at least two slots
  per local walk step. Reaching any limit returns `UNKNOWN`.
- **Public divisibility query** (`ixs_check_divisible_facts`, Python
  `Context.divisible`, C++ `Facts::check_divisible`): first proves that the
  expression is integer-valued, then uses exact values, congruences, and known
  low-zero bits. Exact nonmultiples return `FALSE`; incomplete evidence returns
  `UNKNOWN`. The modulus must be nonzero. Negative moduli use their unsigned
  magnitude, including the `2^63` magnitude of `INT64_MIN`, so normalization
  cannot overflow.
- **Exact quotient construction** (`ixs_try_exact_divide_facts`, Python
  `Context.try_exact_divide`, C++ `Facts::try_exact_divide`): first simplifies
  the expression in the supplied fact domain, then reuses the same divisibility
  proof and returns a canonical expanded quotient only after that proof
  succeeds. A conclusive result also requires the original input to be defined
  over the complete fact domain, so simplification cannot erase uncovered or
  undefined partitions. Its result separates
  `PROVEN`, proven `NOT_EXACT`, insufficient or contradictory `UNKNOWN`, and
  domain/OOM `ERROR`. Only `PROVEN` carries a quotient. Negative divisors
  preserve quotient sign; `INT64_MIN` is handled without taking its signed
  magnitude. Every `ERROR` reached through a valid fact set appends a session
  diagnostic. Structural numerator/denominator partitioning remains an
  internal helper for Trunc remainder and exact equivalence proofs. It is not a
  public algebra query because decomposition alone carries no definedness,
  integrality, or nonzero-denominator proof.
- **Public fact sets** (`ixs_facts`, Python `Facts`): reusable, session-owned
  proof contexts for callers that carry facts through IR rewrites instead of
  re-encoding everything as predicates.  A fact set accepts predicate facts,
  explicit expression ranges, affine range transfer (`scale*base + offset`),
  and substitution transfer. `Context.range(..., facts=f)`,
  `Context.check(..., facts=f)`, `Context.integer_valued(..., facts=f)`,
  `Context.defined(..., facts=f)`, `Context.divisible(..., facts=f)`, and
  `Context.pow2_fact(..., facts=f)` query these facts directly before relying
  on structural interval propagation. `Expr.simplify(facts=f)` and
  `Context.simplify_batch(..., facts=f)` run the rewrite engine directly
  against the same stored bounds. Successful queries may populate sound
  caches but do not weaken or consume the fact set. Detected contradictory
  facts leave simplification results unchanged; they never enable rewriting
  from an empty domain.
- **Fact substitution transfer** (`ixs_facts_substitute_multi`, Python
  `Facts.subs(mapping)`, C++ `Facts::substitute_multi`): applies all target
  replacements simultaneously. Replacements are not traversed, overlapping
  substitutions such as `{x -> y, y -> z}` produce facts for `y` and `z`, and
  the first entry wins when the C/C++ arrays repeat a target. Unchanged source
  facts and all pre-existing destination facts are merged. A direct symbol
  alias transfers the complete symbol record. For an integer affine
  replacement `a*K+b`, ranges are inverted when their exact rational bounds
  remain representable, congruences are reduced by `gcd(a, modulus)`, a
  contiguous known-low-bit prefix is treated as a congruence, and power-of-two
  state transfers only for `b == 0` with positive power-of-two `a`. Thus
  `8 | y` transferred through `y -> 2*K` proves `4 | K`, not `8 | K`.
  Transferred ranges and nonzero constraints remain attached to the complete
  substituted expression even when it is nonlinear; no symbol record is
  guessed for unsupported congruence or bit facts. In-place transfer is additive:
  original facts count as pre-existing destination facts. Validation or OOM
  failure retains the old payload but poisons the destination, preventing
  queries from observing a partially transferred set.

The `IXS_MUL` propagation rule in `bounds_get_propagated`:

```
MUL(coeff, f1^e1, f2^e2, ...) where 0 < abs(ei) <= 64:
  result = interval(coeff)
  for each factor fi:
    powered = iv_pow(bounds(fi), abs(ei))
    if ei < 0: powered = iv_recip(powered)
    result = iv_mul(result, powered)
```

Example: `floor(x / (128*K))` with `x ∈ [0,127], K ≥ 1`.
Internal representation is `floor(MUL(1/128, x^1, K^-1))`.
Propagation: `[1/128, 1/128] * [0, 127] * iv_recip([1, +inf))`
= `[0, 127/128] * [0, 1]` = `[0, 127/128]`.
Then `floor([0, 127/128]) = [0, 0]`, collapsing to constant `0`.

**Scope boundary**: interval propagation outside the admitted unit-difference
graph remains non-relational. For
`floor(x/K)` with `x < K-1, K >= 2`, the bounds engine sees
`x ∈ [0, INT64_MAX]` and `K ∈ [2, INT64_MAX]` independently, so `x/K`
has an unbounded interval. Targeted rules can query normalized comparisons for
specific proofs such as `0 <= x < K` in `Mod(x,K)` and same-bucket floor
differences; arbitrary cross-variable interval projection remains out of
scope.
