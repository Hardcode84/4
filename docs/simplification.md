# Simplification Engine

[Design index](DESIGN.md)

Simplification is **table-driven**. Each node type has an ordered array of
`ixs_rule` entries (function pointer, name, needs-bounds flag). The
`try_rules()` dispatch walks the array, tries each rule, records an
`IXS_STATS` hit when one fires, and returns. Rules that require bounds
are skipped when `bnds == NULL`.

Each `simp_*` constructor (e.g., `simp_floor`, `simp_mod`) applies the
fast pre-checks (sentinel propagation, const fold, identity) directly,
constructs the node, then calls `try_rules(ctx, NULL, node, *_rules, ...)`.
For the top-down rewrite pass, each `simp_*_bnds` variant takes an
optional `ixs_bounds *` and calls `try_rules(ctx, bnds, ...)` so
bounds-dependent rules also fire. `rewrite_impl` is just:
```c
case IXS_FLOOR:
    return simp_floor_bnds(ctx, bnds, rewrite(ctx, arg, ...));
case IXS_TRUNC:
    return simp_trunc_bnds(ctx, bnds, rewrite(ctx, arg, ...));
```
There is one rule table per type, used by both construction and rewriting.

All producers use the same canonical constructors. There is no strict variant
and no synthetic Piecewise domain carrier. Import and deserialization validate
their external representation, then preserve an accepted DAG's structural
semantics; rebuilding or simplifying it uses the same refinement contract.

**Termination guarantee**: The top-down rewrite pass in `ixs_simplify()` runs
a fixed-point loop with a configurable iteration limit (default 64). Each
iteration applies rules bottom-up over the DAG. Most rules are
size-reducing: they either reduce the number of nodes or replace a complex
node with a simpler one (e.g., `floor(3/2)` → `1`, `Mod(x, m)` where
`0 <= x < m` → `x`). A few normalization rules (e.g., comparison
`a > b` → `(a - b) > 0`) may temporarily increase size but enable subsequent
reductions. The iteration limit is the safety net that guarantees termination
regardless. If the limit is reached without convergence, the current best
result is returned and an error is appended to the error list (not sentinel —
the result is still valid, just possibly not fully simplified).

Scalar and batch simplification add an open-addressed cache above the per-walk
direct-mapped memo. It keys rewritten subtrees by interned node identity and
grows at 75% occupancy. Scalar caches span one root's fixed-point iterations;
batch caches also span roots. One cache serves one immutable fact context only.
Piecewise branch forks use independent local memos, so branch facts cannot
escape into siblings or later roots. Initial scalar-cache OOM falls back to the
direct memo. Batch-cache OOM preserves the atomic contract: every output
becomes NULL.
Growth is deferred until a root rewrite returns, outside nested scratch-arena
marks; rule-local restores cannot invalidate cache storage.

## 4.1 Constant Folding

Any operation on constants is immediately evaluated:

- `floor(7/2)` → `3`
- `Mod(17, 5)` → `2`
- `Max(3, 7)` → `7`
- `ceiling(4)` → `4` (floor/ceil of integer = identity)
- `xor(5, 3)` → `6`
- `3 > 2` → `True`

## 4.2 Canonical Form — Add

`IXS_ADD` stores `coeff + Σ ci * ti` where:

- `coeff` is a rational constant (possibly 0)
- Each `ti` is a non-ADD, non-constant node
- Each `ci` is a nonzero rational coefficient
- Terms sorted by canonical order on `ti`

Construction rules:

- `ADD(... + ADD(c + Σ di*ui) ...)` → flatten: merge `c` into coeff, merge
  all `di*ui` terms
- `ADD(... + k * ADD(c + Σ di*ui) ...)` → distribute `k` and flatten
  (enables `(x+y) - (x+y) → 0` by flattening `MUL(-1, ADD(x, y))`)
- Collect like terms: if `ti == tj`, merge `ci + cj`
- Drop terms with `ci == 0`
- If all terms vanish, return `coeff`
- If one term remains with `coeff == 0` and `ci == 1`, return `ti`

## 4.3 Canonical Form — Mul

`IXS_MUL` stores `coeff * Π bi^ei` where:

- `coeff` is a nonzero rational constant (default 1)
- Each `bi` is a non-MUL, non-constant node
- Each `ei` is a nonzero integer exponent
- Factors sorted by canonical order on `bi`

Construction rules:

- `MUL(... * MUL(c * Π dj^fj) ...)` → flatten
- Collect like bases: if `bi == bj`, merge `ei + ej` (checked for `int32_t`
  overflow; on overflow → sentinel + error)
- Drop factors with `ei == 0` (they contribute 1)
- If `coeff == 0`, return `0`
- `expr * 1` → `expr`
- Pull constant factors out of ADD: `2 * (a + b)` is kept as-is (don't
  distribute). Distribution is not performed by the simplifier.
  Use `ixs_expand` to distribute on demand.

## 4.4 Floor / Ceiling / Truncation Rules

Both `floor` and `ceiling` are kept as first-class nodes. They appear in
roughly equal frequency (12,198 and 13,403 occurrences) and normalizing one
to the other (e.g., `ceiling(x) → -floor(-x)`) would introduce negations
that obscure the structure and make output harder to compare against SymPy.

```
floor(integer)                     → identity
floor(p/q)                         → ⌊p/q⌋  (constant fold)
floor(floor(x))                    → floor(x)
floor(ceiling(x))                  → ceiling(x)
floor(integer_valued)              → identity
floor(n + intval_terms + rest)     → n + intval_terms + floor(rest)
    where each intval_term is provably integer-valued (structurally,
    or via congruence: (p/q)*sym when q divides sym's known modulus)
floor(outer * (a + b + ...))       → distribute, extract integer-valued products
    e.g. floor((6*K*floor(x/3) + y) / (2*K)) → 3*floor(x/3) + floor(y/(2*K))
    MUL bases in outer are decomposed for symbolic cancellation

ceiling(integer)                   → identity
ceiling(p/q)                       → ⌈p/q⌉  (constant fold)
ceiling(ceiling(x))                → ceiling(x)
ceiling(floor(x))                  → floor(x)
ceiling(integer_valued)            → identity
ceiling(n + intval_terms + rest)   → n + intval_terms + ceiling(rest)
    (same congruence-aware integrality check as floor)
ceiling(outer * (a + b + ...))     → distribute, extract integer-valued products

trunc(integer)                     -> identity
trunc(p/q)                         -> p/q rounded toward zero (constant fold)
trunc(x)                           -> floor(x) when bounds prove x >= 0
trunc(x)                           -> ceiling(x) when bounds prove x <= 0
```

The ADD and MUL-over-ADD extraction rules share implementation via
`round_extract_add` and `round_extract_mul_add`.  `round_extract_add`
uses a `round_fn` callback for its recursive tail; `round_extract_mul_add`
calls `simp_floor_bnds` / `simp_ceil_bnds` directly (selected by a
`bool is_floor` flag) so the expanded sum inherits bounds context.

```
floor(c + sum(ci*bi))  → floor(sum(ci*bi))
    when every bi is integer-valued and 0 < c < 1/lcm(qi)
    (the sum lies on a 1/L grid; c < 1/L can't cross a grid point)
floor(grid_terms + t)   → floor(grid_terms)
    when bounds prove 0 <= t < the grid spacing of grid_terms
floor(Mod(X, M) / K)  → 0   when K >= M > 0
round(round(A) / D)   → round(A / D)   when D is a positive integer
                                        (round = floor or ceiling)
```

The `round_unwrap_inner` helper applies the identity `round(round(a)/D) = round(a/D)`
for positive integer D.  Proof (floor): let a = D*q + r + f where q = floor(a/D),
0 <= r < D integer, 0 <= f < 1.  Then r + f < D, so both sides equal q.
The ceiling proof is symmetric.  D must be positive; the identity fails for
negative D (counterexample: `floor(floor(-5.5)/(-3)) = 2`, `floor(-5.5/(-3)) = 1`).
The helper detects MUL nodes where one factor is FLOOR/CEIL^1 and computes
D by inverting exponents and reciprocating the coefficient.  Registered as
`floor_unwrap_inner` in `floor_rules[]` and `ceil_unwrap_inner` in `ceil_rules[]`.

The constant-drop rule is implemented in `floor_drop_const` and registered
in `floor_rules[]`.  When bounds are available, `floor_drop_const` refines
the effective denominator per-term: if `Mod(K, M) == 0` is known for a
symbol `K`, then `|coeff|*M` replaces `|coeff|` in the LCM calculation,
widening the grid (e.g. `floor(7/8 + K/256)` -> `K/256` under `256|K`
because the effective grid is 1, not 1/256).  For non-structurally-integer
terms, `is_known_divisible` checks whether the denominator divides out.

`round_extract_add` splits rational constants into integer + fractional
parts (e.g. `65/32 → 2 + 1/32`) before testing the drop condition,
so `floor(65/32 + 1/2*floor(x/16))` reduces to `2 + floor(1/2*floor(x/16))`.
If the checked integer/fractional split is not representable and no other
integer-valued addend can be extracted, the rule leaves the rounding node
unchanged.  Its recursive tail is entered only after an integer constant or
term was actually removed from the remainder.
When bounds are available, `round_extract_add` uses `is_integer_with_divinfo`
and `is_known_divisible` to extract addends with rational coefficients that
are provably integer via congruence (e.g. `floor(x/3 + K/32)` ->
`K/32 + floor(x/3)` when `Mod(K, M) == 0` for any `M` with `32 | M`,
since `32 | K` makes `K/32` integer).  The helper `addterm_is_integer_valued`
encapsulates this check for both the detection and extraction passes.

`is_integer_with_divinfo`, `is_known_divisible`, and target-modulus residue
queries run in one compound proof graph. `DIVISIBLE(x, m)` first proves
`INTEGER(x)`, then proves `RESIDUE(x, m) == 0`; coefficient cancellation alone
cannot certify a nonintegral product. For `p/q * f1^e1 * ... * fn^en`, an
integer proof requests factor residues inside that graph to cancel `q`, while a
residue proof first proves every factor integer before accepting a zero
coefficient or reduced modulus of one. `Max` and `Min` have a known residue only
when every operand has that same residue, which also proves divisibility when
the common residue is zero.

```
floor(C/D + sum(ci * ti / D))  →  floor(C'/D + sum(ci * ti / D))
    when every ti and D are integer-valued, D is proven nonnegative, D is
    symbolic, all terms share D^{-1}, and C' = C - (C mod gcd(g, L)) where
    g = gcd of base numerator coefficients and L = lcm of rational coefficient
    denominators. A defined source division excludes D = 0.
    (Proof: N = sum(ni*ti) is always a multiple of g; adding
    r < gcd(g, L) to N cannot push past the next floor boundary.)
```

The symbolic-denominator constant-drop rule is implemented in
`floor_drop_const_sym`, also registered in `floor_rules[]`. Nonnegativity and
integrality are semantic preconditions: negative and positive fractional
denominators have defined counterexamples.

`round_extract_mul_add` also distributes `floor(outer * (const + terms))`
when `outer` is non-integer and the ADD has a nonzero constant, even if no
distributed term is integer-valued.  This converts factored forms into the
distributed form expected by `floor_drop_const_sym`.

`ixs_node_is_integer_valued` recognises `IXS_PIECEWISE` nodes as
integer-valued when all value branches are integer-valued.

More advanced rules (applied when domain info is available):

```
floor(x / n) where x = n*q + r, 0 <= r < n
  → q    (when r's bounds are provable)

floor(floor(x/a) / b)    → floor(x / (a*b))    when a,b > 0 integer
ceiling(ceiling(x/a) / b) → ceiling(x / (a*b))  when a,b > 0 integer
Mod(a*floor(x/a), a)     → 0
Mod(x, n) where 0 <= x < n is provable → x
floor((A+s)/D) - floor(A/D) → 0
    when D is a positive integer and 0 <= Mod(A,D)+s < D is provable
```

The same-bucket floor scan is linear in the normalized ADD size and inspects
at most 256 candidate pairs. Quotient reconstruction caps repeated powers at
`MAX_FOLD_EXP`; reaching either bound leaves the expression unchanged.

## 4.5 Mod Rules

`Mod(a, b)` is canonically `a - b * floor(a / b)`. The simplifier can either:

(a) Keep `Mod` as a first-class node when no simplification applies, or
(b) Expand to `a - b * floor(a / b)` and let floor rules do the work.

Strategy: keep `Mod` as a node (it reads better and avoids expression blowup),
but apply these rules:

```
Mod(c, m)           where c,m constant   → c mod m
Mod(x, 1)                                → 0
Mod(x + k*m, m)     where k is integer   → Mod(x, m)
Mod(x, m)           where 0 <= x < m     → x
Mod(Mod(x, m), m)                        → Mod(x, m)
Mod(bitop(a1, ..., an), 2^k)             → bitop(Mod(a1, 2^k), ...,
                                                    Mod(an, 2^k))
                     when every ai is integer-valued and
                     bitop is XOR, AND, or OR
Mod((p/q)*(c + sum(ci*ti)), m)           → Mod(c' + sum(ci'*ti), m)
                     when all scaled coefficients are integral
Mod(C + sum(ci*ti), m)                   → r + Mod(C-r + sum(ci*ti), m)
                     where g = gcd(m, |ci|), r = C mod g, 0 < r < g,
                     and every ti is integer-valued
Mod(a*m + b, m)     where a contains no IXS_MOD node → Mod(b, m)
Mod(g*x + r, g*m)   where g > 1, 0 <= r < g,
                     all terms integer   → g*Mod(x, m) + r
Mod(c*x, c*m)       where c > 1         → c*Mod(x, m)
(p/q)*Mod(q*x, q*m) where q > 1, m > 0,
                     x is integer-valued → p*Mod(x, m)

(reverse direction, in simp_add — recognize_mod)
c*E - c*N*floor(E/N)                    → c*Mod(E, N)
c*N*ceil(E/N) - c*E                     → c*Mod(-E, N)
c*E - c*D*floor(E/D)                    → c*Mod(E, D)     (D positive literal)
c*D*ceil(E/D) - c*E                     → c*Mod(-E, D)    (D positive literal)

(forward direction, in simp_add — cancel_floor_mod_pairs)
ci*o*m*floor(E/m) + ci*o*Mod(E, m)      → ci*o*E
                     without requiring a sign or nonzero proof for m
F*floor(E/m) + C*Mod(E, m)               → C*E + (F-C*m)*floor(E/m)
                     when m is a positive integer literal,
                     F/(C*m) is an exact rational greater than one,
                     and the residual stays a constant or one MUL

(consecutive Euclidean digits, in simp_add)
O*Mod(X,A) + O*A*Mod(floor(X/A),B)        → O*Mod(X,A*B)
                     when X, A, and B are integer-valued and the quotient
                     decomposition recovers the same X and A
Mod(X,r0) + r0*d1 + ... + rk*dk           → Mod(X,R)
                     for a complete literal digit row extracted from
                     enclosing Mod(X,M) values, with R dividing every M

(bounds-aware ADD cancellation)
c*Mod(A, m) - c*Mod(B, m)               → 0
                     when the shared m is provably positive and the cached
                     exact-delta proof establishes A == B
                     or, for literal m, A-B ≡ 0 (mod m)
```

The reverse identities, exact floor/Mod cancellation, consecutive-digit
composition, signed-division certificates, and quotient algebra all consume
the same private Euclidean row plan from `src/additive_row.c`. The plan borrows
canonical ADD terms, locates exactly one exponent-one `floor`, `ceiling`, or
`Mod` atom, and recovers its numerator, denominator, and exact scale. It owns
shape and representability only. Each caller still decides positivity,
integer-valuedness, totality, poison refinement, and signed-truncation policy.
Compound product and quotient reconstruction use O(T) scratch restored before
return; row borrowing and direct `Mod` atoms allocate nothing.

Exact floor/Mod cancellation is valid on every defined source evaluation. If
the divisor is invalid, the source is poison and may refine to the replacement;
domain-error detection is best effort. Partial cancellation still requires a
positive integer literal because its residual algebra is not the exact identity.

Consecutive-digit composition admits symbolic integer radices and a symbolic or
partial common scale. A defined source already implies `A > 0` and `B > 0`, so
the exact identity may refine the remaining domain to poison elsewhere. The
product `A*B` uses checked optional arithmetic: an unrepresentable product is a
no-match without a diagnostic, while allocation failure is propagated.
Mod-bearing ADD terms are indexed by carrier and modulus at no more than 50%
load, giving expected O(N) work. Reverse floor/ceiling recognition likewise
indexes the borrowed row by carrier at no more than 50% load instead of pairing
every round with every term. Rebuilding after one match composes complete digit
chains of any length through the same rule. Wrong coefficients, different
carriers, noninteger radices or carriers, incomplete chains, and quotient
normalizations that do not recover the original carrier remain unchanged.

Opposite-coefficient Mod terms share the modular bounds proof used by exact
equivalence. It proves both original Mod operations defined, proves their
shared modulus positive, and reuses the active exact-delta cache. Equal
dividends therefore cancel for a symbolic modulus without a second equality
engine. Positive literal moduli retain the congruence fallback for nonzero
dividend deltas. Missing positivity, unequal dividends, query exhaustion, and
invalid source operations do not become algebraic matches.

Complete literal rows of at most eight terms use the same direct `Mod`
canonical target. Each place must be unique, every later digit must come from
an enclosing `Mod` whose modulus is divisible by the next accumulated radix,
and a terminal bare floor must end exactly at that enclosing modulus. Shape
recognition is allocation-free O(T^2). Construction requires the shared carrier
to be structurally integer-valued or proved integer-valued by active facts;
overflow, a fractional carrier, an incomplete row, or an unrelated term is a
no-match. Equivalence therefore needs no separate mixed-radix tactic: after its
ordinary definedness admission, fact simplification produces the same interned
direct `Mod` on both sides.

Power-of-two bitwise projection is one quotient-ring rule, not three
operator-specific matchers. The shared low-bit engine walks nested XOR/AND/OR
DAGs once and materializes every opaque integer leaf as a residue. Each
projected operand and the rebuilt result lies in `[0, 2^k)`, so the outer
`Mod` disappears. Bounds may prove an otherwise structural operand
integer-valued. Totalness is not required: the rewrite is exact on every
defined source evaluation and may refine poison elsewhere. Non-power-of-two or
dynamic moduli and operands not proven integer-valued remain unchanged.

Refinement happens when a node is constructed. Thus symbolic `k/k` becomes
`1`, and substituting `k = 0` later leaves `1`; directly constructing `0/0`
still produces a domain-error sentinel. Both results satisfy the refinement
contract, and no later pass recreates an operand already removed.

Bounds-aware elimination accepts symbolic integer moduli: proofs of `m > 0`,
`x >= 0`, and `x-m < 0` reduce `Mod(x,m)` to `x`. Interval propagation also
handles symbolic integer moduli. If assumptions prove `1 <= m <= U`, then an
integer-valued `Mod(x, m)` is in `[0, U - 1]`. An equality-constrained symbolic
modulus receives the same dividend-step tightening as a literal modulus. No
remainder bound is inferred unless the modulus is proven positive.

For literal positive moduli, a symbol's finite interval and stored congruence
are intersected before computing the `Mod` range. A full reachable residue
cycle uses its gcd extrema; a partial cycle is enumerated up to 1024 steps.
Larger partial cycles fall back to the structural over-approximation. An exact
known residue produces an exact interval. Bounds environments record whether
any congruence exists, so ordinary interval-only `Mod` queries skip the
recursive residue proof. Empty interval/congruence intersections mark the fact
domain contradictory.

Scaled exact division keeps modular wrap explicit. For example,
`Mod(2*x,2^32)/2` reduces to `Mod(x,2^31)` when `x` is integer-valued, then to
`x` only when the bounds prove `0 <= x < 2^31`. A signed 32-bit range crosses
the wrap and does not justify the second reduction.

Scale extraction may establish the `g*m` condition through congruence facts
instead of a structural leading coefficient.  If every non-constant dividend
coefficient is divisible by `g` and bounds prove `g` divides the symbolic
modulus, `Mod(g*x + r, modulus)` uses the same extraction for `0 <= r < g`.

Forward cancellation inspects at most 256 ADD-term pairs per simplification,
so unrelated large sums retain their original form rather than turning the
hot construction path into an unbounded quadratic scan. Nested-factor pairs in
two-term ADDs cancel during construction. Wider ADDs use one candidate-gated
pass during explicit simplification, avoiding repeated scans while the sum is
built term by term. During that explicit pass, a larger same-sign floor
multiplier may consume exactly one floor-Mod identity. Requiring a positive
literal modulus for partial cancellation and a compact positive residual avoids
expanding a smaller multiplier into a subtractive ADD. Fixed-point
simplification can consume another identity on the next pass,
which exposes radix chains while every individual pass keeps the 256-probe
bound. Failed arithmetic probes discard their private diagnostics; allocation
failure remains visible as `NULL`, so retrying the same simplification is safe.

The rule uses two verification strategies:

1. **floor(A/m) == floor_node** — reconstructs the expected floor via
   `simp_floor(simp_div(A, m))` and checks hash-consed pointer equality.
   Robust against eager floor rewrites (e.g. `round_pull_in_denom`
   collapsing `floor(floor(x/3)/2)` into `floor(x/6)`).

2. **m * floor_arg == A** — distributes `m` over the floor argument using
   `distribute_mul_decompose`, which decomposes compound inverse MUL bases
   (e.g. `K * (K/2)^{-1} → 2`) to enable symbolic cancellation.

### 4.5.1 Opposite-Coefficient MUL-ADD Cancellation

In `simp_add`, after coalescing like terms, `reduce_opposite_mul_add`
scans for pairs of addterms `c*M_i` and `-c*M_j` where both bases are
MUL nodes with the same number of factors.  If the two MUL nodes share
all factors (the "outer product") except for exactly one ADD^1 factor
each, the pair collapses:

```
c*K*(PW + A) - c*K*(PW + B)  ->  c*K*(A - B)
```

This eliminates shared Piecewise sub-expressions that arise when
index computations branch identically across a stride decomposition.
Factor ordering in MUL is hash-based, so the rule compares reconstructed
outer products (via `apply_pow`) rather than relying on positional
matching.  The pass runs to a fixpoint (repeated until no pair reduces).

## 4.6 Piecewise Rules

Piecewise requires `n >= 1`. The last case should have condition `True`
(catch-all default). If after eliminating `False` branches no cases remain,
the result is `IXS_ERROR` (no defined value).

```
Piecewise((v, True))                → v
Piecewise((v, False), rest...)      → Piecewise(rest...)
Piecewise((v, c), (v, d), rest...)  → Piecewise((v, c | d), rest...)
                                      when c and d are structurally total
Piecewise((a, c), (b, True))       where c evaluates to True → a
                                    where c evaluates to False → b

// Propagation through arithmetic:
k * Piecewise((v1, c1), ..., (vn, cn)) → Piecewise((k*v1, c1), ..., (k*vn, cn))
Piecewise(...) + expr                 → Piecewise((v1+expr, c1), ..., (vn+expr, cn))
floor(Piecewise((v1, c1), ...))       → Piecewise((floor(v1), c1), ...)
Mod(Piecewise(...), m)                → Piecewise((Mod(v1, m), c1), ...)
```

**Propagation strategy**: Push Piecewise inward (into branches) when the
enclosing operation is a simple linear function of the Piecewise result
(multiply by constant, add a term, apply floor/Mod). This lets each branch
simplify independently. Do NOT lift Piecewise outward (e.g., wrap an entire
Add in Piecewise) as that duplicates the non-Piecewise terms and causes
expression blowup.

Equal-value conditions are not merged when either condition is partial. The
original Piecewise evaluates them in order, while eager `c | d` would evaluate
both and could introduce a domain error on a branch the source never reaches.

**Branch-aware bounds**: During bounds-aware rewriting, each non-default
Piecewise branch gets a forked copy of the current bounds augmented with
the branch condition.  Conditions like `E > 0` tighten the lower bound of
`E` to 1, letting `Max(1, E)` collapse inside that branch.  Expression-level
bounds are stored alongside per-symbol bounds and intersected during
interval queries.  All four comparison directions (GT, GE, LT, LE) are
stored directly as expression bounds.  For LT/LE conditions (`E < 0`,
`E <= 0`), the negated expression `-E` is also stored with a flipped GT/GE
bound; this is necessary because `Max(-E, c)` sees `-E` as a distinct
hash-consed node from `E`, and the expression-bound lookup requires pointer
equality.

**Product-zero decomposition**: When a guard pins a product `A*B` to zero
(the LE bound and propagated GE bound intersect to `[0,0]`) and all factors
except one are provably nonzero, the remaining factor gets an explicit
`[0,0]` bound.  For example, `floor(C/32)*ceil(M/256) <= 0` with `M >= 1`
forces `ceil(M/256) >= 1`, so `floor(C/32)` must be zero.  This lets the
branch value `floor(-32*floor(C/32)*...) = floor(0) = 0` collapse,
eliminating the entire Piecewise when the branch matches the default.

**Sentinel handling**: Value sentinels do not propagate through Piecewise (see
Error Model). A branch whose condition folds to `False` is silently dropped.
When at least one value branch is not poison, a sentinel value under an
unresolved condition remains contained in the Piecewise. Once folding selects
that branch, the sentinel propagates. If all value branches are poison, the
whole expression is poison. A sentinel condition still propagates because
branch selection itself is poisoned.

## 4.7 Max / Min Rules

```
Max(a) / Min(a)             → a
Max(..., a, a, ...)         → Max(..., a, ...)
Min(..., a, a, ...)         → Min(..., a, ...)
Max(..., constants, ...)    → keep their greatest value
Min(..., constants, ...)    → keep their least value
Max(..., b, ...)            → drop b when another operand is provably >= b
Min(..., b, ...)            → drop b when another operand is provably <= b
```

Nested MAX/MIN nodes flatten before these rules run. Empty MAX/MIN is a domain
error.

## 4.8 XOR Rules

```
xor(..., xor(args...), ...) → xor(..., args..., ...)
xor(..., 0, ...)            → xor(...)
xor(..., constants, ...)    → fold constants with ^
xor(..., a repeated n, ...) → keep a iff n is odd
xor(..., c*xor(b...), ...)  → xor(..., c*b, ...)
                  when c is a positive integer literal and every b is a
                  defined integer proven in [0,1]
xor(..., c1*b, c2*b, ...)   → xor(..., (c1 xor c2)*b, ...)
                  under the same mask and binary-factor conditions
xor(a, b)       → a + b    when a,b >= 0 and known bits do not overlap

k*xor(a, b + 2^n) - k*xor(a, b)
                → k*(2^n - 2*(a & 2^n))
                  when bit n of the pre-toggle operand is known zero
```

Parity reduction replaces the old nested-cancellation rule and handles the
whole flat list in one pass. An even run disappears under the common poison-
refinement contract.

The bounds-aware XOR canonicalizer also treats defined binary integers as a
local GF(2) basis. It distributes a positive literal mask through one directly
scaled XOR level and XOR-combines masks attached to pointer-identical factors.
The structural planning pass caps the prospective form at 256 terms before any
domain query or allocation. Collection proves each admitted factor defined,
integer-valued, and bounded in `[0,1]`; wider, fractional, negative, or partial
factors remain opaque. Reduction uses `O(T)` query scratch and `O(T log T)`
intrinsic work for `T <= 256`, without value enumeration, recursion, or a
context-wide scan. Allocation failure aborts the simplification and permits a
clean retry. Equivalence consumes the same fact-backed simplifier, so an
invertible binary basis is proved through its canonical reconstruction rather
than a second XOR prover.

Fact-backed ADD rewriting gives the XOR-delta rule its active bounds object.
The rule therefore reuses the current bitfacts cache and can consume stored
congruence and mask facts. Fact-free construction retains the same structural
rule through a temporary empty bounds object; it is not used when facts are
active.

The known-bit query merges exact interval facts and propagates low 64-bit
facts through `ADD`, positive power-of-two `MUL`, `floor(x/2^n)` for
non-negative `x`, and `Mod(x, 2^n)`. `MUL` and `Mod` only produce bitfacts
for integer-valued expressions. The XOR-to-ADD rule is deliberately
bounds-aware: both operands must be proven non-negative with finite int64
bounds, because the known-bit lattice tracks only the low 64 bits. The
XOR-delta rule leaves the largest int64 power-of-two delta untouched to avoid
overflowing temporary arithmetic.

`ADD` preserves sparse bitfacts when every normalized addend is a non-negative
integer scaled by a positive power of two and their possible-one masks are
pairwise disjoint. Addition is then carry-free and its possible and required
bits are the unions of the addend masks. Overlapping masks, negative scales,
and non-integer scales keep the interval-derived fallback.

After rebuilding a fact-backed node, the generic exact-integer projector may
materialize it when known-zero and known-one cover all 64 bits. For example,
`Mod(x, 16) == 0` reduces `x & 15` to zero. Partial coverage does not produce a
constant. Projection runs once per rewrite-memo entry and shares the active
bitfacts query rather than walking the reachable DAG in a separate bounds
context.

## 4.9 Bitwise And/Or And Logical Not

```
and(..., and(args...), ...) → and(..., args..., ...)
or(..., or(args...), ...)   → or(..., args..., ...)
and(..., x, x, ...)         → and(..., x, ...)
or(..., x, x, ...)          → or(..., x, ...)
and(..., constants, ...)    → fold constants with &
or(..., constants, ...)     → fold constants with |
0 & x                       → 0       when x is defined and integer
-1 & x                      → x       when x is integer-valued
0 | x                       → x       when x is integer-valued
-1 | x                      → -1      when x is defined and integer
1 & bool                    → bool
1 | bool                    → 1
~0              → 1
~nonzero_const  → 0
~(~bool)        → bool
~(~x)           → x != 0
~(a > b)        → a <= b
bool & ~bool    → 0
bool | ~bool    → 1
```

AND and OR apply these rules across the complete flat list. They are also
boolean operators when every operand is known 0/1-valued. `IXS_NOT` remains
logical truthiness. Complement matching and its proof use one canonical key for
`p` and `~p`, so normalization cannot depend on grouping or proof budget.

## 4.10 Comparison Simplification

```
a > b   → (a - b) > 0   (normalize to compare against 0)
```

Then apply constant folding when `a - b` reduces to a constant, or bound
analysis when the sign of `a - b` is provable. Identity folding, normalization,
and bounds resolution are poison refinements: defined source evaluations keep
the same truth value, while an undefined comparison may refine to either truth
value. Normalization is opportunistic: if the exact `a - b` rational form
exceeds the node representation, the original structurally valid comparison
is retained and the failed fold's diagnostic is discarded. Operand errors and
allocation failure still propagate.

After fact-backed rewriting finishes, a predicate root receives one bounded
truth projection at the caller boundary. Structural predicate evaluation and
the existing finite-domain proof may replace the root with canonical `0` or
`1`; they are not simplifier rules and cannot recurse into rewriting. The
finite fallback inspects at most 4096 nodes and 8 finite-range symbols and
enumerates at most 64 Cartesian points. Varying predicates, eager partial
operands, larger domains, proof limits, and allocation failure retain the
ordinary query status instead of manufacturing a constant.
