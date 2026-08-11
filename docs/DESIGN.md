# ixsimpl — Index Expression Simplifier

A specialized C library for simplifying integer arithmetic expressions
used in index computation, memory addressing, and loop bound calculation.

## Design Map

This file is the entry point for the design specification. Detailed contracts
are split by subsystem:

- [Architecture and representation](architecture.md)
- [Simplification engine](simplification.md)
- [Bounds and proof services](bounds.md)
- [Runtime, errors, and performance](runtime.md)
- [Public API contracts](api.md)
- [Language bindings](bindings.md)
- [Validation and project evolution](validation.md)

The canonical C declarations live in [`include/ixsimpl.h`](../include/ixsimpl.h).
The design documents describe semantics and invariants, not a second copy of
that interface.

## Problem Statement

Compilers for tiled computational kernels generate hundreds of index
expressions to compute memory addresses, loop bounds, and data mappings.
These expressions must be simplified to produce efficient code.

Currently SymPy is used for this task. On a representative workload of 615
expressions from a single kernel compilation:

| Metric | Value |
|---|---|
| Total simplify time | 41.4 s |
| Avg per expression | 68 ms |
| Median | 37 ms |
| P90 | 171 ms |
| P99 | 268 ms |
| Max | 388 ms |
| Expressions >= 100ms | 233 (38%) |

SymPy is a general-purpose Python CAS. It carries enormous overhead for this
narrow domain: polymorphic dispatch through Python objects, general-purpose
pattern matching, and simplification rules for trigonometry, calculus, and
algebra that are never triggered.

**Goal**: A C library that simplifies these expressions 100-1000x faster than
SymPy, targeting < 1ms average and < 5ms worst-case per expression.

## Expression Domain Analysis

### What the expressions look like

A typical expression (929 chars average, 2994 chars max, depth up to 11):

```
128*Piecewise(
  (floor(($WG0 + $WG1*ceiling(_M_div_32/4)
    - 32*ceiling(_M_div_32/4)*floor(ceiling(_N_div_32/8)/32))
    / Max(1, ceiling(_N_div_32/8) - 32*floor(ceiling(_N_div_32/8)/32))),
   (ceiling(_N_div_32/8) - 32*floor(ceiling(_N_div_32/8)/32) > 0)
   & ($WG0 + $WG1*ceiling(_M_div_32/4)
      >= 32*ceiling(_M_div_32/4)*floor(ceiling(_N_div_32/8)/32))),
  (Mod(floor($WG0/32 + $WG1*ceiling(_M_div_32/4)/32),
       ceiling(_M_div_32/4)),
   True))
+ 128*floor($T0/64) + 4*floor((Mod($T0, 64))/16)
```

### Operators and functions (exhaustive list)

| Category | Items | Total occurrences |
|---|---|---|
| Arithmetic | `+`, `-`, `*`, `/` (integer division context) | ~59,000 |
| Rounding | `floor()`, `ceiling()`, `Trunc()` | 25,601 source occurrences plus generated truncation nodes |
| Modular | `Mod(a, b)` | 6,481 |
| Conditional | `Piecewise((val, cond), ..., (val, True))` | 1,136 |
| Min/Max | `Max(a, b)`, `Min(a, b)` | 1,140 |
| Bitwise | `xor(a, ...)` | 116 |
| Boolean | `&` (and), `\|` (or), `~` (not) | ~1,168 |
| Comparison | `>`, `<`, `>=`, `<=`, `==`, `!=` | ~2,236 |

**Not present**: trig, hyperbolic, exp, log, sqrt, abs, derivatives,
integrals, series, polynomials over symbolic variables, matrices, sets,
complex numbers, floating-point constants.

### Variables (complete set, 20 total)

`$T0`, `$T1`, `$T2`, `$WG0`, `$WG1`, `$ARGK`,
`$GPR_NUM`, `$MMA_ACC`, `$MMA_LHS_SCALE`, `$MMA_RHS_SCALE`,
`$MMA_SCALE_FP4`, `$index0`, `$index1`,
`_M_div_32`, `_N_div_32`, `_K_div_256`, `_aligned`,
`M`, `N`, `K`

The `$` and `_` prefixes are external naming conventions with no special
meaning to the library. All are treated uniformly as opaque symbolic names.

### Constants

- All integer constants (no floats). Powers of 2 dominate: 2, 4, 8, 16, 32,
  64, 128, 256, 512, 1024, 2048.
- 127 unique rational constants, all with denominators that are powers of 2
  (mostly /32, /16, /8, /4, /2). One exception: `56/3`.
- Rationals only appear as arguments to `floor()`, e.g.,
  `floor(floor(K/32)/8 + 7/8)`.

### Structural patterns

1. **Template + offset**: Many expressions are identical except for an additive
   constant (`+0`, `+16`, `+32`, `+48`, `+64`, ...). These form families of
   8-16 expressions.

2. **Shared subexpressions**: The Piecewise block for index-to-tile
   mapping appears in ~90% of expressions. Subtrees like
   `ceiling(M/128)*floor(ceiling(N/256)/32)` repeat thousands of times.

3. **Two naming epochs**: Early expressions use `_M_div_32`, `_N_div_32`;
   later ones use raw `M`, `N`, `K` with inline division. Same math, different
   symbolic variable granularity.

4. **Paired differences**: Many expressions come as `f(x+a) - f(x+b)` pairs,
   where the simplification goal is to reduce the difference.
