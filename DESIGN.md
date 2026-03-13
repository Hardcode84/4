# ixsimpl — Index Expression Simplifier

A specialized C library for simplifying integer arithmetic expressions
used in index computation, memory addressing, and loop bound calculation.

## Problem Statement

Compilers for tiled computational kernels generate hundreds of index
expressions to compute memory addresses, loop bounds, and data mappings.
These expressions must be simplified to produce efficient code.

Currently SymPy is used for this task. On a representative workload of 609
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
| Rounding | `floor()`, `ceiling()` | 25,601 |
| Modular | `Mod(a, b)` | 6,481 |
| Conditional | `Piecewise((val, cond), ..., (val, True))` | 1,136 |
| Min/Max | `Max(a, b)`, `Min(a, b)` | 1,140 |
| Bitwise | `xor(a, b)` | 116 |
| Boolean | `&` (and), `\|` (or), `~` (not) | ~1,168 |
| Comparison | `>`, `<`, `>=`, `<=`, `==` | ~2,236 |

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

## Architecture

```
┌──────────────────────────────────────────────────────┐
│                    Public C API                      │
│  ixs_ctx_create / ixs_parse / ixs_simplify / ...     │
├──────────────────────────────────────────────────────┤
│                  Simplifier Engine                   │
│  Constant folding → Canonicalization → Rewrite rules │
│  → Piecewise propagation → floor/ceil/mod rules      │
├──────────────┬───────────────┬───────────────────────┤
│  Expression  │  Hash-consing │  Rational             │
│  DAG Nodes   │  Table        │  Arithmetic           │
├──────────────┴───────────────┴───────────────────────┤
│                Arena Allocator                       │
└──────────────────────────────────────────────────────┘
```

### Layer 0: Memory — Arena Allocator

All expression nodes are allocated from a per-context arena. Nodes are never
individually freed; the entire arena is freed when the context is destroyed.
This eliminates per-node malloc/free overhead and improves cache locality.

```c
typedef struct ixs_arena {
    char *base;
    size_t used;
    size_t capacity;
    struct ixs_arena *next;  // chain for overflow
} ixs_arena;
```

Arenas grow by doubling. Typical working set for one expression is < 64 KB.

### Layer 1: Expression Representation — Hash-Consed DAG

Expressions are represented as a directed acyclic graph (DAG) with
hash-consing. Structurally identical subexpressions share a single node.
This is critical because the input expressions have massive subexpression
sharing.

```c
typedef enum {
    IXS_INT,         // 64-bit integer literal
    IXS_RAT,         // p/q rational (both int64_t, q > 0, gcd(p,q) = 1)
    IXS_SYM,         // named variable
    IXS_ADD,         // n-ary sum: coeff + c1*t1 + c2*t2 + ...
    IXS_MUL,         // n-ary product: coeff * t1^e1 * t2^e2 * ...
    IXS_FLOOR,       // floor(x)
    IXS_CEIL,        // ceiling(x)
    IXS_MOD,         // Mod(a, b) = a - b*floor(a/b), b > 0
    IXS_PIECEWISE,   // Piecewise((v1,c1), ..., (vn, True))
    IXS_MAX,         // Max(a, b)
    IXS_MIN,         // Min(a, b)
    IXS_XOR,         // bitwise xor(a, b) (integer domain)
    IXS_CMP,         // comparison: a op b, op in {>, <, >=, <=, ==, !=}
    IXS_AND,         // boolean and
    IXS_OR,          // boolean or
    IXS_NOT,         // boolean not
    IXS_TRUE,        // boolean constant
    IXS_FALSE,       // boolean constant
} ixs_tag;
```

Each node is a small struct:

```c
typedef struct ixs_node {
    ixs_tag tag;
    uint32_t hash;        // precomputed, used for hash-consing
    uint32_t refcount;    // for external API handles; DAG-internal refs are structural
    union {
        int64_t ival;                     // IXS_INT
        struct { int64_t p, q; } rat;     // IXS_RAT
        const char *name;                 // IXS_SYM
        struct {                          // IXS_ADD
            struct ixs_node *coeff;       //   rational constant term
            uint32_t nterms;
            struct ixs_addterm *terms;    //   sorted array of {node, coeff}
        } add;
        struct {                          // IXS_MUL
            struct ixs_node *coeff;       //   rational constant factor
            uint32_t nfactors;
            struct ixs_mulfactor *factors; //  sorted array of {base, exp}
        } mul;
        struct {                          // IXS_FLOOR, IXS_CEIL
            struct ixs_node *arg;
        } unary;
        struct {                          // IXS_MOD, IXS_MAX, IXS_MIN, IXS_XOR, IXS_CMP
            struct ixs_node *lhs;
            struct ixs_node *rhs;
            uint8_t cmp_op;              // only for IXS_CMP
        } binary;
        struct {                          // IXS_PIECEWISE
            uint32_t ncases;
            struct ixs_pwcase *cases;     //  array of {value, condition}
        } pw;
        struct {                          // IXS_AND, IXS_OR
            uint32_t nargs;
            struct ixs_node **args;
        } logic;
        struct {                          // IXS_NOT
            struct ixs_node *arg;
        } unary_bool;
    };
} ixs_node;
```

**Hash-consing**: A global (per-context) hash table maps
`(tag, hash_of_children)` -> `ixs_node*`. Before creating any node, look it
up. If found, return the existing pointer. This means pointer equality implies
structural equality, and common subexpressions are automatically shared.

**Canonical ordering**: Children of `IXS_ADD` and `IXS_MUL` are sorted by a
total order on nodes (by tag, then by content). This ensures `a + b` and
`b + a` produce the same hash and the same canonical node.

### Layer 2: Rational Arithmetic

All constants are exact rationals `p/q` with `int64_t` numerator and
denominator. For this domain, 64-bit is sufficient (the largest observed
constant is 335/32; intermediates from multiplication of tile sizes stay within
int64 range).

Operations: `add(a, b)`, `sub(a, b)`, `mul(a, b)`, `div(a, b)`,
`neg(a)`, `gcd(a, b)`, `is_zero(a)`, `is_one(a)`, `is_negative(a)`,
`cmp(a, b)`, `floor_rat(a)`, `ceil_rat(a)`, `mod_rat(a, b)`.

All results are reduced to lowest terms. Overflow detection: if any operation
would overflow int64, fall back to 128-bit intermediate (or assert — in
practice, the numbers in this domain are small).

### Layer 3: Parser

Recursive descent parser for the SymPy output format. The grammar is small:

```
expr     = term (('+' | '-') term)*
term     = unary (('*' | '/') unary)*
unary    = '-' unary | atom
atom     = INT | RATIONAL | SYMBOL
         | 'floor' '(' expr ')'
         | 'ceiling' '(' expr ')'
         | 'Mod' '(' expr ',' expr ')'
         | 'Max' '(' expr ',' expr ')'
         | 'Min' '(' expr ',' expr ')'
         | 'xor' '(' expr ',' expr ')'
         | 'Piecewise' '(' pw_cases ')'
         | '(' expr ')'
pw_cases = '(' expr ',' cond ')' (',' '(' expr ',' cond ')')*
cond     = cmp_expr (('&' | '|') cmp_expr)*
cmp_expr = '~' cmp_expr | expr cmp_op expr | 'True' | 'False'
           | '(' cond ')'
cmp_op   = '>' | '<' | '>=' | '<=' | '==' | '!='
```

Symbols: any identifier matching `[A-Za-z_$][A-Za-z0-9_$]*`. All parsed as
`IXS_SYM`. The `$` and `_` prefixes carry no special semantics.

Integer literals: sequences of digits. Rationals are not parsed directly —
they arise from `3/8` being parsed as `IXS_INT(3) / IXS_INT(8)` and
immediately folded to `IXS_RAT(3, 8)`.

The parser builds the DAG directly via the hash-consing table.

### Layer 4: Simplification Engine

Simplification is applied bottom-up during DAG construction (every
`ixs_make_*` constructor runs simplification rules before hash-consing) and
optionally as a top-down rewrite pass.

#### 4.1 Constant Folding

Any operation on constants is immediately evaluated:

- `floor(7/2)` → `3`
- `Mod(17, 5)` → `2`
- `Max(3, 7)` → `7`
- `ceiling(4)` → `4` (floor/ceil of integer = identity)
- `xor(5, 3)` → `6`
- `3 > 2` → `True`

#### 4.2 Canonical Form — Add

`IXS_ADD` stores `coeff + Σ ci * ti` where:

- `coeff` is a rational constant (possibly 0)
- Each `ti` is a non-ADD, non-constant node
- Each `ci` is a nonzero rational coefficient
- Terms sorted by canonical order on `ti`

Construction rules:

- `ADD(... + ADD(c + Σ di*ui) ...)` → flatten: merge `c` into coeff, merge
  all `di*ui` terms
- Collect like terms: if `ti == tj`, merge `ci + cj`
- Drop terms with `ci == 0`
- If all terms vanish, return `coeff`
- If one term remains with `coeff == 0` and `ci == 1`, return `ti`

#### 4.3 Canonical Form — Mul

`IXS_MUL` stores `coeff * Π bi^ei` where:

- `coeff` is a nonzero rational constant (default 1)
- Each `bi` is a non-MUL, non-constant node
- Each `ei` is a nonzero integer exponent
- Factors sorted by canonical order on `bi`

Construction rules:

- `MUL(... * MUL(c * Π dj^fj) ...)` → flatten
- Collect like bases: if `bi == bj`, merge `ei + ej`
- If `coeff == 0`, return `0`
- `expr * 1` → `expr`
- Pull constant factors out of ADD: `2 * (a + b)` is kept as-is (don't
  distribute). Distribution is only done by an explicit `expand()` call.

#### 4.4 Floor / Ceiling Rules

Both `floor` and `ceiling` are kept as first-class nodes. They appear in
roughly equal frequency (12,198 and 13,403 occurrences) and normalizing one
to the other (e.g., `ceiling(x) → -floor(-x)`) would introduce negations
that obscure the structure and make output harder to compare against SymPy.

```
floor(integer)                     → identity
floor(p/q)                         → ⌊p/q⌋  (constant fold)
floor(floor(x))                    → floor(x)
floor(ceiling(x))                  → ceiling(x)
floor(x + n)  where n is integer   → floor(x) + n
floor(n * x)  where n is integer   → n * floor(x)  IF x known integer

ceiling(integer)                   → identity
ceiling(p/q)                       → ⌈p/q⌉  (constant fold)
ceiling(ceiling(x))                → ceiling(x)
ceiling(floor(x))                  → floor(x)
ceiling(x + n)  where n is integer → ceiling(x) + n
ceiling(n * x)  where n is integer → n * ceiling(x)  IF x known integer
```

More advanced rules (applied when domain info is available):

```
floor(x / n) where x = n*q + r, 0 <= r < n
  → q    (when r's bounds are provable)

floor(floor(x/a) / b)    → floor(x / (a*b))    when a,b > 0 integer
ceiling(ceiling(x/a) / b) → ceiling(x / (a*b))  when a,b > 0 integer
Mod(a*floor(x/a), a)     → 0
Mod(x, n) where 0 <= x < n is provable → x
```

#### 4.5 Mod Rules

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
Mod(a*m + b, m)     where a doesn't depend on Mod → Mod(b, m)
```

#### 4.6 Piecewise Rules

```
Piecewise((v, True))                → v
Piecewise((v, False), rest...)      → Piecewise(rest...)
Piecewise((v, c), (v, d), rest...)  → Piecewise((v, c | d), rest...)
                                      (same value, merge conditions)
Piecewise((a, c), (b, True))       where c evaluates to True → a
                                    where c evaluates to False → b

// Propagation through arithmetic:
k * Piecewise((v1,c1),...,(vn,cn)) → Piecewise((k*v1,c1),...,(k*vn,cn))
Piecewise(...) + expr              → Piecewise((v1+expr,c1),...,(vn+expr,cn))
floor(Piecewise((v1,c1),...))      → Piecewise((floor(v1),c1),...)
Mod(Piecewise(...), m)             → Piecewise((Mod(v1,m),c1),...)
```

The strategy is to push Piecewise outward (lift it to the top of the
expression tree) when it enables further simplification, and push it
inward when the branches can be individually simplified.

#### 4.7 Max / Min Rules

```
Max(a, a)       → a
Max(a, b)       where a >= b provable → a
Max(1, x)       where x > 0 provable → max(1, x) (keep)
                where x >= 1 provable → x
Min(a, b)       → -Max(-a, -b)  (normalize to Max)
```

#### 4.8 XOR Rules

```
xor(a, a)       → 0
xor(a, 0)       → a
xor(0, b)       → b
xor(c1, c2)     → c1 ^ c2  (constant fold)
```

XOR appears only 116 times in the corpus and only in specific patterns
(`xor(Mod($T0, 8), floor(Mod($T0, 64)/16) + offset)`). These are bit
manipulation patterns and may not need deep algebraic simplification.

#### 4.9 Boolean Simplification

```
True & x        → x
False & x       → False
True | x        → True
False | x       → x
~True           → False
~False          → True
~(~x)           → x
~(a > b)        → a <= b
(a > b) & (a >= b) → a > b
```

#### 4.10 Comparison Simplification

```
a > b   → (a - b) > 0   (normalize to compare against 0)
```

Then apply constant folding when `a - b` reduces to a constant, or bound
analysis when the sign of `a - b` is provable.

### Layer 5: Bound Analysis (Optional, Phase 2)

Many simplification rules require knowing whether a subexpression is
non-negative, positive, or bounded. A lightweight interval analysis pass:

- Bounded variables: `0 <= $T0 < 256`, `0 <= $T1 < ...`, etc.
  (bounds provided by the caller via API)
- `floor(x)`: if `lo <= x <= hi`, then `floor(lo) <= floor(x) <= floor(hi)`
- `Mod(x, m)`: result in `[0, m-1]` when `m > 0`
- `ceiling(x/m)`: result >= 0 when `x >= 0` and `m > 0`

This enables rules like:

- `Mod(x, 32)` where `0 <= x < 32` → `x`
- `floor(x/64)` where `0 <= x < 64` → `0`
- `Max(1, expr)` where `expr >= 1` → `expr`

## Public API

```c
// Context: owns the arena, hash-consing table, and symbol table
typedef struct ixs_ctx ixs_ctx;
typedef struct ixs_node ixs_node;

// Lifecycle
ixs_ctx   *ixs_ctx_create(void);
void       ixs_ctx_destroy(ixs_ctx *ctx);

// Provide variable bounds (enables deeper simplification)
void ixs_ctx_set_bounds(ixs_ctx *ctx, const char *var, int64_t lo, int64_t hi);

// Assume a predicate (e.g., "M > 0", "_aligned == 1")
void ixs_ctx_assume(ixs_ctx *ctx, ixs_node *predicate);

// Parse a SymPy-format expression string
ixs_node *ixs_parse(ixs_ctx *ctx, const char *input, size_t len);

// Construct expressions programmatically
ixs_node *ixs_int(ixs_ctx *ctx, int64_t val);
ixs_node *ixs_rat(ixs_ctx *ctx, int64_t p, int64_t q);
ixs_node *ixs_sym(ixs_ctx *ctx, const char *name);
ixs_node *ixs_add(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_mul(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_floor(ixs_ctx *ctx, ixs_node *x);
ixs_node *ixs_ceil(ixs_ctx *ctx, ixs_node *x);
ixs_node *ixs_mod(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_max(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_min(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_xor(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_pw(ixs_ctx *ctx, uint32_t n, ixs_node **values, ixs_node **conds);
ixs_node *ixs_cmp(ixs_ctx *ctx, ixs_node *a, uint8_t op, ixs_node *b);
ixs_node *ixs_and(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_or(ixs_ctx *ctx, ixs_node *a, ixs_node *b);
ixs_node *ixs_not(ixs_ctx *ctx, ixs_node *a);

// Simplify (applies the full rewrite pass; parse already simplifies on construction)
ixs_node *ixs_simplify(ixs_ctx *ctx, ixs_node *expr);

// Structural equality (O(1) due to hash-consing)
bool ixs_equal(ixs_node *a, ixs_node *b);  // just pointer comparison

// Substitution
ixs_node *ixs_subs(ixs_ctx *ctx, ixs_node *expr,
                    const char *var, ixs_node *replacement);

// Output
size_t ixs_print(ixs_node *expr, char *buf, size_t bufsize);  // SymPy format
size_t ixs_print_c(ixs_node *expr, char *buf, size_t bufsize); // C code

// Batch: simplify multiple expressions sharing subexpressions
// (preserves CSE across the batch within the same context)
void ixs_simplify_batch(ixs_ctx *ctx, ixs_node **exprs, size_t n);
```

Usage pattern:

```c
ixs_ctx *ctx = ixs_ctx_create();
ixs_ctx_set_bounds(ctx, "$T0", 0, 255);
ixs_ctx_set_bounds(ctx, "$T1", 0, 3);
ixs_ctx_set_bounds(ctx, "$WG0", 0, INT64_MAX);
ixs_ctx_set_bounds(ctx, "$WG1", 0, INT64_MAX);
ixs_ctx_set_bounds(ctx, "M", 1, INT64_MAX);
ixs_ctx_set_bounds(ctx, "N", 1, INT64_MAX);
ixs_ctx_set_bounds(ctx, "K", 1, INT64_MAX);

ixs_node *expr = ixs_parse(ctx, input, strlen(input));
ixs_node *simplified = ixs_simplify(ctx, expr);

char buf[4096];
ixs_print(simplified, buf, sizeof(buf));
printf("%s\n", buf);

ixs_ctx_destroy(ctx);  // frees everything
```

## Performance Design

### Why this can be 100-1000x faster than SymPy

1. **No Python overhead**: Every SymPy operation goes through Python's object
   model, GIL, reference counting, and dynamic dispatch. A single `floor(x+1)`
   in SymPy creates multiple Python objects and calls `__new__`, `__init__`,
   `__hash__`, `__eq__` in Python. In C, it's a hash table lookup and a
   pointer.

2. **Hash-consing eliminates redundant work**: The 609 expressions share most
   of their subexpressions. In SymPy, each expression re-creates and
   re-simplifies common subtrees. With hash-consing, `ceiling(M/128)` is
   created once, stored once, and every expression that uses it gets the
   same pointer for free.

3. **Arena allocation**: Zero per-node malloc/free overhead. Excellent cache
   locality.

4. **No wasted generality**: SymPy checks for trigonometric identities,
   logarithmic simplification, polynomial factoring, etc. on every expression.
   This library checks only for the ~30 rules that actually apply.

5. **Batch mode**: Processing all 609 expressions in one context means the
   hash-consing table is warmed up, and later expressions (which are variants
   of earlier ones) are nearly free.

### Target performance

| Metric | SymPy (current) | Target |
|---|---|---|
| 609 expressions total | 41.4 s | < 50 ms |
| Average per expression | 68 ms | < 0.1 ms |
| Worst case | 388 ms | < 5 ms |

### Memory budget

Estimated working set for 609 expressions with shared subexpressions:

- Unique nodes (after hash-consing): ~10,000-30,000
- Node size: ~64 bytes average
- Hash table: ~128 KB
- Arena: ~2-4 MB
- Total: < 8 MB

## File Structure

```
ixsimpl/
├── include/
│   └── ixsimpl.h            # public C API (single header)
├── src/
│   ├── arena.c               # arena allocator
│   ├── arena.h
│   ├── rational.c            # exact rational arithmetic
│   ├── rational.h
│   ├── node.c                # node creation, hash-consing, canonical forms
│   ├── node.h
│   ├── parser.c              # recursive descent parser
│   ├── parser.h
│   ├── simplify.c            # rewrite rules engine
│   ├── simplify.h
│   ├── bounds.c              # interval/bound analysis
│   ├── bounds.h
│   ├── print.c               # output formatters
│   ├── print.h
│   └── ctx.c                 # context management, public API impl
├── bindings/
│   ├── cpp/
│   │   └── ixsimpl.hpp       # C++ header-only wrapper
│   └── python/
│       ├── ixsimpl.pyi       # type stubs
│       └── _ixsimpl.c        # CPython extension module
├── test/
│   ├── test_rational.c
│   ├── test_parser.c
│   ├── test_simplify.c
│   ├── test_bounds.c
│   ├── test_corpus.c         # run against the 609-expression corpus
│   ├── test_cpp.cpp           # C++ binding tests
│   ├── test_python.py         # Python binding tests
│   └── corpus.txt             # the reference expressions
├── bench/
│   └── bench_corpus.c        # benchmark: time all 609 expressions
├── CMakeLists.txt
├── setup.py                   # Python package build
└── LICENSE                    # MIT
```

Estimated total: 5,000-8,000 lines of C, ~500 lines C++ header, ~800 lines
Python extension.

## Language Bindings

### C++ Binding — `ixsimpl.hpp`

A thin header-only RAII wrapper over the C API. No additional runtime cost.

```cpp
namespace ixs {

class Context {
    ixs_ctx *ctx_;
public:
    Context() : ctx_(ixs_ctx_create()) {}
    ~Context() { ixs_ctx_destroy(ctx_); }
    Context(const Context&) = delete;
    Context& operator=(const Context&) = delete;

    void set_bounds(const char *var, int64_t lo, int64_t hi) {
        ixs_ctx_set_bounds(ctx_, var, lo, hi);
    }
    void assume(Expr pred);

    ixs_ctx *raw() const { return ctx_; }
};

class Expr {
    ixs_ctx *ctx_;
    ixs_node *node_;
public:
    Expr(ixs_ctx *ctx, ixs_node *node) : ctx_(ctx), node_(node) {}

    static Expr parse(Context &ctx, std::string_view input) {
        return {ctx.raw(), ixs_parse(ctx.raw(), input.data(), input.size())};
    }
    static Expr sym(Context &ctx, const char *name) {
        return {ctx.raw(), ixs_sym(ctx.raw(), name)};
    }
    static Expr integer(Context &ctx, int64_t v) {
        return {ctx.raw(), ixs_int(ctx.raw(), v)};
    }

    Expr simplify() const { return {ctx_, ixs_simplify(ctx_, node_)}; }
    Expr subs(const char *var, Expr repl) const {
        return {ctx_, ixs_subs(ctx_, node_, var, repl.node_)};
    }

    Expr operator+(Expr rhs) const { return {ctx_, ixs_add(ctx_, node_, rhs.node_)}; }
    Expr operator*(Expr rhs) const { return {ctx_, ixs_mul(ctx_, node_, rhs.node_)}; }
    bool operator==(Expr rhs) const { return node_ == rhs.node_; }

    std::string str() const {
        char buf[4096];
        size_t n = ixs_print(node_, buf, sizeof(buf));
        return {buf, n};
    }

    ixs_node *raw() const { return node_; }
};

inline Expr floor(Expr x) { return {x.raw_ctx(), ixs_floor(x.raw_ctx(), x.raw())}; }
inline Expr ceil(Expr x)  { return {x.raw_ctx(), ixs_ceil(x.raw_ctx(), x.raw())}; }
inline Expr mod(Expr a, Expr b) { return {a.raw_ctx(), ixs_mod(a.raw_ctx(), a.raw(), b.raw())}; }
// ... etc

} // namespace ixs
```

Key properties:
- `Context` owns the arena; RAII cleans up everything on destruction.
- `Expr` is a lightweight value type (two pointers). Cheap to copy.
- Operator overloading for natural expression building.
- No heap allocations beyond what the C library does internally.
- No exceptions — errors reported via null returns, same as C API.

### Python Binding — `_ixsimpl.c`

A CPython C extension module (no pybind11/ctypes dependency). Exposes two
Python types: `Context` and `Expr`.

```python
import ixsimpl

ctx = ixsimpl.Context()
ctx.set_bounds("$T0", 0, 255)
ctx.set_bounds("M", 1, 2**31)

expr = ctx.parse("128*floor($T0/64) + 4*floor(Mod($T0, 64)/16)")
result = expr.simplify()
print(result)              # SymPy-compatible string
print(result.to_c())       # C code string

# Programmatic construction
x = ctx.sym("x")
y = ctx.sym("y")
e = ixsimpl.floor(x + y) + 3
print(e.simplify())

# Batch
exprs = [ctx.parse(line) for line in lines]
ctx.simplify_batch(exprs)
```

Implementation:
- `_ixsimpl.c` is a single-file CPython extension using the stable ABI
  (`Py_LIMITED_API`), so one `.so` works across Python 3.7+.
- `Context` Python object wraps `ixs_ctx*`; destructor calls
  `ixs_ctx_destroy`.
- `Expr` Python object holds a reference to its `Context` (preventing
  premature GC) and wraps `ixs_node*`.
- `__repr__` and `__str__` call `ixs_print`.
- `__eq__` is pointer comparison (O(1) via hash-consing).
- `__hash__` returns the node's precomputed hash.
- Operator overloading: `__add__`, `__mul__`, `__sub__`, `__neg__`.
- `setup.py` / `pyproject.toml` builds the extension; no runtime
  dependencies.

This binding adds ~800 lines of C and is the primary interface for testing
against SymPy (run both, compare outputs).

## Implementation Plan

### Phase 1: Foundation

- Arena allocator
- Rational arithmetic with full test coverage
- Node types, hash-consing table
- Canonical Add/Mul construction with flattening and term collection
- Basic constant folding
- SymPy-format printer

**Milestone**: Can construct `3*x + 2*x + 1` and get `5*x + 1`.

### Phase 2: Parser + Floor/Ceil/Mod

- Recursive descent parser for the full grammar
- `floor()`, `ceiling()` constructors with basic rules
- `Mod()` constructor with basic rules
- `Max()`, `Min()`, `xor()` constructors

**Milestone**: Can parse and round-trip all 609 expressions. Simplification of
constant subexpressions works.

### Phase 3: Piecewise + Boolean

- Piecewise node type with condition simplification
- Boolean algebra (And/Or/Not) with basic simplification
- Comparison normalization
- Piecewise propagation through arithmetic

**Milestone**: Expressions with Piecewise are simplified correctly. Many
expressions in the corpus should already simplify significantly.

### Phase 4: Advanced Rules + Bound Analysis

- Bound tracking infrastructure
- Domain-aware floor/ceil/Mod rules
- Batch simplification mode
- Full test against corpus
- Benchmark against SymPy baseline

**Milestone**: All 609 expressions produce correct results. Performance target
met (< 50ms total).

### Phase 5: Bindings

- C++ header-only wrapper (`ixsimpl.hpp`)
- CPython extension module (`_ixsimpl.c`)
- Python test suite comparing output against SymPy
- `setup.py` / `pyproject.toml` for pip-installable package

**Milestone**: `pip install .` works; Python tests pass against SymPy oracle.

### Phase 6: Hardening + Integration

- Fuzz testing (generate random expressions, verify against SymPy)
- Edge cases: overflow, division by zero, degenerate Piecewise
- C code output mode
- Documentation
- Integration with the host compiler

## Testing Strategy

1. **Unit tests**: Each rule in isolation (test_rational, test_simplify).
2. **Corpus test**: Parse all 609 expressions, simplify, verify output matches
   SymPy's output (or is provably equivalent via random evaluation).
3. **Equivalence oracle**: For any simplified expression `s` from input `e`,
   verify `s == e` by substituting random values for all variables and
   checking numerical equality. This catches bugs without requiring
   exact output matching.
4. **Fuzz testing**: Hypothesis-based (see below).
5. **Benchmark**: Time all 609 expressions, compare against SymPy baseline.
   Track regressions in CI.

### Fuzz Testing with Hypothesis

Property-based fuzz testing uses Python's
[Hypothesis](https://hypothesis.readthedocs.io/) library to generate random
expressions within the grammar, simplify them with both ixsimpl and SymPy,
and verify equivalence via numerical evaluation.

```python
from hypothesis import given, strategies as st, settings, assume
import sympy
import ixsimpl

# Strategy: generate random expression trees within the grammar
sym_names = st.sampled_from(["x", "y", "z", "w"])
small_ints = st.integers(min_value=-64, max_value=64)
pos_ints = st.integers(min_value=1, max_value=32)

@st.composite
def expressions(draw, max_depth=4):
    if max_depth <= 0 or draw(st.booleans()):
        return draw(st.one_of(sym_names, small_ints))
    op = draw(st.sampled_from([
        "add", "mul", "floor", "ceiling", "mod", "max", "min"
    ]))
    a = draw(expressions(max_depth=max_depth - 1))
    if op in ("floor", "ceiling"):
        return (op, a)
    b = draw(expressions(max_depth=max_depth - 1))
    if op == "mod":
        b = draw(pos_ints)  # modulus must be positive
    return (op, a, b)

def to_sympy(tree):
    """Convert expression tree to SymPy expression."""
    ...

def to_ixsimpl(ctx, tree):
    """Convert expression tree to ixsimpl expression."""
    ...

@given(expr=expressions())
@settings(max_examples=10000)
def test_simplify_matches_numerical(expr):
    """Simplification preserves semantics: evaluate original and simplified
    at random points, check they agree."""
    ctx = ixsimpl.Context()
    ixs_expr = to_ixsimpl(ctx, expr)
    ixs_simplified = ixs_expr.simplify()

    # Evaluate both at random integer points
    for _ in range(10):
        env = {v: random.randint(1, 100) for v in ["x", "y", "z", "w"]}
        orig = eval_expr(expr, env)
        simp = eval_ixs(ixs_simplified, env)
        assert orig == simp, f"Mismatch: {orig} != {simp} at {env}"

@given(expr=expressions())
@settings(max_examples=5000)
def test_matches_sympy(expr):
    """Cross-check against SymPy: both should produce numerically
    equivalent results."""
    ctx = ixsimpl.Context()
    ixs_result = to_ixsimpl(ctx, expr).simplify()

    sp_expr = to_sympy(expr)
    sp_result = sympy.simplify(sp_expr)

    for _ in range(10):
        env = {v: random.randint(1, 100) for v in ["x", "y", "z", "w"]}
        ixs_val = eval_ixs(ixs_result, env)
        sp_val = int(sp_result.subs({sympy.Symbol(k): v for k, v in env.items()}))
        assert ixs_val == sp_val, f"Divergence at {env}"
```

**Known SymPy bug to work around**: SymPy issue
[#28744](https://github.com/sympy/sympy/issues/28744) — `Mod` incorrectly
squares inner `Mod` subexpressions when the variable has `integer=True`
assumption. The bug is in `sympy/core/mod.py` lines 166-172: factors of type
`Mod` are duplicated into both `mod_l` and `non_mod_l`, causing them to
appear squared. The fix (merged to `master` in Dec 2025) has not been included
in any SymPy release yet (latest release is 1.14.0, April 2025).

## Risks and Mitigations

| Risk | Impact | Mitigation |
|---|---|---|
| Simplification produces wrong results | Critical | Numerical equivalence oracle; fuzz testing |
| 64-bit rational overflow | Medium | Overflow check in rational ops; fallback to 128-bit |
| New expression patterns in future workloads | Medium | Grammar is extensible; add new node types as needed |
| Hash-consing table becomes bottleneck | Low | Linear probing with power-of-2 sizing; rehash threshold 70% |
| Simplification rules interact badly (infinite loops) | Medium | Depth limit on rewrite passes; monotonic rewrite ordering |

## Non-Goals

- General symbolic algebra (polynomial factoring, GCD, etc.)
- Floating-point arithmetic
- Calculus (differentiation, integration, series)
- Trigonometric or transcendental functions
- Matrix operations
- Equation solving
- Bindings beyond C++ and Python
