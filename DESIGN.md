# ixsimpl — Index Expression Simplifier

A specialized C library for simplifying integer arithmetic expressions
used in index computation, memory addressing, and loop bound calculation.

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
| Rounding | `floor()`, `ceiling()` | 25,601 |
| Modular | `Mod(a, b)` | 6,481 |
| Conditional | `Piecewise((val, cond), ..., (val, True))` | 1,136 |
| Min/Max | `Max(a, b)`, `Min(a, b)` | 1,140 |
| Bitwise | `xor(a, b)` | 116 |
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

## Architecture

```
┌──────────────────────────────────────────────────────┐
│                    Public C API                      │
│  ixs_ctx_create / ixs_parse / ixs_simplify / ...     │
├──────────────────────────────────────────────────────┤
│          Node Construction + Simplification          │
│  Constructors canonicalize bottom-up via shared      │
│  rule engine; ixs_simplify adds top-down pass with   │
│  assumptions. One rule implementation, not two.      │
├──────────────┬───────────────┬───────────────────────┤
│  Expression  │  Hash-consing │  Rational             │
│  DAG Nodes   │  Table        │  Arithmetic           │
├──────────────┴───────────────┴───────────────────────┤
│                Arena Allocator                       │
└──────────────────────────────────────────────────────┘
```

The diagram above shows the current engine architecture. Later sections
describe the shipped session/store public API: the lower layers stay the
same, while the public state handle is split into a long-lived store plus a
reusable session.

Node construction and simplification are **one logical layer**: every
constructor (e.g., `ixs_add`, `ixs_floor`) applies canonicalization rules
before hash-consing. This is intentional — it ensures all nodes in the DAG
are always in canonical form. `ixs_simplify()` runs an additional top-down
pass that leverages assumptions for bound-dependent rewrites.

**Implementation dependency split**: Public constructors (in `ctx.c`) call
rule functions (in `simplify.c`), which call internal node allocators (in
`node.c`). `node.c` never calls `simplify.c` — the dependency is one-way:
`ctx.c` → `simplify.c` → `node.c`. This prevents circular dependencies.

**Thread safety**: The library has no internal synchronization. A shared
`ixs_ctx` and any `ixs_session` bound to it are not safe for concurrent use
without external synchronization. Distinct stores share no state and can be
used concurrently without synchronization.

**Cross-context contract**: All `ixs_node*` arguments passed to any API
function must belong to the same store as the call handle: the `ctx` argument
for store-only APIs, or the store bound to the `ixs_session` argument for
session-taking APIs.
Passing a node from one store to a different store is **undefined behavior**
(dangling arena pointer, wrong hash table). Structural import is the only
supported cross-store bridge.

Runtime entry points that reject wrong-store nodes test pointer identity in the
destination store's intern table. The check is expected O(1) and never orders
or subtracts pointers from unrelated allocations.

**Depth limit**: The parser enforces a recursion depth limit (default 256) for
nested grammar recursion. Long chains of unary `-` and predicate `~` prefixes
are consumed iteratively. Trees built programmatically via the API have no
depth limit. The simplifier, printer, and `ixs_subs` traverse the DAG
recursively. `ixs_subs` uses a 256-slot direct-mapped memo cache (4 KB on the
stack) keyed by node pointer to avoid exponential re-traversal of shared
subexpressions; collisions only cause redundant work, never incorrect results.
Successful deterministic node transforms use a context-local open-addressed
cache keyed by source-node identity. Current slots memoize top-level expansion
and removal of an ADD constant for shifted bounds. Arena-backed storage stays
at or below 75% load, so hits and inserts are expected O(1). Successful results
survive session reset; failures and sentinels are not cached. Statistics reset
clears the cache so rule-hit counters remain observable.
For expressions built from the corpus (max depth 11) this is safe.
Deliberately constructing extremely deep trees (depth > ~10,000) via the API
may cause stack overflow. This is considered acceptable for the target domain.

### Layer 0: Memory — Arena Allocator

All expression nodes are allocated from a per-context arena. Nodes are never
individually freed; the entire arena is freed when the context is destroyed.
The `ixs_ctx` struct itself is emplaced into the main arena (built on the
stack, then memcpy'd in), so the store object does not need a separate heap
allocation. The hash-consing table still uses `calloc`-backed buckets today, so
`ixs_ctx_create` is not literally `calloc`-free. `ixs_ctx_destroy` snapshots
the arena to a local before freeing it. This eliminates per-node malloc/free
overhead and improves cache locality.

```c
typedef struct ixs_arena_chunk {
  char *base;            /* data region (immediately after header) */
  size_t used;
  size_t capacity;
  struct ixs_arena_chunk *next;
} ixs_arena_chunk;

typedef struct {
  ixs_arena_chunk *current;
  ixs_arena_chunk *spare;
  ixs_arena_chunk *inline_chunk;
  size_t min_chunk;      /* default 4096 */
  size_t fail_after;     /* internal deterministic OOM injection */
} ixs_arena;
```

Each heap-backed chunk is a **single `malloc`** — the `ixs_arena_chunk` header
is emplaced at the start of the block, followed by the data region aligned to
16 bytes. The main node arena uses only heap-backed chunks; session scratch
also has one inline chunk and may retain one detached heap chunk as `spare` for
reuse. Heap chunks grow by doubling (with overflow check — if doubling would
exceed `SIZE_MAX`, treat as OOM). Typical working set for one expression is
< 64 KB.

Tests can call the internal `ixs_arena_set_fail_after` hook to permit a fixed
number of allocation or grow operations before all later operations return
NULL. Injection applies even when an existing or inline chunk has capacity, so
tests do not depend on allocator warm-up. It is stored per arena, remains active
across save/restore, and is disabled by default; production behavior and
thread-safety therefore do not depend on global test state.

#### Scratch Arena

This subsection describes the current implementation after the first
context/session slice. Public callers own an `ixs_session`, which owns scratch
and diagnostics. Internally, the active session temporarily mirrors that state
onto `ixs_ctx` while legacy ctx-based helpers run, so the save/restore
programming model remains unchanged.

Smart constructors (`simp_add`, `simp_mul`, `simp_and`, `simp_or`, `simp_pw`)
and the parser flatten variadic children into temporary arrays before building
the final hash-consed node. These temporaries live on the active session's
scratch arena and are mirrored onto `ctx->scratch` only for the duration of the
bound public call. A save/restore API lets callers rewind the scratch arena
after the temporary data is consumed:

```c
typedef struct {
  ixs_arena_chunk *chunk;
  size_t used;
} ixs_arena_mark;

ixs_arena_mark ixs_arena_save(ixs_arena *a);
void ixs_arena_restore(ixs_arena *a, ixs_arena_mark m);
```

`ixs_arena_save` snapshots the current allocation position — returns
`{a->current, a->current ? a->current->used : 0}`. For an empty arena
(`a->current == NULL`) the mark is `{NULL, 0}`, and restoring to it frees
all chunks. `ixs_arena_restore` rewinds to that snapshot, logically freeing everything
allocated after the save point. Any chunks that were allocated between save
and restore are freed:

```c
void ixs_arena_restore(ixs_arena *a, ixs_arena_mark m) {
  while (a->current != m.chunk) {
    ixs_arena_chunk *doomed = a->current;
    a->current = doomed->next;
    free(doomed);
  }
  if (a->current)
    a->current->used = m.used;
}
```

In the common case (no new chunks allocated), restore is O(1) — just an
offset reset.

**Precondition**: The mark must have been obtained from the same arena via
`ixs_arena_save`. Passing a mark from a different arena or a destroyed arena
is undefined behavior (the loop walks off the chunk list).

Save/restore pairs nest naturally (LIFO). A function that saves, allocates
scratch space, then calls another function which also saves/allocates/restores
— the inner restore only rewinds to the inner save point, leaving the outer
function's scratch data intact. This is safe to arbitrary depth as long as
every save is paired with a restore in the same function scope, which is
guaranteed by the usage pattern (save at entry, restore before return).

**Scratch usage contract**: Only allocate from the scratch arena inside a
save/restore pair. Always use the wrapper/impl pattern (below) so that
restore is called on every exit path. The scratch arena is *not* for
long-lived data — anything that must survive the current function call
belongs in the main arena.

The scratch arena is separate from the main arena because permanent nodes
(created by `ixs_node_add`, etc.) are allocated from the main arena *during*
the window between scratch allocation and restore. Restoring the main arena
would destroy those nodes. The scratch arena holds only temporaries, so
restoring it is always safe.

**Arena grow**: Growing a scratch array is common enough to warrant a
dedicated operation. `ixs_arena_grow` extends an existing allocation in
place when possible, falling back to alloc + copy. Primarily intended for
the scratch arena, where the slow path wastes the old block and restore
reclaims it. Using grow on the main arena wastes the old block permanently,
which is acceptable when growth is rare and bounded (e.g. the error pointer
array doubles at most log2(n) times, totalling negligible waste).
Shrinking is not supported (`new_size` must be `>= old_size`).

```c
void *ixs_arena_grow(ixs_arena *a, void *ptr,
                      size_t old_size, size_t new_size,
                      size_t align) {
  if (!ptr)
    return ixs_arena_alloc(a, new_size, align);
  if (new_size < old_size)
    return NULL;
  /* Fast path: ptr is at the tip of the current chunk.
     Use offset arithmetic (ptr - base) to avoid pointer overflow UB. */
  if (a->current &&
      (char *)ptr >= a->current->base &&
      (size_t)((char *)ptr - a->current->base) + old_size
          == a->current->used) {
    size_t extra = new_size - old_size;
    if (extra <= a->current->capacity - a->current->used) {
      a->current->used += extra;
      return ptr; /* extended in place, no copy */
    }
  }
  /* Slow path: alloc new, copy, old space wasted. */
  void *p = ixs_arena_alloc(a, new_size, align);
  if (p)
    memcpy(p, ptr, old_size);
  return p;
}
```

The fast path is free — no copy, no waste. The `ptr - base` offset
comparison avoids pointer-addition overflow UB on 32-bit systems. The
`extra <= capacity - used` check avoids wrapping (since `used <= capacity`
is a maintained invariant). The slow path wastes the old block, but this
is harmless since scratch space is reclaimed on restore. Returns NULL on
OOM.

**Cleanup discipline — wrapper/impl split**: C has no RAII, and manually
calling `ixs_arena_restore` at every return site is fragile. The solution is
to split each function that uses scratch space into a thin wrapper (owns the
save/restore) and an inner impl (has unrestricted control flow):

```c
static ixs_node *simp_add_impl(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  size_t cap = 16;
  ixs_addterm *terms = ixs_arena_alloc(&ctx->scratch,
                                        cap * sizeof(*terms),
                                        sizeof(void *));
  if (!terms)
    return NULL; /* OOM */
  /* ... can return early from anywhere: */
  if (ixs_node_is_zero(a))
    return b;
  /* ... flatten children into terms[], growing as needed: */
  if (nterms >= cap) {
    size_t newcap = cap * 2;
    if (newcap <= cap || newcap > (size_t)-1 / sizeof(*terms))
      return NULL; /* overflow */
    terms = ixs_arena_grow(&ctx->scratch, terms,
                            cap * sizeof(*terms),
                            newcap * sizeof(*terms),
                            sizeof(void *));
    if (!terms)
      return NULL; /* OOM */
    cap = newcap;
  }
  /* coeff and nterms are computed during flattening (elided). */
  return ixs_node_add(ctx, coeff, nterms, terms);
}

ixs_node *simp_add(ixs_ctx *ctx, ixs_node *a, ixs_node *b) {
  ixs_arena_mark m = ixs_arena_save(&ctx->scratch);
  ixs_node *result = simp_add_impl(ctx, a, b);
  ixs_arena_restore(&ctx->scratch, m);
  return result;
}
```

The impl can have any number of early returns — sentinel propagation, NULL
checks, overflow bailouts — without worrying about cleanup. The wrapper is
mechanical and impossible to get wrong. This is essentially manual RAII: the
wrapper is the destructor scope, the impl is the body.

Alternatives and why they're worse here:

- **goto cleanup**: Viable for one or two exit points; painful when every
  other line can bail out (which is the case in our constructors with
  sentinel/NULL propagation checks).
- **Single-exit with result variable**: Forces deep nesting or threading a
  result through the whole function. Obscures the logic.
- **Cleanup macros**: Can't `return` from inside a macro scope without
  skipping the cleanup, so you're back to the same problem.

In practice, the initial allocation (16 elements) covers >99% of cases;
growth is rare, and when it happens the in-place fast path almost always
hits.

**OOM on scratch**: Scratch allocation failure is treated identically to
main-arena OOM — the impl returns NULL, which propagates through the
existing NULL-propagation rules. The wrapper always calls
`ixs_arena_restore`, even when the impl returned NULL, keeping the scratch
arena consistent. No error string is pushed (same as main-arena OOM — we
can't allocate memory for it).

**Error path cleanup**: With scratch arena, the `MAX_TERMS` limit and its
associated error paths (`"too many Piecewise cases"`, the `overflow` goto
labels that conflated term-count overflow with rational overflow) are
removed entirely. The only remaining failure mode for term accumulation is
OOM (NULL return).

**Scratch arena in the parser**: `parse_piecewise` collects `values[]` and
`conds[]` arrays of unknown length. Same wrapper/impl split:
`parse_piecewise` saves, calls `parse_piecewise_impl` (which has all the
early `return parse_error(...)` exits), then restores.

**Recursive calls**: A wrapper (e.g. `simp_add`) may call another wrapper
(`simp_mul`) which saves/restores its own scratch region. This is safe —
save/restore pairs nest in LIFO order, each wrapper restores only its own
mark. The scratch arena never leaks across wrapper boundaries.

**Lifecycle**: Initialized in `ixs_session_init`, restored to the base mark by
`ixs_session_reset`, and destroyed in `ixs_session_destroy`.

**Status**: Fully implemented. All smart constructors, the parser, `subs`,
`rewrite_impl`, and `walk` use session-backed scratch. The remaining internal
helpers still take `ixs_ctx *`, so public entry points bind the active session
onto the context on entry and copy the final scratch/diagnostic state back out
on exit.
`MAX_TERMS` and `ixs_limits.h` have been removed. OOM injection for
arena testing is tracked separately (bead 4-96o).

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
    IXS_CMP,         // comparison: a op b, returns 0 or 1
    IXS_AND,         // bitwise and(a, b)
    IXS_OR,          // bitwise or(a, b)
    IXS_NOT,         // logical not: (a == 0) ? 1 : 0
    IXS_ERROR,       // sentinel: domain error (div/0, overflow, etc.)
    IXS_PARSE_ERROR, // sentinel: syntax error from ixs_parse
} ixs_tag;

typedef enum {
    IXS_CMP_GT,      // >
    IXS_CMP_GE,      // >=
    IXS_CMP_LT,      // <
    IXS_CMP_LE,      // <=
    IXS_CMP_EQ,      // ==
    IXS_CMP_NE,      // !=
} ixs_cmp_op;
```

Each node is a small struct:

```c
typedef struct ixs_node {
    ixs_tag tag;
    uint32_t hash;        // precomputed, used for hash-consing
    union ixs_node_data {
        int64_t ival;                     // IXS_INT
        struct { int64_t p, q; } rat;     // IXS_RAT
        const char *name;                 // IXS_SYM (interned in arena)
        struct {                          // IXS_ADD
            struct ixs_node *coeff;       //   rational constant term
            uint32_t nterms;
            struct ixs_addterm *terms;    //   sorted array (see below)
        } add;
        struct {                          // IXS_MUL
            struct ixs_node *coeff;       //   rational constant factor
            uint32_t nfactors;
            struct ixs_mulfactor *factors; //  sorted array (see below)
        } mul;
        struct {                          // IXS_FLOOR, IXS_CEIL
            struct ixs_node *arg;
        } unary;
        struct {                          // IXS_MOD, IXS_MAX, IXS_MIN, IXS_XOR, IXS_CMP
            struct ixs_node *lhs;
            struct ixs_node *rhs;
            ixs_cmp_op cmp_op;           // used only for IXS_CMP; value ignored for other binary types
        } binary;
        struct {                          // IXS_PIECEWISE
            uint32_t ncases;
            struct ixs_pwcase *cases;     //  array of {value, condition}
        } pw;
        struct {                          // IXS_AND, IXS_OR
            uint32_t nargs;
            struct ixs_node **args;       // new nodes use exactly 2 args
        } logic;
        struct {                          // IXS_NOT
            struct ixs_node *arg;
        } unary_bool;
    } u;
} ixs_node;
```

`ixs_true(s)` returns the interned integer `1`, and `ixs_false(s)` returns the
interned integer `0`. The v1 binary format still accepts legacy true/false wire
tags and maps them to those integer constants during deserialization.

New `IXS_AND` and `IXS_OR` nodes are binary bitwise operators. The storage still
records `nargs` so old serialized n-ary logic nodes can be imported, but smart
constructors build two-child nodes.

Bitwise operations use unbounded integer two's-complement semantics, matching
Python and SymPy-style integer bitwise behavior. There is no fixed bit-width,
no signed/unsigned reinterpretation, and no wraparound in the core expression
model. `IXS_NOT` remains logical truthiness, not bitwise complement; adding
bitwise complement would require a distinct node.

Helper structs for compound nodes:

```c
typedef struct ixs_addterm {
    struct ixs_node *term;    // the non-constant subexpression
    struct ixs_node *coeff;   // rational coefficient (IXS_INT or IXS_RAT, nonzero)
} ixs_addterm;

typedef struct ixs_mulfactor {
    struct ixs_node *base;    // the non-constant base
    int32_t exp;              // nonzero integer exponent
} ixs_mulfactor;

typedef struct ixs_pwcase {
    struct ixs_node *value;   // branch value
    struct ixs_node *cond;    // branch condition (boolean expression)
} ixs_pwcase;
```

**Symbol interning**: Symbol names are copied into the arena and deduplicated.
The `name` pointer in `IXS_SYM` always points to arena-owned memory, so it
remains valid for the lifetime of the context regardless of whether the caller
frees the original input string.

**Hash-consing**: A global (per-context) hash table maps
`(tag, hash_of_children)` → `ixs_node*`. The table uses open addressing
with linear probing and rehashes at 70% load.

**Probe-before-allocate**: Each node constructor builds a stack-local
`ixs_node tmp`, populates its fields and hash, and probes the hash table
via `htab_lookup`. On hit (full structural comparison confirms match), the
existing pointer is returned with zero arena allocation. On miss, the
constructor arena-allocates the node, copies `tmp` into it, and inserts it
into the table. This avoids wasting arena memory on duplicate nodes.

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

**Division and Mod use floored (Python/SymPy) semantics, not C truncated
semantics.** This is critical for correctness when comparing against SymPy:

- `floor_div(a, b)` = floor(a / b), e.g., `floor_div(-7, 2) = -4` (not -3)
- `floor_mod(a, b)` = `a - b * floor_div(a, b)`, always non-negative when
  `b > 0`, e.g., `floor_mod(-7, 2) = 1` (not -1)

All results are reduced to lowest terms.

**Overflow**: All intermediate arithmetic is checked for overflow. On overflow
the enclosing constructor returns the sentinel node and appends an error (see
Error Model). Not UB, not assert. `INT64_MIN` is explicitly handled throughout:

- `neg(INT64_MIN)` → sentinel + error.
- `floor_div(INT64_MIN, -1)` → sentinel + error.
- `ixs_rat(s, INT64_MIN, q)` for any `q < 0` → sentinel + error (negating
  `p` overflows). Includes `q = -1, -2, ...`.
- `ixs_rat(s, p, INT64_MIN)` → sentinel + error (`-q` overflows).
- `gcd(|p|, |q|)` where `p == INT64_MIN` or `q == INT64_MIN` → the GCD
  implementation must handle this without computing `abs(INT64_MIN)`. Use
  binary GCD or special-case: `gcd(INT64_MIN, q)` treats `INT64_MIN` as
  `2^63` (its unsigned magnitude) for the purpose of reduction.

In practice the constants in this domain are small (< 2^20), so the slow path
should be rare. Rational comparison nevertheless includes a portable emulated
128-bit cross-multiply fallback when direct 64-bit multiplication would
overflow.

**Division by zero**: `ixs_rat(s, p, 0)` returns sentinel. `Mod(x, 0)` and
any `x / 0` during construction or parsing returns sentinel. `ixs_rat` with
`q < 0` normalizes to `(-p, -q)`.

**Mod divisor domain**: `Mod(x, b)` requires `b > 0`. A known nonpositive
constant returns `IXS_ERROR`. A symbolic divisor remains representable without
a positivity proof, but substitution or assumption-aware simplification
returns `IXS_ERROR` when it proves `b <= 0`. Unknown sign remains unresolved;
range and modular-fact queries use no Mod-specific facts until positivity is
proven. This matches the corpus, where every Mod divisor is a positive constant
or is provably positive under assumptions.

### Layer 3: Parser

Recursive descent parser for the SymPy output format. A configurable
recursion depth limit (default 256) prevents stack overflow on maliciously
deep inputs. The grammar is small:

```
expr     = bit_or
bit_or   = bit_and ('|' bit_and)*
bit_and  = sum ('&' sum)*
sum      = term (('+' | '-') term)*
term     = unary (('*' | '/') unary)*
unary    = '-'* atom
atom     = INT | SYMBOL
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
cmp_expr = '~'* cmp_body
cmp_body = expr cmp_op sum | 'True' | 'False' | '(' cond ')' | sum
cmp_op   = '>' | '<' | '>=' | '<=' | '==' | '!='
```

**Bare expressions in conditions**: The grammar allows a bare arithmetic
expression in condition context (the `| sum` alternative in `cmp_expr`). This handles
corpus patterns like `$MMA_LHS_SCALE | $MMA_RHS_SCALE | $MMA_SCALE_FP4` in
Piecewise conditions, where integer-valued flag variables are used as boolean
tests. A bare expression `e` in condition context is desugared to `e != 0`
(i.e., `ixs_cmp(s, e, IXS_CMP_NE, ixs_int(s, 0))`). The `|` and `&`
operators in condition grammar coerce both operands to 0/1 predicates first.
The resulting `IXS_OR` and `IXS_AND` nodes are still integer bitwise operators,
but on 0/1 operands they have the same truth tables as boolean OR and AND.
The same tokens are also accepted as bitwise integer operators in expression
grammar. In predicate comparisons, the left operand may be a full bitwise
expression for mask-like spellings (`x & 3 == 1`). A leading bare flag followed
by a symbolic condition operand remains condition shorthand (`x | y == 0`
means `x != 0 | y == 0`); write `(x | y) == 0` for a bitwise var-var
comparison. The right operand uses arithmetic grammar unless a bitwise
expression is parenthesized (`x == (y | 1)`), preserving the older condition
shorthand `x > 0 | y > 0`.

Symbols: any identifier matching `[A-Za-z_$][A-Za-z0-9_$]*`. All parsed as
`IXS_SYM`. The `$` and `_` prefixes carry no special semantics.

The parser accepts SymPy's `ceiling`; the C API uses `ixs_ceil` for brevity.
Similarly, the parser accepts `True`/`False`; both parse to integer `1`/`0`.
The API convenience functions `ixs_true`/`ixs_false` return the same integer
nodes.

Integer literals: sequences of digits. Rationals are not parsed directly —
they arise from `3/8` being parsed as `IXS_INT(3) / IXS_INT(8)` and
immediately folded to `IXS_RAT(3, 8)`.

The parser builds the DAG directly via the hash-consing table.

### Layer 4: Simplification Engine

Simplification is **table-driven**. Each node type has an ordered array of
`ixs_rule` entries (function pointer, name, needs-bounds flag). The
`try_rules()` dispatch walks the array, tries each rule, records an
`IXS_STATS` hit when one fires, and returns. Rules that require bounds
are skipped when `bnds == NULL`.

Each `simp_*` constructor (e.g., `simp_floor`, `simp_mod`) applies the
fast pre-checks (sentinel propagation, const fold, identity) directly,
constructs the node, then calls `try_rules(ctx, NULL, node, *_rules)`.
For the top-down rewrite pass, each `simp_*_bnds` variant takes an
optional `ixs_bounds *` and calls `try_rules(ctx, bnds, ...)` so
bounds-dependent rules also fire. `rewrite_impl` is just:
```c
case IXS_FLOOR:
    return simp_floor_bnds(ctx, bnds, rewrite(ctx, arg, ...));
```
There is one rule table per type, used by both construction and rewriting.

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

Batch simplification adds a batch-local open-addressed cache above the
per-walk direct-mapped memo. It keys rewritten subtrees by interned node
identity and grows at 75% occupancy, giving expected O(1) lookup across roots
and fixed-point iterations. One cache serves one immutable fact context only.
Piecewise branch forks use independent local memos, so branch facts cannot
escape into siblings or later roots. Cache allocation failure preserves the
batch API's atomic OOM contract: every output becomes NULL.
Growth is deferred until a root rewrite returns, outside nested scratch-arena
marks; rule-local restores cannot invalidate cache storage.

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
- `ADD(... + k * ADD(c + Σ di*ui) ...)` → distribute `k` and flatten
  (enables `(x+y) - (x+y) → 0` by flattening `MUL(-1, ADD(x, y))`)
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
- Collect like bases: if `bi == bj`, merge `ei + ej` (checked for `int32_t`
  overflow; on overflow → sentinel + error)
- Drop factors with `ei == 0` (they contribute 1)
- If `coeff == 0`, return `0`
- `expr * 1` → `expr`
- Pull constant factors out of ADD: `2 * (a + b)` is kept as-is (don't
  distribute). Distribution is not performed by the simplifier.
  Use `ixs_expand` to distribute on demand.

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
When bounds are available, `round_extract_add` uses `is_integer_with_divinfo`
and `is_known_divisible` to extract addends with rational coefficients that
are provably integer via congruence (e.g. `floor(x/3 + K/32)` ->
`K/32 + floor(x/3)` when `Mod(K, M) == 0` for any `M` with `32 | M`,
since `32 | K` makes `K/32` integer).  The helper `addterm_is_integer_valued`
encapsulates this check for both the detection and extraction passes.

Both `is_integer_with_divinfo` and `is_known_divisible` handle multi-factor
MUL nodes: for `p/q * f1^e1 * ... * fn^en`, each positive-exponent factor
is checked for integer-valued-ness, and any single factor whose congruence
absorbs the remaining denominator suffices to prove the whole product
integer-valued (or divisible by a given modulus).  This is a sufficient
OR-of-factors test, not full product factorization: `6 | (2*3)` cannot
be proved when neither factor alone is divisible by 6.

`is_known_divisible` also handles `Max` and `Min` when both operands are
provably divisible; either selected value then preserves the divisor.

```
floor(C/D + sum(ci * ti / D))  →  floor(C'/D + sum(ci * ti / D))
    when every ti is integer-valued, D is symbolic, all terms share D^{-1},
    and C' = C - (C mod gcd(g, L)) where g = gcd of base numerator
    coefficients and L = lcm of rational coefficient denominators.
    (Proof: N = sum(ni*ti) is always a multiple of g; adding
    r < gcd(g, L) to N cannot push past the next floor boundary.)
```

The symbolic-denominator constant-drop rule is implemented in
`floor_drop_const_sym`, also registered in `floor_rules[]`.

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
Mod((p/q)*(c + sum(ci*ti)), m)           → Mod(c' + sum(ci'*ti), m)
                     when all scaled coefficients are integral
Mod(a*m + b, m)     where a contains no IXS_MOD node → Mod(b, m)
Mod(g*x + r, g*m)   where g > 1, 0 <= r < g,
                     all terms integer   → g*Mod(x, m) + r
Mod(c*x, c*m)       where c > 1         → c*Mod(x, m)
(p/q)*Mod(q*x, q*m) where q > 1, m > 0,
                     x is integer-valued → p*Mod(x, m)

(reverse direction, in simp_add — recognize_mod)
c*E - c*N*floor(E/N)                    → c*Mod(E, N)
c*N*ceil(E/N) - c*E                     → c*Mod(-E, N)
c*E - c*D*floor(E/D)                    → c*Mod(E, D)     (D symbolic)
c*D*ceil(E/D) - c*E                     → c*Mod(-E, D)    (D symbolic)

(forward direction, in simp_add — cancel_floor_mod_pairs)
ci*m*floor(E/m) + ci*Mod(E, m)          → ci*E

(bounds-aware ADD cancellation)
c*Mod(A, m) - c*Mod(B, m)               → 0
                     when m > 0 is literal and A-B ≡ 0 (mod m)
```

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

The forward cancellation uses two verification strategies:

1. **floor(A/m) == floor_node** — reconstructs the expected floor via
   `simp_floor(simp_div(A, m))` and checks hash-consed pointer equality.
   Robust against eager floor rewrites (e.g. `round_pull_in_denom`
   collapsing `floor(floor(x/3)/2)` into `floor(x/6)`).

2. **m * floor_arg == A** — distributes `m` over the floor argument using
   `distribute_mul_decompose`, which decomposes compound inverse MUL bases
   (e.g. `K * (K/2)^{-1} → 2`) to enable symbolic cancellation.

#### 4.5.1 Opposite-Coefficient MUL-ADD Cancellation

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

#### 4.6 Piecewise Rules

Piecewise requires `n >= 1`. The last case should have condition `True`
(catch-all default). If after eliminating `False` branches no cases remain,
the result is `IXS_ERROR` (no defined value).

```
Piecewise((v, True))                → v
Piecewise((v, False), rest...)      → Piecewise(rest...)
Piecewise((v, c), (v, d), rest...)  → Piecewise((v, c | d), rest...)
                                      (same value, merge conditions)
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

**Sentinel handling**: Sentinels do not eagerly propagate through Piecewise
(see Error Model). A sentinel value in a branch whose condition folds to
`False` is silently dropped. A sentinel condition in an unreachable branch
(preceded by a `True` condition) is silently dropped. Only when the sentinel
is in the "live" path does the Piecewise become sentinel.

#### 4.7 Max / Min Rules

```
Max(a, a)       → a
Max(a, b)       where a >= b provable → a
Max(1, x)       where x > 0 provable → Max(1, x) (keep)
                where x >= 1 provable → x

Min(a, a)       → a
Min(a, b)       where a <= b provable → a
Min(a, b)       where a,b constant   → min(a, b)
```

#### 4.8 XOR Rules

```
xor(a, a)       → 0
xor(a, 0)       → a
xor(0, b)       → b
xor(a, xor(a,b)) → b  (either outer or inner operand order)
xor(c1, c2)     → c1 ^ c2  (constant fold)
xor(a, b)       → a + b    when a,b >= 0 and known bits do not overlap

k*xor(a, b + 2^n) - k*xor(a, b)
                → k*(2^n - 2*(a & 2^n))
                  when bit n of the pre-toggle operand is known zero
```

The known-bit query merges exact interval facts and propagates low 64-bit
facts through `ADD`, positive power-of-two `MUL`, `floor(x/2^n)` for
non-negative `x`, and `Mod(x, 2^n)`. `MUL` and `Mod` only produce bitfacts
for integer-valued expressions. The XOR-to-ADD rule is deliberately
bounds-aware: both operands must be proven non-negative with finite int64
bounds, because the known-bit lattice tracks only the low 64 bits. The
XOR-delta rule leaves the largest int64 power-of-two delta untouched to avoid
overflowing temporary arithmetic.

#### 4.9 Bitwise And/Or And Logical Not

```
0 & x           → 0
-1 & x          → x
0 | x           → x
-1 | x          → -1
c1 & c2         → c1 & c2  (constant fold)
c1 | c2         → c1 | c2  (constant fold)
1 & bool        → bool
1 | bool        → 1
~0              → 1
~nonzero_const  → 0
~(~bool)        → bool
~(~x)           → x != 0
~(a > b)        → a <= b
bool & ~bool    → 0
bool | ~bool    → 1
```

`IXS_AND` and `IXS_OR` are binary bitwise integer operators. They are also
boolean operators when both operands are known 0/1-valued. `IXS_NOT` is logical
truthiness, not bitwise complement: it returns `1` exactly when its operand is
zero and `0` otherwise.

#### 4.10 Comparison Simplification

```
a > b   → (a - b) > 0   (normalize to compare against 0)
```

Then apply constant folding when `a - b` reduces to a constant, or bound
analysis when the sign of `a - b` is provable.

### Layer 5: Bound Analysis (Phase 4)

Many simplification rules require knowing whether a subexpression is
non-negative, positive, or bounded. A lightweight interval analysis pass:

- **Variable storage**: Per-variable bounds live in a growable array on the
  scratch arena (starts at 16 slots, doubles on overflow).  Lookup is O(n)
  linear scan by interned name pointer.  If profiling shows this is hot,
  the array can be swapped for an open-addressing hash map keyed on the
  same pointer — the `ixs_bounds` interface is designed to make that a
  drop-in replacement.
- **Interval bounds**: `$T0 >= 0`, `$T0 < 256`, etc. — the simplifier
  extracts interval bounds from comparison assumptions automatically
- **Expression range facts**: explicit or derived facts of the form
  `range(expr) = [lo, hi]` are stored in the same bounds context as
  symbol intervals.  They are keyed by hash-consed expression node and by an
  expanded canonical alias, so `2*(A + 8*B)` and `2*A + 16*B` can prove the
  same range when both normalize to the same expanded form.  Comparison
  assumptions over integer-valued expressions also materialize expression
  range facts; for example `-C + expr <= 0` records `expr <= C`.
- **Nonzero facts**: normalized `expr != 0` assumptions are retained in a
  pointer-keyed expression set. The set is copied by bounds forks and fact
  substitution, so reciprocal guards can use both incoming disequalities and
  branch-local conditions. A direct zero range for the same expression is a
  detected contradiction.
- **Contradiction cache**: the detected-empty result is cached until any bound,
  congruence, bit, nonzero, or expression-range mutation. Query hits are O(1);
  a miss performs the full variable, expression-pair, and exclusion scan.
- **Modular congruence**: `Mod(K, 32) == R` — the simplifier tracks
  `K ≡ R (mod 32)`.  Multiple assumptions on the same symbol merge via CRT
  (Chinese Remainder Theorem).  Pure divisibility (`R == 0`) is the common
  special case; `Mod(K, 256) == 0` implies `Mod(K, 32) == 0`.
- **Modular entailment**: `ixs_check` uses the same congruence facts for
  `Mod(expr, m) == r` and `Mod(expr, m) != r` queries.  It proves exact
  symbol remainders when the stored modulus is a multiple of the query
  modulus, and proves zero remainders for composite expressions through
  the same sufficient divisibility predicate used by simplification rules.
- **Atomic predicate checks**: `ixs_check` and `ixs_check_facts` accept a
  normalized comparison or the canonical integer `1`/`0` produced when a
  smart constructor resolves a comparison. Other non-comparison expressions
  remain unknown. Contradictory fact domains never prove even a constant
  predicate.
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

  Initial storage is symbol-level in `ixs_var_bound`. Expression-level
  bitfacts are computed on demand for constants, symbols, comparisons,
  logical NOT, and bounded-depth `AND`/`OR`/`XOR` trees. A pointer-keyed side
  table can be added later if expression-level assumptions need to persist.
  Branch-local facts are copied by `ixs_bounds_fork`, so `Piecewise` branch
  assumptions remain isolated.
- `floor(x)`: if `lo <= x <= hi`, then `floor(lo) <= floor(x) <= floor(hi)`
- `Mod(x, m)`: result in `[0, m-1]` when `m > 0` and `x` is integer-valued
- `ceiling(x/m)`: result >= 0 when `x >= 0` and `m > 0`

**Compound assumption ingestion**: All predicate-bearing entry points use one
bounded iterative walker: `ixs_simplify`, `ixs_simplify_batch`, `ixs_check`,
`ixs_check_integer_valued`, `ixs_check_defined`, `ixs_get_pow2_fact`,
`ixs_range`, `ixs_facts_assume_pred`, and `ixs_facts_assume_preds`. Each
predicate root may be a CMP, a canonical true/false node, or an AND tree whose
leaves have those forms. True
contributes no fact; false marks the bounds as contradictory. Supporting these
constants preserves predicates that simplify before ingestion, such as
`(x & 0) == 0`. The walker visits at most 1024 nodes per root and therefore does
not consume one C call frame per nested conjunction.

OR, NOT, other node kinds, NULL or sentinel nodes, malformed CMP/AND nodes, and
nodes from another context are rejected with an `assumptions:` diagnostic.
Legacy array ingestion discards the whole temporary bound context when any
entry is rejected or fails; it never queries a partially ingested prefix.
`ixs_facts_assume_preds` applies the whole array to one fork and commits only
after every tree succeeds; `ixs_facts_assume_pred` is its one-element form.
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
see them: empty interval intersections, duplicate expression bounds that
intersect to empty, and future bitfact conflicts such as a bit known both zero
and one. Query APIs treat detected contradictions as unknown/no-result rather
than manufacturing a concrete answer. Simplification may return `IXS_ERROR` and
append a diagnostic when the reporting path has enough context, but callers must
not rely on every contradictory assumption set producing an error string.

Not all contradictions are detectable. Cross-variable constraints like
`x >= y, y >= x + 1` require relational constraint solving, which is out of
scope. When a contradiction goes undetected, the result is undefined with
respect to that inconsistent assumption set; passing consistent assumptions is
the caller's responsibility.

This enables rules like:

- **Equality substitution**: when a symbol's bounds collapse to a point
  interval `[c, c]` (from `sym == c` assumption, or derived via
  `sym >= c` ∧ `sym <= c`), the rewriter replaces the symbol with integer
  `c` throughout the expression tree. This cascades through constant
  folding, collapsing `ceiling(M/256)` to `1` when `M == 256`, etc.
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
- `c*Mod(A,m) - c*Mod(B,m)` → `0` when `A-B ≡ 0 (mod m)` is proven
  for the shared positive literal modulus

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
  conservative helpers such as `ixs_bounds_is_pow2_positive` and
  `ixs_bounds_is_known_divisible`.

**Algebraic rewrites** (no bounds needed):

- `Mod(c1*t1 + ... + c, q)` → `Mod(terms, q) + c` when each `|ci|`
  divides `q`, each `ti` is integer-valued, and `0 < c < gcd(|ci|)`.
  (Ported from IREE Wave's `symbol_utils.py`, corrected: use `gcd` not
  `min` for the multi-term case.)

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
- **Bitwise XOR**: propagation requires both operands to be provably integer
  and nonnegative. Finite upper bounds determine the possible high-bit span;
  operand known bits then tighten the result's required and possible bits. If
  either nonnegative operand is unbounded above, the result is `[0,+inf)`.
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
  assumption set.
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
  facts, then evaluates `AND`, `OR`, and `NOT` with conservative tri-state
  truth tables. `AND` is true only when every child is true and false when any
  child is false; `OR` is true when any child is true and false only when every
  child is false; `NOT` inverts true and false. Predicate-valued `Piecewise`
  nodes that do not collapse during fact-backed simplification remain
  unknown. Numeric bitwise `AND`/`OR` nodes are rejected with a `predicate:`
  diagnostic rather than interpreted as boolean trees. The evaluator uses a
  1024-frame stack and an 8192-node visit budget.
- **Total fact-backed equivalence** (`ixs_equivalent_facts`, Python
  `Context.equivalent`, C++ `Facts::equivalent`): requires both operands to be
  defined over every valuation admitted by the incoming facts before pointer
  identity can prove equality. It then tries fact-backed simplification of the
  difference, expansion followed by simplification under the shared fact
  environment, flattened order-independent matching of predicate `AND`/`OR`
  terms, and a query-specific congruence proof for otherwise identical
  comparisons of `Mod` residuals. Congruence is deliberately not a generic
  equality rule: a divisible residual delta does not prove arbitrary
  comparisons or `x == 0`. A nonzero constant difference or predicates with
  opposite proven truth values return `FALSE`; other failed sufficient proofs
  return `UNKNOWN`. Contradictory facts never prove equivalence. Recursive
  predicate-shape comparison has depth 32, 4096 proof visits, and at most 1024
  flattened terms, so this API is not an unbounded theorem prover.
- **Narrow fact-backed algebra helpers** (`ixs_constant_difference_facts`,
  `ixs_affine_decompose_facts`, `ixs_finite_difference_facts`, and
  `ixs_split_additive_constant_facts`): prove definedness over the complete
  incoming fact domain, then simplify, expand, and simplify again in that same
  environment. Constant differences and additive constants must fit
  `int64_t`; affine coefficients may be exact rational nodes. Affine
  decomposition accepts only one symbol and rejects any nonlinear occurrence
  or residual reference to it. Finite difference substitutes
  `symbol + step` once and may return a symbolic result such as `2*i + 1`;
  callers decide whether that result is loop invariant. A step referencing the
  target symbol is rejected. Unsupported shapes, undefined partitions,
  contradictory facts, representation overflow, and bounded-walk or expansion
  limits fail conservatively. These helpers do not add relational, polyhedral,
  or SMT reasoning.
- **Public integrality queries**: `ixs_node_is_integer_valued` is a
  conservative structural test. It rejects negative powers and rational
  coefficients without consulting facts. `ixs_check_integer_valued` and
  `ixs_check_integer_valued_facts` add interval and congruence reasoning, so
  `K/32` is proven integral under `Mod(K, 32) == 0`. A `Piecewise` is proven
  integral only when every branch not proven unreachable has an integral
  value. `TRUE` and `FALSE` are universal proofs; a failed sufficient proof is
  `UNKNOWN`, while an exact noninteger rational point may return `FALSE`.
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
  `Context.try_exact_divide`, C++ `Facts::try_exact_divide`): reuses the same
  divisibility proof and returns a canonical expanded quotient only after that
  proof succeeds. Its result separates `PROVEN`, proven `NOT_EXACT`,
  insufficient or contradictory `UNKNOWN`, and domain/OOM `ERROR`. Only
  `PROVEN` carries a quotient. Negative divisors preserve quotient sign;
  `INT64_MIN` is handled without taking its signed magnitude. Every `ERROR`
  reached through a valid fact set appends a session diagnostic.
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

**Limitation**: general interval propagation remains non-relational. For
`floor(x/K)` with `x < K-1, K >= 2`, the bounds engine sees
`x ∈ [0, INT64_MAX]` and `K ∈ [2, INT64_MAX]` independently, so `x/K`
has an unbounded interval. Targeted rules can query normalized comparisons for
specific proofs such as `0 <= x < K` in `Mod(x,K)`; arbitrary cross-variable
interval projection remains out of scope.

## Error Model

The library uses a three-tier error model: NULL, and two distinct sentinel
node types.

### Tier 1: NULL — Out of Memory (catastrophic)

All constructors and parse entry points return `NULL` when the arena cannot
grow. This is unrecoverable. No error string is set (we can't allocate memory
for it). NULL propagates silently: any constructor that receives a NULL
argument returns NULL immediately without side effects.

### Tier 2: Parse Error Sentinel (`IXS_PARSE_ERROR`)

Returned by `ixs_parse` when the input is syntactically malformed (unexpected
token, unmatched parentheses, unknown function name, recursion depth limit
exceeded) or when a parsed root has the wrong kind. There is one parse-error
sentinel per store (singleton). Diagnostics are appended to the active session
error list.

Only the parse entry points produce this sentinel. Constructors never produce
it.

### Tier 3: Domain Error Sentinel (`IXS_ERROR`)

Returned by constructors when an operation is mathematically undefined:
division by zero, `Mod(x, 0)`, rational overflow, `ixs_rat(..., p, 0)`,
integer literal overflow during parsing of a syntactically valid number.
There is one domain-error sentinel per store (singleton). Diagnostics are
appended to the active session error list.

The parse entry points can return this sentinel when the input is
syntactically valid but contains a domain error (e.g., `"1/0 + x"`).

### Propagation rules

Both sentinels propagate identically through constructors:

| Input | Behavior |
|---|---|
| Any constructor receives a sentinel arg | Returns that sentinel silently (no new error) |
| Any constructor receives NULL arg | Returns NULL silently |
| Two sentinel args (different kinds) | Returns `IXS_PARSE_ERROR` (highest sentinel priority) |
| NULL + any sentinel | Returns NULL (NULL always wins) |
| Operation causes domain error | Returns `IXS_ERROR`, appends error to list |

**Priority**: `NULL` > `IXS_PARSE_ERROR` > `IXS_ERROR`. When multiple error
tiers are present in the arguments, the highest-priority one wins. This
ensures that parse errors are never masked by domain errors, and OOM is
never masked by anything.

Only the operation that **originates** the error appends to the error list.
Propagation through downstream constructors is silent.

**Piecewise exception** — sentinels do NOT eagerly propagate through
`ixs_pw`. A Piecewise branch may contain a sentinel value or sentinel
condition without poisoning the entire expression, similar to LLVM's poison
semantics in `select`:

- If a condition folds to `False`, the branch is dropped — sentinel in its
  value disappears harmlessly.
- If a condition folds to `True`, the branch value (sentinel or not) becomes
  the result.
- If the first non-eliminated condition is a sentinel, the Piecewise cannot
  determine which branch to take and becomes that sentinel.
- `Piecewise((sentinel, x > 0), (42, True))` with `x = -1` simplifies to
  `42`, not sentinel.

This enables batch processing: one expression with a div/0 in a dead
Piecewise branch doesn't invalidate the other 608 expressions.

### Error List API (Current Implementation)

The functions below describe the current implementation. Sentinel tiers and
propagation rules remain the same; the mutable diagnostic list now lives on
`ixs_session`.

```c
// Query errors accumulated since last clear.
// ixs_session_error returns NULL if index >= ixs_session_nerrors(s).
size_t      ixs_session_nerrors(ixs_session *s);
const char *ixs_session_error(ixs_session *s, size_t index);
void        ixs_session_clear_errors(ixs_session *s);

// Check sentinel kind
bool        ixs_is_error(const ixs_node *node);        // true for either sentinel
bool        ixs_is_parse_error(const ixs_node *node);   // true only for IXS_PARSE_ERROR
bool        ixs_is_domain_error(const ixs_node *node);  // true only for IXS_ERROR
```

In the current implementation, error strings are arena-allocated in the
session diagnostics arena. They remain valid until
`ixs_session_clear_errors`, `ixs_session_reset`, or `ixs_session_destroy`.
Each string includes the error kind and location, e.g.:
- `"parse error at offset 7: unexpected token 'bar'"`
- `"parse error: recursion depth limit (256) exceeded"`
- `"division by zero"`
- `"Mod: divisor is zero"`
- `"Mod: divisor is negative"`
- `"Mod: divisor is not positive under assumptions"`
- `"rational overflow in multiply"`
- `"integer literal overflow at offset 42"`

### Summary Table

| Condition | Return | Error list | Example |
|---|---|---|---|
| OOM | `NULL` | unchanged | arena exhausted |
| Syntax error | `IXS_PARSE_ERROR` | appended | `"foo bar +"` |
| Domain error | `IXS_ERROR` | appended | `1/0`, `Mod(x,0)`, overflow |
| Valid parse with domain error | `IXS_ERROR` | appended | `"1/0 + x"` |
| NULL parser input | `IXS_PARSE_ERROR` | unchanged | `ixs_parse(s, NULL, len)` |
| NULL node input to NULL-safe APIs | `NULL` | unchanged | propagation |
| Sentinel input | same sentinel | unchanged | propagation |
| Sentinel in Piecewise value | Piecewise kept | unchanged | dead branch |
| `ixs_print(sentinel)` | writes `"<error>"` | unchanged | round-trip safe |

### ixs_parse Return Values

| Input | Return |
|---|---|
| Valid expression | `ixs_node*` (valid) |
| Syntax error | `IXS_PARSE_ERROR` sentinel |
| Syntactically valid but contains domain error | `IXS_ERROR` sentinel |
| OOM | `NULL` |

## Core API (Session Split Snapshot)

This section records the first context/session landing and the core surface it
introduced. It is not a complete API reference: later sections in this
document extend it with the currently shipped kind-aware parse, traversal,
structural import, and structural serialization APIs.

```c
// Long-lived store: owns interned nodes, hash-consing, and singletons.
typedef struct ixs_ctx ixs_ctx;
typedef struct ixs_node ixs_node;

// Reusable workspace: owns scratch and diagnostics. The public object is a
// fixed-size 4 KB blob so callers can stack-allocate it.
#define IXS_SESSION_BYTES 4096u
typedef union {
  void *ptr_align;
  unsigned char storage[IXS_SESSION_BYTES];
} ixs_session;

// Lifecycle. ixs_ctx_create returns NULL on OOM.
ixs_ctx *ixs_ctx_create(void);
void ixs_ctx_destroy(ixs_ctx *ctx);  // NULL-safe
void ixs_session_init(ixs_session *s, ixs_ctx *ctx);
void ixs_session_reset(ixs_session *s);
void ixs_session_destroy(ixs_session *s);

// Diagnostics and sentinel checks.
size_t ixs_session_nerrors(ixs_session *s);
const char *ixs_session_error(ixs_session *s, size_t index);
void ixs_session_clear_errors(ixs_session *s);
bool ixs_is_error(const ixs_node *node);        // true for either sentinel
bool ixs_is_parse_error(const ixs_node *node);  // true only for IXS_PARSE_ERROR
bool ixs_is_domain_error(const ixs_node *node); // true only for IXS_ERROR

// Parse a SymPy-format expression. Errors append to the session list.
// The current parser surface also includes ixs_parse_expr(),
// ixs_parse_pred(), ixs_node_is_expr(), and ixs_node_is_pred(); see
// "Shipped API Surface" below.
ixs_node *ixs_parse(ixs_session *s, const char *input, size_t len);

// Construct expressions programmatically. All node arguments must belong to
// the context bound to s.
ixs_node *ixs_int(ixs_session *s, int64_t val);
ixs_node *ixs_rat(ixs_session *s, int64_t p, int64_t q);
ixs_node *ixs_sym(ixs_session *s, const char *name);
ixs_node *ixs_add(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_sub(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_neg(ixs_session *s, ixs_node *a);
ixs_node *ixs_mul(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_div(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_floor(ixs_session *s, ixs_node *x);
ixs_node *ixs_ceil(ixs_session *s, ixs_node *x);
ixs_node *ixs_mod(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_max(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_min(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_xor(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_pw(ixs_session *s, uint32_t n, ixs_node **values,
                 ixs_node **conds);
ixs_node *ixs_cmp(ixs_session *s, ixs_node *a, ixs_cmp_op op, ixs_node *b);
ixs_node *ixs_and(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_or(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_not(ixs_session *s, ixs_node *a);
ixs_node *ixs_true(ixs_session *s);
ixs_node *ixs_false(ixs_session *s);

// Assumption roots must be CMP or canonical true/false nodes, or AND trees with
// those leaves, built in the same context. True is a no-op and false is a
// contradiction. OR, NOT, malformed, NULL, sentinel, and other roots are
// rejected atomically with an `assumptions:` diagnostic. Trees are walked with
// a 1024-node limit per root. Pass NULL/0 for no assumptions.
// NOTE: if the fixed-point iteration limit is reached without convergence, the
// current best result is returned and an error is appended to the session list.
ixs_node *ixs_simplify(ixs_session *s, ixs_node *expr,
                       ixs_node *const *assumptions, size_t n_assumptions);

// Introspection — node must not be NULL:
ixs_tag ixs_node_tag(const ixs_node *node);       // returns the node's type tag
int64_t ixs_node_int_val(const ixs_node *node);   // IXS_INT value; UB if wrong tag
uint32_t ixs_node_hash(const ixs_node *node);     // precomputed content hash

// Pointer equality (O(1) — hash-consing guarantees that structurally
// identical expressions within the same context share the same pointer).
// Only valid for nodes from the same ixs_ctx. NULL arguments are allowed:
// ixs_same_node(NULL, NULL) returns true, ixs_same_node(NULL, x) returns false.
bool ixs_same_node(const ixs_node *a, const ixs_node *b);

// Substitution — single-pass: replaces all occurrences of `target` in
// `expr` with `replacement`. target can be any node (symbol, constant,
// subexpression). Matching uses pointer equality (O(1) per node thanks
// to hash-consing). Does NOT re-substitute into the replacement itself
// (no recursive expansion). NULL/sentinel propagation applies to expr,
// target, and replacement as with constructors.
ixs_node *ixs_subs(ixs_session *s, ixs_node *expr,
                   ixs_node *target, ixs_node *replacement);

// Simultaneous multi-target substitution.  Replaces targets[i] with
// replacements[i] in a single walk.  No replacement is recursed into,
// so {A->B, B->C} on A+B yields B+C, not C+C.  Duplicate targets:
// first matching entry wins.  Thin wrapper around the same engine as
// ixs_subs (nsubs=1 delegates here).
ixs_node *ixs_subs_multi(ixs_session *s, ixs_node *expr, uint32_t nsubs,
                         ixs_node *const *targets,
                         ixs_node *const *replacements);

// Cross-store import: rebuild `src` into the store bound to `s`.
// Sentinels map to the destination store's sentinels. If `src` already
// belongs to the destination store, it is returned directly.
ixs_node *ixs_import_node(ixs_session *s, const ixs_node *src);

// Batch import: on success writes all imported nodes to `out` and returns
// true. On failure returns false, leaves `out` unchanged, and may already
// have interned some successfully imported nodes into the destination store.
bool ixs_import_many(ixs_session *s, const ixs_node *const *src,
                     size_t count, ixs_node **out);

// Output — snprintf-like: returns the number of chars that would be written
// (excluding '\0'). If buf is NULL or bufsize is 0, returns the required
// length without writing. Output is always null-terminated when bufsize > 0.
// Sentinel prints as "<error>". NULL expr returns 0 and does not modify buf.
size_t ixs_print(const ixs_node *expr, char *buf, size_t bufsize);  // SymPy
size_t ixs_print_c(const ixs_node *expr, char *buf, size_t bufsize); // C code

// Batch: simplify multiple expressions **in place**, sharing the same
// assumption-derived bounds and rewritten-subtree cache. Both are scoped to
// this call and fact context.
// Each exprs[i] is overwritten with its simplified form.
// NULL/sentinel entries in exprs are left unchanged. Assumptions use the
// shared compound-predicate contract above. Rejection sets every entry to
// IXS_ERROR.
// OOM: if any simplification hits OOM, ALL entries in exprs are set to
// NULL (the arena is likely exhausted, so no expression is trustworthy).
// Precondition: exprs must be non-NULL when n > 0. A NULL assumptions pointer
// with n_assumptions > 0 is rejected. No-op when n == 0.
void ixs_simplify_batch(ixs_session *s, ixs_node **exprs, size_t n,
                        ixs_node *const *assumptions, size_t n_assumptions);

// Entailment check: is a boolean expression provably true or false
// under the given assumptions?  Uses interval propagation and modular
// congruence facts, but no rewriting.  Returns IXS_CHECK_TRUE, IXS_CHECK_FALSE, or
// IXS_CHECK_UNKNOWN.  Lighter than ixs_simplify for pure truth queries.
typedef enum { IXS_CHECK_TRUE, IXS_CHECK_FALSE, IXS_CHECK_UNKNOWN } ixs_check_result;
typedef enum {
    IXS_EXACT_DIVIDE_PROVEN,
    IXS_EXACT_DIVIDE_NOT_EXACT,
    IXS_EXACT_DIVIDE_UNKNOWN,
    IXS_EXACT_DIVIDE_ERROR
} ixs_exact_divide_status;
typedef struct {
    ixs_exact_divide_status status;
    ixs_node *quotient;
} ixs_exact_divide_result;
ixs_check_result ixs_check(ixs_session *s, ixs_node *expr,
                           ixs_node *const *assumptions, size_t n_assumptions);
bool ixs_node_is_integer_valued(const ixs_node *expr);
ixs_check_result ixs_check_integer_valued(
    ixs_session *s, ixs_node *expr,
    ixs_node *const *assumptions, size_t n_assumptions);
ixs_check_result ixs_check_defined(
    ixs_session *s, ixs_node *expr,
    ixs_node *const *assumptions, size_t n_assumptions);

// Power-of-two fact query under assumptions.  Returns the strongest provable
// fact, or UNKNOWN when no fact is proven.
typedef enum {
    IXS_POW2_UNKNOWN,
    IXS_POW2_OR_ZERO,
    IXS_POW2_POSITIVE
} ixs_pow2_fact;
typedef struct {
    uint64_t known_zero;
    uint64_t known_one;
    ixs_pow2_fact pow2;
} ixs_known_bits;
ixs_pow2_fact ixs_get_pow2_fact(ixs_session *s, ixs_node *expr,
                                ixs_node *const *assumptions,
                                size_t n_assumptions);

// Inclusive range query under assumptions.  Returns false when unknown.
typedef struct {
    bool has_lower;
    bool has_upper;
    int64_t lower_p, lower_q;  // exact lower endpoint if has_lower
    int64_t upper_p, upper_q;  // exact upper endpoint if has_upper
} ixs_range_result;
bool ixs_range(ixs_session *s, ixs_node *expr,
               ixs_node *const *assumptions, size_t n_assumptions,
               ixs_range_result *out);

// Session-owned fact sets. The handle is a store-owned tombstone until ctx
// destruction; its proof payload is usable only until session reset/destroy.
// Failed mutation poisons the set, and later queries fail conservatively.
typedef struct ixs_facts ixs_facts;
ixs_facts *ixs_facts_create(ixs_session *s);
bool ixs_facts_assume_pred(ixs_facts *facts, ixs_node *pred);
bool ixs_facts_assume_range(ixs_facts *facts, ixs_node *expr,
                            const ixs_range_result *range);
bool ixs_facts_derive_affine(ixs_facts *facts, ixs_node *base, int64_t scale,
                             int64_t offset, ixs_node *derived);
bool ixs_facts_substitute(ixs_facts *dst, const ixs_facts *src,
                          ixs_node *target, ixs_node *replacement);
bool ixs_facts_substitute_multi(ixs_facts *dst, const ixs_facts *src,
                                uint32_t nsubs,
                                ixs_node *const *targets,
                                ixs_node *const *replacements);
ixs_node *ixs_simplify_facts(ixs_facts *facts, ixs_node *expr);
void ixs_simplify_batch_facts(ixs_facts *facts, ixs_node **exprs, size_t n);
ixs_check_result ixs_check_facts(ixs_facts *facts, ixs_node *expr);
ixs_check_result ixs_check_predicate_facts(ixs_facts *facts,
                                           ixs_node *predicate);
ixs_check_result ixs_equivalent_facts(ixs_facts *facts,
                                      ixs_node *lhs, ixs_node *rhs);
bool ixs_constant_difference_facts(ixs_facts *facts, ixs_node *lhs,
                                   ixs_node *rhs, int64_t *delta);
bool ixs_affine_decompose_facts(ixs_facts *facts, ixs_node *expr,
                                ixs_node *symbol, ixs_node **coefficient,
                                ixs_node **residual);
bool ixs_finite_difference_facts(ixs_facts *facts, ixs_node *expr,
                                 ixs_node *symbol, ixs_node *step,
                                 ixs_node **difference);
bool ixs_split_additive_constant_facts(ixs_facts *facts, ixs_node *expr,
                                       ixs_node **residual,
                                       int64_t *constant);
ixs_check_result ixs_check_integer_valued_facts(ixs_facts *facts,
                                                ixs_node *expr);
ixs_check_result ixs_check_defined_facts(ixs_facts *facts, ixs_node *expr);
ixs_check_result ixs_check_divisible_facts(ixs_facts *facts,
                                           ixs_node *expr,
                                           int64_t modulus);
ixs_exact_divide_result ixs_try_exact_divide_facts(ixs_facts *facts,
                                                   ixs_node *expr,
                                                   int64_t divisor);
ixs_pow2_fact ixs_get_pow2_fact_facts(ixs_facts *facts, ixs_node *expr);
bool ixs_get_known_bits_facts(ixs_facts *facts, ixs_node *expr,
                              ixs_known_bits *out);
bool ixs_get_symbol_congruence_facts(ixs_facts *facts, ixs_node *symbol,
                                     int64_t *modulus, int64_t *residue);
ixs_check_result ixs_check_congruent_facts(ixs_facts *facts,
                                           ixs_node *expr,
                                           int64_t modulus,
                                           int64_t residue);
bool ixs_range_facts(ixs_facts *facts, ixs_node *expr,
                     ixs_range_result *out);

// Expand: distribute MUL over ADD recursively (sum-of-products form).
// Recurses into subexpressions (floor args, piecewise branches, etc.).
// The canonical form keeps products factored; call this when you need
// expanded form for term-by-term analysis.  NULL-safe.
ixs_node *ixs_expand(ixs_session *s, ixs_node *expr);

// Rule-hit statistics (requires -DIXS_STATS at compile time).
// When disabled, nstats returns 0, stat returns 0/NULL, reset is a no-op.
// Stats are per-context and not thread-safe for a shared context.
size_t   ixs_ctx_nstats(ixs_ctx *ctx);      // distinct rules that fired
uint64_t ixs_ctx_stat(ixs_ctx *ctx, size_t index, const char **name);
void     ixs_ctx_stats_reset(ixs_ctx *ctx);  // zero all counters
size_t   ixs_nrules(void);                   // total registered rule names
const char *ixs_rule_name(size_t index);     // NULL if out of range
```

**Rule-hit statistics** (`-DIXS_STATS`): When compiled with `IXS_STATS`,
the `try_rules()` dispatch automatically records a hit count for each
rule that fires, using the rule name from the `ixs_rule` table. Counts
are stored in a per-context open-addressing hash table (128 slots, keyed
on rule-name pointer identity). Rules not dispatched through `try_rules`
(e.g., ADD/MUL canonicalization) use the `IXS_STAT_HIT(ctx)` macro
directly. CMake: `-DENABLE_STATS=ON`. The Python
binding exposes `ctx.stats()` (returns a `{name: count}` dict) and
`ctx.stats_reset()`. The Python wheel does not enable stats by default;
build from source with `-DENABLE_STATS=ON` for profiling.

Usage pattern:

```c
ixs_ctx *ctx = ixs_ctx_create();
ixs_session s;
ixs_session_init(&s, ctx);

// Assumptions are just boolean expressions built with the same API
ixs_node *T0  = ixs_sym(&s, "$T0");
ixs_node *T1  = ixs_sym(&s, "$T1");
ixs_node *M   = ixs_sym(&s, "M");
ixs_node *N   = ixs_sym(&s, "N");
ixs_node *K   = ixs_sym(&s, "K");
ixs_node *assumptions[] = {
    ixs_cmp(&s, T0, IXS_CMP_GE, ixs_int(&s, 0)),   // $T0 >= 0
    ixs_cmp(&s, T0, IXS_CMP_LT, ixs_int(&s, 256)), // $T0 < 256
    ixs_cmp(&s, T1, IXS_CMP_GE, ixs_int(&s, 0)),   // $T1 >= 0
    ixs_cmp(&s, T1, IXS_CMP_LT, ixs_int(&s, 4)),   // $T1 < 4
    ixs_cmp(&s, M,  IXS_CMP_GE, ixs_int(&s, 1)),   // M >= 1
    ixs_cmp(&s, N,  IXS_CMP_GE, ixs_int(&s, 1)),   // N >= 1
    ixs_cmp(&s, K,  IXS_CMP_GE, ixs_int(&s, 1)),   // K >= 1
};
size_t n_assumptions = sizeof(assumptions) / sizeof(assumptions[0]);

ixs_node *expr = ixs_parse(&s, input, strlen(input));
if (!expr) { /* OOM */ return; }
if (ixs_is_parse_error(expr)) {
    fprintf(stderr, "syntax: %s\n", ixs_session_error(&s, 0));
    ixs_session_clear_errors(&s);
    return;
}

ixs_node *simplified = ixs_simplify(&s, expr, assumptions, n_assumptions);
if (!simplified) { /* OOM */ return; }

if (ixs_is_domain_error(simplified)) {
    for (size_t i = 0; i < ixs_session_nerrors(&s); i++)
        fprintf(stderr, "error: %s\n", ixs_session_error(&s, i));
    ixs_session_clear_errors(&s);
} else {
    char buf[4096];
    ixs_print(simplified, buf, sizeof(buf));
    printf("%s\n", buf);
}

ixs_session_destroy(&s);
ixs_ctx_destroy(ctx);  // frees everything
```

### Node Introspection API

Nodes are opaque — `struct ixs_node` is internal. The public C API exposes
structural introspection through `ixs_node_tag`, type-specific field
accessors, generic child access, and scratch-backed tree walks.

Interned node payloads are immutable. Sentinel checks, pointer equality,
printers, and every structural accessor therefore accept `const ixs_node *`.
Child accessors still return `ixs_node *`: changing that return type would
break source compatibility and would prevent direct composition with the
constructor, transform, proof-query, walk, and pointer-array APIs, whose
historic handle types remain mutable. The mutable spelling is only a handle
compatibility contract; opaque node payloads are never caller-mutable.

**Representation mismatch with sympy**: sympy's `Add(a, 2*b, 3)` has
`args = [a, 2*b, 3]` — flat list of sub-expressions. ixsimpl's ADD is
`coeff=3, terms=[{a,1},{b,2}]` — structured. Similarly, sympy MUL has
`Pow(x,-1)` as a first-class arg; ixsimpl stores exponents as `int32_t`
on each mulfactor. The C API exposes ixsimpl's actual structure; the
Python binding layer reconstructs sympy-compatible `.args` if needed.
The accessor API is tied to the current node layout; changes to the
internal representation of ADD/MUL are API-breaking.

#### Type-specific accessors

One function per field. Caller must check `ixs_node_tag` first — calling
the wrong accessor is UB (same contract as `ixs_node_int_val`). No
allocation, no ctx needed.

```c
/* Only valid when tag is IXS_RAT. */
int64_t ixs_node_rat_num(const ixs_node *node);
int64_t ixs_node_rat_den(const ixs_node *node);

/* Only valid when tag is IXS_SYM.  Pointer valid for ctx lifetime. */
const char *ixs_node_sym_name(const ixs_node *node);

/* Only valid when tag is IXS_ADD.  i must be < nterms.
 * ADD = coeff + sum(term_coeff[i] * term[i]). */
ixs_node *ixs_node_add_coeff(const ixs_node *node);
uint32_t ixs_node_add_nterms(const ixs_node *node);
ixs_node *ixs_node_add_term(const ixs_node *node, uint32_t i);
ixs_node *ixs_node_add_term_coeff(const ixs_node *node, uint32_t i);

/* Only valid when tag is IXS_MUL.  i must be < nfactors.
 * MUL = coeff * product(base[i] ^ exp[i]). */
ixs_node *ixs_node_mul_coeff(const ixs_node *node);
uint32_t ixs_node_mul_nfactors(const ixs_node *node);
ixs_node *ixs_node_mul_factor_base(const ixs_node *node, uint32_t i);
int32_t ixs_node_mul_factor_exp(const ixs_node *node, uint32_t i);

/* Only valid when tag is IXS_FLOOR, IXS_CEIL, or IXS_NOT. */
ixs_node *ixs_node_unary_arg(const ixs_node *node);

/* Only valid when tag is IXS_MOD, IXS_MAX, IXS_MIN,
 * IXS_XOR, or IXS_CMP. */
ixs_node *ixs_node_binary_lhs(const ixs_node *node);
ixs_node *ixs_node_binary_rhs(const ixs_node *node);

/* Only valid when tag is IXS_CMP. */
ixs_cmp_op ixs_node_cmp_op(const ixs_node *node);

/* Only valid when tag is IXS_PIECEWISE.  i must be < ncases. */
uint32_t ixs_node_pw_ncases(const ixs_node *node);
ixs_node *ixs_node_pw_value(const ixs_node *node, uint32_t i);
ixs_node *ixs_node_pw_cond(const ixs_node *node, uint32_t i);

/* Only valid when tag is IXS_AND or IXS_OR.  i must be < nargs. */
uint32_t ixs_node_logic_nargs(const ixs_node *node);
ixs_node *ixs_node_logic_arg(const ixs_node *node, uint32_t i);
```

~20 functions, all trivial one-liners into the internal union fields
(except `ixs_node_unary_arg` which branches on tag internally).

#### Generic child access

```c
/* Number of child node pointers.  Leaves return 0. */
uint32_t ixs_node_nchildren(const ixs_node *node);

/* i-th child node.  i must be < ixs_node_nchildren(node). */
ixs_node *ixs_node_child(const ixs_node *node, uint32_t i);
```

Single point of truth for "which child-node pointers does this node
have?" — used by the walk and available to FFI callers for custom
traversal without callbacks.  Child order matches the type-specific
accessors:

| Tag | nchildren | order |
|-----|-----------|-------|
| ADD | 1 + 2*nterms | coeff, (term_coeff[0], term[0]), ... |
| MUL | 1 + nfactors | coeff, base[0], base[1], ... |
| binary | 2 | lhs, rhs |
| unary | 1 | arg |
| PW | 2*ncases | (value[0], cond[0]), ... |
| AND/OR | nargs | arg[0], arg[1], ... |
| leaves | 0 | — |

Non-node data (MUL exponents, CMP operator) is not exposed through
this API — use the type-specific accessors for that.  The generic
child API is intended for traversal, not for structural operations
like hashing, equality, or printing.

#### Tree walk

```c
/* Callback action: controls walk behavior after visiting a node. */
typedef enum {
  IXS_WALK_CONTINUE,  /* recurse into children */
  IXS_WALK_SKIP,      /* skip this node's children (pre-order only) */
  IXS_WALK_STOP       /* stop the entire walk */
} ixs_walk_action;

/* Callback must return exactly one of the three values above.
 * Any other return value is undefined behavior. */
typedef ixs_walk_action (*ixs_visit_fn)(ixs_node *node, void *userdata);

/* Pre-order: visit node, then recurse into children.
 * Returns root on completion, the stopping node on STOP, NULL if root
 * is NULL or the explicit scratch-backed traversal stack cannot grow.
 * s must be non-NULL when root is non-NULL.
 * Sentinels (ERROR, PARSE_ERROR) are visited as leaves; the callback
 * must check ixs_node_tag before using type-specific accessors.
 * SKIP prevents descent into children. */
ixs_node *ixs_walk_pre(ixs_session *s, ixs_node *root,
                       ixs_visit_fn fn, void *userdata);

/* Post-order: recurse into children, then visit node.
 * Same return/NULL/sentinel semantics as ixs_walk_pre.
 * SKIP is a no-op in post-order (children already visited). */
ixs_node *ixs_walk_post(ixs_session *s, ixs_node *root,
                        ixs_visit_fn fn, void *userdata);
```

**Return value**:
- `root` — walk completed, all reachable nodes visited.
- other non-NULL — callback returned STOP on that node.
- `NULL` — root was NULL or the scratch-backed explicit stack ran out of
  memory.

The caller distinguishes NULL-root from OOM because they know what they
passed. The edge case where STOP fires on root itself (returns `root`,
same as completion) is detectable via userdata if it matters.

No dedup: the walk follows the tree shape, not the DAG. Hash-consed
graphs with heavy sharing can have exponentially more tree paths than
unique nodes, so callers doing exhaustive collection (e.g.
`free_symbols`) should maintain their own visited set keyed on pointer
identity. Callers that don't need dedup (printing, conversion) get the
fast path without paying for a hash set.

`s` provides the scratch arena used by the iterative implementation's
explicit stack. This keeps walk depth bounded by available arena memory
instead of the C call stack, so deep trees no longer risk stack overflow.
For non-NULL roots, `s` must be non-NULL. The only failure mode for
non-NULL roots is scratch-stack OOM, reported as `NULL`.

Use cases:
- `ixs_walk_pre`: top-down — pattern matching with subtree-skipping,
  symbol-dependency checks ("does symbol X appear?" — stop early),
  conversion to external representations. Replaces sympy's
  `preorder_traversal`.
- `ixs_walk_post`: bottom-up — numeric evaluation, size/depth
  computation, any transform that needs children results first.

#### Contracts

- **NULL node**: passing NULL to any type-specific accessor is UB.
- **Wrong tag**: calling a type-specific accessor on the wrong tag is UB
  (same as `ixs_node_int_val`).
- **Invalid index**: out-of-range index arguments are UB. Implementations
  contain `assert()` for debug builds but no runtime checks in release.
- **Walk preconditions**: `s` and `fn` must be non-NULL. `root` may be
  NULL (returns NULL). The callback must not destroy `s` or its bound
  store. All other operations (constructors, simplify, subs, parse) are
  safe — nodes are immutable, and scratch arena save/restore nests
  correctly via LIFO.

## Performance Design

### Why this can be 100-1000x faster than SymPy

1. **No Python overhead**: Every SymPy operation goes through Python's object
   model, GIL, reference counting, and dynamic dispatch. A single `floor(x+1)`
   in SymPy creates multiple Python objects and calls `__new__`, `__init__`,
   `__hash__`, `__eq__` in Python. In C, it's a hash table lookup and a
   pointer.

2. **Hash-consing eliminates redundant work**: The 615 expressions share most
   of their subexpressions. In SymPy, each expression re-creates and
   re-simplifies common subtrees. With hash-consing, `ceiling(M/128)` is
   created once, stored once, and every expression that uses it gets the
   same pointer for free.

3. **Arena allocation**: Zero per-node malloc/free overhead. Excellent cache
   locality.

4. **No wasted generality**: SymPy checks for trigonometric identities,
   logarithmic simplification, polynomial factoring, etc. on every expression.
   This library checks only for the ~30 rules that actually apply.

5. **Batch mode**: Processing all 615 expressions in one context means the
   hash-consing table is warmed up, and later expressions (which are variants
   of earlier ones) are nearly free.

### Target performance

| Metric | SymPy (current) | Target |
|---|---|---|
| 615 expressions total | 41.4 s | < 50 ms |
| Average per expression | 68 ms | < 0.1 ms |
| Worst case | 388 ms | < 5 ms |

### Memory budget

Estimated peak memory for one `ixs_ctx` processing all 615 corpus expressions
in batch mode (the primary use case):

- Unique nodes (after hash-consing): ~10,000-30,000
- Node size: ~64 bytes average
- Hash table: ~128 KB
- Arena: ~2-4 MB
- Error list, symbol table: negligible
- **Total: < 8 MB per context**

### Performance invariants

Hot paths — node construction, interning, simplification, ownership
validation, fact/proof queries, walker callbacks — must not execute work
linear in total arena/ctx state. Two size axes matter: `n`, the size of
the expression being processed (any bound in `n` is acceptable), and `A`,
the total allocated state of the context (hot paths must not depend on it).

A function whose cost grows with `A` is a *scan* and carries a tag in a
comment immediately above its definition:

```c
/* scan: arena */
```

The tag must be a standalone comment immediately above the definition —
only comments and whitespace, no blank line, between. Tags are read from
AST comment nodes, so tag-shaped string literals and prose are inert.

Registered scan types (in `SCAN_TYPES` in `scripts/check_hotpaths.py`):

- `arena`: cost grows with total live arena chunks/bytes.
- `ctx`: cost grows with ctx-wide table state. Reserved; no instances yet.

Adding a scan type is one line in `SCAN_TYPES` plus the tag above the
function plus an update to this list, same commit. Tags with unregistered
types fail the check, so a typo cannot silently pass.

Amortized O(1) mechanisms are not scans: hash-table growth rehashes, and
`ixs_arena_restore`, whose chunk walk is proportional to the work being
rolled back rather than to `A`.

`scripts/check_hotpaths.py` enforces the invariant. It builds the static
call graph of `src/*.[ch]` with tree-sitter-c, propagates scan-taint
backward from tagged functions, and fails with a witness call path when a
hot function transitively reaches a scan. Public API functions are hot
roots by default; the lifecycle and bulk-IO exceptions are listed in the
script. A `/* hot */` tag pins the contract on an internal helper. The
check runs in pre-commit and as the ctest target `check_hotpaths` (the
ctest instance skips silently when the tree-sitter Python modules are not
installed; pinned versions live in `scripts/requirements-check.txt`).

Known blind spots, by design: calls through function pointers and calls
to external (libc) functions are assumed scan-free, so walker callbacks
must honor the hot contract on their own. Function-like macros are
modeled as pseudo-functions — their bodies are re-parsed for calls, so
scans reached through a macro are caught; same-name macro variants
(conditional compilation) union their edges, a sound over-approximation.
Tags are human classification; the checker only propagates it. The
empirical backstop is scaling benchmarks over the corpus, which catch
data-dependent blowups that no static classification can see.

## Build and CI

**CMake options**:

- `ENABLE_ASAN` (default `OFF`): Build with AddressSanitizer
  (`-fsanitize=address -fno-omit-frame-pointer`).

```bash
cmake -B build -DCMAKE_BUILD_TYPE=Debug -DENABLE_ASAN=ON
cmake --build build
ctest --test-dir build
```

**GitHub Actions** (`.github/workflows/ci.yml`) runs on every push to
`master` and on pull requests:

| Job | What it does |
|-----|-------------|
| Release | Build + test with optimizations |
| Debug + ASAN | Build + test under AddressSanitizer |
| Python bindings + fuzz | Build extension with ASAN, run Hypothesis fuzz tests |
| Lint | `pre-commit` (clang-format, whitespace, REUSE) |
| REUSE compliance | License metadata check |

## File Structure

```
ixsimpl/
├── include/
│   └── ixsimpl.h            # public C API (single header)
├── src/
│   ├── arena.c              # arena allocator
│   ├── arena.h
│   ├── rational.c           # exact rational arithmetic
│   ├── rational.h
│   ├── node.c               # node creation, hash-consing, canonical forms
│   ├── node.h
│   ├── parser.c             # recursive descent parser
│   ├── parser.h
│   ├── simplify.c           # rewrite rules engine
│   ├── simplify.h
│   ├── expand.c             # MUL-over-ADD distribution
│   ├── expand.h
│   ├── bounds.c             # bound storage, propagation, assumption extraction
│   ├── bounds.h
│   ├── interval.c           # interval arithmetic
│   ├── interval.h
│   ├── print.c              # output formatters
│   ├── print.h
│   ├── import.c             # cross-store structural import
│   ├── serialize.c          # stable binary codec
│   ├── walk.c               # scratch-backed tree traversal
│   ├── internal.h
│   └── ctx.c                # context/session management, public API impl
├── bindings/
│   ├── cpp/
│   │   └── ixsimpl.hpp      # C++ header-only wrapper
│   └── python/
│       ├── _ixsimpl.c       # CPython extension module
│       └── ixsimpl/
│           ├── __init__.py
│           ├── _ixsimpl.pyi # type stubs
│           └── sympy_conv.py
├── test/
│   ├── test_arena.c
│   ├── test_rational.c
│   ├── test_parser.c
│   ├── test_import.c
│   ├── test_serialize.c
│   ├── test_introspect.c
│   ├── test_bounds.c
│   ├── test_simplify.c
│   ├── test_expand.c
│   ├── test_edge_cases.c
│   ├── test_corpus.c
│   ├── test_accessors.py
│   ├── test_python.py
│   ├── test_sympy_conv.py
│   ├── conftest.py
│   ├── corpus.txt
│   ├── corpus_expected.txt
│   └── corpus_assumptions.txt # shared assumption set for corpus tests
├── bench/
│   └── bench_corpus.c       # benchmark: individual or batch corpus simplify
├── scripts/
│   ├── amalgamate.py        # generate ixsimpl_amalg.c
│   ├── check_exports.py     # verify public symbol surface
│   ├── gen_expected.py      # generate corpus_expected.txt via SymPy
│   └── requirements-gen.txt # pinned SymPy version for generation
├── ixsimpl_amalg.c          # generated single-TU distribution file
├── CMakeLists.txt
├── pyproject.toml           # Python package build (PEP 517)
├── REUSE.toml               # licensing metadata
├── README.md
└── DESIGN.md
```

Estimated total: 5,000-8,000 lines of C, ~500 lines C++ header, ~800 lines
Python extension.

## Language Bindings

The binding sketches below mirror the current session-based API. `Context`
owns the long-lived store plus an embedded reusable session, and node-producing
operations route through that session. The code blocks are illustrative
subsets, not exhaustive dumps of the shipped wrapper surface; consult
`bindings/cpp/ixsimpl.hpp` and the Python stubs for the full API.

### C++ Binding — `ixsimpl.hpp`

A thin header-only RAII wrapper over the C API. No additional runtime cost.

```cpp
namespace ixs {

class Context {
    ixs_ctx *ctx_;
    ixs_session session_;
public:
    Context() : ctx_(ixs_ctx_create()) {
        if (!ctx_) throw std::bad_alloc();
        ixs_session_init(&session_, ctx_);
    }
    ~Context() {
        ixs_session_destroy(&session_);
        ixs_ctx_destroy(ctx_);
    }
    Context(const Context&) = delete;
    Context& operator=(const Context&) = delete;

    ixs_ctx *raw() const { return ctx_; }
    ixs_session *session() { return &session_; }
    const ixs_session *session() const { return &session_; }

    size_t nerrors() const { return ixs_session_nerrors(&session_); }
    const char *error(size_t i) const { return ixs_session_error(&session_, i); }
    void clear_errors() { ixs_session_clear_errors(&session_); }
};

class Expr {
    ixs_ctx *ctx_;
    ixs_session *session_;
    ixs_node *node_;
public:
    Expr(ixs_ctx *ctx, ixs_session *session, ixs_node *node)
        : ctx_(ctx), session_(session), node_(node) {}

    static Expr parse(Context &ctx, std::string_view input) {
        return {ctx.raw(), ctx.session(),
                ixs_parse(ctx.session(), input.data(), input.size())};
    }
    static Expr parse_expr(Context &ctx, std::string_view input) {
        return {ctx.raw(), ctx.session(),
                ixs_parse_expr(ctx.session(), input.data(), input.size())};
    }
    static Expr parse_pred(Context &ctx, std::string_view input) {
        return {ctx.raw(), ctx.session(),
                ixs_parse_pred(ctx.session(), input.data(), input.size())};
    }
    static Expr sym(Context &ctx, const char *name) {
        return {ctx.raw(), ctx.session(), ixs_sym(ctx.session(), name)};
    }
    static Expr integer(Context &ctx, int64_t v) {
        return {ctx.raw(), ctx.session(), ixs_int(ctx.session(), v)};
    }

    Expr simplify(const Expr *assumptions, size_t n_assumptions) const {
        std::vector<ixs_node*> raw(n_assumptions);
        for (size_t i = 0; i < n_assumptions; i++)
            raw[i] = assumptions[i].raw();
        return {ctx_, session_,
                ixs_simplify(session_, node_, raw.data(), raw.size())};
    }
    Expr simplify() const {
        return {ctx_, session_, ixs_simplify(session_, node_, nullptr, 0)};
    }
    Expr subs(Expr target, Expr repl) const {
        return {ctx_, session_,
                ixs_subs(session_, node_, target.node_, repl.node_)};
    }

    Expr operator+(Expr rhs) const {
        return {ctx_, session_, ixs_add(session_, node_, rhs.node_)};
    }
    Expr operator-(Expr rhs) const {
        ixs_node *neg = ixs_mul(session_, ixs_int(session_, -1), rhs.node_);
        return {ctx_, session_, ixs_add(session_, node_, neg)};
    }
    Expr operator*(Expr rhs) const {
        return {ctx_, session_, ixs_mul(session_, node_, rhs.node_)};
    }
    Expr operator-() const {
        return {ctx_, session_,
                ixs_mul(session_, ixs_int(session_, -1), node_)};
    }
    bool operator==(Expr rhs) const { return ixs_same_node(node_, rhs.node_); }

    std::string str() const {
        if (!node_) return {};
        size_t n = ixs_print(node_, nullptr, 0);
        std::string s(n + 1, '\0');
        ixs_print(node_, s.data(), n + 1);
        s.resize(n);
        return s;
    }

    bool is_null() const { return node_ == nullptr; }
    bool is_error() const { return node_ && ixs_is_error(node_); }
    bool is_parse_error() const { return node_ && ixs_is_parse_error(node_); }
    bool is_domain_error() const { return node_ && ixs_is_domain_error(node_); }
    bool is_expr() const { return node_ && ixs_node_is_expr(node_); }
    bool is_pred() const { return node_ && ixs_node_is_pred(node_); }
    bool is_integer_valued() const {
        return node_ && ixs_node_is_integer_valued(node_);
    }
    explicit operator bool() const { return node_ && !ixs_is_error(node_); }

    ixs_node *raw() const { return node_; }
    ixs_ctx *raw_ctx() const { return ctx_; }
    ixs_session *raw_session() const { return session_; }
};

} // namespace ixs
```

Key properties:
- `Context` owns both the long-lived store and one embedded reusable session.
  RAII cleans up both on destruction. Constructor throws `std::bad_alloc` on
  OOM.
- `Expr` is a lightweight value type (three pointers: store, session, node).
  Cheap to copy. **`Expr` must not outlive its `Context`** — destroying a
  `Context` invalidates all `Expr` values created from it (dangling pointers).
- `operator bool()` returns `true` only for valid, non-error expressions.
  `is_null()` checks OOM, `is_parse_error()`/`is_domain_error()` check
  specific sentinels, `is_error()` checks either.
- `parse_expr()` and `parse_pred()` expose the kind-aware parse surface;
  `parse()` remains the backward-compatible expression parser.
- `Expr::is_integer_valued()` exposes structural classification, while
  `Expr::check()`, `check_integer_valued()`, `check_defined()`,
  `get_pow2_fact()`, and `range()` consume an optional assumption array.
  `Expr::expand()` exposes distribution. `Context::facts()` returns a
  lightweight session-owned `Facts` wrapper whose `assume_range()` and
  `derive_affine()` expose explicit range ingestion and whose `simplify()`,
  `simplify_batch()`, `check()`, `check_integer_valued()`, `check_defined()`,
  `check_divisible()`, `get_pow2_fact()`, and `range()` expose every
  fact-backed transform and core proof query.
  `get_known_bits()`, `get_symbol_congruence()`, and `check_congruent()` expose
  the low-64 and query-specific modular interfaces without adding wrapper-side
  reasoning. `Facts::substitute()` and `Facts::substitute_multi()` mutate a
  destination wrapper from a source fact set and mirror the transactional C
  transfer contract.
  `Expr::simplify(const Facts&)` is the expression-oriented spelling.
  `Facts::try_exact_divide()` returns an `ExactDivideResult` containing the
  four-way status and a nullable `Expr` quotient; errors remain available
  through the owning `Context` diagnostics.
  `Facts::constant_difference()`, `affine_decompose()`,
  `finite_difference()`, and `split_additive_constant()` mirror the narrow
  fact-backed C helpers and fill their output references only on success.
- `Expr::raw_const()` supplies a const-qualified node view for inspection and
  serialization. `raw()` remains mutable-typed for source compatibility with
  older consumers and node-producing C APIs; neither permits payload mutation.
- Operator overloading for natural expression building.
- No heap allocations in expression construction or simplification beyond
  what the C library does internally. (`str()` allocates a `std::string`.)
- NULL and sentinel propagate through operators (same as C API).
- **Cross-context contract** applies: all `Expr` values passed to an
  operation (including assumptions in `simplify()`) must belong to the
  same `Context`. Mixing contexts is undefined behavior.

### Python Binding — `_ixsimpl.c`

A CPython C extension module (no pybind11/ctypes dependency). Exposes three
Python types: `Context`, `Expr`, and `Facts`.

```python
import ixsimpl

ctx = ixsimpl.Context()

T0 = ctx.sym("$T0")
M  = ctx.sym("M")
assumptions = [T0 >= 0, T0 < 256, M >= 1]

expr = ctx.parse("128*floor($T0/64) + 4*floor(Mod($T0, 64)/16)")
result = expr.simplify(assumptions=assumptions)
print(result)              # SymPy-compatible string
print(result.to_c())       # C code string

facts = ctx.facts()
for assumption in assumptions:
    facts.assume(assumption)
result = expr.simplify(facts=facts)
batch = [expr, x % 16]
ctx.simplify_batch(batch, facts=facts)

# Programmatic construction
x = ctx.sym("x")
y = ctx.sym("y")
e = ixsimpl.floor(x + y) + 3
print(e.simplify(assumptions=assumptions))

# Module-level convenience functions
e2 = x % 4                  # equivalent to ixsimpl.mod(x, 4)
e3 = ixsimpl.max_(x, y)   # trailing _ avoids shadowing builtin max
e4 = ixsimpl.min_(x, y)
e5 = ixsimpl.pw((x, x >= 0), (-x, ctx.true_()))  # piecewise
cond = ixsimpl.and_(x >= 0, y >= 0)               # bitwise on 0/1 predicates
cond2 = ixsimpl.or_(x >= 0, y >= 0)
mask = x & 3                  # equivalent to ixsimpl.and_(x, 3)
flags = x | y                 # equivalent to ixsimpl.or_(x, y)
cond3 = ixsimpl.not_(x >= 0)
e5 = ixsimpl.ceil(x / 4)

# Batch
exprs = [ctx.parse(line) for line in lines]
ctx.simplify_batch(exprs, assumptions=assumptions)

# First-class expression range facts
facts = ctx.facts()
orig = ctx.sym("orig")
A = ctx.sym("A")
B = ctx.sym("B")
facts.assume_range(orig, 0, 1073741815)
facts.derive_affine(orig, 2, 0, 2*orig)
subst_facts = facts.subs(orig, A + 8*B)
print(ctx.range(2*A + 16*B, facts=subst_facts))  # (0, 2147483630)

# Mapping form is simultaneous: the replacement A is not rewritten to B.
multi_facts = facts.subs({orig: A, A: B})
```

Implementation:
- `_ixsimpl.c` is a single-file CPython extension module written in plain C.
- `Context` Python object owns both `ixs_ctx*` and an embedded `ixs_session`;
  destructor destroys the session and then the store.
- `Expr` Python object holds a reference to its `Context` (preventing
  premature GC) and wraps `ixs_node*`.
- `__repr__` and `__str__` call `ixs_print`. Sentinel prints as `"<error>"`.
- `__int__` returns the integer value if the node is `IXS_INT`; raises
  `TypeError` otherwise. Used by `eval_ixs` for numerical evaluation.
- `__eq__` is pointer comparison (O(1) via hash-consing).
- `__hash__` returns the node's precomputed hash.
- `Expr.is_error` property — `True` for either sentinel.
- `Expr.is_parse_error` / `Expr.is_domain_error` — specific checks.
- `Expr.is_expr` / `Expr.is_pred` — root-kind checks. Predicate values are also
  expressions; `is_pred` means the node is known to produce only `0` or `1`.
- `Expr.is_integer_valued` — conservative structural integrality, without
  assumptions or facts.
- `Expr.node_ptr` — raw `ixs_node*` address exposed as a Python `int`.
  This is for identity/debug/FFI plumbing only.  It is not a stable semantic
  ID, and it is only meaningful while the owning `Context` is alive.
- `Context.errors` property — returns list of error strings; `Context.clear_errors()` resets.
- `Context.parse()` remains the backward-compatible expression parser.
  `Context.parse_expr()` and `Context.parse_pred()` expose the kind-aware parse
  entry points.
- `Context.check(expr, assumptions=[...])` returns `True`, `False`, or `None`
  for interval and modular-congruence entailment checks.  `Context.range(expr,
  assumptions=[...])` returns `(lower, upper)` from the same interval engine,
  or `None` when unknown.  Endpoints are Python `int`,
  `fractions.Fraction`, or `None` for an unbounded side.
- `Context.integer_valued(expr, assumptions=[...])` and the alternative
  `facts=...` form expose tri-state integrality. `Context.divisible(expr,
  modulus, facts)` exposes fact-backed tri-state divisibility and raises
  `ValueError` for modulus zero.
- `Context.known_bits(expr, facts)` returns
  `(known_zero, known_one, pow2)` for a valid query, including `(0, 0, None)`
  when nothing is known. `Context.symbol_congruence(symbol, facts)` returns the
  stored `(modulus, residue)` or `None`. `Context.congruent(expr, modulus,
  residue, facts)` returns tri-state `True`, `False`, or `None`; modulus zero
  raises `ValueError`.
- `Context.try_exact_divide(expr, divisor, facts)` returns
  `("proven", quotient)`, `("not_exact", None)`, or `("unknown", None)`.
  Core `ERROR` results raise `ValueError` for domain/representation failures
  and `MemoryError` for OOM while preserving the session diagnostic.
- `Context.constant_difference(lhs, rhs, facts)` returns an `int` or `None`;
  `Context.affine_decompose(expr, symbol, facts)` returns
  `(coefficient, residual)` or `None`; `Context.finite_difference(...)`
  returns an `Expr` or `None`; and `Context.split_additive_constant(...)`
  returns `(residual, constant)` or `None`. Invalid contexts, sentinels, and
  non-symbol affine targets raise `ValueError`; valid but unproved queries do
  not add diagnostics.
- `Context.check_predicate(predicate, facts)` and
  `Context.equivalent(lhs, rhs, facts)` expose conservative tri-state results
  as `True`, `False`, or `None`.
- `Context.facts()` creates a session-owned `Facts` object.  `Facts.assume()`
  imports predicates, `Facts.assume_range()` attaches direct expression
  ranges, `Facts.derive_affine()` transfers ranges through
  `scale*base + offset`, and `Facts.subs()` accepts either one pair or a
  simultaneous substitution dictionary. It transfers ranges and only the
  congruence, known-bit, and power-of-two facts justified by each replacement.
  `Context.check`, `Context.range`,
  `Context.integer_valued`, and `Context.pow2_fact` accept `facts=...` as an
  alternative to `assumptions=[...]`; `Context.divisible` requires a fact set.
- Every Python `assumptions=[...]` entry and `Facts.assume()` predicate must be
  a CMP, a canonical boolean constant, or an AND tree with those leaves.
  Unsupported or malformed predicate shapes raise `ValueError`; a failed
  `Facts.assume()` leaves prior facts unchanged.
- Operator overloading: `__add__`, `__mul__`, `__sub__`, `__mod__`, `__and__`,
  `__or__`, `__neg__`, `__ge__`, `__gt__`, `__le__`, `__lt__`, `__eq__`
  (comparisons return
  `Expr` nodes, not Python `bool`, so they can be used as assumptions).
- `Context.int_(val)` creates an `IXS_INT` node (wraps `ixs_int`).
- NULL (OOM) raises `MemoryError`. Sentinel propagates as a regular Expr.
- Module-level functions: `ixsimpl.floor()`, `ixsimpl.ceil()`,
  `ixsimpl.mod()`, `ixsimpl.max_()`, `ixsimpl.min_()`, `ixsimpl.xor_()`,
  `ixsimpl.and_()`, `ixsimpl.or_()`, `ixsimpl.not_()`,
  `ixsimpl.pw((val, cond), ...)`.
  Trailing underscore on `max_`/`min_`/`xor_`/`and_`/`or_`/`not_` avoids
  shadowing Python builtins.
- `pyproject.toml` builds the extension; no runtime dependencies.

This binding adds ~800 lines of C and is the primary interface for testing
against SymPy (run both, compare outputs).

## Session/Store API (Shipped Surface and Rationale)

This section is the normative session/store contract for the shipped API.
`Core API (Session Split Snapshot)` above records the first landing; the
signatures and rules here consolidate the current public surface and the
rationale behind it.

### Goals

The session/store split has four concrete goals:

1. Keep `ixsimpl`'s current symbolic semantics -- immutable hash-consed DAG
   nodes, canonical smart constructors, sentinel propagation, and
   assumption-driven simplification.
2. Separate long-lived store-owned state from short-lived parse/simplify
   scratch so interned nodes are not tied to ephemeral parser and
   simplifier state.
3. Make scratch reusable across calls instead of reallocating from zero for
   every parse/simplify/import operation.
4. Provide structural import and structural binary serialization so assembly
   text is only a human-facing view, not the steady-state interchange format.

### Ownership Model

The long-lived object remains `ixs_ctx`, but its role becomes narrower. The
public session type is a fixed-size opaque blob that can live on the stack or
inline inside host objects:

```c
#define IXS_SESSION_BYTES 4096

typedef union {
  void *ptr_align;
  unsigned char storage[IXS_SESSION_BYTES];
} ixs_session;
```

The union makes `ixs_session` itself pointer-aligned, which is sufficient for
the inline `ixs_arena_chunk` header placed at the start of `storage`. As with
the heap-backed arena, the usable data region is then aligned upward inside
`storage` before any object that needs stronger interior alignment is emplaced
there. The usable inline scratch capacity is therefore slightly less than 4 KB,
which is acceptable.

`IXS_SESSION_BYTES` is part of the public ABI. Changing it is an ABI break; the
initial contract fixes it at 4096 bytes.

`ixs_ctx` owns:

- the permanent arena for interned nodes
- the hash-consing table
- singletons (`IXS_ERROR`, `IXS_PARSE_ERROR`, `true`, `false`, `0`, `1`)
- any permanent rule/stat tables

During session-taking API calls, the bound session's scratch and diagnostic
state is mirrored onto `ixs_ctx` so internal helpers can keep taking
`ixs_ctx *`. Those fields are not independently owned by the store and are
copied back out to the session on return.

Authoritatively owned by `ixs_session` (and only mirrored on `ixs_ctx` while a
session is bound):

- scratch allocations
- parser state
- temporary memo tables
- mutable diagnostics

`ixs_session` is a reusable workspace bound to exactly one `ixs_ctx`. It owns:

- the inline first scratch chunk plus any active heap-grown scratch chunk
- one cached spare heap chunk for reuse
- diagnostic list / messages
- temporary parse state
- import memo tables
- temporary buffers used by simplify, bounds, expand, and walk

The older "all state lives in one context" design was convenient for a
standalone library, but it coupled unrelated lifetimes. The shipped split keeps
`ixs_ctx` as the immutable symbolic store and moves all ephemeral state into
`ixs_session`.

### Lifecycle

Lifecycle for the current session slice:

```c
ixs_ctx *ixs_ctx_create(void);
void ixs_ctx_destroy(ixs_ctx *ctx);  /* NULL-safe */

void ixs_session_init(ixs_session *s, ixs_ctx *ctx);
void ixs_session_reset(ixs_session *s);
void ixs_session_destroy(ixs_session *s);
```

Contract:

- `ixs_session_init` requires non-NULL `s` and `ctx`.
- `ixs_session_init` performs no heap allocation. It emplaces the inline
  scratch chunk and the private session header inside `s->storage`, so
  initialization cannot fail once the preconditions are met.
- `ixs_session_reset` and `ixs_session_destroy` are only valid after
  initialization and before the matching destroy.
- `ixs_session_destroy` releases heap-grown scratch storage, clears
  diagnostics, and returns `*s` to an uninitialized byte blob. Reinitialize a
  session only after destroying it.
- `ixs_ctx_destroy(NULL)` remains a no-op. For a non-NULL store, every session
  bound to that store must already have been destroyed. Destroying the store
  invalidates all nodes obtained from it.

`ixs_session` requires no separate heap allocation for the session object
itself. After initialization it is a logical non-copyable object: copying the
raw bytes duplicates interior pointers and is invalid.

`ixs_session_reset`:

- clears diagnostics
- restores scratch to the session's post-init `base_mark`
- retains one cached spare heap chunk for reuse

Each initialization and reset assigns a new store-local session epoch. A fact
handle keeps its creating epoch in a store-arena header while all bounds
payload remains in session scratch. This header survives scratch rewind long
enough to reject a stale handle before following any rewound pointers. Destroy
zeros the inline session header; reinitializing the same public storage receives
a different epoch. The fact handle itself is released with the store.

This is the critical performance property: hot paths stop paying allocator
setup cost on every parse/simplify/import call.

### Sentinel And Diagnostics Model

The shipped split keeps the existing three-tier node-level error model:

- `NULL` for OOM
- `IXS_PARSE_ERROR` for syntax / format / wrong-kind parse failure
- `IXS_ERROR` for domain failure

Sentinel propagation rules stay the same, including the `Piecewise` dead-branch
exception. The change is only where diagnostics live.

Diagnostics move from `ixs_ctx` to `ixs_session`:

```c
size_t ixs_session_nerrors(ixs_session *s);
const char *ixs_session_error(ixs_session *s, size_t index);
void ixs_session_clear_errors(ixs_session *s);
```

Rules:

- the operation that **originates** an error appends to the session error list
- propagated sentinels stay silent
- OOM still returns `NULL` and leaves diagnostics unchanged
- error strings returned by `ixs_session_error` remain valid until
  `ixs_session_clear_errors`, `ixs_session_reset`, or `ixs_session_destroy`
- diagnostics are stored separately from rewound scratch, so nested
  save/restore inside parse/simplify/walk cannot erase them prematurely

This preserves cheap in-band error propagation while removing mutable
diagnostic state from the long-lived store object.

### Shipped API Surface

All node-valued APIs take `ixs_session *`, including singleton accessors. The
shipped API keeps `ixs_parse` as a backward-compatible expression-parser wrapper
and adds kind-specific parse entry points.

Constructors and parsers:

```c
ixs_node *ixs_int(ixs_session *s, int64_t val);
ixs_node *ixs_rat(ixs_session *s, int64_t p, int64_t q);
ixs_node *ixs_sym(ixs_session *s, const char *name);

ixs_node *ixs_add(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_sub(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_neg(ixs_session *s, ixs_node *a);
ixs_node *ixs_mul(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_div(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_floor(ixs_session *s, ixs_node *x);
ixs_node *ixs_ceil(ixs_session *s, ixs_node *x);
ixs_node *ixs_mod(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_max(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_min(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_xor(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_cmp(ixs_session *s, ixs_node *a, ixs_cmp_op op, ixs_node *b);
ixs_node *ixs_and(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_or(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_not(ixs_session *s, ixs_node *a);
ixs_node *ixs_pw(ixs_session *s, uint32_t n, ixs_node **values,
                 ixs_node **conds);

ixs_node *ixs_true(ixs_session *s);
ixs_node *ixs_false(ixs_session *s);

ixs_node *ixs_parse(ixs_session *s, const char *input, size_t len);
ixs_node *ixs_parse_expr(ixs_session *s, const char *input, size_t len);
ixs_node *ixs_parse_pred(ixs_session *s, const char *input, size_t len);
```

Transforms and queries that allocate temporary state:

```c
ixs_node *ixs_simplify(ixs_session *s, ixs_node *expr,
                       ixs_node *const *assumptions, size_t n_assumptions);
void ixs_simplify_batch(ixs_session *s, ixs_node **exprs, size_t n,
                        ixs_node *const *assumptions, size_t n_assumptions);

ixs_check_result ixs_check(ixs_session *s, ixs_node *expr,
                           ixs_node *const *assumptions, size_t n_assumptions);
ixs_check_result ixs_check_integer_valued(
    ixs_session *s, ixs_node *expr,
    ixs_node *const *assumptions, size_t n_assumptions);
ixs_check_result ixs_check_defined(
    ixs_session *s, ixs_node *expr,
    ixs_node *const *assumptions, size_t n_assumptions);

typedef enum {
  IXS_EXACT_DIVIDE_PROVEN,
  IXS_EXACT_DIVIDE_NOT_EXACT,
  IXS_EXACT_DIVIDE_UNKNOWN,
  IXS_EXACT_DIVIDE_ERROR
} ixs_exact_divide_status;
typedef struct {
  ixs_exact_divide_status status;
  ixs_node *quotient;
} ixs_exact_divide_result;

ixs_pow2_fact ixs_get_pow2_fact(ixs_session *s, ixs_node *expr,
                                ixs_node *const *assumptions,
                                size_t n_assumptions);

typedef struct {
  uint64_t known_zero;
  uint64_t known_one;
  ixs_pow2_fact pow2;
} ixs_known_bits;

typedef struct {
  bool has_lower;
  bool has_upper;
  int64_t lower_p, lower_q;
  int64_t upper_p, upper_q;
} ixs_range_result;
bool ixs_range(ixs_session *s, ixs_node *expr,
               ixs_node *const *assumptions, size_t n_assumptions,
               ixs_range_result *out);

typedef struct ixs_facts ixs_facts;
ixs_facts *ixs_facts_create(ixs_session *s);
bool ixs_facts_assume_pred(ixs_facts *facts, ixs_node *pred);
bool ixs_facts_assume_range(ixs_facts *facts, ixs_node *expr,
                            const ixs_range_result *range);
bool ixs_facts_derive_affine(ixs_facts *facts, ixs_node *base, int64_t scale,
                             int64_t offset, ixs_node *derived);
bool ixs_facts_substitute(ixs_facts *dst, const ixs_facts *src,
                          ixs_node *target, ixs_node *replacement);
bool ixs_facts_substitute_multi(ixs_facts *dst, const ixs_facts *src,
                                uint32_t nsubs,
                                ixs_node *const *targets,
                                ixs_node *const *replacements);
ixs_node *ixs_simplify_facts(ixs_facts *facts, ixs_node *expr);
void ixs_simplify_batch_facts(ixs_facts *facts, ixs_node **exprs, size_t n);
ixs_check_result ixs_check_facts(ixs_facts *facts, ixs_node *expr);
ixs_check_result ixs_check_predicate_facts(ixs_facts *facts,
                                           ixs_node *predicate);
ixs_check_result ixs_equivalent_facts(ixs_facts *facts,
                                      ixs_node *lhs, ixs_node *rhs);
bool ixs_constant_difference_facts(ixs_facts *facts, ixs_node *lhs,
                                   ixs_node *rhs, int64_t *delta);
bool ixs_affine_decompose_facts(ixs_facts *facts, ixs_node *expr,
                                ixs_node *symbol, ixs_node **coefficient,
                                ixs_node **residual);
bool ixs_finite_difference_facts(ixs_facts *facts, ixs_node *expr,
                                 ixs_node *symbol, ixs_node *step,
                                 ixs_node **difference);
bool ixs_split_additive_constant_facts(ixs_facts *facts, ixs_node *expr,
                                       ixs_node **residual,
                                       int64_t *constant);
ixs_check_result ixs_check_integer_valued_facts(ixs_facts *facts,
                                                ixs_node *expr);
ixs_check_result ixs_check_defined_facts(ixs_facts *facts, ixs_node *expr);
ixs_check_result ixs_check_divisible_facts(ixs_facts *facts,
                                           ixs_node *expr,
                                           int64_t modulus);
ixs_exact_divide_result ixs_try_exact_divide_facts(ixs_facts *facts,
                                                   ixs_node *expr,
                                                   int64_t divisor);
ixs_pow2_fact ixs_get_pow2_fact_facts(ixs_facts *facts, ixs_node *expr);
bool ixs_get_known_bits_facts(ixs_facts *facts, ixs_node *expr,
                              ixs_known_bits *out);
bool ixs_get_symbol_congruence_facts(ixs_facts *facts, ixs_node *symbol,
                                     int64_t *modulus, int64_t *residue);
ixs_check_result ixs_check_congruent_facts(ixs_facts *facts,
                                           ixs_node *expr,
                                           int64_t modulus,
                                           int64_t residue);
bool ixs_range_facts(ixs_facts *facts, ixs_node *expr,
                     ixs_range_result *out);

ixs_node *ixs_expand(ixs_session *s, ixs_node *expr);
ixs_node *ixs_subs(ixs_session *s, ixs_node *expr,
                   ixs_node *target, ixs_node *replacement);
ixs_node *ixs_subs_multi(ixs_session *s, ixs_node *expr, uint32_t nsubs,
                         ixs_node *const *targets,
                         ixs_node *const *replacements);
ixs_node *ixs_walk_pre(ixs_session *s, ixs_node *root,
                       ixs_visit_fn fn, void *userdata);
ixs_node *ixs_walk_post(ixs_session *s, ixs_node *root,
                        ixs_visit_fn fn, void *userdata);
```

Node-only APIs do not take a session. Pure inspection is const-qualified:

- sentinel checks
- pointer equality
- printers
- node introspection accessors

Their child accessors retain mutable-typed return handles for compatibility.
Transforms, proof queries, walks, and node pointer arrays retain their historic
mutable-typed inputs for the same source-compatibility reason; node payloads
remain immutable.

Store inspection APIs that do not create nodes stay on `ixs_ctx`. That
includes rule-hit statistics and any future store-level counters.

Kind predicates are needed for callers that distinguish arbitrary numeric
expressions from 0/1 predicate values:

```c
bool ixs_node_is_expr(const ixs_node *node);
bool ixs_node_is_pred(const ixs_node *node);
bool ixs_node_is_integer_valued(const ixs_node *expr);
```

Exact classification:

- expression nodes: all non-sentinel arithmetic and predicate-value nodes,
  including `IXS_CMP`, `IXS_AND`, `IXS_OR`, and `IXS_NOT`
- predicate nodes: nodes known to produce only `0` or `1`; this includes
  `IXS_CMP`, `IXS_NOT`, integer constants `0` and `1`, `IXS_AND`/`IXS_OR`
  whose operands are predicate nodes, and `IXS_PIECEWISE` whose values are
  predicate nodes
- sentinels are neither

Structural integrality is likewise a node-only conservative classification.
Integer constants, symbols, floor/ceiling, predicates, integer-coefficient
sums/products with nonnegative powers, and compositions whose operands are all
structurally integral return true. Rational coefficients, negative powers, and
any `Piecewise` with a nonintegral value return false. Use the tri-state query
when assumptions or fact sets should participate.

`ixs_pw` remains expression-valued: every non-sentinel branch value must be an
expression, every branch condition is evaluated with logical truthiness, and a
final catch-all condition should be `ixs_true(s)` / integer `1`.

`ixs_parse` is a backward-compatible wrapper for `ixs_parse_expr`.
`ixs_parse_expr` accepts only expression roots. `ixs_parse_pred` accepts only
predicate roots. If the input is syntactically well-formed but the top-level
kind is wrong, the parser returns `IXS_PARSE_ERROR` and appends a diagnostic
such as `expected predicate, got expression`.

### Scratch Arena Reuse

Scratch restore rewinds to the saved mark, retains at most one detached heap
chunk as `spare`, and frees any additional detached chunks. The reusable
session model adds one inline scratch chunk inside the 4 KB public blob, so the
common case stays allocation-free after warm-up.

Conceptually:

```c
typedef struct ixs_arena {
  ixs_arena_chunk *current;
  ixs_arena_chunk *spare;
  ixs_arena_chunk *inline_chunk;
  size_t min_chunk;
  size_t fail_after;
} ixs_arena;
```

Initialization layout:

1. place the inline `ixs_arena_chunk` header at the start of `storage`
2. align the bytes immediately after that header up to `ARENA_MAX_ALIGN`
3. initialize the scratch arena with that inline chunk as `current`
4. allocate the private session header as the first scratch allocation
5. record a `base_mark` immediately after that allocation

The private session header therefore lives inside the inline scratch chunk, but
`ixs_session_reset` never destroys it because reset restores to `base_mark`,
not to the empty chunk start.

Behavior after initialization:

- `ixs_arena_restore` rewinds active allocations above the relevant mark
- if restore detaches one heap chunk, that chunk becomes `spare`
- if restore detaches additional heap chunks, they are freed immediately
- future scratch growth reuses `spare` before calling `malloc`
- if a future growth needs a larger chunk than `spare` can satisfy, the cached
  chunk is freed and replaced
- `ixs_session_reset` clears diagnostics and restores scratch to `base_mark`
- the inline first chunk is never freed
- `ixs_session_destroy` frees active and spare heap chunks, but never the
  inline first chunk

This keeps hot paths allocation-light without changing the symbolic semantics
or the save/restore programming model, and it puts a hard bound on retained
spare scratch memory.

### Structural Import Between Contexts

Raw node pointers remain store-owned. Mixing nodes from different stores is
still invalid. The sanctioned bridge is structural import:

```c
ixs_node *ixs_import_node(ixs_session *s, const ixs_node *src);
bool ixs_import_many(ixs_session *s, const ixs_node *const *src,
                     size_t count, ixs_node **out);
```

Semantics:

- if `src` is a sentinel, return the matching sentinel in the store bound to
  `s`
- rebuild every non-sentinel `src` structurally into the store bound to `s`;
  import is a boundary operation, not a hot-path ownership shortcut
- let destination hash-consing reuse existing nodes as an incidental result,
  including for same-store input, without guaranteeing a no-allocation path
- use a session-local memo table keyed by source pointer
- import through the canonical constructors so the destination store interns
  and normalizes the result
- `ixs_import_node` returns `NULL` on OOM or when `src == NULL`
- `ixs_import_many(count == 0, ...)` is a no-op success, even if `src == NULL`
  and `out == NULL`
- `ixs_import_many` returns `true` only if every element imports successfully
- when `count > 0`, NULL `src`, NULL `out`, or NULL elements fail cleanly
- if `ixs_import_many` returns `false`, `out` is left unchanged
- import is not transactional with respect to the destination store: nodes
  interned before a failing import may remain available for later reuse

This import API is the required bridge for:

- safe cross-store cloning
- importing expressions created in foreign stores
- structural binary loading

### Structural Serialization

For durable binary interchange, symbolic data must not be printed and reparsed
through symbolic text. Add a stable structural codec:

```c
typedef bool (*ixs_writer_write_fn)(void *userdata, const void *buf, size_t len);
typedef bool (*ixs_reader_read_fn)(void *userdata, void *buf, size_t len);
typedef size_t (*ixs_reader_remaining_fn)(void *userdata);

typedef struct {
  ixs_writer_write_fn write;
  void *userdata;
} ixs_writer;

typedef struct {
  ixs_reader_read_fn read;
  ixs_reader_remaining_fn remaining;
  void *userdata;
} ixs_reader;

bool ixs_serialize_node(ixs_session *s, const ixs_node *root, ixs_writer *w);
ixs_node *ixs_deserialize_node(ixs_session *s, ixs_reader *r);
```

Bindings expose the same codec as `Context.serialize()` / `Context.deserialize()`
in Python and `Context::serialize_expr()` / `Context::deserialize_expr()` in
C++.

Wire-format contract:

- host-independent and little-endian
- fixed-width scalar fields (`uint8_t` tag, `uint32_t` counts/indices,
  `int64_t` integer payloads)
- leading magic/version header: magic `IXSB`, version `1`
- topologically ordered unique-node table
- child references by earlier table index
- explicit tag values for sentinels and boolean singletons
- final root index
- writer callbacks are all-or-nothing: either consume exactly `len` bytes or
  fail without partial writes
- reader callbacks expose the exact unread byte count via `remaining`

Failure contract:

- `ixs_serialize_node` returns `true` on success and `false` on writer failure
  or OOM. Writer failures are reported by `ixs_writer`; `root == NULL` or an
  unencodable internal payload also returns `false`; validation failures append
  session diagnostics; writer failure and OOM leave diagnostics unchanged.
- `ixs_deserialize_node` returns a node on success, the destination store's
  `IXS_PARSE_ERROR` sentinel on malformed or unsupported binary, and `NULL` on
  OOM.
- malformed input appends session diagnostics and the decoder validates
  framing, lengths, tag payloads, integer widths, and child references in
  session scratch before interning anything from that malformed payload
- malformed input therefore reports a parse error without partially importing
  garbage into the store
- OOM leaves diagnostics unchanged but can still happen during the later build
  step, after some validated nodes have already been interned into the
  destination store
- size/count fields that overflow `size_t`, exceed the remaining reader bytes,
  or reference nonexistent table entries are rejected as parse errors
- streams that exceed the implementation's decode node-count limit are rejected
  as malformed input before allocation

This codec is the backend for:

- persistent binary interchange
- any future out-of-line symbolic resource storage

Text parsing/printing remains for:

- human-facing syntax
- debugging
- explicit text roundtrip tests

## Implementation Plan

The phase list below describes the engine as implemented today. The
session/store section above is an API and lifetime refactor over the same core,
not a restart from Phase 1.

### Phase 1: Foundation

- Arena allocator
- Rational arithmetic with full test coverage (floored division/Mod)
- Node types, hash-consing table, symbol interning
- Canonical Add/Mul construction with flattening and term collection
- Basic constant folding
- SymPy-format printer
- Generate `test/corpus_expected.txt` by running SymPy on all 615 corpus
  expressions (one-time script `scripts/gen_expected.py`, checked in). The
  script reads `corpus.txt` and `corpus_assumptions.txt`, applies the
  `Mod(p, q, evaluate=False)` workaround (see SymPy #28744 section), and
  writes one simplified expression per line. The SymPy version is pinned in
  `scripts/requirements-gen.txt` (e.g., `sympy==1.14.0`). This is the ground
  truth for all subsequent phases.

**Milestone**: Can construct `3*x + 2*x + 1` and get `5*x + 1`. Corpus
expected outputs are available for comparison.

### Phase 2: Parser + Floor/Ceil/Mod

- Recursive descent parser for the full grammar
- `floor()`, `ceiling()` constructors with basic rules
- `Mod()` constructor with basic rules
- `Max()`, `Min()`, `xor()` constructors

**Milestone**: Can parse and round-trip all 615 expressions. Simplification of
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

**Milestone**: All 615 expressions produce correct results. Performance target
met (< 50ms total).

### Phase 5: Bindings

- C++ header-only wrapper (`ixsimpl.hpp`)
- CPython extension module (`_ixsimpl.c`)
- Python test suite comparing output against SymPy
- `pyproject.toml` for pip-installable package

**Milestone**: `pip install .` works; Python tests pass against SymPy oracle.

### Phase 6: Hardening

- Fuzz testing (generate random expressions, verify against SymPy)
- Edge cases: overflow, division by zero, degenerate Piecewise
- C code output mode
- Documentation

## Testing Strategy

1. **Unit tests**: Each rule in isolation (test_rational, test_simplify).
2. **Corpus test**: Parse all 615 expressions, simplify, verify output matches
   SymPy's output (or is provably equivalent via random evaluation).

   **Corpus file format** — `corpus.txt` uses one expression per non-blank
   line, prefixed with timing info: `simplify time: X.XXXXs: <expression>`.
   The loader strips the prefix up to and including the second `: ` to extract
   the raw expression. Blank lines are skipped.
   `corpus_expected.txt` contains one simplified expression per line,
   aligned 1:1 with the non-blank lines of `corpus.txt` (same count, same
   order). Lines that SymPy cannot simplify are copied verbatim.

   **Corpus assumptions** — The corpus test uses the following fixed
   assumption set (matching the kernel's known variable ranges):

   ```
   $T0 >= 0, $T0 < 256
   $T1 >= 0, $T1 < 4
   $T2 >= 0
   $WG0 >= 0, $WG1 >= 0
   $GPR_NUM >= 0
   M >= 1, N >= 1, K >= 1
   _M_div_32 >= 0, _N_div_32 >= 0, _K_div_256 >= 0
   $ARGK >= 0
   $MMA_ACC >= 0, $MMA_LHS_SCALE >= 0, $MMA_RHS_SCALE >= 0
   $MMA_SCALE_FP4 >= 0
   $index0 >= 0, $index1 >= 0
   _aligned >= 0
   ```

   These are stored in `test/corpus_assumptions.txt` (one assumption per
   line, same syntax as the parser accepts) and loaded by the corpus test
   and the `corpus_expected.txt` generation script. Using a shared
   assumption file ensures SymPy and ixsimpl see identical constraints.
3. **Equivalence oracle**: For any simplified expression `s` from input `e`,
   verify `s == e` by substituting random values for all variables and
   checking numerical equality. This catches bugs without requiring
   exact output matching.
4. **Negative/error-path tests**: Verify correct behavior for invalid inputs:
   - Parse errors: `"foo bar +"` → `IXS_PARSE_ERROR`
   - Depth limit: deeply nested input → `IXS_PARSE_ERROR`
   - Domain error in parsed input: `"1/0 + x"` → `IXS_ERROR`
   - Division by zero via API: `ixs_mod(s, x, zero)` → `IXS_ERROR`
   - Integer literal overflow: `"99999999999999999999"` → `IXS_ERROR`
   - `ixs_rat(s, 1, 0)` → `IXS_ERROR`
   - NULL propagation: `ixs_add(s, NULL, x)` → NULL
   - Sentinel propagation: `ixs_floor(s, sentinel)` → same sentinel, no new error
   - Piecewise sentinel in dead branch: drops cleanly
   - `ixs_is_error` true for both, `ixs_is_parse_error` / `ixs_is_domain_error` specific
5. **Fuzz testing**: Hypothesis-based (see below).
6. **Benchmark**: Time all 615 expressions, compare against SymPy baseline.
   `bench_corpus --batch` measures shared-cache batch simplification;
   no argument measures independent calls.
   Track regressions in CI.  `bench/bench_sympy.py` runs ixsimpl vs
   `sympy.simplify` and `sympy.cancel` on the full corpus.  Typical
   results: ixsimpl ~23 ms total vs sympy.cancel ~25 s (~1000x) and
   sympy.simplify ~1000 s (~45000x).

### Fuzz Testing with Hypothesis

Property-based fuzz testing uses Python's
[Hypothesis](https://hypothesis.readthedocs.io/) library to generate random
expressions within the grammar, simplify them with both ixsimpl and SymPy,
and verify equivalence via numerical evaluation.

```python
import random
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
    ops = _OPS_WITH_PW if include_piecewise else _OPS_BASE
    op = draw(st.sampled_from(ops))
    a = draw(expressions(max_depth=max_depth - 1))
    if op in ("floor", "ceiling"):
        return (op, a)
    b = draw(expressions(max_depth=max_depth - 1))
    if op == "mod":
        b = draw(pos_ints)  # modulus must be positive
    if op == "div":
        b = draw(pos_ints)  # divisor must be nonzero
    if op == "piecewise":
        cond = draw(conditions(max_depth=max_depth - 1))
        default = draw(expressions(max_depth=max_depth - 1))
        return ("piecewise", a, cond, default)
    return (op, a, b)

@st.composite
def conditions(draw, max_depth=2):
    if max_depth <= 0 or draw(st.booleans()):
        a = draw(expressions(max_depth=2))
        b = draw(expressions(max_depth=2))
        op = draw(st.sampled_from([">=", ">", "<=", "<", "==", "!="]))
        return ("cmp", op, a, b)
    combiner = draw(st.sampled_from(["and", "or", "not"]))
    c1 = draw(conditions(max_depth=max_depth - 1))
    if combiner == "not":
        return ("not", c1)
    c2 = draw(conditions(max_depth=max_depth - 1))
    return (combiner, c1, c2)

def to_sympy(tree):
    """Convert expression tree to SymPy expression."""
    ...

def to_ixsimpl(ctx, tree):
    """Convert expression tree to ixsimpl expression."""
    ...

def eval_expr(tree, env):
    """Evaluate expression tree numerically using Python arithmetic.
    Raises ZeroDivisionError/ValueError on undefined operations."""
    ...

def eval_ixs(expr, ctx, env):
    """Evaluate ixsimpl Expr by substituting all variables via subs,
    then reading the resulting integer constant.
    Returns int or raises ValueError if result is not a constant/integer."""
    result = expr.subs({name: ctx.int_(val) for name, val in env.items()})
    if result.is_error:
        raise ValueError("sentinel")
    # Expr.__int__ returns IXS_INT value; raises TypeError for non-INT nodes
    # (including IXS_RAT — valid index expressions always reduce to integers)
    try:
        return int(result)
    except TypeError:
        raise ValueError(f"result is not an integer constant: {result}")

_VARS = ["x", "y", "z", "w"]

def _env_st(lo=1, hi=100):
    return st.fixed_dictionaries({v: st.integers(lo, hi) for v in _VARS})

@given(expr=expressions(), envs=st.lists(_env_st(0, 100), min_size=1, max_size=10))
@settings(max_examples=10000)
def test_simplify_matches_numerical(expr, envs):
    """Simplification preserves semantics: evaluate original and simplified
    at random points, check they agree."""
    ctx = ixsimpl.Context()
    ixs_expr = to_ixsimpl(ctx, expr)
    assume(not ixs_expr.is_error)  # skip if construction hit domain error
    ixs_simplified = ixs_expr.simplify()
    assume(not ixs_simplified.is_error)  # skip if simplification hit error

    for env in envs:
        try:
            orig = eval_expr(expr, env)
        except (ZeroDivisionError, ValueError, TypeError):
            continue  # skip points where original is undefined
        simp = eval_ixs(ixs_simplified, ctx, env)
        assert orig == simp, f"Mismatch: {orig} != {simp} at {env}"

@given(expr=expressions(), envs=st.lists(_env_st(), min_size=1, max_size=10))
@settings(max_examples=5000)
def test_matches_sympy(expr, envs):
    """Cross-check against SymPy: both should produce numerically
    equivalent results."""
    ctx = ixsimpl.Context()
    ixs_result = to_ixsimpl(ctx, expr).simplify()
    assume(not ixs_result.is_error)

    sp_expr = to_sympy(expr)
    sp_result = sympy.simplify(sp_expr)

    for env in envs:
        try:
            ixs_val = eval_ixs(ixs_result, ctx, env)
            sp_val = int(sp_result.subs({sympy.Symbol(k): v for k, v in env.items()}))
        except (ZeroDivisionError, ValueError, TypeError):
            continue
        assert ixs_val == sp_val, f"Divergence at {env}"
```

**Known SymPy bug to work around**: SymPy issue
[#28744](https://github.com/sympy/sympy/issues/28744) — `Mod` incorrectly
squares inner `Mod` subexpressions when the variable has `integer=True`
assumption. The bug is in `sympy/core/mod.py` lines 166-172: factors of type
`Mod` are duplicated into both `mod_l` and `non_mod_l`, causing them to
appear squared. The fix (merged to `master` in Dec 2025) has not been included
in any SymPy release yet (latest release is 1.14.0, April 2025).

Concrete workarounds for the fuzz test oracle:

1. **Reconstruct Mod with `evaluate=False`** when using SymPy as oracle.
   The bug is in SymPy's auto-evaluation of `Mod()` — when `integer=True`
   symbols are present, `Mod(k*Mod(x,n), m)` silently squares the inner
   Mod factor. The fix (from IREE Wave's `_bounds_simplify_once`) is to
   rebuild Mod nodes with `sympy.Mod(p, q, evaluate=False)` after
   simplifying their arguments, bypassing the buggy code path. This lets
   us keep `integer=True` on symbols (which is needed for other SymPy
   rewrites to fire) while avoiding the specific Mod bug. Non-Mod nodes
   are reconstructed normally via `expr.func(*simplified_args)`.
2. **Primary oracle is numerical evaluation**, not SymPy's symbolic output.
   For each test case, substitute 10+ random integer values into both the
   original and simplified expressions and check equality. This catches bugs
   in both SymPy and ixsimpl independently.
3. **Pin SymPy version** for `corpus_expected.txt` generation and document it.
   When a new SymPy release includes the fix, re-generate and note the
   version.
4. **Hypothesis `@example` decorators** for the specific pattern from #28744:
   `Mod(2*Mod(x, 3), 5)` — ensure this is always tested and known to
   diverge from buggy SymPy.

## Risks and Mitigations

| Risk | Impact | Mitigation |
|---|---|---|
| Simplification produces wrong results | Critical | Numerical equivalence oracle; fuzz testing |
| 64-bit rational overflow | Medium | Checked arithmetic plus portable emulated 128-bit compare fallback; constructors still return sentinel + error list on overflow |
| New expression patterns in future workloads | Medium | Grammar is extensible; add new node types as needed |
| Hash-consing table becomes bottleneck | Low | Linear probing with power-of-2 sizing; rehash threshold 70% |
| Simplification rules interact badly (infinite loops) | Medium | Fixed-point iteration limit (64); monotonically size-reducing rules |

## Future Ideas

- **Arena-backed hash table.** Replace the `calloc`/`free`-managed hash
  table with arena-allocated non-contiguous blocks (sizes S, S, 2S, 4S,
  8S, ...).  Old blocks remain live after resize (total capacity doubles by
  appending one new block), so there is zero arena waste.  Linear index
  decomposition to (block, offset) is O(1) via highest-bit.  Trade-off:
  extra indirection per probe and cross-block cache misses on long chains.
  Enables a fully `malloc`-free library where `ixs_ctx_destroy` is just
  two `ixs_arena_destroy` calls.

## Non-Goals

- General symbolic algebra (polynomial factoring, GCD, etc.)
- Floating-point arithmetic
- Calculus (differentiation, integration, series)
- Trigonometric or transcendental functions
- Matrix operations
- Equation solving
- Bindings beyond C++ and Python
