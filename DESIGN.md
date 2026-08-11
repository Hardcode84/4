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
before hash-consing. Every rewrite is a poison refinement: wherever the source
has a defined value, the replacement has the same value; where the source is
undefined, the replacement may be any value. Constructors, parsing, expansion,
substitution, ordinary simplification, and fact-backed simplification all use
this contract. Domain diagnostics are best effort and never block an exact
refinement. Public boundaries still reject malformed input, wrong ownership,
and operations that are immediately known invalid; sentinels and transport
failures remain explicit values and are not latent poison.

`ixs_simplify()` runs an additional top-down pass that uses assumptions for
bounds-dependent refinements. A conditional algebraic rewrite still requires
its stated preconditions: poison permits replacing an undefined source, not
changing a defined source value.

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
cache keyed by source-node identity. Current slots memoize top-level expansion,
removal of an ADD constant for shifted bounds, proportional ADD primitives,
and bounds-canonical aliases.
Arena-backed storage stays at or below 75% load, so hits and inserts are
expected O(1). A bounds-canonical miss costs expansion plus bounded-iteration,
fact-free simplification of the expanded DAG; later queries hit the cache.
Successful results survive session reset; failures and sentinels are not
cached. Cache-allocation failure leaves the result uncached without failing
the query. Statistics reset clears the cache so rule-hit counters remain
observable.
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

Smart constructors for ADD, MUL, Piecewise, and the associative family use
temporary arrays before building the final hash-consed node. These temporaries live on the active session's
scratch arena and are mirrored onto `ctx->scratch` only for the duration of the
bound public call. A save/restore API lets callers rewind the scratch arena
after the temporary data is consumed:

```c
typedef struct {
  ixs_arena_chunk *chunk;
  size_t used;
} ixs_arena_mark;

ixs_arena_mark ixs_arena_save(const ixs_arena *a);
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
`MAX_TERMS` and `ixs_limits.h` have been removed.

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
    IXS_MAX,         // flat n-ary Max(args...)
    IXS_MIN,         // flat n-ary Min(args...)
    IXS_XOR,         // flat n-ary bitwise xor(args...)
    IXS_CMP,         // comparison: a op b, returns 0 or 1
    IXS_AND,         // flat n-ary bitwise and(args...)
    IXS_OR,          // flat n-ary bitwise or(args...)
    IXS_NOT,         // logical not: (a == 0) ? 1 : 0
    IXS_ERROR,       // sentinel: domain error (div/0, overflow, etc.)
    IXS_PARSE_ERROR, // sentinel: syntax error from ixs_parse
    IXS_TRUNC,       // truncation toward zero
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

The public node name is intrinsically const-qualified. The implementation tag
is used directly only while a node is being assembled before interning, or for
short-lived stack probes that are never published:

```c
typedef const struct ixs_node_impl ixs_node;

struct ixs_node_impl {
    uint16_t tag;
    uint8_t properties;  // cached integer/boolean/total classification
    uint8_t reserved;
    uint32_t hash;        // precomputed, used for hash-consing
    union ixs_node_data {
        int64_t ival;                     // IXS_INT
        struct { int64_t p, q; } rat;     // IXS_RAT
        const char *name;                 // IXS_SYM (interned in arena)
        struct {                          // IXS_ADD
            ixs_node *coeff;              //   rational constant term
            uint32_t nterms;
            const struct ixs_addterm *terms; // sorted array (see below)
        } add;
        struct {                          // IXS_MUL
            ixs_node *coeff;              //   rational constant factor
            uint32_t nfactors;
            const struct ixs_mulfactor *factors; // sorted array (see below)
        } mul;
        struct {                          // IXS_FLOOR, IXS_CEIL, IXS_TRUNC
            ixs_node *arg;
        } unary;
        struct {                          // IXS_MOD, IXS_CMP
            ixs_node *lhs;
            ixs_node *rhs;
            ixs_cmp_op cmp_op;           // used only for IXS_CMP; value ignored for other binary types
        } binary;
        struct {                          // IXS_PIECEWISE
            uint32_t ncases;
            const struct ixs_pwcase *cases; // array of {value, condition}
        } pw;
        struct {                          // IXS_MAX, IXS_MIN, IXS_XOR,
                                          // IXS_AND, IXS_OR
            uint32_t nargs;
            ixs_node *const *args;        // sorted canonical operands
        } assoc;
        struct {                          // IXS_NOT
            ixs_node *arg;
        } unary_bool;
    } u;
};
```

Because `ixs_node` aliases a const-qualified implementation struct,
`ixs_node *` always means "pointer to immutable interned node." The owned ADD,
MUL, Piecewise, and associative child arrays are const after publication.
This makes mutation through a node handle a compile-time error in both C and
C++; it is not merely an API convention.

Construction computes the property byte in the same child-array pass that
checks integer and total classification. ADD, MUL, Piecewise, and associative
nodes OR the already-published descendant property bytes once; they do not
walk each child separately for rounding, Piecewise, and nested-Piecewise bits.

`ixs_true(s)` returns the interned integer `1`, and `ixs_false(s)` returns the
interned integer `0`.

Bitwise operations use unbounded integer two's-complement semantics, matching
Python and SymPy-style integer bitwise behavior. There is no fixed bit-width,
no signed/unsigned reinterpretation, and no wraparound in the core expression
model. `IXS_NOT` remains logical truthiness, not bitwise complement; adding
bitwise complement would require a distinct node.

#### Flat associative nodes

MAX, MIN, XOR, AND, and OR keep distinct tags but share the `u.assoc` payload
and collection code. A generic tag plus an opcode would duplicate the tag's
job and permit invalid states.

Construction collects the complete operand list in scratch, iteratively
flattens same-tag children, applies operation-specific reductions, sorts, and
interns one immutable contiguous array. No binary tree, rope, or chunked form
is retained. Every association and permutation of the same operands therefore
has the same node identity.

MAX/MIN/AND/OR are idempotent. XOR is not: equal operands are reduced by
parity, and constants are folded together. Bitwise reductions use the same
poison-refinement rule as arithmetic. If an operand is partial or non-integral,
the source operation is undefined there, so parity, complement, absorber, and
identity rewrites do not retain it merely to preserve a diagnostic.

Empty AND, OR, and XOR use identities `-1`, `0`, and `0`; empty MAX/MIN is an
error. A single operand returns directly.

The binary C functions remain convenience wrappers. Producers that already
have a list -- parser, import, deserializer, bindings, rewrite, and substitution
-- call the matching `*_many` constructor once rather than building a chain.

Helper structs for compound nodes:

```c
typedef struct ixs_addterm {
    ixs_node *term;    // the non-constant subexpression
    ixs_node *coeff;   // rational coefficient (IXS_INT or IXS_RAT, nonzero)
} ixs_addterm;

typedef struct ixs_mulfactor {
    ixs_node *base;    // the non-constant base
    int32_t exp;              // nonzero integer exponent
} ixs_mulfactor;

typedef struct ixs_pwcase {
    ixs_node *value;   // branch value
    ixs_node *cond;    // branch condition (boolean expression)
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
`struct ixs_node_impl tmp`, populates its fields and hash, and probes the hash
table via `htab_lookup`. On hit (full structural comparison confirms match),
the existing immutable pointer is returned with zero arena allocation. On
miss, the constructor arena-allocates a mutable implementation object, copies
`tmp` into it, interns it, and exposes only the const-qualified handle. This
avoids wasting arena memory on duplicate nodes.

**Canonical ordering**: Children of `IXS_ADD`, `IXS_MUL`, and every flat
associative node are sorted by a total order on nodes (by tag, then by content).

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
         | 'Trunc' '(' expr ')'
         | 'Mod' '(' expr ',' expr ')'
         | 'Max' '(' expr_list ')'
         | 'Min' '(' expr_list ')'
         | 'xor' '(' bit_list ')'
         | 'Piecewise' '(' pw_cases ')'
         | '(' expr ')'
pw_cases = '(' expr ',' cond ')' (',' '(' expr ',' cond ')')*
expr_list = expr (',' expr)*
bit_list = expr ',' expr (',' expr)*
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
`Trunc` is ixsimpl's stable spelling for truncation toward zero because SymPy
has no built-in exact-integer truncation node with the required structural
round trip. Similarly, the parser accepts `True`/`False`; both parse to integer
`1`/`0`.
Piecewise values try the arithmetic grammar first, which is the common corpus
path. Reaching the case comma commits that parse; any other following token
restores parser and diagnostic state before using the predicate-valued grammar.
Thus boolean-valued branches retain their syntax without parsing every numeric
branch twice.
The API convenience functions `ixs_true`/`ixs_false` return the same integer
nodes.

Integer literals: sequences of digits. Rationals are not parsed directly —
they arise from `3/8` being parsed as `IXS_INT(3) / IXS_INT(8)` and
immediately folded to `IXS_RAT(3, 8)`.

The parser collects each associative chain or argument list and calls its
`*_many` constructor once.

### Layer 4: Simplification Engine

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

#### 4.4 Floor / Ceiling / Truncation Rules

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

Both `is_integer_with_divinfo` and `is_known_divisible` handle multi-factor
MUL nodes: for `p/q * f1^e1 * ... * fn^en`, each positive-exponent factor
is checked for integer-valued-ness, and any single factor whose congruence
absorbs the remaining denominator suffices to prove the whole product
integer-valued (or divisible by a given modulus).  This is a sufficient
OR-of-factors test, not full product factorization: `6 | (2*3)` cannot
be proved when neither factor alone is divisible by 6.

`is_known_divisible` also handles `Max` and `Min` when every operand is
provably divisible; any selected value then preserves the divisor.

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

(bounds-aware ADD cancellation)
c*Mod(A, m) - c*Mod(B, m)               → 0
                     when m > 0 is literal and A-B ≡ 0 (mod m)
```

Exact floor/Mod cancellation is valid on every defined source evaluation. If
the divisor is invalid, the source is poison and may refine to the replacement;
domain-error detection is best effort. Partial cancellation still requires a
positive integer literal because its residual algebra is not the exact identity.

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

#### 4.7 Max / Min Rules

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

#### 4.8 XOR Rules

```
xor(..., xor(args...), ...) → xor(..., args..., ...)
xor(..., 0, ...)            → xor(...)
xor(..., constants, ...)    → fold constants with ^
xor(..., a repeated n, ...) → keep a iff n is odd
xor(a, b)       → a + b    when a,b >= 0 and known bits do not overlap

k*xor(a, b + 2^n) - k*xor(a, b)
                → k*(2^n - 2*(a & 2^n))
                  when bit n of the pre-toggle operand is known zero
```

Parity reduction replaces the old nested-cancellation rule and handles the
whole flat list in one pass. An even run disappears under the common poison-
refinement contract.

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

#### 4.9 Bitwise And/Or And Logical Not

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

#### 4.10 Comparison Simplification

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

### Layer 5: Bound Analysis (Phase 4)

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
`bounds_integer.c` owns exact integer and divisibility proofs.
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
Piecewise selector proofs. `bounds_modular.c` owns generic normalized
exact-value projection, paired-Mod exact-delta search, wide signed arithmetic,
dynamic no-wrap lifts, and its growable progress stack.
`bounds_residue.c` owns target-modulus residue queries, including
proof-independent rational cancellation and branch-sensitive Piecewise
evaluation. `bounds_stride.c` owns phase-free stride queries and coefficient
scaling.
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

  This is the ordered Euclidean split/merge part of mixed-radix layout algebra,
  not a general layout-composition engine. Direct Euclidean `Mod` splits accept
  a dynamic positive modulus. Dynamic floor-radix chains, XOR and mask
  projections, products, Piecewise, and general digit reconstruction retain
  their existing proof domains.
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
  stride, residue, and interval queries start at 16 frames. `bounds_integer.c`
  runs exact integer proofs with 16 inline frames and scratch growth.
  Definedness, predicate, and AND-assumption walks start at 32 frames.

  The structural driver owns push/pop, growth, and optional LIFO abort. Its
  `run` entry owns one scratch mark; memo-first consumers use the mark-free
  seeded driver inside a caller-owned mark. Definedness, predicate, and
  AND-assumption walks allocate a per-query node-identity memo before their
  stack. Exact integer proofs keep an inline 32-entry compound-key memo over
  `(node, relation, modulus)`. Bitfacts, stride, residue, and interval walks use
  the central `bounds_query` cache because their keys and values belong to that
  environment. Local identity and compound memos share the stack's caller-owned
  mark and die at its restore. The central cache is generation-scoped and
  owner-keyed; forks share its query state while those keys isolate bounds
  owners and generations.

  `bounds_residue.c` keeps the requested modulus in each typed frame. ADD
  coefficients are reduced before recursive queries, equal representatives are
  grouped in scratch storage, and reachable Piecewise branches run in bounds
  forks. Its proof-independent mode consults only structural and stored facts.
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
- `c*Mod(A,m) - c*Mod(B,m)` → `0` when `A-B ≡ 0 (mod m)` is proven
  for the shared positive literal modulus
- Opposite-coefficient floors with one denominator cancel when a remainder
  proof shows the numerator shift stays in the same quotient bucket

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
  facts, then evaluates `AND`, `OR`, and `NOT` with conservative tri-state
  truth tables. `AND` is true only when every child is true and false when any
  child is false; `OR` is true when any child is true and false only when every
  child is false; `NOT` inverts true and false. Predicate-valued `Piecewise`
  nodes that do not collapse during fact-backed simplification remain
  unknown. Numeric bitwise `AND`/`OR` nodes are rejected with a `predicate:`
  diagnostic rather than interpreted as boolean trees. The evaluator is
  iterative and memoized over the predicate DAG using query-arena storage;
  allocation failure returns unknown.

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
  Recognition and cache hits are O(1), while constant-drop cache misses,
  affine-round splitting, and relation sign partitioning are O(T).
  Constructing the relation residual inherits the simplifier's O(T^2) worst
  case; partitioning uses O(T) query scratch.

  Signed truncating division is implemented by the private
  `src/division_algebra.c` component around the exact relation `N = D*Q + R`.
  Its exact quotient-parts parser is shared with positive-divisor quotient
  algebra and reports representability misses separately from allocation.
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
  preserving sparse form without internal expansion.

  Every admitted atom requires `n` and `d` to be defined and integer-valued
  and `d > 0`. Isolating `Mod(n,d) = r` succeeds only when `r` is the unique
  Euclidean remainder: `r` is defined and integer-valued, `0 <= r < d`, and
  `n-r` is divisible by `d`. Isolating `floor(n/d) = q` instead requires `q`
  integer-valued and `n-d*q` in `[0,d)`. Exact closure may replace all direct
  floor atoms in one row by `(n-Mod(n,d))/d`. Congruence closure may replace a
  direct `c*Mod(n,m)` by `c*n` modulo a target `d` only after proving
  `(c*m)/d` integer-valued; unchecked nested occurrences remain opaque.

  Canonical mixed-radix ranges use the same row. Each positive integer digit
  `c*Mod(n,m)` contributes `[0,c*(m-1)]`; the ordinary interval engine bounds
  the residual once, and the symbolic upper bound is simplified as
  `upper-d < 0`. Thus the rule is not keyed to a particular radix, literal
  divisor, or term count. A separate `floor(expr/d) == 0` fact may certify a
  canonical remainder when interval correlation alone is insufficient. This
  proves, for example,
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

  Paired-Mod projection uses a growable query-local proof stack. Every child
  enters a Mod dividend or removes one matched Mod pair from a canonical ADD,
  so progress is structural and there is no separate 32-level, 4096-visit, or
  fixed-term semantic cutoff. Allocation or checked-size failure returns
  unknown. For `T` terms at one level, candidate matching is O(T^2) in the
  worst case and residual construction is O(T); it visits only the queried
  expression DAG and exact residuals use the weighted equality forest rather
  than inequality adjacency or context-wide scans.

  After those exact strategies miss, the private `src/low_bits_algebra.c`
  component handles two original outer `Mod` nodes with the same positive,
  representable power-of-two literal modulus. The bounds adapter proves the
  original outer operations and both original dividends defined and
  integer-valued over the complete fact domain; normalized roots never replace
  those source obligations. The component then projects the dividends through
  the typed ring `Z/(2^k)`. It propagates through integer-coefficient `ADD`,
  integer-coefficient `MUL` with only positive powers, numeric `XOR`/`AND`/`OR`,
  and a nested literal `Mod` whose modulus is divisible by the outer modulus.
  Every supported node and immediate child is independently re-proved total
  and integer-valued, and the adapter re-proves both projected roots. Other
  nodes, including rounding,
  `Piecewise`, extrema, predicates, rational coefficients, reciprocal powers,
  and dynamic or incompatible `Mod`, remain opaque. Pointer-identical opaque
  subtrees can still participate in a successful exact proof. The rule sees
  the original pair because fact-backed simplification can remove only one of
  the matching outer operations.

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
- **Generic exact-value projection**: fact-backed rewriting asks the bounds
  solver whether each normalized result has one exact `int64_t` value. The
  lower query consumes normalized nodes and never calls the simplifier. It
  combines exact point ranges, additive rows over the weighted relation
  forest, and paired-Mod projection; the rewrite memo ensures each input DAG
  node is normalized and projected once per simplification. The rewrite does
  not dispatch on ADD or subtraction: additive rows are one lower proof
  backend, any parent can consume a projected child, and scalar and batch
  simplification use the same path. A successful projection is a poison
  refinement, so it need only agree where the source is defined.
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

These sentinels report failures already detected at a public construction or
validation boundary. They are not the same as a symbolic expression that may
be undefined for some later substitution. Explicit sentinels propagate; latent
undefinedness is poison and may disappear through a valid refinement.

**Piecewise exception** — sentinel values do not eagerly propagate through
`ixs_pw`. A Piecewise branch may contain a sentinel value without poisoning
the entire expression, similar to LLVM's poison semantics in `select`:

- If a condition folds to `False`, the branch is dropped — sentinel in its
  value disappears harmlessly.
- If a condition folds to `True`, its branch value becomes the result,
  including a sentinel value when no earlier unresolved branch remains.
- A sentinel condition always propagates, even after an earlier constant-true
  branch. Branch selection itself is poisoned.
- Sentinel branch values propagate when selected or when every value branch is
  a sentinel. Otherwise an unresolved sentinel arm stays inside the Piecewise.
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
size_t      ixs_session_nerrors(const ixs_session *s);
const char *ixs_session_error(const ixs_session *s, size_t index);
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
- `"ixs_cmp: invalid comparison operator"`
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
typedef const struct ixs_node_impl ixs_node;

// Every ixs_node * below is an immutable handle because the typedef itself is
// const-qualified.

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
size_t ixs_session_nerrors(const ixs_session *s);
const char *ixs_session_error(const ixs_session *s, size_t index);
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
ixs_node *ixs_trunc(ixs_session *s, ixs_node *x);
ixs_node *ixs_mod(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_max(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_min(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_xor(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_max_many(ixs_session *s, uint32_t n, ixs_node *const *args);
ixs_node *ixs_min_many(ixs_session *s, uint32_t n, ixs_node *const *args);
ixs_node *ixs_xor_many(ixs_session *s, uint32_t n, ixs_node *const *args);
ixs_node *ixs_pw(ixs_session *s, uint32_t n,
                 ixs_node *const *values, ixs_node *const *conds);
ixs_node *ixs_cmp(ixs_session *s, ixs_node *a, ixs_cmp_op op, ixs_node *b);
ixs_node *ixs_and(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_or(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_and_many(ixs_session *s, uint32_t n, ixs_node *const *args);
ixs_node *ixs_or_many(ixs_session *s, uint32_t n, ixs_node *const *args);
ixs_node *ixs_not(ixs_session *s, ixs_node *a);
ixs_node *ixs_true(ixs_session *s);
ixs_node *ixs_false(ixs_session *s);

// Assumption roots must be CMP or canonical true/false nodes, or flat AND
// nodes with those leaves, built in the same context. True is a no-op and
// false is a contradiction. OR, NOT, malformed, NULL, sentinel, and other
// roots are rejected atomically with an `assumptions:` diagnostic. Trees are
// walked iteratively without a semantic depth ceiling. Pass NULL/0 for no
// assumptions.
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
// first matching entry wins.  One target uses a direct pointer comparison;
// multiple targets build a query-scratch hash table once.  Target lookup and
// reachable-DAG traversal are expected O(N + E + C) for N nodes, E edges, and
// C targets, with O(N + C) scratch. Canonical ADD/MUL reconstruction retains
// its O(children^2) worst case. Thin wrapper around the same engine as ixs_subs
// (nsubs=1 delegates here).
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
ixs_facts *ixs_facts_create_preds(ixs_session *s,
                                  ixs_node *const *preds, size_t n_preds);
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
bool ixs_affine_decompose_facts(ixs_facts *facts, ixs_node *expr,
                                ixs_node *symbol, ixs_node **coefficient,
                                ixs_node **residual);
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
size_t   ixs_ctx_nstats(const ixs_ctx *ctx); // distinct rules that fired
uint64_t ixs_ctx_stat(const ixs_ctx *ctx, size_t index, const char **name);
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

Nodes are opaque — `struct ixs_node_impl` is internal. The public C API exposes
structural introspection through `ixs_node_tag`, type-specific field
accessors, generic child access, and scratch-backed tree walks.

Interned node payloads are immutable. `ixs_node` is a typedef of
`const struct ixs_node_impl`, so every `ixs_node *` parameter, result, callback
argument, pointer-array element, and child accessor result is const-qualified.
The occasional explicit `const ixs_node *` spelling is equivalent but
redundant. Constructors and transforms compose directly with child accessors
without offering a mutable escape hatch.

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

/* Only valid when tag is IXS_FLOOR, IXS_CEIL, IXS_TRUNC, or IXS_NOT. */
ixs_node *ixs_node_unary_arg(const ixs_node *node);

/* Only valid when tag is IXS_MOD or IXS_CMP. */
ixs_node *ixs_node_binary_lhs(const ixs_node *node);
ixs_node *ixs_node_binary_rhs(const ixs_node *node);

/* Only valid when tag is IXS_CMP. */
ixs_cmp_op ixs_node_cmp_op(const ixs_node *node);

/* Only valid when tag is IXS_PIECEWISE.  i must be < ncases. */
uint32_t ixs_node_pw_ncases(const ixs_node *node);
ixs_node *ixs_node_pw_value(const ixs_node *node, uint32_t i);
ixs_node *ixs_node_pw_cond(const ixs_node *node, uint32_t i);

/* Only valid for MAX, MIN, XOR, AND, or OR.  i must be < nargs. */
uint32_t ixs_node_assoc_nargs(const ixs_node *node);
ixs_node *ixs_node_assoc_arg(const ixs_node *node, uint32_t i);
```

The type-specific accessors are trivial one-liners into the internal union fields
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
| MOD/CMP | 2 | lhs, rhs |
| unary | 1 | arg |
| PW | 2*ncases | (value[0], cond[0]), ... |
| MAX/MIN/XOR/AND/OR | nargs | arg[0], arg[1], ... |
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
typedef ixs_walk_action (*ixs_visit_fn)(const ixs_node *node, void *userdata);

/* Pre-order: visit node, then recurse into children.
 * Returns root on completion, the stopping node on STOP, NULL if root
 * is NULL or the explicit scratch-backed traversal stack cannot grow.
 * s must be non-NULL when root is non-NULL.
 * Sentinels (ERROR, PARSE_ERROR) are visited as leaves; the callback
 * must check ixs_node_tag before using type-specific accessors.
 * SKIP prevents descent into children. */
const ixs_node *ixs_walk_pre(ixs_session *s, const ixs_node *root,
                       ixs_visit_fn fn, void *userdata);

/* Post-order: recurse into children, then visit node.
 * Same return/NULL/sentinel semantics as ixs_walk_pre.
 * SKIP is a no-op in post-order (children already visited). */
const ixs_node *ixs_walk_post(ixs_session *s, const ixs_node *root,
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

### Flat associative construction

Normalizing `m` collected operands uses O(m) scratch and O(m log m)
lexicographic comparisons. A comparison costs O(p) for the unequal structural
prefix traversed and uses an explicit O(p) scratch stack; interned shared
children stop at pointer equality. The interned node owns one O(m) argument
array. Known lists use `*_many` once.
Repeated binary append can retain successively larger arrays and is not the
bulk construction path.

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

Amortized O(1) mechanisms are not scans: hash-table growth rehashes;
`ixs_arena_restore` walks only work allocated after its mark; and
`ixs_arena_destroy_transient` releases only one operation's input-sized
workspace. None depends on retained context state `A`.
`query_state_arena` persists across operations but retains only one state plus
geometric buffers bounded by the largest single query, so its transient destroy
also depends on that query size rather than operation count.

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
must honor the hot contract on their own. Advance and abort callbacks used by
`query_walk.c` are explicit `/* hot */` roots. The generic callback result
contains structural progress, consumer stop, or storage failure. The driver
does not classify or publish proof values, cache entries, or transport status.
Function-like macros are modeled as pseudo-functions. Their bodies are
re-parsed for calls, so scans reached through a macro are caught; same-name
macro variants
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
│   ├── additive_row.c       # canonical additive-row operations
│   ├── additive_row.h
│   ├── algebra_status.h     # shared private algebra result ordering
│   ├── arena.c              # arena allocator
│   ├── arena.h
│   ├── rational.c           # exact rational and modular arithmetic
│   ├── rational.h
│   ├── hash.h               # shared hot pointer-identity mixer
│   ├── node.c               # node creation, hash-consing, canonical forms
│   ├── node.h
│   ├── parser.c             # recursive descent parser
│   ├── parser.h
│   ├── simplify.c           # rewrite rules engine
│   ├── simplify.h
│   ├── expand.c             # MUL-over-ADD distribution
│   ├── expand.h
│   ├── facts_query.c        # fact-set reads, simplification, public query API
│   ├── facts_store.c        # persistent facts lifetime, transactions, closure
│   ├── facts_store.h
│   ├── bounds.h             # aggregate private bounds state
│   ├── bounds_assume.c      # assumptions, aliases, and fact refinement
│   ├── bounds_assume.h
│   ├── bounds_bitfacts.c    # structural known-bit and power-of-two queries
│   ├── bounds_bitfacts.h
│   ├── bounds_defined.c     # domain and Piecewise coverage proof
│   ├── bounds_defined.h
│   ├── bounds_difference.c  # directed constraints and interval propagation
│   ├── bounds_difference.h
│   ├── bounds_equivalence.c # equivalence proof policy
│   ├── bounds_equivalence.h
│   ├── bounds_integer.c     # exact integer and divisibility proof
│   ├── bounds_integer.h
│   ├── bounds_lifecycle.c   # aggregate initialization, fork, and destruction
│   ├── bounds_modular.c     # paired-Mod exact-delta proof
│   ├── bounds_modular.h
│   ├── bounds_predicate.c   # tri-state and finite-domain predicate proof
│   ├── bounds_predicate.h
│   ├── bounds_query.c       # central query state, cache, and transport lifecycle
│   ├── bounds_query.h
│   ├── bounds_store.c       # retained fact records, indexes, and mutation
│   ├── bounds_store.h
│   ├── bounds_range.c       # interval transfer, caches, and comparisons
│   ├── bounds_range.h
│   ├── bounds_relation.c    # exact-component cursor and equality projection
│   ├── bounds_relation.h
│   ├── bounds_residue.c     # target-modulus and branch-sensitive residue proof
│   ├── bounds_residue.h
│   ├── bounds_stride.c      # phase-free expression stride proof
│   ├── bounds_stride.h
│   ├── division_algebra.c   # signed truncating-division certificates
│   ├── division_algebra.h
│   ├── quotient_algebra.c   # bounded Euclidean sparse-row equality
│   ├── quotient_algebra.h
│   ├── query_walk.c         # shared iterative stacks, node sets, and vectors
│   ├── query_walk.h
│   ├── radix_algebra.c      # bounded mixed-radix nonnegativity proof
│   ├── radix_algebra.h
│   ├── relation_algebra.c   # indexed exact additive relations
│   ├── relation_algebra.h
│   ├── interval.c           # interval and integer-congruence arithmetic
│   ├── interval.h
│   ├── low_bits_algebra.c   # power-of-two quotient-ring projection
│   ├── low_bits_algebra.h
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
│   ├── test_equivalence_context.c
│   ├── test_piecewise_equivalence.c
│   ├── test_relational_contract.c
│   ├── test_simplify.c
│   ├── test_expand.c
│   ├── test_edge_cases.c
│   ├── test_corpus.c
│   ├── test_accessors.py
│   ├── test_python.py
│   ├── test_relational_contract.py
│   ├── test_sympy_conv.py
│   ├── conftest.py
│   ├── corpus.txt
│   ├── corpus_expected.txt
│   └── corpus_assumptions.txt # shared assumption set for corpus tests
├── bench/
│   ├── bench_corpus.c       # benchmark: individual or batch corpus simplify
│   └── bench_relational_facts.c # relational production witness and RSS slope
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
    const ixs_node *node_;
public:
    Expr(ixs_ctx *ctx, ixs_session *session, const ixs_node *node)
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
        std::vector<const ixs_node*> raw(n_assumptions);
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
        const ixs_node *neg =
            ixs_mul(session_, ixs_int(session_, -1), rhs.node_);
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

    const ixs_node *raw() const { return node_; }
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
  `Facts::affine_decompose()` and `split_additive_constant()` mirror the narrow
  fact-backed C helpers and fill their output references only on success.
  Constant and finite differences use ordinary `Expr` subtraction,
  substitution, optional expansion, and `Facts::simplify()`.
- `Expr::raw()` returns `const ixs_node *`. `Expr::raw_const()` remains as a
  compatibility alias, but neither method offers a mutable node handle.
- Operator overloading for natural expression building.
- Range overloads for MAX/MIN/XOR/AND/OR use one temporary contiguous buffer
  and call one `*_many` function; binary operators allocate no wrapper storage.
- Simplification adds no C++-side heap allocation. (`str()` and range
  construction allocate their result/temporary buffers.)
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
- `Context.affine_decompose(expr, symbol, facts)` returns
  `(coefficient, residual)` or `None`;
  `Context.split_additive_constant(...)`
  returns `(residual, constant)` or `None`. Invalid contexts, sentinels, and
  non-symbol affine targets raise `ValueError`; valid but unmatched queries do
  not add diagnostics. Constant and finite differences are composed from
  `Expr` subtraction, `subs()`, `expand()`, and fact-backed `simplify()`.
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
  `ixsimpl.mod()`, variadic `ixsimpl.max_()`, `ixsimpl.min_()`,
  `ixsimpl.xor_()`, `ixsimpl.and_()`, `ixsimpl.or_()`, `ixsimpl.not_()`,
  `ixsimpl.pw((val, cond), ...)`.
  Trailing underscore on `max_`/`min_`/`xor_`/`and_`/`or_`/`not_` avoids
  shadowing Python builtins.
- Variadic associative functions validate one context and issue one `*_many`
  call; they do not left-fold through Python operators.
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
- discards the prepared direct-assumption domain
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
size_t ixs_session_nerrors(const ixs_session *s);
const char *ixs_session_error(const ixs_session *s, size_t index);
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
ixs_node *ixs_trunc(ixs_session *s, ixs_node *x);
ixs_node *ixs_mod(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_max(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_min(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_xor(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_max_many(ixs_session *s, uint32_t n, ixs_node *const *args);
ixs_node *ixs_min_many(ixs_session *s, uint32_t n, ixs_node *const *args);
ixs_node *ixs_xor_many(ixs_session *s, uint32_t n, ixs_node *const *args);
ixs_node *ixs_cmp(ixs_session *s, ixs_node *a, ixs_cmp_op op, ixs_node *b);
ixs_node *ixs_and(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_or(ixs_session *s, ixs_node *a, ixs_node *b);
ixs_node *ixs_and_many(ixs_session *s, uint32_t n, ixs_node *const *args);
ixs_node *ixs_or_many(ixs_session *s, uint32_t n, ixs_node *const *args);
ixs_node *ixs_not(ixs_session *s, ixs_node *a);
ixs_node *ixs_pw(ixs_session *s, uint32_t n,
                 ixs_node *const *values, ixs_node *const *conds);

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
ixs_facts *ixs_facts_create_preds(ixs_session *s,
                                  ixs_node *const *preds, size_t n_preds);
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
bool ixs_affine_decompose_facts(ixs_facts *facts, ixs_node *expr,
                                ixs_node *symbol, ixs_node **coefficient,
                                ixs_node **residual);
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

Node-only APIs do not take a session. The opaque node typedef is
const-qualified across the entire surface, including:

- sentinel checks
- pointer equality
- printers
- node introspection accessors
- constructors and transform results
- proof-query inputs
- walk roots, callbacks, and stopping-node results
- child accessors and node pointer arrays

Store inspection APIs that do not create nodes stay on `ixs_ctx`. That
includes rule-hit statistics and any future store-level counters.

Fact-backed queries retain `ixs_facts *`, not `const ixs_facts *`: they bind
the owning session, populate and clear proof caches, and record OOM or invalid
state. Their node inputs are immutable, but the fact-set workspace is
logically mutable. Likewise, writer and reader `userdata` remains `void *`
because callbacks normally advance a cursor or grow a sink; only the codec
descriptor itself is const-qualified.

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

bool ixs_serialize_node(ixs_session *s, const ixs_node *root,
                        const ixs_writer *w);
ixs_node *ixs_deserialize_node(ixs_session *s, const ixs_reader *r);
```

The codec descriptors are read-only. Their callbacks may still mutate the
object referenced by `userdata`, as required for advancing a reader or
growing a writer sink.

Bindings expose the same codec as `Context.serialize()` / `Context.deserialize()`
in Python and `Context::serialize_expr()` / `Context::deserialize_expr()` in
C++.

Wire-format contract:

- host-independent and little-endian
- fixed-width scalar fields (`uint8_t` tag, `uint32_t` counts/indices,
  `int64_t` integer payloads)
- leading magic/version header: magic `IXSB`, version `2`
- topologically ordered unique-node table
- child references by earlier table index
- explicit tag values for sentinels
- final root index
- writer callbacks are all-or-nothing: either consume exactly `len` bytes or
  fail without partial writes
- reader callbacks expose the exact unread byte count via `remaining`

Version 2 stores MAX, MIN, XOR, AND, and OR uniformly as their tag followed by
`uint32_t nargs` and `nargs` earlier-node indices. The encoder emits sorted,
flat arrays; the decoder rebuilds each record with one `*_many` call. Boolean
singletons are ordinary integer 0/1 records. Valid noncanonical lists are
canonicalized; constructor-domain or arity failures are malformed input.
`Trunc` is a unary record with stable wire tag 18 and one earlier-node index.

The decoder accepts version 2 only. A bad version returns `IXS_PARSE_ERROR`
immediately after the header; there is no legacy decoder, migration, or
fallback path.

Failure contract:

- `ixs_serialize_node` returns `true` on success and `false` on writer failure
  or OOM. Writer failures are reported by `ixs_writer`; `root == NULL` or an
  unencodable internal payload also returns `false`; validation failures append
  session diagnostics; writer failure and OOM leave diagnostics unchanged.
- `ixs_deserialize_node` returns a node on success, the destination store's
  `IXS_PARSE_ERROR` sentinel on malformed or unsupported binary, and `NULL` on
  OOM.
- malformed input appends session diagnostics and the decoder validates
  framing and payloads in session scratch, then preflights constructors in an
  isolated context before interning into the destination
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

The flat associative transition is one focused change:

1. Replace the binary/logic payloads with `u.assoc` and add the five `*_many`
   constructors plus shared flatten/sort support.
2. Make MAX/MIN, XOR, AND, and OR reductions operate on complete arrays.
3. Move hashing, equality, traversal, proofs, printing, import, rewrite,
   substitution, and bindings to the common associative accessors.
4. Emit version 2 counted lists and reject every other wire version.
5. Regenerate the amalgamation and run C, Python, fuzz, corpus, and benchmark
   gates.

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
- Seed `test/corpus_expected.txt` by running SymPy on all 615 corpus
  expressions (one-time script `scripts/gen_expected.py`, checked in). The
  script reads `corpus.txt` and `corpus_assumptions.txt`, applies the
  `Mod(p, q, evaluate=False)` workaround (see SymPy #28744 section), and
  writes one simplified expression per line. The SymPy version is pinned in
  `scripts/requirements-gen.txt` (e.g., `sympy==1.14.0`). Audited canonical
  refinements may update individual checked-in lines when SymPy retains an
  equivalent expression or does not model poison refinement.

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
2. **Corpus test**: Parse all 615 expressions, simplify, and verify the exact
   checked-in canonical outputs. The initial outputs come from SymPy; audited
   poison refinements and branch-local proofs may be more canonical.

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
   substitute random values for all variables and check equality wherever `e`
   is defined. This catches bugs without requiring exact output matching.
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
5. **Associative tests**: Every permutation and parenthesization of
   MAX/MIN/XOR/AND/OR has the same pointer; XOR parity, AND/OR idempotence,
   poison refinement, and version rejection are covered directly.
6. **Fuzz testing**: Hypothesis-based (see below).
7. **Benchmark**: Time all 615 expressions, compare against SymPy baseline.
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

Proof-specific generators also build small, complete integer domains rather
than relying on sampled points. The combined symbolic-proof property mixes
bounded related and unrelated nested `Mod` chains, signed integer and rational
coefficients, floor partitions, congruent and incongruent radix
reconstructions, and arithmetic at both int64 boundaries. Every reported range
must contain every reachable value, and every successful equality or predicate
proof must hold throughout the domain. One-shot assumptions and reusable facts
are queried against the same semantic oracle.

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
