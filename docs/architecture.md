# Architecture and Representation

[Design index](DESIGN.md)

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

## Layer 0: Memory — Arena Allocator

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

### Scratch Arena

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

## Layer 1: Expression Representation — Hash-Consed DAG

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

### Flat associative nodes

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

## Layer 2: Rational Arithmetic

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

## Layer 3: Parser

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

## File Structure

```
ixsimpl/
├── include/
│   └── ixsimpl.h            # public C API (single header)
├── src/
│   ├── additive_row.c       # canonical additive and Euclidean row plans
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
│   ├── facts_query.c        # fact reads, rewriting, root projection, public API
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
│   ├── radix_algebra.c      # bounded mixed-radix order proofs
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
└── docs/
    ├── DESIGN.md             # design index and domain analysis
    ├── architecture.md       # this file
    ├── simplification.md     # rewrite engine and canonical forms
    ├── bounds.md             # facts, bounds, and proof services
    ├── runtime.md            # errors, performance, build, and CI
    ├── api.md                # public semantic contracts
    ├── bindings.md           # C++ and Python bindings
    └── validation.md         # implementation and validation strategy
```

Estimated total: 5,000-8,000 lines of C, ~500 lines C++ header, ~800 lines
Python extension.
