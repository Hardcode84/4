# Public API Contracts

[Design index](DESIGN.md)

The canonical declarations and ABI constants live in
[`include/ixsimpl.h`](../include/ixsimpl.h). This document records semantic
contracts that declarations cannot express; it deliberately does not reproduce
the C prototypes.

## Rule-Hit Statistics

When compiled with `IXS_STATS`,
the `try_rules()` dispatch automatically records a hit count for each
rule that fires, using the rule name from the `ixs_rule` table. Counts
are stored in a per-context open-addressing hash table (128 slots, keyed
on rule-name pointer identity). Rules not dispatched through `try_rules`
(e.g., ADD/MUL canonicalization) use the `IXS_STAT_HIT(ctx)` macro
directly. CMake: `-DENABLE_STATS=ON`. The Python
binding exposes `ctx.stats()` (returns a `{name: count}` dict) and
`ctx.stats_reset()`. The Python wheel does not enable stats by default;
build from source with `-DENABLE_STATS=ON` for profiling.

## Node Introspection

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

### Type-specific accessors

One function per field. Caller must check `ixs_node_tag` first — calling
the wrong accessor is UB (same contract as `ixs_node_int_val`). No
allocation, no ctx needed.

The type-specific accessors are trivial one-liners into the internal union fields
(except `ixs_node_unary_arg` which branches on tag internally).

### Generic child access

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

### Tree walk

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

### Contracts

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

## Session and Store

This section is the normative session/store contract for the shipped API.

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
public session type is the fixed-size opaque, pointer-aligned storage declared
in the public header. It can live on the stack or inline inside host objects.
That alignment is sufficient for
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

The lifecycle entry points are declared in the public header. Their contract is:

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

Diagnostics move from `ixs_ctx` to `ixs_session` under these rules:

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
shipped API keeps `ixs_parse` as the expression-parser wrapper and provides
kind-specific parse entry points.

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

Kind predicates distinguish arbitrary numeric expressions from 0/1 predicate
values. Their exact classification is:

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

## Scratch Arena Reuse

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

## Structural Import Between Contexts

Raw node pointers remain store-owned. Mixing nodes from different stores is
still invalid. The structural-import entry points declared in the public header
are the sanctioned bridge, with these semantics:

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

## Structural Serialization

For durable binary interchange, symbolic data must not be printed and reparsed
through symbolic text. The public header declares the stable structural codec.
Its descriptors are read-only. Their callbacks may still mutate the
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
