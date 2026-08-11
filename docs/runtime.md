# Runtime, Errors, and Performance

[Design index](DESIGN.md)

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
| Print traversal OOM | `SIZE_MAX`, buffer cleared | unchanged | action-stack growth |

### ixs_parse Return Values

| Input | Return |
|---|---|
| Valid expression | `ixs_node*` (valid) |
| Syntax error | `IXS_PARSE_ERROR` sentinel |
| Syntactically valid but contains domain error | `IXS_ERROR` sentinel |
| OOM | `NULL` |

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
