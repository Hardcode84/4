#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 ixsimpl contributors
# SPDX-License-Identifier: Apache-2.0
"""Static hot-path complexity guard.

Enforces the performance policy in AGENTS.md: hot paths must not execute
work linear in total arena/ctx state.  Builds the static call graph of
src/*.c and src/*.h with tree-sitter-c, propagates taint from functions
tagged '/* scan: <axis> */' backward to their callers, and reports any
hot function that transitively reaches a scan function, with a witness
call path.

Tags are standalone C comments placed immediately above a function
definition (only comments and whitespace, no blank line, between):

  /* scan: <type> */  Cost grows with a context-wide resource.  The
                      type must be registered in SCAN_TYPES below.
  /* hot */           Hot-path contract: must not reach a scan.

Tags are read only from AST comment nodes, so a tag-shaped string
literal or doc prose is inert.  Function-like macros are modeled as
pseudo-functions: their replacement text is parsed for calls, so a scan
reached through a macro is caught.  Macro bodies are parsed as isolated
fragments, and same-name macro variants (conditional compilation) union
their edges — a sound over-approximation.

Public API functions are parsed out of include/ixsimpl.h with
tree-sitter (no line regexes) and are hot roots by default; NONHOT_API
below lists the lifecycle and bulk-IO exceptions.  Amortized O(1)
mechanisms (hash-table growth rehash, arena rollback proportional to
the rolled-back work) are not scans and stay untagged.  Calls through
function pointers and calls to external (libc) functions are assumed
scan-free; see DESIGN.md for the full threat model.

Adding a scan type: one line in SCAN_TYPES, the tag above the function,
and a DESIGN.md update in the same commit.  Tags with unregistered
types are rejected, so a typo cannot silently pass.

Exits 0 when clean, 1 on violations or graph inconsistencies.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

import tree_sitter_c
from tree_sitter import Language, Node, Parser

REPO = Path(__file__).resolve().parent.parent

# Public API functions exempt from the hot-path policy: context/session
# lifecycle, parsing, serialization, printing, and stats introspection.
# Everything else exported from ixsimpl.h is a hot root.
NONHOT_API = frozenset(
    {
        "ixs_ctx_create",
        "ixs_ctx_destroy",
        "ixs_ctx_nstats",
        "ixs_ctx_stat",
        "ixs_ctx_stats_reset",
        "ixs_nrules",
        "ixs_parse",
        "ixs_parse_expr",
        "ixs_parse_pred",
        "ixs_print",
        "ixs_print_c",
        "ixs_rule_name",
        "ixs_deserialize_node",
        "ixs_serialize_node",
        "ixs_session_clear_errors",
        "ixs_session_destroy",
        "ixs_session_error",
        "ixs_session_init",
        "ixs_session_nerrors",
        "ixs_session_reset",
    }
)

# Registry of scan types: axis -> one-line description.  A '/* scan: x */'
# tag with an unregistered x is an error — adding a type is deliberately
# one line here plus the tag plus a DESIGN.md update, same commit.
SCAN_TYPES = {
    "arena": "cost grows with total live arena chunks/bytes",
    "ctx": "cost grows with ctx-wide table state",
}

# A tag is the entire comment, not a substring of one.
TAG_BLOCK_RE = re.compile(r"/\*\s*(hot|scan)(?:\s*:\s*([a-z][a-z0-9_]*))?\s*\*/")
TAG_LINE_RE = re.compile(r"//\s*(hot|scan)(?:\s*:\s*([a-z][a-z0-9_]*))?\s*")

# Near-miss detector: a comment that opens like a tag and carries a
# colon but does not parse as one.  Silent tag loss would turn the
# whole check into theater.
TAG_LIKE_RE = re.compile(r"\s*(?:/\*|//)\s*(?:hot|scan)\b[^*]*:", re.IGNORECASE)

# Macros used in storage-specifier position that the C grammar cannot
# know.  Replaced by same-length text before parsing so byte offsets
# (and therefore tag positions and line numbers) stay exact.
SPECIFIER_MACROS = (b"IXS_STATIC",)


def sanitize(text: bytes) -> bytes:
    """Neutralize specifier macros and C++ linkage guards, byte-exactly."""
    out = []
    prev = b""
    for line in text.split(b"\n"):
        stripped = line.strip()
        if stripped == b'extern "C" {':
            # C++-only syntax inside '#ifdef __cplusplus'; the C grammar
            # chokes on it.  Blank it, preserving length.
            out.append(b" " * len(line))
        elif stripped == b"}" and prev.strip() == b"#ifdef __cplusplus":
            out.append(b" " * len(line))
        else:
            if not line.lstrip().startswith(b"#"):
                for macro in SPECIFIER_MACROS:
                    line = line.replace(macro, b"static".ljust(len(macro)))
            out.append(line)
        prev = line
    return b"\n".join(out)


@dataclass(eq=False)
class FuncDef:
    """A function (or macro pseudo-function) definition plus check state."""

    name: str
    file: Path
    line: int
    start_byte: int
    is_macro: bool = False
    tag: str | None = None
    scan_axis: str | None = None
    unresolved: list[str] = field(default_factory=list)

    def loc(self) -> str:
        return f"{self.file}:{self.line}"


@dataclass(eq=False)
class RawCall:
    """A call site before name resolution."""

    caller: FuncDef
    callee_name: str
    line: int


def declarator_name(node: Node) -> str | None:
    """Descend declarator nesting to the function name identifier."""
    decl = node.child_by_field_name("declarator")
    while decl is not None:
        if decl.type == "identifier":
            return decl.text.decode() if decl.text else None
        decl = decl.child_by_field_name("declarator")
    return None


def has_function_declarator(node: Node) -> bool:
    """True if the declaration subtree contains a function_declarator."""
    decl = node.child_by_field_name("declarator")
    stack = [decl] if decl is not None else []
    while stack:
        inner = stack.pop()
        if inner.type == "function_declarator":
            return True
        stack.extend(inner.children)
    return False


def parse_public_api(root: Path, parser: Parser) -> tuple[set[str], list[str]]:
    """Extract public function names from the header via the C grammar."""
    header = root / "include" / "ixsimpl.h"
    warnings: list[str] = []
    tree = parser.parse(sanitize(header.read_bytes()))
    if tree.root_node.has_error:
        warnings.append(f"{header.relative_to(root)}: tree-sitter failed to parse; no API roots")
        return set(), warnings
    names: set[str] = set()
    stack = [tree.root_node]
    while stack:
        node = stack.pop()
        if node.type == "function_definition":
            name = declarator_name(node)
            if name is not None:
                names.add(name)
        elif node.type == "declaration":
            is_typedef = any(
                c.type == "storage_class_specifier" and c.text == b"typedef" for c in node.children
            )
            if not is_typedef and has_function_declarator(node):
                name = declarator_name(node)
                if name is not None:
                    names.add(name)
        stack.extend(node.children)
    return names, warnings


def walk_calls(owner: FuncDef, node: Node, raw_calls: list[RawCall], line_offset: int = 0) -> None:
    """Walk a subtree, recording direct call names and indirect lines."""
    stack = [node]
    while stack:
        current = stack.pop()
        if current.type == "call_expression":
            fn = current.child_by_field_name("function")
            line = line_offset + current.start_point.row + 1
            if fn is not None and fn.type == "identifier" and fn.text:
                raw_calls.append(RawCall(owner, fn.text.decode(), line))
            else:
                owner.unresolved.append(f"<indirect> line {line}")
        stack.extend(current.children)


def match_tag(comment: str) -> re.Match[str] | None:
    """A tag is a standalone comment: the whole comment must be the tag."""
    return TAG_BLOCK_RE.fullmatch(comment) or TAG_LINE_RE.fullmatch(comment)


def parse_sources(root: Path, parser: Parser) -> tuple[list[FuncDef], list[RawCall], list[str]]:
    """Parse all C sources; return function/macro defs, raw calls, warnings."""
    defs: list[FuncDef] = []
    raw_calls: list[RawCall] = []
    warnings: list[str] = []
    sources = [*sorted(root.glob("src/*.[ch]")), root / "include" / "ixsimpl.h"]
    for src in sources:
        text = sanitize(src.read_bytes())
        rel = src.relative_to(root)
        tree = parser.parse(text)
        if tree.root_node.has_error:
            # Error-recovery nodes can carry insane coordinates; never walk them.
            warnings.append(f"{rel}: tree-sitter failed to parse cleanly; file skipped")
            continue
        file_defs: list[FuncDef] = []
        file_comments: list[Node] = []

        stack = [tree.root_node]
        while stack:
            node = stack.pop()
            if node.type == "function_definition":
                name = declarator_name(node)
                if name is not None:
                    func = FuncDef(name, rel, node.start_point.row + 1, node.start_byte)
                    file_defs.append(func)
                    walk_calls(func, node, raw_calls)
            elif node.type == "comment":
                file_comments.append(node)
            elif node.type in ("preproc_function_def", "preproc_def"):
                name_node = node.child_by_field_name("name")
                value = node.child_by_field_name("value")
                if name_node is not None and name_node.text and value is not None and value.text:
                    mdef = FuncDef(
                        name_node.text.decode(),
                        rel,
                        node.start_point.row + 1,
                        node.start_byte,
                        is_macro=True,
                    )
                    # The replacement text is a flat token blob in the
                    # grammar; re-parse it as a fragment to find its calls.
                    mini = parser.parse(value.text)
                    walk_calls(mdef, mini.root_node, raw_calls, line_offset=mdef.line - 1)
                    file_defs.append(mdef)
            stack.extend(node.children)
        defs.extend(file_defs)

        for c in sorted(file_comments, key=lambda n: n.start_byte):
            ctext = c.text.decode() if c.text else ""
            m = match_tag(ctext)
            if m is None:
                if TAG_LIKE_RE.match(ctext):
                    warnings.append(f"{rel}:{c.start_point.row + 1}: malformed tag {ctext!r}")
                continue
            kind, axis = m.group(1), m.group(2)
            line_no = c.start_point.row + 1
            if kind == "hot" and axis is not None:
                warnings.append(f"{rel}:{line_no}: '/* hot */' takes no axis")
                continue
            if kind == "scan" and (axis is None or axis not in SCAN_TYPES):
                known = ", ".join(sorted(SCAN_TYPES))
                warnings.append(
                    f"{rel}:{line_no}: unknown scan type {axis or '<missing>'!r}; "
                    f"known types: {known}; register new ones in SCAN_TYPES "
                    f"in scripts/check_hotpaths.py"
                )
                continue
            following = [f for f in file_defs if f.start_byte > c.end_byte]
            if not following:
                warnings.append(
                    f"{rel}:{line_no}: "
                    f"dangling '/* {kind} */' tag with no following function definition"
                )
                continue
            target = min(following, key=lambda f: f.start_byte)
            if target.is_macro:
                warnings.append(
                    f"{rel}:{line_no}: tag must annotate a function definition, "
                    f"not macro '{target.name}'"
                )
                continue
            # Adjacency: only comments and whitespace, no blank line,
            # may separate the tag from its function.
            gap = bytearray(text[c.end_byte : target.start_byte])
            base = c.end_byte
            for c2 in file_comments:
                if base <= c2.start_byte and c2.end_byte <= target.start_byte:
                    gap[c2.start_byte - base : c2.end_byte - base] = b" " * (
                        c2.end_byte - c2.start_byte
                    )
            gap_bytes = bytes(gap)
            if gap_bytes.strip() or b"\n\n" in gap_bytes:
                warnings.append(
                    f"{rel}:{line_no}: '/* {kind} */' tag must sit immediately above "
                    f"'{target.name}' (only comments and whitespace between)"
                )
                continue
            if target.tag is not None:
                warnings.append(f"{target.loc()}: conflicting tags on '{target.name}'")
                continue
            target.tag = kind
            target.scan_axis = axis
    return defs, raw_calls, warnings


def resolve_calls(
    defs: list[FuncDef], raw_calls: list[RawCall]
) -> tuple[dict[FuncDef, set[FuncDef]], list[str]]:
    """Resolve callee names to definitions; return edges and warnings."""
    by_name: dict[str, list[FuncDef]] = {}
    for f in defs:
        by_name.setdefault(f.name, []).append(f)

    warnings: list[str] = []
    edges: dict[FuncDef, set[FuncDef]] = {}
    for call in raw_calls:
        candidates = by_name.get(call.callee_name, [])
        targets: set[FuncDef] = set()
        if len(candidates) == 1:
            targets = {candidates[0]}
        elif candidates:
            local = [c for c in candidates if c.file == call.caller.file]
            functions = [c for c in candidates if not c.is_macro]
            if len(local) == 1:
                targets = {local[0]}
            elif len(local) > 1:
                targets = set(local)
            elif len(functions) == 1:
                targets = {functions[0]}
            else:
                # Sound over-approximation: keep every candidate's edge.
                # All-macro ambiguity is normal conditional compilation
                # and stays silent; function ambiguity is suspicious.
                targets = set(candidates)
                if not all(c.is_macro for c in candidates):
                    warnings.append(
                        f"{call.caller.loc()}: ambiguous callee '{call.callee_name}' "
                        f"({len(candidates)} definitions); all edges kept"
                    )
        targets.discard(call.caller)  # Self-recursion adds no new taint.
        if not targets and not candidates and call.callee_name not in call.caller.unresolved:
            call.caller.unresolved.append(call.callee_name)
        edges.setdefault(call.caller, set()).update(targets)
    return edges, warnings


def propagate_taint(edges: dict[FuncDef, set[FuncDef]], sources: set[FuncDef]) -> set[FuncDef]:
    """Backward taint propagation: a caller is tainted if any callee is."""
    tainted = set(sources)
    worklist = list(sources)
    while worklist:
        node = worklist.pop()
        for caller, callees in edges.items():
            if node in callees and caller not in tainted:
                tainted.add(caller)
                worklist.append(caller)
    return tainted


def witness_path(
    root: FuncDef, edges: dict[FuncDef, set[FuncDef]], tainted: set[FuncDef]
) -> list[FuncDef]:
    """Shortest call path from root to a scan source, through tainted callees."""
    prev: dict[FuncDef, FuncDef] = {}
    queue = [root]
    target: FuncDef | None = None
    while queue and target is None:
        next_queue: list[FuncDef] = []
        for node in queue:
            for callee in sorted(
                edges.get(node, set()), key=lambda f: (f.name, str(f.file), f.line)
            ):
                if callee not in tainted or callee in prev or callee is root:
                    continue
                prev[callee] = node
                if callee.tag == "scan":
                    target = callee
                    break
                next_queue.append(callee)
            if target is not None:
                break
        queue = next_queue
    if target is None:
        return [root]
    path = [target]
    while path[-1] is not root:
        path.append(prev[path[-1]])
    path.reverse()
    return path


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", type=Path, default=REPO, help="repository root")
    ap.add_argument("--verbose", action="store_true", help="print graph stats and unresolved calls")
    args = ap.parse_args(argv)
    root: Path = args.root.resolve()

    parser = Parser(Language(tree_sitter_c.language()))
    defs, raw_calls, warnings = parse_sources(root, parser)
    edges, resolve_warnings = resolve_calls(defs, raw_calls)
    warnings.extend(resolve_warnings)
    public_api, api_warnings = parse_public_api(root, parser)
    warnings.extend(api_warnings)

    # A function shadows a same-named macro for root/self-check purposes.
    by_name: dict[str, FuncDef] = {}
    for f in defs:
        if f.name not in by_name or by_name[f.name].is_macro:
            by_name[f.name] = f
    header = root / "include" / "ixsimpl.h"
    missing = sorted(n for n in public_api if n not in by_name)
    for name in missing:
        warnings.append(f"{header.relative_to(root)}: public API '{name}' has no definition")

    hot_roots = sorted(
        {by_name[n] for n in public_api - NONHOT_API if n in by_name}
        | {f for f in defs if f.tag == "hot"},
        key=lambda f: f.name,
    )
    if not hot_roots:
        # A checker with no roots passes anything; that is not success.
        warnings.append("no hot roots found; the check would be vacuous")
    sources = {f for f in defs if f.tag == "scan"}
    tainted = propagate_taint(edges, sources)

    errors = 0
    for root_fn in hot_roots:
        if root_fn not in tainted:
            continue
        path = witness_path(root_fn, edges, tainted)
        sink = path[-1]
        axis = sink.scan_axis or "?"
        print(f"error: hot path reaches 'scan: {axis}': {root_fn.name} ({root_fn.loc()})")
        hops = " -> ".join(f"{f.name} ({f.loc()})" for f in path)
        print(f"  path: {hops} [scan: {axis}: {SCAN_TYPES.get(axis, 'unregistered')}]")
        errors += 1

    for w in warnings:
        print(f"warning: {w}", file=sys.stderr)

    if args.verbose:
        n_edges = sum(len(v) for v in edges.values())
        unresolved = sorted({u for f in defs for u in f.unresolved})
        print(f"graph: {len(defs)} functions, {len(raw_calls)} call sites, {n_edges} edges")
        print(f"roots: {len(hot_roots)} hot, sources: {len(sources)} scan, tainted: {len(tainted)}")
        for s in sorted(sources, key=lambda f: (f.scan_axis or "", f.name)):
            print(f"scan source: {s.name} ({s.loc()}) [scan: {s.scan_axis}]")
        if unresolved:
            print(f"unresolved callees (assumed scan-free): {', '.join(unresolved)}")

    if errors or warnings:
        return 1
    print(
        f"OK: {len(hot_roots)} hot roots, {len(defs)} functions, "
        f"{len(sources)} scan sources; no violations."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
