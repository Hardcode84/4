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

Tags are C comments placed immediately above a function definition:

  /* scan: arena */   Cost grows with total allocated arena state.
  /* scan: ctx */     Cost grows with ctx-wide table state.
  /* hot */           Hot-path contract: must not reach a scan.

Public API functions from include/ixsimpl.h are hot roots by default;
NONHOT_API below lists the lifecycle and bulk-IO exceptions.  Amortized
O(1) mechanisms (hash-table growth rehash, arena rollback proportional
to the rolled-back work) are not scans and stay untagged.  Calls through
function pointers and calls to external (libc) functions are assumed
scan-free; see DESIGN.md for the full threat model.

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

# Type names from ixsimpl.h that the API regex would otherwise mistake
# for functions (function-pointer typedefs, struct names).
API_TYPE_NAMES = frozenset(
    {"ixs_ctx", "ixs_node", "ixs_visit_fn", "ixs_session", "ixs_facts", "ixs_reader", "ixs_writer"}
)

TAG_RE = re.compile(r"/\*\s*(hot|scan)(?:\s*:\s*([a-z][a-z0-9 ]*?))?\s*\*/")

# Near-miss detector: a comment that looks like a tag but does not parse.
# Silent tag loss would turn the whole check into theater.
TAG_LIKE_RE = re.compile(r"/\*\s*(hot|scan)\b[^*]*\*/")

API_NAME_RE = re.compile(r"\b(ixs_\w+)\s*\(")

# Macros used in storage-specifier position that the C grammar cannot
# know.  Replaced by same-length text before parsing so byte offsets
# (and therefore tag positions and line numbers) stay exact.
SPECIFIER_MACROS = (b"IXS_STATIC",)


def sanitize(text: bytes) -> bytes:
    """Neutralize specifier macros without shifting any byte offsets."""
    out = []
    for line in text.split(b"\n"):
        if not line.lstrip().startswith(b"#"):
            for macro in SPECIFIER_MACROS:
                line = line.replace(macro, b"static".ljust(len(macro)))
        out.append(line)
    return b"\n".join(out)


@dataclass(eq=False)
class FuncDef:
    """A function definition plus everything the checker knows about it."""

    name: str
    file: Path
    line: int
    start_byte: int
    tag: str | None = None
    scan_axis: str | None = None
    callees: dict[FuncDef, int] = field(default_factory=dict)
    unresolved: list[str] = field(default_factory=list)

    def loc(self) -> str:
        return f"{self.file}:{self.line}"


@dataclass(eq=False)
class RawCall:
    """A call site before name resolution."""

    caller: FuncDef
    callee_name: str
    line: int


def parse_public_api(header: Path) -> set[str]:
    """Extract public function names declared in the header."""
    names: set[str] = set()
    for line in header.read_text().splitlines():
        line = line.strip()
        if line.startswith("typedef") or line.startswith("#") or line.startswith("/*"):
            continue
        m = API_NAME_RE.search(line)
        if m and m.group(1) not in API_TYPE_NAMES:
            names.add(m.group(1))
    return names


def declarator_name(node: Node) -> str | None:
    """Descend declarator nesting to the function name identifier."""
    decl = node.child_by_field_name("declarator")
    while decl is not None:
        if decl.type == "identifier":
            return decl.text.decode() if decl.text else None
        decl = decl.child_by_field_name("declarator")
    return None


def collect_calls(func: FuncDef, def_node: Node, raw_calls: list[RawCall]) -> None:
    """Walk a function body, recording direct call names and indirect lines."""
    stack = [def_node]
    while stack:
        node = stack.pop()
        if node.type == "call_expression":
            fn = node.child_by_field_name("function")
            if fn is not None and fn.type == "identifier" and fn.text:
                raw_calls.append(RawCall(func, fn.text.decode(), node.start_point.row + 1))
            else:
                func.unresolved.append(f"<indirect> line {node.start_point.row + 1}")
        stack.extend(node.children)


def parse_sources(root: Path, parser: Parser) -> tuple[list[FuncDef], list[RawCall], list[str]]:
    """Parse all C sources; return function defs, raw calls, and warnings."""
    defs: list[FuncDef] = []
    raw_calls: list[RawCall] = []
    warnings: list[str] = []
    sources = sorted(root.glob("src/*.[ch]"))
    for src in sources:
        text = sanitize(src.read_bytes())
        rel = src.relative_to(root)
        tree = parser.parse(text)
        if tree.root_node.has_error:
            # Error-recovery nodes can carry insane coordinates; never walk them.
            warnings.append(f"{rel}: tree-sitter failed to parse cleanly; file skipped")
            continue
        file_defs: list[FuncDef] = []

        stack = [tree.root_node]
        while stack:
            node = stack.pop()
            if node.type == "function_definition":
                name = declarator_name(node)
                if name is not None:
                    func = FuncDef(name, rel, node.start_point.row + 1, node.start_byte)
                    file_defs.append(func)
                    collect_calls(func, node, raw_calls)
            stack.extend(node.children)
        defs.extend(file_defs)

        content = text.decode()
        tag_starts: set[int] = set()
        for m in TAG_RE.finditer(content):
            tag_starts.add(m.start())
            kind, axis = m.group(1), m.group(2)
            following = [f for f in file_defs if f.start_byte > m.end()]
            if not following:
                warnings.append(
                    f"{rel}:{content[: m.start()].count(chr(10)) + 1}: "
                    f"dangling '/* {kind} */' tag with no following function definition"
                )
                continue
            target = min(following, key=lambda f: f.start_byte)
            if target.tag is not None:
                warnings.append(f"{target.loc()}: conflicting tags on '{target.name}'")
                continue
            target.tag = kind
            target.scan_axis = axis
        for m in TAG_LIKE_RE.finditer(content):
            if m.start() not in tag_starts:
                line_no = content[: m.start()].count(chr(10)) + 1
                warnings.append(f"{rel}:{line_no}: malformed tag {m.group(0)!r}")
    return defs, raw_calls, warnings


def resolve_calls(
    defs: list[FuncDef], raw_calls: list[RawCall]
) -> tuple[dict[FuncDef, set[FuncDef]], list[str]]:
    """Resolve callee names to definitions; return edges and warnings."""
    by_name: dict[str, list[FuncDef]] = {}
    for f in defs:
        by_name.setdefault(f.name, []).append(f)

    warnings: list[str] = []
    callers: dict[FuncDef, set[FuncDef]] = {}
    for call in raw_calls:
        candidates = by_name.get(call.callee_name, [])
        target: FuncDef | None = None
        if len(candidates) == 1:
            target = candidates[0]
        elif len(candidates) > 1:
            local = [c for c in candidates if c.file == call.caller.file]
            if len(local) == 1:
                target = local[0]
            else:
                warnings.append(
                    f"{call.caller.loc()}: ambiguous callee '{call.callee_name}' "
                    f"({len(candidates)} definitions); edge dropped"
                )
        if target is None:
            if not candidates and call.callee_name not in call.caller.unresolved:
                call.caller.unresolved.append(call.callee_name)
        elif target is not call.caller:
            # Self-recursion cannot introduce new taint.
            callers.setdefault(call.caller, set()).add(target)
    return callers, warnings


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

    header = root / "include" / "ixsimpl.h"
    parser = Parser(Language(tree_sitter_c.language()))
    defs, raw_calls, warnings = parse_sources(root, parser)
    edges, resolve_warnings = resolve_calls(defs, raw_calls)
    warnings.extend(resolve_warnings)

    by_name = {f.name: f for f in defs}
    public_api = parse_public_api(header)
    missing = sorted(n for n in public_api if n not in by_name)
    for name in missing:
        warnings.append(f"{header.relative_to(root)}: public API '{name}' has no definition")

    hot_roots = sorted(
        {by_name[n] for n in public_api - NONHOT_API if n in by_name}
        | {f for f in defs if f.tag == "hot"},
        key=lambda f: f.name,
    )
    sources = {f for f in defs if f.tag == "scan"}
    tainted = propagate_taint(edges, sources)

    errors = 0
    for root_fn in hot_roots:
        if root_fn not in tainted:
            continue
        path = witness_path(root_fn, edges, tainted)
        sink = path[-1]
        print(f"error: hot path reaches 'scan: {sink.scan_axis}': {root_fn.name} ({root_fn.loc()})")
        hops = " -> ".join(f"{f.name} ({f.loc()})" for f in path)
        print(f"  path: {hops} [scan: {sink.scan_axis}]")
        errors += 1

    for w in warnings:
        print(f"warning: {w}", file=sys.stderr)

    if args.verbose:
        n_edges = sum(len(v) for v in edges.values())
        unresolved = sorted({u for f in defs for u in f.unresolved})
        print(f"graph: {len(defs)} functions, {len(raw_calls)} call sites, {n_edges} edges")
        print(f"roots: {len(hot_roots)} hot, sources: {len(sources)} scan, tainted: {len(tainted)}")
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
