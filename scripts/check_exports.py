#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 ixsimpl contributors
# SPDX-License-Identifier: Apache-2.0
"""Verify the compiled public API and retired-contract absence.

Compiles ixsimpl_amalg.c into a temporary .so, extracts exported text
symbols via nm, and compares against function declarations parsed from
include/ixsimpl.h. Removed contracts are checked in source and with negative
consumer compilations. Exits 0 only when all checks are clean.
"""

import re
import subprocess
import sys
import tempfile
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
AMALG = REPO / "ixsimpl_amalg.c"
HEADER = REPO / "include" / "ixsimpl.h"
REMOVED_C_API_USES = {
    "ixs_integer_range_result": "ixs_integer_range_result value = {0}; (void)value;",
    "ixs_integer_range": "(void)&ixs_integer_range;",
    "ixs_integer_range_facts": "(void)&ixs_integer_range_facts;",
    "ixs_equivalent_finite_domain_facts": "(void)&ixs_equivalent_finite_domain_facts;",
}
REMOVED_SOURCE_PATHS = (
    HEADER,
    AMALG,
    *sorted((REPO / "src").glob("*.[ch]")),
    *sorted((REPO / "bindings").rglob("*.c")),
    *sorted((REPO / "bindings").rglob("*.h")),
    *sorted((REPO / "bindings").rglob("*.hpp")),
    *sorted((REPO / "bindings").rglob("*.py")),
    *sorted((REPO / "bindings").rglob("*.pyi")),
)

FUNC_DECL_RE = re.compile(
    r"^(?:ixs_\w+)\s*\(",
    re.MULTILINE,
)


def parse_public_api(header: Path) -> set[str]:
    """Extract function names declared in the public header."""
    text = header.read_text()
    names: set[str] = set()
    for line in text.splitlines():
        line = line.strip()
        if line.startswith("typedef") or line.startswith("#") or line.startswith("/*"):
            continue
        m = re.search(r"\b(ixs_\w+)\s*\(", line)
        if m:
            name = m.group(1)
            if name not in ("ixs_ctx", "ixs_node", "ixs_visit_fn"):
                names.add(name)
    return names


def compiler_command(source: Path) -> list[str]:
    return [
        "gcc",
        "-std=c99",
        "-pedantic",
        "-Wall",
        "-Wextra",
        "-Werror",
        "-fsyntax-only",
        str(source),
        f"-I{REPO / 'include'}",
        f"-I{REPO / 'src'}",
    ]


def compile_snippet(body: str) -> subprocess.CompletedProcess[str]:
    source_text = "#include <ixsimpl.h>\n" "int main(void) {\n" f"  {body}\n" "  return 0;\n" "}\n"
    with tempfile.TemporaryDirectory() as tmp:
        source = Path(tmp) / "removed_api_probe.c"
        source.write_text(source_text)
        return subprocess.run(compiler_command(source), capture_output=True, text=True, check=False)


def check_removed_api_compilation() -> bool:
    control = compile_snippet("ixs_range_result value = {0}; (void)value;")
    if control.returncode != 0:
        print("error: public-header control compilation failed", file=sys.stderr)
        print(control.stderr, file=sys.stderr)
        return False
    stale = [
        name for name, body in REMOVED_C_API_USES.items() if compile_snippet(body).returncode == 0
    ]
    if not stale:
        return True
    print(f"STALE ({len(stale)} removed API declarations still compile):")
    for name in stale:
        print(f"  {name}")
    return False


def check_removed_api_sources() -> bool:
    stale: list[tuple[Path, str]] = []
    for path in REMOVED_SOURCE_PATHS:
        text = path.read_text()
        for name in REMOVED_C_API_USES:
            if name in text:
                stale.append((path.relative_to(REPO), name))
    if not stale:
        return True
    print(f"STALE ({len(stale)} removed API references remain):")
    for path, name in stale:
        print(f"  {path}: {name}")
    return False


def build_so(amalg: Path, output: Path) -> None:
    """Compile the amalgamation into a temporary shared library."""
    cmd = [
        "gcc",
        "-std=c99",
        "-pedantic",
        "-Wall",
        "-Wextra",
        "-Werror",
        "-O0",
        "-shared",
        "-fPIC",
        "-o",
        str(output),
        str(amalg),
        f"-I{REPO / 'include'}",
        f"-I{REPO / 'src'}",
    ]
    subprocess.check_call(cmd, stderr=subprocess.PIPE)


def get_exported_functions(so_path: Path) -> set[str]:
    """Get exported text symbols from a shared library."""
    out = subprocess.check_output(
        ["nm", "-D", "--defined-only", str(so_path)],
        text=True,
    )
    names: set[str] = set()
    for line in out.splitlines():
        parts = line.split()
        if len(parts) == 3 and parts[1] == "T":
            names.add(parts[2])
    return names


def main() -> int:
    if not AMALG.exists():
        print(f"error: {AMALG} not found; run scripts/amalgamate.py first", file=sys.stderr)
        return 1

    if not check_removed_api_sources() or not check_removed_api_compilation():
        return 1

    public_api = parse_public_api(HEADER)
    with tempfile.TemporaryDirectory() as tmp:
        so_path = Path(tmp) / "libixsimpl.so"
        build_so(AMALG, so_path)
        exported = get_exported_functions(so_path)

    leaked = exported - public_api
    missing = public_api - exported

    ok = True
    if leaked:
        print(f"LEAKED ({len(leaked)} symbols not in public API):")
        for name in sorted(leaked):
            print(f"  {name}")
        ok = False
    if missing:
        print(f"MISSING ({len(missing)} public API symbols not exported):")
        for name in sorted(missing):
            print(f"  {name}")
        ok = False

    if ok:
        print(f"OK: {len(exported)} exported symbols match public API.")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
