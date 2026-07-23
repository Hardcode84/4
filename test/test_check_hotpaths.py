# SPDX-FileCopyrightText: 2026 ixsimpl contributors
# SPDX-License-Identifier: Apache-2.0
"""Regression tests for scripts/check_hotpaths.py against a fixture tree."""

import subprocess
import sys
from pathlib import Path

import pytest

pytest.importorskip("tree_sitter_c")

REPO = Path(__file__).resolve().parent.parent
FIXTURE = REPO / "test" / "fixtures" / "hotpaths"


def run_checker() -> tuple[int, str]:
    proc = subprocess.run(
        [
            sys.executable,
            str(REPO / "scripts" / "check_hotpaths.py"),
            "--root",
            str(FIXTURE),
            "--verbose",
        ],
        capture_output=True,
        text=True,
        check=False,
    )
    return proc.returncode, proc.stdout + proc.stderr


def test_macro_calls_join_the_call_graph() -> None:
    code, out = run_checker()
    assert code == 1
    assert "error: hot path reaches 'scan: ctx': ixs_fast" in out
    assert "helper" in out and "KILL" in out and "scan_state" in out


def test_string_literal_is_not_a_tag() -> None:
    _, out = run_checker()
    assert out.count("scan source:") == 1
    assert "scan source: scan_state" in out


def test_header_prose_and_split_declarations() -> None:
    _, out = run_checker()
    assert "ixs_ghost" not in out
    assert "roots: 2 hot" in out  # ixs_fast plus the split ixs_split.


def test_non_adjacent_tag_is_rejected() -> None:
    _, out = run_checker()
    assert "must sit immediately above 'distant'" in out
