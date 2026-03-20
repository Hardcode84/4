# SPDX-FileCopyrightText: 2026 ixsimpl contributors
# SPDX-License-Identifier: Apache-2.0
"""ixsimpl - Fast index expression simplifier for integer arithmetic."""

from __future__ import annotations

import functools
from typing import TYPE_CHECKING

from ixsimpl._ixsimpl import (
    ADD,
    AND,
    CEIL,
    CMP,
    CMP_EQ,
    CMP_GE,
    CMP_GT,
    CMP_LE,
    CMP_LT,
    CMP_NE,
    ERROR,
    FALSE,
    FLOOR,
    INT,
    MAX,
    MIN,
    MOD,
    MUL,
    NOT,
    OR,
    PARSE_ERROR,
    PIECEWISE,
    RAT,
    SYM,
    TRUE,
    XOR,
    _Expr,
    _set_expr_class,
)
from ixsimpl._ixsimpl import and_ as _and
from ixsimpl._ixsimpl import ceil as _ceil
from ixsimpl._ixsimpl import floor as _floor
from ixsimpl._ixsimpl import max_ as _max
from ixsimpl._ixsimpl import min_ as _min
from ixsimpl._ixsimpl import mod as _mod
from ixsimpl._ixsimpl import not_ as _not
from ixsimpl._ixsimpl import or_ as _or
from ixsimpl._ixsimpl import pw as _pw
from ixsimpl._ixsimpl import same_node as _same_node
from ixsimpl._ixsimpl import xor_ as _xor


class Expr(_Expr):
    """Expression node with Python-level extensions."""

    @functools.cached_property
    def free_symbols(self) -> frozenset[Expr]:
        """Set of all symbol nodes appearing in this expression."""
        syms: set[Expr] = set()
        stack: list[_Expr] = [self]
        while stack:
            node = stack.pop()
            if node.tag == SYM:
                syms.add(node)  # type: ignore[arg-type]
            else:
                for i in range(node.nchildren):
                    stack.append(node.child(i))
        return frozenset(syms)


_set_expr_class(Expr)


if TYPE_CHECKING:
    from collections.abc import Sequence

    from ixsimpl._ixsimpl import Context as _Context

    class Context(_Context):
        def sym(self, name: str) -> Expr: ...
        def parse(self, input: str) -> Expr: ...
        def int_(self, val: int) -> Expr: ...
        def rat(self, p: int, q: int) -> Expr: ...
        def true_(self) -> Expr: ...
        def false_(self) -> Expr: ...
        def eq(self, a: _Expr | int, b: _Expr | int) -> Expr: ...
        def ne(self, a: _Expr | int, b: _Expr | int) -> Expr: ...
        def simplify_batch(
            self,
            exprs: Sequence[_Expr],
            *,
            assumptions: Sequence[_Expr] | None = None,
        ) -> None: ...

    def floor(expr: Expr) -> Expr: ...
    def ceil(expr: Expr) -> Expr: ...
    def mod(a: Expr, b: Expr | int) -> Expr: ...
    def max_(a: Expr, b: Expr | int) -> Expr: ...
    def min_(a: Expr, b: Expr | int) -> Expr: ...
    def xor_(a: Expr, b: Expr | int) -> Expr: ...
    def and_(a: Expr, b: Expr | int) -> Expr: ...
    def or_(a: Expr, b: Expr | int) -> Expr: ...
    def not_(a: Expr) -> Expr: ...
    def pw(*branches: tuple[Expr | int, Expr | int]) -> Expr: ...
    def same_node(a: Expr, b: Expr) -> bool: ...

else:
    from ixsimpl._ixsimpl import Context

    floor = _floor
    ceil = _ceil
    mod = _mod
    max_ = _max
    min_ = _min
    xor_ = _xor
    and_ = _and
    or_ = _or
    not_ = _not
    pw = _pw
    same_node = _same_node

__all__ = [
    "ADD",
    "AND",
    "CEIL",
    "CMP",
    "CMP_EQ",
    "CMP_GE",
    "CMP_GT",
    "CMP_LE",
    "CMP_LT",
    "CMP_NE",
    "ERROR",
    "FALSE",
    "FLOOR",
    "INT",
    "MAX",
    "MIN",
    "MOD",
    "MUL",
    "NOT",
    "OR",
    "PARSE_ERROR",
    "PIECEWISE",
    "RAT",
    "SYM",
    "TRUE",
    "XOR",
    "Context",
    "Expr",
    "and_",
    "ceil",
    "floor",
    "max_",
    "min_",
    "mod",
    "not_",
    "or_",
    "pw",
    "same_node",
    "xor_",
]
