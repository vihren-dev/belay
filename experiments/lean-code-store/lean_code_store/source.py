"""Source text helpers: cut a range and split names.

Ranges use lines that count from 1 and code point columns, as Lean's declaration ranges do.
"""

from __future__ import annotations

import re

from lean_code_store.facts import Range

PRIVATE_PREFIX = re.compile(r"^_private\.(?:.*?)\.0\.")
"""Lean's prefix of a private name: `_private.<module>.0.`."""


def name_components(name: str) -> list[str]:
    """The components of a Lean name, split at each dot.

    An escaped component that contains a dot (`«a.b»`) is split into two components.
    """
    return name.split(".")


def user_name(name: str) -> str:
    """A name without Lean's private prefix."""
    return PRIVATE_PREFIX.sub("", name, count=1)


def offset(lines: list[str], line: int, column: int) -> int:
    """The code point offset of a line and column in the text that `lines` split."""
    return sum(len(text) + 1 for text in lines[: line - 1]) + column


def range_text(lines: list[str], span: Range) -> str:
    """The text of a range."""
    text = "\n".join(lines)
    return text[offset(lines, span[0], span[1]): offset(lines, span[3], span[4])]
