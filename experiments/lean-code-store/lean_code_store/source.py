"""Source text helpers: cut a range, split names, find a `deriving instance` command.

Ranges use lines that count from 1 and code point columns, as Lean's declaration ranges do.
"""

from __future__ import annotations

import re

from lean_code_store.facts import Range

PRIVATE_PREFIX = re.compile(r"^_private\.(?:.*?)\.0\.")
"""Lean's prefix of a private name: `_private.<module>.0.`."""

DERIVING_INSTANCE = re.compile(
    r"(?m)^[ \t]*deriving\s+instance\b.*?\bfor\s+[^\s,]+(?:\s*,\s*[^\s,]+)*", re.DOTALL)
"""A `deriving instance` command: the classes, `for`, and the comma-separated list of types."""


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


def deriving_command(lines: list[str], span: Range) -> Range | None:
    """The `deriving instance` command that contains a range.

    The command ends at the last type of its `for` list, also when the classes or the types
    continue on lines with the same indentation.
    """
    text = "\n".join(lines)
    position = offset(lines, span[0], span[1])
    for match in DERIVING_INSTANCE.finditer(text):
        start = match.start() + len(match.group(0)) - len(match.group(0).lstrip())
        if start <= position < match.end():
            return _range_of(text, start, match.end())
    return None


def _range_of(text: str, start: int, end: int) -> Range:
    """The range of two code point offsets; the UTF-16 columns are not computed."""
    start_line = text.count("\n", 0, start) + 1
    end_line = text.count("\n", 0, end) + 1
    start_column = start - (text.rfind("\n", 0, start) + 1)
    end_column = end - (text.rfind("\n", 0, end) + 1)
    return (start_line, start_column, start_column, end_line, end_column, end_column)
