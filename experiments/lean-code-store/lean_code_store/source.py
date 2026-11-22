"""Source text helpers: cut a range, split names, find a `deriving instance` command.

Ranges use lines that count from 1 and code point columns, as Lean's declaration ranges do.
"""

from __future__ import annotations

import re

from lean_code_store.facts import Range

PRIVATE_PREFIX = re.compile(r"^_private\.(?:.*?)\.0\.")
"""Lean's prefix of a private name: `_private.<module>.0.`."""

DERIVING_INSTANCE = re.compile(r"(?m)^[ \t]*deriving[ \t]+instance\b")
"""The start of a `deriving instance` command."""


def name_components(name: str) -> list[str]:
    """The components of a Lean name. Escaped components with dots are not split correctly.

    No name of the default selection has such a component (the prototype run checks this).
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
    """The `deriving instance` command that contains a range, as a range of whole lines.

    The command ends before the next line that is empty or starts in column 0.
    """
    text = "\n".join(lines)
    position = offset(lines, span[0], span[1])
    starts = [match.start() for match in DERIVING_INSTANCE.finditer(text) if match.start() <= position]
    if not starts:
        return None
    start_line = text.count("\n", 0, starts[-1]) + 1
    end_line = start_line
    while end_line < len(lines) and lines[end_line].strip() and lines[end_line][0] in " \t":
        end_line += 1
    if not start_line <= span[0] <= end_line:
        return None
    start_column = len(lines[start_line - 1]) - len(lines[start_line - 1].lstrip())
    end_column = len(lines[end_line - 1])
    return (start_line, start_column, start_column, end_line, end_column, end_column)
