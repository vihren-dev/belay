"""The `mention` relationships of one module, from its `.ilean` file.

The specification ("Column rules") gives the user of a mention: the container that the
`.ilean` file records, after folding, when it is a declaration; else the declaration with the
smallest full range that contains the usage, when exactly one has that range; else none.
"""

from __future__ import annotations

from collections.abc import Callable
from dataclasses import dataclass
import json
from typing import cast

from lean_code_store.facts import Range
from lean_code_store.folding import Declaration


@dataclass(frozen=True)
class Usage:
    """One usage of a constant that Lean recorded in the `.ilean` file."""

    target_module: str
    target_name: str
    line: int
    """Line of the start of the usage, counted from 1."""
    utf16_column: int
    container: str | None


@dataclass(frozen=True)
class MentionUser:
    """The user of one usage and the source that gave it."""

    user: Declaration | None
    source: str
    """`container`, `range` or `none`."""


def read_usages(ilean: str) -> list[Usage]:
    """The usages of constants in an `.ilean` document. Definitions are not usages."""
    document = cast(dict[str, object], json.loads(ilean))
    references = document.get("references")
    if not isinstance(references, dict):
        raise ValueError("The .ilean file has no references object; rebuild the module")
    usages: list[Usage] = []
    for key, entry in cast(dict[str, object], references).items():
        identifier = cast(dict[str, object], json.loads(key))
        constant = identifier.get("c")
        if not isinstance(constant, dict) or not isinstance(entry, dict):
            continue
        module, name = str(constant["m"]), str(constant["n"])
        for usage in cast(list[list[object]], cast(dict[str, object], entry).get("usages") or []):
            container = usage[4] if len(usage) > 4 and isinstance(usage[4], str) else None
            usages.append(Usage(module, name, int(cast(int, usage[0])) + 1,
                                int(cast(int, usage[1])), container))
    return usages


def _contains(span: Range, line: int, utf16_column: int) -> bool:
    """Whether a full range contains a position, compared in UTF-16 columns as `.ilean` gives them."""
    return (span[0], span[2]) <= (line, utf16_column) < (span[3], span[5])


def _size(span: Range) -> tuple[int, int]:
    """An order of ranges by size: lines first, then columns."""
    return (span[3] - span[0], span[5] - span[2])


def mention_user(usage: Usage, module: str, resolve: Callable[[str, str], Declaration | None],
                 declarations: dict[str, Range]) -> MentionUser:
    """The user of one usage, in the order of the specification.

    `declarations` maps each written declaration of the module to its full range.
    """
    if usage.container is not None:
        folded = resolve(module, usage.container)
        if folded is not None and folded[0] == module and folded[1] in declarations:
            return MentionUser(folded, "container")
        if folded is not None and folded[0] != module:
            return MentionUser(folded, "container")
    containing = [(name, span) for name, span in declarations.items()
                  if _contains(span, usage.line, usage.utf16_column)]
    if containing:
        smallest = min(_size(span) for _, span in containing)
        best = [name for name, span in containing if _size(span) == smallest]
        if len(best) == 1:
            return MentionUser((module, best[0]), "range")
    return MentionUser(None, "none")
