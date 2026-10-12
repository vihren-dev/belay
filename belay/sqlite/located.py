"""Statement syntax in the model's JSON transport, with the source range of each node.

A model restriction from Lean names a statement index and a node path. Each path
step is the argument position of a constructor or a structure field, then the
index in a list. `Located` keeps the same tree shape, so a path selects the byte
range of the node that the restriction refers to.
"""

from dataclasses import dataclass
from typing import TypeAlias

Json: TypeAlias = None | bool | int | str | list["Json"] | dict[str, "Json"]


@dataclass(frozen=True)
class Located:
    """One syntax value, its UTF-8 byte range and its located children in path order."""

    value: Json
    start: int
    end: int
    children: tuple["Located", ...] = ()

    def span(self, path: list[int]) -> tuple[int, int]:
        """Return the range of the deepest node on the path; a path past a leaf stops at the leaf."""
        node = self
        for step in path:
            if not 0 <= step < len(node.children):
                break
            node = node.children[step]
        return node.start, node.end


def leaf(value: Json, start: int, end: int) -> Located:
    """A value without located parts, such as a name or a flag."""
    return Located(value, start, end)


def sequence(items: list[Located], start: int, end: int) -> Located:
    """A list value whose path steps are the item indexes."""
    return Located([item.value for item in items], start, end, tuple(items))


def constructor(name: str, fields: list[tuple[str, Located]], start: int, end: int) -> Located:
    """A constructor with named arguments, encoded as Lean derives it: `{name: {field: value}}`."""
    return Located({name: {field: part.value for field, part in fields}}, start, end,
                   tuple(part for _, part in fields))


def structure(fields: list[tuple[str, Located]], start: int, end: int) -> Located:
    """A structure value, encoded as an object of its fields in declaration order."""
    return Located({field: part.value for field, part in fields}, start, end,
                   tuple(part for _, part in fields))


def pair(first: Located, second: Located, start: int, end: int) -> Located:
    """A Lean pair, encoded as a two-element array."""
    return Located([first.value, second.value], start, end, (first, second))
