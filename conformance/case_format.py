"""The version 3 conformance case: statement syntax and native truth.

A case carries the schema and migration as the Lean `Syntax` JSON of
`belay.sqlite.syntax`, and each native observation as tables with their PRAGMA
metadata (`conformance.native_metadata`) and typed rows. Lean decodes it with
`Belay.Sqlite.Conformance.decodeCase`.
"""

from typing import TypeAlias

from belay.sqlite.located import Json

__all__ = ["CASE_VERSION", "Cell", "Json", "cell_wire", "literal_cell", "row_wire"]

CASE_VERSION = 3
"""The case version that Lean's `decodeCase` accepts."""

Cell: TypeAlias = tuple[int, int | bytes | None]
"""A typed SQLite cell: fundamental datatype code and payload."""


def cell_wire(cell: Cell) -> Json:
    """TEXT and BLOB are byte arrays; REAL is its unsigned 64-bit decimal bit string."""
    kind, value = cell
    if kind == 5 and value is None:
        return "null"
    if kind in (1, 2) and isinstance(value, int):
        return {"integer": {"value": value}} if kind == 1 else {"real": {"bits": str(value)}}
    if kind in (3, 4) and isinstance(value, bytes):
        return {"text" if kind == 3 else "blob": {"bytes": list(value)}}
    raise ValueError("Invalid typed SQLite cell")


def literal_cell(value: int | str | bytes | None) -> Cell:
    """Encode a Python literal as the typed cell that SQLite stores without conversion."""
    if value is None:
        return 5, None
    if isinstance(value, int):
        return 1, value
    return (3, value.encode()) if isinstance(value, str) else (4, value)


def row_wire(rowid: int, cells: tuple[Cell, ...]) -> Json:
    """One stored row: its physical rowid and typed cells in column order."""
    return {"rowid": rowid, "values": [cell_wire(cell) for cell in cells]}
