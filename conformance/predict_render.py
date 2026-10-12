"""Render the model's predicted tables in the form that SQLite's recordings use (ADR 0011).

The judge compares predictions with recorded observations in SQLite's catalog terms. This
module is the subject's side of that agreement. Lean writes each table of the model as
`PRAGMA table_xinfo` and `index_list` metadata (`VerifierConformance.Predict`); this module
states the PRAGMA rows that SQLite reports for it, including the indexes that SQLite makes
for keys, and writes rows and cells as the recordings do.
"""

from conformance.case_format import Json

BINARY = "BINARY"
"""The collation of every index key that the model supports."""


def text_cell(value: str) -> Json:
    """A TEXT cell, as recordings store metadata text."""
    return {"text": {"bytes": list(value.encode())}}


def integer_cell(value: int) -> Json:
    """An INTEGER cell, as recordings store metadata numbers and row ids."""
    return {"integer": {"value": value}}


def value_cell(value: Json) -> Json:
    """A model value in the recorded cell form; REAL bits are a decimal string there."""
    if value == "null":
        return value
    if isinstance(value, dict) and len(value) == 1:
        kind, payload = next(iter(value.items()))
        if kind == "real" and isinstance(payload, dict):
            return {"real": {"bits": str(payload["bits"])}}
        if kind in ("integer", "text", "blob"):
            return value
    raise ValueError(f"unknown model value: {value!r}")


def column_row(position: int, column: dict[str, Json], primary_key: list[int]) -> list[Json]:
    """One `PRAGMA table_xinfo` row: number, name, type, not-null, default, key position, hidden."""
    key = primary_key.index(position) + 1 if position in primary_key else 0
    default = "null" if column["defaultValue"] is None else text_cell(str(column["defaultValue"]))
    return [integer_cell(position), text_cell(str(column["name"])), text_cell(str(column["declaredType"])),
            integer_cell(int(bool(column["notNull"]))), default, integer_cell(key), integer_cell(0)]


def index_entry(names: list[str], keys: list[int], name: str, unique: bool, origin: str,
                number: int) -> dict[str, Json]:
    """One `PRAGMA index_list` entry with its `index_xinfo` key rows."""
    return {"entry": [integer_cell(number), text_cell(name), integer_cell(int(unique)), text_cell(origin),
                      integer_cell(0)],
            "columns": [[integer_cell(rank), integer_cell(key), text_cell(names[key]), integer_cell(0),
                         text_cell(BINARY), integer_cell(1)] for rank, key in enumerate(keys)]}


def indexes(table: dict[str, Json], rowid_primary_key: bool) -> list[dict[str, Json]]:
    """Declared indexes, and the implicit unique indexes of UNIQUE constraints and of a primary
    key that is not the row id."""
    name = str(table["name"])
    names = [str(column["name"]) for column in table["columns"]]
    primary = [int(key) for key in table["primaryKey"]]
    implicit = [("u", [int(key) for key in unique]) for unique in table["uniqueKeys"]]
    if primary and not rowid_primary_key:
        implicit.append(("pk", primary))
    entries = [index_entry(names, keys, f"sqlite_autoindex_{name}_{number}", True, origin, number)
               for number, (origin, keys) in enumerate(implicit, start=1)]
    entries += [index_entry(names, [int(key) for key in index["columns"]], str(index["name"]),
                            bool(index["unique"]), "c", len(entries) + number)
                for number, index in enumerate(table["indexes"])]
    return entries


def table_record(predicted: dict[str, Json]) -> dict[str, Json]:
    """One model table in the recorded table form."""
    table = predicted["table"]
    primary = [int(key) for key in table["primaryKey"]]
    return {"name": table["name"], "kind": "table", "withoutRowid": False, "foreignKeys": [],
            "columns": [column_row(position, column, primary) for position, column in enumerate(table["columns"])],
            "indexes": indexes(table, bool(predicted["rowidPrimaryKey"])),
            "rows": [{"identity": [integer_cell(int(row["rowid"]))], "values": [value_cell(v) for v in row["values"]]}
                     for row in table["rows"]]}


def view_record(tables: list[Json]) -> dict[str, Json]:
    """The model's tables of one view as a recorded view."""
    return {"tables": [table_record(table) for table in tables if isinstance(table, dict)]}


def output_record(output: Json) -> Json:
    """A model statement output in the recorded output form; `None` stays `None`."""
    if output is None:
        return None
    return {"columns": output["columns"], "changes": output["changes"],
            "rows": [[value_cell(value) for value in row] for row in output["rows"]]}
