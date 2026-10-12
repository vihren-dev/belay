"""Render the model's predicted tables in the form that SQLite's recordings use (ADR 0011).

The judge compares predictions with recorded observations in SQLite's catalog terms. This
module is the subject's side of that agreement: it states what SQLite would report in
`PRAGMA table_xinfo`, `index_list` and `index_xinfo` for a table of the model, and writes
rows and cells as the recordings do. `conformance.native_metadata.check_inventory` states the
same correspondence in the other direction.
"""

from conformance.case_format import Json

DECLARED_SPELLING = {"bigInt": "BIGINT", "timestamp": "TIMESTAMP", "boolean": "BOOLEAN", "untyped": ""}
"""Declared types whose spelling is not the affinity's name; `canonical` spells the affinity."""
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


def declared_type(column: dict[str, Json]) -> str:
    """The declared type that SQLite reports for a model column."""
    spelling = column["declaredType"]
    return str(column["affinity"]).upper() if spelling == "canonical" else DECLARED_SPELLING[str(spelling)]


def column_row(position: int, column: dict[str, Json], primary_key: list[str]) -> list[Json]:
    """One `PRAGMA table_xinfo` row: number, name, type, not-null, default, key position, hidden."""
    name = str(column["name"])
    key = primary_key.index(name) + 1 if name in primary_key else 0
    default = text_cell("CURRENT_TIMESTAMP") if column.get("defaultValue") == "currentTimestamp" else "null"
    return [integer_cell(position), text_cell(name), text_cell(declared_type(column)),
            integer_cell(int(bool(column["notNull"]))), default, integer_cell(key), integer_cell(0)]


def index_entry(table: str, columns: list[str], keys: list[str], name: str, unique: bool,
                origin: str, number: int) -> dict[str, Json]:
    """One `PRAGMA index_list` entry with its `index_xinfo` key rows."""
    return {"entry": [integer_cell(number), text_cell(name), integer_cell(int(unique)), text_cell(origin),
                      integer_cell(0)],
            "columns": [[integer_cell(rank), integer_cell(columns.index(key)), text_cell(key), integer_cell(0),
                         text_cell(BINARY), integer_cell(1)] for rank, key in enumerate(keys)]}


def indexes(name: str, table: dict[str, Json]) -> list[dict[str, Json]]:
    """Declared indexes, and the implicit unique indexes of UNIQUE constraints and of a primary
    key that is not the row id (an INTEGER PRIMARY KEY with the canonical spelling is)."""
    columns = [str(column["name"]) for column in table["columns"]]
    properties = table["properties"]
    primary = [str(key) for key in properties["primaryKey"]]
    implicit = [[str(key) for key in unique] for unique in properties["uniqueKeys"]]
    if primary:
        first = next(column for column in table["columns"] if column["name"] == primary[0])
        if len(primary) != 1 or first["affinity"] != "integer" or first["declaredType"] != "canonical":
            implicit.append(primary)
    entries = [index_entry(name, columns, keys, f"sqlite_autoindex_{name}_{number}", True, "u", number)
               for number, keys in enumerate(implicit, start=1)]
    entries += [index_entry(name, columns, [str(key) for key in index["columns"]], str(index["name"]),
                            bool(index["unique"]), "c", len(entries) + number)
                for number, index in enumerate(properties["indexes"])]
    return entries


def table_record(name: str, table: dict[str, Json]) -> dict[str, Json]:
    """One model table in the recorded table form."""
    primary = [str(key) for key in table["properties"]["primaryKey"]]
    return {"name": name, "kind": "table", "withoutRowid": False, "foreignKeys": [],
            "columns": [column_row(position, column, primary) for position, column in enumerate(table["columns"])],
            "indexes": indexes(name, table),
            "rows": [{"identity": [integer_cell(int(row["rowid"]))], "values": [value_cell(v) for v in row["values"]]}
                     for row in table["rows"]]}


def view_record(tables: list[Json]) -> dict[str, Json]:
    """The model's `[name, table or null]` list as a recorded view; absent tables are left out."""
    return {"tables": [table_record(str(entry[0]), entry[1]) for entry in tables if entry[1] is not None]}


def output_record(output: Json) -> Json:
    """A model statement output in the recorded output form; `None` stays `None`."""
    if output is None:
        return None
    return {"columns": output["columns"], "changes": output["changes"],
            "rows": [[value_cell(value) for value in row] for row in output["rows"]]}
