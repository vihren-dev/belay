"""Render the model's predicted tables in the form that SQLite's recordings use (ADR 0011).

The judge compares predictions with recorded observations in SQLite's catalog terms. This
module is the subject's side of that agreement. Lean writes each table of the model as
`PRAGMA table_xinfo` and `index_list` metadata (`VerifierConformance.Predict`); this module
states the PRAGMA rows that SQLite reports for it, including the indexes that SQLite makes
for keys, and writes rows and cells as the recordings do.
"""

from conformance.case_format import Json

BINARY = "BINARY"
"""The collation of a column or an index term without COLLATE."""


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
    """One `PRAGMA table_xinfo` row: number, name, type, not-null, default, key position, and
    hidden: 2 for a VIRTUAL and 3 for a STORED generated column, else 0."""
    key = primary_key.index(position) + 1 if position in primary_key else 0
    default = "null" if column["defaultValue"] is None else text_cell(str(column["defaultValue"]))
    return [integer_cell(position), text_cell(str(column["name"])), text_cell(str(column["declaredType"])),
            integer_cell(int(bool(column["notNull"]))), default, integer_cell(key),
            integer_cell(int(column.get("hidden", 0)))]


def index_entry(names: list[str], keys: list[int | None], name: str, unique: bool, origin: str,
                number: int, descending: list[bool], collations: list[str],
                partial: bool = False) -> dict[str, Json]:
    """One `PRAGMA index_list` entry with its `index_xinfo` key rows: a column key by its
    position and name, an expression key as column -2 without a name, each with its sort
    order and collation; `partial` marks an index with a `WHERE` filter."""
    return {"entry": [integer_cell(number), text_cell(name), integer_cell(int(unique)), text_cell(origin),
                      integer_cell(int(partial))],
            "columns": [[integer_cell(rank), integer_cell(-2 if key is None else key),
                         "null" if key is None else text_cell(names[key]),
                         integer_cell(int(order)), text_cell(collation), integer_cell(1)]
                        for rank, (key, order, collation) in enumerate(zip(keys, descending, collations,
                                                                            strict=True))]}


def declared_index(names: list[str], index: dict[str, Json], number: int) -> dict[str, Json]:
    """One declared index of the prediction: its key terms (`None` for an expression), and its
    sort orders, collations and partial flag, which the prediction gives only when present."""
    keys = [None if key is None else int(key) for key in index["columns"]]
    orders = [bool(order) for order in index.get("descending") or [False] * len(keys)]
    collations = [str(collation) for collation in index.get("collations") or [BINARY] * len(keys)]
    return index_entry(names, keys, str(index["name"]), bool(index["unique"]), "c", number, orders, collations,
                       bool(index.get("partial", False)))


def indexes(table: dict[str, Json], rowid_primary_key: bool, descending_key: bool,
            column_collations: list[str]) -> list[dict[str, Json]]:
    """Declared indexes, and the implicit unique indexes of UNIQUE constraints and of a primary
    key that is not the row id; a `PRIMARY KEY DESC` key gives a descending index, and an
    implicit index compares each column under the column's collation."""
    name = str(table["name"])
    names = [str(column["name"]) for column in table["columns"]]
    primary = [int(key) for key in table["primaryKey"]]
    implicit = [("u", [int(key) for key in unique], False) for unique in table["uniqueKeys"]]
    if primary and not rowid_primary_key:
        implicit.append(("pk", primary, descending_key))
    entries = [index_entry(names, list(keys), f"sqlite_autoindex_{name}_{number}", True, origin, number,
                           [descending] * len(keys), [column_collations[key] for key in keys])
               for number, (origin, keys, descending) in enumerate(implicit, start=1)]
    entries += [declared_index(names, index, len(entries) + number) for number, index in enumerate(table["indexes"])]
    return entries


def foreign_key_rows(keys: list[Json]) -> list[list[Json]]:
    """The `PRAGMA foreign_key_list` rows of a table's foreign keys, given in the order in
    which SQLite creates them: SQLite numbers them in the reverse order, gives one row per
    column, NULL as the referenced column of a key without a column list, and the match
    `NONE`."""
    rows: list[list[Json]] = []
    for number, key in enumerate(reversed(keys)):
        referenced = [str(name) for name in key["referenced"]]
        for sequence, column in enumerate(key["columns"]):
            rows.append([integer_cell(number), integer_cell(sequence), text_cell(str(key["table"])),
                         text_cell(str(column)), text_cell(referenced[sequence]) if referenced else "null",
                         text_cell(str(key["onUpdate"])), text_cell(str(key["onDelete"])), text_cell("NONE")])
    return rows


def table_record(predicted: dict[str, Json]) -> dict[str, Json]:
    """One model table in the recorded table form. A row's identity is its rowid, or its
    primary-key cells in a `WITHOUT ROWID` table, as the recorder writes it."""
    table = predicted["table"]
    primary = [int(key) for key in table["primaryKey"]]
    without_rowid = bool(table.get("withoutRowid", False))

    def identity(row: dict[str, Json]) -> list[Json]:
        """The row's identity as the recorder writes it: its primary-key cells in a `WITHOUT
        ROWID` table, else its rowid."""
        values = row["values"]
        return ([value_cell(values[key]) for key in primary] if without_rowid
                else [integer_cell(int(row["rowid"]))])
    return {"name": table["name"], "kind": "table", "withoutRowid": without_rowid,
            "foreignKeys": foreign_key_rows(list(predicted.get("foreignKeys") or [])),
            "columns": [column_row(position, column, primary) for position, column in enumerate(table["columns"])],
            "indexes": indexes(table, bool(predicted["rowidPrimaryKey"]), bool(predicted["primaryKeyDescending"]),
                               [str(collation) for collation in
                                predicted.get("collations") or [BINARY] * len(table["columns"])]),
            "rows": [{"identity": identity(row), "values": [value_cell(v) for v in row["values"]]}
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
