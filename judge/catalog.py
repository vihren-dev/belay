"""The comparison form of one observation, built only from what SQLite recorded.

The subject writes its prediction in the same raw form as a recorded observation. Both are
reduced to this form by the judge, so the subject cannot influence the reduction, and a
step agrees when the two forms are equal. The form uses SQLite's own catalog terms
(`PRAGMA table_xinfo`, `index_list`, `index_xinfo`, `foreign_key_list`) and typed rows. It
never translates recorded SQL. SQLite treats identifiers and type names without regard to
ASCII case, so the form folds them; it keeps string literals exactly.
"""

import json

from judge.cells import Json, checked_cell, integer, text

DEFAULT_KEYWORDS = frozenset({"CURRENT_TIMESTAMP", "CURRENT_DATE", "CURRENT_TIME", "NULL", "TRUE", "FALSE"})
"""Default expressions that are keywords; SQLite records them as written, in any case."""
FOLD = str.maketrans("ABCDEFGHIJKLMNOPQRSTUVWXYZ", "abcdefghijklmnopqrstuvwxyz")
"""ASCII case folding, as SQLite applies it to identifiers."""


def fold(name: str) -> str:
    """An identifier in the case that SQLite ignores."""
    return name.translate(FOLD)


def default_form(value: Json) -> str | None:
    """A recorded default: `None` without one, keywords in upper case, other text exactly."""
    if value == "null":
        return None
    sql = text(value)
    return sql.upper() if sql.upper() in DEFAULT_KEYWORDS else sql


def column_form(row: list[Json], position: int) -> list[Json]:
    """One `PRAGMA table_xinfo` row: name, declared type, not-null, default, key position, hidden."""
    cid, name, declared, not_null, default, primary, hidden = row
    if integer(cid) != position:
        raise ValueError(f"column {position} is recorded with number {integer(cid)}")
    return [fold(text(name)), text(declared).upper(), integer(not_null), default_form(default),
            integer(primary), integer(hidden)]


def index_form(index: dict[str, Json]) -> list[Json]:
    """One index: its origin, its name if declared, uniqueness, partiality and key columns.

    Implicit indexes (from PRIMARY KEY and UNIQUE) get generated names, so the form keeps
    no name for them and does not separate the two origins. A key column without a name is
    an expression.
    """
    _, name, unique, origin, partial = index["entry"]
    keys = [[None if column == "null" else fold(text(column)), integer(descending), text(collation).upper()]
            for _, _, column, descending, collation, key in index["columns"] if integer(key)]
    declared = text(origin) == "c"
    return ["declared" if declared else "implicit", fold(text(name)) if declared else None,
            integer(unique), integer(partial), keys]


def table_form(table: dict[str, Json]) -> dict[str, Json]:
    """One table in the comparison form, with rows sorted by their identity.

    A row's identity is its row id, or its primary-key cells in a WITHOUT ROWID table.
    """
    rows = [[[checked_cell(cell) for cell in row["identity"]], [checked_cell(cell) for cell in row["values"]]]
            for row in table["rows"]]
    return {"kind": table["kind"], "withoutRowid": table["withoutRowid"],
            "columns": [column_form(row, position) for position, row in enumerate(table["columns"])],
            "indexes": sorted((index_form(index) for index in table["indexes"]), key=json.dumps),
            "foreignKeys": [[checked_cell(cell) for cell in row] for row in table.get("foreignKeys", [])],
            "rows": sorted(rows, key=lambda row: json.dumps(row[0], sort_keys=True))}


def tables_form(view: dict[str, Json]) -> dict[str, Json]:
    """All tables of one recorded view (visible or persisted), by folded name."""
    forms = {fold(table["name"]): table_form(table) for table in view["tables"]}
    if len(forms) != len(view["tables"]):
        raise ValueError("two recorded tables have the same folded name")
    return forms


def step_form(observation: dict[str, Json]) -> dict[str, Json]:
    """One recorded step: both table views, the transaction state and the primary result code."""
    return {"visible": tables_form(observation["visible"]), "persisted": tables_form(observation["persisted"]),
            "transactionOpen": observation["transactionOpen"], "primaryCode": observation.get("primaryCode", 0)}
