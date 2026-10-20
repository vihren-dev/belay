"""Native SQLite table metadata in the conformance case format.

Native SQLite is the oracle: the PRAGMA inventories are only decoded here, never
compared with a Python translation. Lean compares them with the catalog that
resolution computes (`VerifierConformance.Native.tablesMatch`).
"""

from belay.sqlite.located import Json
from conformance.native_connection import Cell, Row, Connection


def quoted(name: str) -> str:
    """Quote an identifier without treating its contents as SQL."""
    return '"' + name.replace('"', '""') + '"'


def text(cell: Cell) -> str:
    """Decode metadata only; application TEXT remains arbitrary bytes."""
    kind, value = cell
    if kind != 3 or not isinstance(value, bytes):
        raise ValueError("Expected native textual schema metadata")
    return value.decode("utf-8")


def identifier(cell: Cell) -> str:
    """Fold an SQLite identifier with ASCII case folding, as SQLite compares names."""
    return text(cell).translate(str.maketrans("ABCDEFGHIJKLMNOPQRSTUVWXYZ", "abcdefghijklmnopqrstuvwxyz"))


def integer(cell: Cell) -> int:
    """Reject coerced native metadata and rowids."""
    kind, value = cell
    if kind != 1 or not isinstance(value, int):
        raise ValueError("Expected native integer")
    return value


def native_columns(info: list[Row]) -> list[Json]:
    """Decode `PRAGMA table_xinfo` rows: name, declared type, NOT NULL and default text.

    Hidden columns belong to virtual and generated tables, which the frontend
    refuses, so one here is evidence corruption.
    """
    columns: list[Json] = []
    for number, (cid, name, declared, not_null, default, _, hidden) in enumerate(info):
        if integer(cid) != number or integer(hidden) != 0:
            raise ValueError("Unexpected native column inventory")
        columns.append({"name": text(name), "declaredType": text(declared), "notNull": bool(integer(not_null)),
                        "defaultValue": None if default[0] == 5 else text(default)})
    return columns


def native_keys(info: list[Row], indexes: list[tuple[Row, list[Row]]]) -> tuple[list[int], list[Json], list[Json]]:
    """Decode the primary key and the UNIQUE and explicit indexes of one table.

    The primary key lists column positions in key order. UNIQUE constraint indexes
    (origin `u`) give key positions; explicit indexes (origin `c`) give their name, the
    position of each key term (`None` for an expression, column -2), uniqueness, and,
    only when present, the sort order of each term and the partial flag. The primary-key
    index (origin `pk`) repeats the key.
    """
    primary = [number for _, number in sorted((integer(row[5]), number) for number, row in enumerate(info)
                                              if integer(row[5]))]
    unique_keys: list[Json] = []
    explicit: list[Json] = []
    for (_, name, unique, origin, partial), index_columns in indexes:
        positions: list[Json] = []
        orders: list[Json] = []
        for _, cid, _, descending, collation, key in index_columns:
            if not integer(key):
                continue  # Auxiliary rowid is not part of the declared index key.
            expression = integer(cid) == -2 and text(origin) == "c"
            if (integer(cid) < 0 and not expression) or text(collation) != "BINARY" or (
                    integer(descending) and text(origin) == "u"):
                raise ValueError(f"Unexpected native index key: {text(name)}")
            positions.append(None if integer(cid) == -2 else integer(cid))
            orders.append(bool(integer(descending)))
        if integer(partial) and text(origin) != "c":
            raise ValueError(f"Unexpected partial native index: {text(name)}")
        if text(origin) == "c":
            index: dict[str, Json] = {"name": text(name), "columns": positions, "unique": bool(integer(unique))}
            if any(orders):
                index["descending"] = orders
            if integer(partial):
                index["partial"] = True
            explicit.append(index)
        elif text(origin) == "u" and integer(unique):
            unique_keys.append(positions)
        elif text(origin) != "pk":
            raise ValueError(f"Unexpected native index origin: {text(name)}")
    return primary, unique_keys, explicit


def native_table(name: str, info: list[Row], indexes: list[tuple[Row, list[Row]]],
                 rows: list[Json]) -> dict[str, Json]:
    """One native table of a case: its name in `sqlite_schema`, metadata and encoded rows."""
    primary, unique_keys, explicit = native_keys(info, indexes)
    return {"name": name, "columns": native_columns(info), "primaryKey": list(primary), "uniqueKeys": unique_keys,
            "indexes": explicit, "rows": rows}


def table_metadata(connection: Connection, name: str) -> tuple[list[Row], list[tuple[Row, list[Row]]]]:
    """Query `PRAGMA table_xinfo` and each index's `index_xinfo` of a live table."""
    info = connection.query(f"PRAGMA table_xinfo({quoted(name)});")
    indexes = [(entry, connection.query(f"PRAGMA index_xinfo({quoted(text(entry[1]))});"))
               for entry in connection.query(f"PRAGMA index_list({quoted(name)});")]
    return info, indexes
