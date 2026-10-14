"""Authored coverage cases of row-dependent writes (ADR 0012, amendment 1, slice 3b).

The cases follow the amendment's "Testing" list. Store-time affinity: each case writes
one value into a column of each affinity (INTEGER, NUMERIC, REAL, TEXT and BLOB) and
returns the stored values. UPDATE: values that read the old row, a swap, filters that
are NULL, false or true for some rows, `AND`, `OR`, `IS` and `IS NULL`, no match, a
NOT NULL and a unique failure after some rows match, an integer overflow to REAL, the
store of assigned values, and the boundary case of the slice 3a filter obligation, a
REAL `1.0` that equals the filter value `1`. Native SQLite is the only source of
outcomes. The cases use `conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

STORE = "CREATE TABLE s(i INTEGER, n NUMERIC, r REAL, x TEXT, b BLOB);"
"""An empty table with one column of each affinity."""

UPDATED = ("CREATE TABLE u(k INTEGER UNIQUE, v INTEGER, w TEXT, c, n INTEGER NOT NULL, m); "
           "INSERT INTO u VALUES(1, 10, 'a', 1.0, 1, NULL), (2, 20, 'b', NULL, 2, 5), (3, NULL, 'c', 3, 3, NULL);")
"""Three rows with a unique integer key, an INTEGER, a TEXT and an untyped column, a NOT
NULL column, and a column that is NULL in two rows; the untyped column holds the REAL
1.0 in the first row."""

TEXT_NUMBER = ("R-12079-51392", "R-36476-47203", "R-05192-57965", "R-18885-42713", "R-21926-12440")
"""Well-formed number text becomes INTEGER or REAL in numeric columns and stays TEXT in TEXT."""


def store(value: str) -> str:
    """INSERT the value into every column of `s` and return the stored values."""
    return f"INSERT INTO s VALUES({value}, {value}, {value}, {value}, {value}) RETURNING *;"


def definitions() -> list[QueryCase]:
    """The coverage cases of store-time affinity and row-dependent UPDATE."""
    case = QueryCase
    return [
        case("store-number-text", STORE, store("'3.0e+5'"), TEXT_NUMBER, ("store", "text", "number")),
        case("store-spaced-integer-text", STORE, store("' 12 '"), TEXT_NUMBER, ("store", "text", "spaces")),
        case("store-hex-text", STORE, store("'0x10'"), ("R-47301-17448",), ("store", "text", "hexadecimal")),
        case("store-other-text", STORE, store("'abc'"), ("R-47301-17448",), ("store", "text", "neighbor")),
        case("store-integer-text-beyond-64-bits", STORE, store("'9223372036854775808'"), ("R-27233-06819",),
             ("store", "text", "range")),
        case("store-exponent-overflow-text", STORE, store("'1e400'"), ("R-27233-06819",),
             ("store", "text", "infinity")),
        case("store-whole-real", STORE, store("5.0"), ("R-22849-20349", "R-54378-38553"), ("store", "real", "whole")),
        case("store-fraction-real", STORE, store("5.5"), ("R-25142-32967",), ("store", "real", "neighbor")),
        case("store-real-at-2-63", STORE, store("9223372036854775808.0"), ("R-22849-20349", "R-25142-32967"),
             ("store", "real", "range")),
        case("store-integer-into-real", STORE, store("9007199254740993"), ("R-18885-42713",),
             ("store", "integer", "rounding")),
        case("store-blob", STORE, store("X'3132'"), ("R-03366-15091",), ("store", "blob")),
        case("update-reads-old-row", UPDATED, "UPDATE u SET v = v + 1 RETURNING k, v;",
             ("R-36239-04077", "R-55869-30521"), ("update", "row-dependent", "every-row")),
        case("update-swap", UPDATED, "UPDATE u SET v = n, n = v WHERE v IS NOT NULL RETURNING k, v, n;",
             ("R-40598-36595",), ("update", "row-dependent", "swap")),
        case("update-null-filter", UPDATED, "UPDATE u SET w = 'x' WHERE c > 1 RETURNING k;", ("R-58095-46013",),
             ("update", "filter", "null")),
        case("update-and-or-filter", UPDATED,
             "UPDATE u SET w = 'y' WHERE (k = 1 OR k = 3) AND v IS NOT NULL RETURNING k;",
             ("R-58095-46013",), ("update", "filter", "and-or")),
        case("update-is-filter", UPDATED, "UPDATE u SET w = 'z' WHERE m IS NULL AND c IS 3 RETURNING k;",
             ("R-58095-46013",), ("update", "filter", "is")),
        case("update-no-match", UPDATED, "UPDATE u SET w = 'q' WHERE k = 99 RETURNING k;", ("R-58129-20729",),
             ("update", "filter", "empty-result")),
        case("update-not-null-failure", UPDATED, "UPDATE u SET n = m WHERE k >= 2 RETURNING k;",
             ("R-55069-12282",), ("update", "constraint-failure", "not-null")),
        case("update-unique-failure", UPDATED, "UPDATE u SET k = 5 WHERE k < 3 RETURNING k;", ("R-47224-48532",),
             ("update", "constraint-failure", "unique")),
        case("update-overflow-to-real", UPDATED,
             "UPDATE u SET v = v + 9223372036854775807 WHERE k = 2 RETURNING v;",
             ("R-36239-04077",), ("update", "row-dependent", "overflow")),
        case("update-stores-affinity", UPDATED, "UPDATE u SET v = '42', w = 7 WHERE k = 1 RETURNING v, w;",
             ("R-12079-51392", "R-54378-38553"), ("update", "store")),
        case("update-stores-row-value", UPDATED, "UPDATE u SET w = v + 1 WHERE k = 1 RETURNING w;",
             ("R-54378-38553", "R-36239-04077"), ("update", "store", "row-dependent")),
        case("update-key-number-text", UPDATED, "UPDATE u SET k = '7' WHERE k = 3 RETURNING k;", ("R-12079-51392",),
             ("update", "store", "key")),
        case("update-filter-real-equals-integer", UPDATED, "UPDATE u SET w = 'r' WHERE c = 1 RETURNING k;",
             ("R-29765-45832",), ("update", "filter", "real-equals-integer")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `row-writes`."""
    return query_records(definitions() if cases is None else cases, part="row-writes")
