"""Authored coverage cases of unique key values (ADR 0012, amendment 4, slice 5a).

The cases follow the "Tests" list of the slice 5a task: TEXT keys that differ by case and
that are equal; REAL keys with `1`, `1.0` and `'1'`; a key column without affinity with
`1`, `'1'`, `1.0` and `x'31'`; NUMERIC keys with `'1.0'` and `1`; composite keys of mixed
affinity with NULL; a duplicate within one INSERT; an UPDATE that makes and one that
avoids a duplicate TEXT key; a key of `CREATE UNIQUE INDEX` and a TEXT `PRIMARY KEY`;
and `RETURNING` of an INSERT that fails. Native SQLite is the only source of outcomes.
The cases use `conformance.authored_queries.QueryCase` and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE tx(k TEXT UNIQUE, v INTEGER); CREATE TABLE r(k REAL UNIQUE); CREATE TABLE b(k UNIQUE); "
          "CREATE TABLE n(k NUMERIC UNIQUE); CREATE TABLE m(a INTEGER, b TEXT, UNIQUE(a, b)); "
          "CREATE TABLE ix(a TEXT, v INTEGER); CREATE UNIQUE INDEX ia ON ix(a); "
          "CREATE TABLE pt(k TEXT PRIMARY KEY, v INTEGER); "
          "INSERT INTO tx VALUES('a', 1), ('b', 2); INSERT INTO r VALUES(1); INSERT INTO b VALUES(1); "
          "INSERT INTO n VALUES('1.0'); INSERT INTO m VALUES(1, 'x'); INSERT INTO ix VALUES('p', 1); "
          "INSERT INTO pt VALUES('k1', 1);")
"""One table per kind of key: TEXT, REAL, without affinity, NUMERIC, composite, of a
unique index, and a TEXT primary key, each with a row whose key the cases meet."""

UNIQUE = "R-30981-64168"
"""SQLite: each row must hold a unique combination of values in the columns of a UNIQUE constraint."""
NUMERIC_COMPARISON = "R-29765-45832"
"""SQLite: an INTEGER or REAL compared to another INTEGER or REAL is compared numerically."""
TEXT_COMPARISON = "R-53528-47027"
"""SQLite: the BINARY collation compares strings with memcmp(), whatever the encoding."""
NULL_DISTINCT = "R-00404-17670"
"""SQLite: NULL values are distinct from all other values, also other NULLs, in a UNIQUE key."""


def definitions() -> list[QueryCase]:
    """The coverage cases of unique key values."""
    case = QueryCase
    return [
        case("key-text-case", TABLES, "INSERT INTO tx VALUES('A', 3) RETURNING k;", (UNIQUE, TEXT_COMPARISON),
             ("key", "text")),
        case("key-text-duplicate", TABLES, "INSERT INTO tx VALUES('a', 3);", (UNIQUE, TEXT_COMPARISON),
             ("key", "text", "constraint")),
        case("key-real-integer", TABLES, "INSERT INTO r VALUES(1);", (UNIQUE, NUMERIC_COMPARISON),
             ("key", "real", "constraint")),
        case("key-real-text", TABLES, "INSERT INTO r VALUES('1');", (UNIQUE, NUMERIC_COMPARISON),
             ("key", "real", "affinity", "constraint")),
        case("key-real-other-text", TABLES, "INSERT INTO r VALUES('x') RETURNING k;", (UNIQUE,), ("key", "real")),
        case("key-untyped-classes", TABLES, "INSERT INTO b VALUES('1'), (x'31') RETURNING k;", (UNIQUE,),
             ("key", "untyped")),
        case("key-untyped-real", TABLES, "INSERT INTO b VALUES(1.0);", (UNIQUE, NUMERIC_COMPARISON),
             ("key", "untyped", "constraint")),
        case("key-numeric-text", TABLES, "INSERT INTO n VALUES(1);", (UNIQUE, NUMERIC_COMPARISON),
             ("key", "numeric", "constraint")),
        case("key-composite-null", TABLES, "INSERT INTO m VALUES(1, NULL), (1, NULL), (1, 'y') RETURNING a, b;",
             (UNIQUE, NULL_DISTINCT), ("key", "composite", "null")),
        case("key-composite-duplicate", TABLES, "INSERT INTO m VALUES('1', 'x');", (UNIQUE,),
             ("key", "composite", "affinity", "constraint")),
        case("key-duplicate-within-insert", TABLES, "INSERT INTO tx VALUES('c', 3), ('c', 4);", (UNIQUE,),
             ("key", "text", "constraint")),
        case("key-update-duplicate", TABLES, "UPDATE tx SET k = 'a' WHERE v = 2;", (UNIQUE,),
             ("key", "update", "constraint")),
        case("key-update-unique", TABLES, "UPDATE tx SET k = 'B' WHERE v = 2 RETURNING k;", (UNIQUE, TEXT_COMPARISON),
             ("key", "update")),
        case("key-index-text", TABLES, "INSERT INTO ix VALUES('p', 2);", (UNIQUE,), ("key", "index", "constraint")),
        case("key-primary-text", TABLES, "INSERT INTO pt VALUES('k1', 2);", (UNIQUE,),
             ("key", "primary", "constraint")),
        case("key-primary-null", TABLES, "INSERT INTO pt VALUES(NULL, 2), (NULL, 3) RETURNING k, v;",
             (NULL_DISTINCT,), ("key", "primary", "null")),
        case("key-returning-failed", TABLES, "INSERT INTO tx VALUES('c', 3), ('a', 4) RETURNING k;", (UNIQUE,),
             ("key", "returning", "constraint")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `keys`."""
    return query_records(definitions() if cases is None else cases, part="keys")
