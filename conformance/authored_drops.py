"""Authored coverage cases of `DROP INDEX` and `DROP TABLE` (ADR 0014, slice 7).

The cases follow the "Tests" list of the slice 7 task: each prepare error and `IF EXISTS`;
a DROP followed by statements on later objects; an index of a later table that keeps its
table; a DROP that a ROLLBACK undoes; and a CREATE after a DROP of the same name. Native
SQLite is the only source of outcomes. The cases use `conformance.authored_queries.QueryCase`
and its recorder.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.case_format import Json

TABLES = ("CREATE TABLE t(a INTEGER PRIMARY KEY, b TEXT UNIQUE, c INT); CREATE INDEX ti ON t(c); "
          "CREATE TABLE u(x INT, y TEXT); CREATE UNIQUE INDEX ui ON u(x); "
          "INSERT INTO t VALUES(1, 'p', 10), (2, 'q', 20); INSERT INTO u VALUES(5, 'r'), (6, 's');")
"""Two tables, each with an index and rows: `t` comes first, so a DROP of `t` moves `u` and
its index `ui` to lower catalog positions."""

DROP_TABLE = "R-01463-03846"
"""SQLite: the DROP TABLE statement removes a table added with CREATE TABLE."""
DROP_TABLE_DATA = "R-33950-57093"
"""SQLite: all indices and triggers associated with the table are also deleted."""
DROP_INDEX = "R-42037-15614"
"""SQLite: the DROP INDEX statement removes an index added with CREATE INDEX."""
TABLE_IF_EXISTS = "R-57089-01510"
"""SQLite: the optional IF EXISTS clause suppresses the error of a table that does not exist."""
TABLE_REMOVED = "R-40197-14811"
"""SQLite: the dropped table is completely removed from the database schema."""


def definitions() -> list[QueryCase]:
    """The coverage cases of DROP INDEX and DROP TABLE."""
    case = QueryCase
    return [
        case("drop-index", TABLES, "DROP INDEX ti; SELECT a, c FROM t WHERE c = 20;", (DROP_INDEX,),
             ("drop", "index")),
        case("drop-index-case", TABLES, "DROP INDEX TI; CREATE INDEX ti ON t(b, c); SELECT b FROM t;", (DROP_INDEX,),
             ("drop", "index", "create-after")),
        case("drop-table", TABLES, "DROP TABLE t; SELECT x, y FROM u;", (DROP_TABLE, DROP_TABLE_DATA),
             ("drop", "table")),
        case("drop-table-later-index", TABLES, "DROP TABLE t; INSERT INTO u VALUES(5, 'z');",
             (DROP_TABLE, DROP_TABLE_DATA), ("drop", "table", "positions")),
        case("drop-table-later-write", TABLES, "DROP TABLE t; INSERT INTO u VALUES(7, 'z'); "
             "UPDATE u SET y = 'w' WHERE x = 5; SELECT x, y FROM u;", (DROP_TABLE,), ("drop", "table", "positions")),
        case("drop-table-create-again", TABLES, "DROP TABLE t; CREATE TABLE t(z TEXT); INSERT INTO t VALUES('n'); "
             "SELECT z FROM t; SELECT x FROM u;", (DROP_TABLE,), ("drop", "table", "create-after")),
        case("drop-table-index-name-free", TABLES, "DROP TABLE t; CREATE INDEX ti ON u(y);", (DROP_TABLE_DATA,),
             ("drop", "table", "index")),
        case("drop-later-table", TABLES, "DROP TABLE u; SELECT a, b FROM t; INSERT INTO t VALUES(3, 'p', 1);",
             (DROP_TABLE,), ("drop", "table")),
        case("drop-index-then-table", TABLES, "DROP INDEX ui; DROP TABLE t; INSERT INTO u VALUES(5, 'dup'); "
             "SELECT x, y FROM u;", (DROP_INDEX, DROP_TABLE), ("drop", "index", "table")),
        case("drop-rollback", TABLES, "BEGIN; DROP TABLE t; ROLLBACK; SELECT a, b FROM t; SELECT x FROM u;",
             (DROP_TABLE,), ("drop", "transaction")),
        case("drop-commit", TABLES, "BEGIN; DROP INDEX ui; COMMIT; INSERT INTO u VALUES(5, 'dup'); SELECT x FROM u;",
             (DROP_INDEX,), ("drop", "transaction")),
        case("drop-no-such-table", TABLES, "DROP TABLE nope;", (TABLE_IF_EXISTS,), ("drop", "prepare-error")),
        case("drop-table-of-index", TABLES, "DROP TABLE ti;", (TABLE_IF_EXISTS,), ("drop", "prepare-error")),
        case("drop-table-if-exists", TABLES, "DROP TABLE IF EXISTS nope; DROP TABLE IF EXISTS ti; SELECT a FROM t;",
             (TABLE_IF_EXISTS,), ("drop", "if-exists")),
        case("drop-no-such-index", TABLES, "DROP INDEX nope;", (DROP_INDEX,), ("drop", "prepare-error")),
        case("drop-index-of-table", TABLES, "DROP INDEX t;", (DROP_INDEX,), ("drop", "prepare-error")),
        case("drop-index-if-exists", TABLES, "DROP INDEX IF EXISTS nope; DROP INDEX IF EXISTS u; SELECT x FROM u;",
             (DROP_INDEX,), ("drop", "if-exists")),
        case("drop-schema-table", TABLES, "DROP TABLE sqlite_master;", (DROP_TABLE,), ("drop", "prepare-error")),
        case("drop-schema-table-alias", TABLES, "DROP TABLE IF EXISTS Sqlite_Schema;", (DROP_TABLE,),
             ("drop", "prepare-error")),
        case("drop-temp-schema-table", TABLES, "DROP TABLE sqlite_temp_schema;", (DROP_TABLE,),
             ("drop", "prepare-error")),
        case("drop-then-missing", TABLES, "DROP TABLE t; SELECT a FROM t;", (TABLE_REMOVED,), ("drop", "prepare-error")),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 5 record with outputs, in the part `drops`."""
    return query_records(definitions() if cases is None else cases, part="drops")
