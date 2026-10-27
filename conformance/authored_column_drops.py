"""Native inputs for ALTER TABLE DROP COLUMN (ADR 0019, D4, part 3).

The cases cover what a drop keeps (the other cells, their order, rowids, the other tables, indexes), what makes it
fail (a key, a UNIQUE column, the last column, a view, a missing table or column, a definition that still names the
column), a failed statement that leaves the rows as they were, a rollback, and the statements after the drop that
read, write or fail under the new shape. SQLite supplies every outcome through the query recorder.
"""

from conformance.authored_foreign_keys import profile as foreign_key_profile
from conformance.authored_queries import QueryCase
from conformance.authored_resolution import profile
from conformance.case_format import Json
from conformance.column_drop_setups import (
    CHILD, INDEXED, KEYED, READER, ROWIDS, ROWS, TABLE_KEYS, TABLE_RULES, TRIGGERED, VIEWED)
from conformance.native_record import record_sql

REMOVES = "R-44709-33024"
"""SQLite: the DROP COLUMN command removes the named column from the table and purges its data."""
CONDITIONS = "R-24098-10282"
"""SQLite: the DROP COLUMN command only works if no other part of the schema references the column, and it is no
PRIMARY KEY and has no UNIQUE constraint."""
SYNTAX = "R-58318-35349"
"""SQLite: the DROP COLUMN syntax is used to remove an existing column from a table."""


def definitions() -> list[QueryCase]:
    """The cases: the drop that works, what it keeps, its errors, and its later statements."""
    def case(name: str, setup: str, sql: str, requirements: tuple[str, ...], *features: str) -> QueryCase:
        """Give a case its name prefix and features."""
        return QueryCase("column-drop-" + name, setup, sql, requirements, ("column-drop", *features))

    return [
        case("rows", ROWS, "ALTER TABLE t DROP COLUMN b; SELECT * FROM t ORDER BY a;", (REMOVES,), "rows"),
        case("rows-last-column", ROWS, "ALTER TABLE t DROP COLUMN d; SELECT * FROM t ORDER BY a;", (REMOVES,), "rows"),
        case("rowids", ROWIDS, "ALTER TABLE r DROP COLUMN y; SELECT x,z FROM r ORDER BY x; "
             "INSERT INTO r VALUES('d','n'); SELECT x,z FROM r ORDER BY x;", (REMOVES,), "rows", "rowid"),
        case("other-table", ROWS, "ALTER TABLE t DROP COLUMN b; SELECT x,b FROM u ORDER BY x;", (REMOVES,), "scope"),
        case("index", ROWS, "ALTER TABLE t DROP COLUMN b; INSERT INTO t VALUES(7,0.5,40); "
             "SELECT a,c FROM t WHERE c > 1 ORDER BY c;", (REMOVES,), "index"),
        case("without-keyword", ROWS, "ALTER TABLE t DROP d; SELECT * FROM t ORDER BY a;", (SYNTAX,), "syntax"),
        case("case-insensitive", ROWS, "ALTER TABLE T DROP COLUMN B; SELECT * FROM t ORDER BY a;", (SYNTAX,), "case"),
        case("quoted", ROWS, 'ALTER TABLE t DROP COLUMN "b"; SELECT * FROM t ORDER BY a;', (SYNTAX,), "quoted"),
        case("old-name", ROWS, "ALTER TABLE t DROP COLUMN b; SELECT b FROM t;", (REMOVES,), "error"),
        case("insert-after", ROWS, "ALTER TABLE t DROP COLUMN b; INSERT INTO t VALUES(7,0.5,40); "
             "INSERT INTO t VALUES(8,'x',1.5,50);", (REMOVES,), "write", "error"),
        case("writes-after", ROWS, "ALTER TABLE t DROP COLUMN b; UPDATE t SET d = d + 1 WHERE c IS NULL; "
             "DELETE FROM t WHERE a = 1; SELECT * FROM t ORDER BY a;", (REMOVES,), "write"),
        case("generated-unrelated", KEYED, "ALTER TABLE t DROP COLUMN d; SELECT a,b,c FROM t ORDER BY a;", (REMOVES,),
             "generated"),
        case("primary-key", KEYED, "ALTER TABLE t DROP COLUMN a; SELECT * FROM t;", (CONDITIONS,), "key", "prepare-error"),
        case("unique", KEYED, "ALTER TABLE t DROP COLUMN b; SELECT * FROM t;", (CONDITIONS,), "key", "prepare-error"),
        case("primary-key-case", KEYED, "ALTER TABLE t DROP COLUMN A;", (CONDITIONS,), "key", "prepare-error"),
        case("last-column", "CREATE TABLE s(x INTEGER); INSERT INTO s VALUES(1);", "ALTER TABLE s DROP COLUMN x; SELECT * FROM s;",
             (CONDITIONS,), "prepare-error"),
        case("no-such-table", ROWS, "ALTER TABLE nope DROP COLUMN b;", (SYNTAX,), "prepare-error"),
        case("no-such-column", ROWS, "ALTER TABLE t DROP COLUMN nope;", (SYNTAX,), "prepare-error"),
        case("of-view", VIEWED, "ALTER TABLE v DROP COLUMN a;", (SYNTAX,), "view", "prepare-error"),
        case("of-index", ROWS, "ALTER TABLE ti DROP COLUMN c;", (SYNTAX,), "prepare-error"),
        case("schema-table", ROWS, "ALTER TABLE sqlite_master DROP COLUMN sql;", (SYNTAX,), "prepare-error"),
        case("index-reads-column", INDEXED, "ALTER TABLE t DROP COLUMN b; SELECT * FROM t;", (CONDITIONS,), "index",
             "prepare-error"),
        case("partial-index-reads-column", INDEXED, "ALTER TABLE t DROP COLUMN c; SELECT * FROM t;", (CONDITIONS,), "index",
             "prepare-error"),
        case("view-reads-column", VIEWED, "ALTER TABLE t DROP COLUMN b; SELECT * FROM v;", (CONDITIONS,), "view",
             "prepare-error"),
        case("view-unrelated", VIEWED, "ALTER TABLE t DROP COLUMN c; SELECT * FROM v ORDER BY a;", (REMOVES,), "view"),
        case("trigger-reads-column", TRIGGERED, "ALTER TABLE t DROP COLUMN b; INSERT INTO t VALUES(2,3);", (CONDITIONS,),
             "trigger", "prepare-error"),
        case("trigger-unrelated", TRIGGERED, "ALTER TABLE t DROP COLUMN c; INSERT INTO t VALUES(2,'z'); SELECT m FROM log;",
             (REMOVES,), "trigger"),
        case("table-check", TABLE_RULES, "ALTER TABLE t DROP COLUMN c; SELECT * FROM t;", (CONDITIONS,), "check",
             "prepare-error"),
        case("table-check-unrelated", TABLE_RULES, "ALTER TABLE t DROP COLUMN b; INSERT INTO t VALUES(1,3,0);",
             (REMOVES,), "check", "error"),
        case("table-unique", TABLE_KEYS, "ALTER TABLE t DROP COLUMN b; SELECT * FROM t;", (CONDITIONS,), "key",
             "prepare-error"),
        case("generated-reads-column", READER, "ALTER TABLE t DROP COLUMN b; SELECT * FROM t;", (CONDITIONS,), "generated",
             "prepare-error"),
        case("child-column", CHILD, "ALTER TABLE c DROP COLUMN pid; SELECT * FROM c;", (CONDITIONS,), "foreign-key",
             "prepare-error"),
        case("child-unrelated", CHILD, "ALTER TABLE c DROP COLUMN note; INSERT INTO c VALUES(11,9); SELECT count(*) FROM c;",
             (REMOVES,), "foreign-key", "error"),
        case("parent-unrelated", CHILD, "ALTER TABLE p DROP COLUMN extra; DELETE FROM p WHERE id=2; SELECT id FROM c;",
             (REMOVES,), "foreign-key"),
        case("failed-leaves-rows", KEYED, "ALTER TABLE t DROP COLUMN a; SELECT * FROM t ORDER BY a;", (CONDITIONS,),
             "key", "prepare-error"),
        case("rollback", ROWS, "BEGIN; ALTER TABLE t DROP COLUMN b; SELECT * FROM t ORDER BY a; ROLLBACK; "
             "SELECT * FROM t ORDER BY a;", (REMOVES,), "transaction"),
        case("commit-twice", ROWS, "BEGIN; ALTER TABLE t DROP COLUMN b; ALTER TABLE t DROP COLUMN d; COMMIT; "
             "SELECT * FROM t ORDER BY a;", (REMOVES,), "transaction"),
        case("counters", ROWS, "INSERT INTO t VALUES(7,'z',0.5,40); ALTER TABLE t DROP COLUMN b; "
             "SELECT changes(), total_changes();", (REMOVES,), "counters"),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 7 record: the migration runs on after an error, as the statements
    after a failed drop need. A case with the feature `foreign-key` runs under the measured profile with foreign keys
    on, any other case under SQLite's default measured profile."""
    selected = definitions() if cases is None else cases
    defaults, enforced = profile(()), foreign_key_profile()
    return [{**record_sql(case.setup, case.sql, name=case.name, requirements=list(case.requirements), outputs=True,
                          profile=enforced if "foreign-key" in case.features else defaults, run_on=True, counters=True),
             "part": "column-drops", "features": list(case.features)}
            for case in selected]
