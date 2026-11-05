"""Native inputs for CREATE TABLE and CREATE INDEX with IF NOT EXISTS (ADR 0030, slice 1).

The cases follow the table "Conditional creation: SQLite" of the ADR: each kind of object of the
name (none, a table, a view, an index, a trigger) for both statements; the checks before the name
check (a reserved name, a missing table, a view as the table); bodies that SQLite does not read on
an existing object; `UNIQUE` over duplicate rows with an existing and a free name; the counters
after a no-op; a no-op in a transaction that rolls back; ASCII case folding of names; and the
clause in the schema description. SQLite supplies every outcome through the query recorder.
"""

from conformance.authored_queries import QueryCase
from conformance.authored_resolution import profile
from conformance.case_format import Json
from conformance.native_record import record_sql

TABLES = "CREATE TABLE t(a INTEGER, b TEXT); INSERT INTO t VALUES(1, 'x'), (1, 'y'); CREATE INDEX i ON t(b);"
"""A table with a duplicate value in `a` and an index: a database that the kernel cases can hold."""
OBJECTS = TABLES + " CREATE VIEW v AS SELECT a FROM t; CREATE TRIGGER tr AFTER INSERT ON t BEGIN SELECT 1; END;"
"""`TABLES` with a view and a trigger: one object of each kind."""

TABLE_NO_OP = "R-33917-24086"
"""SQLite: with IF NOT EXISTS, a table or view of the name makes CREATE TABLE a no-op."""
TABLE_INDEX_ERROR = "R-16465-40078"
"""SQLite: an existing index of the name is still an error for CREATE TABLE IF NOT EXISTS."""
INDEX_NO_OP = "R-16085-53730"
"""SQLite: with IF NOT EXISTS, an index of the name makes CREATE INDEX a no-op."""


def definitions() -> list[QueryCase]:
    """The cases: each kind of object of the name, the errors before the name check, the bodies that a
    no-op does not read, uniqueness, counters, a rollback, names and the schema description."""
    def case(name: str, sql: str, requirements: tuple[str, ...], *features: str,
             setup: str = TABLES) -> QueryCase:
        """Give a case its name prefix and features."""
        return QueryCase("conditional-creation-" + name, setup, sql, requirements, ("if-not-exists", *features))

    return [
        case("table-over-table", "CREATE TABLE IF NOT EXISTS t(z); SELECT a, b FROM t ORDER BY b;",
             (TABLE_NO_OP,), "table", "no-op"),
        case("table-over-view", "CREATE TABLE IF NOT EXISTS v(z); SELECT a FROM v ORDER BY a;",
             (TABLE_NO_OP,), "table", "no-op", setup=OBJECTS),
        case("table-over-index", "CREATE TABLE IF NOT EXISTS i(z);", (TABLE_INDEX_ERROR,), "table", "prepare-error"),
        case("table-over-trigger", "CREATE TABLE IF NOT EXISTS tr(z); INSERT INTO tr VALUES(5); SELECT z FROM tr;",
             (TABLE_NO_OP,), "table", "trigger", setup=OBJECTS),
        case("table-free", "CREATE TABLE IF NOT EXISTS n(z PRIMARY KEY); INSERT INTO n VALUES(1); "
             "INSERT INTO n VALUES(1);", (TABLE_NO_OP,), "table", "create"),
        case("table-reserved", "CREATE TABLE IF NOT EXISTS sqlite_x(z);", (TABLE_NO_OP,), "table", "prepare-error"),
        case("table-reserved-master", "CREATE TABLE IF NOT EXISTS sqlite_master(z);", (TABLE_NO_OP,), "table",
             "prepare-error"),
        case("table-body-duplicate-column", "CREATE TABLE IF NOT EXISTS t(a, a); SELECT a, b FROM t ORDER BY b;",
             (TABLE_NO_OP,), "table", "body"),
        case("table-body-check", "CREATE TABLE IF NOT EXISTS t(a, CHECK (nosuch > 0));", (TABLE_NO_OP,), "table",
             "body"),
        case("table-body-without-rowid", "CREATE TABLE IF NOT EXISTS t(a) WITHOUT ROWID;", (TABLE_NO_OP,), "table",
             "body"),
        case("table-body-strict", "CREATE TABLE IF NOT EXISTS t(a FOO) STRICT;", (TABLE_NO_OP,), "table", "body"),
        case("index-over-index", "CREATE TABLE u(c); CREATE UNIQUE INDEX IF NOT EXISTS i ON u(c); "
             "INSERT INTO u VALUES(1), (1); SELECT c FROM u;", (INDEX_NO_OP,), "index", "no-op"),
        case("index-over-table", "CREATE INDEX IF NOT EXISTS t ON t(a);", (INDEX_NO_OP,), "index", "prepare-error"),
        case("index-over-view", "CREATE INDEX IF NOT EXISTS v ON t(a);", (INDEX_NO_OP,), "index", "prepare-error",
             setup=OBJECTS),
        case("index-over-trigger", "CREATE INDEX IF NOT EXISTS tr ON t(a); CREATE INDEX tr ON t(b);",
             (INDEX_NO_OP,), "index", "trigger", setup=OBJECTS),
        case("index-free", "CREATE INDEX IF NOT EXISTS j ON t(a); CREATE INDEX j ON t(b);", (INDEX_NO_OP,), "index",
             "create"),
        case("index-missing-table", "CREATE INDEX IF NOT EXISTS i ON missing(a);", (INDEX_NO_OP,), "index",
             "prepare-error", "order"),
        case("index-view-target", "CREATE INDEX IF NOT EXISTS i ON v(a);", (INDEX_NO_OP,), "index",
             "prepare-error", "order", setup=OBJECTS),
        case("index-reserved-table", "CREATE INDEX IF NOT EXISTS i ON sqlite_master(name);", (INDEX_NO_OP,),
             "index", "prepare-error", "order"),
        case("index-reserved-name", "CREATE INDEX IF NOT EXISTS sqlite_i ON t(a);", (INDEX_NO_OP,), "index",
             "prepare-error", "order"),
        case("index-body-unknown-column", "CREATE INDEX IF NOT EXISTS i ON t(nosuch);", (INDEX_NO_OP,), "index",
             "body"),
        case("index-body-filter", "CREATE INDEX IF NOT EXISTS i ON t(a) WHERE nosuch > 0;", (INDEX_NO_OP,), "index",
             "body"),
        case("index-body-random", "CREATE INDEX IF NOT EXISTS i ON t(random());", (INDEX_NO_OP,), "index", "body"),
        case("index-body-collation", "CREATE INDEX IF NOT EXISTS i ON t(a COLLATE nosuchcoll);", (INDEX_NO_OP,),
             "index", "body"),
        case("unique-existing", "CREATE UNIQUE INDEX IF NOT EXISTS i ON t(a); INSERT INTO t VALUES(1, 'z');",
             (INDEX_NO_OP,), "index", "unique", "no-op"),
        case("unique-free", "CREATE UNIQUE INDEX IF NOT EXISTS j ON t(a);", (INDEX_NO_OP,), "index", "unique",
             "constraint"),
        case("counters", "INSERT INTO t VALUES(2, 'z'); CREATE TABLE IF NOT EXISTS t(z); "
             "CREATE INDEX IF NOT EXISTS i ON t(a); SELECT changes(), total_changes(), last_insert_rowid();",
             (TABLE_NO_OP, INDEX_NO_OP), "counters"),
        case("rollback", "BEGIN; CREATE TABLE IF NOT EXISTS t(z); CREATE TABLE IF NOT EXISTS n(z); "
             "CREATE INDEX IF NOT EXISTS j ON t(a); ROLLBACK; CREATE TABLE n(z); CREATE INDEX j ON t(a);",
             (TABLE_NO_OP, INDEX_NO_OP), "transaction"),
        case("ascii-folding", "CREATE TABLE IF NOT EXISTS T(z); CREATE INDEX IF NOT EXISTS I ON t(a); "
             'CREATE INDEX "Ix" ON t(a); CREATE INDEX IF NOT EXISTS "iX" ON t(b); SELECT a, b FROM T ORDER BY b;',
             (TABLE_NO_OP, INDEX_NO_OP), "names"),
        case("non-ascii-name", 'CREATE TABLE "Ä"(x); CREATE TABLE IF NOT EXISTS "ä"(y); INSERT INTO "ä" VALUES(1); '
             'SELECT y FROM "ä";', (TABLE_NO_OP,), "names"),
        case("schema", "INSERT INTO s VALUES(1); SELECT a FROM s;", (TABLE_NO_OP, INDEX_NO_OP), "schema",
             setup="CREATE TABLE IF NOT EXISTS s(a); CREATE TABLE IF NOT EXISTS s(b); "
                   "CREATE INDEX IF NOT EXISTS si ON s(a); CREATE INDEX IF NOT EXISTS si ON s(b);"),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 7 record under SQLite's default measured profile: the
    migration runs on after an error, as the statements after a failed creation need."""
    selected = definitions() if cases is None else cases
    defaults = profile(())
    return [{**record_sql(case.setup, case.sql, name=case.name, requirements=list(case.requirements), outputs=True,
                          profile=defaults, run_on=True, counters=True),
             "part": "conditional-creation", "features": list(case.features)}
            for case in selected]
