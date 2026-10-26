"""Native inputs for INSERT from a query (ADR 0019, D4, amended 2026-10-25).

The cases cover the rows that the query gives and the statement that writes them: explicit and
implicit columns, defaults and generated values, INTEGER PRIMARY KEY and WITHOUT ROWID, bound
parameters, aggregates, sorting and compounds; each conflict path, RETURNING, triggers and foreign
keys; failures at preparation, in the source and in the insertion; the order of a source that SQLite
may read by its scan or by an index; and the later statements that observe partial effects. SQLite
supplies every outcome through the query recorder. The cases whose source SQLite may read in an
order that the model does not describe stay unmodeled.
"""

from conformance.authored_foreign_keys import profile as foreign_key_profile
from conformance.authored_queries import QueryCase
from conformance.authored_resolution import profile
from conformance.case_format import Json
from conformance.native_record import record_sql

TABLES = (
    "CREATE TABLE s(a INTEGER, b TEXT); INSERT INTO s VALUES(1,'x'),(2,'y'),(3,'z'); "
    "CREATE TABLE t(a INTEGER, b TEXT); "
    "CREATE TABLE k(id INTEGER PRIMARY KEY, v TEXT UNIQUE); INSERT INTO k VALUES(10,'y'); "
    "CREATE TABLE e(a INTEGER, b TEXT);"
)
"""A source with three rows, an empty target, a target with a rowid alias and a unique column
that holds one row, and an empty source."""
INDEXED = (
    "CREATE TABLE s(id INTEGER PRIMARY KEY, x INTEGER); CREATE INDEX sx ON s(x); "
    "INSERT INTO s VALUES(1,20),(2,10); CREATE TABLE t(id INTEGER PRIMARY KEY, name INTEGER);"
)
"""A source with an index on `x`, whose rows 20 and 10 are in the opposite order of the index."""
OVERFLOW = (
    "CREATE TABLE t(id INTEGER PRIMARY KEY); CREATE TABLE u(id INTEGER PRIMARY KEY); INSERT INTO u VALUES(5); "
    "CREATE TABLE s(x INTEGER); INSERT INTO s VALUES(5),(-9223372036854775808);"
)
"""A target, a target that already holds the first row, and a source with a row and then the smallest
integer, whose `abs` overflows. The last row inserted is the second row of the source, so that a
statement that writes the row 5 and then fails shows whether it wrote before it failed."""

TWO_ORDERS = (
    "CREATE TABLE s(id INTEGER PRIMARY KEY, x INTEGER); CREATE INDEX sx ON s(x); INSERT INTO s VALUES(1,20),(2,10); "
    "CREATE TABLE t(x INTEGER); CREATE TABLE log(id INTEGER PRIMARY KEY, x INTEGER); "
    "CREATE TRIGGER r AFTER INSERT ON t BEGIN INSERT INTO log(x) VALUES(new.x); END;"
)
"""A source that SQLite may read by its scan or by an index, and a target whose trigger logs each row."""

PRECEDENCE = (
    "CREATE TABLE src(x INTEGER); INSERT INTO src VALUES(2),(1),(-9223372036854775808); "
    "CREATE TABLE dest(x INTEGER UNIQUE); INSERT INTO dest VALUES(1);"
)
"""Source rows 2, 1 and the smallest integer, and a unique destination that holds 1."""
SORTED = (
    "CREATE TABLE src(id INTEGER PRIMARY KEY, x INTEGER, k INTEGER); "
    "INSERT INTO src VALUES(1,2,1),(2,1,2),(3,-9223372036854775808,3); "
    "CREATE TABLE dest(x INTEGER UNIQUE); INSERT INTO dest VALUES(1);"
)
"""Source rows ordered by `k`, and a unique destination that holds 1."""
TRIGGERED = (
    "CREATE TABLE s(a INTEGER, b TEXT); INSERT INTO s VALUES(1,'x'),(2,'y'); "
    "CREATE TABLE t(a INTEGER UNIQUE, b TEXT); CREATE TABLE log(x);"
)
"""A source, a unique target and a log table that triggers write."""
TRANSFER = (
    "CREATE TABLE s(a INTEGER UNIQUE); CREATE TABLE t(a INTEGER UNIQUE); "
    "INSERT INTO s VALUES(10),(20),(30); DELETE FROM s WHERE a=20;"
)
"""A source and a target with the same index, whose source rowids are 1 and 3."""
KEYS = (
    "CREATE TABLE p(id INTEGER PRIMARY KEY); INSERT INTO p VALUES(1),(2); "
    "CREATE TABLE c(id INTEGER PRIMARY KEY, p INTEGER REFERENCES p(id) ON DELETE CASCADE); "
    "CREATE TABLE s(a INTEGER); INSERT INTO s VALUES(1),(2),(3);"
)
"""A parent with two rows, a child with a cascade, and a source with a missing parent."""
SHAPES = (
    "CREATE TABLE s(a INTEGER, b TEXT); INSERT INTO s VALUES(1,'x'),(2,'y'); "
    "CREATE TABLE g(a INTEGER, b TEXT DEFAULT 'd', c INTEGER AS (a*2), d INTEGER DEFAULT 7); "
    "CREATE TABLE w(a INTEGER PRIMARY KEY, b TEXT) WITHOUT ROWID;"
)
"""A source, a target with a default and a generated column, and a WITHOUT ROWID target."""

ROWS = "R-52173-30215"
"""SQLite: a new entry is inserted for each row of data returned by the SELECT."""
ANY_SELECT = "R-31074-37730"
"""SQLite: any SELECT, also with ORDER BY and LIMIT, may be used in an INSERT of this form."""
COUNT = "R-58951-07798"
"""SQLite: without a column list, the SELECT gives as many columns as the table has."""
LISTED = "R-63614-47421"
"""SQLite: with a column list, the SELECT gives as many columns as the list has."""
FAIL = "R-31882-08811"
"""SQLite: the FAIL algorithm does not back out the prior changes of the failing statement."""


def definitions() -> list[QueryCase]:
    """The cases: each form of source and write, the failures, and the orders of the source."""
    def case(name: str, setup: str, sql: str, *features: str) -> QueryCase:
        """Give a case the requirements of INSERT from a query and its features."""
        return QueryCase("insert-query-" + name, setup, sql, (ROWS, ANY_SELECT), ("insert-query", *features))

    return [
        case("all-columns", TABLES, "INSERT INTO t SELECT a,b FROM s; SELECT a,b FROM t ORDER BY a;", "columns"),
        case("star", TABLES, "INSERT INTO t SELECT * FROM s; SELECT a,b FROM t ORDER BY a;", "columns", "star"),
        case("column-list", TABLES, "INSERT INTO t(b) SELECT b FROM s; SELECT a,b FROM t ORDER BY b;",
             "columns", "default"),
        case("reordered-list", TABLES, "INSERT INTO t(b,a) SELECT b,a FROM s; SELECT a,b FROM t ORDER BY a;", "columns"),
        case("rowid-alias", TABLES, "INSERT INTO k(v) SELECT b FROM s WHERE b<>'y'; SELECT id,v FROM k ORDER BY id;",
             "rowid", "alias"),
        case("affinity", TABLES, "INSERT INTO t SELECT b,a FROM s; SELECT a,b,typeof(a),typeof(b) FROM t ORDER BY b;",
             "affinity"),
        case("empty-source", TABLES, "INSERT INTO t SELECT a,b FROM e; SELECT count(*),changes() FROM t;", "empty"),
        case("filter", TABLES, "INSERT INTO t SELECT a,b FROM s WHERE a>1; SELECT a,b FROM t ORDER BY a;", "where"),
        case("expression", TABLES, "INSERT INTO t SELECT a*10,b||'!' FROM s; SELECT a,b FROM t ORDER BY a;", "expression"),
        case("constants", TABLES, "INSERT INTO t SELECT 1,'c'; SELECT a,b FROM t;", "no-from"),
        case("order-limit", TABLES, "INSERT INTO t SELECT a,b FROM s ORDER BY a DESC LIMIT 2; SELECT a,b FROM t ORDER BY a;",
             "order-by", "limit"),
        case("offset", TABLES, "INSERT INTO t SELECT a,b FROM s ORDER BY a LIMIT 1 OFFSET 1; SELECT a,b FROM t;",
             "order-by", "limit", "offset"),
        case("aggregate", TABLES, "INSERT INTO t SELECT count(*),group_concat(b) FROM s; SELECT a,b FROM t;", "aggregate"),
        case("group-by", TABLES, "INSERT INTO t SELECT a%2,count(*) FROM s GROUP BY a%2; SELECT a,b FROM t ORDER BY a;",
             "aggregate", "group-by"),
        case("distinct", TABLES, "INSERT INTO t SELECT DISTINCT a%2,'d' FROM s; SELECT a,b FROM t ORDER BY a;", "distinct"),
        case("compound", TABLES,
             "INSERT INTO t SELECT a,b FROM s WHERE a=1 UNION ALL SELECT a,b FROM s WHERE a=3; SELECT a,b FROM t ORDER BY a;",
             "compound"),
        case("parameter-free-subquery", TABLES,
             "INSERT INTO t SELECT a,(SELECT max(a) FROM s) FROM s; SELECT a,b FROM t ORDER BY a;", "subquery"),
        case("self", TABLES, "INSERT INTO s SELECT a+10,b FROM s; SELECT count(*),changes() FROM s;", "self"),
        case("self-twice", TABLES,
             "INSERT INTO s SELECT a,b FROM s; INSERT INTO s SELECT a,b FROM s; SELECT count(*) FROM s;", "self"),
        case("destination-in-subquery", TABLES,
             "INSERT INTO t SELECT a,b FROM s WHERE a IN (SELECT a FROM t); SELECT count(*) FROM t;", "self", "subquery"),
        case("counters", TABLES,
             "INSERT INTO k(v) SELECT b FROM s WHERE b<>'y'; SELECT changes(),total_changes(),last_insert_rowid();",
             "counters"),
        case("or-ignore", TABLES, "INSERT OR IGNORE INTO k(v) SELECT b FROM s; SELECT id,v FROM k ORDER BY id;",
             "algorithm", "ignore"),
        case("or-replace", TABLES, "INSERT OR REPLACE INTO k(v) SELECT b FROM s; SELECT id,v FROM k ORDER BY id;",
             "algorithm", "replace"),
        case("replace-into", TABLES, "REPLACE INTO k(v) SELECT b FROM s; SELECT id,v FROM k ORDER BY id;",
             "algorithm", "replace"),
        case("or-fail-keeps-earlier-rows", TABLES, "INSERT OR FAIL INTO k(v) SELECT b FROM s WHERE b<>'x' ORDER BY a DESC; "
             "SELECT id,v FROM k ORDER BY id;", "algorithm", "fail", "partial"),
        case("or-abort-conflict", TABLES, "INSERT INTO k(v) SELECT b FROM s; SELECT id,v FROM k ORDER BY id;",
             "algorithm", "abort", "error"),
        case("upsert-nothing", TABLES, "INSERT INTO k(v) SELECT b FROM s WHERE true ON CONFLICT(v) DO NOTHING; "
             "SELECT id,v FROM k ORDER BY id;", "upsert"),
        case("upsert-update", TABLES, "INSERT INTO k(v) SELECT b FROM s WHERE true ON CONFLICT(v) DO UPDATE SET id=id+100; "
             "SELECT id,v FROM k ORDER BY id;", "upsert"),
        case("returning", TABLES, "INSERT INTO t SELECT a,b FROM s RETURNING a,b;", "returning"),
        case("returning-then-query", TABLES, "INSERT INTO k(v) SELECT b FROM s WHERE b<>'y' RETURNING id,v; "
             "SELECT last_insert_rowid();", "returning", "counters"),
        case("column-count-error", TABLES, "INSERT INTO t SELECT a FROM s;", "error", "prepare"),
        case("listed-count-error", TABLES, "INSERT INTO t(a) SELECT a,b FROM s;", "error", "prepare"),
        case("missing-table", TABLES, "INSERT INTO t SELECT a,b FROM missing;", "error", "prepare"),
        case("missing-column", TABLES, "INSERT INTO t SELECT a,nope FROM s;", "error", "prepare"),
        case("defaults-and-generated", SHAPES, "INSERT INTO g(a) SELECT a FROM s; SELECT a,b,c,d FROM g ORDER BY a;",
             "default", "generated"),
        case("generated-in-list", SHAPES, "INSERT INTO g(a,c) SELECT a,a FROM s;", "generated", "error", "prepare"),
        case("without-rowid", SHAPES, "INSERT INTO w SELECT a,b FROM s; SELECT a,b FROM w ORDER BY a;", "without-rowid"),
        case("without-rowid-conflict", SHAPES, "INSERT INTO w SELECT a%1,b FROM s; SELECT a,b FROM w;", "without-rowid", "error"),
        case("source-error-keeps-no-row", OVERFLOW,
             "INSERT INTO t SELECT abs(x) FROM s; SELECT count(*) FROM t; SELECT last_insert_rowid();",
             "source-failure", "streaming", "partial"),
        case("source-error-collected", OVERFLOW,
             "INSERT INTO s SELECT abs(x) FROM s; SELECT count(*) FROM s; SELECT last_insert_rowid();",
             "source-failure", "collected", "partial"),
        case("conflict-before-source-error", OVERFLOW,
             "INSERT INTO u SELECT abs(x) FROM s; SELECT count(*) FROM u;", "source-failure", "conflict", "precedence"),
        case("unused-destination-cte-streams", OVERFLOW,
             "WITH c AS (SELECT id FROM t) INSERT INTO t SELECT abs(x) FROM s; SELECT count(*) FROM t; "
             "SELECT last_insert_rowid();", "source-failure", "cte"),
        case("fail-streams-without-trigger", PRECEDENCE,
             "INSERT OR FAIL INTO dest SELECT abs(x) FROM src; SELECT x FROM dest ORDER BY x;",
             "source-failure", "algorithm", "fail", "precedence"),
        case("fail-collects-with-trigger", PRECEDENCE + " CREATE TRIGGER r AFTER INSERT ON dest BEGIN SELECT 1; END;",
             "INSERT OR FAIL INTO dest SELECT abs(x) FROM src; SELECT x FROM dest ORDER BY x;",
             "source-failure", "algorithm", "fail", "trigger", "precedence"),
        case("fail-streams-with-update-trigger", PRECEDENCE + " CREATE TRIGGER r AFTER UPDATE ON dest BEGIN SELECT 1; END;",
             "INSERT OR FAIL INTO dest SELECT abs(x) FROM src; SELECT x FROM dest ORDER BY x;",
             "source-failure", "trigger", "precedence"),
        case("fail-collects-with-inactive-trigger",
             PRECEDENCE + " CREATE TRIGGER r AFTER INSERT ON dest WHEN 0 BEGIN SELECT 1; END;",
             "INSERT OR FAIL INTO dest SELECT abs(x) FROM src; SELECT x FROM dest ORDER BY x;",
             "source-failure", "trigger", "when", "precedence"),
        case("fail-collects-with-returning", PRECEDENCE,
             "INSERT OR FAIL INTO dest SELECT abs(x) FROM src RETURNING x; SELECT x FROM dest ORDER BY x;",
             "source-failure", "returning", "precedence"),
        case("sorted-without-index", SORTED,
             "INSERT OR FAIL INTO dest SELECT abs(x) FROM src ORDER BY k; SELECT x FROM dest ORDER BY x;",
             "source-failure", "order-by", "precedence"),
        case("sorted-with-index", SORTED + " CREATE INDEX srck ON src(k);",
             "INSERT OR FAIL INTO dest SELECT abs(x) FROM src ORDER BY k; SELECT x FROM dest ORDER BY x;",
             "source-failure", "order-by", "index", "precedence"),
        case("scan-order", INDEXED, "INSERT INTO t(name) SELECT x FROM s; SELECT id,name FROM t ORDER BY id;",
             "order", "scan"),
        case("index-order", INDEXED, "INSERT INTO t(name) SELECT x FROM s WHERE x>0; SELECT id,name FROM t ORDER BY id;",
             "order", "index"),
        case("no-index-order", INDEXED.replace(" CREATE INDEX sx ON s(x);", ""),
             "INSERT INTO t(name) SELECT x FROM s WHERE x>0; SELECT id,name FROM t ORDER BY id;", "order", "scan"),
        case("index-order-keeps-other-rows", INDEXED + " CREATE TABLE d(v INTEGER UNIQUE); INSERT INTO d VALUES(10);",
             "INSERT OR FAIL INTO d SELECT x FROM s WHERE x>0; SELECT v FROM d ORDER BY v;",
             "order", "index", "algorithm", "fail", "partial"),
        case("no-index-keeps-other-rows",
             INDEXED.replace(" CREATE INDEX sx ON s(x);", "") + " CREATE TABLE d(v INTEGER UNIQUE); INSERT INTO d VALUES(10);",
             "INSERT OR FAIL INTO d SELECT x FROM s WHERE x>0; SELECT v FROM d ORDER BY v;",
             "order", "scan", "algorithm", "fail", "partial"),
        case("trigger-two-orders", TWO_ORDERS,
             "INSERT INTO t SELECT x FROM s WHERE x>0; SELECT id,x FROM log ORDER BY id;", "trigger", "order", "index"),
        case("trigger-sees-rows", TRIGGERED + " CREATE TRIGGER r AFTER INSERT ON t BEGIN INSERT INTO log VALUES(new.a); END;",
             "INSERT INTO t SELECT a,b FROM s; SELECT x FROM log ORDER BY x; SELECT changes();", "trigger"),
        case("trigger-when-false", TRIGGERED + " CREATE TRIGGER r AFTER INSERT ON t WHEN 0 BEGIN INSERT INTO log VALUES(1); END;",
             "INSERT INTO t SELECT a,b FROM s; SELECT count(*) FROM log;", "trigger", "when"),
        case("trigger-before-conflict", TRIGGERED + " CREATE TRIGGER r BEFORE INSERT ON t BEGIN INSERT INTO log VALUES(new.a); END;",
             "INSERT INTO t VALUES(2,'q'); INSERT OR IGNORE INTO t SELECT a,b FROM s; SELECT x FROM log ORDER BY x;",
             "trigger", "algorithm", "ignore"),
        case("foreign-key-violation", KEYS, "INSERT INTO c SELECT a,a FROM s; SELECT count(*) FROM c;",
             "foreign-key", "error"),
        case("foreign-key-ok", KEYS, "INSERT INTO c SELECT a,a FROM s WHERE a<3; DELETE FROM p WHERE id=1; "
             "SELECT id,p FROM c ORDER BY id;", "foreign-key", "cascade"),
        case("transfer-with-rowid-gap", TRANSFER, "INSERT INTO t SELECT * FROM s; SELECT a FROM t ORDER BY a;",
             "transfer", "rowid"),
        case("transfer-column-list", TRANSFER, "INSERT INTO t(a) SELECT a FROM s; SELECT a FROM t ORDER BY a;",
             "transfer", "rowid"),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 7 record: the migration runs on after an error, which
    the executions of a statement need, and the record holds the counters of the writer. A case with
    the feature `foreign-key` runs under the measured profile with foreign keys on, any other case
    under SQLite's default measured profile."""
    selected = definitions() if cases is None else cases
    defaults, enforced = profile(()), foreign_key_profile()
    return [{**record_sql(case.setup, case.sql, name=case.name, requirements=list(case.requirements), outputs=True,
                          profile=enforced if "foreign-key" in case.features else defaults, run_on=True, counters=True),
             "part": "insert-queries", "features": list(case.features)}
            for case in selected]
