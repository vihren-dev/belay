"""Native inputs for views as stored queries (ADR 0019, D5, view part).

A view keeps its query text and resolves it at each use. The cases cover CREATE and
DROP VIEW, reads of nested views and views with column lists, `table_info` of views,
writes to views, late binding and the errors of broken views. SQLite supplies every
outcome through the existing query recorder. Cases that the model deliberately leaves
out carry the feature `unmodeled`.
"""

from conformance.authored_queries import QueryCase, records as query_records
from conformance.authored_query_sources import TABLES
from conformance.authored_subqueries import COLUMN_TYPE, SUBQUERY
from conformance.case_format import Json

CREATE_VIEW = "R-13439-14752-32196-09382-64767-42844-00603-31803"
"""CREATE VIEW names a pre-packaged SELECT."""
USE_VIEW = "R-63075-15970-39501-22460-58793-43455-08281-02350"
"""A view can replace a table name in the FROM clause."""
VIEW_COLUMNS = "R-49858-53293-55345-56898-28930-13121-51128-08876"
"""A column-name list determines the names of the view columns."""
DERIVED_COLUMNS = "R-36185-29671-26091-33323-34163-48928-21638-35689"
"""Without a list, the names derive from the result columns."""
DROP_VIEW = "R-27002-52307-56024-23951-62365-30891-30149-50327"
"""DROP VIEW removes a view."""
DROP_MISSING = "R-25558-37487-19096-36063-17437-04044-36041-27526"
"""DROP VIEW of a missing view is an error."""
DROP_IF_EXISTS = "R-07490-32536-65444-08514-64358-21801-57919-13418"
"""DROP VIEW IF EXISTS of a missing view does nothing."""
READ_ONLY = "R-16775-34716-48016-59856-43563-01952-64923-08515"
"""A view cannot be the target of DELETE, INSERT or UPDATE."""
NAME_COLLISION = "R-01232-54838-06099-51737-48729-53565-23196-29255"
"""A new table cannot share a name with a table, index or view."""
TABLE_INFO = "R-35224-32827-55933-44478-17553-06933-55583-57822"
"""The table named in table_info can be a view."""


def definitions() -> list[QueryCase]:
    """Creation, use, listing, drop, write and late-binding cases of stored views."""
    def case(name: str, sql: str, requirements: tuple[str, ...], *features: str) -> QueryCase:
        """Give a view case the common tables and the requirements that it covers."""
        return QueryCase("view-" + name, TABLES, sql, (CREATE_VIEW, *requirements), ("view", *features))

    return [
        case("read", "CREATE VIEW v AS SELECT a,b FROM t; SELECT * FROM v ORDER BY b;", (USE_VIEW, DERIVED_COLUMNS), "read"),
        case("column-list", "CREATE VIEW v(x,y) AS SELECT a,b FROM t; SELECT x,y FROM v ORDER BY y;", (VIEW_COLUMNS,), "columns"),
        case("column-list-overrides-names", "CREATE VIEW v(x) AS SELECT b AS y FROM t; SELECT * FROM v ORDER BY x; SELECT y FROM v;", (VIEW_COLUMNS,), "columns", "error"),
        case("column-list-too-short", "CREATE VIEW v(x) AS SELECT a,b FROM t; SELECT * FROM v;", (VIEW_COLUMNS,), "columns", "error"),
        case("column-list-too-long", "CREATE VIEW v(x,y,z) AS SELECT a,b FROM t; SELECT * FROM v;", (VIEW_COLUMNS,), "columns", "error"),
        case("unused-bad-column-list", "CREATE VIEW v(x,y,z) AS SELECT a,b FROM t; SELECT 1;", (VIEW_COLUMNS,), "columns", "unused"),
        case("duplicate-result-names", "CREATE VIEW v AS SELECT b,b,b+1 FROM t; SELECT * FROM v ORDER BY 1;", (DERIVED_COLUMNS,), "columns", "names"),
        case("derived-names", "CREATE VIEW v AS SELECT a, b+1, t.b, 7 AS seven FROM t; PRAGMA table_info(v);", (DERIVED_COLUMNS, TABLE_INFO), "columns", "table-info"),
        case("nested", "CREATE VIEW v1 AS SELECT b FROM t; CREATE VIEW v2(d) AS SELECT b*2 FROM v1; SELECT d FROM v2 ORDER BY d;", (USE_VIEW,), "nested"),
        case("nested-three", "CREATE VIEW v1 AS SELECT a,b FROM t; CREATE VIEW v2 AS SELECT * FROM v1 WHERE b>1; CREATE VIEW v3 AS SELECT a FROM v2; SELECT * FROM v3 ORDER BY a;", (USE_VIEW,), "nested"),
        case("metadata", "CREATE VIEW v AS SELECT a,b,c FROM t; SELECT a='A', b='1', c=1 FROM v WHERE b=1;", (USE_VIEW, COLUMN_TYPE), "affinity", "collation"),
        case("nested-metadata", "CREATE VIEW v1 AS SELECT a,b FROM t; CREATE VIEW v2 AS SELECT * FROM v1; SELECT a='A', b='1' FROM v2 WHERE b=1;", (USE_VIEW, COLUMN_TYPE), "affinity", "collation", "nested"),
        case("join", "CREATE VIEW v AS SELECT a,b FROM t; SELECT v.a,v.b,u.a,u.b FROM v JOIN u ON v.b=u.b;", (USE_VIEW,), "join"),
        case("left-join", "CREATE VIEW v AS SELECT a,b FROM u; SELECT t.b,v.a FROM t LEFT JOIN v ON t.b=v.b ORDER BY t.b;", (USE_VIEW,), "join"),
        case("self-join", "CREATE VIEW v AS SELECT b FROM u; SELECT l.b,r.b FROM v l JOIN v r ON l.b<r.b;", (USE_VIEW,), "join"),
        case("aggregate", "CREATE VIEW v AS SELECT a,count(*) AS n,sum(b) AS s FROM t GROUP BY a; SELECT a,n,s FROM v ORDER BY a;", (USE_VIEW,), "aggregate"),
        case("compound", "CREATE VIEW v AS SELECT b FROM t UNION ALL SELECT b FROM u; SELECT b FROM v ORDER BY b;", (USE_VIEW,), "compound"),
        case("subquery", "CREATE VIEW v AS SELECT b FROM u; SELECT b,b IN (SELECT b FROM v),(SELECT max(b) FROM v) FROM t ORDER BY b;", (USE_VIEW, SUBQUERY), "subquery"),
        case("derived-source", "CREATE VIEW v AS SELECT a,b FROM t; SELECT d.b FROM (SELECT b FROM v WHERE b>1) d ORDER BY d.b;", (USE_VIEW,), "derived-source"),
        case("view-in-body-cte", "CREATE VIEW v AS WITH c(x) AS (SELECT b FROM t) SELECT x FROM c; SELECT x FROM v ORDER BY x;", (USE_VIEW,), "common-table"),
        case("view-under-cte", "CREATE VIEW v AS SELECT b FROM t; WITH c(x) AS (SELECT b FROM v) SELECT x FROM c ORDER BY x;", (USE_VIEW,), "common-table"),
        case("cte-shadows-view", "CREATE VIEW v AS SELECT 1 AS x; WITH v(x) AS (SELECT 2) SELECT x FROM v;", (USE_VIEW,), "common-table", "shadowing"),
        case("body-does-not-see-cte", "CREATE VIEW v AS SELECT * FROM c; WITH c(x) AS (SELECT 2) SELECT * FROM v;", (USE_VIEW,), "common-table", "scope", "error"),
        case("body-does-not-see-outer-row", "CREATE VIEW v AS SELECT b AS x FROM u; SELECT b,(SELECT x FROM v WHERE x=t.b) FROM t ORDER BY b;", (USE_VIEW,), "scope", "correlated"),
        case("name-case", "CREATE VIEW MixedCase AS SELECT 1 AS x; SELECT x FROM mixedcase;", (USE_VIEW,), "names"),
        case("function-call-source", "CREATE VIEW v AS SELECT 1 AS x; SELECT * FROM v(1);", (USE_VIEW,), "error"),
        case("star-follows-table", "CREATE VIEW v AS SELECT * FROM e; DROP TABLE e; CREATE TABLE e(z,a,b); INSERT INTO e VALUES(1,'p',2); SELECT * FROM v;", (USE_VIEW,), "late-binding", "star"),
        case("star-with-added-column", "CREATE VIEW v AS SELECT * FROM e; ALTER TABLE e ADD COLUMN k; INSERT INTO e VALUES('p',2,3); SELECT * FROM v;", (USE_VIEW,), "late-binding", "star", "alter"),
        case("insert-reads-view", "CREATE VIEW v AS SELECT a,b FROM t WHERE b>1; INSERT INTO e VALUES('x',(SELECT max(b) FROM v)); SELECT a,b FROM e;", (USE_VIEW,), "write", "read"),
        case("trigger-reads-view", "CREATE VIEW v AS SELECT b FROM u; CREATE TRIGGER r AFTER INSERT ON e BEGIN SELECT (SELECT max(b) FROM v); END; INSERT INTO e VALUES('a',1); SELECT a,b FROM e;", (USE_VIEW,), "trigger"),
        case("created-before-table", "CREATE VIEW v AS SELECT * FROM later; CREATE TABLE later(x); INSERT INTO later VALUES(5); SELECT * FROM v;", (CREATE_VIEW,), "late-binding"),
        case("read-before-table", "CREATE VIEW v AS SELECT * FROM later; SELECT * FROM v; CREATE TABLE later(x); SELECT * FROM v;", (CREATE_VIEW,), "late-binding", "error"),
        case("unused-missing-table", "CREATE VIEW v AS SELECT * FROM missing; SELECT count(*) FROM t;", (CREATE_VIEW,), "late-binding", "unused"),
        case("missing-after-drop", "CREATE VIEW v AS SELECT b FROM t; DROP TABLE t; SELECT * FROM v;", (CREATE_VIEW,), "late-binding", "error"),
        case("recreated-table", "CREATE VIEW v AS SELECT b FROM t; DROP TABLE t; CREATE TABLE t(b); INSERT INTO t VALUES(8); SELECT * FROM v;", (CREATE_VIEW,), "late-binding"),
        case("missing-column", "CREATE VIEW v AS SELECT zz FROM t; SELECT * FROM v;", (CREATE_VIEW,), "late-binding", "error"),
        case("dropped-column-target", "CREATE VIEW v AS SELECT b FROM t; DROP TABLE t; CREATE TABLE t(a); SELECT * FROM v;", (CREATE_VIEW,), "late-binding", "error"),
        case("view-of-dropped-view", "CREATE VIEW v1 AS SELECT b FROM t; CREATE VIEW v2 AS SELECT b FROM v1; DROP VIEW v1; SELECT * FROM v2;", (CREATE_VIEW, DROP_VIEW), "late-binding", "nested", "error"),
        case("self-cycle", "CREATE VIEW v AS SELECT * FROM v; SELECT * FROM v;", (CREATE_VIEW,), "cycle", "error"),
        case("indirect-cycle", "CREATE VIEW a AS SELECT * FROM b; CREATE VIEW b AS SELECT * FROM a; SELECT * FROM a;", (CREATE_VIEW,), "cycle", "error"),
        case("cycle-closed-late", "CREATE VIEW a AS SELECT * FROM b; CREATE VIEW b AS SELECT 1 AS x; DROP VIEW b; CREATE VIEW b AS SELECT * FROM a; SELECT * FROM b;", (CREATE_VIEW,), "cycle", "error"),
        case("unused-cycle", "CREATE VIEW v AS SELECT * FROM v; SELECT 1;", (CREATE_VIEW,), "cycle", "unused"),
        case("body-uses-new", "CREATE VIEW v AS SELECT new.a FROM t; SELECT * FROM v;", (CREATE_VIEW,), "error", "scope"),
        case("body-uses-missing-in-where", "CREATE VIEW v AS SELECT a FROM t WHERE zz; SELECT * FROM v;", (CREATE_VIEW,), "late-binding", "error"),
        case("body-missing-in-join", "CREATE VIEW v AS SELECT * FROM t JOIN missing; SELECT * FROM v;", (CREATE_VIEW,), "late-binding", "error"),
        case("body-missing-in-compound", "CREATE VIEW v AS SELECT a FROM t UNION SELECT * FROM missing; SELECT * FROM v;", (CREATE_VIEW,), "late-binding", "error"),
        case("body-missing-in-source", "CREATE VIEW v AS SELECT * FROM (SELECT * FROM missing); SELECT * FROM v;", (CREATE_VIEW,), "late-binding", "error"),
        case("fallible-body", "CREATE VIEW v AS SELECT abs(-9223372036854775808); SELECT 1;", (CREATE_VIEW,), "failure", "unmodeled"),
        case("create-existing", "CREATE VIEW v AS SELECT 1; CREATE VIEW v AS SELECT 2;", (CREATE_VIEW,), "names", "error"),
        case("create-if-not-exists", "CREATE VIEW v AS SELECT 1 AS x; CREATE VIEW IF NOT EXISTS v AS SELECT 2 AS x; SELECT x FROM v;", (CREATE_VIEW,), "names"),
        case("create-over-table", "CREATE VIEW t AS SELECT 1;", (CREATE_VIEW, NAME_COLLISION), "names", "error"),
        case("create-if-not-exists-over-table", "CREATE VIEW IF NOT EXISTS t AS SELECT 1; SELECT count(*) FROM t;", (CREATE_VIEW, NAME_COLLISION), "names"),
        case("table-over-view", "CREATE VIEW v AS SELECT 1; CREATE TABLE v(x);", (CREATE_VIEW, NAME_COLLISION), "names", "error"),
        case("index-over-view-name", "CREATE VIEW v AS SELECT 1; CREATE INDEX v ON t(b);", (CREATE_VIEW, NAME_COLLISION), "names", "error"),
        case("index-on-view", "CREATE VIEW v AS SELECT b FROM t; CREATE INDEX i ON v(b);", (CREATE_VIEW,), "index", "error"),
        case("drop", "CREATE VIEW v AS SELECT 1; DROP VIEW v; SELECT * FROM v;", (DROP_VIEW,), "drop", "error"),
        case("drop-keeps-tables", "CREATE VIEW v AS SELECT b FROM t; DROP VIEW v; SELECT count(*) FROM t;", (DROP_VIEW,), "drop"),
        case("drop-missing", "DROP VIEW v;", (DROP_MISSING,), "drop", "error"),
        case("drop-if-exists-missing", "DROP VIEW IF EXISTS v; SELECT 1;", (DROP_IF_EXISTS,), "drop"),
        case("drop-if-exists-present", "CREATE VIEW v AS SELECT 1; DROP VIEW IF EXISTS v; SELECT * FROM v;", (DROP_VIEW, DROP_IF_EXISTS), "drop", "error"),
        case("drop-view-on-table", "DROP VIEW t;", (DROP_VIEW,), "drop", "error"),
        case("drop-table-on-view", "CREATE VIEW v AS SELECT 1; DROP TABLE v;", (DROP_VIEW,), "drop", "error"),
        case("drop-view-if-exists-on-table", "DROP VIEW IF EXISTS t;", (DROP_VIEW, DROP_IF_EXISTS), "drop", "error"),
        case("drop-nested-keeps-outer", "CREATE VIEW v1 AS SELECT b FROM t; CREATE VIEW v2 AS SELECT b FROM v1; DROP VIEW v2; SELECT count(*) FROM v1;", (DROP_VIEW,), "drop", "nested"),
        case("drop-and-recreate", "CREATE VIEW v AS SELECT 1 AS x; DROP VIEW v; CREATE VIEW v AS SELECT 2 AS y; SELECT y FROM v;", (DROP_VIEW,), "drop"),
        case("rollback-create", "BEGIN; CREATE VIEW v AS SELECT 1; ROLLBACK; SELECT * FROM v;", (CREATE_VIEW,), "transaction", "error"),
        case("rollback-drop", "CREATE VIEW v AS SELECT 1 AS x; BEGIN; DROP VIEW v; ROLLBACK; SELECT x FROM v;", (DROP_VIEW,), "transaction"),
        case("commit-create", "BEGIN; CREATE VIEW v AS SELECT b FROM t; COMMIT; SELECT count(*) FROM v;", (CREATE_VIEW,), "transaction"),
        case("table-info", "CREATE VIEW v AS SELECT a,b,c FROM t; PRAGMA table_info(v);", (TABLE_INFO,), "table-info"),
        case("table-info-column-list", "CREATE VIEW v(x,y) AS SELECT a,b+1 FROM t; PRAGMA table_info(v);", (TABLE_INFO, VIEW_COLUMNS), "table-info", "columns"),
        case("table-info-nested", "CREATE VIEW v1 AS SELECT a,b FROM t; CREATE VIEW v2 AS SELECT b,a FROM v1; PRAGMA table_info(v2);", (TABLE_INFO,), "table-info", "nested"),
        case("table-xinfo", "CREATE VIEW v AS SELECT a,b FROM t; PRAGMA table_xinfo(v);", (TABLE_INFO,), "table-info"),
        case("table-info-broken", "CREATE VIEW v AS SELECT * FROM missing; PRAGMA table_info(v);", (TABLE_INFO,), "table-info", "late-binding", "error"),
        case("table-info-cycle", "CREATE VIEW v AS SELECT * FROM v; PRAGMA table_info(v);", (TABLE_INFO,), "table-info", "cycle", "error"),
        case("table-info-missing", "PRAGMA table_info(v);", (TABLE_INFO,), "table-info"),
        case("table-list", "CREATE VIEW v AS SELECT a,b FROM t; PRAGMA table_list;", (CREATE_VIEW,), "table-info", "unmodeled"),
        case("insert-into-view", "CREATE VIEW v AS SELECT a,b FROM t; INSERT INTO v VALUES('x',1);", (READ_ONLY,), "write", "error"),
        case("update-view", "CREATE VIEW v AS SELECT a,b FROM t; UPDATE v SET b=0;", (READ_ONLY,), "write", "error"),
        case("delete-from-view", "CREATE VIEW v AS SELECT a,b FROM t; DELETE FROM v;", (READ_ONLY,), "write", "error"),
        case("write-broken-view", "CREATE VIEW v AS SELECT * FROM missing; INSERT INTO v VALUES(1);", (READ_ONLY,), "write", "late-binding", "error"),
        case("write-cyclic-view", "CREATE VIEW v AS SELECT * FROM v; DELETE FROM v;", (READ_ONLY,), "write", "cycle", "error"),
        case("write-with-subquery-view", "CREATE VIEW v AS SELECT b FROM u; UPDATE t SET b=(SELECT max(b) FROM v); SELECT b FROM t ORDER BY b;", (USE_VIEW,), "write", "read"),
        case("instead-of-insert", "CREATE VIEW v AS SELECT a,b FROM t; CREATE TRIGGER r INSTEAD OF INSERT ON v BEGIN INSERT INTO e VALUES(new.a,new.b); END; INSERT INTO v VALUES('x',9); SELECT a,b FROM e;", (READ_ONLY,), "write", "instead-of", "unmodeled"),
        case("returning-view", "CREATE VIEW v AS SELECT a,b FROM t; INSERT INTO v VALUES('x',1) RETURNING *;", (READ_ONLY,), "write", "error"),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record the chosen view inputs with the existing native output recorder."""
    return query_records(definitions() if cases is None else cases, part="query-sources")

