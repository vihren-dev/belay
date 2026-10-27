"""Native inputs for ALTER TABLE RENAME TO and RENAME COLUMN (ADR 0019, D4, part 2).

The cases cover what a rename keeps (rows, rowids, affinity, collation, indexes), what it rewrites (views,
triggers, constraints, generated columns, partial indexes, foreign keys on both sides), what it leaves (a
column of the same name in another table, a string that spells the name), the prepare errors, a rollback,
and the statements after the rename that read, write or fail under the new name. SQLite supplies every
outcome through the query recorder.
"""

from conformance.authored_foreign_keys import profile as foreign_key_profile
from conformance.authored_queries import QueryCase
from conformance.authored_resolution import profile
from conformance.case_format import Json
from conformance.native_record import record_sql
from conformance.rename_setups import CONSTRAINTS, DEPENDENTS, KEYS, ROWIDS, TABLES

RENAME_TO = "R-32485-24703"
"""SQLite: the RENAME TO syntax changes the name of table-name to new-table-name."""
ATTACHED = "R-18692-17694"
"""SQLite: triggers and indices remain attached to the table after it has been renamed."""
PARENT = "R-47080-02069"
"""SQLite: the foreign key definitions of a renamed parent table refer to it by its new name."""
COLUMN = "R-58318-35349"
"""SQLite: a statement of the ALTER TABLE family changes an existing table (the nearest sentence for RENAME COLUMN)."""


def definitions() -> list[QueryCase]:
    """The cases: each rename form, what it keeps and rewrites, its errors and its later statements."""
    def case(name: str, setup: str, sql: str, requirements: tuple[str, ...], *features: str) -> QueryCase:
        """Give a case its name prefix and features."""
        return QueryCase("rename-" + name, setup, sql, requirements, ("rename", *features))

    return [
        case("table-rows", TABLES, "ALTER TABLE t RENAME TO w; SELECT a,b,c FROM w ORDER BY a;", (RENAME_TO,), "table"),
        case("table-old-name", TABLES, "ALTER TABLE t RENAME TO w; SELECT a FROM t;", (RENAME_TO,), "table", "error"),
        case("table-rowids", ROWIDS, "ALTER TABLE r RENAME TO w; SELECT x,y FROM w ORDER BY y; INSERT INTO w VALUES('d',4); "
             "SELECT x,y FROM w ORDER BY y;", (RENAME_TO,), "table", "rowid"),
        case("table-affinity-collation", TABLES, "ALTER TABLE t RENAME TO w; INSERT INTO w VALUES('7','P','3'); "
             "SELECT typeof(a),typeof(c),b='p' FROM w WHERE a=7;", (RENAME_TO,), "table", "affinity", "collation"),
        case("table-index", TABLES, "ALTER TABLE t RENAME TO w; INSERT INTO w VALUES(9,'p',0); "
             "SELECT a FROM w WHERE b='P' ORDER BY a;", (ATTACHED,), "table", "index"),
        case("table-case-only", TABLES, "ALTER TABLE t RENAME TO T; SELECT a FROM t ORDER BY a;", (RENAME_TO,),
             "table", "case"),
        case("table-quoted-name", TABLES, 'ALTER TABLE t RENAME TO "w w"; SELECT a FROM "w w" ORDER BY a;', (RENAME_TO,),
             "table", "quoted"),
        case("table-view", DEPENDENTS, "ALTER TABLE t RENAME TO w; SELECT a,label,text FROM v ORDER BY a;", (RENAME_TO,),
             "table", "view"),
        case("table-trigger", DEPENDENTS, "ALTER TABLE t RENAME TO w; INSERT INTO w VALUES(3,'r'); SELECT m FROM log;",
             (ATTACHED,), "table", "trigger"),
        case("table-parent", KEYS, "ALTER TABLE p RENAME TO q; DELETE FROM q WHERE id=1; SELECT id FROM c;", (PARENT,),
             "table", "foreign-key"),
        case("table-parent-violation", KEYS, "ALTER TABLE p RENAME TO q; INSERT INTO c VALUES(12,7,'x'); "
             "SELECT count(*) FROM c;", (PARENT,), "table", "foreign-key", "error"),
        case("table-parent-enforcement-off", KEYS, "ALTER TABLE p RENAME TO q; "
             "SELECT id,\"table\",\"from\",\"to\" FROM pragma_foreign_key_list('c') ORDER BY id;", (PARENT,), "table", "foreign-key-off"),
        case("table-main-schema", TABLES, "ALTER TABLE main.t RENAME TO w; SELECT a FROM w ORDER BY a;", (RENAME_TO,),
             "table", "schema"),
        case("table-rollback", TABLES, "BEGIN; ALTER TABLE t RENAME TO w; ROLLBACK; SELECT a FROM t ORDER BY a;",
             (RENAME_TO,), "table", "transaction"),
        case("table-commit-twice", TABLES, "BEGIN; ALTER TABLE t RENAME TO w; ALTER TABLE w RENAME TO z; COMMIT; "
             "SELECT a FROM z ORDER BY a;", (RENAME_TO,), "table", "transaction"),
        case("table-no-such", TABLES, "ALTER TABLE nope RENAME TO w;", (RENAME_TO,), "table", "prepare-error"),
        case("table-taken", TABLES, "ALTER TABLE t RENAME TO U;", (RENAME_TO,), "table", "prepare-error"),
        case("table-index-name-taken", TABLES, "ALTER TABLE t RENAME TO ti;", (RENAME_TO,), "table", "prepare-error"),
        case("table-of-view", DEPENDENTS, "ALTER TABLE v RENAME TO w;", (RENAME_TO,), "table", "prepare-error"),
        case("table-reserved", TABLES, "ALTER TABLE t RENAME TO sqlite_x;", (RENAME_TO,), "table", "prepare-error"),
        case("column-rows", TABLES, "ALTER TABLE t RENAME COLUMN b TO d; SELECT a,d,c FROM t ORDER BY a;", (COLUMN,),
             "column"),
        case("column-old-name", TABLES, "ALTER TABLE t RENAME COLUMN b TO d; SELECT b FROM t;", (COLUMN,), "column", "error"),
        case("column-other-table", TABLES, "ALTER TABLE t RENAME COLUMN b TO d; SELECT x,b FROM u ORDER BY x;", (COLUMN,),
             "column", "scope"),
        case("column-index", TABLES, "ALTER TABLE t RENAME COLUMN b TO d; INSERT INTO t VALUES(9,'p',0); "
             "SELECT a FROM t WHERE d='P' ORDER BY a;", (COLUMN,), "column", "index"),
        case("column-quoted-new-name", TABLES, 'ALTER TABLE t RENAME COLUMN b TO "Z z"; SELECT a,"Z z" FROM t ORDER BY a;',
             (COLUMN,), "column", "quoted"),
        case("column-affinity-collation", TABLES, "ALTER TABLE t RENAME COLUMN b TO d; INSERT INTO t VALUES(7,'P',1); "
             "SELECT typeof(c),d='p' FROM t WHERE a=7;", (COLUMN,), "column", "affinity", "collation"),
        case("column-rowid-alias", TABLES, "ALTER TABLE t RENAME COLUMN a TO id; SELECT id FROM t WHERE id=5 ORDER BY id;",
             (COLUMN,), "column", "rowid"),
        case("column-without-keyword", TABLES, "ALTER TABLE t RENAME b TO d; SELECT a,d FROM t ORDER BY a;", (COLUMN,),
             "column", "syntax"),
        case("column-expression-index", TABLES + " CREATE INDEX te ON t(b || 'x', c * 2);",
             "ALTER TABLE t RENAME COLUMN b TO d; INSERT INTO t VALUES(8,'z',0); SELECT a,d FROM t WHERE d || 'x' = 'zx' "
             "ORDER BY a;", (COLUMN,), "column", "index", "expression"),
        case("column-view", DEPENDENTS, "ALTER TABLE t RENAME COLUMN b TO d; SELECT a,label,text FROM v ORDER BY a;",
             (COLUMN,), "column", "view"),
        case("column-trigger", DEPENDENTS, "ALTER TABLE t RENAME COLUMN b TO d; INSERT INTO t VALUES(3,'r'); "
             "SELECT m FROM log;", (COLUMN,), "column", "trigger"),
        case("column-constraints", CONSTRAINTS, "ALTER TABLE t RENAME COLUMN b TO d; INSERT INTO t(a,d) VALUES(5,0);",
             (COLUMN,), "column", "check", "error"),
        case("column-generated", CONSTRAINTS, "ALTER TABLE t RENAME COLUMN b TO d; SELECT a,d,c FROM t ORDER BY a;",
             (COLUMN,), "column", "generated"),
        case("column-key", CONSTRAINTS, "ALTER TABLE t RENAME COLUMN a TO k; INSERT INTO t(k,b) VALUES(1,9);",
             (COLUMN,), "column", "key", "error"),
        case("column-parent", KEYS, "ALTER TABLE p RENAME COLUMN id TO pk; DELETE FROM p WHERE pk=1; SELECT id FROM c;",
             (COLUMN,), "column", "foreign-key"),
        case("column-child", KEYS, "ALTER TABLE c RENAME COLUMN pid TO owner; INSERT INTO c VALUES(12,7,'x'); "
             "SELECT count(*) FROM c;", (COLUMN,), "column", "foreign-key", "error"),
        case("column-parent-unique", KEYS, "ALTER TABLE p RENAME COLUMN name TO label; INSERT INTO c VALUES(12,1,'z'); "
             "SELECT count(*) FROM c;", (COLUMN,), "column", "foreign-key", "error"),
        case("column-rollback", TABLES, "BEGIN; ALTER TABLE t RENAME COLUMN b TO d; ROLLBACK; SELECT a,b FROM t ORDER BY a;",
             (COLUMN,), "column", "transaction"),
        case("column-writes", TABLES, "ALTER TABLE t RENAME COLUMN b TO d; UPDATE t SET d = 'z' WHERE a=1; "
             "DELETE FROM t WHERE d='Q'; SELECT a,d FROM t;", (COLUMN,), "column", "write"),
        case("column-no-such", TABLES, "ALTER TABLE t RENAME COLUMN nope TO d;", (COLUMN,), "column", "prepare-error"),
        case("column-duplicate", TABLES, "ALTER TABLE t RENAME COLUMN b TO c;", (COLUMN,), "column", "prepare-error"),
        case("column-no-such-table", TABLES, "ALTER TABLE nope RENAME COLUMN b TO d;", (COLUMN,), "column", "prepare-error"),
        case("column-same-name", TABLES, "ALTER TABLE t RENAME COLUMN b TO B; SELECT a,B FROM t ORDER BY a;", (COLUMN,),
             "column", "case"),
        case("column-view-ambiguous", "CREATE TABLE t(a INTEGER, c INTEGER); CREATE TABLE u(x INTEGER); "
             "CREATE VIEW v AS SELECT c FROM t, u;", "ALTER TABLE t RENAME COLUMN c TO x; SELECT * FROM v;", (COLUMN,),
             "column", "view", "prepare-error"),
        case("column-trigger-ambiguous", "CREATE TABLE t(a INTEGER, c INTEGER); CREATE TABLE u(x INTEGER); "
             "CREATE TRIGGER g AFTER INSERT ON u BEGIN SELECT c FROM t, u; END;",
             "ALTER TABLE t RENAME COLUMN c TO x; INSERT INTO u VALUES(1);", (COLUMN,), "column", "trigger",
             "prepare-error"),
        case("column-view-text-name", TABLES + ' CREATE VIEW q AS SELECT "x" || b FROM t;',
             "ALTER TABLE t RENAME COLUMN a TO x; SELECT * FROM q;", (COLUMN,), "column", "view", "quotefix"),
        case("table-view-text-name", TABLES + ' CREATE VIEW q AS SELECT "x" || b FROM t;',
             "ALTER TABLE t RENAME TO w; SELECT * FROM q;", (RENAME_TO,), "table", "view", "quotefix"),
        case("column-view-recursive-aggregate", TABLES + " CREATE VIEW q AS WITH r(n) AS (SELECT 1 UNION ALL "
             "SELECT sum(n) FROM r) SELECT n FROM r;", "ALTER TABLE t RENAME COLUMN b TO d; SELECT a,d FROM t ORDER BY a;",
             (COLUMN,), "column", "view", "common-table"),
        case("column-check-loose-quote", "CREATE TABLE t(a INTEGER, b TEXT CHECK (b <> \"zz\")); INSERT INTO t VALUES(1,'p');",
             "ALTER TABLE t RENAME COLUMN a TO z; INSERT INTO t VALUES(2,'zz'); SELECT z,b FROM t ORDER BY z;", (COLUMN,),
             "column", "check", "quotefix"),
        case("table-check-loose-quote", "CREATE TABLE t(a INTEGER, b TEXT CHECK (b <> \"zz\")); INSERT INTO t VALUES(1,'p');",
             "ALTER TABLE t RENAME TO w; INSERT INTO w VALUES(2,'zz'); SELECT a,b FROM w ORDER BY a;", (RENAME_TO,),
             "table", "check", "quotefix"),
        case("column-view-error", "CREATE TABLE t(a INTEGER, b INTEGER); CREATE VIEW v AS SELECT a FROM t JOIN t AS s USING (a);",
             "ALTER TABLE t RENAME COLUMN a TO c;", (COLUMN,), "column", "view", "prepare-error"),
    ]


def records(cases: list[QueryCase] | None = None) -> list[dict[str, Json]]:
    """Record each case natively as a version 7 record: the migration runs on after an error, as the
    statements after a failed rename need. A case with the feature `foreign-key` runs under the measured
    profile with foreign keys on, any other case under SQLite's default measured profile."""
    selected = definitions() if cases is None else cases
    defaults, enforced = profile(()), foreign_key_profile()
    return [{**record_sql(case.setup, case.sql, name=case.name, requirements=list(case.requirements), outputs=True,
                          profile=enforced if "foreign-key" in case.features else defaults, run_on=True, counters=True),
             "part": "renames", "features": list(case.features)}
            for case in selected]
