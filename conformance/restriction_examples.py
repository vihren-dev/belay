"""One example script for each model restriction of the registry.

Every restriction id of `RestrictionKind.id` (`Resolution/RestrictionText.lean`) has
an example here: a schema and a migration that the resolver refuses with that id.
The examples show that each restriction can be reached from SQL, and they show users
what each restriction refuses. `resolve_example` runs one example through the frontend and the resolver, as
`migration_check.inputs` does for `verify`.
"""

import json
from pathlib import Path
import subprocess
from tempfile import TemporaryDirectory

from belay.sqlite.dialects import ProfileIdentity
from belay.sqlite.located import Json
from belay.sqlite.profiles import profile
from belay.sqlite.sql_tree import SqlError, SqlParser, parse
from belay.sqlite.syntax import script_record, statements
from conformance.record_parser import runtime_library

EXAMPLES: dict[str, tuple[str, str]] = {
    "schema-statement": ("CREATE TABLE t(a INTEGER); INSERT INTO t VALUES (1);", "SELECT a FROM t;"),
    "engine-table": ("CREATE TABLE t(a INTEGER); CREATE TABLE sqlite_sequence(name, seq);", "SELECT a FROM t;"),
    "rowid-column-name": ("CREATE TABLE t(a INTEGER);", "CREATE TABLE u(rowid TEXT);"),
    "check-function": ("CREATE TABLE t(a TEXT);", "CREATE TABLE u(a TEXT CHECK (date(a) IS NOT NULL));"),
    "add-column-check-error": ("CREATE TABLE t(a TEXT);", "ALTER TABLE t ADD COLUMN b CHECK (zz > 0);"),
    "generated-function": ("CREATE TABLE t(a TEXT);", "CREATE TABLE u(a TEXT, b AS (date(a)));"),
    "generated-loop": ("CREATE TABLE t(a TEXT);", "CREATE TABLE u(a, b AS (c), c AS (b));"),
    "upsert-generated": ("CREATE TABLE t(a INTEGER UNIQUE, b AS (a + 1));",
                         "INSERT INTO t(a) VALUES(1) ON CONFLICT(a) DO UPDATE SET b = 2;"),
    "add-column-generated": ("CREATE TABLE t(a INTEGER);", "ALTER TABLE t ADD COLUMN b AS (a + 1);"),
    "add-column-strict-type": ("CREATE TABLE t(a INTEGER) STRICT;", "ALTER TABLE t ADD COLUMN b VARCHAR(5);"),
    "drop-constraint-index": ("CREATE TABLE t(a INTEGER UNIQUE);", "DROP INDEX sqlite_autoindex_t_1;"),
    "unmodeled-default": ("CREATE TABLE t(a INTEGER DEFAULT -'a');", "SELECT a FROM t;"),
    "index-string-term": ("CREATE TABLE t(a INTEGER);", "CREATE INDEX i ON t('a');"),
    "index-date-function": ("CREATE TABLE t(a TEXT);", "CREATE INDEX i ON t(date(a));"),
    "index-json-function": ("CREATE TABLE t(a TEXT);", "CREATE INDEX i ON t(json_extract(a, '$.k'));"),
    "unknown-collation": ("CREATE TABLE t(a TEXT);", "SELECT a COLLATE foo FROM t;"),
    "add-column-constraint": ("CREATE TABLE t(a INTEGER);", "ALTER TABLE t ADD COLUMN b TEXT DEFAULT +'x';"),
    "row-dependent-key": ("CREATE TABLE t(a INTEGER UNIQUE);", "UPDATE t SET a = a + 1;"),
    "conflict-without-target": ("CREATE TABLE t(a INTEGER UNIQUE, b INTEGER UNIQUE);",
                                "INSERT INTO t VALUES (1, 2) ON CONFLICT DO UPDATE SET b = 3;"),
    "mixed-conflict-algorithms": ("CREATE TABLE t(a INTEGER UNIQUE ON CONFLICT IGNORE, b INTEGER UNIQUE);",
                                  "INSERT INTO t VALUES (1, 2);"),
    "constraint-algorithm-update": ("CREATE TABLE t(a INTEGER UNIQUE ON CONFLICT REPLACE);", "UPDATE t SET a = 1;"),
    "replace-default": ("CREATE TABLE t(a INTEGER NOT NULL DEFAULT CURRENT_TIMESTAMP);",
                        "INSERT OR REPLACE INTO t VALUES (NULL);"),
    "insert-column-twice": ("CREATE TABLE t(a INTEGER);", "INSERT INTO t(a, a) VALUES (1, 2);"),
    "update-column-twice": ("CREATE TABLE t(a INTEGER);", "UPDATE t SET a = 1, a = 2;"),
    "rowid-name": ("CREATE TABLE t(a INTEGER);", "SELECT rowid FROM t;"),
    "join-operator": ("CREATE TABLE t(a INTEGER); CREATE TABLE u(a INTEGER);",
                      "SELECT * FROM t INNER OUTER JOIN u ON t.a = u.a;"),
    "later-table-in-on": ("CREATE TABLE t(a INTEGER); CREATE TABLE u(a INTEGER); CREATE TABLE v(a INTEGER);",
                          "SELECT t.a FROM t JOIN u ON v.a = 1 JOIN v;"),
    "system-table": ("CREATE TABLE t(a INTEGER);", "SELECT name FROM sqlite_schema;"),
    "unmodeled-function": ("CREATE TABLE t(a INTEGER);", "SELECT ln(a) FROM t;"),
    "aggregate-in-expression": ("CREATE TABLE t(a INTEGER);", "SELECT json(count(*)) FROM t;"),
    "alias-in-expression": ("CREATE TABLE t(a INTEGER);", "SELECT a AS b FROM t WHERE b = 1;"),
    "group-by-term": ("CREATE TABLE t(a INTEGER);", "SELECT count(*) FROM t GROUP BY a + 1;"),
    "bare-column": ("CREATE TABLE t(a INTEGER, b INTEGER);", "SELECT a, count(*) FROM t GROUP BY b;"),
    "aggregate-order-by": ("CREATE TABLE t(a INTEGER, b INTEGER);", "SELECT count(*) FROM t GROUP BY a ORDER BY b;"),
    "window-value": ("CREATE TABLE t(a INTEGER);", "SELECT a FROM t LIMIT 'x';"),
    "negative-offset": ("CREATE TABLE t(a INTEGER);", "SELECT a FROM t LIMIT 1 OFFSET -1;"),
    "windowed-group-sum": ("CREATE TABLE t(a INTEGER);", "SELECT sum(a) FROM t GROUP BY a LIMIT 1;"),
    "constant-function-error": ("CREATE TABLE t(a);", "INSERT INTO t VALUES (json_extract('x', '$'));"),
    "table-function": ("CREATE TABLE t(a);", "SELECT * FROM json_tree('[1]');"),
    "function-join": ("CREATE TABLE t(a);", "SELECT * FROM t RIGHT JOIN json_each('[1]');"),
    "later-source-in-arguments": ("CREATE TABLE t(a);", "SELECT * FROM t, json_each(b.value) AS a, json_each('[1]') AS b;"),
    "json-subtype": ("CREATE TABLE t(a);", "SELECT json_array(coalesce(json(a), 1)) FROM t;"),
    "subquery-here": ("CREATE TABLE t(a);", "SELECT * FROM t JOIN t AS b ON EXISTS (SELECT 1);"),
    "outer-aggregate": ("CREATE TABLE t(a);", "SELECT (SELECT count(t.a) FROM t AS b) FROM t;"),
    "subquery-fallible-call": ("CREATE TABLE t(a);", "SELECT json((SELECT a FROM t));"),
    "subquery-reads-target": ("CREATE TABLE t(a);", "UPDATE t SET a = (SELECT max(a) FROM t);"),
    "distinct-order-by": ("CREATE TABLE t(a, b);", "SELECT DISTINCT a FROM t ORDER BY b;"),
    "deferred-foreign-key": ("CREATE TABLE p(id PRIMARY KEY); CREATE TABLE c(x REFERENCES p DEFERRABLE INITIALLY DEFERRED);",
                             "PRAGMA foreign_keys = ON; INSERT INTO c VALUES (1);"),
    "foreign-key-upsert": ("CREATE TABLE p(id PRIMARY KEY); CREATE TABLE c(id PRIMARY KEY, x REFERENCES p);",
                           "PRAGMA foreign_keys = ON; INSERT INTO c VALUES (1, NULL) ON CONFLICT(id) DO UPDATE SET x = NULL;"),
    "raise-form": ("CREATE TABLE t(a);",
                   "CREATE TRIGGER r BEFORE INSERT ON t BEGIN SELECT 1 WHERE RAISE(IGNORE); END; INSERT INTO t VALUES (1);"),
    "trigger-form": ("CREATE TABLE t(a UNIQUE); CREATE TABLE u(a);",
                     "CREATE TRIGGER r AFTER INSERT ON u BEGIN INSERT INTO t VALUES (new.a) ON CONFLICT(a) DO UPDATE SET a = 2; "
                     "END; INSERT INTO u VALUES (1);"),
    "trigger-writes-own-table": ("CREATE TABLE t(a);",
                                 "CREATE TRIGGER r BEFORE DELETE ON t BEGIN DELETE FROM t; END; DELETE FROM t;"),
    "schema-trigger-order": ("CREATE TABLE t(a); CREATE TABLE log(x); "
                             "CREATE TRIGGER r AFTER INSERT ON t BEGIN INSERT INTO log VALUES (1); END; "
                             "CREATE TRIGGER s AFTER INSERT ON t BEGIN INSERT INTO log VALUES (2); END;",
                             "INSERT INTO t VALUES (1);"),
}
"""For each restriction id: a schema and a migration that the resolver refuses with it."""

PROFILE = "3.51.0"
"""The execution profile of the examples."""


def resolve_example(runtime: Path, schema: str, migration: str) -> dict[str, Json]:
    """Parse the example with the runtime's parser library and resolve it with the runtime's
    `migration-resolver`. Return the resolver's result, or `{"status": "frontend", "message": ...}`
    when the frontend refuses the SQL."""
    selected = profile(PROFILE)
    parser = SqlParser.for_profile(runtime_library(runtime), ProfileIdentity(selected.engine, selected.source_id))
    try:
        record = script_record(selected, statements(parse(parser, schema.encode(), "schema.sql")),
                               statements(parse(parser, migration.encode(), "migration.sql")))
    except SqlError as error:
        return {"status": "frontend", "message": str(error)}
    with TemporaryDirectory(prefix="restriction-example-") as directory:
        record_path, output = Path(directory) / "record.json", Path(directory) / "generated"
        record_path.write_text(json.dumps(record), encoding="utf-8")
        output.mkdir()
        resolved = subprocess.run([str(runtime / ".lake/build/bin/migration-resolver"), str(record_path), str(output)],
                                  capture_output=True, text=True, timeout=30, check=False)
    if resolved.returncode:
        raise RuntimeError(f"migration-resolver failed: {resolved.stderr}")
    result: dict[str, Json] = json.loads(resolved.stdout)
    return result

