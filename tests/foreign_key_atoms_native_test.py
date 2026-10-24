"""Native SQLite checks the execution cases behind the split foreign-key atoms."""

from dataclasses import replace
from pathlib import Path

import pytest

from conformance.authored_resolution import profile
from conformance.model_check import compiled, prove
from conformance.native_record import record_sql
from conformance.native_replay import model_case
from conformance.sql_text import runtime_translator

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.kernel,
              pytest.mark.requires_lean, pytest.mark.requires_native("translation-program", "sqlite3")]

PROBES: list[tuple[str, str, str, int, str | None]] = [
    ("drop-supporting-index",
     "CREATE TABLE p(k TEXT); CREATE UNIQUE INDEX p_key ON p(k);"
     "CREATE TABLE c(x TEXT REFERENCES p(k)); INSERT INTO p VALUES('a'); INSERT INTO c VALUES('a');",
     "PRAGMA foreign_keys=ON; DROP INDEX p_key; PRAGMA foreign_key_check;", 1, "prepare"),
    ("orphan-with-valid-schema",
     "CREATE TABLE p(k PRIMARY KEY); CREATE TABLE c(x REFERENCES p);"
     "INSERT INTO p VALUES(1); INSERT INTO c VALUES(1);",
     "DELETE FROM p; PRAGMA foreign_key_check;", 0, None),
    ("missing-null", "CREATE TABLE c(x REFERENCES p); INSERT INTO c VALUES(NULL);",
     "PRAGMA foreign_key_check;", 0, None),
    ("missing-nonnull", "CREATE TABLE c(x REFERENCES p); INSERT INTO c VALUES(9);",
     "PRAGMA foreign_key_check;", 0, None),
    ("nonunique-null", "CREATE TABLE p(k); CREATE TABLE c(x REFERENCES p(k)); INSERT INTO c VALUES(NULL);",
     "PRAGMA foreign_key_check;", 1, "prepare"),
    ("repeated-parent-columns",
     "CREATE TABLE p(a,b,PRIMARY KEY(a,a)); CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b));",
     "PRAGMA foreign_keys=ON; INSERT INTO p VALUES(1,2); INSERT INTO c VALUES(1,99);"
     "PRAGMA foreign_key_check;", 0, None),
    ("repeated-unused-null-write",
     "CREATE TABLE p(a,b,PRIMARY KEY(a,a)); CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b));"
     "INSERT INTO p VALUES(1,2);",
     "PRAGMA foreign_keys=ON; INSERT INTO c VALUES(99,NULL);", 19, "step"),
    ("repeated-unused-null-pragma",
     "CREATE TABLE p(a,b,PRIMARY KEY(a,a)); CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b));"
     "INSERT INTO p VALUES(1,2); INSERT INTO c VALUES(99,NULL);",
     "PRAGMA foreign_key_check;", 0, None),
    ("repeated-selected-null-write",
     "CREATE TABLE p(a,b,PRIMARY KEY(a,a)); CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b));",
     "PRAGMA foreign_keys=ON; INSERT INTO c VALUES(NULL,99); PRAGMA foreign_key_check;", 0, None),
    ("repeated-unused-null-update",
     "CREATE TABLE p(a,b,PRIMARY KEY(a,a)); CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b));"
     "INSERT INTO p VALUES(1,2); INSERT INTO c VALUES(1,NULL);",
     "PRAGMA foreign_keys=ON; UPDATE c SET x=99;", 19, "step"),
    ("repeated-selected-null-update",
     "CREATE TABLE p(a,b,PRIMARY KEY(a,a)); CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b));"
     "INSERT INTO p VALUES(1,2); INSERT INTO c VALUES(1,99);",
     "PRAGMA foreign_keys=ON; UPDATE c SET x=NULL; PRAGMA foreign_key_check;", 0, None),
    ("repeated-unused-null-parent-delete",
     "CREATE TABLE p(a,b,PRIMARY KEY(a,a)); CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b));"
     "INSERT INTO p VALUES(1,2); INSERT INTO c VALUES(1,NULL);",
     "PRAGMA foreign_keys=ON; DELETE FROM p;", 19, "step"),
    ("repeated-unused-null-parent-update",
     "CREATE TABLE p(a,b,PRIMARY KEY(a,a)); CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b));"
     "INSERT INTO p VALUES(1,2); INSERT INTO c VALUES(1,NULL);",
     "PRAGMA foreign_keys=ON; UPDATE p SET a=99;", 19, "step"),
    ("repeated-unused-null-cascade",
     "CREATE TABLE p(a,b,PRIMARY KEY(a,a));"
     "CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b) ON UPDATE CASCADE);"
     "INSERT INTO p VALUES(1,2); INSERT INTO c VALUES(1,NULL);",
     "PRAGMA foreign_keys=ON; UPDATE p SET a=99; PRAGMA foreign_key_check;", 0, None),
    ("repeated-cascade-unused-column",
     "CREATE TABLE p(a,b,PRIMARY KEY(a,a));"
     "CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b) ON UPDATE CASCADE);"
     "INSERT INTO p VALUES(1,2); INSERT INTO c VALUES(1,99);",
     "PRAGMA foreign_keys=ON; UPDATE p SET a=2; SELECT x,y FROM c;", 0, None),
    ("repeated-set-null-unused-column",
     "CREATE TABLE p(a,b,PRIMARY KEY(a,a));"
     "CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b) ON DELETE SET NULL);"
     "INSERT INTO p VALUES(1,2); INSERT INTO c VALUES(1,99);",
     "PRAGMA foreign_keys=ON; DELETE FROM p; SELECT x,y FROM c;", 0, None),
    ("repeated-set-default-unused-column",
     "CREATE TABLE p(a,b,PRIMARY KEY(a,a));"
     "CREATE TABLE c(x DEFAULT 3,y DEFAULT 4,FOREIGN KEY(x,y) REFERENCES p(a,b) ON DELETE SET DEFAULT);"
     "INSERT INTO p VALUES(1,2),(3,4); INSERT INTO c VALUES(1,99);",
     "PRAGMA foreign_keys=ON; DELETE FROM p WHERE a=1; SELECT x,y FROM c;", 0, None),
    ("repeated-action-trigger-columns",
     "CREATE TABLE p(a,b,PRIMARY KEY(a,a));"
     "CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b) ON UPDATE CASCADE);"
     "CREATE TABLE log(k);"
     "INSERT INTO p VALUES(1,2); INSERT INTO c VALUES(1,99);",
     "PRAGMA foreign_keys=ON;"
     "CREATE TRIGGER used AFTER UPDATE OF x ON c BEGIN INSERT INTO log VALUES('x'); END;"
     "CREATE TRIGGER unused AFTER UPDATE OF y ON c BEGIN INSERT INTO log VALUES('y'); END;"
     "UPDATE p SET a=2; SELECT x,y FROM c; SELECT k FROM log ORDER BY k;", 0, None),
    ("repeated-update-set-null",
     "CREATE TABLE p(a,b,PRIMARY KEY(a,a));"
     "CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b) ON UPDATE SET NULL);"
     "INSERT INTO p VALUES(1,2); INSERT INTO c VALUES(1,99);",
     "PRAGMA foreign_keys=ON; UPDATE p SET a=2; SELECT x,y FROM c;", 0, None),
    ("repeated-update-set-default",
     "CREATE TABLE p(a,b,PRIMARY KEY(a,a));"
     "CREATE TABLE c(x DEFAULT 3,y DEFAULT 4,FOREIGN KEY(x,y) REFERENCES p(a,b) ON UPDATE SET DEFAULT);"
     "INSERT INTO p VALUES(1,2),(3,4); INSERT INTO c VALUES(1,99);",
     "PRAGMA foreign_keys=ON; UPDATE p SET a=2 WHERE a=1; SELECT x,y FROM c;", 0, None),
    ("selected-generated-constraint",
     "CREATE TABLE p(a,b,PRIMARY KEY(a,a)); CREATE TABLE q(k PRIMARY KEY);"
     "CREATE TABLE c(x,y,z GENERATED ALWAYS AS(x+1) STORED REFERENCES q(k),"
     "FOREIGN KEY(x,y) REFERENCES p(a,b) ON UPDATE CASCADE);"
     "INSERT INTO p VALUES(1,2); INSERT INTO q VALUES(2); INSERT INTO c(x,y) VALUES(1,99);",
     "PRAGMA foreign_keys=ON; UPDATE p SET a=2;", 19, "step"),
    ("unused-generated-constraint",
     "PRAGMA foreign_keys=OFF; CREATE TABLE p(a,b,PRIMARY KEY(a,a)); CREATE TABLE q(k PRIMARY KEY);"
     "CREATE TABLE c(x,y,z GENERATED ALWAYS AS(y+1) STORED REFERENCES q(k),"
     "FOREIGN KEY(x,y) REFERENCES p(a,b) ON UPDATE CASCADE);"
     "INSERT INTO p VALUES(1,2); INSERT INTO c(x,y) VALUES(1,99); PRAGMA foreign_keys=ON;",
     "PRAGMA foreign_keys=ON; UPDATE p SET a=2; SELECT x,y,z FROM c;", 0, None),
    ("ordinary-composite-action-order",
     "CREATE TABLE p(a,b,PRIMARY KEY(b,a));"
     "CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b) ON UPDATE CASCADE);"
     "INSERT INTO p VALUES(1,2); INSERT INTO c VALUES(1,2);",
     "PRAGMA foreign_keys=ON; UPDATE p SET a=3,b=4; SELECT x,y FROM c;", 0, None),
    ("rowid-parent-actions",
     "CREATE TABLE p(k INTEGER PRIMARY KEY);"
     "CREATE TABLE c(x REFERENCES p ON UPDATE CASCADE ON DELETE SET NULL,y);"
     "INSERT INTO p VALUES(1); INSERT INTO c VALUES(1,99);",
     "PRAGMA foreign_keys=ON; UPDATE p SET k=2; SELECT x,y FROM c; DELETE FROM p; SELECT x,y FROM c;", 0, None),
    ("unused-action-trigger-not-prepared",
     "CREATE TABLE p(a,b,PRIMARY KEY(a,a));"
     "CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b) ON UPDATE CASCADE);"
     "CREATE TRIGGER unused AFTER UPDATE OF y ON c BEGIN INSERT INTO absent VALUES(1); END;"
     "INSERT INTO p VALUES(1,2); INSERT INTO c VALUES(1,99);",
     "PRAGMA foreign_keys=ON; UPDATE p SET a=2; SELECT x,y FROM c;", 0, None),
    ("generated-action-trigger-not-prepared",
     "CREATE TABLE p(a INTEGER PRIMARY KEY);"
     "CREATE TABLE c(x REFERENCES p ON UPDATE CASCADE,z GENERATED ALWAYS AS(x+1) STORED);"
     "CREATE TRIGGER unused AFTER UPDATE OF z ON c BEGIN INSERT INTO absent VALUES(1); END;"
     "INSERT INTO p VALUES(1); INSERT INTO c(x) VALUES(1);",
     "PRAGMA foreign_keys=ON; UPDATE p SET a=2; SELECT x,z FROM c;", 0, None),
    ("missing-composite-null-fallback",
     "CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b)); INSERT INTO c VALUES(99,NULL);",
     "PRAGMA foreign_key_check;", 0, None),
    ("lookup-scan-affinity-orphan",
     "CREATE TABLE p(k TEXT UNIQUE); CREATE TABLE c(x INTEGER REFERENCES p(k));"
     "INSERT INTO p VALUES('1'); INSERT INTO c VALUES(1);"
     "CREATE TRIGGER replace_parent AFTER DELETE ON p WHEN old.k='1'"
     " BEGIN INSERT INTO p VALUES('01'); END;",
     "PRAGMA foreign_keys=ON; DELETE FROM p WHERE k='1'; PRAGMA foreign_key_check;", 0, None),
    ("composite-affinity-collation",
     "CREATE TABLE p(a INTEGER,b TEXT COLLATE NOCASE,PRIMARY KEY(a,b));"
     "CREATE TABLE c(x TEXT,y TEXT,FOREIGN KEY(x,y) REFERENCES p);",
     "PRAGMA foreign_keys=ON; INSERT INTO p VALUES(1,'A'); INSERT INTO c VALUES('01','a');"
     "PRAGMA foreign_key_check;", 0, None),
    ("rowid-affinity", "CREATE TABLE p(k INTEGER PRIMARY KEY); CREATE TABLE c(x REFERENCES p);",
     "PRAGMA foreign_keys=ON; INSERT INTO p VALUES(1); INSERT INTO c VALUES('01'); PRAGMA foreign_key_check;", 0, None),
    ("filtered-parent-index", "CREATE TABLE p(k); CREATE UNIQUE INDEX pk ON p(k) WHERE k>0;"
     "CREATE TABLE c(x REFERENCES p(k));", "PRAGMA foreign_key_check;", 1, "prepare"),
    ("expression-parent-index", "CREATE TABLE p(k); CREATE UNIQUE INDEX pk ON p(k+0);"
     "CREATE TABLE c(x REFERENCES p(k));", "PRAGMA foreign_key_check;", 1, "prepare"),
    ("wrong-index-collation", "CREATE TABLE p(k TEXT); CREATE UNIQUE INDEX pk ON p(k COLLATE NOCASE);"
     "CREATE TABLE c(x REFERENCES p(k));", "PRAGMA foreign_key_check;", 1, "prepare"),
    ("implicit-primary-arity", "CREATE TABLE p(a,b,PRIMARY KEY(a,b)); CREATE TABLE c(x REFERENCES p);",
     "PRAGMA foreign_key_check;", 1, "prepare"),
    ("second-eligible-index", "CREATE TABLE p(a,b); CREATE UNIQUE INDEX first_key ON p(a,b);"
     "CREATE UNIQUE INDEX second_key ON p(b,a); CREATE TABLE c(x,y,FOREIGN KEY(x,y) REFERENCES p(a,b));"
     "INSERT INTO p VALUES(1,2); INSERT INTO c VALUES(1,2);",
     "PRAGMA foreign_keys=ON; DROP INDEX first_key; PRAGMA foreign_key_check;", 0, None),
]
"""Execution probes of the cases quantified by ForeignKeyFacts and ForeignKeyCheckLaws."""


@pytest.mark.parametrize("name,setup,sql,code,phase", PROBES, ids=[probe[0] for probe in PROBES])
def test_foreign_key_atom_execution_matches_native(name: str, setup: str, sql: str, code: int,
                                                  phase: str | None, runtime_root: Path, tmp_path: Path) -> None:
    """The existing FK engine and pragma agree with native on every atom-separation case.

    The same native trace is classified by the executable model and replayed as a kernel proof;
    preparation errors cannot be confused with an empty violation list.
    """
    enabled = sql.startswith("PRAGMA foreign_keys=ON;")
    sql = sql.removeprefix("PRAGMA foreign_keys=ON;")
    selected = replace(profile(()), foreign_keys=enabled)
    record = record_sql(setup, sql, name=name, outputs=True, profile=selected, run_on=True)
    assert record["trace"][-1]["primaryCode"] == code, record["trace"]
    assert record["trace"][-1]["phase"] == phase, record["trace"]
    case = model_case(record, runtime_translator(runtime_root))
    answer = compiled(case, runtime_root, emit_lean=True)
    assert answer["verdict"] == "AGREE", answer
    prove(answer["caseLean"], runtime_root, tmp_path / "ForeignKeyNative.lean", case=case)
