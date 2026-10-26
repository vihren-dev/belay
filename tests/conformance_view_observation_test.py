"""View observations use current query metadata, rows and connection context (ADR 0019)."""

import json
from pathlib import Path
import subprocess
import sys

import pytest

from conformance.authored_clock import profile as clock_profile
from conformance.authored_resolution import profile
from conformance.case_format import Json
from conformance.model_check import kernel_check
from conformance.native_record import record_sql
from judge.compare import case_verdict
from judge.records import subject_input

pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.requires_lean,
              pytest.mark.requires_native("translation-program", "sqlite3")]


def predictions(runtime: Path, inputs: list[dict[str, Json]]) -> list[dict[str, Json]]:
    """Run the real subject on supplied inputs, with a finite subprocess deadline."""
    result = subprocess.run([sys.executable, "-m", "conformance.predict", "--runtime", str(runtime)],
                            input="".join(json.dumps(item) + "\n" for item in inputs),
                            capture_output=True, text=True, timeout=60, check=False)
    assert result.returncode == 0, result.stderr
    answers = [json.loads(line) for line in result.stdout.splitlines()]
    assert len(answers) == len(inputs)
    return answers


@pytest.mark.parametrize("setup,migration", [
    ("CREATE TABLE t(a INTEGER PRIMARY KEY, b VARCHAR(4) NOT NULL); INSERT INTO t VALUES(1,'x');"
     "CREATE VIEW v AS SELECT b,b,a+1 AS n FROM t;", "INSERT INTO t VALUES(2,'x');"),
    ("CREATE TABLE t(a INTEGER); INSERT INTO t VALUES(1),(1),(2);"
     "CREATE VIEW v(x) AS SELECT a FROM t; CREATE VIEW w AS SELECT * FROM v;",
     "BEGIN; DELETE FROM t WHERE a=1; ROLLBACK; DROP VIEW w;"),
    ("CREATE VIEW v AS SELECT CAST(1 AS INT) AS x UNION ALL SELECT 2;", "SELECT * FROM v;"),
    ("CREATE TABLE t(a TEXT);", "CREATE VIEW v AS SELECT a FROM t; DROP VIEW v;"),
])
def test_view_observations_match_native(runtime_root: Path, setup: str, migration: str) -> None:
    """PredictTables and the renderer match native view metadata, duplicate rows and snapshots."""
    record = record_sql(setup, migration, name="view-observation", outputs=True)
    [answer] = predictions(runtime_root, [subject_input(record)])
    assert case_verdict(record, answer).name == "AGREE", answer


@pytest.mark.parametrize("setup,migration", [
    ("CREATE TABLE t(a INTEGER PRIMARY KEY, b VARCHAR(4) NOT NULL DEFAULT 'x', c);"
     "CREATE VIEW v AS SELECT a,b,c,a+1,CAST(b AS TEXT) AS e FROM t;", "PRAGMA table_info(v);"),
    ("CREATE TABLE t(a INT, b TEXT); CREATE VIEW v(x,y) AS SELECT * FROM t;", "PRAGMA table_info(V);"),
    ("CREATE VIEW v AS SELECT 1, 'x', NULL;", "PRAGMA table_info(v); PRAGMA table_info(v);"),
    ("CREATE TABLE t(a); CREATE VIEW v AS SELECT a,a FROM t; CREATE VIEW w AS SELECT * FROM v;",
     "PRAGMA table_info(w);"),
    ("CREATE TABLE t(a INT);", "CREATE VIEW v AS SELECT a FROM t; PRAGMA table_info(v); DROP VIEW v;"),
    # A pragma table function in a view body works when the schema is trusted, the default of
    # the profile; native SQLite refuses it as unsafe only after PRAGMA trusted_schema=OFF.
    ("CREATE TABLE t(a INT);", "CREATE VIEW v AS SELECT name FROM pragma_table_info('t');"
     "SELECT * FROM v; PRAGMA table_info(v);"),
])
def test_view_table_info_matches_native(runtime_root: Path, setup: str, migration: str) -> None:
    """PRAGMA table_info of a view gives the current names and normalized types of its
    query, with notnull 0, dflt_value NULL and pk 0, like native SQLite."""
    record = record_sql(setup, migration, name="view-table-info", outputs=True)
    [answer] = predictions(runtime_root, [subject_input(record)])
    assert case_verdict(record, answer).name == "AGREE", answer


@pytest.mark.parametrize("statement", [
    "INSERT INTO v VALUES(1)", "UPDATE v SET a=1 WHERE zz=1", "DELETE FROM v", "REPLACE INTO v VALUES(1)",
    "INSERT INTO V VALUES(1, zz)", "CREATE INDEX i ON v(a)", "CREATE INDEX t ON v(zz)",
    "ALTER TABLE v ADD COLUMN c", "CREATE TRIGGER tr AFTER INSERT ON v BEGIN SELECT 1; END",
    "CREATE TRIGGER tr BEFORE UPDATE ON V BEGIN SELECT 1; END",
])
def test_view_write_errors_match_native(runtime_root: Path, statement: str) -> None:
    """A write, an index, an added column or a trigger on a readable view fails as in native SQLite,
    after the statements before it, and the view observation of the data stays the same."""
    record = record_sql("CREATE TABLE t(a); INSERT INTO t VALUES(1); CREATE VIEW v AS SELECT a FROM t;",
                        "INSERT INTO t VALUES(2); " + statement + "; INSERT INTO t VALUES(3);",
                        name="view-write-error", outputs=True)
    [answer] = predictions(runtime_root, [subject_input(record)])
    assert case_verdict(record, answer).name == "AGREE", answer


def test_view_observation_counter_context(runtime_root: Path) -> None:
    """The pass preserves writer counters; an open snapshot's independent reader has zeros."""
    record = record_sql("CREATE TABLE t(a); INSERT INTO t VALUES(1),(2);"
                        "CREATE VIEW v AS SELECT changes(),total_changes(),last_insert_rowid();",
                        "BEGIN; INSERT INTO t VALUES(3); ROLLBACK;", name="view-counters",
                        outputs=True, profile=profile(()), run_on=True, counters=True)
    [answer] = predictions(runtime_root, [subject_input(record)])
    assert case_verdict(record, answer).name == "AGREE", answer


def test_view_observation_clock_context(runtime_root: Path) -> None:
    """A newly created view observes each supplied clock, without inventing an initial clock."""
    record = record_sql("", "CREATE VIEW v AS SELECT unixepoch('now') AS t; SELECT 1;",
                        name="view-clock", outputs=True, profile=clock_profile(),
                        setup_clock=1700000000000, clock_values=[1800000000000, 1900000000000])
    [answer] = predictions(runtime_root, [subject_input(record)])
    assert case_verdict(record, answer).name == "AGREE", answer


def test_view_observation_unavailable_context(runtime_root: Path) -> None:
    """Missing historical counters and a missing setup clock stay explicitly unmodeled."""
    counters = record_sql("CREATE VIEW v AS SELECT total_changes();", "", name="unknown-counters")
    clock = record_sql("CREATE VIEW v AS SELECT unixepoch('now');", "SELECT 1;", name="unknown-clock",
                       outputs=True, profile=clock_profile(), setup_clock=1700000000000,
                       clock_values=[1800000000000])
    withheld = subject_input(clock)
    del withheld["setupClockUnixMilliseconds"]
    answers = predictions(runtime_root, [subject_input(counters), withheld])
    assert all(answer["status"] == "unsupported" for answer in answers), answers
    assert "total_changes" in answers[0]["reason"] and "clock" in answers[1]["reason"]


def test_view_observation_uses_the_forwarded_setup_clock(runtime_root: Path) -> None:
    """The judge forwards the clock of the setup, so a schema view that reads the clock is observed
    at the start as SQLite observed it, and the prediction agrees."""
    record = record_sql("CREATE VIEW v AS SELECT unixepoch('now') AS t;", "SELECT 1;", name="setup-clock",
                        outputs=True, profile=clock_profile(), setup_clock=1700000000000,
                        clock_values=[1800000000000])
    given = subject_input(record)
    assert given["setupClockUnixMilliseconds"] == 1700000000000
    [answer] = predictions(runtime_root, [given])
    assert case_verdict(record, answer).name == "AGREE", answer


@pytest.mark.parametrize("body", [
    "SELECT * FROM missing", "SELECT * FROM v", "SELECT zzz FROM t", "SELECT new.a FROM t", "SELECT a FROM t WHERE zz",
    "SELECT * FROM t JOIN missing", "SELECT a FROM t UNION SELECT * FROM missing",
    "SELECT * FROM (SELECT * FROM missing)",
])
def test_unreadable_view_is_recorded_with_its_error(runtime_root: Path, body: str) -> None:
    """A view over a missing table or column, or in a cycle, is created and kept by SQLite, which fails
    only when a statement reads it. The recorder keeps its error code, the model predicts the code
    through the same resolver, and the prediction agrees. The recording stops at the first read of the view,
    which fails as SQLite fails it."""
    record = record_sql("CREATE TABLE t(a); INSERT INTO t VALUES(1);", f"CREATE VIEW v AS {body}; "
                        "INSERT INTO t VALUES(2); SELECT * FROM v; DROP VIEW v;",
                        name="unreadable-view", outputs=True)
    kept = [table for step in [record["initial"], *record["trace"]] for table in step["visible"]["tables"]
            if table.get("unreadable")]
    assert len(kept) == 3 and all(table["unreadable"]["primaryCode"] == 1 for table in kept), kept
    [answer] = predictions(runtime_root, [subject_input(record)])
    assert case_verdict(record, answer).name == "AGREE", answer


def test_unreadable_views_in_the_schema_and_in_a_transaction(runtime_root: Path) -> None:
    """An unreadable view that exists before the migration, and one created or dropped inside a
    transaction that rolls back, give the committed and visible snapshots of SQLite."""
    record = record_sql("CREATE TABLE t(a); CREATE VIEW v AS SELECT * FROM missing;",
                        "BEGIN; CREATE VIEW c AS SELECT * FROM c; INSERT INTO t VALUES(1); ROLLBACK; "
                        "DROP VIEW v; CREATE TABLE missing(x); CREATE VIEW v AS SELECT * FROM missing;"
                        "SELECT * FROM v;", name="unreadable-view-transaction", outputs=True)
    [answer] = predictions(runtime_root, [subject_input(record)])
    assert case_verdict(record, answer).name == "AGREE", answer


def test_a_failing_view_body_stays_out_of_scope(runtime_root: Path) -> None:
    """A view whose body fails when it runs, here by an integer overflow, is recorded with its code,
    but the model keeps the existing fallible-source restriction, so the case is out of scope."""
    record = record_sql("", "CREATE VIEW v AS SELECT abs(-9223372036854775808);", name="failing-view",
                        outputs=True)
    assert record["trace"][0]["visible"]["tables"][0]["unreadable"]["primaryCode"] == 1
    [answer] = predictions(runtime_root, [subject_input(record)])
    assert answer["status"] == "unsupported" and "view observation" in answer["reason"], answer
    assert case_verdict(record, answer).name == "MODEL_UNSUPPORTED", answer


def test_view_observation_output_boundaries(runtime_root: Path, tmp_path: Path) -> None:
    """The kernel checks multiset alternatives, empty alternatives and SQL-error retention."""
    source = tmp_path / "ViewObservationBoundaries.lean"
    source.write_text('''import VerifierConformance.ViewObservation
open Belay.Sqlite.Model Belay.Sqlite.Model.Conformance
def rowsOf : Except ViewObservationIssue (List (List Value)) → Option (List (List Value))
  | .ok rows => some rows
  | .error _ => none
def errorCode : Except ViewObservationIssue (List (List Value)) → Option Nat
  | .error (.output (.error code)) => some code
  | _ => none
theorem sameMultiset : rowsOf (viewObservationRows (.oneOf
    [[[.integer 1], [.integer 2]], [[.integer 2], [.integer 1]]])) =
    some [[.integer 1], [.integer 2]] := by decide +kernel
theorem differentMultiset : rowsOf (viewObservationRows (.oneOf
    [[[.integer 1]], [[.integer 2]]])) = none := by decide +kernel
theorem emptyAlternatives : rowsOf (viewObservationRows (.oneOf [])) = none := by decide +kernel
theorem sqlFailure : errorCode (viewObservationRows (.error 1)) = some 1 := by decide +kernel
#print axioms sameMultiset
#print axioms differentMultiset
#print axioms emptyAlternatives
#print axioms sqlFailure
''')
    assert kernel_check(runtime_root, source).count("depends on axioms") == 4
