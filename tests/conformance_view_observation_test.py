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
    """Missing historical counters and the unforwarded setup clock stay explicitly unmodeled."""
    counters = record_sql("CREATE VIEW v AS SELECT total_changes();", "", name="unknown-counters")
    clock = record_sql("CREATE VIEW v AS SELECT unixepoch('now');", "SELECT 1;", name="unknown-clock",
                       outputs=True, profile=clock_profile(), setup_clock=1700000000000,
                       clock_values=[1800000000000])
    answers = predictions(runtime_root, [subject_input(counters), subject_input(clock)])
    assert all(answer["status"] == "unsupported" for answer in answers), answers
    assert "total_changes" in answers[0]["reason"] and "clock" in answers[1]["reason"]


@pytest.mark.parametrize("body,status", [("SELECT * FROM missing", "error"), ("SELECT * FROM v", "error"),
                                        ("SELECT abs(-9223372036854775808)", "unsupported")])
def test_unreadable_view_is_failed_observation(runtime_root: Path, body: str, status: str) -> None:
    """A broken view keeps its prepare error; the existing fallible-source restriction stays explicit.

    These are subject-only inputs: the current native recorder itself fails while taking
    such a snapshot. Direct native CREATE/use coverage is in ClaimsViewCreate.
    """
    given = subject_input(record_sql("", "", name="unreadable-view"))
    given["initialSchemaSql"] = f"CREATE VIEW v AS {body};"
    [answer] = predictions(runtime_root, [given])
    assert answer["status"] == status and "view observation" in answer["reason"], answer
    assert "in view v" in answer["reason"], answer
    if status == "error":
        assert "Change the view or drop it" in answer["reason"], answer


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
