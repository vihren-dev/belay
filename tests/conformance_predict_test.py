"""The subject's predict command (`conformance.predict`, `conformance.predict_render`), ADR 0011.

The judge compares the subject's predictions with SQLite's recordings in SQLite's catalog
terms, so the renderer must state what SQLite reports for each table shape that the model
supports. Each declaration below is recorded by native SQLite, translated by the frontend and
rendered; the judge's comparison form (`judge.catalog`) of both must be equal.
"""

import json
from pathlib import Path
import subprocess
import sys

import pytest

from belay.sqlite.sql_tree import parse
from belay.sqlite.translate import starting_schema
from conformance.case_format import schema_wire
from conformance.native_record import record_sql
from conformance.predict_render import view_record
from conformance.record_parser import default_parser
from judge.catalog import tables_form
from judge.records import subject_input

pytestmark = [pytest.mark.integration, pytest.mark.conformance,
              pytest.mark.requires_lean, pytest.mark.requires_native("parser-library", "sqlite3")]

PREDICT_TIMEOUT_SECONDS = 60
"""One predict run over one small case."""
DECLARATIONS = {
    "affinities": "CREATE TABLE t(a INTEGER, b REAL, c TEXT, d BLOB, e NUMERIC);",
    "spellings": "CREATE TABLE t(a BIGINT, b TIMESTAMP, c BOOLEAN, d);",
    "not null and default": "CREATE TABLE t(a TEXT NOT NULL, b TIMESTAMP DEFAULT CURRENT_TIMESTAMP);",
    "lower-case default": "CREATE TABLE t(a TIMESTAMP DEFAULT current_timestamp);",
    "text primary key": "CREATE TABLE t(id TEXT PRIMARY KEY, a TEXT);",
    "integer primary key that is not the row id": "CREATE TABLE t(id BIGINT PRIMARY KEY, a TEXT);",
    "unique constraint": "CREATE TABLE t(a INTEGER, b TEXT, UNIQUE(a, b));",
    "indexes": "CREATE TABLE t(a INTEGER, b TEXT); CREATE INDEX t_a ON t(a); CREATE UNIQUE INDEX t_b ON t(b);",
}
"""Table shapes that the frontend admits and the model represents. Row-id aliases
(`INTEGER PRIMARY KEY`) and PRIMARY KEY table constraints are outside the model's scope."""


@pytest.mark.parametrize("name", DECLARATIONS)
def test_rendered_catalog_equals_native(name: str, runtime_root: Path) -> None:
    """`conformance.predict_render.view_record`: the catalog that the renderer states for a
    translated declaration is the catalog that native SQLite records for it."""
    record = record_sql(DECLARATIONS[name], "", name=name)
    recorded = record["initial"]["visible"]
    sql = subject_input(record)["initialSchemaSql"]
    schema = starting_schema(parse(default_parser(runtime_root), sql.encode(), "schema.sql"))
    model = [[table.name, {**{key: value for key, value in schema_wire(table).items() if key != "name"}, "rows": []}]
             for table in schema]
    assert tables_form(view_record(model)) == tables_form(recorded)


def test_predict_command_reports_scope(runtime_root: Path) -> None:
    """`conformance.predict.main`: an admitted case is predicted with one step per executed
    statement and a start offset; a refused one is out of scope with the frontend's reason."""
    admitted = record_sql("CREATE TABLE t(a INTEGER);", "INSERT INTO t(a) VALUES (1);", name="admitted")
    refused = record_sql("CREATE TABLE t(a INTEGER);", "CREATE VIEW v AS SELECT a FROM t;", name="refused")
    lines = "".join(json.dumps(subject_input(record)) + "\n" for record in (admitted, refused))
    result = subprocess.run([sys.executable, "-m", "conformance.predict", "--runtime", str(runtime_root)],
                            input=lines, capture_output=True, text=True, timeout=PREDICT_TIMEOUT_SECONDS, check=False)
    assert result.returncode == 0, result.stderr
    first, second = (json.loads(line) for line in result.stdout.splitlines())
    assert first["status"] == "predicted" and first["supported"] and len(first["steps"]) == 2
    assert first["steps"][1]["start"] == 0
    assert tables_form(first["steps"][1]["visible"]) == tables_form(admitted["trace"][0]["visible"])
    assert second["status"] == "unsupported" and second["reason"]


def test_execution_profiles_stay_out_of_scope(runtime_root: Path) -> None:
    """`conformance.predict.translated`: a case recorded with an execution profile (native
    record version 4) is out of scope, and the reason names the case and why."""
    given = {**subject_input(record_sql("CREATE TABLE t(a INTEGER);", "", name="profiled")), "nativeVersion": 4}
    result = subprocess.run([sys.executable, "-m", "conformance.predict", "--runtime", str(runtime_root)],
                            input=json.dumps(given) + "\n", capture_output=True, text=True,
                            timeout=PREDICT_TIMEOUT_SECONDS, check=False)
    prediction = json.loads(result.stdout)
    assert prediction["status"] == "unsupported"
    assert prediction["reason"].startswith("profiled: the model does not implement execution profiles")
