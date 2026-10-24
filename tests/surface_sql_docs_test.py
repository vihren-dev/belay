"""Checked SQL observations and a native Verso integration probe use installed surface code."""

import json
from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, module_setup

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_sql_doc_observations(runtime_root: Path, tmp_path: Path) -> None:
    """Our checker retains exact typed outputs, all alternatives and whitespace, and its
    actual-run adapter uses bindings, fresh databases and explicit clock environments."""
    setup = module_setup(runtime_root, tmp_path)
    result = run_command([str(runtime_root / "lean/bin/lean"), f"--setup={setup}",
                          str(FIXTURES / "SqlDocObservation.lean")], cwd=tmp_path, timeout=120)
    assert result.returncode == 0, result.diagnostic()
    assert "SQL doc observation checks passed" in result.stdout, result.diagnostic()


def test_sql_doc_native_registration_probe(runtime_root: Path, tmp_path: Path) -> None:
    """Our native raw-expander integration imports and calls the real observation adapter.
    Documentation data retains the SQL/comments, independent blocks start afresh, and
    changing either expected output or a SQL predicate rejects the checked example.
    The fixture's sql_probe name is not the future public sql handler."""
    setup = module_setup(runtime_root, tmp_path)
    config = json.loads(setup.read_text())
    config["name"] = "SqlDocRegistration"
    setup.write_text(json.dumps(config))
    artifact = tmp_path / "SqlDocRegistration.olean"
    result = run_command([str(runtime_root / "lean/bin/lean"), f"--setup={setup}",
                          "-o", str(artifact), str(FIXTURES / "SqlDocRegistration.lean")],
                         cwd=tmp_path, timeout=120)
    assert result.returncode == 0, result.diagnostic()
    config["importArts"]["SqlDocRegistration"] = [[str(artifact)]]
    config["name"] = "DocConsumer"
    setup.write_text(json.dumps(config))
    source = '''import SqlDocRegistration
set_option doc.verso true
open Belay.Sqlite
def start : Database := db! r"CREATE TABLE t(x INTEGER); INSERT INTO t VALUES(1)"
/-- Checked SQL body.
```sql_probe (db := start) (expected := "7")
UPDATE t SET x = 7;
SELECT x FROM t WHERE x = 7;
-- retained comment
```
-/
def documented : Unit := ()
/-- A second block starts from its own database.
```sql_probe (db := start) (expected := "1")
SELECT x FROM t;
```
-/
def independent : Unit := ()
open Lean Elab Command in
run_cmd do
  let some (.inr doc) ← findInternalDocString? (← getEnv) ``documented
    | throwError "Missing checked documentation data"
  let bodies := doc.text.filterMap fun
    | .code body => some body
    | _ => none
  unless bodies == #["UPDATE t SET x = 7;\\nSELECT x FROM t WHERE x = 7;\\n-- retained comment\\n"] do
    throwError "The checked documentation changed its SQL body: {bodies}"
  logInfo "SQL doc registration and preservation passed"
'''
    consumer = tmp_path / "DocConsumer.lean"
    for label, text in (
        ("passing", source),
        ("expectation", source.replace('(expected := "7")', '(expected := "8")')),
        ("predicate", source.replace("WHERE x = 7", "WHERE x = 8")),
    ):
        consumer.write_text(text)
        result = run_command([str(runtime_root / "lean/bin/lean"), f"--setup={setup}",
                              str(consumer)], cwd=tmp_path, timeout=120)
        if label == "passing":
            assert result.returncode == 0, result.diagnostic()
            assert "SQL doc registration and preservation passed" in result.stdout, result.diagnostic()
        else:
            assert result.returncode != 0, (label, result.diagnostic())
            assert "SQL result mismatch" in result.stdout, result.diagnostic()
            assert "expected text:" in result.stdout and "actual text:" in result.stdout, result.diagnostic()
