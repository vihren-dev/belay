"""S7 compiled SQL-source records: they persist with the module, survive imports and count each source once."""

from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.sql_file_support import installed_layout, lake_build, write_package
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

QUERIES = '''import Belay
open Belay.Sqlite

/-- The first use of the schema file. -/
def schema := sql_file "sql/schema.sql"
/-- A second declaration that uses the same file. -/
def sameFile := sql_file "sql/schema.sql"
sql_module Named from "sql/named.sql"
'''
"""A module with two declarations that use one file, and a module that uses another file."""

PROBE = '''import Lean
import SqlRecords.Queries
import Belay.Sqlite.SqlSourceRecord
import Belay.Sqlite.SqlCheckReport
open Belay.Sqlite Lean Elab Command

/-- The text of each file with `\n` line ends, as Lake would hash it. -/
def expectedText : String → String
  | "sql/schema.sql" => "SELECT 1;\nSELECT 2;\n"
  | "sql/named.sql" => "-- name: q\nSELECT 3;\n"
  | _ => ""

elab "check_imported_records" : command => do
  let env ← getEnv
  let some index := env.getModuleIdx? `SqlRecords.Queries | throwError "the Queries module is not imported"
  let uses := sqlSourceUseExtension.getModuleEntries env index
  let names := uses.toList.map (·.declaration)
  unless uses.all (fun use => use.package == "SqlRecords") do throwError "wrong package in {repr uses}"
  unless uses.all (fun use => use.hash == sqlTextHash (expectedText use.path)) do
    throwError "wrong hash in {repr uses}"
  for expected in [some `schema, some `sameFile, some `Named.q] do
    unless names.contains expected do throwError "no record for {expected} in {repr uses}"
  unless (uses.filter fun use => use.path == "sql/schema.sql").size >= 2 do throwError "uses were merged: {repr uses}"
  let resolved := uses.map fun use => ({ use, file := use.path, shown := use.path : ResolvedUse }, some use.hash)
  unless (groupSources resolved).size == 2 do
    throwError "sources were counted per declaration: {repr uses}"
  logInfo "imported records passed"

check_imported_records
'''


def test_pure_record_checks(runtime_root: Path, tmp_path: Path) -> None:
    """`sqlTextHash` and `dedupeSqlSourceUses` (`SqlSourceRecord.lean`), and `groupSources` (`SqlCheckReport.lean`), over small values."""
    result = run_command(surface_command(runtime_root, FIXTURES / "SqlSourceRecordChecks.lean", tmp_path),
                         cwd=tmp_path, timeout=60)
    assert result.returncode == 0, result.diagnostic()


def test_records_survive_an_import(runtime_root: Path, tmp_path: Path) -> None:
    """`loadSqlFileSource` and `defineEntry` (`SqlFileLoad.lean`, `SqlModule.lean`) add `SqlSourceUse` records to the
    extension of `SqlSourceRecord.lean`; a module that imports the compiled one sees one record per use, with the
    package, the relative path and the line-ending-normalized hash, and the same source counted once."""
    installed = installed_layout(runtime_root, tmp_path)
    package = tmp_path / "records"
    write_package(package, "SqlRecords", installed)
    texts = {"sql/schema.sql": "SELECT 1;\r\nSELECT 2;\r\n", "sql/named.sql": "-- name: q\nSELECT 3;\n"}
    for path, text in texts.items():
        (package / path).write_bytes(text.encode())
    (package / "lean/SqlRecords").mkdir()
    (package / "lean/SqlRecords/Queries.lean").write_text(QUERIES)
    (package / "lean/SqlRecords.lean").write_text("import SqlRecords.Queries\n")
    (package / "lean/SqlRecords/Probe.lean").write_text(PROBE)
    result = lake_build(installed, package, "SqlRecords.Queries")
    assert result.returncode == 0, result.diagnostic()
    result = lake_build(installed, package, "SqlRecords.Probe")
    assert result.returncode == 0, result.diagnostic()
    assert "imported records passed" in result.stdout, result.diagnostic()
