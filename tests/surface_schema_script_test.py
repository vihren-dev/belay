"""The step, frame and success laws of the schema, transaction and pragma statements (ADR 0017, S6)."""

from pathlib import Path
import re
import shutil

import pytest

from tests.runtime_support import run_command
from tests.surface_assertion_examples_test import check_module_chain, lines_after
from tests.surface_replay_test import model_cell, native_replay, native_rows

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler"),
              pytest.mark.requires_native("sqlite3")]

EXPECTED_ROWS: dict[str, list[list[object]]] = {
    "drop-off": [[10, 1, "a"], [11, 2, "b"], [12, 2, "c"]],
    "drop-on": [],
    "refusals": [[0], [1], [3]],
    "inserts": [[1, "a"], [2, "b"]],
}
"""The rows that the model gives for each replay, which pinned SQLite must give too."""

EXPECTED_ERRORS: dict[str, list[str]] = {
    "drop-off": [],
    "drop-on": [],
    "refusals": ["already exists", "no such table", "no transaction is active",
                 "cannot start a transaction within a transaction"],
    "inserts": ["NOT NULL constraint failed", "UNIQUE constraint failed", "CHECK constraint failed",
                "cannot store TEXT value in INTEGER column"],
}
"""The refusal that pinned SQLite gives for each error output of the model, in order."""


def test_schema_laws_on_concrete_databases_agree_with_pinned_sqlite(runtime_root: Path, tmp_path: Path) -> None:
    """The fixtures SchemaStepLaws, ControlStepExamples, CertificateAfterDrop and InsertSelectExamples apply the
    step, frame and success laws of CREATE TABLE, DROP TABLE, BEGIN, COMMIT, the pragmas foreign_keys and
    foreign_key_check, and INSERT from a query to concrete databases. They include DROP TABLE with foreign keys on
    whose cascade changes the observed table, a read certificate that survives the drop of an earlier table, and
    a failing case for each premise of the success law of INSERT from a query. Every theorem uses only logical
    axioms. The fixture SchemaScriptReplays emits scripts of the same statements. Pinned SQLite 3.51.0 gives the
    rows that the model gives, and refuses the statements that the model refuses, in the same order."""
    stdout = check_module_chain(runtime_root, tmp_path, (
        ("SchemaStepLaws", 7), ("ControlStepExamples", 7), ("CertificateAfterDrop", 2),
        ("InsertSelectExamples", 6), ("SchemaScriptReplays", 0)))
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    version = run_command([sqlite, "-version"], cwd=tmp_path, timeout=5)
    assert version.returncode == 0 and version.stdout.startswith("3.51.0 "), version.diagnostic()
    reports = {str(report["name"]): report for report in lines_after(stdout, "REPLAY:") if isinstance(report, dict)}
    assert set(reports) == set(EXPECTED_ROWS), stdout
    for name, report in reports.items():
        result = native_replay(sqlite, report["sql"], tmp_path, name)
        outputs = report["outputs"]
        assert isinstance(outputs, list)
        modeled = [[model_cell(cell) for cell in row] for output in outputs for row in output.get("rows", [])]
        assert native_rows(result.stdout) == modeled == EXPECTED_ROWS[name], (name, result.stdout, modeled)
        refusals = re.findall(r"error near line \d+: (.*)", result.stderr)
        modeled_errors = [output for output in outputs if "error" in output]
        assert len(refusals) == len(modeled_errors) == len(EXPECTED_ERRORS[name]), (name, result.stderr)
        for line, expected in zip(refusals, EXPECTED_ERRORS[name], strict=True):
            assert expected in line, (name, line, expected)
