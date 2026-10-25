"""Migration examples compare complete public executions with pinned SQLite."""

import json
from pathlib import Path
import re
import shutil

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler"),
              pytest.mark.requires_native("sqlite3")]


def counter_cell(cell: object) -> str | int:
    """Decode the integer/text cells used by the checked customer example."""
    assert isinstance(cell, dict), cell
    if "integer" in cell:
        value = cell["integer"]
        assert isinstance(value, dict) and isinstance(value.get("value"), int), cell
        return value["value"]
    value = cell["text"]
    assert isinstance(value, dict) and isinstance(value.get("bytes"), list), cell
    return bytes(value["bytes"]).decode("utf-8")


def test_expansion_counter_refutes_full_commutation(runtime_root: Path, tmp_path: Path) -> None:
    """The complete expansion has equal final rows/application observations in both
    public execution orders, but its maintenance trigger changes total_changes.
    Kernel proofs establish original success and refute full commutation; native
    SQLite runs the fixture's retained SQL and independently checks both totals."""
    result = run_command(surface_command(runtime_root, FIXTURES / "MigrationExpansionCounter.lean", tmp_path),
                         cwd=tmp_path, timeout=180)
    assert result.returncode == 0, result.diagnostic()
    reports = re.findall(r"(?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
    assert len(reports) == 7, result.diagnostic()
    for report in reports:
        assert set(filter(None, map(str.strip, report.split(",")))) <= {
            "propext", "Classical.choice", "Quot.sound"}, result.diagnostic()
    lines = [line.removeprefix("MIGRATION-COUNTER:") for line in result.stdout.splitlines()
             if line.startswith("MIGRATION-COUNTER:")]
    assert len(lines) == 1, result.diagnostic()
    evidence = json.loads(lines[0])
    assert evidence["migration"].count("CREATE TRIGGER") == 2, evidence
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    version = run_command([sqlite, "-version"], cwd=tmp_path, timeout=5)
    assert version.returncode == 0 and version.stdout.startswith("3.51.0 "), version.diagnostic()
    for order, segments in (("before", ("application", "migration")),
                            ("after", ("migration", "application"))):
        sql = ";\n".join(evidence[name] for name in ("setup", *segments)) + ";\n"
        sql += ("SELECT id,name,email,email_lower,total_changes() AS total,"
                "changes() AS changed,last_insert_rowid() AS last_id FROM customers;\n")
        script = tmp_path / f"{order}.sql"
        script.write_text(sql)
        native = run_command([sqlite, "-batch", "-bail", "-json", ":memory:", f'.read "{script}"'],
                             cwd=tmp_path, timeout=10)
        assert native.returncode == 0 and not native.stderr, native.diagnostic()
        rows = json.loads(native.stdout)
        model = evidence[order]
        assert len(rows) == len(model["rows"]) == 1, (order, rows, model)
        row = rows[0]
        assert [row[name] for name in ("id", "name", "email", "email_lower")] == [
            counter_cell(cell) for cell in model["rows"][0]], (order, rows, model)
        assert {name: row[name] for name in ("total", "changed", "last_id")} == {
            name: model[name] for name in ("total", "changed", "last_id")}, (order, rows, model)
    assert evidence["before"]["total"] == 3 and evidence["after"]["total"] == 4, evidence
