"""A table rebuild that changes the declared type of a column changes stored values (ADR 0017, S6)."""

from pathlib import Path
import shutil

import pytest

from tests.runtime_support import run_command
from tests.surface_assertion_examples_test import check_module_chain, lines_after
from tests.surface_replay_test import model_cell, native_replay, native_rows

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler"),
              pytest.mark.requires_native("sqlite3")]


def test_type_change_rebuild_loses_the_text_of_a_number(runtime_root: Path, tmp_path: Path) -> None:
    """Fixture RebuildAffinity checks the rebuild of a TEXT column into an INTEGER column against model execution
    and pinned SQLite. The kernel proves that the rebuild succeeds, that '01234' becomes the integer 1234, that
    'n/a' stays text, that the rebuild does not preserve the query of both columns, and that a STRICT table
    refuses the copy. Native SQLite 3.51.0 gives the rows that the kernel gives for the three runs, and its
    error text for the STRICT copy names the column. Every theorem uses only logical axioms."""
    stdout = check_module_chain(runtime_root, tmp_path, (("RebuildAffinity", 7),))
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    version = run_command([sqlite, "-version"], cwd=tmp_path, timeout=5)
    assert version.returncode == 0 and version.stdout.startswith("3.51.0 "), version.diagnostic()
    reports = {str(report["name"]): report for report in lines_after(stdout, "REPLAY:") if isinstance(report, dict)}
    assert set(reports) == {"zip-before", "zip-after", "strict-copy"}, stdout
    expected_rows = {"zip-before": [[1, "01234"], [2, "n/a"]], "zip-after": [[1, 1234], [2, "n/a"]],
                     "strict-copy": [[0]]}
    for name, report in reports.items():
        result = native_replay(sqlite, report["sql"], tmp_path, name)
        outputs = report["outputs"]
        assert isinstance(outputs, list)
        modeled = [[model_cell(cell) for cell in row] for output in outputs for row in output.get("rows", [])]
        assert native_rows(result.stdout) == modeled == expected_rows[name], (name, result.stdout, modeled)
        if name == "strict-copy":
            assert [output.get("error") for output in outputs] == [None, 19, None], outputs
            assert "cannot store TEXT value in INTEGER column addresses_new.zip" in result.stderr, result.diagnostic()
        else:
            assert result.returncode == 0 and not result.stderr, result.diagnostic()
