"""The explicit SQL command and searched tactic use certified checking and replay."""

import re
import shutil
from textwrap import indent
from collections.abc import Callable
from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.surface_replay_test import native_replay, native_rows
from tests.surface_support import FIXTURES, surface_command

FORBIDDEN_DEPENDENCIES: tuple[str, ...] = ("sorryAx", "ofReduceBool", "ofReduceNat", "trustCompiler", "_native")
"""Admission and native-computation dependencies forbidden in the exported theorem audits."""

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


@pytest.mark.requires_native("sqlite3")
def test_sql_check_reports_checked_outcomes(runtime_root: Path, tmp_path: Path,
        record_testsuite_property: Callable[[str, object], None]) -> None:
    """SqlCheckCommand covers all outcomes with default inference, original data premises,
    explicit inputs and native replay; its printed proof checks against the original claim."""
    result = run_command(surface_command(runtime_root, FIXTURES / "CounterexampleCheckCommand.lean", tmp_path),
                         cwd=tmp_path, timeout=240)
    assert result.returncode == 0, result.diagnostic()
    blocks = dict(re.findall(r"SQL-COMMAND-BEGIN ([\w-]+)\n(.*?)\nSQL-COMMAND-END \1:",
                             result.stdout, re.DOTALL))
    false_cases = {"missing", "nonempty", "fails", "success", "parameter", "plain", "ordered",
                   "nocase", "nonascii", "overflow"}
    assert set(blocks) == false_cases | {"proof", "disabled", "no-candidates", "low-depth",
                                         "unavailable", "after-limits"}, result.stdout
    for name in false_cases:
        assert blocks[name].startswith("SQL check: false."), (name, blocks[name])
        assert "Database:" in blocks[name] and "Environment:" in blocks[name], blocks[name]
    for name in ("disabled", "no-candidates", "low-depth", "unavailable"):
        assert blocks[name].startswith("SQL check: unknown;"), (name, blocks[name])
    for name in ("proof", "after-limits"):
        assert blocks[name].startswith("SQL check: proved."), (name, blocks[name])
    costs = re.findall(r"SQL-COMMAND-END .*", result.stdout)
    record_testsuite_property("sql_check.frontend_costs", "\n".join(costs))
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    version = run_command([sqlite, "-version"], cwd=tmp_path, timeout=5)
    assert version.returncode == 0 and version.stdout.startswith("3.51.0 "), version.diagnostic()
    expected_rows = {"nonempty": [[1]], "fails": [[1]], "parameter": [["'"]], "plain": [],
                     "ordered": [[7]], "nocase": [[1]], "nonascii": []}
    for name in sorted(false_cases):
        sql = blocks[name].split("SQLite replay:\n", 1)[1]
        replay = native_replay(sqlite, sql, tmp_path, name)
        if name in ("missing", "success", "overflow"):
            error = "integer overflow" if name == "overflow" else "no such table"
            assert replay.returncode != 0 and error in replay.stderr, replay.diagnostic()
        else:
            assert replay.returncode == 0 and not replay.stderr, replay.diagnostic()
            assert native_rows(replay.stdout) == expected_rows[name], (name, replay.diagnostic())
    assert "Bindings:" not in blocks["plain"] and "Model outputs:" not in blocks["plain"]
    proof = blocks["proof"].split("Checked proof: by ", 1)[1]
    copied = tmp_path / "CopiedProof.lean"
    copied.write_text("import Belay\nopen Belay.Sqlite\n"
                      f"theorem copied (kernel : Nat) : ∀ db : Database, kernel = kernel ∧ db = db := by\n"
                      f"{indent(proof, '  ')}\n#print axioms copied\n")
    checked = run_command(surface_command(runtime_root, copied, tmp_path), cwd=tmp_path, timeout=30)
    assert checked.returncode == 0, checked.diagnostic()
    assert all(name not in checked.stdout for name in FORBIDDEN_DEPENDENCIES), checked.stdout


def test_sql_refute_search_and_explicit_modes(runtime_root: Path, tmp_path: Path) -> None:
    """SqlRefuteSearch preserves explicit witnesses, custom candidates, failed goals and the
    command cancellation context; all resulting theorem dependencies remain kernel-safe."""
    result = run_command(surface_command(runtime_root, FIXTURES / "CounterexampleCheckTactic.lean", tmp_path),
                         cwd=tmp_path, timeout=180)
    assert result.returncode == 0, result.diagnostic()
    assert "custom candidates certify the original plain predicate" in result.stdout, result.stdout
    assert "frontend command cancellation propagated" in result.stdout, result.stdout
    for forbidden in FORBIDDEN_DEPENDENCIES:
        assert forbidden not in result.stdout, result.stdout
    assert result.stdout.count("depends on axioms") + result.stdout.count("does not depend on any axioms") == 9


@pytest.mark.parametrize(("inputs", "diagnostic"), [
    ("(db := 7)", "Database"),
    ("(schema := 7)", "Database"),
    ("(env := 7)", "Env"),
    ("(schema := Database.empty) (schema := Database.empty)", "supply only one SQL search schema"),
    ("(input n := 1) (input n := 2)", "supply only one value for this quantified input"),
    ("(bogus := Database.empty)", "expected schema, db or env"),
])
def test_sql_check_reports_input_errors_at_terms(runtime_root: Path, tmp_path: Path,
        inputs: str, diagnostic: str) -> None:
    """CheckInputs rejects malformed/ill-typed explicit terms before a proved result can hide them."""
    source = tmp_path / "BadInputs.lean"
    source.write_text(f"import Belay\nopen Belay.Sqlite\n#sql_check True with {inputs}\n")
    result = run_command(surface_command(runtime_root, source, tmp_path), cwd=tmp_path, timeout=30)
    assert result.returncode != 0, result.diagnostic()
    assert "BadInputs.lean:3:" in result.stdout and diagnostic in result.stdout, result.diagnostic()
    assert "SQL check: proved" not in result.stdout and "SQL check: false" not in result.stdout


@pytest.mark.requires_native("sqlite3")
def test_sql_check_sampling_options(runtime_root: Path, tmp_path: Path) -> None:
    """CheckOptions changes seeded search, row/sample limits and checked shrinking;
    configured size reaches a real size-sensitive custom generator."""
    result = run_command(surface_command(runtime_root, FIXTURES / "CounterexampleCheckOptions.lean", tmp_path),
                         cwd=tmp_path, timeout=240)
    assert result.returncode == 0, result.diagnostic()
    blocks = dict(re.findall(r"OPTION-BEGIN ([\w-]+)\n(.*?)\nOPTION-END \1", result.stdout, re.DOTALL))
    expected_rows = {"seed-13": [[-1]], "two-random": [[-1]],
                     "no-shrink": [[7]], "two-shrinks": [[None]]}
    unknown = {"seed-0", "no-random", "one-random", "no-rows"}
    assert set(blocks) == expected_rows.keys() | unknown, result.stdout
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    for name, rows in expected_rows.items():
        assert blocks[name].startswith("SQL check: false."), (name, blocks[name])
        sql = blocks[name].split("SQLite replay:\n", 1)[1] + "\nSELECT a FROM t;\n"
        replay = native_replay(sqlite, sql, tmp_path, name)
        assert replay.returncode == 0 and not replay.stderr, replay.diagnostic()
        assert native_rows(replay.stdout) == rows, (name, replay.diagnostic())
    for name in unknown:
        assert blocks[name].startswith("SQL check: unknown;"), (name, blocks[name])
    for size in (7, 9):
        assert f"sized candidate certified with row {size}" in result.stdout, result.stdout
