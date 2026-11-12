"""The shared SQL checking operation: original-claim certificates, cleanup and replay."""

import json
import shutil
from collections.abc import Callable
from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.surface_support import fixture_file, surface_command
from tests.surface_replay_test import model_cell, native_replay, native_rows

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_shared_search_certifies_and_restores_failed_attempts(runtime_root: Path, tmp_path: Path) -> None:
    """CheckCandidates rejects false proofs, CheckBudget restores state, and CheckReplayData's
    internal reifiers preserve ordinary imported Except display."""
    result = run_command(surface_command(runtime_root, fixture_file("CounterexampleSearchCore.lean"), tmp_path),
                         cwd=tmp_path, timeout=90)
    assert result.returncode == 0, result.diagnostic()
    assert "shared checker certificates and rollback passed" in result.stdout, result.stdout
    assert "discard this" not in result.stdout, result.stdout
    assert "sorry" not in result.stdout, result.stdout


@pytest.mark.requires_native("sqlite3")
def test_shared_search_reuses_samples_and_original_replays(runtime_root: Path, tmp_path: Path,
        record_testsuite_property: Callable[[str, object], None]) -> None:
    """Check.check finds intended SQL data boundaries and keeps unavailable observations inconclusive."""
    result = run_command(surface_command(runtime_root, fixture_file("CounterexampleSearch.lean"), tmp_path),
                         cwd=tmp_path, timeout=240)
    assert result.returncode == 0, result.diagnostic()
    assert result.stdout.count(": certified; heartbeats=") == 9, result.stdout
    assert "shared SQL search and replay passed" in result.stdout, result.stdout
    record_testsuite_property("sql_search.case_costs", result.stdout)
    sqlite = shutil.which("sqlite3")
    assert sqlite is not None
    version = run_command([sqlite, "-version"], cwd=tmp_path, timeout=5)
    assert version.returncode == 0 and version.stdout.startswith("3.51.0 "), version.diagnostic()
    reports = [json.loads(line.removeprefix("SEARCH-REPLAY:"))
               for line in result.stdout.splitlines() if line.startswith("SEARCH-REPLAY:")]
    assert len(reports) == 9, reports
    for report in reports:
        name = report["name"].removeprefix("SearchFixture.")
        replay = native_replay(sqlite, report["sql"], tmp_path, name)
        if name in ("missing", "success", "overflow"):
            expected = "integer overflow" if name == "overflow" else "no such table"
            assert report["outputs"] == [{"error": 1}], report
            assert replay.returncode != 0 and expected in replay.stderr, replay.diagnostic()
        else:
            assert replay.returncode == 0 and not replay.stderr, replay.diagnostic()
            rows = [[model_cell(cell) for cell in row]
                    for output in report["outputs"] for row in output["rows"]]
            assert native_rows(replay.stdout) == rows, (name, replay.stdout, rows)
    assert "sorry" not in result.stdout, result.stdout


def test_shared_search_bounds_compiled_data(runtime_root: Path, tmp_path: Path,
        record_testsuite_property: Callable[[str, object], None]) -> None:
    """CheckData computes data with compiled code under the time limit and cancellation, refuses
    compiled overrides and opaque constants, and retains logical data and reconstruction errors."""
    result = run_command(surface_command(runtime_root, fixture_file("CounterexampleSearchBudget.lean"), tmp_path),
                         cwd=tmp_path, timeout=90)
    assert result.returncode == 0, result.diagnostic()
    assert "bounded data, original definitions, bytes and construction passed" in result.stdout, result.stdout
    record_testsuite_property("sql_search.resource_stop", result.stdout)
    assert "discard this" not in result.stdout, result.stdout
    assert "sorry" not in result.stdout, result.stdout


def test_candidates_fill_touched_tables_with_constrained_rows(runtime_root: Path, tmp_path: Path) -> None:
    """SampleTouched and SampleConstraints: the search fills only the tables that the claim's
    statements touch through triggers and foreign keys, and its rows satisfy NOT NULL, UNIQUE
    and foreign keys by construction."""
    result = run_command(surface_command(runtime_root, fixture_file("CandidateConstraints.lean"), tmp_path),
                         cwd=tmp_path, timeout=90)
    assert result.returncode == 0, result.diagnostic()
    assert "candidate constraints passed" in result.stdout, result.stdout


def test_search_screens_while_generating_with_a_share_per_value(runtime_root: Path, tmp_path: Path) -> None:
    """CheckSamples.visitCandidates and Sampling.candidates: the search stops generating at the
    first candidate that the screen accepts, continues after a rejected certificate, screens the
    last candidate within the time limit, and gives each parameter value a share of the
    candidate count, so that NULL does not use the count of the value 1."""
    result = run_command(surface_command(runtime_root, fixture_file("CandidateShares.lean"), tmp_path),
                         cwd=tmp_path, timeout=90)
    assert result.returncode == 0, result.diagnostic()
    assert "candidate shares passed" in result.stdout, result.stdout
