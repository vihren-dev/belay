"""Compare Belay's plain UPDATE with pinned SQLite on intermediate unique keys."""

from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.surface_support import surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler"),
              pytest.mark.requires_native("sqlite3"), pytest.mark.timeout(90)]


def test_update_checks_old_and_new_unique_keys(runtime_root: Path, tmp_path: Path) -> None:
    """Database.run refuses an order-dependent success and admits a write whose keys remain distinct."""
    examples = [
        ("CREATE TABLE ex(a INTEGER, b INTEGER); CREATE UNIQUE INDEX expr ON ex(a + b); "
         "INSERT INTO ex VALUES (3,9),(1,2);", "UPDATE ex SET b = 0;", "index 'expr'"),
        ("CREATE TABLE pi(a,b,c); CREATE UNIQUE INDEX partial ON pi(a) WHERE b > c; "
         "INSERT INTO pi VALUES (1,10,20),(1,3,0);", "UPDATE pi SET c = 5;", "pi.a"),
        ("CREATE TABLE ex(a,b); CREATE UNIQUE INDEX expr ON ex(a + b); "
         "INSERT INTO ex VALUES (3,0),(1,8);", "UPDATE ex SET b = 0;", None),
    ]
    fixture = ["import Belay", "open Belay.Sqlite"]
    for setup, update, constraint in examples:
        native = run_command(["sqlite3", "-batch", "-bail", ":memory:", setup + update], cwd=tmp_path, timeout=5)
        if constraint is None:
            assert native.returncode == 0, native.diagnostic()
            expected = "outputs == [.done 2]"
        else:
            assert native.returncode != 0 and f"UNIQUE constraint failed: {constraint}" in native.stderr, native.diagnostic()
            expected = "outputs matches [.unmodeled _]"
        fixture.append(f'#guard ((db! r"{setup}").run (sql r"{update}")).{expected}')
    source = tmp_path / "TransientKeys.lean"
    source.write_text("\n".join(fixture), encoding="utf-8")
    result = run_command(surface_command(runtime_root, source, tmp_path), cwd=tmp_path, timeout=60)
    assert result.returncode == 0, result.diagnostic()
