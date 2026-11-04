"""Evaluate the observability suite's actual Nix identity without starting ClickHouse."""

import json
from pathlib import Path
import shutil

import pytest

from tests.runtime_support import run_command

ROOT = Path(__file__).resolve().parents[1]
pytestmark = [pytest.mark.integration, pytest.mark.requires_nix, pytest.mark.timeout(60)]


def test_observability_inputs_are_narrow_and_complete(tmp_path: Path) -> None:
    """Uploader/schema/helper edits invalidate our cached check; unrelated model edits do not."""
    files = ["pytest.ini", "conftest.py", "tools/__init__.py", "tests/__init__.py",
             "tests/runtime_support.py", "tests/runtime_fixtures.py", "tests/nix_suites.json",
             "tests/nix_mutant_suites.json", "tests/observability_support.py",
             "tests/observability_clickhouse_test.py", "build-support/observability-schema.sql",
             "nix/pytest-reportlog.nix"]
    files += [str(path.relative_to(ROOT)) for path in (ROOT / "tools").glob("observability_*.py")]
    for name in files:
        target = tmp_path / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / name, target)

    def identity() -> str:
        """Evaluate only this test derivation through the production entrypoint."""
        literal = json.dumps(str(tmp_path)).replace("${", "\\${")
        expression = f'(import ./build-support/default.nix {{ root = /. + {literal}; }}).tests.observability.drvPath'
        result = run_command(["nix-instantiate", "--eval", "--strict", "--json", "--expr", expression,
                              "--extra-experimental-features", "nix-command flakes"], cwd=ROOT, timeout=15)
        assert result.returncode == 0, result.diagnostic()
        return result.stdout

    baseline = identity()
    model = tmp_path / "packages/belay-sqlite-model/Unrelated.lean"
    model.parent.mkdir(parents=True)
    model.write_text("-- unrelated model edit\n")
    assert identity() == baseline
    for name in ["tools/observability_upload.py", "build-support/observability-schema.sql",
                 "tests/observability_clickhouse_test.py", "tools/observability_spool.py"]:
        target = tmp_path / name
        original = target.read_bytes()
        target.write_bytes(original + b"\n")
        assert identity() != baseline, name
        target.write_bytes(original)
