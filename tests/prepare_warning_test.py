"""`prepare` warns about approved code that runs during elaboration and still prepares (ADR 0010, "Decisions").

Cached contract outputs are reused within a trust domain; code that runs while Lean
elaborates a contract module can make a cached output differ from a fresh one, so
the contract's reviewer should see it.
"""

from collections.abc import Callable
from pathlib import Path

import pytest

from migration_check.project_config import load
from tests.runtime_support import CommandResult

pytestmark = [pytest.mark.e2e, pytest.mark.requires_lean, pytest.mark.requires_native]


@pytest.mark.parametrize("added,warned", [("", False), ("\n#eval (1 : Nat)\n", True)], ids=["plain", "eval"])
def test_prepare_warns_about_elaboration_commands(added: str, warned: bool, runtime_root: Path, tmp_path: Path,
        example_factory: Callable[[str], Path], command_runner: Callable[..., CommandResult]) -> None:
    """With `#eval` added to the approved requirements, `prepare` reports it with its module and line and still
    writes the bundle; the unchanged contract gives no warning."""
    examples = example_factory(".")
    config = load(examples / "add_column_then_table/belay.toml", examples)
    with config.requirements.open("a") as stream:
        stream.write(added)
    result = command_runner([str(runtime_root / "bin/migration-check"), "prepare", "--format", "json",
                             *config.contract_arguments(), "--project", str(config.proofs),
                             "--output", str(tmp_path / "proof.bundle")], cwd=tmp_path, timeout=180)
    report = result.json_object()
    assert report["status"] == "PREPARED", result.diagnostic()
    assert [warning for warning in report["warnings"] if "Requirements:" in warning and "#eval" in warning] == (
        report["warnings"] if warned else []), report
    assert bool(report["warnings"]) == warned, report
