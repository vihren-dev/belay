"""`prepare` and `verify-bundle` reuse Lake's artifact cache and compile only changed modules (ADR 0010)."""

from collections.abc import Callable
from pathlib import Path

import pytest

from migration_check.project_config import load
from tests.bundle_test import data_path, small  # noqa: F401  (fixtures)
from tests.runtime_support import CommandResult

pytestmark = [pytest.mark.e2e, pytest.mark.kernel, pytest.mark.requires_lean, pytest.mark.requires_native]


def test_verify_bundle_reuses_its_lake_cache(data_path: Callable[..., dict[str, object]], small: dict[str, Path],
                                             tmp_path: Path) -> None:
    """`verify-bundle` builds the contract with Lake (ADR 0010): the first run compiles the approved modules and
    `SchemaInputs`; a second run with the same cache, in a new directory, compiles nothing and gives the same
    status."""
    cold = tmp_path / "cold-cache"  # its own cache: a seeded suite cache would already hold the contract
    first = data_path(approved=small["approved"], candidate=small["candidate"], schema=small["schema"],
                      directory=tmp_path / "first", cache=cold)
    second = data_path(approved=small["approved"], candidate=small["candidate"], schema=small["schema"],
                       directory=tmp_path / "second", cache=cold)
    assert first["status"] == second["status"] == "VERIFIED", (first, second)
    assert set(first["compiled_modules"]) == {"Requirements", "Interpretation", "SchemaInputs"}, first
    assert second["compiled_modules"] == [], second


def test_sql_edit_reuses_modules_without_sql_inputs(runtime_root: Path, example_factory: Callable[[str], Path],
                                                     tmp_path: Path, command_runner: Callable[..., CommandResult]) -> None:
    """After an Atuin SQL edit, modules that do not import SqlInputs are reused and the bundle verifies."""
    atuin = example_factory("atuin")
    launcher = str(runtime_root / "bin/migration-check")
    config = load(atuin / "belay.toml", atuin)
    common = ["--format", "json", *config.contract_arguments()]
    bundle = tmp_path / "atuin.bundle"

    def prepare() -> dict[str, object]:
        """Prepare the same proofs project (the checked-in Atuin case) with the same cache."""
        result = command_runner([launcher, "prepare", *common, "--project", str(config.proofs),
                                 "--cache", str(tmp_path / "cold-cache"),
                                 "--output", str(bundle)], cwd=tmp_path, timeout=180)
        report = result.json_object()
        assert report["status"] == "PREPARED", result.diagnostic()
        return report

    first = prepare()
    for path, old, new in ((atuin / "migration.sql", "add column shell text;", "add column other text;"),
                           (atuin / "AtuinFacts.lean", 'name := "shell"', 'name := "other"')):
        text = path.read_text()
        assert old in text
        path.write_text(text.replace(old, new))
    second = prepare()
    unchanged = {"AtuinWitness", "HistoryDecodingChecks", "SchemaInputs", *(path.stem for path in config.contract.glob("*.lean"))}
    assert unchanged <= set(first["compiled_modules"]), first
    assert not unchanged & set(second["compiled_modules"]), second
    assert {"SqlInputs", "AtuinFacts", "Proofs"} <= set(second["compiled_modules"]), second
    checked = command_runner([launcher, "verify-bundle", *common, "--bundle", str(bundle)], cwd=tmp_path, timeout=120)
    assert checked.json_object()["status"] == "VERIFIED", checked.diagnostic()

