"""Checked-in cases compile nothing when a Nix target seeded its cache (ADR 0010 section 8).

The seeds (`build-support/case-seeds.nix`) hold every case's outputs, so CI compiles
each checked-in case once, in its seed, and not again in every test.
"""

from collections.abc import Callable
import os
from pathlib import Path

import pytest

from migration_check.project_config import discover, load
from tests.runtime_support import CommandResult

pytestmark = [pytest.mark.e2e, pytest.mark.requires_lean, pytest.mark.requires_native,
              pytest.mark.skipif(not os.environ.get("BELAY_TEST_SEEDED"),
                                 reason="runs in a Nix target whose cache the case seeds filled")]


def pytest_generate_tests(metafunc: pytest.Metafunc) -> None:
    """One run for each checked-in case of the runtime under test."""
    if "case_name" in metafunc.fixturenames:
        examples = (metafunc.config.getoption("runtime_root") or metafunc.config.rootpath) / "examples"
        metafunc.parametrize("case_name", [path.parent.relative_to(examples).as_posix() for path in discover(examples)])


def test_unchanged_case_compiles_nothing(case_name: str, runtime_root: Path, tmp_path: Path,
                                         example_factory: Callable[[str], Path],
                                         command_runner: Callable[..., CommandResult]) -> None:
    """`prepare` and `verify-bundle` on an unchanged case take every module from the seeded cache."""
    examples = example_factory(".")
    case = load(examples / case_name / "belay.toml", examples)
    launcher, bundle = str(runtime_root / "bin/migration-check"), tmp_path / "proof.bundle"
    for command in (["prepare", *case.contract_arguments(), "--project", str(case.proofs), "--output", str(bundle)],
                    ["verify-bundle", *case.contract_arguments(), "--bundle", str(bundle)]):
        report = command_runner([launcher, *command, "--format", "json"], cwd=tmp_path, timeout=180).json_object()
        assert report["status"] in ("PREPARED", case.test_status), report
        assert report["compiled_modules"] == [], report
