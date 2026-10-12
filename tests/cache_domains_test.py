"""Lake caches across trust domains and against no cache (ADR 0010 sections 4 and 5).

`prepare` (the agent) and `verify-bundle` (the verifier) may use different caches;
the verifier's result must not depend on the agent's cache, and a warm cache must give
the same result as no cache for every checked-in case.
"""

from collections.abc import Callable
from pathlib import Path

import pytest

from migration_check.project_config import discover, load
from tests.runtime_support import CommandResult

pytestmark = [pytest.mark.e2e, pytest.mark.kernel, pytest.mark.requires_lean, pytest.mark.requires_native]


def pytest_generate_tests(metafunc: pytest.Metafunc) -> None:
    """One run of the equivalence test for each checked-in case, from the runtime under test."""
    if "case_name" in metafunc.fixturenames:
        examples = (metafunc.config.getoption("runtime_root") or metafunc.config.rootpath) / "examples"
        metafunc.parametrize("case_name", [path.parent.relative_to(examples).as_posix() for path in discover(examples)])


def run(runtime_root: Path, tmp_path: Path, command_runner: Callable[..., CommandResult],
        *arguments: str) -> dict[str, object]:
    """One command's JSON report."""
    result = command_runner([str(runtime_root / "bin/migration-check"), *arguments, "--format", "json"],
                            cwd=tmp_path, timeout=240)
    return result.json_object()


def test_warm_cache_equals_no_cache_and_ignores_the_agents_cache(
        case_name: str, runtime_root: Path, tmp_path: Path, example_factory: Callable[[str], Path],
        command_runner: Callable[..., CommandResult]) -> None:
    """`prepare` uses the agent's cache; `verify-bundle` then gives the case's status with its own empty cache
    (compiling the contract), again with that cache warm (compiling nothing), and with `--no-cache`."""
    examples = example_factory(".")
    case = load(examples / case_name / "belay.toml", examples)
    bundle = tmp_path / "proof.bundle"
    prepared = run(runtime_root, tmp_path, command_runner, "prepare", *case.contract_arguments(),
                   "--project", str(case.proofs), "--output", str(bundle), "--cache", str(tmp_path / "agent"))
    assert prepared["status"] == "PREPARED", prepared
    check = ["verify-bundle", *case.contract_arguments(), "--bundle", str(bundle)]
    verifier = ["--cache", str(tmp_path / "verifier")]
    cold = run(runtime_root, tmp_path, command_runner, *check, *verifier)
    warm = run(runtime_root, tmp_path, command_runner, *check, *verifier)
    fresh = run(runtime_root, tmp_path, command_runner, *check, "--no-cache")
    assert cold["status"] == warm["status"] == fresh["status"] == case.test_status, (cold, warm, fresh)
    if case.test_status == "VERIFIED":
        assert cold["compiled_modules"] and warm["compiled_modules"] == [], (cold, warm)
