"""Host collection preserves source checks and excludes every delegated Nix suite."""

import json
from pathlib import Path
import subprocess
import sys

import pytest

from tools.ci_checks import SCOPE_RECIPES

ROOT = Path(__file__).resolve().parents[1]
pytestmark = [pytest.mark.unit, pytest.mark.environment]


def test_host_collection_retains_source_owned_conformance_checks() -> None:
    """Use actual pytest discovery so the shared ownership list cannot silently lose host tests."""
    result = subprocess.run([sys.executable, "-m", "pytest", "--collect-only", "-q", "tests",
                             "--source-checks", "-m", "not requires_nix"],
                            cwd=ROOT, capture_output=True, text=True, timeout=30)
    assert result.returncode == 0, result.stdout + result.stderr
    collected = {line.split("::")[0] for line in result.stdout.splitlines() if "::" in line}
    suites = json.loads((ROOT / "tests/nix_suites.json").read_text())
    delegated = {name for files in suites.values() for name in files}
    assert not collected & delegated
    assert "tests/runtime_package_test.py" not in collected
    assert {"tests/conformance_axioms_test.py", "tests/conformance_native_test.py",
            "tests/test_ci_checks.py", "tests/test_test_ownership.py"} <= collected
    assert all((ROOT / name).is_file() for name in delegated)


def test_each_delegated_file_belongs_to_one_suite() -> None:
    """Every mutant file has one scheduled owner; duplicate owners rerun the same tests."""
    suites = json.loads((ROOT / "tests/nix_suites.json").read_text())
    owners: dict[str, list[str]] = {}
    for suite, files in suites.items():
        for name in files:
            owners.setdefault(name, []).append(suite)
    shared = {name: names for name, names in owners.items() if len(names) > 1}
    assert not shared, f"Test files listed in more than one Nix suite: {shared}"
    mutants = json.loads((ROOT / "tests/nix_mutant_suites.json").read_text())
    assert {file for suite in mutants for file in suites[suite]} == {
        str(path.relative_to(ROOT)) for path in (ROOT / "tests").glob("conformance_*mutants_test.py")}


@pytest.mark.requires_native("just")
def test_recipe_expansion_retains_full_model_in_ci_checks() -> None:
    """Actual just dependencies select the sample for development and the full set for CI."""
    for recipe, target in (("test", "developmentTestReports"), ("test-full", "testReports")):
        result = subprocess.run(["just", "--dry-run", recipe], cwd=ROOT,
                                capture_output=True, text=True, timeout=5)
        assert result.returncode == 0, result.stdout + result.stderr
        commands = result.stdout + result.stderr
        assert f"-A {target} --out-link build/nix-tests" in commands
        if recipe != "test":
            assert "-A developmentTestReports" not in commands


def test_scheduled_suites_run_only_in_the_full_scope() -> None:
    """A scheduled suite (`tests/nix_scheduled_suites.json`) is an owned Nix suite, the pull
    request recipes build only `tests`, which excludes it, and the CI scope `full`
    (`tools/ci_checks.py`), which main pushes and scheduled runs use, builds it through
    `test-scheduled-checks`, except the mutant suites (`tests/nix_mutant_suites.json`), which the
    CI job `mutants` builds one at a time through `test-mutants`."""
    suites = json.loads((ROOT / "tests/nix_suites.json").read_text())
    scheduled = json.loads((ROOT / "tests/nix_scheduled_suites.json").read_text())
    assert scheduled and set(scheduled) <= set(suites)
    recipes = (ROOT / "justfile").read_text()
    mutants = json.loads((ROOT / "tests/nix_mutant_suites.json").read_text())
    assert mutants and set(mutants) < set(scheduled)
    assert SCOPE_RECIPES["full"] == ["test-full", "test-nix", "test-scheduled-checks"]
    assert "\ntest-scheduled-checks:\n" in recipes
    assert "-A scheduledCheckReports " in recipes and "-A testReports " in recipes
    assert '-A "scheduledTests.{{suite}}" ' in recipes
    assert "(pkgs.lib.removeAttrs scheduledTests mutantSuites);" in (ROOT / "build-support/default.nix").read_text()
    default = (ROOT / "build-support/default.nix").read_text()
    assert "tests = pkgs.lib.removeAttrs allTests scheduledSuites;" in default
