"""Check that the justfile's Nix builds can be stopped by a caller and that their limits nest.

A CI phase (tools/ci_checks.py) kills the process group of its command at its deadline
(tests/runtime_support.py). Each Nix test suite has its own limit (build-support/tests.nix),
so a suite that hangs outside a test fails with its own name, but only if that limit ends
before the limit of the recipe that builds the suite.
"""

import json
from pathlib import Path
import re
import shlex
import sys

import pytest

from tests import dev_loop_test as loop
from tests.runtime_support import run_command
from tools.ci_checks import CHECKS_PHASE_LIMIT_SECONDS

ROOT = Path(__file__).resolve().parents[1]
OTHER_HOST_TESTS_SECONDS = 600
"""Time reserved for Nix identity, target and environment tests after the local dev loop."""

SUITE_TARGETS = {"developmentTestReports", "testReports", "scheduledTestReports", "scheduledCheckReports",
                 "scheduledTests.{{suite}}"}
"""The `nix-build -A` targets of build-support/default.nix that build test suites."""


def development_exclusions() -> set[str]:
    """The suites that `developmentTests` of build-support/default.nix leaves out."""
    default = (ROOT / "build-support/default.nix").read_text()
    match = re.search(r"developmentTests = pkgs\.lib\.removeAttrs tests \[([^]]*)\];", default)
    assert match is not None, "build-support/default.nix has no developmentTests"
    return set(re.findall(r'"([^"]+)"', match.group(1)))


def built_suites(target: str, suites: set[str], scheduled: set[str], mutants: set[str]) -> set[str]:
    """The suites that a `nix-build -A` target of the justfile builds: `testReports` the suites
    that are not scheduled, `developmentTestReports` those without the suites that `just test`
    skips (`development_exclusions`), `scheduledTestReports` every scheduled suite,
    `scheduledCheckReports` the scheduled suites but the mutant suites, and `scheduledTests.{{suite}}`
    one mutant suite."""
    if target == "testReports":
        return suites - scheduled
    if target == "developmentTestReports":
        return suites - scheduled - development_exclusions()
    if target == "scheduledTestReports":
        return scheduled
    if target == "scheduledCheckReports":
        return scheduled - mutants
    assert target == "scheduledTests.{{suite}}", target
    return mutants

pytestmark = [pytest.mark.unit, pytest.mark.environment]


def nix_build_recipe_lines() -> list[list[str]]:
    """The words of each justfile line that runs nix-build under `timeout`, with the
    justfile's `NAME := "VALUE"` variables put in place of `{{NAME}}`. A variable
    `NAME := if os() == "macos" { "MACOS" } else { "OTHER" }` takes the value for this platform."""
    text = (ROOT / "justfile").read_text()
    variables = dict(re.findall(r'(?m)^([a-z_]+) := "([^"]*)"$', text))
    for name, macos, other in re.findall(
            r'(?m)^([a-z_]+) := if os\(\) == "macos" \{ "([^"]*)" \} else \{ "([^"]*)" \}$', text):
        variables[name] = macos if sys.platform == "darwin" else other
    text = re.sub(r"\{\{([a-z_]+)\}\}", lambda match: variables.get(match.group(1), match.group(0)), text)
    lines = [shlex.split(line) for line in text.splitlines()
             if line.lstrip().startswith("timeout ") and " nix-build " in line]
    for line in text.splitlines():
        if line.lstrip().startswith("python3 -m tools.observability_nix --timeout "):
            words = shlex.split(line)
            lines.append(["timeout", "--foreground", words[4], *words[5:]])
    return [words for words in lines if "nix-build" in words]


def test_nix_builds_stay_in_the_callers_process_group() -> None:
    """Each justfile `timeout ... nix-build` uses `--foreground`.

    Without it, GNU timeout moves itself and nix-build into a new process group. The
    CI phase kill then misses them, and they keep the output pipes open (pull request
    #161, run 39239259061).
    """
    lines = nix_build_recipe_lines()
    assert lines, "The justfile has no nix-build recipe"
    for words in lines:
        assert words[1] == "--foreground" and words[3] == "nix-build", shlex.join(words)


@pytest.mark.requires_nix
def test_suite_limit_ends_before_the_limits_that_build_suites() -> None:
    """The per-suite limit that Nix renders is less than the limit of each recipe that builds the
    suite."""
    result = run_command(["nix-instantiate", "--eval", "--strict", "--json",
                          "--extra-experimental-features", "nix-command flakes", "--expr",
                          "builtins.mapAttrs (_: test: test.installPhase) "
                          f"(import {ROOT / 'build-support/default.nix'} {{}}).allTests"],
                         cwd=ROOT, timeout=60)
    assert result.returncode == 0, result.diagnostic()
    suite_limits = {name: int(next(shlex.split(line)[1] for line in script.replace("\\\n", " ").splitlines()
                                   if line.strip().startswith("timeout ")))
                    for name, script in json.loads(result.stdout).items()}
    recipe_limits = {words[words.index("-A") + 1]: int(words[2]) for words in nix_build_recipe_lines()
                     if words[words.index("-A") + 1] in SUITE_TARGETS}
    assert set(recipe_limits) == SUITE_TARGETS
    suites = set(json.loads((ROOT / "tests/nix_suites.json").read_text()))
    scheduled = set(json.loads((ROOT / "tests/nix_scheduled_suites.json").read_text()))
    mutants = set(json.loads((ROOT / "tests/nix_mutant_suites.json").read_text()))
    assert set(suite_limits) == suites
    for target, enclosing in recipe_limits.items():
        for name in built_suites(target, suites, scheduled, mutants):
            assert suite_limits[name] < enclosing, (name, suite_limits[name], target, enclosing)


def test_suite_build_limit_ends_before_the_checks_phase_on_each_system() -> None:
    """On each native CI system, the justfile's `suite_build_limit` is less than the limit of the
    phase that runs the recipes (`CHECKS_PHASE_LIMIT_SECONDS` of tools/ci_checks.py). Otherwise the
    phase stops `nix-build` first, and the report does not say that the suites ran out of time."""
    text = (ROOT / "justfile").read_text()
    match = re.search(r'(?m)^suite_build_limit := if os\(\) == "macos" \{ "([0-9]+)" \} else \{ "([0-9]+)" \}$', text)
    assert match is not None, "the justfile has no suite_build_limit for macOS and other systems"
    limits = {"aarch64-darwin": int(match.group(1)), "x86_64-linux": int(match.group(2))}
    assert set(limits) == set(CHECKS_PHASE_LIMIT_SECONDS)
    for system, limit in limits.items():
        assert limit < CHECKS_PHASE_LIMIT_SECONDS[system], (system, limit, CHECKS_PHASE_LIMIT_SECONDS[system])


def test_host_nix_limit_allows_every_dev_loop_phase() -> None:
    """The test-nix recipe must let the dev loop report its own timeout at every phase (issue 439)."""
    recipe = run_command(["just", "--dry-run", "test-nix"], cwd=ROOT, timeout=10)
    assert recipe.returncode == 0, recipe.diagnostic()
    commands = (recipe.stdout + recipe.stderr).splitlines()
    runtime, = [i for i, line in enumerate(commands) if " -A conformance " in line]
    suite, = [i for i, line in enumerate(commands) if "-m requires_nix" in line]
    assert runtime < suite, commands
    command = shlex.split(commands[suite])
    assert command[:2] == ["timeout", "--foreground"], command
    inner = (loop.COLD_BUILD_SECONDS + loop.WARM_BUILD_SECONDS + len(loop.PROGRAMS) * loop.PROGRAM_START_SECONDS
             + loop.METADATA_SECONDS + loop.VERDICT_SECONDS)
    assert int(command[2]) > inner + OTHER_HOST_TESTS_SECONDS, (command, inner, OTHER_HOST_TESTS_SECONDS)
