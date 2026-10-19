"""Check the layout of the test reports that the justfile recipes and CI keep."""

import json
from pathlib import Path

import pytest

from tests.runtime_support import run_command

ROOT = Path(__file__).resolve().parents[1]

pytestmark = [pytest.mark.unit, pytest.mark.environment]


@pytest.mark.requires_nix
def test_report_targets_link_each_suite_under_its_name() -> None:
    """`testReports`, `developmentTestReports` and `scheduledTestReports` (build-support/default.nix)
    link exactly the suites of `tests`, `developmentTests` and `scheduledTests`, each under its
    own name. The recipes build these targets, so a report path names its suite
    (`build/nix-tests-full/frozen/junit.xml`) and the recipes still build every suite.
    """
    expression = f'''let
      builds = import {ROOT / "build-support/default.nix"} {{}};
      check = reports: suites: let links = reports.passthru.entries; in {{
        names = builtins.attrNames links;
        same = map (name: links.${{name}} == suites.${{name}}) (builtins.attrNames links);
        expected = builtins.attrNames suites;
      }};
    in {{
      full = check builds.testReports builds.tests;
      development = check builds.developmentTestReports builds.developmentTests;
      scheduled = check builds.scheduledTestReports builds.scheduledTests;
    }}'''
    result = run_command(["nix-instantiate", "--eval", "--strict", "--json",
                          "--extra-experimental-features", "nix-command flakes", "--expr", expression],
                         cwd=ROOT, timeout=60)
    assert result.returncode == 0, result.diagnostic()
    layouts = json.loads(result.stdout)
    for name, layout in layouts.items():
        assert layout["names"] == layout["expected"], name
        assert layout["expected"] and all(layout["same"]), name
    assert "frozen" in layouts["full"]["names"] and "frozen" not in layouts["development"]["names"]
