"""Check the layout of the test reports that the justfile recipes and CI keep, and their summary."""

from datetime import datetime, timezone
import json
from pathlib import Path
import subprocess
from unittest.mock import patch

import pytest

from tests.runtime_support import CommandResult, run_command
from tools.ci_checks import run_checks
from tools.test_reports import find_reports, render_summary

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


SINCE = datetime(2026, 10, 19, 12, 0, tzinfo=timezone.utc)
"""The start of the CI job in the summary tests."""


def write_junit(path: Path, timestamp: str | None, cases: dict[str, float], failures: int = 0) -> Path:
    """Write a small pytest-style JUnit file with one suite and the given case times."""
    path.parent.mkdir(parents=True, exist_ok=True)
    stamp = f' timestamp="{timestamp}"' if timestamp else ""
    body = "".join(f'<testcase classname="tests.probe" name="{name}" time="{seconds}"/>'
                   for name, seconds in cases.items())
    path.write_text(f'<?xml version="1.0"?><testsuites><testsuite name="pytest" errors="0" '
                    f'failures="{failures}" skipped="0" tests="{len(cases)}" '
                    f'time="{sum(cases.values())}"{stamp}>{body}</testsuite></testsuites>')
    return path


def test_summary_separates_suites_that_ran_from_reused_ones(tmp_path: Path) -> None:
    """`tools/test_reports.py` marks a report as run in this job only when its suite started after
    the job started, and lists only the cases of those reports as the slowest.

    A Nix suite whose inputs did not change keeps the report of an earlier build; before this
    summary, the CI artifact did not tell such a report from a new one.
    """
    write_junit(tmp_path / "nix-tests-full/frozen/junit.xml", "2026-10-19T12:05:00+00:00",
                {"slow": 40.0, "fast": 1.5}, failures=1)
    write_junit(tmp_path / "nix-tests-full/documentation/junit.xml", "2026-10-13T02:28:31+00:00",
                {"older and slower": 90.0})
    write_junit(tmp_path / "test-results/source.xml", "2026-10-19T14:10:00+02:00", {"host": 3.0})
    reports = find_reports(tmp_path)
    assert [report.path for report in reports] == [
        "nix-tests-full/documentation/junit.xml", "nix-tests-full/frozen/junit.xml", "test-results/source.xml"]
    summary = render_summary(reports, SINCE)
    assert "| nix-tests-full/frozen/junit.xml | 2 | 1 | 41.5 | ran in this job |" in summary
    assert "| test-results/source.xml | 1 | 0 | 3.0 | ran in this job |" in summary
    assert "| nix-tests-full/documentation/junit.xml | 1 | 0 | 90.0 | reused from 2026-10-1" in summary
    slowest = summary.split("### Slowest test cases that ran in this job", 1)[1]
    assert slowest.index("tests.probe::slow") < slowest.index("tests.probe::host") < slowest.index("tests.probe::fast")
    assert "older and slower" not in slowest


def test_summary_lists_at_most_ten_cases_and_handles_missing_data(tmp_path: Path) -> None:
    """The slowest-case list is capped, a report without a timestamp is marked, and an empty
    build folder gives a short summary instead of an error."""
    assert "No JUnit reports in build/." in render_summary(find_reports(tmp_path), SINCE)
    write_junit(tmp_path / "nix-tests-bundle/junit.xml", None, {"untimed": 5.0})
    assert "No test case ran in this job." in render_summary(find_reports(tmp_path), SINCE)
    write_junit(tmp_path / "test-results/nix.xml", "2026-10-19T12:01:00+00:00",
                {f"case{index}": float(index) for index in range(15)})
    summary = render_summary(find_reports(tmp_path), SINCE)
    assert "| nix-tests-bundle/junit.xml | 1 | 0 | 5.0 | no timestamp |" in summary
    listed = [line for line in summary.splitlines() if "tests.probe::case" in line]
    assert len(listed) == 10 and "tests.probe::case14" in listed[0] and "tests.probe::case5 " in listed[-1]


def test_ci_writes_the_summary_after_a_failed_checks_phase(tmp_path: Path, monkeypatch: pytest.MonkeyPatch,
                                                           capsys: pytest.CaptureFixture[str]) -> None:
    """`run_checks` writes the summary to the log and to `GITHUB_STEP_SUMMARY` also when the
    checks phase fails, because a failed run is when the reports matter most."""
    page = tmp_path / "step-summary.md"
    monkeypatch.setenv("SQLITE_VERIFIER_SYSTEM", "x86_64-linux")
    monkeypatch.setenv("GITHUB_STEP_SUMMARY", str(page))

    def run(command: list[str], **options: object) -> CommandResult:
        """Pass the setup and version phases; fail the checks phase after it wrote one report."""
        if command[0] != "just" or command[1] == "setup":
            return CommandResult(tuple(command), 0, "", "", 0.01)
        write_junit(tmp_path / "build/test-results/source.xml", datetime.now(timezone.utc).isoformat(),
                    {"checked": 2.0})
        return CommandResult(tuple(command), 1, "", "", 0.01)

    with patch("tools.ci_checks.check_resources"), patch("tools.ci_checks.run_command", side_effect=run):
        with pytest.raises(subprocess.CalledProcessError):
            run_checks("test", "source", "x86_64-linux", tmp_path)
    assert "| test-results/source.xml | 1 | 0 | 2.0 | ran in this job |" in capsys.readouterr().out
    assert "tests.probe::checked" in page.read_text()
