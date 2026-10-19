"""Summarize the JUnit reports in build/: what ran in this job, what Nix reused, and the slowest cases.

Nix reuses the output of a test suite when its inputs did not change (build-support/tests.nix),
so a report in build/ can come from a build of an earlier commit. The JUnit timestamp, which
pytest writes when the suite starts, tells the two apart. CI prints this summary after its checks
phase (tools/ci_checks.py), so the log says which suites actually ran.
"""

from dataclasses import dataclass
from datetime import datetime
import os
from pathlib import Path
import xml.etree.ElementTree as ElementTree

REPORT_PATTERNS = ("test-results/*.xml", "nix-tests*/junit.xml", "nix-tests*/*/junit.xml")
"""Report paths under build/: host pytest runs, the Darwin bundle phase and one folder per Nix suite.
Each pattern names its folder levels, because a recursive pattern does not enter the symbolic
links that the Nix report folders are made of."""
SLOWEST_CASES = 10
"""How many of the slowest test cases that ran in this job the summary lists."""


@dataclass(frozen=True)
class CaseTime:
    """The time of one test case, as `classname::name`."""

    seconds: float
    name: str


@dataclass(frozen=True)
class Report:
    """The counts, start time and case times of one JUnit report file."""

    path: str
    tests: int
    failed: int
    seconds: float
    started: datetime | None
    cases: tuple[CaseTime, ...]

    def ran_since(self, since: datetime) -> bool:
        """Whether the suite of this report started at or after `since`."""
        return self.started is not None and self.started >= since


def parse_timestamp(text: str | None) -> datetime | None:
    """A JUnit timestamp as an aware datetime; a timestamp without an offset is local time."""
    if not text:
        return None
    try:
        value = datetime.fromisoformat(text)
    except ValueError:
        return None
    return value if value.tzinfo is not None else value.astimezone()


def read_report(path: Path, build: Path) -> Report:
    """Read one JUnit file; a file with several suites adds their counts and keeps the first start."""
    root = ElementTree.parse(path).getroot()
    suites = [root] if root.tag == "testsuite" else list(root.iter("testsuite"))
    starts = [time for time in (parse_timestamp(suite.get("timestamp")) for suite in suites) if time]
    cases = tuple(CaseTime(float(case.get("time") or 0), f"{case.get('classname')}::{case.get('name')}")
                  for suite in suites for case in suite.iter("testcase"))
    return Report(
        path=str(path.relative_to(build)),
        tests=sum(int(suite.get("tests") or 0) for suite in suites),
        failed=sum(int(suite.get("failures") or 0) + int(suite.get("errors") or 0) for suite in suites),
        seconds=sum(float(suite.get("time") or 0) for suite in suites),
        started=min(starts) if starts else None,
        cases=cases)


def find_reports(build: Path) -> list[Report]:
    """All JUnit reports under `build`, in path order."""
    paths = sorted({path for pattern in REPORT_PATTERNS for path in build.glob(pattern)})
    return [read_report(path, build) for path in paths]


def origin(report: Report, since: datetime) -> str:
    """Whether the report's suite ran in this job, or when the build that Nix reused ran it."""
    if report.started is None:
        return "no timestamp"
    if report.ran_since(since):
        return "ran in this job"
    return f"reused from {report.started.astimezone().strftime('%Y-%m-%d %H:%M %Z')}"


def render_summary(reports: list[Report], since: datetime) -> str:
    """A Markdown summary: one row per report, then the slowest cases that ran in this job."""
    if not reports:
        return "### Test reports\n\nNo JUnit reports in build/.\n"
    lines = ["### Test reports", "", "| Report | Tests | Failed | Seconds | Origin |",
             "| --- | ---: | ---: | ---: | --- |"]
    lines += [f"| {report.path} | {report.tests} | {report.failed} | {report.seconds:.1f} | "
              f"{origin(report, since)} |" for report in reports]
    fresh = sorted(((case, report.path) for report in reports if report.ran_since(since)
                    for case in report.cases), key=lambda item: -item[0].seconds)[:SLOWEST_CASES]
    lines += ["", "### Slowest test cases that ran in this job", ""]
    if not fresh:
        return "\n".join(lines + ["No test case ran in this job.", ""])
    lines += ["| Seconds | Test case | Report |", "| ---: | --- | --- |"]
    lines += [f"| {case.seconds:.1f} | {case.name} | {path} |" for case, path in fresh]
    return "\n".join(lines + [""])


def write_summary(build: Path, since: datetime) -> str:
    """Print the summary and add it to the GitHub job summary page when `GITHUB_STEP_SUMMARY` is set."""
    summary = render_summary(find_reports(build), since)
    print(summary, flush=True)
    page = os.environ.get("GITHUB_STEP_SUMMARY")
    if page:
        with open(page, "a", encoding="utf-8") as stream:
            stream.write(summary + "\n")
    return summary
