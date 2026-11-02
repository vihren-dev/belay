"""Check the event plugin with existing review and report tests and their conftest."""

import json
from pathlib import Path
import sys
import xml.etree.ElementTree as ET

from probe_support import run, write_json


def measure(root: Path, output: Path) -> None:
    """Compare events with JUnit for the repository's unmodified tooling tests."""
    output.mkdir()
    events_path = output / "events.jsonl"
    junit_path = output / "junit.xml"
    run(output, "repository-tests", [sys.executable, "-m", "pytest",
        "tests/test_review_log.py", "tests/test_test_reports.py", "-m", "not requires_nix",
        "-p", "pytest_events",
        "-p", "no:cacheprovider", f"--junitxml={junit_path}"], cwd=root,
        environment={"PYTEST_DISABLE_PLUGIN_AUTOLOAD": "1", "PROBE_EVENTS": str(events_path),
                     "PYTHONPATH": f"{root / 'experiments/observability'}:{root}"})
    events = [json.loads(line) for line in events_path.read_text().splitlines()]
    cases = ET.parse(junit_path).findall(".//testcase")
    finished = [event for event in events if event["kind"] == "test_finish"]
    assert len(cases) == len(finished) > 0
    write_json(output / "summary.json", {"junit_cases": len(cases), "finished_events": len(finished),
        "scope": "Existing review/report tests with repository conftest; host-Nix test deselected."})
