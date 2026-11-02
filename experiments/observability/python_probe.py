"""Exercise public pytest events and coverage contexts with checkable counterexamples."""

from collections import Counter
import json
from pathlib import Path
import shutil
import sys
import xml.etree.ElementTree as ET

from probe_support import run, write_json
from coverage_probe import measure as coverage_measure


def events(path: Path) -> list[dict[str, object]]:
    """Read this probe's JSONL stream for assertions against the controlled fixture."""
    return [json.loads(line) for line in path.read_text().splitlines()]


def measure(output: Path) -> None:
    """Prove selection, incomplete-run detection and the scope of per-test coverage."""
    output.mkdir()
    work = output / "work"
    work.mkdir()
    for name in ("subject.py", "cases.py", "pytest_events.py"):
        shutil.copyfile(Path(__file__).with_name(name), work / name)
    (work / "pytest.ini").write_text("[pytest]\naddopts = -p no:cacheprovider\n")
    environment = {"PYTEST_DISABLE_PLUGIN_AUTOLOAD": "1", "PYTHONPATH": str(work)}
    base = [sys.executable, "-m", "pytest", "-c", "pytest.ini", "-p", "pytest_events", "cases.py"]
    for label, selection, expected in (("outcomes", "not abrupt_exit", 1),
                                        ("abrupt", "abrupt_exit", 17)):
        run(output, label, [*base, "-k", selection, "--junitxml", str(output / f"{label}.xml")],
            cwd=work, environment={**environment, "PROBE_EVENTS": str(output / f"{label}.jsonl")}, expected=expected)
    normal = events(output / "outcomes.jsonl")
    phases = [event for event in normal if event["kind"] == "phase"]
    assert len([event for event in normal if event["kind"] == "collected"]) == 8
    assert len([event for event in normal if event["kind"] == "test_finish"]) == 7
    assert any(event["outcome"] == "failed" and event["phase"] == "setup" for event in phases)
    assert any(event["outcome"] == "failed" and event["phase"] == "call" for event in phases)
    assert any(event["xfail"] for event in phases)
    assert not any(event["phase"] == "call" and "setup_error" in str(event["nodeid"]) for event in phases)
    junit = ET.parse(output / "outcomes.xml")
    assert len(list(junit.iter("testcase"))) == 7
    abrupt = events(output / "abrupt.jsonl")
    assert any(event["kind"] == "test_start" for event in abrupt)
    assert not any(event["kind"] in ("session_finish", "test_finish") for event in abrupt)
    assert not (output / "abrupt.xml").exists()
    run(output, "inventory", [*base, "--collect-only", "-k", "classify"], cwd=work,
        environment={**environment, "PROBE_EVENTS": str(output / "inventory.jsonl")})
    inventory = events(output / "inventory.jsonl")
    assert len(next(event["nodeids"] for event in inventory if event["kind"] == "selected")) == 2
    coverage = coverage_measure(work, output, base, environment)
    write_json(output / "summary.json", {
        "collected": 8, "selected": 7, "completed": 7,
        "phase_outcomes": dict(Counter(f"{event['phase']}:{event['outcome']}" for event in phases)),
        "junit_cases": 7, "abrupt_has_start": True, "abrupt_has_junit": False,
        "coverage": coverage})
