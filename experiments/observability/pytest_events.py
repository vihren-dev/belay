"""Probe pytest's public hooks without changing the repository's test runner."""

import json
import os
from pathlib import Path
import time

import pytest


def emit(kind: str, **fields: object) -> None:
    """Close each JSONL write so completed events survive an abrupt process exit."""
    event = {"kind": kind, "observed_ns": time.time_ns(), **fields}
    with Path(os.environ["PROBE_EVENTS"]).open("a") as stream:
        stream.write(json.dumps(event) + "\n")


def pytest_sessionstart(session: pytest.Session) -> None:
    """Identify the process that owns this session's events."""
    emit("session_start", pid=os.getpid(), root=str(session.config.rootpath))


def pytest_itemcollected(item: pytest.Item) -> None:
    """Capture parametrized IDs before selection removes collected items."""
    emit("collected", nodeid=item.nodeid)


def pytest_deselected(items: list[pytest.Item]) -> None:
    """Distinguish deselection from a runtime skip."""
    emit("deselected", nodeids=[item.nodeid for item in items])


def pytest_collection_finish(session: pytest.Session) -> None:
    """Capture the selected inventory even for a collect-only invocation."""
    emit("selected", nodeids=[item.nodeid for item in session.items])


def pytest_runtest_logstart(nodeid: str, location: tuple[str, int | None, str]) -> None:
    """Record an attempt before fixtures run, including attempts that never finish."""
    emit("test_start", nodeid=nodeid)


def pytest_runtest_logreport(report: pytest.TestReport) -> None:
    """Use documented report fields for phase times, outcomes and diagnostics."""
    emit("phase", nodeid=report.nodeid, phase=report.when, outcome=report.outcome,
         start=report.start, stop=report.stop, duration=report.duration,
         failure=report.longreprtext if report.failed else None,
         xfail=getattr(report, "wasxfail", None))


def pytest_runtest_logfinish(nodeid: str, location: tuple[str, int | None, str]) -> None:
    """Mark completed attempts without inventing a finish for a killed process."""
    emit("test_finish", nodeid=nodeid)


def pytest_sessionfinish(session: pytest.Session, exitstatus: int) -> None:
    """Record pytest's exit status separately from individual test outcomes."""
    emit("session_finish", exitstatus=int(exitstatus))
