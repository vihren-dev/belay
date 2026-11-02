"""Controlled outcomes test the observability integration, outside the normal suite."""

import os
import subprocess
import sys

import pytest

from subject import classify


@pytest.mark.parametrize("value,expected", [(1, "positive"), (0, "nonpositive")], ids=["positive", "zero"])
def test_classify(value: int, expected: str) -> None:
    """Check that the experiment distinguishes parametrized paths and identities."""
    assert classify(value) == expected


def test_child() -> None:
    """Expose whether the supported subprocess patch retains parent test context."""
    result = subprocess.run([sys.executable, "-c", "from subject import child_only; print(child_only())"],
                            check=True, capture_output=True, text=True, timeout=5)
    assert result.stdout.strip() == "child-only"


def test_failure() -> None:
    """Supply a known call-phase failure for event and JUnit extraction."""
    assert classify(0) == "intentional failure"


@pytest.fixture
def broken_setup() -> None:
    """Supply a known setup error before a test body can run."""
    raise RuntimeError("intentional setup error")


def test_setup_error(broken_setup: None) -> None:
    """Require a setup report and no call report for the experiment's failed fixture."""
    raise AssertionError("body must not run")


@pytest.mark.skip(reason="intentional skip")
def test_skip() -> None:
    """Give the probe a runtime skip, distinct from deselection."""


@pytest.mark.xfail(reason="intentional expected failure", strict=True)
def test_xfail() -> None:
    """Give the probe an expected failure with pytest's public outcome annotation."""
    assert False


def test_abrupt_exit() -> None:
    """Demonstrate report loss when no teardown or session-finish hook can execute."""
    os._exit(17)
