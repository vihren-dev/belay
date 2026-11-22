"""Test setup of the Lean code store prototype: import path and per-test timeouts.

The host shell has no pytest-timeout plugin, so the `timeout` marker is enforced here with an
alarm signal. Each test of this directory must carry the marker.
"""

from __future__ import annotations

from collections.abc import Iterator
from pathlib import Path
import signal
import sys
from types import FrameType

import pytest

EXPERIMENT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(EXPERIMENT))
sys.path.insert(0, str(EXPERIMENT.parents[1]))


def _expire(signum: int, frame: FrameType | None) -> None:
    """Fail the running test when its time limit is reached."""
    raise TimeoutError("The test ran longer than its timeout marker allows")


@pytest.fixture(autouse=True)
def enforce_timeout(request: pytest.FixtureRequest) -> Iterator[None]:
    """Apply the `timeout` marker of the test; a test without the marker fails."""
    marker = request.node.get_closest_marker("timeout")
    if marker is None:
        pytest.fail("Each test of the Lean code store prototype needs a timeout marker")
    previous = signal.signal(signal.SIGALRM, _expire)
    signal.alarm(int(marker.args[0]))
    try:
        yield
    finally:
        signal.alarm(0)
        signal.signal(signal.SIGALRM, previous)
