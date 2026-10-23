"""The `belay.sqlite` frontend is the only portion of the `belay` namespace package.

This check runs on the host, on the complete checkout. In a Nix suite it would see only the frontend
modules listed in `tests/conformance_frontend.json`, so it could not check a module that is missing
from that list.
"""

from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
FRONTEND = ROOT / "belay/sqlite"
pytestmark = [pytest.mark.unit]


def test_namespace_has_one_portion() -> None:
    """The namespace contains one portion, with frontend sources in it."""
    assert not (ROOT / "belay/__init__.py").exists()
    assert {path.name for path in (ROOT / "belay").iterdir()} == {"sqlite"}
    assert sorted(FRONTEND.glob("*.py")), f"No frontend sources found in {FRONTEND}"
