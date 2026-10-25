"""S5's shared Plausible samplers and bounded certificate-preserving shrinker."""

from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_samples_and_shrinks_retain_checked_counterexamples(runtime_root: Path, tmp_path: Path) -> None:
    """Our generator checks validity, targets case/SUM boundaries, and our shrinker recertifies
    every retained candidate under a finite attempt bound, even for repeating proposals."""
    result = run_command(surface_command(runtime_root, FIXTURES / "CounterexampleSamples.lean", tmp_path),
                         cwd=tmp_path, timeout=180)
    assert result.returncode == 0, result.diagnostic()
    for message in ("generated and shrunk databases certified", "ASCII NOCASE duplicate certified",
                    "non-ASCII case distinction certified", "integer SUM overflow certified",
                    "bounded shrinking recertified"):
        assert message in result.stdout, result.stdout
    assert "sorry" not in result.stdout, result.stdout
