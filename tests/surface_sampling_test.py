"""S5's shared Plausible samplers and bounded certificate-preserving shrinker."""

from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.surface_support import fixture_file, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]
SAMPLES_COMPILE_SECONDS = 280
"""The limit for the compile of the sampling fixture. It takes 74-103 s on Linux and about twice that on
hosted macOS; the limit stays below the test's limit of 300 s, so a hang still fails with the name of the test."""


def test_samples_and_shrinks_retain_checked_counterexamples(runtime_root: Path, tmp_path: Path) -> None:
    """Our generator checks validity, targets case/SUM boundaries, and our shrinker recertifies
    every retained candidate under a finite attempt bound, even for repeating proposals."""
    result = run_command(surface_command(runtime_root, fixture_file("CounterexampleSamples.lean"), tmp_path),
                         cwd=tmp_path, timeout=SAMPLES_COMPILE_SECONDS)
    assert result.returncode == 0, result.diagnostic()
    for message in ("generated and shrunk databases certified", "ASCII NOCASE duplicate certified",
                    "non-ASCII case distinction certified", "integer SUM overflow certified",
                    "bounded shrinking recertified"):
        assert message in result.stdout, result.stdout
    assert "sorry" not in result.stdout, result.stdout
