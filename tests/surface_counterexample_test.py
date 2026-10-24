"""Kernel certification and explicit witnesses at the SQL checker's trust boundary."""

from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


def test_explicit_witnesses_require_kernel_certificates(runtime_root: Path, tmp_path: Path) -> None:
    """SqlRefute and CounterexampleCertificate check the exact claim, complete environments,
    and preconditions, and reject forged, admitted, native and self-dependent evidence."""
    result = run_command(surface_command(runtime_root, FIXTURES / "CounterexampleCertificates.lean", tmp_path),
                         cwd=tmp_path, timeout=60)
    assert result.returncode == 0, result.diagnostic()
    assert result.stdout.count("depends on axioms") == 6, result.stdout
    assert all(name not in result.stdout for name in ("sorryAx", "ofReduceBool", "_native")), result.stdout
