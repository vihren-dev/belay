"""The compiled screen of #sql_check: accepted candidates, claims without a screen, the time limit."""

from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.s6_check_support import false_answer, split_blocks
from tests.surface_support import fixture_file, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


@pytest.mark.timeout(200)
def test_screen_proposes_and_certification_decides(runtime_root: Path, tmp_path: Path) -> None:
    """CheckSamples.visitCandidates and CheckScreen.compileScreen: an accept-all screen gives no false
    result for a true claim; a claim with an implemented_by constant has no screen, so it is unknown
    with the reason, and its supplied database still certifies; a slow screen stops at
    sql.checkTimeLimit with the time-limit reason and no error. CheckOperation.check shrinks with the
    screen and certifies only the result: a shrink that the kernel rejects keeps the original witness."""
    result = run_command(surface_command(runtime_root, fixture_file("CheckScreenFixture.lean"), tmp_path),
                         cwd=tmp_path, timeout=180)
    assert result.returncode == 0, result.diagnostic()
    assert "accept-all screen: unknown" in result.stdout, result.stdout
    assert "screened shrinking: original kept; shrunk to NULL" in result.stdout, result.stdout
    blocks = split_blocks(result.stdout)
    assert blocks["override"].startswith("SQL check: unknown; the search could not compile a screen"), blocks
    assert "(db := ...)" in blocks["override"], blocks["override"]
    false_answer(blocks["override-witness"])
    assert blocks["slow"].startswith(
        "SQL check: unknown; the search reached its time limit; increase sql.checkTimeLimit"), blocks["slow"]
    assert "error" not in result.stdout.lower(), result.stdout
