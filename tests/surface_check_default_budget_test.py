"""Claims of issue #317 answer at the default SQL check budget, and the audit record keeps the audit's result."""

from pathlib import Path

import pytest

from tests.runtime_support import run_command
from tests.s6_check_support import split_blocks
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


@pytest.mark.timeout(300)
def test_rebuild_claim_is_false_at_the_default_budget(runtime_root: Path, tmp_path: Path) -> None:
    """The record of accepted constants (CertificateAuditCache, auditDependencies) lets the check of the
    rebuild with three sessions certify its counterexample within the default budget. The audits of the
    fixture show that the record does not change a result: a use of the excluded declaration through a
    lemma is rejected after other constants were accepted, and a record made with other exclusions is
    not used."""
    result = run_command(surface_command(runtime_root, FIXTURES / "CheckDefaultBudget.lean", tmp_path),
                         cwd=tmp_path, timeout=280)
    assert result.returncode == 0, result.diagnostic()
    assert "audit record checks passed" in result.stdout, result.diagnostic()
    block = split_blocks(result.stdout)["rebuild"]
    assert block.startswith("SQL check: false."), block
