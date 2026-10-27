"""The effect rules, frame rules and dependency certificates of ADR 0017, S6, hold in the kernel."""

from pathlib import Path
import re

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, surface_command

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]

ALLOWED_PROOF_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
"""Ordinary logical axioms; unchecked evaluation and assumed execution soundness are excluded."""

FIXTURE_TIMEOUT_SECONDS = 400
"""The time limit of one fixture. The fixtures use kernel evaluation of small programs."""


def check_fixture(runtime_root: Path, tmp_path: Path, name: str, reports_expected: int) -> None:
    """Elaborate one fixture under `tests/surface`. It must succeed without errors, report the expected
    number of `#print axioms` results, and every report must list only ordinary logical axioms."""
    result = run_command(surface_command(runtime_root, FIXTURES / name, tmp_path), cwd=tmp_path,
                         timeout=FIXTURE_TIMEOUT_SECONDS)
    assert result.returncode == 0, result.diagnostic()
    reports = re.findall(r"(?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)", result.stdout)
    assert len(reports) == reports_expected, result.diagnostic()
    for report in reports:
        assert set(filter(None, map(str.strip, report.split(",")))) <= ALLOWED_PROOF_AXIOMS, result.diagnostic()


def test_effect_rules_prove_statements(runtime_root: Path, tmp_path: Path) -> None:
    """The rules `Sql.ifOk_send_plainUpdate`, `Sql.ifOk_send_addColumn` and `plainUpdate_database` prove
    conditional and total fresh-run claims about an UPDATE and an ADD COLUMN for every complete environment."""
    check_fixture(runtime_root, tmp_path, "S6RulesEffects.lean", 3)


def test_frame_rules_prove_a_program(runtime_root: Path, tmp_path: Path) -> None:
    """The rules `Sql.Frame.bind` and `Sql.Frame.sendStatements_sheltered` prove the frame of a program whose
    continuation depends on a read with two permitted results: the program keeps the catalog, a table, the
    settings and the snapshot of an open transaction, and it writes a table that the frame does not shelter."""
    check_fixture(runtime_root, tmp_path, "S6RulesFrames.lean", 7)


def test_certificate_rules_prove_the_query_pattern(runtime_root: Path, tmp_path: Path) -> None:
    """The analysis `ReadAnalysis.analyze`, its soundness theorem and the rules `ReadCertificate.preservesAt_send`
    and `ReadCertificate.commutesOn_send` prove that a lookup by name gives the same results before and after a
    migration that appends a column, for every bound value, with a certificate that the analysis returns."""
    check_fixture(runtime_root, tmp_path, "S6RulesQueryPattern.lean", 8)


def test_certificate_rules_refuse_dependent_reads(runtime_root: Path, tmp_path: Path) -> None:
    """The certificate rules give no certificate, and the outputs differ, for reads that depend on more than
    the columns below the width: SELECT star, table metadata, a counter read, a change count, an unmodeled
    schema read, and a certificate with a width that is too narrow, whose obligation fails."""
    check_fixture(runtime_root, tmp_path, "S6RulesNegativeReads.lean", 8)
    check_fixture(runtime_root, tmp_path, "S6RulesNegativeCertificates.lean", 6)


def test_frame_rule_refuses_writes_outside_its_shelter(runtime_root: Path, tmp_path: Path) -> None:
    """The shelter of `Sql.Frame.sendStatements_sheltered` does not cover a trigger, a foreign-key action, a
    generated column, a rollback or a moving clock: the statements are not sheltered and the frame claim is
    false on the actual run."""
    check_fixture(runtime_root, tmp_path, "S6RulesNegativeFrames.lean", 7)


def test_commutation_rule_refuses_a_moving_clock(runtime_root: Path, tmp_path: Path) -> None:
    """The premise of `ReadCertificate.commutesOn` that the clock gives one date at every statement index
    fails for a clock that changes, and a read does not commute with a migration that stores the clock."""
    check_fixture(runtime_root, tmp_path, "S6RulesNegativeClock.lean", 2)
