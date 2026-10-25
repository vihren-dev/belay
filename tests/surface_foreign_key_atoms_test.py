"""Public FK atoms distinguish row truth, parent compatibility and pragma preparation."""

from pathlib import Path
import re

import pytest

from tests.runtime_support import run_command
from tests.surface_support import FIXTURES, surface_command

STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
"""Logical axioms admitted by the kernel audit; semantic assumptions are excluded."""

pytestmark = [pytest.mark.integration, pytest.mark.parser, pytest.mark.requires_lean("compiler")]


@pytest.mark.parametrize("fixture,axioms", [("ForeignKeyAtoms.lean", 14), ("ForeignKeyComparison.lean", 6),
                                         ("ForeignKeyCounter.lean", 13), ("ForeignKeySchemaRuns.lean", 8),
                                         ("ForeignKeyDelete.lean", 20), ("ForeignKeyInsert.lean", 34),
                                         ("ForeignKeyUpdate.lean", 30), ("ForeignKeyUpdateNecessity.lean", 6),
                                         ("ForeignKeyCoverage.lean", 33), ("ForeignKeyEngine.lean", 6),
                                         ("ForeignKeyEngineAxioms.lean", 33), ("ForeignKeyStatement.lean", 9),
                                         ("ForeignKeyRuns.lean", 9), ("ForeignKeyStatementAxioms.lean", 14),
                                         ("ForeignKeyCreate.lean", 19), ("ForeignKeyDdlDrop.lean", 16),
                                         ("ForeignKeyEnforcedDrop.lean", 18), ("ForeignKeyDropOutcomes.lean", 4),
                                         ("ForeignKeyAddColumn.lean", 41), ("ForeignKeyDdlRuns.lean", 19), ("ForeignKeyDdlDropRuns.lean", 27),
                                         ("ForeignKeyDdlNecessity.lean", 6), ("ForeignKeyActionRuns.lean", 8),
                                         ("ForeignKeyDdlViews.lean", 8)])
def test_independent_foreign_key_atoms(fixture: str, axioms: int, runtime_root: Path, tmp_path: Path) -> None:
    """ForeignKeyFacts, mapping transport and pragma laws compile through Belay's exported API.

    The fixture distinguishes both atoms, tests NULL and missing targets, repeated parent
    columns, affinity, rowid and NOCASE, and rejects an untransported child position after DROP.
    The comparison fixture checks structural lookup/scan agreement and a mixed-affinity
    counterexample. The counter fixture checks total violations and false raw update metadata;
    the schema-run fixture checks cascade, rollback and the saved-snapshot entry requirement.
    The deletion fixture applies the generic counter-bound law to a self-reference and checks
    the pending violation count for a parent with a retained child. The insertion fixture
    applies the new-row bound, repairs an orphan and shows why key uniqueness is required.
    The update fixture composes selected checks and frames unchanged keys. Its necessity
    fixture preserves stale-self-scan and stale-generated-cell counterexamples.
    The coverage fixture connects actual assignments, selected parent mappings and mapped
    action targets to the generic frame, including repeated columns and rowid aliases.
    The engine fixture applies the closed row/action/trigger induction to a cascading UPDATE
    and an AFTER-trigger FAIL that retains both changes; a separate fixture audits every
    exported engine proof. The statement fixtures exercise cascading UPDATE and the other
    enforced write forms, while the run fixture checks enforcement-off writes outside the FK
    footprint, partial FAIL, rollback and surface resolution. The statement audit covers all
    exported statement/run proofs. CREATE and plain DROP fixtures distinguish row truth
    from parent-schema compatibility, transport shifted positions, and permit removal
    of children together with parents. Enforced DROP uses the actual implicit DELETE and
    checks SET NULL, CASCADE, retained FAIL rows, NO ACTION rejection and rollback. Its
    separate catalog transport can fail even when the row atom holds. The ADD COLUMN fixture
    keeps both atoms for a column without constraints and for a reference without default,
    shows that a default of 99 breaks the row atom unless the statement refuses it, and
    accepts that default on a table without rows. The DDL run fixtures run CREATE TABLE, ADD
    COLUMN and DROP through the run contracts of the selected mapping and show, for each
    condition, a statement outside it that breaks an atom. The necessity fixture shows that a
    repeated-column index can change the selected projection and break row truth, as
    SQLite does, and that a column that references an absent table breaks only the schema
    atom. The action fixture runs RESTRICT against NO ACTION with a repairing trigger, SET
    DEFAULT with and without a parent for the default, and a deferred key with enforcement
    on and off. The view fixture shows that CREATE VIEW changes a selected parent link only for a
    declaration that names the view, which turns a missing parent into a mismatch, that a view with
    another name keeps both atoms, and that DROP VIEW of a named view fails the transport
    condition. Every displayed law excludes native-computation or admission axioms.
    """
    result = run_command(surface_command(runtime_root, FIXTURES / fixture, tmp_path),
                         cwd=tmp_path, timeout=90)
    assert result.returncode == 0, result.diagnostic()
    reports = re.findall(r"depends on axioms: \[([^]]*)\]|does not depend on any axioms", result.stdout)
    assert len(reports) == axioms, result.diagnostic()
    for report in reports:
        assert set(filter(None, map(str.strip, report.split(",")))) <= STANDARD_AXIOMS, result.diagnostic()
