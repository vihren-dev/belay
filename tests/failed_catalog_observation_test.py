"""Check that comparison and prediction read each view under the catalog of its own database.

The execution state carries the catalog (ADR 0013, D1), so an observation's visible and
committed databases each name their catalog. `compareSteps` and `stepJson`
(`VerifierConformance/Case.lean`, `Predict.lean`) must use that catalog for each view,
also after a failed statement inside a transaction.
"""

from pathlib import Path

import pytest

from tests.shared_table_shape_test import compile_checks

pytestmark = [pytest.mark.integration, pytest.mark.kernel,
              pytest.mark.requires_lean("compiler")]

CHECKS = """
import VerifierConformance.Predict
open Belay.Sqlite Belay.Sqlite.Conformance

def shape : CatalogTable := { columns := [{ name := "id", declaredType := none }] }
def table : Table := { shape, rows := [{ rowid := 1, values := [.integer 7] }] }
def catalog (name : String) : Catalog := [{ name, entry := .table shape }]
-- Distinct names make use of the wrong catalog observable in JSON as well as comparison.
def visible : Database := { catalog := catalog "visible", rows := [table.rows] }
def committed : Database := { catalog := catalog "committed", rows := [table.rows] }
def failed : Observation := ⟨visible, committed, true, some (0, .constraintViolation)⟩
def expected : NativeObservation where
  visible := [nativeTableOf visible.catalog 0 "visible" table]
  persisted := [nativeTableOf committed.catalog 0 "committed" table]
  transactionOpen := true
  primaryCode := 19
  extendedCode := 1299
  phase := some .step

example : compareSteps 0 [failed] [expected] = .agree := by decide +kernel
example : compareSteps 0 [failed] [{ expected with visible := [] }] = .disagree (some 0) := by decide +kernel
-- The committed view is compared under the committed catalog, not the visible one.
example : compareSteps 0 [failed] [{ expected with persisted := expected.visible }] = .disagree (some 0) := by
  decide +kernel
#guard (stepJson failed).getObjValD "visible" == predictedTables visible
#guard (stepJson failed).getObjValD "persisted" == predictedTables committed
#guard predictedTables visible != predictedTables committed
"""


def test_each_view_uses_its_own_catalog(tmp_path: Path, lean_sysroot: Path,
        lean_libraries: tuple[Path, Path]) -> None:
    """compareSteps and stepJson read the visible and the committed view under their own catalogs."""
    compile_checks(CHECKS, tmp_path, lean_sysroot, lean_libraries)
