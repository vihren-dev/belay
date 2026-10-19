"""Kernel-check transaction trace observations independently of the trace evaluator."""

import os
from pathlib import Path
import subprocess

import pytest


pytestmark = [pytest.mark.integration, pytest.mark.conformance, pytest.mark.kernel,
              pytest.mark.requires_lean]


def test_production_trace(tmp_path: Path, lean_sysroot: Path, lean_libraries: tuple[Path, Path]) -> None:
    """Snapshots preserve writes, commits, rollbacks, failure positions and stop-on-error."""
    proof = tmp_path / "TraceChecks.lean"
    proof.write_text('''import VerifierConformance.Pass
open Belay.Sqlite Belay.Sqlite.Conformance

def columns : List CatalogColumn := [{ name := "value", declaredType := some "INTEGER" }]
def original : Table := {
  shape := { columns := columns, uniqueKeys := [[0]] }
  rows := [⟨-4, [.integer 7]⟩, ⟨22, [.integer 8]⟩] }
def changed : Table := { original with rows := original.rows ++ [⟨23, [.integer 9]⟩] }
def catalog : Catalog :=
  [{ name := "p", entry := .table { columns := columns } }, { name := "t", entry := .table original.shape }]
def initial : Database := { catalog, rows := [[], original.rows.reverse] }
def before : Database := { catalog, rows := [[], original.rows] }
def after : Database := { catalog, rows := [[], changed.rows] }
def idle : Observation := ⟨before, before, false, none⟩
def begun : Observation := ⟨before, before, true, none⟩
def written : Observation := ⟨after, before, true, none⟩
def committed : Observation := ⟨after, after, false, none⟩
def insertNew : Resolved.Statement := .insert 1 [[.integer 9]] []
def writeScript : List Resolved.Statement := [.begin, insertNew]

theorem pending_write : trace writeScript initial = [idle, begun, written] := by
  decide +kernel
theorem explicit_commit : trace (writeScript ++ [.commit]) initial =
    [idle, begun, written, committed] := by decide +kernel
theorem explicit_rollback : trace (writeScript ++ [.rollback]) initial =
    [idle, begun, written, idle] := by decide +kernel
theorem constraint_halts : trace (writeScript ++ [insertNew, .commit]) initial =
    [idle, begun, written, { written with error := some (2, .constraintViolation) }] := by
  decide +kernel
theorem nested_begin_halts : trace (writeScript ++ [.begin, .rollback]) initial =
    [idle, begun, written, { written with error := some (2, .transactionAlreadyActive) }] := by
  decide +kernel
theorem empty_trace : trace [] initial = [idle] := by decide +kernel
theorem no_transaction : trace [.commit, insertNew] initial =
    [idle, { idle with error := some (0, .noActiveTransaction) }] := by decide +kernel
theorem prepare_error_halts : trace [.begin, .prepareError (.noSuchTable "absent")] initial =
    [idle, begun, { begun with error := some (1, .prepare (.noSuchTable "absent")) }] := by decide +kernel
#print axioms trace_final
#print axioms pending_write
#print axioms explicit_commit
#print axioms explicit_rollback
#print axioms constraint_halts
#print axioms nested_begin_halts
#print axioms empty_trace
#print axioms no_transaction
#print axioms prepare_error_halts
''')
    result = subprocess.run([str(lean_sysroot / "bin/lean"), str(proof)],
                            env={**os.environ, "LEAN_PATH": os.pathsep.join(map(str, lean_libraries))},
                            text=True, capture_output=True, timeout=30)
    assert result.returncode == 0, result.stdout + result.stderr
    for forbidden in ("sorryAx", "ofReduceBool", "_native"):
        assert forbidden not in result.stdout, result.stdout


def test_statement_outputs(tmp_path: Path, lean_sysroot: Path, lean_libraries: tuple[Path, Path]) -> None:
    """Native groups allow tie permutations and cuts while rejecting corrupted outputs."""
    proof = tmp_path / "OutputChecks.lean"
    proof.write_text('''import VerifierConformance.Outputs
open Belay.Sqlite Belay.Sqlite.Conformance

def a : ResultRow := [.integer 1]
def b : ResultRow := [.integer 2]
def c : ResultRow := [.integer 3]
def output (rows : List ResultRow) : StatementOutput := ⟨["x"], rows, some 0⟩
def groups : List OutputGroup := [⟨[a, b], 2⟩, ⟨[c], 1⟩]
def checks : List Bool := [
  matchesOutput (output [a,b,c]) (output [b,a,c]) (some groups),
  !matchesOutput (output [a,b,c]) (output [c,a,b]) (some groups),
  !matchesOutput (output [a,b,c]) (output [a,a,c]) (some groups),
  matchesOutput (output [a,b,c]) (output [c,b,a]) none,
  !matchesOutput (output [a,b,c]) (output [a,a,c]) none,
  matchesOutput (output [a,c]) (output [b,c]) (some [⟨[a,b],1⟩,⟨[c,a],1⟩]),
  matchesOutput (output [a]) (output [b]) (some [⟨[a,b,c],1⟩]),
  !matchesOutput (output [a]) (output [b,b]) (some [⟨[a,b,c],1⟩]),
  !matchesOutput (output [a]) (output [a]) (some [⟨[],1⟩]),
  !matchesOutput (output []) (output []) (some [⟨[a],0⟩]),
  !matchesOutput (output [a,b,c]) (output [a,b,c])
    (some [⟨[a],1⟩,⟨[b,a],1⟩,⟨[c],1⟩]),
  matchesOutput (output []) (output []) (some []),
  !matchesOutput (output []) ⟨[], [], some 0⟩ none,
  !matchesOutput (output [a]) ⟨["x"], [a], some 1⟩ none,
  !matchesOutput (output [a]) ⟨["x"], [a], none⟩ none,
  !matchesOutput ⟨["x"], [[]], none⟩ ⟨["x"], [[]], none⟩ none,
  !matchesOutput (output [a]) (output [c]) none]
theorem output_contract : checks.all id = true := by decide +kernel
#print axioms output_contract
#eval if checks.all id then "COMPILED_OUTPUTS_OK" else "COMPILED_OUTPUTS_FAILED"
''')
    result = subprocess.run([str(lean_sysroot / "bin/lean"), str(proof)],
                            env={**os.environ, "LEAN_PATH": os.pathsep.join(map(str, lean_libraries))},
                            text=True, capture_output=True, timeout=30)
    assert result.returncode == 0, result.stdout + result.stderr
    assert "COMPILED_OUTPUTS_OK" in result.stdout, result.stdout
    for forbidden in ("sorryAx", "ofReduceBool", "_native"):
        assert forbidden not in result.stdout, result.stdout
