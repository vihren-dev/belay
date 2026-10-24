"""Fresh consumers of S4's complete-environment and every-branch success contracts."""

from pathlib import Path

import pytest

from tests.shared_table_shape_test import compile_checks
from tests.surface_support import module_setup

pytestmark = [pytest.mark.integration, pytest.mark.kernel, pytest.mark.requires_lean("compiler")]

CHECKS = """
import Belay.Sqlite.QuerySuccess
open Belay.Sqlite
example {α : Type} (p : Sql α) (predicate : Database → Prop) :
    Succeeds p predicate ↔ ∀ db, predicate db → ∀ env : Env, env.Complete →
      p.SucceedsFrom env.clock 0 (db.raw.connection env.counters) := Iff.rfl
theorem actual_run_succeeds {σ α : Type} [Runnable σ α] {p : σ} {predicate : Database → Prop}
    (success : Succeeds p predicate) {db : Database} (holds : predicate db)
    {env : Env} (complete : env.Complete) : (db.run p env).outputs.allOk = true :=
  success.allOk holds complete
theorem scripts_need_no_extra_branches (script : Script) (predicate : Database → Prop) :
    Succeeds script predicate ↔
      ∀ db, predicate db → ∀ env : Env, env.Complete → (db.run script env).outputs.allOk = true :=
  Succeeds.script_iff script predicate
theorem default_query_success (script : Script) (query : script.isQuery = true) (db : Database) :
    (db.run script).outputs.allOk = true ↔
      ¬ Fails script db query ∧ (script.outputOn db).any Output.endsRun = false :=
  Script.query_allOk_iff query db
theorem public_run_keeps_the_model_result {α : Type} (program : Sql α) (db : Database) (env : Env) :
    let result := program.runFrom env.clock 0 (db.raw.connection env.counters)
    (program.run db env).value = result.value ∧
    (program.run db env).outputs = result.outputs ∧
    (program.run db env).db.raw = result.connection.state.database ∧
    (program.run db env).start = db ∧
    (program.run db env).transaction = result.connection.state.snapshot ∧
    (program.run db env).foreignKeys = result.connection.foreignKeys ∧
    (program.run db env).recursiveTriggers = result.connection.recursiveTriggers :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
#print axioms public_run_keeps_the_model_result
#print axioms Sql.runFrom_database_valid
#print axioms default_query_success
#print axioms Succeeds.of_holds
#print axioms actual_run_succeeds
#print axioms scripts_need_no_extra_branches
#print axioms Succeeds.pure
#print axioms Succeeds.mono
"""


def test_success_contracts_have_checked_proofs(runtime_root: Path, tmp_path: Path) -> None:
    """The success quantifiers, exact model-result wrapper and default-query equivalence compile
    against built surface modules, with no unchecked evaluation axiom."""
    libraries = (runtime_root / "packages/belay/.lake/build/lib/lean",
                 runtime_root / "packages/belay-sqlite-model/.lake/build/lib/lean")
    output = compile_checks(CHECKS, tmp_path, runtime_root / "lean", libraries,
                            setup=module_setup(runtime_root, tmp_path))
    assert len([line for line in output.splitlines() if "depends on axioms" in line]) == 8, output
