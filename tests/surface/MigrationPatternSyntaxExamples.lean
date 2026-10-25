import Belay

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace MigrationSyntaxExamples
open Belay.Sqlite

/-- A pure migration makes the notation examples independent of database schema. -/
def migration : Sql Unit := .pure ()

/-- The guard observes the default query environment rather than the complete
environment quantified by migration comparisons. -/
def sqlGuard : Script := sql r"PRAGMA foreign_keys"

/-- The unguarded preservation spelling retains its fresh primitive. -/
theorem preserves_expansion : (migration preserves sql r"SELECT 1") =
    Migration.QueryPreserves migration (sql r"SELECT 1") (fun _ => True) := rfl

/-- A parameterized guarded query uses the default Holds predicate. -/
theorem guarded_preserves_expansion (value : Value) :
    (migration preserves sql r"SELECT $value" where sqlGuard) =
      Migration.QueryPreserves migration (sql r"SELECT $value") (fun db => Holds sqlGuard db) := rfl

/-- Translation supports scripts as migrations through the existing Runnable instance. -/
theorem translates_expansion :
    ((sql r"SELECT 3") translates sql r"SELECT 1" to sql r"SELECT 2") =
      Migration.QueryTranslates (send (sql r"SELECT 3")) (sql r"SELECT 1") (sql r"SELECT 2") (fun _ => True) := rfl

/-- Guarded translation retains both admitted query scripts and its default guard. -/
theorem guarded_translates_expansion :
    (migration translates sql r"SELECT 1" to sql r"SELECT 2" where sqlGuard) =
      Migration.QueryTranslates migration (sql r"SELECT 1") (sql r"SELECT 2") (fun db => Holds sqlGuard db) := rfl

/-- Same-application commutation retains the application's arbitrary return type. -/
theorem commutes_expansion : ((Sql.pure 7) commutes with migration) =
    Migration.Commutes migration (.pure 7) (fun _ => True) := rfl

/-- A guarded commutation uses exactly the guard's Holds observation. -/
theorem guarded_commutes_expansion : ((Sql.pure 7) commutes with migration where sqlGuard) =
    Migration.Commutes migration (.pure 7) (fun db => Holds sqlGuard db) := rfl

/-- Replacement commutation retains both application values without coercing to Unit. -/
theorem replacement_expansion : ((Sql.pure 7) commutes with migration as (Sql.pure 8)) =
    Migration.CommutesAs migration (.pure 7) (.pure 8) (fun _ => True) := rfl

/-- Guarded replacement commutation retains fresh environment and database quantification. -/
theorem guarded_replacement_expansion :
    ((Sql.pure 7) commutes with migration as (Sql.pure 8) where sqlGuard) =
      Migration.CommutesAs migration (.pure 7) (.pure 8) (fun db => Holds sqlGuard db) := rfl

/-- Quiet is the explicit annotation of the original script, not an executable action. -/
theorem quiet_expansion : quiet (sql r"SELECT 1") = Sql.View.quiet (send (sql r"SELECT 1")) := rfl

/-- Default Holds has unknown counters, while a complete comparison environment
can know zero changes. This guards against evaluating where in that environment.
Proof sketch: reduce both observations and the complete-environment predicate. -/
theorem default_guard_is_distinct :
    let guardQuery := sql r"SELECT 1 WHERE changes() = 0"
    let environment : Env := { clock := some (fun _ => 0), counters := Counters.newConnection }
    ¬ Holds guardQuery Database.empty ∧ environment.Complete ∧
      (Database.empty.run guardQuery environment).outputs = [.rows [[1]]] := by
  exact ⟨by decide +kernel, ⟨rfl, rfl, rfl, rfl⟩, rfl⟩

#explain migration preserves sql r"SELECT 1" where sqlGuard
#explain migration translates sql r"SELECT 1" to sql r"SELECT 2"
#explain (Sql.pure 7) commutes with migration
#explain (Sql.pure 7) commutes with migration as (Sql.pure 8) where sqlGuard

#print axioms preserves_expansion
#print axioms guarded_preserves_expansion
#print axioms translates_expansion
#print axioms guarded_translates_expansion
#print axioms commutes_expansion
#print axioms guarded_commutes_expansion
#print axioms replacement_expansion
#print axioms guarded_replacement_expansion
#print axioms quiet_expansion
#print axioms default_guard_is_distinct
end MigrationSyntaxExamples
