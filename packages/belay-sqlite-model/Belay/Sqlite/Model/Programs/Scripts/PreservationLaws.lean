import Belay.Sqlite.Model.Programs.Scripts.SqlLaws
import Belay.Sqlite.Model.Schema.Columns.PreservationLaws

set_option doc.verso true

/-! Derived extension lemmas concern arbitrary initial rows, including duplicate
application values. They do not assume a fixed fixture or prove native refinement. -/

namespace Belay.Sqlite.Model

/-- For every script of statements with any values whose statements are only CREATE/ADD,
idle starting database and position, the computed SQL result extends the starting database. Invalid schema
attempts and later errors retain the successful prefix. This makes no claim for
data writes or transaction control. The proof inducts over the guarded schema
transitions and composes their table preservation witnesses. -/
theorem runSqlFrom_extends (guard : SchemaOnly (script.map (·.1))) :
    DatabaseExtends database (runSqlFrom position script { database := database }).database := by
  induction script generalizing database position with
  | nil => exact DatabaseExtends.refl database
  | cons entry rest ih =>
    obtain ⟨statement, parameters⟩ := entry
    have head : SchemaOnly [statement] := fun item member => by
      simp only [List.mem_singleton] at member
      subst item
      exact guard statement (by simp)
    have tail : SchemaOnly (rest.map (·.1)) := fun item member => guard item (by simp_all)
    have first := step_extends 0 {} parameters statement database (by rw [guard statement (by simp)]; decide)
      (by rw [guard statement (by simp)]; decide)
    cases h : step 0 {} parameters statement database with
    | error failure => simpa [runSqlFrom, advance_schemaOnly head, h, Outcome.database] using DatabaseExtends.refl database
    | ok result =>
      simp only [h, effectDatabase] at first
      simpa [runSqlFrom, advance_schemaOnly head, h] using first.trans (ih tail (database := result))

/-- For every script of statements with any values whose statements are schema-only, and every
starting database, {name}`runSql` preserves
all existing tables, rows and old fields, including failure prefixes. The guard
excludes writes and transaction control. This is the idle, position-zero instance
of {name}`runSqlFrom_extends`; it does not claim native refinement. -/
theorem runSql_extends (guard : SchemaOnly (script.map (·.1))) (database : Database) :
    DatabaseExtends database (runSql script database).database :=
  runSqlFrom_extends guard

end Belay.Sqlite.Model
