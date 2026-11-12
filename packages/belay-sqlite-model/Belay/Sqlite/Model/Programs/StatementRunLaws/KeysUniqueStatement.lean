import Belay.Sqlite.Model.Programs.Scripts.KeysUniqueWrites
import Belay.Sqlite.Model.Programs.Scripts.KeysUniqueCreate
import Belay.Sqlite.Model.Programs.Scripts.InsertSelectLaws
import Belay.Sqlite.Model.Programs.Scripts.StatementDropColumn
import Belay.Sqlite.Model.Programs.Scripts.KeysUniqueDrop
import Belay.Sqlite.Model.Schema.Columns.KeysUniqueStatement

set_option doc.verso true

/-! The statement theorem of the atom "keys unique" (ADR 0022, D3, slice 2): every resolved
statement keeps {lit}`Database.KeysUnique` on the databases that a run keeps from its effect,
when it meets its condition ({lit}`Resolved.Statement.KeysCondition`). It covers the writes with
and without foreign keys and trigger programs, and has no hypothesis on the support check. -/

namespace Belay.Sqlite.Model

/-- The statement theorem. For every clock value, counters, parameter list, resolved statement and
database: if the database satisfies {name}`Database.KeysUnique` and the statement meets its
condition on the database ({name}`Resolved.Statement.KeysCondition`), the effect of
{name}`runStatement` satisfies {name}`Effect.Satisfies` for {name}`Database.KeysUnique`: the database of a success, and the
database that an error with {name}`ExecutionError.constraintFail` carries, satisfy
{name}`Database.KeysUnique`. It assumes nothing about the connection or the support check
({lit}`ready`). Proof sketch: a case for each statement form; a write without rules is the
theorem of its form, a write with rules is a write of the row engine
({name}`rowsKeys_keysUnique`, {name}`dropKeys_keysUnique`), and a missing table keeps the
database. -/
theorem runStatement_keysUnique (clock : Int) (counters : Counters) (parameters : List Value) (statement : Resolved.Statement)
    {database : Database} (unique : database.KeysUnique) (condition : statement.KeysCondition database) :
    (runStatement clock counters parameters statement database).effect.Satisfies Database.KeysUnique := by
  cases statement with
  | createTable target name shape => exact runStatement_createTable_keysUnique clock counters parameters target name shape unique
  | createIndex target name index => exact runStatement_createIndex_keysUnique clock counters parameters target name index unique
  | createView target name view =>
    exact runStatement_createView_keysUnique clock counters parameters target name view unique
  | createTrigger target name trigger =>
    exact runStatement_createTrigger_keysUnique clock counters parameters target name trigger unique
  | addColumn target column refuses => exact runStatement_addColumn_keysUnique clock counters parameters target column refuses unique condition
  | dropColumn position index stored =>
    exact runStatement_dropColumn_satisfies clock counters parameters position index stored unique fun runs =>
      unique.dropColumn runs
  | rewrite renamed =>
    exact runStatement_rewrite_satisfies clock counters parameters renamed unique fun same => unique.of_outline same
  | drop positions rules =>
    cases rules with
    | none => exact runStatement_drop_keysUnique clock counters parameters positions unique condition
    | some rules =>
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      exact Effect.satisfies_of_effectDatabase (dropKeys_keysUnique rules clock positions unique condition)
  | begin => exact runStatement_writesNone_keysUnique clock counters parameters unique _ (by simp)
  | commit => exact runStatement_writesNone_keysUnique clock counters parameters unique _ (by simp)
  | rollback => exact runStatement_writesNone_keysUnique clock counters parameters unique _ (by simp)
  | prepareError error => exact runStatement_writesNone_keysUnique clock counters parameters unique _ (by simp)
  | query query subqueries => exact runStatement_writesNone_keysUnique clock counters parameters unique _ (by simp)
  | setting setting on => exact runStatement_writesNone_keysUnique clock counters parameters unique _ (by simp)
  | insert target rows returning subqueries rules =>
    cases rules with
    | none => exact runStatement_insert_keysUnique clock counters parameters target rows returning subqueries unique
    | some rules =>
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      split
      · exact Effect.satisfies_of_database unique rfl
      · exact rowsKeys_effect_keysUnique rules clock target _ unique _ _
  | update target assignments filter returning subqueries rules =>
    cases rules with
    | none => exact runStatement_update_keysUnique clock counters parameters target assignments filter returning subqueries unique
    | some rules =>
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      split
      · exact Effect.satisfies_of_database unique rfl
      · exact rowsKeys_effect_keysUnique rules _ target _ unique _ _
  | upsert target rows clauses returning algorithm subqueries rules =>
    cases rules with
    | none =>
      exact Effect.satisfies_of_effectDatabase
        (runStatement_upsert_keysUnique clock counters parameters target rows clauses returning algorithm subqueries unique)
    | some rules =>
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      split
      · exact Effect.satisfies_of_database unique rfl
      · exact rowsKeys_effect_keysUnique rules clock target _ unique _ _
  | insertSelect target cells query clauses returning algorithm subqueries rules =>
    cases rules with
    | none =>
      exact runStatement_insertSelect_none_satisfies clock counters parameters target cells query clauses returning algorithm subqueries unique
        fun literals => Effect.satisfies_of_effectDatabase
          (runStatement_upsert_keysUnique clock counters parameters target literals clauses returning algorithm subqueries unique)
    | some rules =>
      exact runStatement_insertSelect_some_satisfies clock counters parameters target cells query clauses returning algorithm subqueries rules unique
        fun _ _ _ plain conflict => rowsKeys_effect_keysUnique rules clock target _ unique plain conflict
  | delete target filter returning subqueries rules =>
    cases rules with
    | none => exact runStatement_delete_keysUnique clock counters parameters target filter returning subqueries unique
    | some rules =>
      simp only [runStatement, Option.map_some, StatementRun.withKeys]
      split
      · exact Effect.satisfies_of_database unique rfl
      · exact rowsKeys_effect_keysUnique rules _ target _ unique _ _

end Belay.Sqlite.Model
