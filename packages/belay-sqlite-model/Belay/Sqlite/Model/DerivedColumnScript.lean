import Belay.Sqlite.Model.AddColumnPlainStep
import Belay.Sqlite.Model.CreateTriggerStep
import Belay.Sqlite.Model.ColumnPositionAppend
import Belay.Sqlite.Model.DerivedColumnBackfillStep

set_option doc.verso true

/-! A migration that adds a column, backfills it from an expression and registers triggers, as one
script (ADR 0017, S6). The state theorem names the connection that a successful run reaches. The table,
the catalog entry and the scan of the reached database are read from {name}`Belay.Sqlite.Model.Database.addDerivedColumn`. -/

namespace Belay.Sqlite.Model
open Resolved

/-- The CREATE TRIGGER statement without IF NOT EXISTS that registers a trigger, with the values bound to it. -/
def triggerStatement (trigger : (Identifier × CatalogTrigger) × List Value) : Syntax.Statement × List Value :=
  (.createTrigger trigger.1.1 false trigger.1.2.time trigger.1.2.event trigger.1.2.table trigger.1.2.condition
    trigger.1.2.body, trigger.2)

/-- The migration script: ADD COLUMN of a column definition, the backfill
{lit}`UPDATE t SET name = value` of the added column with no filter, and one CREATE TRIGGER statement for
each trigger, with the values bound to each statement. The trigger names and definitions are arbitrary;
registration executes no trigger body. -/
def derivedColumnScript (tableName : Identifier) (definition : Syntax.ColumnDefinition) (value : Syntax.Expr)
    (addValues updateValues : List Value) (triggers : List ((Identifier × CatalogTrigger) × List Value)) :
    List (Syntax.Statement × List Value) :=
  (.addColumn tableName definition, addValues) ::
    (.update tableName [(definition.name, value)] none [] [], updateValues) :: triggers.map triggerStatement

/-- For every list of triggers, and every run of their CREATE TRIGGER statements with only modeled,
error-free outputs, the reached connection is the start connection with the triggers appended in order
({name}`Database.appendTrigger`) and some counters, and the run has one output for each trigger. Clock,
snapshot and both settings stay. Proof sketch: induction over the triggers with
{name}`createTrigger_step` for the first. -/
theorem createTriggers_state {context : ResolveContext} {clock : Option Clock}
    (triggers : List ((Identifier × CatalogTrigger) × List Value)) :
    ∀ {index : Nat} {connection : Connection},
    (runScriptFrom context clock index connection (triggers.map triggerStatement)).outputs.all
        (fun output => !output.isError && !output.endsRun) = true →
    ∃ counters, (runScriptFrom context clock index connection (triggers.map triggerStatement)).connection =
        { connection with state := { connection.state with
          database := (triggers.map (·.1)).foldl (fun database trigger => database.appendTrigger trigger.1 trigger.2)
            connection.state.database, counters } } ∧
      (runScriptFrom context clock index connection (triggers.map triggerStatement)).outputs.length =
        triggers.length := by
  induction triggers with
  | nil => intro index connection _; exact ⟨connection.state.counters, by cases connection; rfl, rfl⟩
  | cons trigger rest ih =>
    intro index connection success
    obtain ⟨output, next, _, step, noError, later⟩ := successful_script_cons success
    obtain ⟨counters, reached⟩ := createTrigger_step trigger.1.1 trigger.1.2 step noError
    obtain ⟨more, connectionEq, lengthEq⟩ := ih later
    refine ⟨more, ?_, ?_⟩
    · simp only [List.map_cons, runScriptFrom, triggerStatement, step]
      rw [connectionEq, reached]
      simp [Database.appendTrigger]
    · simp only [List.map_cons, runScriptFrom, triggerStatement, step, List.length_cons]
      rw [lengthEq]

/-- For every original table with wide aliased rows and plain columns, and every script of ADD COLUMN of a
column without constraints, backfill of the column from a written value, and any number of CREATE TRIGGER
statements, if the run has only modeled, error-free outputs, then it has one output per statement and
reaches the start connection with the database {name}`Database.addDerivedColumn` and some counters. Clock,
snapshot and both settings stay. The written value must resolve, in the scope of the table with the added
column, to an expression of the old columns whose assigned form is context-free, and the new name must be
absent from the table. Both settings are off, and the catalog after ADD COLUMN must select no trigger for an
UPDATE of the new column. Other triggers, indexes and tables are unrestricted. Proof sketch: peel the
successful steps; ADD COLUMN gives the extended table ({name}`addColumn_plain_step`), the backfill stores
the computed rows ({name}`backfill_step`) under the premises that the extended catalog and table laws
establish, and the triggers append ({name}`createTriggers_state`). -/
theorem derivedColumn_state {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {tableName : Identifier} {definition : Syntax.ColumnDefinition}
    {value : Syntax.Expr} {position : Nat} (table : Table) {derived : Resolved.Expr} {affinity : Option Affinity}
    (addValues updateValues : List Value) (triggers : List ((Identifier × CatalogTrigger) × List Value))
    (found : connection.state.database.catalog.findTable tableName = some (position, table.shape))
    (present : connection.state.database.table position = some table)
    (constraintFree : definition.constraints = [])
    (admitted : addColumnRestriction table.shape definition = none)
    (fresh : columnPosition table.shape.columns definition.name = none)
    (operand : resolveOperand context.profile.dqsDml
      (backfillScope position tableName table.shape (definedColumn table.shape.strict definition)) {} true value =
        .ok (derived, affinity))
    (below : derived.readsBelow table.shape.columns.length = true)
    (contextFree : (assignedExpression
      (backfillScope position tableName table.shape (definedColumn table.shape.strict definition))
      table.shape.columns.length value derived).ContextFree)
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none)
    (foreign : connection.foreignKeys = false) (recursive : connection.recursiveTriggers = false)
    (noneFiring : (connection.state.database.catalog.addColumn position
      (definedColumn table.shape.strict definition)).triggersFiring
      { table := position, event := .update (some [table.shape.columns.length]) } = [])
    (success : (runScriptFrom context clock index connection
      (derivedColumnScript tableName definition value addValues updateValues triggers)).outputs.all
        (fun output => !output.isError && !output.endsRun) = true) :
    ∃ counters,
      (runScriptFrom context clock index connection
        (derivedColumnScript tableName definition value addValues updateValues triggers)).connection =
        { connection with state := { connection.state with
          database := connection.state.database.addDerivedColumn position table
            (definedColumn table.shape.strict definition)
            (assignedExpression
              (backfillScope position tableName table.shape (definedColumn table.shape.strict definition))
              table.shape.columns.length value derived)
            (triggers.map (·.1)),
          counters } } ∧
      (runScriptFrom context clock index connection
        (derivedColumnScript tableName definition value addValues updateValues triggers)).outputs.length =
          triggers.length + 2 := by
  obtain ⟨o1, c1, _, s1, e1, success⟩ := successful_script_cons success
  obtain ⟨k1, h1⟩ := addColumn_plain_step constraintFree admitted found present s1 e1
  have d1 : c1.state.database = connection.state.database.addColumn position
      (definedColumn table.shape.strict definition) .null := by rw [h1]
  obtain ⟨o2, c2, _, s2, e2, success⟩ := successful_script_cons success
  have extended : c1.state.database.catalog.findTable tableName = some (position,
      { table.shape with columns := table.shape.columns ++ [definedColumn table.shape.strict definition] }) := by
    rw [d1]
    simp only [Database.addColumn]
    rw [Catalog.findTable_addColumn, found, Option.map_some]
    simp [Catalog.tableAt_of_findTable found]
  have extendedPresent : c1.state.database.table position =
      some (table.appendColumns [(definedColumn table.shape.strict definition, .null)]) := by
    rw [d1]; exact Database.table_addColumn _ _ present
  have noTrigger : c1.state.database.catalog.triggersFiring
      { table := position, event := .update (some [table.shape.columns.length]) } = [] := by
    rw [d1]; exact noneFiring
  have added : columnPosition (table.shape.columns ++ [definedColumn table.shape.strict definition])
      definition.name = some table.shape.columns.length :=
    columnPosition_append_new fresh (by simp [definedColumn])
  obtain ⟨k2, h2⟩ := backfill_step (connection := c1) table (definedColumn table.shape.strict definition)
    extended extendedPresent added (by simp [definedColumn]) operand below contextFree wide aliased plain
    (by rw [h1]; exact foreign) (by rw [h1]; exact recursive) noTrigger s2 e2
  obtain ⟨k3, h3, count⟩ := createTriggers_state triggers success
  have run : runScriptFrom context clock index connection
      (derivedColumnScript tableName definition value addValues updateValues triggers) =
      { outputs := o1 :: o2 :: (runScriptFrom context clock (index + 1 + 1) c2 (triggers.map triggerStatement)).outputs,
        connection := (runScriptFrom context clock (index + 1 + 1) c2 (triggers.map triggerStatement)).connection } := by
    simp only [derivedColumnScript, runScriptFrom, s1, s2]
  rw [run]
  refine ⟨k3, ?_, ?_⟩
  · simp only
    subst h2
    rw [h3]
    subst h1
    simp [Database.addDerivedColumn, Database.addColumn]
  · simp only [List.length_cons, count]

end Belay.Sqlite.Model
