import Belay.Sqlite.Model.Programs.StatementRunLaws.DerivedColumnScript
import Belay.Sqlite.Model.Programs.Scripts.OrdinaryStepOk
import Belay.Sqlite.Model.Schema.Writes.DerivedColumnUpdateRun

set_option doc.verso true

/-! The success law of the derived-column migration without triggers (ADR 0017, S6): ADD COLUMN of a
column without constraints, then {lit}`UPDATE t SET c = e` of that column, runs with no error output when
the two statements resolve as the migration needs and the written value cannot fail. -/

namespace Belay.Sqlite.Model
open Resolved

/-- For every connection, table, migration without triggers and values bound to its two statements, the
run of the migration has only outputs that are neither an error nor an end of the run, when all of these
hold, with {lit}`column` the column that {name}`definedColumn` makes of the definition and {lit}`width` the
number of old columns:

* the catalog finds the table at the position, and the database holds it there;
* ADD COLUMN resolves to the addition of {lit}`column` at the position, with no check of a populated table;
* {lit}`column` is not a {lit}`STRICT` typed column, and the table has no column with its name;
* the written value resolves in the scope of the table with {lit}`column` to the expression;
* with {lit}`column` added to the catalog, the UPDATE resolves, and its exact event fires no trigger;
* both settings of the connection are off;
* the rows of the table are admitted ({name}`Table.Admitted`), keep NOT NULL, fit their types, pass their
  checks, and are unique for the keys of the database after ADD COLUMN;
* every check of the table and every key of the database after ADD COLUMN read only old columns, the rowid
  alias is ready and is an old column, and no old column is generated;
* the assigned expression reads only old columns, has no fallible call and does not read the clock, and the
  resolved UPDATE reads no counter.

The law covers no trigger, and it says nothing about the database that the run reaches
({name}`derivedColumn_state` does). Proof sketch: ADD COLUMN of a column without a default, NOT NULL or
check succeeds on every table ({name}`runScriptStep_ordinary_ok`); the UPDATE resolves to the backfill
({name}`backfill_resolution`), and {name}`runStatement_backfill_ok` gives its successful run. -/
theorem derivedColumn_script_ok {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {tableName : Identifier} {definition : Syntax.ColumnDefinition}
    {value : Syntax.Expr} {position : Nat} (table : Table) {derived : Resolved.Expr} {affinity : Option Affinity}
    (addValues updateValues : List Value)
    (found : connection.state.database.catalog.findTable tableName = some (position, table.shape))
    (present : connection.state.database.table position = some table)
    (addResolves : ∃ after, resolveStatement context connection.resolveState (.addColumn tableName definition) =
      .ok (.addColumn position (definedColumn table.shape.strict definition) false, after))
    (loose : (definedColumn table.shape.strict definition).strictType = none)
    (fresh : columnPosition table.shape.columns definition.name = none)
    (operand : resolveOperand context.profile.dqsDml
      (backfillScope position tableName table.shape (definedColumn table.shape.strict definition)) {} true value =
        .ok (derived, affinity))
    (updateResolves : ∃ resolution, resolveStatement context
      { connection.resolveState with
        catalog := connection.state.database.catalog.addColumn position (definedColumn table.shape.strict definition) }
      (.update tableName [(definition.name, value)] none [] []) = .ok resolution)
    (noneFiring : (connection.state.database.catalog.addColumn position
      (definedColumn table.shape.strict definition)).triggersFiring
      { table := position, event := .update (some [table.shape.columns.length]) } = [])
    (foreign : connection.foreignKeys = false) (recursive : connection.recursiveTriggers = false)
    (admitted : table.Admitted) (notNull : table.NotNull) (fits : table.TypesFit) (holds : table.ChecksHold)
    (unique : table.KeysUnique ((connection.state.database.addColumn position
      (definedColumn table.shape.strict definition) .null).keys position
        (table.appendColumns [(definedColumn table.shape.strict definition, .null)])))
    (checksBelow : ∀ check ∈ table.shape.allChecks, check.condition.readsBelow table.shape.columns.length = true)
    (keysBelow : ∀ key ∈ (connection.state.database.addColumn position
      (definedColumn table.shape.strict definition) .null).keys position
        (table.appendColumns [(definedColumn table.shape.strict definition, .null)]),
      key.readsBelow table.shape.columns.length = true)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none)
    (alias : LiteralData.aliasReady table.shape = true)
    (aliasBelow : table.shape.rowidAlias.all (· < table.shape.columns.length) = true)
    (assignedBelow : (assignedExpression
      (backfillScope position tableName table.shape (definedColumn table.shape.strict definition))
      table.shape.columns.length value derived).readsBelow table.shape.columns.length = true)
    (safe : (assignedExpression
      (backfillScope position tableName table.shape (definedColumn table.shape.strict definition))
      table.shape.columns.length value derived).any Resolved.Expr.isFallibleCall = false)
    (free : (Statement.update position [(table.shape.columns.length, assignedExpression
      (backfillScope position tableName table.shape (definedColumn table.shape.strict definition))
      table.shape.columns.length value derived)] none [] [] none).readsClock = false)
    (noCounters : (Statement.update position [(table.shape.columns.length, assignedExpression
      (backfillScope position tableName table.shape (definedColumn table.shape.strict definition))
      table.shape.columns.length value derived)] none [] [] none).counterReads = []) :
    (runScriptFrom context clock index connection
      (derivedColumnScript tableName definition value addValues updateValues [])).outputs.all
        (fun output => !output.isError && !output.endsRun) = true := by
  obtain ⟨after1, resolved1⟩ := addResolves
  have read : readDefaultValue (definedColumn table.shape.strict definition) = .ok .null := rfl
  have noClock : (definedColumn table.shape.strict definition).clockDefault = false := by
    simp [definedColumn, CatalogColumn.clockDefault]
  have nullable : (definedColumn table.shape.strict definition).notNull = false := rfl
  have unchecked : (definedColumn table.shape.strict definition).checks = [] := rfl
  obtain ⟨o1, c1, s1, e1, n1⟩ := runScriptStep_ordinary_ok (clock := clock) (index := index)
    (parameters := addValues) (value := 0)
    (database := connection.state.database.addColumn position (definedColumn table.shape.strict definition) .null)
    resolved1 rfl (by intro _ _ same; cases same) (by simp [statementClock, Statement.readsClock,
      Statement.clockExpressions]) (by rfl)
    (by simp only [SqlState.statementRun, runStatement, noClock, read]; rfl)
    (by simp [SqlState.statementRun, runStatement])
    (by simp [SqlState.statementRun, runStatement, Model.step, present, noClock, read, nullable, unchecked])
    (by simp [statementOutput])
  have extended : (connection.state.database.addColumn position (definedColumn table.shape.strict definition)
      .null).catalog.findTable tableName = some (position,
        { table.shape with columns := table.shape.columns ++ [definedColumn table.shape.strict definition] }) := by
    simp only [Database.addColumn]
    rw [Catalog.findTable_addColumn, found, Option.map_some]
    simp [Catalog.tableAt_of_findTable found]
  have present1 : c1.state.database.table position =
      some (table.appendColumns [(definedColumn table.shape.strict definition, .null)]) := by
    rw [n1]; exact Database.table_addColumn _ _ present
  have added : columnPosition (table.shape.columns ++ [definedColumn table.shape.strict definition])
      definition.name = some table.shape.columns.length :=
    columnPosition_append_new fresh (by simp [definedColumn])
  obtain ⟨⟨resolved2, after2⟩, resolved2Eq⟩ := updateResolves
  obtain ⟨rfl, rfl⟩ := backfill_resolution (state := { connection.resolveState with
      catalog := connection.state.database.catalog.addColumn position (definedColumn table.shape.strict definition) })
    extended added rfl operand foreign recursive noneFiring resolved2Eq
  have resolved2 : resolveStatement context c1.resolveState (.update tableName [(definition.name, value)] none [] []) =
      .ok (.update position [(table.shape.columns.length, assignedExpression
        (backfillScope position tableName table.shape (definedColumn table.shape.strict definition))
        table.shape.columns.length value derived)] none [] [] none,
        { connection.resolveState with
          catalog := connection.state.database.catalog.addColumn position
            (definedColumn table.shape.strict definition) }) := by
    rw [n1]; exact resolved2Eq
  have run := runStatement_backfill_ok 0 (c1.state.counters.view [])
    updateValues present1 admitted notNull fits holds (by rw [n1]; exact unique) checksBelow
    (by rw [n1]; exact keysBelow) nullable loose unchecked rfl plain
    alias aliasBelow assignedBelow safe
  obtain ⟨ready2, single2, effect2⟩ := run
  obtain ⟨o2, c2, s2, e2, -⟩ := runScriptStep_ordinary_ok (clock := clock) (index := index + 1)
    (parameters := updateValues) (value := 0) resolved2 rfl (by intro _ _ same; cases same)
    (by simp [statementClock, free]) (by rw [noCounters]; rfl)
    (by simp only [SqlState.statementRun, noCounters]; rw [ready2]; rfl)
    (by simp only [SqlState.statementRun, noCounters]; exact single2)
    (by simp only [SqlState.statementRun, noCounters]; exact effect2)
    (by simp [statementOutput, SqlTransition.counted, SqlState.publish, present1])
  have quiet1 := (runScriptStep_continued s1).2
  have quiet2 := (runScriptStep_continued s2).2
  simp [derivedColumnScript, runScriptFrom, s1, s2, e1, e2, quiet1, quiet2]
