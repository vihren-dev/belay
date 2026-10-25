import Belay.Sqlite.Model.NormalizedFieldBackfillStep
import Belay.Sqlite.Model.NormalizedFieldDdlEffects

set_option doc.verso true

/-! The whole four-statement lowercase-field expansion as one state theorem:
ADD the plain TEXT field, backfill it with the lowercase of an existing column,
then register two triggers. The surrounding catalog, the table shape, the stored
rows and the statement values are arbitrary within the explicit premises. -/

namespace Belay.Sqlite.Model.NormalizedField

/-- The expansion's four statements with the values bound to each: ADD COLUMN of
the plain TEXT field, the backfill {lit}`UPDATE t SET field = lower(source)`, and
two CREATE TRIGGER statements without IF NOT EXISTS. The trigger names and
definitions are arbitrary; registration executes no trigger body. -/
def expansionScript (tableName name sourceName : Identifier)
    (first second : Identifier × CatalogTrigger) (firstValues secondValues thirdValues fourthValues : List Value) :
    List (Syntax.Statement × List Value) :=
  [(.addColumn tableName (textDefinition name), firstValues),
   (.update tableName [(name, .call "lower" [.identifier sourceName .none])] none [] [], secondValues),
   (.createTrigger first.1 false first.2.time first.2.event first.2.table first.2.condition first.2.body,
     thirdValues),
   (.createTrigger second.1 false second.2.time second.2.event second.2.table second.2.condition
     second.2.body, fourthValues)]

/-- Append one trigger object to the catalog and one empty storage slot, as the
actual CREATE TRIGGER step does. -/
def withTrigger (database : Database) (name : Identifier) (trigger : CatalogTrigger) : Database :=
  { catalog := database.catalog.createTrigger name trigger, rows := database.rows ++ [[]] }

/-- The database that the expansion reaches from the original database: the field
added at the table's position, its rows replaced by {name}`loweredRows`, then the
two trigger objects appended in order. -/
def expandedDatabase (database : Database) (position source : Nat) (table : Table) (name : Identifier)
    (first second : Identifier × CatalogTrigger) : Database :=
  withTrigger (withTrigger ((database.addColumn position (textColumn name table.shape.strict) .null).setRows
    position (loweredRows table source)) first.1 first.2) second.1 second.2

/-- If a four-statement expansion script has only modeled, error-free outputs, its
actual run has four outputs and reaches the original connection with the database
{name}`expandedDatabase` and some counters. Clock, snapshot, foreign-key and
recursive-trigger settings are unchanged. The table must be physical and present
at the stated position with wide, aliased rows and plain original columns; the
new field name must be absent and the source present. Both settings are off, and
the extended catalog selects no trigger for an UPDATE of the new column. Other
triggers, indexes and tables are unrestricted. Proof sketch: peel the four
successful steps, compose their exact effects, and use the extended catalog
and table laws to establish each later step's premises. -/
theorem expansion_state {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {tableName name sourceName : Identifier} {position source : Nat}
    (table : Table) (first second : Identifier × CatalogTrigger)
    (firstValues secondValues thirdValues fourthValues : List Value)
    (found : connection.state.database.catalog.findTable tableName = some (position, table.shape))
    (present : connection.state.database.table position = some table)
    (fresh : columnPosition table.shape.columns name = none)
    (sourceFound : columnPosition table.shape.columns sourceName = some source)
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none)
    (foreign : connection.foreignKeys = false) (recursive : connection.recursiveTriggers = false)
    (noneFiring : (connection.state.database.catalog.addColumn position
      (textColumn name table.shape.strict)).triggersFiring
      { table := position, event := .update (some [table.shape.columns.length]) } = [])
    (success : (runScriptFrom context clock index connection
      (expansionScript tableName name sourceName first second firstValues secondValues thirdValues fourthValues)).outputs.all
        (fun output => !output.isError && !output.endsRun) = true) :
    ∃ counters,
      (runScriptFrom context clock index connection
        (expansionScript tableName name sourceName first second firstValues secondValues thirdValues fourthValues)).connection =
        { connection with state := { connection.state with
          database := expandedDatabase connection.state.database position source table name first second,
          counters } } ∧
      (runScriptFrom context clock index connection
        (expansionScript tableName name sourceName first second firstValues secondValues thirdValues fourthValues)).outputs.length = 4 := by
  obtain ⟨o1, c1, s1, e1, success⟩ := successful_script_cons success
  obtain ⟨k1, h1⟩ := add_step (table := table) found present s1 e1
  have d1 : c1.state.database =
      connection.state.database.addColumn position (textColumn name table.shape.strict) .null := by rw [h1]
  obtain ⟨o2, c2, s2, e2, success⟩ := successful_script_cons success
  have extended : c1.state.database.catalog.findTable tableName = some (position,
      { table.shape with columns := table.shape.columns ++ [textColumn name table.shape.strict] }) := by
    rw [d1]; exact findTable_addColumn (textColumn name table.shape.strict) found
  have extendedPresent : c1.state.database.table position =
      some (table.appendColumns [(textColumn name table.shape.strict, .null)]) := by
    rw [d1]; exact Database.table_addColumn _ _ present
  have noTrigger : c1.state.database.catalog.triggersFiring
      { table := position, event := .update (some [table.shape.columns.length]) } = [] := by
    rw [d1]; exact noneFiring
  obtain ⟨k2, h2⟩ := backfill_step (position := position) (source := source) table extended extendedPresent fresh
    sourceFound wide aliased plain (by rw [h1]; exact foreign) (by rw [h1]; exact recursive) noTrigger s2 e2
  obtain ⟨o3, c3, s3, e3, success⟩ := successful_script_cons success
  obtain ⟨k3, h3⟩ := trigger_step first.1 first.2 s3 e3
  obtain ⟨o4, c4, s4, e4, success⟩ := successful_script_cons success
  obtain ⟨k4, h4⟩ := trigger_step second.1 second.2 s4 e4
  have run : runScriptFrom context clock index connection
      (expansionScript tableName name sourceName first second firstValues secondValues thirdValues fourthValues) =
      { outputs := [o1, o2, o3, o4], connection := c4 } := by
    simp only [expansionScript, runScriptFrom, s1, s2, s3, s4]
  rw [run]
  refine ⟨k4, ?_, rfl⟩
  simp [h4, h3, h2, h1, expandedDatabase, withTrigger]

end Belay.Sqlite.Model.NormalizedField
