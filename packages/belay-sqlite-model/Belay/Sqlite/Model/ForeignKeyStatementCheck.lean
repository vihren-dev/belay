import Belay.Sqlite.Model.Resolution.StatementArms
import Belay.Sqlite.Model.ForeignKeyPragmaQuery

set_option doc.verso true

/-! The full foreign-key pragma statement, with preparation stated separately from rows.
The conditions permit missing parents; empty violation results do not prove compatible
parent schemas. -/

namespace Belay.Sqlite.Model

/-- For every execution context, clock, index, connection and bound values, if no catalog
position has a foreign-key mismatch, the full database-wide pragma statement returns exactly
one empty row result if and only if the database has valid row references under its selected
mapping. A missing parent is permitted by the preparation condition; it can still invalidate
non-NULL child rows. The condition is exactly the successful-query preparation condition
of {name}`resolvePragma_keyCheck_iff`.
Proof sketch: resolve to the pragma query, apply its exact empty-output law, then apply
{name}`Database.keyCheck_nil_iff`. Clock, counters and transaction state are unrestricted. -/
theorem runScriptStep_keyCheck_empty (context : ResolveContext) (clock : Option Clock)
    (index : Nat) (connection : Connection) (parameters : List Value)
    (prepares : ∀ position < connection.state.database.catalog.length,
      connection.state.database.catalog.keyMismatch position = none) :
    (runScriptStep context clock index connection (.pragma (.foreignKeyCheck none)) parameters).output = .rows [] ↔
      connection.state.database.RowReferencesHold connection.state.database.catalog.foreignKeyMapping := by
  have prepared := (resolvePragma_keyCheck_iff connection.resolveState).mpr prepares
  rw [runScriptStep_output]
  simp only [statement_arms, resolveStatementPragma_foreignKeyCheck, prepared]
  rw [resolvedStepOutput_keyCheck_clock, resolvedStepOutput_keyCheck_empty]
  exact connection.state.database.keyCheck_nil_iff

/-- For every named table found at a catalog position, every execution context, clock, index,
connection and bound values, if that position has no foreign-key mismatch, the full named
pragma returns exactly one empty row result if and only if that table has valid row references
under the catalog-selected mapping. Other child tables need not satisfy their row references
or prepare successfully. Parent rows still determine the named table's references.
Proof sketch: the name and mismatch condition resolve to the table-specific query;
its exact empty-output law and {name}`Database.tableKeyCheck_nil_iff` give the result. -/
theorem runScriptStep_tableKeyCheck_empty (context : ResolveContext) (clock : Option Clock)
    (index : Nat) (connection : Connection) (parameters : List Value) (name : Identifier)
    (position : Nat) (table : Table)
    (found : connection.state.database.catalog.findTable name = some (position, table.shape))
    (present : connection.state.database.table position = some table)
    (prepares : connection.state.database.catalog.keyMismatch position = none) :
    (runScriptStep context clock index connection (.pragma (.foreignKeyCheck (some name))) parameters).output = .rows [] ↔
      table.RowReferencesHold connection.state.database.catalog.foreignKeyMapping connection.state.database position := by
  have prepared := (resolvePragma_tableKeyCheck_iff connection.resolveState name position table.shape found).mpr prepares
  rw [runScriptStep_output]
  simp only [statement_arms, resolveStatementPragma_foreignKeyCheck, prepared]
  rw [resolvedStepOutput_keyCheck_clock, resolvedStepOutput_keyCheck_empty]
  exact connection.state.database.tableKeyCheck_nil_iff present

end Belay.Sqlite.Model
