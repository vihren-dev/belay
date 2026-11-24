import Belay

set_option doc.verso true

/-! The two original foreign-key pragma contracts use their preparation conditions and
the database and table row-reference criteria. -/

namespace Belay.Sqlite.Model.ReplacedQueries
open Resolved

/-- The former {lit}`runScriptStep_keyCheck_empty` equates empty rows with valid references
across the database when the pragma prepares. -/
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

#print axioms runScriptStep_keyCheck_empty

/-- The former {lit}`runScriptStep_tableKeyCheck_empty` checks the named table’s references
from its lookup, its preparation condition and the table-specific row criterion. -/
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

#print axioms runScriptStep_tableKeyCheck_empty

end Belay.Sqlite.Model.ReplacedQueries
