import Belay

set_option doc.verso true

/-! The former schema statements of ADR 0033, derived with their original premises. -/

namespace Belay.Sqlite.Model.ReplacedSchema

/-- The deleted law {lit}`runScriptStep_rewrite`. For every connection and statement that resolves to a rewrite of the catalog, and every step that
continues: the step has no error output and no further execution, the rewritten catalog has the outline
of the catalog before ({name}`Catalog.sameOutline`), and the next connection is the connection with the
rewritten catalog and the rows as they were. In plain words, a rename never fails in the model and keeps
every row; a table found in the rewritten catalog at a position holds the rows of that position before
(failure and success law). Proof sketch: the applicable branch of {name}`runScriptStep_rewrite_eq` gives the result. -/
theorem runScriptStep_rewrite {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {renamed : Catalog}
    (found : resolveStatement context connection.resolveState statement = .ok (.rewrite renamed, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    output.isError = false ∧ others = [] ∧
      connection.state.database.catalog.sameOutline renamed = true ∧
      next = { connection with state := { connection.state with
        database := { connection.state.database with catalog := renamed } } } := by
  rw [runScriptStep_rewrite_eq found] at step
  dsimp only at step
  split at step
  · rename_i outline; cases step; exact ⟨rfl, rfl, outline, rfl⟩
  · cases step

#print axioms runScriptStep_rewrite

end Belay.Sqlite.Model.ReplacedSchema
