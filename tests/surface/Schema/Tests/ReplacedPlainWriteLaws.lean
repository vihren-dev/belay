import Belay

set_option doc.verso true

namespace Belay.Sqlite.Model.ReplacedPlainWriteLaws

/-- The deleted law {lit}`plainDelete_database`. For every plain DELETE without subqueries,
if its target holds a table and its step continues without an error, the next database stores
the computed rows at the target, with a clock value returned for the statement.
Proof sketch: the exact rule excludes every ending case; the successful case gives the rows. -/
theorem plainDelete_database {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {target : Nat} {filter : Option Resolved.Expr} {after : ResolveState} {table : Table}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.delete target filter [] [] none, after))
    (present : connection.state.database.table target = some table)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (noError : output.isError = false) :
    ∃ value : Int, statementClock clock index (.delete target filter [] [] none) = some value ∧
      next.state.database = connection.state.database.setRows target
        (LiteralData.deleted (Resolved.statementContext value
          (connection.state.counters.view (Resolved.Statement.delete target filter [] [] none).counterReads)
          parameters connection.state.database []) table filter).rows := by
  rw [runScriptStep_plainDelete_eq found] at step
  split at step
  · cases step
  · rename_i value timed
    refine ⟨value, timed, ?_⟩
    dsimp only at step
    split at step
    · cases step
    · simp only [present] at step
      split at step
      · cases step; rfl
      · cases step

/-- The deleted law {lit}`plainUpdate_database`. For every plain UPDATE without subqueries,
if its target holds a table and its step continues without an error, the next database stores
the computed rows at the target, with a clock value returned for the statement.
Proof sketch: the exact rule excludes every ending case; the successful case gives the rows. -/
theorem plainUpdate_database {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {target : Nat} {assignments : List (Nat × Resolved.Expr)} {filter : Option Resolved.Expr}
    {after : ResolveState} {table : Table}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.update target assignments filter [] [] none, after))
    (present : connection.state.database.table target = some table)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (noError : output.isError = false) :
    ∃ value : Int, statementClock clock index (.update target assignments filter [] [] none) = some value ∧
      next.state.database = connection.state.database.setRows target
        (LiteralData.updated (Resolved.statementContext value
          (connection.state.counters.view
            (Resolved.Statement.update target assignments filter [] [] none).counterReads)
          parameters connection.state.database []) table assignments filter).rows := by
  rw [runScriptStep_plainUpdate_eq found] at step
  split at step
  · cases step
  · rename_i value timed
    refine ⟨value, timed, ?_⟩
    dsimp only at step
    split at step
    · cases step
    · simp only [present] at step
      split at step
      · split at step
        · cases step; rfl
        · cases step; cases noError
      · cases step

#print axioms plainDelete_database
#print axioms plainUpdate_database

end Belay.Sqlite.Model.ReplacedPlainWriteLaws
