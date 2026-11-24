import Belay.Sqlite.Model.Programs.Scripts.UpsertRule

set_option doc.verso true

/-! The output and connection for one admitted production of INSERT from a query. -/

namespace Belay.Sqlite.Model

/-- The observable execution for a modeled write effect. Success installs the new database
and uses the output of its written rows or change count. Failure uses the reached rows and
the conflict algorithm to select the next connection. -/
def StatementExecution.ofWriteEffect (connection : Connection) (index : Nat) (counts : Counts)
    (success : Output) : Effect → StatementExecution
  | .ok database => ⟨success, connection.afterWrite database counts⟩
  | .error (reason, reached) => ⟨.error reason.primaryCode, connection.afterWriteError index reason reached counts⟩

/-- RETURNING gives the normalized evaluated rows of this production. With no RETURNING
columns, the output is its direct change count. -/
def insertSelectSuccessOutput (eval : Resolved.EvalContext) (returning : List (Resolved.Expr × String))
    (counts : Counts) (written : Option (List Row)) : Output :=
  if returning.isEmpty then .done (counts.changes.getD 0)
  else .rows (Resolved.normalForm (returnedRows eval returning ((written.getD []).map (·.values))))

/-- The execution of a production with a modeled effect is its change count or RETURNING
rows and updated connection, or its primary error and the connection selected by the error.
Proof sketch: a successful effect publishes the new database. Each modeled error halts
with its code, including FAIL and ROLLBACK in a transaction. -/
theorem StatementExecution.ofRun_insertSelect {index target : Nat} {value : Int} {connection : Connection}
    {parameters : List Value} {cells : List Resolved.SourceCell} {query : Resolved.Query}
    {clauses : List Resolved.ConflictClause} {returning : List (Resolved.Expr × String)}
    {algorithm : Option ConflictAlgorithm} {subqueries : List Resolved.Query} {rules : Option Resolved.WriteRules}
    (run : StatementRun) (modeled : run.effect.isModeled = true) :
    let stmt := Resolved.Statement.insertSelect target cells query clauses returning algorithm subqueries rules
    let after := connection.resolveState.after stmt
    let eval := Resolved.statementContext value (connection.state.counters.view stmt.counterReads) parameters
      connection.state.database subqueries
    StatementExecution.ofRun parameters connection stmt after value run (advanceRun index stmt connection.state run) =
      .ok (StatementExecution.ofWriteEffect connection index run.counts
        (insertSelectSuccessOutput eval returning run.counts run.keyRows) run.effect) := by
  dsimp only
  have ordinary : (Resolved.Statement.insertSelect target cells query clauses returning algorithm subqueries rules).isControl = false := rfl
  rw [advanceRun_ordinary _ _ _ _ ordinary, ResolveState.after_of_isControl _ ordinary]
  cases effect : run.effect with
  | ok database =>
    cases returning <;> simp [StatementExecution.ofRun, Output.ofStep, statementOutput, SqlState.publish,
      SqlTransition.counted, haltError, Resolved.Statement.returnsRows, StatementExecution.ofWriteEffect,
      insertSelectSuccessOutput, Connection.afterStep, Connection.afterWrite, Connection.resolveState] <;> rfl
  | error pair =>
    obtain ⟨reason, reached⟩ := pair
    cases reason <;> simp [effect, Effect.isModeled] at modeled <;>
      simp [StatementExecution.ofRun, Output.ofStep, SqlState.publish, SqlTransition.counted, haltError_failed,
        StatementExecution.ofWriteEffect, Connection.afterStep, Connection.afterWriteError, Connection.resolveState] <;> rfl

end Belay.Sqlite.Model
