import Belay.Sqlite.Model.Programs.Scripts.InsertSelectResults
import Belay.Sqlite.Model.Programs.Scripts.WriteRuleProofs

set_option doc.verso true

/-! The effect and alternative executions of supported INSERT SELECT runs in every write mode. -/

namespace Belay.Sqlite.Model

/-- With any resolved INSERT SELECT and clock value, failure of the support check ends the step.
On success of that check each further production is modeled. The main effect gives either its
change count or returned rows and a published database, an unmodeled stop, or the primary error
and conflict transition. Each further execution uses its own effect and counts.
Proof sketch: without rules, readiness includes modeledness of the further productions. With
rules there are no further executions. Apply {name}`ranScriptStep_insertSelect` in either case. -/
theorem insertSelectReady_results {index target : Nat} {value : Int} {connection : Connection}
    {parameters : List Value} {cells : List Resolved.SourceCell} {query : Resolved.Query}
    {clauses : List Resolved.ConflictClause} {returning : List (Resolved.Expr × String)}
    {algorithm : Option ConflictAlgorithm} {subqueries : List Resolved.Query} {rules : Option Resolved.WriteRules} :
    let stmt := Resolved.Statement.insertSelect target cells query clauses returning algorithm subqueries rules
    let run := connection.state.statementRun value parameters stmt
    let eval := Resolved.statementContext value (connection.state.counters.view stmt.counterReads) parameters
      connection.state.database subqueries
    let output := insertSelectSuccessOutput eval returning
    let further := run.alternatives.map fun other =>
      StatementExecution.ofWriteEffect connection index other.counts (output other.counts other.keyRows) other.effect
    (if run.ready then ranScriptStep index parameters connection stmt (connection.resolveState.after stmt) value run
      (advanceRun index stmt connection.state run) else .ended unmodeledHere) =
      if run.ready then match run.effect with
        | .ok db => .continued (output run.counts run.keyRows) (connection.afterWrite db run.counts) further
        | .error (reason, reached) => if reason = .unmodeled then .ended unmodeledHere
          else .continued (.error reason.primaryCode) (connection.afterWriteError index reason reached run.counts) further
      else .ended unmodeledHere := by
  dsimp only
  split
  · rename_i ready
    apply ranScriptStep_insertSelect
    cases rules with
    | none =>
      apply runStatement_insertSelect_none_alternatives
      exact (Bool.and_eq_true_iff.1 ready).1
    | some work =>
      intro other member
      rw [SqlState.statementRun_alternatives _ _ _ _ _ (by rfl)] at member
      contradiction
  · rfl

/-- A transfer that copies rowids directly is unavailable when write programs run.
Proof sketch: the transfer condition requires the absence of write rules. -/
theorem insertSelectTransferRowids_withRules (target : Nat) (cells : List Resolved.SourceCell) (query : Resolved.Query)
    (table : Table) (db : Database) (rules : Resolved.WriteRules) :
    insertSelectTransferRowids target cells query table db (some rules) = none := by
  unfold insertSelectTransferRowids
  split <;> simp

end Belay.Sqlite.Model
