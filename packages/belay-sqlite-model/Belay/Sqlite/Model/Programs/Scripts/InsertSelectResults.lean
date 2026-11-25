import Belay.Sqlite.Model.Programs.Scripts.InsertSelectExecutions

set_option doc.verso true

/-! Compute the complete executions of an INSERT from a query in the order of its source productions. -/

namespace Belay.Sqlite.Model

/-- The list of successful results of a fallible function follows the order of its arguments.
Proof sketch: take the result for the head and apply the induction hypothesis to the tail. -/
private theorem mapM_known {α β : Type} (f : α → Except String β) (g : α → β) (xs : List α)
    (known : ∀ x ∈ xs, f x = .ok (g x)) : xs.mapM f = .ok (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs tail =>
    rw [List.mapM_cons, known x List.mem_cons_self, tail (fun y mem => known y (List.mem_cons_of_mem _ mem))]
    rfl

/-- The other productions of an INSERT from a query give their own output and connection in
source order when their effects are modeled. Proof sketch: compute the execution for each
production using {name}`StatementExecution.ofRun_insertSelect` and project the traces. -/
theorem StatementExecution.insertSelect_others {index target : Nat} {value : Int} {connection : Connection}
    {parameters : List Value} {cells : List Resolved.SourceCell} {query : Resolved.Query}
    {clauses : List Resolved.ConflictClause} {returning : List (Resolved.Expr × String)}
    {algorithm : Option ConflictAlgorithm} {subqueries : List Resolved.Query} {rules : Option Resolved.WriteRules}
    (run : StatementRun) (modeled : ∀ other ∈ run.alternatives, other.effect.isModeled = true) :
    let stmt := Resolved.Statement.insertSelect target cells query clauses returning algorithm subqueries rules
    let eval := Resolved.statementContext value (connection.state.counters.view stmt.counterReads) parameters
      connection.state.database subqueries
    (StatementExecution.ofAlternatives index parameters connection stmt (connection.resolveState.after stmt) value run).map
      (List.map Traced.execution) = .ok (run.alternatives.map fun other =>
        ofWriteEffect connection index other.counts (insertSelectSuccessOutput eval returning other.counts other.keyRows)
          other.effect) := by
  dsimp only
  unfold ofAlternatives
  let stmt := Resolved.Statement.insertSelect target cells query clauses returning algorithm subqueries rules
  let eval := Resolved.statementContext value (connection.state.counters.view stmt.counterReads) parameters
    connection.state.database subqueries
  let traced (other : StatementRun.Alternative) : Traced :=
    ⟨ofWriteEffect connection index other.counts (insertSelectSuccessOutput eval returning other.counts other.keyRows)
      other.effect, other.toRun, advanceRun index stmt connection.state other.toRun⟩
  rw [mapM_known _ traced run.alternatives (fun other mem => by
    dsimp only
    rw [ofRun_insertSelect other.toRun (modeled other mem)]
    rfl)]
  simp [Except.map, List.map_map, traced, Function.comp_def, eval, stmt]

/-- A step whose main execution has an output continues with that execution and its
alternatives. A main execution with an unmodeled output ends the step with its reason.
Proof sketch: split the computed output, which both definitions inspect. -/
private theorem ranScriptStep_ofRun (index : Nat) (parameters : List Value) (connection : Connection)
    (stmt : Resolved.Statement) (after : ResolveState) (value : Int) (run : StatementRun) (transition : SqlTransition) :
    ranScriptStep index parameters connection stmt after value run transition =
      match StatementExecution.ofRun parameters connection stmt after value run transition with
      | .error reason => .ended reason
      | .ok main => .withOthers main.output main.next
          ((StatementExecution.ofAlternatives index parameters connection stmt after value run).map
            (List.map StatementExecution.Traced.execution)) := by
  unfold ranScriptStep StatementExecution.ofRun
  cases Output.ofStep value parameters stmt connection.state run transition <;> rfl

/-- When every alternative has a modeled effect, a successful main production installs its database and returns the number
of changes or its RETURNING rows. An unmodeled main effect ends the step. Each other main
failure continues with its primary code and conflict semantics. All further productions
carry their own output and state. Proof sketch: project the executions, then distinguish
the main effect and use the modeledness of each alternative. -/
theorem ranScriptStep_insertSelect {index target : Nat} {value : Int} {connection : Connection}
    {parameters : List Value} {cells : List Resolved.SourceCell} {query : Resolved.Query}
    {clauses : List Resolved.ConflictClause} {returning : List (Resolved.Expr × String)}
    {algorithm : Option ConflictAlgorithm} {subqueries : List Resolved.Query} {rules : Option Resolved.WriteRules}
    (run : StatementRun) (modeled : ∀ other ∈ run.alternatives, other.effect.isModeled = true) :
    let stmt := Resolved.Statement.insertSelect target cells query clauses returning algorithm subqueries rules
    let eval := Resolved.statementContext value (connection.state.counters.view stmt.counterReads) parameters
      connection.state.database subqueries
    let output := insertSelectSuccessOutput eval returning
    let further := run.alternatives.map fun other =>
      StatementExecution.ofWriteEffect connection index other.counts (output other.counts other.keyRows) other.effect
    ranScriptStep index parameters connection stmt (connection.resolveState.after stmt) value run
      (advanceRun index stmt connection.state run) =
      match run.effect with
      | .ok db => .continued (output run.counts run.keyRows) (connection.afterWrite db run.counts) further
      | .error (reason, reached) => if reason = .unmodeled then .ended unmodeledHere
        else .continued (.error reason.primaryCode) (connection.afterWriteError index reason reached run.counts) further := by
  dsimp only
  rw [ranScriptStep_ofRun, StatementExecution.insertSelect_others run modeled]
  by_cases main : run.effect.isModeled = true
  · rw [StatementExecution.ofRun_insertSelect run main]
    cases effect : run.effect with
    | ok => rfl
    | error failure =>
      obtain ⟨reason, reached⟩ := failure
      have different : reason ≠ .unmodeled := by simpa [effect, Effect.isModeled] using main
      simp [StatementExecution.ofWriteEffect, RunStep.withOthers, different]
  · have ordinary : (Resolved.Statement.insertSelect target cells query clauses returning algorithm subqueries rules).isControl = false := rfl
    cases effect : run.effect with
    | ok => simp [effect, Effect.isModeled] at main
    | error failure =>
      obtain ⟨reason, reached⟩ := failure
      have same : reason = .unmodeled := by simpa [effect, Effect.isModeled] using main
      subst reason
      simp [StatementExecution.ofRun, Output.ofStep, advanceRun_ordinary _ _ _ _ ordinary, SqlState.publish,
        effect, SqlTransition.counted, haltError_failed]

end Belay.Sqlite.Model
