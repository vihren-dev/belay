import Belay.Sqlite.Model.InsertSelectLaws
import Belay.Sqlite.Model.InsertSelectKeeps
import Belay.Sqlite.Model.StatementSingleton
import Belay.Sqlite.Model.StatementExecutionLaws
import Belay.Sqlite.Model.StatementOutput
import Belay.Sqlite.Model.Output

set_option doc.verso true

/-! Every further execution of INSERT from a query has an output (ADR 0019, D4, amended 2026-10-25).
A step of a script ends the run when a further execution has no output
({lit}`StatementExecution.ofAlternatives`). The support check of INSERT from a query excludes an error
with the reason {lit}`ExecutionError.unmodeled` in a further execution, and then every output of an
execution of this statement is a result. So the step of a statement that passes the support check
ends the run only when the output of the model's own execution is not a result. -/

namespace Belay.Sqlite.Model

/-- For every state, position, error and database, a statement that fails with the error halts with
that error ({name}`haltError`), also in an open transaction and for a rollback failure. Proof
sketch: unfold the failure of the state and take the cases of its snapshot. -/
theorem haltError_failed (state : SqlState) (position : Nat) (reason : ExecutionError) (database : Database) :
    haltError (.halt (state.failed position reason database)) = some reason := by
  unfold SqlState.failed SqlState.finish
  split
  · cases h : state.snapshot <;> simp [haltError]
  · cases h : state.snapshot <;> simp [haltError]

/-- For every state, position, run of INSERT from a query whose effect is no error with the reason
{name}`ExecutionError.unmodeled` ({name}`Effect.isModeled`), the output of its step
({name}`Output.ofStep`) with the transition of {name}`advanceRun` is no {name}`Output.unmodeled`. Proof sketch: a
success continues and gives the output of the statement; an error halts with its reason
({name}`haltError_failed`), which gives {name}`Output.error`. -/
theorem Output.ofStep_insertSelect_ne_unmodeled (value : Int) (parameters : List Value) (target : Nat)
    (cells : List Resolved.SourceCell) (query : Resolved.Query) (clauses : List Resolved.ConflictClause)
    (returning : List (Resolved.Expr × String)) (algorithm : Option ConflictAlgorithm) (subqueries : List Resolved.Query)
    (rules : Option Resolved.WriteRules) (state : SqlState) (position : Nat) (run : StatementRun)
    (modeled : run.effect.isModeled = true) (reason : String) :
    Output.ofStep value parameters (.insertSelect target cells query clauses returning algorithm subqueries rules) state run
      (advanceRun position (.insertSelect target cells query clauses returning algorithm subqueries rules) state run) ≠
      .unmodeled reason := by
  rcases effect : run.effect with ⟨failure, reached⟩ | database
  · simp only [effect, Effect.isModeled, bne_iff_ne, ne_eq] at modeled
    have transition : advanceRun position (.insertSelect target cells query clauses returning algorithm subqueries rules)
        state run = .halt (state.failed position failure (if failure = .constraintFail then reached else state.database)) := by
      simp only [advanceRun, advanceWith, effect, SqlState.publish, SqlTransition.counted]
    unfold Output.ofStep
    rw [transition, haltError_failed]
    cases failure <;> simp_all
  · obtain ⟨next, transition⟩ : ∃ next, advanceRun position
        (.insertSelect target cells query clauses returning algorithm subqueries rules) state run = .next next :=
      ⟨_, by simp only [advanceRun, advanceWith, effect, SqlState.publish, SqlTransition.counted]; rfl⟩
    unfold Output.ofStep
    rw [transition]
    simp only [haltError, statementOutput]
    by_cases returns : (Resolved.Statement.insertSelect target cells query clauses returning algorithm subqueries
      rules).returnsRows = true <;> simp [returns]

/-- For every function that can fail and list of arguments on which it succeeds, the monadic map
succeeds. Proof sketch: induction on the arguments. -/
theorem List.mapM_except_ok {α β : Type} (f : α → Except String β) :
    ∀ (arguments : List α), (∀ argument ∈ arguments, ∃ result, f argument = .ok result) →
      ∃ results, arguments.mapM f = .ok results
  | [], _ => ⟨[], by simp [List.mapM_nil]; rfl⟩
  | argument :: rest, succeeds => by
    obtain ⟨head, first⟩ := succeeds argument List.mem_cons_self
    obtain ⟨tail, others⟩ := List.mapM_except_ok f rest fun other member => succeeds other (List.mem_cons_of_mem _ member)
    exact ⟨head :: tail, by simp [List.mapM_cons, first, others, bind, Except.bind, pure, Except.pure]⟩

/-- For every clock value, counters, parameters, target, cells, query, clauses, {lit}`RETURNING`
list, algorithm, subqueries and database: if the run of INSERT from a query without rules passes the
support check, no further execution of it is an error with the reason
{name}`ExecutionError.unmodeled` ({name}`Effect.isModeled`). Proof sketch: the support check of the run
asks that of each further execution. -/
theorem runStatement_insertSelect_none_alternatives (clock : Int) (counters : Counters) (parameters : List Value)
    (target : Nat) (cells : List Resolved.SourceCell) (query : Resolved.Query) (clauses : List Resolved.ConflictClause)
    (returning : List (Resolved.Expr × String)) (algorithm : Option ConflictAlgorithm)
    (subqueries : List Resolved.Query) (database : Database) :
    (runStatement clock counters parameters (.insertSelect target cells query clauses returning algorithm subqueries none)
      database).ready = true →
    ∀ alternative ∈ (runStatement clock counters parameters
      (.insertSelect target cells query clauses returning algorithm subqueries none) database).alternatives,
      alternative.effect.isModeled = true := by
  rw [show runStatement clock counters parameters (.insertSelect target cells query clauses returning algorithm subqueries none)
    database = insertSelectRun clock counters parameters target cells query clauses returning algorithm subqueries none database
    from rfl]
  unfold insertSelectRun
  cases found : database.table target with
  | none => intro _ alternative member; simp at member
  | some table =>
    dsimp only
    cases productions : query.productions (Resolved.statementContext clock counters parameters database subqueries) database
        (!Resolved.Statement.collectsSource target query subqueries returning none) with
    | none => intro _ alternative member; simp at member
    | some list =>
      cases list with
      | nil => intro _ alternative member; simp at member
      | cons first others =>
        dsimp only
        intro ready alternative member
        simp only [Option.isNone_none, ite_true, List.map_map, List.mem_map, Function.comp] at member
        obtain ⟨other, inOthers, rfl⟩ := member
        simp only [Bool.and_eq_true] at ready
        obtain ⟨⟨⟨⟨⟨⟨_, restReady⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := ready
        exact (Bool.and_eq_true_iff.1 (List.all_eq_true.1 restReady _ (List.mem_map_of_mem inOthers))).2

/-- For every index, values, connection, resolved statement, resolution state and clock value: if the
run of the statement on the connection passes the support check, every alternative of the run has an
execution, so {name}`StatementExecution.ofAlternatives` succeeds. Proof sketch: a statement that is no
INSERT from a query without rules has no alternative; for that statement, no further execution is an
error with the reason {name}`ExecutionError.unmodeled`, and then its output is no
{name}`Output.unmodeled` ({name}`Output.ofStep_insertSelect_ne_unmodeled`). -/
theorem StatementExecution.ofAlternatives_ok_of_ready (index : Nat) (parameters : List Value) (connection : Connection)
    (resolved : Resolved.Statement) (after : ResolveState) (value : Int)
    (ready : (connection.state.statementRun value parameters resolved).ready = true) :
    ∃ further, StatementExecution.ofAlternatives index parameters connection resolved after value
      (connection.state.statementRun value parameters resolved) = .ok further := by
  by_cases single : resolved.fromQuery = false
  · exact ⟨[], StatementExecution.ofAlternatives_of_single _ _ _ _ _ _
      (SqlState.statementRun_alternatives _ _ _ _ _ single)⟩
  · obtain ⟨target, cells, source, clauses, returning, algorithm, subqueries, rfl⟩ :=
      Resolved.Statement.fromQuery_form (by simpa using single)
    have modeled := runStatement_insertSelect_none_alternatives value
      (connection.state.counters.view
        (Resolved.Statement.insertSelect target cells source clauses returning algorithm subqueries none).counterReads)
      parameters target cells source clauses returning algorithm subqueries connection.state.database
      (Bool.and_eq_true_iff.1 ready).1
    unfold StatementExecution.ofAlternatives
    apply List.mapM_except_ok
    intro alternative member
    have output := Output.ofStep_insertSelect_ne_unmodeled value parameters target cells source clauses returning algorithm
      subqueries none connection.state index alternative.toRun (modeled alternative member)
    unfold StatementExecution.ofRun
    dsimp only
    split
    · rename_i reason same
      exact absurd same (output reason)
    all_goals exact ⟨_, rfl⟩

end Belay.Sqlite.Model
