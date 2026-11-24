import Belay.Sqlite.Model.Programs.Scripts.OrdinaryStepEffects

set_option doc.verso true

/-! When a step continues (ADR 0017, S6). The step laws of the schema and transaction statements say what a
step does if it continues. A proof of success also needs the other direction: that the model describes the
statement, so that the step continues. This module gives the general form for a statement without further
executions: the step continues when the statement resolves, has a clock value, reads only known counters, has
a ready run without alternatives, and the output of the run is not a stop of the model. -/

namespace Belay.Sqlite.Model

/-- For every clock value, parameters, statement that is no query, state, run, transition and initial
database: if the transition does not halt with the stop of the model, and the statement has an output for the
run, then the output of the step is not a stop of the model. In plain words, a statement other than a query
that the model runs gives an output that lets the run go on. Proof sketch: unfold the output; the halt cases
give an error, and the other case gives rows or a count of changes. -/
theorem Output.ofStep_ne_unmodeled (clock : Int) (parameters : List Value) (statement : Resolved.Statement)
    (before : SqlState) (run : StatementRun) (transition : SqlTransition) (initial : Option Database)
    (notQuery : ∀ query subqueries, statement ≠ .query query subqueries)
    (calm : haltError transition ≠ some .unmodeled)
    (output : (statementOutput clock parameters statement before run transition).isSome = true) :
    ∀ reason, Output.ofStep clock parameters statement before run transition initial ≠ .unmodeled reason := by
  intro reason
  obtain ⟨found, hasOutput⟩ := Option.isSome_iff_exists.mp output
  unfold Output.ofStep
  cases halted : haltError transition with
  | none =>
    cases statement
    case query query subqueries => exact absurd rfl (notQuery query subqueries)
    case createView => (simp [hasOutput] <;> split <;> simp)
    case createTable => (simp [hasOutput] <;> split <;> simp)
    case createIndex => (simp [hasOutput] <;> split <;> simp)
    case createTrigger => (simp [hasOutput] <;> split <;> simp)
    case addColumn => (simp [hasOutput] <;> split <;> simp)
    case drop => (simp [hasOutput] <;> split <;> simp)
    case rewrite => (simp [hasOutput] <;> split <;> simp)
    case dropColumn => (simp [hasOutput] <;> split <;> simp)
    case begin => (simp [hasOutput] <;> split <;> simp)
    case commit => (simp [hasOutput] <;> split <;> simp)
    case rollback => (simp [hasOutput] <;> split <;> simp)
    case insert => (simp [hasOutput] <;> split <;> simp)
    case update => (simp [hasOutput] <;> split <;> simp)
    case upsert => (simp [hasOutput] <;> split <;> simp)
    case insertSelect => (simp [hasOutput] <;> split <;> simp)
    case delete => (simp [hasOutput] <;> split <;> simp)
    case prepareError => (simp [hasOutput] <;> split <;> simp)
    case setting => (simp [hasOutput] <;> split <;> simp)
  | some failure =>
    rw [halted] at calm
    cases failure <;> simp_all
    done

/-- If a statement resolves, has a clock value, and its run is ready, has no alternative
execution, and gives a modeled output, then {name}`runScriptStep` continues
with no further executions. Proof sketch: readiness implies that every counter read is known.
Unfold the step and use the premises to rule out each stop. -/
theorem runScriptStep_continues {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value}
    {resolved : Resolved.Statement} {after : ResolveState} {value : Int}
    (found : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    (timed : statementClock clock index resolved = some value)
    (ready : (connection.state.statementRun value parameters resolved).ready = true)
    (single : (connection.state.statementRun value parameters resolved).alternatives = [])
    (modeled : ∀ reason, Output.ofStep value parameters resolved connection.state
      (connection.state.statementRun value parameters resolved)
      (advanceRun index resolved connection.state (connection.state.statementRun value parameters resolved)) ≠
        .unmodeled reason) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] := by
  have known : connection.state.counters.firstUnknown resolved.counterReads = none := by
    simpa [SqlState.statementRun] using (Bool.and_eq_true_iff.mp ready).2
  simp only [runScriptStep, runScriptStepWith, found, timed, known, ready, Bool.not_true, Bool.false_eq_true,
    ite_false, ranScriptStep]
  split
  · rename_i reason same
    exact absurd same (modeled reason)
  all_goals
    simp only [StatementExecution.ofAlternatives, single, List.mapM_nil, Except.map, pure, Except.pure,
      List.map_nil, RunStep.withOthers]
    exact ⟨_, _, rfl⟩

/-- For every connection, statement and values that resolve to a DROP TABLE without rules, which is the
resolution while foreign-key enforcement is off: the step continues, with no further execution. In plain
words, the model describes a drop that no foreign key can cascade from. Proof sketch:
{name}`runScriptStep_continues`; the drop is an unconditional effect. -/
theorem runScriptStep_drop_continues {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {positions : List Nat}
    (found : resolveStatement context connection.resolveState statement = .ok (.drop positions none, after)) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] := by
  refine runScriptStep_continues found rfl rfl rfl fun reason => ?_
  apply Output.ofStep_ne_unmodeled _ _ _ _ _ _ _ (by intro _ _ same; cases same) ?_ (by simp [statementOutput]) reason
  simp [advanceRun, advanceWith, SqlTransition.counted, SqlState.publish, haltError, SqlState.statementRun, runStatement,
    Model.step, StatementRun.withKeys]

/-- For every connection, statement and values that resolve to a rewrite of the catalog that keeps the
outline of the catalog ({name}`Catalog.sameOutline`), as a rename does: the step continues, with no further
execution. In plain words, the model describes a rename whose new catalog has the outline of the old one.
Proof sketch: {name}`runScriptStep_continues`; the effect succeeds under the guard. -/
theorem runScriptStep_rewrite_continues {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {renamed : Catalog}
    (found : resolveStatement context connection.resolveState statement = .ok (.rewrite renamed, after))
    (outline : connection.state.database.catalog.sameOutline renamed = true) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] := by
  refine runScriptStep_continues found rfl rfl rfl fun reason => ?_
  apply Output.ofStep_ne_unmodeled _ _ _ _ _ _ _ (by intro _ _ same; cases same) ?_ (by simp [statementOutput]) reason
  simp [advanceRun, advanceWith, SqlTransition.counted, SqlState.publish, haltError, SqlState.statementRun, runStatement,
    Model.step, outline]

end Belay.Sqlite.Model
