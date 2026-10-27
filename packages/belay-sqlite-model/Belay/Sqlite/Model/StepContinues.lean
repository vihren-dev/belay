import Belay.Sqlite.Model.FailedStepFrame
import Belay.Sqlite.Model.OrdinaryStepEffects

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

/-- For every statement that resolves, has a clock value and reads only known counters, whose run is ready and
has no alternative execution, and whose output is not a stop of the model: the step continues,
with no further execution. In plain words, a statement that the model describes and that has one execution
gives a step that continues. The premises are the cases in which {name}`runScriptStep` ends the run, one
for each. Proof sketch: unfold the step; every case that ends the run is excluded by a premise; the
alternatives are empty, so the list of further executions is empty. -/
theorem runScriptStep_continues {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value}
    {resolved : Resolved.Statement} {after : ResolveState} {value : Int}
    (found : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    (timed : statementClock clock index resolved = some value)
    (known : connection.state.counters.firstUnknown resolved.counterReads = none)
    (ready : (connection.state.statementRun value parameters resolved).ready = true)
    (single : (connection.state.statementRun value parameters resolved).alternatives = [])
    (modeled : ∀ reason, Output.ofStep value parameters resolved connection.state
      (connection.state.statementRun value parameters resolved)
      (advanceRun index resolved connection.state (connection.state.statementRun value parameters resolved)) ≠
        .unmodeled reason) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] := by
  simp only [runScriptStep, runScriptStepWith, found, timed, known, ready, Bool.not_true, Bool.false_eq_true,
    ite_false, ranScriptStep]
  split
  · rename_i reason same
    exact absurd same (modeled reason)
  all_goals
    simp only [StatementExecution.ofAlternatives, single, List.mapM_nil, Except.map, pure, Except.pure,
      List.map_nil, RunStep.withOthers]
    exact ⟨_, _, rfl⟩

/-- For every statement that resolves to a statement that reads neither the clock nor a counter, whose run
at clock value 0 is ready and has no alternative execution, and whose output is not a stop of the model: the
step continues, with no further execution. In plain words, this is {name}`runScriptStep_continues` for the
statements that need no clock and no counter, which is every statement of a schema change or a transaction.
Proof sketch: the clock value is 0 and no counter is read, so the premises of
{name}`runScriptStep_continues` follow. -/
theorem runScriptStep_continues_free {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value}
    {resolved : Resolved.Statement} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    (free : resolved.readsClock = false) (noCounters : resolved.counterReads = [])
    (ready : (runStatement 0 (connection.state.counters.view []) parameters resolved connection.state.database).ready =
      true)
    (single : (runStatement 0 (connection.state.counters.view []) parameters resolved
      connection.state.database).alternatives = [])
    (modeled : ∀ reason, Output.ofStep 0 parameters resolved connection.state
      (connection.state.statementRun 0 parameters resolved)
      (advanceRun index resolved connection.state (connection.state.statementRun 0 parameters resolved)) ≠
        .unmodeled reason) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] := by
  have known : connection.state.counters.firstUnknown resolved.counterReads = none := by
    rw [noCounters]; rfl
  refine runScriptStep_continues found (by simp [statementClock, free]) known ?_ ?_ modeled
  · simp only [SqlState.statementRun, noCounters, ready, Bool.true_and]
    rfl
  · simpa [SqlState.statementRun, noCounters] using single

/-- For every connection, statement and values that resolve to a CREATE TABLE at the end of an aligned
catalog, at every clock: the step continues, with no further execution. In plain words, the model describes
CREATE TABLE whenever the resolver put the table at the end of the catalog and the rows have one list for each
catalog entry, which every valid database satisfies. Proof sketch: {name}`runScriptStep_continues_free`; the
effect succeeds on an aligned catalog. -/
theorem runScriptStep_createTable_continues {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {name : Identifier} {table : CatalogTable}
    (found : resolveStatement context connection.resolveState statement = .ok (.createTable target name table, after))
    (atEnd : target = connection.state.database.catalog.length)
    (aligned : connection.state.database.rows.length = connection.state.database.catalog.length) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] := by
  refine runScriptStep_continues_free found rfl rfl (by simp [runStatement]) (by simp [runStatement]) fun reason => ?_
  apply Output.ofStep_ne_unmodeled _ _ _ _ _ _ _ (by intro _ _ same; cases same) ?_ (by simp [statementOutput]) reason
  simp [advanceRun, advanceWith, SqlTransition.counted, SqlState.publish, haltError, SqlState.statementRun, runStatement,
    Model.step, atEnd, aligned]

/-- For every connection, statement and values that resolve to a DROP TABLE without rules, which is the
resolution while foreign-key enforcement is off: the step continues, with no further execution. In plain
words, the model describes a drop that no foreign key can cascade from. Proof sketch:
{name}`runScriptStep_continues_free`; the drop is an unconditional effect. -/
theorem runScriptStep_drop_continues {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {positions : List Nat}
    (found : resolveStatement context connection.resolveState statement = .ok (.drop positions none, after)) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] := by
  refine runScriptStep_continues_free found rfl rfl (by simp [runStatement, StatementRun.withKeys])
    (by simp [runStatement, StatementRun.withKeys]) fun reason => ?_
  apply Output.ofStep_ne_unmodeled _ _ _ _ _ _ _ (by intro _ _ same; cases same) ?_ (by simp [statementOutput]) reason
  simp [advanceRun, advanceWith, SqlTransition.counted, SqlState.publish, haltError, SqlState.statementRun, runStatement,
    Model.step, StatementRun.withKeys]

/-- For every connection, statement and values that resolve to a rewrite of the catalog that keeps the
outline of the catalog ({name}`Catalog.sameOutline`), as a rename does: the step continues, with no further
execution. In plain words, the model describes a rename whose new catalog has the outline of the old one.
Proof sketch: {name}`runScriptStep_continues_free`; the effect succeeds under the guard. -/
theorem runScriptStep_rewrite_continues {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {renamed : Catalog}
    (found : resolveStatement context connection.resolveState statement = .ok (.rewrite renamed, after))
    (outline : connection.state.database.catalog.sameOutline renamed = true) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] := by
  refine runScriptStep_continues_free found rfl rfl (by simp [runStatement]) (by simp [runStatement]) fun reason => ?_
  apply Output.ofStep_ne_unmodeled _ _ _ _ _ _ _ (by intro _ _ same; cases same) ?_ (by simp [statementOutput]) reason
  simp [advanceRun, advanceWith, SqlTransition.counted, SqlState.publish, haltError, SqlState.statementRun, runStatement,
    Model.step, outline]

/-- For every connection, statement and values that resolve to a setting: the step continues, with no further
execution. Proof sketch: {name}`runScriptStep_continues_free`; a setting keeps the database. -/
theorem runScriptStep_setting_continues {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {setting : Syntax.PragmaSetting} {on : Bool}
    (found : resolveStatement context connection.resolveState statement = .ok (.setting setting on, after)) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] := by
  refine runScriptStep_continues_free found rfl rfl (by simp [runStatement]) (by simp [runStatement]) fun reason => ?_
  apply Output.ofStep_ne_unmodeled _ _ _ _ _ _ _ (by intro _ _ same; cases same) ?_ (by simp [statementOutput]) reason
  simp [advanceRun, advanceWith, SqlTransition.counted, SqlState.publish, haltError, SqlState.statementRun, runStatement,
    Model.step]

/-- For every connection, statement and values that resolve to BEGIN, inside a transaction or outside one: the
step continues, with no further execution. In plain words, the model describes BEGIN in both cases: it opens a
transaction, or fails because one is open. Proof sketch: {name}`runScriptStep_continues_free`; the transition
continues or halts with an error that is no stop of the model. -/
theorem runScriptStep_begin_continues {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (.begin, after)) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] := by
  refine runScriptStep_continues_free found rfl rfl (by simp [runStatement]) (by simp [runStatement]) fun reason => ?_
  apply Output.ofStep_ne_unmodeled _ _ _ _ _ _ _ (by intro _ _ same; cases same) ?_ (by simp [statementOutput]) reason
  cases snapshot : connection.state.snapshot <;>
    simp [advanceRun, advanceWith, SqlTransition.counted, SqlState.finish, haltError, SqlState.statementRun,
      runStatement, snapshot]

/-- For every connection, statement and values that resolve to COMMIT, inside a transaction or outside one: the
step continues, with no further execution. In plain words, the model describes COMMIT in both cases: it closes
the transaction, or fails because none is open. Proof sketch: as {name}`runScriptStep_begin_continues`. -/
theorem runScriptStep_commit_continues {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (.commit, after)) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] := by
  refine runScriptStep_continues_free found rfl rfl (by simp [runStatement]) (by simp [runStatement]) fun reason => ?_
  apply Output.ofStep_ne_unmodeled _ _ _ _ _ _ _ (by intro _ _ same; cases same) ?_ (by simp [statementOutput]) reason
  cases snapshot : connection.state.snapshot <;>
    simp [advanceRun, advanceWith, SqlTransition.counted, haltError, SqlState.statementRun,
      runStatement, snapshot]

end Belay.Sqlite.Model
