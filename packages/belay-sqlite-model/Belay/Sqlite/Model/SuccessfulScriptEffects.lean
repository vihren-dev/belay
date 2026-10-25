import Belay.Sqlite.Model.QueryStepOutput
import Belay.Sqlite.Model.ScriptRunIndex
import Belay.Sqlite.Model.SqlStateLaws
import Belay.Sqlite.Model.Resolution.StatementCatalog
import Belay.Sqlite.Model.Resolution.ResolveStateSpec

set_option doc.verso true

/-! Recover the actual effect of a successful ordinary script step. These laws
follow the existing resolver and executor, so a proof about stored rows can
start from the public run's success without assuming the desired row relation. -/

namespace Belay.Sqlite.Model

/-- Every continuing script step comes from a successful resolution, an available
statement clock and counters, and a ready statement run. Its output and next
connection are exactly those of that run and its transition. SQL error outputs
are included here. Proof sketch: unfold the step; every earlier refusal ends
the run, and each remaining output carries the same transition. -/
theorem runScriptStep_ran {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection next : Connection} {statement : Syntax.Statement} {parameters : List Value}
    {output : Output}
    (step : runScriptStep context clock index connection statement parameters = .continued output next) :
    ∃ resolved after value,
      resolveStatement context connection.resolveState statement = .ok (resolved, after) ∧
      statementClock clock index resolved = some value ∧
      connection.state.counters.firstUnknown resolved.counterReads = none ∧
      (connection.state.statementRun value parameters resolved).ready = true ∧
      output = Output.ofStep value parameters resolved connection.state
        (connection.state.statementRun value parameters resolved)
        (advanceRun index resolved connection.state (connection.state.statementRun value parameters resolved)) ∧
      next = connection.afterStep after (connection.state.statementRun value parameters resolved).counts
        (advanceRun index resolved connection.state (connection.state.statementRun value parameters resolved)) := by
  unfold runScriptStep runScriptStepWith at step
  split at step
  · cases step
  · rename_i resolved after found
    split at step
    · cases step
    · rename_i value timed
      split at step
      · cases step
      · rename_i known
        dsimp only at step
        split at step
        · cases step
        · rename_i ready
          have ready : (connection.state.statementRun value parameters resolved).ready = true := by
            cases valueReady : (connection.state.statementRun value parameters resolved).ready <;>
              simp_all
          refine ⟨resolved, after, value, found, timed, known, ready, ?_⟩
          unfold ranScriptStep at step
          split at step <;> cases step <;> simp_all

/-- An ordinary statement's transition publishes its supplied effect, then
applies its supplied counts. Transaction control and connection-setting
statements are excluded by the ordinary premise. Proof sketch: every other statement has this defining arm. -/
theorem advanceRun_ordinary (index : Nat) (statement : Resolved.Statement)
    (state : SqlState) (run : StatementRun) (ordinary : statement.isControl = false) :
    advanceRun index statement state run = (state.publish index run.effect).counted run.counts := by
  cases statement <;> simp_all [Resolved.Statement.isControl, advanceRun, advanceWith]

/-- For every ordinary statement and supplied run, if its output is neither an
error nor an unmodeled stop, its effect succeeds with some database. The actual
transition retains the original snapshot and clock and applies exactly the
run's counts. This says nothing about whether the resolver admits the statement.
Proof sketch: a failed effect always publishes its error, contradicting one of
the output assumptions; a successful effect publishes the database and counts. -/
theorem successful_output_effect (value : Int) (parameters : List Value)
    (index : Nat) (statement : Resolved.Statement) (state : SqlState) (run : StatementRun)
    (ordinary : statement.isControl = false)
    (noError : (Output.ofStep value parameters statement state run
      (advanceRun index statement state run)).isError = false)
    (noStop : (Output.ofStep value parameters statement state run
      (advanceRun index statement state run)).endsRun = false) :
    ∃ database, run.effect = .ok database ∧
      advanceRun index statement state run =
        .next { state with database, counters := state.counters.apply run.counts } := by
  rw [advanceRun_ordinary index statement state run ordinary] at noError noStop ⊢
  cases effect : run.effect with
  | ok database => exact ⟨database, rfl, rfl⟩
  | error failure =>
    obtain ⟨reason, reached⟩ := failure
    have error : haltError ((state.publish index (.error (reason, reached))).counted run.counts) =
        some reason := by
      have halted (outcome : Outcome) : haltError (.halt outcome) = outcome.error? := by
        cases outcome <;> rfl
      simp only [SqlState.publish, SqlTransition.counted, halted]
      exact state.failed_error ..
    rw [effect] at noError noStop
    simp only [Output.ofStep, error] at noError noStop
    cases reason <;> simp_all [Output.isError, Output.endsRun]

/-- For an admitted resolution to an ordinary statement, a continuing error-free
step has a successful actual effect. Its next database is that effect's result;
its snapshot, state clock and connection settings are unchanged. Its counters
receive exactly the actual run's counts. The supplied statement clock is kept
in the conclusion instead of replacing the environment. Proof sketch: recover
the run, exclude failed effects by their outputs, then use the resolver's state
law and the successful transition. -/
theorem runScriptStep_effect {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection next : Connection} {statement : Syntax.Statement} {parameters : List Value}
    {output : Output} {resolved : Resolved.Statement} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    (ordinary : resolved.isControl = false)
    (step : runScriptStep context clock index connection statement parameters = .continued output next)
    (noError : output.isError = false) :
    ∃ value database,
      statementClock clock index resolved = some value ∧
      (connection.state.statementRun value parameters resolved).effect = .ok database ∧
      next = { connection with state := { connection.state with
        database := database
        counters := connection.state.counters.apply
          (connection.state.statementRun value parameters resolved).counts } } := by
  obtain ⟨actual, actualAfter, value, actualFound, timed, _, _, observed, advanced⟩ :=
    runScriptStep_ran step
  rw [found] at actualFound
  cases actualFound
  have noStop := (runScriptStep_continued step).2
  rw [observed] at noError noStop
  obtain ⟨database, effect, transition⟩ := successful_output_effect value parameters index
    resolved connection.state _ ordinary noError noStop
  refine ⟨value, database, timed, effect, ?_⟩
  rw [advanced, transition, resolveStatement_after context connection.resolveState after statement resolved found,
    ResolveState.after_of_isControl connection.resolveState ordinary]
  rfl

/-- If a nonempty script has only modeled, error-free outputs, its first step
continues without an error and its remaining run has the same success property.
The exact output and reached connection are witnesses. Proof sketch: an ended
first step contradicts success; a continuing step exposes the list conjunction. -/
theorem successful_script_cons {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value}
    {rest : List (Syntax.Statement × List Value)}
    (success : (runScriptFrom context clock index connection ((statement, parameters) :: rest)).outputs.all
      (fun output => !output.isError && !output.endsRun) = true) :
    ∃ output next,
      runScriptStep context clock index connection statement parameters = .continued output next ∧
      output.isError = false ∧
      (runScriptFrom context clock (index + 1) next rest).outputs.all
        (fun output => !output.isError && !output.endsRun) = true := by
  cases step : runScriptStep context clock index connection statement parameters with
  | ended reason => simp [runScriptFrom, step, Output.isError, Output.endsRun] at success
  | continued output next =>
    simp only [runScriptFrom, step, List.all_cons, Bool.and_eq_true,
      Bool.not_eq_true'] at success
    exact ⟨output, next, rfl, success.1.1, success.2⟩

end Belay.Sqlite.Model
