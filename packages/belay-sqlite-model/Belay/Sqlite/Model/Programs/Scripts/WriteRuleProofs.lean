import Belay.Sqlite.Model.Programs.Scripts.UpsertRule

set_option doc.verso true

/-! Shared proof obligations for the clock, counters and the one execution of an ordinary write. -/

namespace Belay.Sqlite.Model

/-- For every resolution, the missing clock and first unknown counter end the step with their
reasons. It suffices to compute the remaining result at each clock value with known counters.
Proof sketch: reduce the step at the given resolution and take the two guards in order. -/
theorem runScriptStep_of_clock_counter {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value}
    {resolved : Resolved.Statement} {after : ResolveState} {rest : Int → RunStep}
    (found : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    (compute : ∀ value, connection.state.counters.firstUnknown resolved.counterReads = none →
      let run := connection.state.statementRun value parameters resolved
      (if run.ready then ranScriptStep index parameters connection resolved after value run
        (advanceRun index resolved connection.state run) else .ended unmodeledHere) = rest value) :
    runScriptStep context clock index connection statement parameters =
      match statementClock clock index resolved with
      | none => .ended clockUnmodeled
      | some value => match connection.state.counters.firstUnknown resolved.counterReads with
        | some kind => .ended (counterUnknownReason kind)
        | none => rest value := by
  simp only [runScriptStep, runScriptStepWith, found]
  cases statementClock clock index resolved with
  | none => rfl
  | some value =>
    cases known : connection.state.counters.firstUnknown resolved.counterReads with
    | some => rfl
    | none =>
      have result := compute value known
      cases ready : (connection.state.statementRun value parameters resolved).ready <;> simpa [ready] using result

/-- An ordinary write with one execution, a post-resolution state differing only by application of its
catalog edit, installs its database and applies its counts on success. The proposed
output is modeled. For each successful effect, {name}`Output.ofStep` after advancing the run
gives that output. Its unmodeled effect ends the step. Each modeled refusal
gives the primary code and the connection selected by the conflict algorithm.
Proof sketch: a successful effect advances to the published state. A failed effect halts,
and the halted state's reason determines the output. -/
theorem ranScriptStep_write {index : Nat} {connection : Connection} {resolved : Resolved.Statement}
    {after : ResolveState} {value : Int} {parameters : List Value} {run : StatementRun} {output : Output}
    (ordinary : resolved.isControl = false)
    (same : after = { connection.resolveState with catalog := resolved.applyCatalog connection.resolveState.catalog })
    (single : run.alternatives = []) (observed : ∀ reason, output ≠ .unmodeled reason)
    (success : ∀ db, run.effect = .ok db →
      Output.ofStep value parameters resolved connection.state run (advanceRun index resolved connection.state run) = output) :
    ranScriptStep index parameters connection resolved after value run (advanceRun index resolved connection.state run) =
      match run.effect with
      | .ok db => .continued output (connection.afterWrite db run.counts) []
      | .error (reason, reached) => if reason = .unmodeled then .ended unmodeledHere else
        .continued (.error reason.primaryCode) (connection.afterWriteError index reason reached run.counts) [] := by
  have others := StatementExecution.ofAlternatives_of_single index parameters connection resolved after value single
  unfold ranScriptStep
  cases effect : run.effect with
  | ok db =>
    rw [success db effect, advanceRun_ordinary _ _ _ _ ordinary, effect, others]
    cases output <;> first | exact False.elim (observed _ rfl) | subst after; rfl
  | error pair =>
    obtain ⟨reason, reached⟩ := pair
    rw [advanceRun_ordinary _ _ _ _ ordinary, effect, others]
    cases reason <;> simp [Output.ofStep, SqlState.publish, SqlTransition.counted, haltError_failed,
      Except.map, RunStep.withOthers, Connection.afterStep, Connection.afterWriteError, same, Connection.resolveState] <;> rfl

/-- Suppose a statement resolves to a non-control operation outside the source writes that
can have alternative executions ({name}`Resolved.Statement.fromQuery`). At every clock value,
for any run and any database it can publish successfully, its output must equal the supplied
modeled output. For example, an INSERT with a trigger can supply its direct change count.
Compute {lit}`rest` from the raw run at each clock value. An unsupported run or unmodeled
error ends the step. A success publishes the database and counts. A modeled error applies
the conflict transition. Then a missing required clock or an unknown counter ends the
resolved step with its reason, and when both checks pass the step equals {lit}`rest`.
Proof sketch: apply {name}`runScriptStep_of_clock_counter` to the resolution and
{name}`ranScriptStep_write` to the single execution. -/
theorem runScriptStep_of_single_write {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value}
    {resolved : Resolved.Statement} {after : ResolveState} {rest : Int → RunStep}
    (found : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    (ordinary : resolved.isControl = false) (single : resolved.fromQuery = false)
    {output : Int → StatementRun → Output}
    (success : ∀ value run db, Output.ofStep value parameters resolved connection.state run
      ((connection.state.publish index (.ok db)).counted run.counts) = output value run)
    (modeled : ∀ value run reason, output value run ≠ .unmodeled reason)
    (compute : ∀ value,
      let run := runStatement value (connection.state.counters.view resolved.counterReads) parameters
        resolved connection.state.database
      (if run.ready then match run.effect with
        | .ok db => .continued (output value run) (connection.afterWrite db run.counts) []
        | .error (reason, reached) => if reason = .unmodeled then .ended unmodeledHere else
          .continued (.error reason.primaryCode) (connection.afterWriteError index reason reached run.counts) []
       else .ended unmodeledHere) = rest value) :
    runScriptStep context clock index connection statement parameters =
      match statementClock clock index resolved with
      | none => .ended clockUnmodeled
      | some value => match connection.state.counters.firstUnknown resolved.counterReads with
        | some kind => .ended (counterUnknownReason kind)
        | none => rest value := by
  apply runScriptStep_of_clock_counter found
  intro value known
  have same := (resolveStatement_certificate context connection.resolveState after statement _ found).after
  rw [ResolveState.after_of_isControl connection.resolveState ordinary] at same
  dsimp only
  rw [ranScriptStep_write ordinary same (connection.state.statementRun_alternatives value parameters resolved none single)
    (modeled value _) (fun db effect => by
      rw [advanceRun_ordinary _ _ _ _ ordinary, effect]
      exact success value _ db)]
  simpa only [SqlState.statementRun, known, Option.isNone_none, Bool.and_true] using compute value

end Belay.Sqlite.Model
