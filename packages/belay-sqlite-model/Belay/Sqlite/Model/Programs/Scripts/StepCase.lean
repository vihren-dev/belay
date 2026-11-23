import Belay.Sqlite.Model.Programs.Scripts.ScriptRun

set_option doc.verso true

/-! The part of a case type that all statement kinds share (statement rule pilot, "Case type of plain INSERT"). After
the resolution, the step function {lit}`runScriptStepWith` checks the clock and the counters of each resolved
statement before the statement runs. {lit}`StepCase` states these two checks once, as two cases, and takes the
cases of one statement kind as a parameter for the inputs that pass them. The case type of a kind is
{lit}`StepCase` with the cases of that kind. -/

namespace Belay.Sqlite.Model

/-- The cases of the step of a resolved statement, for the clock, the index and the connection. The parameter
{lit}`kindCase` gives the cases of the statement kind: {lit}`kindCase value result` says that, at the clock value,
the run of the statement gives the result. A result is in a case when one of these holds:
* {lit}`noClock`: the statement has no clock value ({name}`statementClock`), and the result is the end of the run
  with {name}`clockUnmodeled`;
* {lit}`unknownCounter`: the statement has a clock value, the connection does not know a counter that the
  statement reads, and the result is the end of the run with {name}`counterUnknownReason` of the first such counter
  in the list {name}`Resolved.Statement.counterReads` ({name}`Counters.firstUnknown`);
* {lit}`checked`: the statement has the clock value, no counter that it reads is unknown, and the kind relates the
  clock value to the result. -/
inductive StepCase (clock : Option Clock) (index : Nat) (connection : Connection) (resolved : Resolved.Statement)
    (kindCase : Int → RunStep → Prop) : RunStep → Prop where
  /-- The statement reads the clock and the run has no clock value for it, so the run ends. -/
  | noClock (timed : statementClock clock index resolved = none) :
      StepCase clock index connection resolved kindCase (.ended clockUnmodeled)
  /-- The statement has a clock value and reads a counter that the connection does not know, so the run ends with
  the reason of the first such counter in the list of the counters that it reads. -/
  | unknownCounter {value : Int} {kind : CounterKind} (timed : statementClock clock index resolved = some value)
      (unknown : connection.state.counters.firstUnknown resolved.counterReads = some kind) :
      StepCase clock index connection resolved kindCase (.ended (counterUnknownReason kind))
  /-- The statement passes both checks at the clock value, and the cases of its kind give the result. -/
  | checked {value : Int} {result : RunStep} (timed : statementClock clock index resolved = some value)
      (known : connection.state.counters.firstUnknown resolved.counterReads = none) (case : kindCase value result) :
      StepCase clock index connection resolved kindCase result

/-- For every clock, index, connection, resolved statement, cases of a kind and function {lit}`body` from clock
values to results: if, for each clock value that the statement has, when the connection knows each counter that
the statement reads, the kind relates the clock value to the result of {lit}`body` at it, then the case type
relates the inputs to this result:
* the end of the run with {name}`clockUnmodeled` when the statement has no clock value;
* else the end of the run with {name}`counterUnknownReason` of the first counter in the list
  {name}`Resolved.Statement.counterReads` that the connection does not know, when there is one;
* else {lit}`body` at the clock value.
Only the last result needs the premise. In plain words, a step that makes the two checks and then gives the
function of the clock value is in a case, when the kind covers the function. Use it to prove the cover of a kind
from its kind rule. Proof sketch: split on the clock value and on the first unknown counter; each branch is one
constructor. -/
theorem StepCase.of_checks {clock : Option Clock} {index : Nat} {connection : Connection}
    {resolved : Resolved.Statement} {kindCase : Int → RunStep → Prop} {body : Int → RunStep}
    (kind : ∀ value, statementClock clock index resolved = some value →
      connection.state.counters.firstUnknown resolved.counterReads = none → kindCase value (body value)) :
    StepCase clock index connection resolved kindCase
      (match statementClock clock index resolved with
       | none => .ended clockUnmodeled
       | some value => match connection.state.counters.firstUnknown resolved.counterReads with
         | some kind => .ended (counterUnknownReason kind)
         | none => body value) := by
  cases timed : statementClock clock index resolved with
  | none => exact .noClock timed
  | some value =>
    cases known : connection.state.counters.firstUnknown resolved.counterReads with
    | some kind => exact .unknownCounter timed known
    | none => exact .checked timed known (kind value timed known)

/-- For every clock, index, connection, resolved statement and cases of a kind: if, for every integer clock value,
the kind relates that value to at most one result, then two results that the case type relates to the inputs are
equal. In plain words, one result of the kind gives one result of the step. The premise is for every integer, also
when the statement has no clock value; the proof uses it only when both results are in the case {lit}`checked`.
Proof sketch: the clock value and the first unknown counter select the same constructor on both sides. -/
theorem StepCase.unique {clock : Option Clock} {index : Nat} {connection : Connection}
    {resolved : Resolved.Statement} {kindCase : Int → RunStep → Prop}
    (kindUnique : ∀ value first second, kindCase value first → kindCase value second → first = second)
    {first second : RunStep} :
    StepCase clock index connection resolved kindCase first → StepCase clock index connection resolved kindCase second →
      first = second
  | .noClock _, .noClock _ => rfl
  | .noClock timed, .unknownCounter other _ | .noClock timed, .checked other _ _ => by simp [timed] at other
  | .unknownCounter timed _, .noClock other | .checked timed _ _, .noClock other => by simp [timed] at other
  | .unknownCounter _ unknown, .unknownCounter _ other => by rw [unknown] at other; cases other; rfl
  | .unknownCounter _ unknown, .checked _ known _ | .checked _ known _, .unknownCounter _ unknown => by
    simp [unknown] at known
  | .checked timed _ case, .checked other _ next => by
    rw [timed] at other
    cases other
    exact kindUnique _ _ _ case next

/-- For every result of a step, every given result and every relation on results: if the step is in the relation
(cover), the relation holds for no more than one result (one result), and it holds for the given result, then the
step is the given result. In plain words, a case type that covers the step and gives one result gives the
equation of the step for each of its cases. The theorem holds for each statement kind. Proof: one result applied
to the step and the given result. -/
theorem RunStep.eq_of_cover {step result : RunStep} {cases : RunStep → Prop} (cover : cases step)
    (unique : ∀ first second, cases first → cases second → first = second) (case : cases result) : step = result :=
  unique step result cover case

end Belay.Sqlite.Model
