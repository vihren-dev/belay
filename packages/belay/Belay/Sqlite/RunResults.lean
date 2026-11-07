import Belay.Sqlite.ProgramRun
import Belay.Sqlite.Model.QueryOutputs

set_option doc.verso true

/-! Successful-result observations of a run (ADR 0027, D2): {lit}`run.returnsResult Q` says that the
run gives one statement output, which is one result with the property {lit}`Q` or a nonempty choice
of results that all have it; {lit}`run.returnsRows P` asks {lit}`P` of each row; {lit}`run.returnsError E`
says that the one output is an error with a code that satisfies {lit}`E`. Each one is decidable when
its property is, so {lit}`decide` checks it on a concrete database. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- {lit}`run.returnsResult Q`: the run gave a value, and it has exactly one output, which returns
a result with the property {lit}`Q` ({name}`Output.returnsResult`). In terms of the formula:

* the value of the run is some value, so no statement ended the run;
* the outputs are one output: {name}`Output.rows` with rows that satisfy {lit}`Q`, or
  {name}`Output.oneOf` with a nonempty list of results that all satisfy {lit}`Q`.

An error, {name}`Output.done`, {name}`Output.unmodeled`, an empty choice, no output and more than
one output are all false, for every {lit}`Q`. For example, the run of {lit}`SELECT 1` returns the
result {lit}`[[1]]`. Use {lit}`fun _ => True` when only a successful result matters. -/
def Run.returnsResult {α : Type} (run : Run α) (property : List (List Value) → Prop) : Prop :=
  run.value.isSome = true ∧ match run.outputs with
    | [output] => output.returnsResult property
    | [] | _ :: _ :: _ => False

/-- {lit}`run.returnsRows P`: the run returns a result ({name}`Run.returnsResult`) in which each row
satisfies {lit}`P`, for each result that the model permits. A result without rows satisfies it, so
this claim does not say that a row exists; combine it with {name}`Run.returnsResult` for that. -/
abbrev Run.returnsRows {α : Type} (run : Run α) (property : List Value → Prop) : Prop :=
  run.returnsResult fun rows => ∀ row ∈ rows, property row

/-- {lit}`run.returnsError E`: the run gave a value, and it has exactly one output, which is an error
({name}`Output.error`) with a result code that satisfies {lit}`E` ({name}`Output.returnsError`).
Every other output, no output and more than one output are false. Use {lit}`fun _ => True` for any
error. -/
def Run.returnsError {α : Type} (run : Run α) (property : Nat → Prop) : Prop :=
  run.value.isSome = true ∧ match run.outputs with
    | [output] => output.returnsError property
    | [] | _ :: _ :: _ => False

instance {α : Type} (run : Run α) (property : List (List Value) → Prop) [DecidablePred property] :
    Decidable (run.returnsResult property) :=
  match outputs : run.outputs with
  | [output] =>
    if found : run.value.isSome = true ∧ output.returnsResult property then
      isTrue ⟨found.1, by rw [outputs]; exact found.2⟩
    else isFalse fun ⟨valued, holds⟩ => found ⟨valued, by rw [outputs] at holds; exact holds⟩
  | [] | _ :: _ :: _ => isFalse fun ⟨_, holds⟩ => by rw [outputs] at holds; exact holds

instance {α : Type} (run : Run α) (property : Nat → Prop) [DecidablePred property] :
    Decidable (run.returnsError property) :=
  match outputs : run.outputs with
  | [output] =>
    if found : run.value.isSome = true ∧ output.returnsError property then
      isTrue ⟨found.1, by rw [outputs]; exact found.2⟩
    else isFalse fun ⟨valued, holds⟩ => found ⟨valued, by rw [outputs] at holds; exact holds⟩
  | [] | _ :: _ :: _ => isFalse fun ⟨_, holds⟩ => by rw [outputs] at holds; exact holds

/-- For every run and property, {name}`Run.returnsResult` holds exactly when the value of the run is
some value and the outputs are one output that returns a result with the property. Proof sketch: by
the cases of the output list. -/
theorem Run.returnsResult_iff {α : Type} (run : Run α) (property : List (List Value) → Prop) :
    run.returnsResult property ↔
      run.value.isSome = true ∧ ∃ output, run.outputs = [output] ∧ output.returnsResult property := by
  unfold Run.returnsResult
  split <;> simp_all

/-- For every run and two properties {lit}`P` and {lit}`Q` of a result: if every result with
{lit}`P` has {lit}`Q`, a run that returns a result with {lit}`P` returns a result with {lit}`Q`. For
example, a result that is a permutation of a list has its length. Proof sketch: the same output, and
for a choice the same nonempty list of results. -/
theorem Run.returnsResult.mono {α : Type} {run : Run α} {stronger weaker : List (List Value) → Prop}
    (holds : run.returnsResult stronger) (implies : ∀ result, stronger result → weaker result) :
    run.returnsResult weaker := by
  obtain ⟨valued, output, outputs, returned⟩ := (Run.returnsResult_iff run stronger).mp holds
  refine (Run.returnsResult_iff run weaker).mpr ⟨valued, output, outputs, ?_⟩
  cases output with
  | rows found => exact implies found returned
  | oneOf results => exact ⟨returned.1, fun result member => implies result (returned.2 result member)⟩
  | done _ | error _ | unmodeled _ => exact returned

/-- For every run and property, {name}`Run.returnsError` holds exactly when the value of the run is
some value and the outputs are one output that is an error with a code that has the property. Proof
sketch: by the cases of the output list. -/
theorem Run.returnsError_iff {α : Type} (run : Run α) (property : Nat → Prop) :
    run.returnsError property ↔
      run.value.isSome = true ∧ ∃ output, run.outputs = [output] ∧ output.returnsError property := by
  unfold Run.returnsError
  split <;> simp_all

end Belay.Sqlite
