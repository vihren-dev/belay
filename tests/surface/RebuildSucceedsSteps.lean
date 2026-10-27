import RebuildSucceedsCopy

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-! Claim 2 of the guide's table rebuild, the first statements (ADR 0017, S6, part 3). {lit}`Good` joins the facts
that every step keeps ({lit}`Kept`) with the facts about the customers ({lit}`Held`). For each statement of the
rebuild, the lemmas {lit}`good_0` to {lit}`good_4` (here) and {lit}`good_5` to {lit}`good_8` ({lit}`RebuildSucceedsFinish`)
show that the step continues without an error and that every execution of it keeps the facts, from every connection
that has them. They use the success laws of the model for the pragma, BEGIN, CREATE TABLE and DROP statements. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace RebuildGuide

/-- For a table of the sessions, a table of the customers, a number of statements and a connection: the facts of
{name}`Kept` and of {name}`Held` both hold. -/
def Good (sessions customers : Table) (count : Nat) (connection : Connection) : Prop :=
  Kept sessions count connection ∧ Held customers count connection

/-- The output of the single execution of a step with no further execution is the output of the step. -/
theorem single_output {output : Output} {next : Connection} {found : StatementExecution}
    (member : found ∈ (RunStep.continued output next []).executions) : found.output = output := by
  simp only [RunStep.executions, List.mem_singleton] at member
  rw [member]

/-- For a step that continues with one execution that has no error: if the facts of {name}`Kept` hold after the step
in every execution that has no error, and the facts of {name}`Held` hold for the next connection, every execution of the
step has no error output and reaches a connection with {name}`Good`. Proof sketch: the one execution has the output and
the connection of the step. -/
theorem good_step {sessions customers : Table} {count : Nat} {output : Output} {next : Connection}
    (noError : output.isError = false)
    (kept : ∀ found ∈ (RunStep.continued output next []).executions, found.output.isError = false →
      Kept sessions (count + 1) found.next)
    (held : Held customers (count + 1) next) :
    ∀ found ∈ (RunStep.continued output next []).executions,
      found.output.isError = false ∧ Good sessions customers (count + 1) found.next := by
  intro found member
  have err : found.output.isError = false := by rw [single_output member]; exact noError
  exact ⟨err, kept found member err, by rw [single_next member]; exact held⟩

/-- Statement 0, {lit}`PRAGMA foreign_keys = OFF`: the step continues without an error in every execution, and the
facts hold after it. The customers are not changed. Proof sketch: {name}`runScriptStep_setting_ok` and
{name}`runScriptStep_setting_frame`, with {name}`advance_0`. -/
theorem good_0 {clock : Option Clock} {index : Nat} {c : Connection} {sessions customers : Table}
    (good : Good sessions customers 0 c) :
    ∃ output next, runScriptStep runContext clock index c requireName.statements[0].1 requireName.statements[0].2 =
      .continued output next [] ∧ ∀ found ∈ (RunStep.continued output next []).executions,
        found.output.isError = false ∧ Good sessions customers 1 found.next := by
  obtain ⟨output, next, step, noError⟩ := runScriptStep_setting_ok (context := runContext) (clock := clock) (index := index)
    (statement := requireName.statements[0].1) (parameters := requireName.statements[0].2)
    (found := by rw [good.1.1]; with_unfolding_all exact rfl)
  have frame := runScriptStep_setting_frame (found := by rw [good.1.1]; with_unfolding_all exact rfl) step
  refine ⟨output, next, step, good_step noError (advance_0 good.1 step) ⟨fun _ => ?_, fun h => by omega⟩⟩
  rw [frame]; exact good.2.1 (by omega)

/-- Statement 1, {lit}`BEGIN`: the step continues without an error in every execution, and the facts hold after it.
The transaction is closed before it, as the resolution state shows. Proof sketch: {name}`runScriptStep_begin_ok` and
{name}`runScriptStep_begin_frame`, with {name}`advance_1`. -/
theorem good_1 {clock : Option Clock} {index : Nat} {c : Connection} {sessions customers : Table}
    (good : Good sessions customers 1 c) :
    ∃ output next, runScriptStep runContext clock index c requireName.statements[1].1 requireName.statements[1].2 =
      .continued output next [] ∧ ∀ found ∈ (RunStep.continued output next []).executions,
        found.output.isError = false ∧ Good sessions customers 2 found.next := by
  have idle : c.state.snapshot = none := by
    have closed : (reachedAfter 1).resolveState.saved = none := by with_unfolding_all rfl
    have h2 := (resolveState_parts good.1.1).2.1
    rw [closed] at h2
    simpa using h2
  obtain ⟨output, next, step, noError⟩ := runScriptStep_begin_ok (context := runContext) (clock := clock) (index := index)
    (statement := requireName.statements[1].1) (parameters := requireName.statements[1].2)
    (found := by rw [good.1.1]; with_unfolding_all exact rfl) idle
  have frame := runScriptStep_begin_frame (found := by rw [good.1.1]; with_unfolding_all exact rfl) step
  refine ⟨output, next, step, good_step noError (advance_1 good.1 step) ⟨fun _ => ?_, fun h => by omega⟩⟩
  rw [frame]; exact good.2.1 (by omega)

/-- Statement 2, the CREATE TABLE of the new customers: the step continues without an error in every execution, and
the facts hold after it. The customers are not changed, and the new table holds no row. Proof sketch:
{name}`runScriptStep_createTable_ok` for the position at the end of the catalog, which is 2, and the shape of the rows
of a valid database; {name}`runScriptStep_createTable` gives the next database, with the rows of the customers as they
were and one empty list of rows appended. -/
theorem good_2 {clock : Option Clock} {index : Nat} {c : Connection} {sessions customers : Table}
    (good : Good sessions customers 2 c) (valid : c.state.Holds (Database.Valid Profile.pinned)) :
    ∃ output next, runScriptStep runContext clock index c requireName.statements[2].1 requireName.statements[2].2 =
      .continued output next [] ∧ ∀ found ∈ (RunStep.continued output next []).executions,
        found.output.isError = false ∧ Good sessions customers 3 found.next := by
  have length : c.state.database.catalog.length = 2 := by
    rw [(resolveState_parts good.1.1).1]; with_unfolding_all rfl
  obtain ⟨output, next, step, noError⟩ := runScriptStep_createTable_ok (context := runContext) (clock := clock) (index := index)
    (statement := requireName.statements[2].1) (parameters := requireName.statements[2].2)
    (found := by rw [good.1.1]; with_unfolding_all exact rfl) (by rw [length]; with_unfolding_all rfl)
    (by rw [length]; exact length ▸ valid.1.admitted.rowsShaped.1)
  obtain ⟨-, -, -, aligned, nextEq⟩ := runScriptStep_createTable
    (found := by rw [good.1.1]; with_unfolding_all exact rfl) step
  refine ⟨output, next, step, good_step noError (advance_2 good.1 step) ⟨fun _ => ?_, fun _ => ?_⟩⟩
  · exact runScriptStep_createTable_frame (found := by rw [good.1.1]; with_unfolding_all exact rfl) step
      (good.2.1 (by omega))
  · rw [nextEq]
    simp [List.getD_eq_getElem?_getD, aligned, length]

/-- Statement 3, the INSERT from a query: the step continues without an error in its first execution when no old
customer lacks a name, and every execution that has no error keeps the facts. The execution of the model is the only
one that the model describes. Proof sketch: {name}`copy_continues` and {name}`advance_3`; the facts about the customers
end with the copy. -/
theorem good_3 {clock : Option Clock} {index : Nat} {c : Connection} {sessions customers : Table}
    (good : Good sessions customers 3 c) (valid : c.state.Holds (Database.Valid Profile.pinned))
    (named : ∀ row ∈ customers.rows, row.values[1]? ≠ some .null) :
    ∃ output next, runScriptStep runContext clock index c requireName.statements[3].1 requireName.statements[3].2 =
      .continued output next [] ∧ ∀ found ∈ (RunStep.continued output next []).executions,
        found.output.isError = false ∧ Good sessions customers 4 found.next := by
  obtain ⟨output, next, step, noError⟩ := copy_continues good.1 good.2 valid named
  exact ⟨output, next, step, good_step noError (advance_3 good.1 step) ⟨fun h => by omega, fun h => by omega⟩⟩

/-- Statement 4, the DROP of the old customers: the step continues without an error in every execution, and the
facts hold after it. Proof sketch: {name}`runScriptStep_drop_ok` and {name}`advance_4`; the facts about the customers
end with the copy. -/
theorem good_4 {clock : Option Clock} {index : Nat} {c : Connection} {sessions customers : Table}
    (good : Good sessions customers 4 c) :
    ∃ output next, runScriptStep runContext clock index c requireName.statements[4].1 requireName.statements[4].2 =
      .continued output next [] ∧ ∀ found ∈ (RunStep.continued output next []).executions,
        found.output.isError = false ∧ Good sessions customers 5 found.next := by
  obtain ⟨output, next, step, noError⟩ := runScriptStep_drop_ok (context := runContext) (clock := clock) (index := index)
    (statement := requireName.statements[4].1) (parameters := requireName.statements[4].2)
    (found := by rw [good.1.1]; with_unfolding_all exact rfl)
  exact ⟨output, next, step, good_step noError (advance_4 good.1 step) ⟨fun h => by omega, fun h => by omega⟩⟩

end RebuildGuide
