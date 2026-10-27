import RebuildSucceedsSteps
import RebuildKeepsFinish

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-! Claim 2 of the guide's table rebuild, the last statements (ADR 0017, S6, part 3). The lemmas {lit}`good_5` to
{lit}`good_8` continue {lit}`RebuildSucceedsSteps`: the rename, the check of the foreign keys, COMMIT and the last
pragma. {lit}`good_advance` joins the nine statements, in the form that {lit}`sendStatements_succeedsFrom` takes. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace RebuildGuide

/-- Whether the rename of the rebuild resolves, on the resolution state after the first five statements, to a new
catalog that has the outline of the old one ({name}`Catalog.sameOutline`). -/
def renameKeepsOutline : Bool :=
  match resolveStatement runContext (reachedAfter 5).resolveState requireName.statements[5].1 with
  | .ok (.rewrite renamed, _) => (reachedAfter 5).resolveState.catalog.sameOutline renamed
  | .ok (.query .., _) | .ok (.createView .., _) | .ok (.createTable .., _) | .ok (.createIndex .., _)
  | .ok (.createTrigger .., _) | .ok (.addColumn .., _) | .ok (.dropColumn .., _) | .ok (.drop .., _) | .ok (.begin, _)
  | .ok (.commit, _) | .ok (.rollback, _) | .ok (.insert .., _) | .ok (.update .., _) | .ok (.upsert .., _)
  | .ok (.insertSelect .., _) | .ok (.delete .., _) | .ok (.prepareError _, _) | .ok (.setting .., _) | .error _ => false

/-- The rename resolves to a new catalog that has the outline of the old one. Proof sketch: kernel evaluation of
{name}`renameKeepsOutline`. -/
theorem rename_resolves : ∃ renamed after,
    resolveStatement runContext (reachedAfter 5).resolveState requireName.statements[5].1 = .ok (.rewrite renamed, after) ∧
      (reachedAfter 5).resolveState.catalog.sameOutline renamed = true := by
  have ok : renameKeepsOutline = true := by decide +kernel
  unfold renameKeepsOutline at ok
  split at ok
  · rename_i renamed after resolved
    exact ⟨renamed, after, resolved, ok⟩
  all_goals simp at ok

/-- Statement 5, the rename of the new customers: the step continues without an error in every execution, and the
facts hold after it. Proof sketch: {name}`runScriptStep_rewrite_ok`, where the new catalog has the outline of the
old one by evaluation, and {name}`advance_5`. -/
theorem good_5 {clock : Option Clock} {index : Nat} {c : Connection} {sessions customers : Table}
    (good : Good sessions customers 5 c) :
    ∃ output next, runScriptStep runContext clock index c requireName.statements[5].1 requireName.statements[5].2 =
      .continued output next [] ∧ ∀ found ∈ (RunStep.continued output next []).executions,
        found.output.isError = false ∧ Good sessions customers 6 found.next := by
  obtain ⟨renamed, after, resolved, outline⟩ := rename_resolves
  obtain ⟨output, next, step, noError⟩ := runScriptStep_rewrite_ok (context := runContext) (clock := clock)
    (index := index) (statement := requireName.statements[5].1) (parameters := requireName.statements[5].2)
    (found := by rw [good.1.1]; exact resolved) (by rw [(resolveState_parts good.1.1).1]; exact outline)
  exact ⟨output, next, step, good_step noError (advance_5 good.1 step) ⟨fun h => by omega, fun h => by omega⟩⟩

/-- Statement 6, {lit}`PRAGMA foreign_key_check`: the step continues without an error in every execution, and the
facts hold after it. The check gives rows for the sessions only, so the model describes its result. Proof sketch:
in the catalog of the state, only the sessions have a foreign key, so no other table gives rows
({name}`Database.foreignKeyCheckRows_isSome`); then {name}`runScriptStep_keyCheck_continues` and {name}`advance_6`. -/
theorem good_6 {clock : Option Clock} {index : Nat} {c : Connection} {sessions customers : Table}
    (good : Good sessions customers 6 c) :
    ∃ output next, runScriptStep runContext clock index c requireName.statements[6].1 requireName.statements[6].2 =
      .continued output next [] ∧ ∀ found ∈ (RunStep.continued output next []).executions,
        found.output.isError = false ∧ Good sessions customers 7 found.next := by
  have catalog := (resolveState_parts good.1.1).1
  have links : c.state.database.catalog.foreignKeyLinks.all (·.child == 0) = true := by
    rw [catalog]; decide +kernel
  obtain ⟨rows, found⟩ := Database.foreignKeyCheckRows_isSome c.state.database 0 (by
    intro position table differs _
    have notChild : childLinks c.state.database.catalog.foreignKeyLinks position = [] := by
      unfold childLinks
      rw [List.filter_eq_nil_iff.mpr (fun link member => by
        have zero := List.all_eq_true.mp links link member
        simp only [beq_iff_eq] at zero ⊢
        omega)]
      rfl
    simp [Database.keyCheckRows, notChild])
  have statement : requireName.statements[6] = (.pragma (.foreignKeyCheck none), []) := by with_unfolding_all rfl
  obtain ⟨output, step, noError⟩ := runScriptStep_keyCheck_continues runContext clock index c [] rows
    (by rw [catalog]; decide +kernel) found
  have step' : runScriptStep runContext clock index c requireName.statements[6].1 requireName.statements[6].2 =
      .continued output c [] := by rw [statement]; exact step
  exact ⟨output, c, step', good_step noError (advance_6 good.1 step') ⟨fun h => by omega, fun h => by omega⟩⟩

/-- Statement 7, {lit}`COMMIT`: the step continues without an error in every execution, and the facts hold after it.
The transaction is open before it, as the resolution state shows. Proof sketch: {name}`runScriptStep_commit_ok` and
{name}`advance_7`. -/
theorem good_7 {clock : Option Clock} {index : Nat} {c : Connection} {sessions customers : Table}
    (good : Good sessions customers 7 c) :
    ∃ output next, runScriptStep runContext clock index c requireName.statements[7].1 requireName.statements[7].2 =
      .continued output next [] ∧ ∀ found ∈ (RunStep.continued output next []).executions,
        found.output.isError = false ∧ Good sessions customers 8 found.next := by
  have active : ∃ original, c.state.snapshot = some original := by
    have open_ : ∃ catalog, (reachedAfter 7).resolveState.saved = some catalog := by
      with_unfolding_all exact ⟨_, rfl⟩
    obtain ⟨catalog, saved⟩ := open_
    have h2 := (resolveState_parts good.1.1).2.1
    rw [saved] at h2
    cases snapshot : c.state.snapshot with
    | none => simp [snapshot] at h2
    | some original => exact ⟨original, rfl⟩
  obtain ⟨original, active⟩ := active
  obtain ⟨output, next, step, noError⟩ := runScriptStep_commit_ok (context := runContext) (clock := clock)
    (index := index) (statement := requireName.statements[7].1) (parameters := requireName.statements[7].2)
    (found := by rw [good.1.1]; with_unfolding_all exact rfl) active
  exact ⟨output, next, step, good_step noError (advance_7 good.1 step) ⟨fun h => by omega, fun h => by omega⟩⟩

/-- Statement 8, {lit}`PRAGMA foreign_keys = ON`: the step continues without an error in every execution, and the
facts hold after it. Proof sketch: {name}`runScriptStep_setting_ok` and {name}`advance_8`. -/
theorem good_8 {clock : Option Clock} {index : Nat} {c : Connection} {sessions customers : Table}
    (good : Good sessions customers 8 c) :
    ∃ output next, runScriptStep runContext clock index c requireName.statements[8].1 requireName.statements[8].2 =
      .continued output next [] ∧ ∀ found ∈ (RunStep.continued output next []).executions,
        found.output.isError = false ∧ Good sessions customers 9 found.next := by
  obtain ⟨output, next, step, noError⟩ := runScriptStep_setting_ok (context := runContext) (clock := clock)
    (index := index) (statement := requireName.statements[8].1) (parameters := requireName.statements[8].2)
    (found := by rw [good.1.1]; with_unfolding_all exact rfl)
  exact ⟨output, next, step, good_step noError (advance_8 good.1 step) ⟨fun h => by omega, fun h => by omega⟩⟩

/-- For every clock, tables of the sessions and the customers, and customers that hold no NULL name: for every
statement of the rebuild and every valid connection that has the facts before it, the step of the statement continues,
and every execution of it has no error output and reaches a connection that has the facts after it. In plain words,
each step of the rebuild succeeds and keeps the facts, in every execution. Proof sketch: the nine cases
{lit}`good_0` to {lit}`good_8`. -/
theorem good_advance (clock : Option Clock) (sessions customers : Table)
    (named : ∀ row ∈ customers.rows, row.values[1]? ≠ some .null) :
    ∀ (n : Nat) (inList : n < requireName.statements.length) (index : Nat) (connection : Connection),
      connection.state.Holds (Database.Valid Profile.pinned) → Good sessions customers n connection →
      ∃ output next others, runScriptStep runContext clock index connection requireName.statements[n].1
          requireName.statements[n].2 = .continued output next others ∧
        ∀ found ∈ (RunStep.continued output next others).executions,
          found.output.isError = false ∧ Good sessions customers (n + 1) found.next := by
  intro n inList index connection valid good
  have small : n < 9 := inList
  match n, small with
  | 0, _ => obtain ⟨output, next, step, all⟩ := good_0 (clock := clock) (index := index) good; exact ⟨output, next, _, step, all⟩
  | 1, _ => obtain ⟨output, next, step, all⟩ := good_1 (clock := clock) (index := index) good; exact ⟨output, next, _, step, all⟩
  | 2, _ => obtain ⟨output, next, step, all⟩ := good_2 (clock := clock) (index := index) good valid; exact ⟨output, next, _, step, all⟩
  | 3, _ => obtain ⟨output, next, step, all⟩ := good_3 (clock := clock) (index := index) good valid named; exact ⟨output, next, _, step, all⟩
  | 4, _ => obtain ⟨output, next, step, all⟩ := good_4 (clock := clock) (index := index) good; exact ⟨output, next, _, step, all⟩
  | 5, _ => obtain ⟨output, next, step, all⟩ := good_5 (clock := clock) (index := index) good; exact ⟨output, next, _, step, all⟩
  | 6, _ => obtain ⟨output, next, step, all⟩ := good_6 (clock := clock) (index := index) good; exact ⟨output, next, _, step, all⟩
  | 7, _ => obtain ⟨output, next, step, all⟩ := good_7 (clock := clock) (index := index) good; exact ⟨output, next, _, step, all⟩
  | 8, _ => obtain ⟨output, next, step, all⟩ := good_8 (clock := clock) (index := index) good; exact ⟨output, next, _, step, all⟩

end RebuildGuide
