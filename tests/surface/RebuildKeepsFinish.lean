import RebuildKeepsInvariant

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! The last four statements of the rebuild keep the facts of {lit}`RebuildKeepsInvariant` (ADR 0017, S6, part 3). -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace RebuildGuide

/-- Statement 5, the rename of the new customers, keeps the facts (the form of {name}`advance_0`). The rename leaves
the definition of the sessions as it is. Proof sketch: the step law of the statement gives the next connection;
the resolution state is compared by evaluation. -/
theorem advance_5 {clock : Option Clock} {index : Nat} {c next : Connection} {output : Output}
    {others : List StatementExecution} {sessions : Table} (kept : Kept sessions 5 c)
    (step : runScriptStep runContext clock index c requireName.statements[5].1 requireName.statements[5].2 =
      .continued output next others) :
    ∀ found ∈ (RunStep.continued output next others).executions, found.output.isError = false →
      Kept sessions 6 found.next := by
  obtain ⟨hres, hnamed⟩ := kept
  obtain ⟨h1, h2, h3, h4⟩ := resolveState_parts hres
  obtain ⟨-, rfl, -, nextEq⟩ := runScriptStep_rewrite (found := by rw [hres]; with_unfolding_all exact rfl) step
  intro found member _
  rw [single_next member, nextEq]
  refine ⟨?_, Database.tableNamed_rewrite hnamed ?_⟩
  · simp only [Connection.resolveState]
    rw [h2, h3, h4]
    decide +kernel
  · have lookup := (Database.tableNamed_some hnamed).1
    rw [h1] at lookup
    refine Eq.trans ?_ lookup
    with_unfolding_all rfl

/-- Statement 6, {lit}`PRAGMA foreign_key_check`, keeps the facts: it changes nothing. -/
theorem advance_6 {clock : Option Clock} {index : Nat} {c next : Connection} {output : Output}
    {others : List StatementExecution} {sessions : Table} (kept : Kept sessions 6 c)
    (step : runScriptStep runContext clock index c requireName.statements[6].1 requireName.statements[6].2 =
      .continued output next others) :
    ∀ found ∈ (RunStep.continued output next others).executions, found.output.isError = false →
      Kept sessions 7 found.next := by
  obtain ⟨hres, hnamed⟩ := kept
  obtain ⟨rfl, rfl⟩ := runScriptStep_readOnly_keeps (found := by rw [hres]; with_unfolding_all exact rfl)
    (Or.inl ⟨_, _, rfl⟩) step
  intro found member _
  rw [single_next member]
  exact ⟨by rw [hres]; with_unfolding_all rfl, hnamed⟩

/-- Statement 7, {lit}`COMMIT`, keeps the facts (the form of {name}`advance_0`). The transaction is open before it, as
the resolution state shows. Proof sketch: the step law of the statement gives the next connection; the resolution
state is compared by evaluation. -/
theorem advance_7 {clock : Option Clock} {index : Nat} {c next : Connection} {output : Output}
    {others : List StatementExecution} {sessions : Table} (kept : Kept sessions 7 c)
    (step : runScriptStep runContext clock index c requireName.statements[7].1 requireName.statements[7].2 =
      .continued output next others) :
    ∀ found ∈ (RunStep.continued output next others).executions, found.output.isError = false →
      Kept sessions 8 found.next := by
  obtain ⟨hres, hnamed⟩ := kept
  obtain ⟨h1, h2, h3, h4⟩ := resolveState_parts hres
  have active : ∃ original, c.state.snapshot = some original := by
    have open_ : ∃ catalog, (reachedAfter 7).resolveState.saved = some catalog := by
      with_unfolding_all exact ⟨_, rfl⟩
    obtain ⟨catalog, saved⟩ := open_
    rw [saved] at h2
    cases snapshot : c.state.snapshot with
    | none => simp [snapshot] at h2
    | some original => exact ⟨original, rfl⟩
  obtain ⟨original, active⟩ := active
  obtain ⟨-, rfl, nextEq⟩ := runScriptStep_commit_active
    (found := by rw [hres]; with_unfolding_all exact rfl) active step
  intro found member _
  rw [single_next member, nextEq]
  refine ⟨?_, hnamed⟩
  simp only [Connection.resolveState, Option.map_none]
  rw [h1, h3, h4]
  with_unfolding_all rfl

/-- Statement 8, {lit}`PRAGMA foreign_keys = ON`, keeps the facts (the form of {name}`advance_0`). The transaction is
closed before it. Proof sketch: the step law of the statement gives the next connection; the resolution state is
compared by evaluation. -/
theorem advance_8 {clock : Option Clock} {index : Nat} {c next : Connection} {output : Output}
    {others : List StatementExecution} {sessions : Table} (kept : Kept sessions 8 c)
    (step : runScriptStep runContext clock index c requireName.statements[8].1 requireName.statements[8].2 =
      .continued output next others) :
    ∀ found ∈ (RunStep.continued output next others).executions, found.output.isError = false →
      Kept sessions 9 found.next := by
  obtain ⟨hres, hnamed⟩ := kept
  obtain ⟨h1, h2, h3, h4⟩ := resolveState_parts hres
  have idle : c.state.snapshot = none := by
    have closed : (reachedAfter 8).resolveState.saved = none := by with_unfolding_all rfl
    rw [closed] at h2
    simpa using h2
  obtain ⟨-, rfl, nextEq⟩ := runScriptStep_pragma_foreignKeys (found := by rw [hres]; with_unfolding_all exact rfl) step
  intro found member _
  rw [single_next member, nextEq]
  refine ⟨?_, hnamed⟩
  simp only [Connection.resolveState, idle, Option.isSome_none]
  rw [h1, h4]
  with_unfolding_all rfl

end RebuildGuide
