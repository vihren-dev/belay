import RebuildKeepsInvariant

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! The last three statements of the rebuild keep the facts of {lit}`RebuildKeepsInvariant` (ADR 0017, S6, part 3). -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace RebuildGuide

/-- Statement 5, the rename of the new customers, keeps the facts (the form of {name}`advance_0`). The rename leaves
the definition of the sessions as it is. Proof sketch: the prefix law gives the schema, and the statement frame gives the sessions. -/
theorem advance_5 {clock : Option Clock} {index : Nat} {c next : Connection} {output : Output}
    {others : List StatementExecution} {sessions : Table} (kept : Kept sessions 5 c)
    (step : runScriptStep runContext clock index c makeStrict.statements[5].1 makeStrict.statements[5].2 =
      .continued output next others) :
    ∀ found ∈ (RunStep.continued output next others).executions, found.output.isError = false →
      Kept sessions 6 found.next := by
  have resolution := resolutionAt 5 kept.1
  intro found member ok
  refine ⟨runScriptStep_resolveState resolution step member ok, ?_⟩
  obtain rfl := runScriptStep_others step resolution (by with_unfolding_all rfl)
  rw [single_next member]
  obtain ⟨_, _, _, nextEq⟩ := runScriptStep_rewrite (found := by with_unfolding_all exact resolution) step
  rw [nextEq]
  apply Database.tableNamed_rewrite kept.2
  have lookup := (Database.tableNamed_some kept.2).1
  have catalog : c.state.database.catalog = (schemaAt 5).catalog := congrArg ResolveState.catalog kept.1
  rw [catalog] at lookup
  exact Eq.trans (by with_unfolding_all rfl) lookup

/-- Statement 6, {lit}`COMMIT`, keeps the facts (the form of {name}`advance_0`). The transaction is open before it, as
the resolution state shows. Proof sketch: the prefix law gives the schema, and the statement frame gives the sessions. -/
theorem advance_6 {clock : Option Clock} {index : Nat} {c next : Connection} {output : Output}
    {others : List StatementExecution} {sessions : Table} (kept : Kept sessions 6 c)
    (step : runScriptStep runContext clock index c makeStrict.statements[6].1 makeStrict.statements[6].2 =
      .continued output next others) :
    ∀ found ∈ (RunStep.continued output next others).executions, found.output.isError = false →
      Kept sessions 7 found.next := by
  have resolution := resolutionAt 6 kept.1
  intro found member ok
  refine ⟨runScriptStep_resolveState resolution step member ok, ?_⟩
  obtain rfl := runScriptStep_others step resolution (by with_unfolding_all rfl)
  rw [single_next member]
  rw [runScriptStep_commit_frame (found := by with_unfolding_all exact resolution) step]
  exact kept.2

/-- Statement 7, {lit}`PRAGMA foreign_keys = ON`, keeps the facts (the form of {name}`advance_0`). The transaction is
closed before it. Proof sketch: the prefix law gives the schema, and the statement frame gives the sessions. -/
theorem advance_7 {clock : Option Clock} {index : Nat} {c next : Connection} {output : Output}
    {others : List StatementExecution} {sessions : Table} (kept : Kept sessions 7 c)
    (step : runScriptStep runContext clock index c makeStrict.statements[7].1 makeStrict.statements[7].2 =
      .continued output next others) :
    ∀ found ∈ (RunStep.continued output next others).executions, found.output.isError = false →
      Kept sessions 8 found.next := by
  have resolution := resolutionAt 7 kept.1
  intro found member ok
  refine ⟨runScriptStep_resolveState resolution step member ok, ?_⟩
  obtain rfl := runScriptStep_others step resolution (by with_unfolding_all rfl)
  rw [single_next member]
  rw [runScriptStep_setting_frame (found := by with_unfolding_all exact resolution) step]
  exact kept.2

end RebuildGuide
