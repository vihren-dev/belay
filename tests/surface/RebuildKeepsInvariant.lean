import RebuildGuide

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! The facts that every execution of the rebuild keeps (ADR 0017, S6, part 3). The rebuild {lit}`requireName` has an
INSERT from a query, so a branch of a run can reach a connection that the model's own run does not reach. The
facts that hold in all branches are about the resolution state, which does not depend on the rows, and about the
table of the sessions, which the rebuild never writes. {lit}`Kept` states them after the first statements, and
the lemmas {lit}`advance_0` to {lit}`advance_4` (here) and {lit}`advance_5` to {lit}`advance_8`
({lit}`RebuildKeepsFinish`) show that each statement keeps them, in every execution of its step. The lemmas use the
general step laws of the model; this module holds only what is particular to the guide's script. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace RebuildGuide

/-- The name of the table of the sessions. -/
def sessionsName : Identifier := name! "sessions"

/-- The connection that the model reaches after the first statements of the rebuild, started on the sample. -/
def reachedAfter (count : Nat) : Connection :=
  (runScriptFrom runContext none 0 sample.raw.connection (requireName.statements.take count)).connection

/-- Where the sessions are after the first statements: at position 1 until the drop of the customers, at position 0
after it. -/
def sessionsPosition (count : Nat) : Nat := if count ≤ 4 then 1 else 0

/-- For the table of the sessions, a number of statements and a connection: after that many statements of the rebuild,
the connection has the resolution state of the model's run of the rebuild on the sample, and the name of the
sessions finds the given table at {name}`sessionsPosition`. In plain words, the catalog, the open transaction and
the settings are as in the model's run, whatever the rows are, and the sessions are the same table with the same
rows. -/
def Kept (sessions : Table) (count : Nat) (connection : Connection) : Prop :=
  connection.resolveState = (reachedAfter count).resolveState ∧
    connection.state.database.tableNamed sessionsName = some (sessionsPosition count, sessions)

/-- For every connection with a given resolution state: the catalog, the saved catalog and the two settings of the
connection are those of the state. Proof sketch: unfold the equation of the structure. -/
theorem resolveState_parts {c : Connection} {R : ResolveState} (h : c.resolveState = R) :
    c.state.database.catalog = R.catalog ∧ c.state.snapshot.map (·.catalog) = R.saved ∧
      c.foreignKeys = R.foreignKeys ∧ c.recursiveTriggers = R.recursiveTriggers := by
  cases R
  simp only [Connection.resolveState, ResolveState.mk.injEq] at h
  exact h

/-- The single execution of a step with no further execution: its connection is the next connection. -/
theorem single_next {output : Output} {next : Connection} {found : StatementExecution}
    (member : found ∈ (RunStep.continued output next []).executions) : found.next = next := by
  simp only [RunStep.executions, List.mem_singleton] at member
  rw [member]

/-- For every connection that satisfies {name}`Kept` after 0 statements, and every execution of the step of statement
0 ({lit}`PRAGMA foreign_keys = OFF`) that has no error output: the connection of the execution satisfies
{name}`Kept` after 1 statement. The lemmas {lit}`advance_1` to {lit}`advance_8` have the same form for the later
statements. Proof sketch: the step law {name}`runScriptStep_setting` gives the next connection, and the resolution
state of the sample run is compared by evaluation. -/
theorem advance_0 {clock : Option Clock} {index : Nat} {c next : Connection} {output : Output}
    {others : List StatementExecution} {sessions : Table} (kept : Kept sessions 0 c)
    (step : runScriptStep runContext clock index c requireName.statements[0].1 requireName.statements[0].2 =
      .continued output next others) :
    ∀ found ∈ (RunStep.continued output next others).executions, found.output.isError = false →
      Kept sessions 1 found.next := by
  obtain ⟨hres, hnamed⟩ := kept
  obtain ⟨h1, h2, h3, h4⟩ := resolveState_parts hres
  have law := runScriptStep_setting (found := by rw [hres]; with_unfolding_all exact rfl) step
  obtain ⟨-, rfl, nextEq⟩ := law
  intro found member _
  rw [single_next member, nextEq]
  refine ⟨?_, hnamed⟩
  simp only [Connection.set, Connection.resolveState]
  rw [h1, h2, h4]
  with_unfolding_all rfl

/-- Statement 1, {lit}`BEGIN`, keeps the facts (the form of {name}`advance_0`). The transaction is closed before it,
as the resolution state shows. Proof sketch: the step law of the statement gives the next connection; the
resolution state is compared by evaluation. -/
theorem advance_1 {clock : Option Clock} {index : Nat} {c next : Connection} {output : Output}
    {others : List StatementExecution} {sessions : Table} (kept : Kept sessions 1 c)
    (step : runScriptStep runContext clock index c requireName.statements[1].1 requireName.statements[1].2 =
      .continued output next others) :
    ∀ found ∈ (RunStep.continued output next others).executions, found.output.isError = false →
      Kept sessions 2 found.next := by
  obtain ⟨hres, hnamed⟩ := kept
  obtain ⟨h1, h2, h3, h4⟩ := resolveState_parts hres
  have idle : c.state.snapshot = none := by
    have closed : (reachedAfter 1).resolveState.saved = none := by with_unfolding_all rfl
    rw [closed] at h2
    simpa using h2
  obtain ⟨-, rfl, nextEq⟩ := runScriptStep_begin_idle (found := by rw [hres]; with_unfolding_all exact rfl) idle step
  intro found member _
  rw [single_next member, nextEq]
  refine ⟨?_, hnamed⟩
  simp only [Connection.resolveState, Option.map_some]
  rw [h1, h3, h4]
  with_unfolding_all rfl

/-- Statement 2, the CREATE TABLE of the new customers, keeps the facts (the form of {name}`advance_0`). Proof sketch:
the step law of the statement gives the next connection; the resolution state is compared by evaluation. -/
theorem advance_2 {clock : Option Clock} {index : Nat} {c next : Connection} {output : Output}
    {others : List StatementExecution} {sessions : Table} (kept : Kept sessions 2 c)
    (step : runScriptStep runContext clock index c requireName.statements[2].1 requireName.statements[2].2 =
      .continued output next others) :
    ∀ found ∈ (RunStep.continued output next others).executions, found.output.isError = false →
      Kept sessions 3 found.next := by
  obtain ⟨hres, hnamed⟩ := kept
  obtain ⟨h1, h2, h3, h4⟩ := resolveState_parts hres
  obtain ⟨-, rfl, -, -, nextEq⟩ := runScriptStep_createTable (found := by rw [hres]; with_unfolding_all exact rfl) step
  intro found member _
  rw [single_next member]
  refine ⟨?_, ?_⟩
  · rw [nextEq]
    simp only [Connection.resolveState]
    rw [h1, h2, h3, h4]
    with_unfolding_all rfl
  · exact runScriptStep_createTable_frame (found := by rw [hres]; with_unfolding_all exact rfl) step hnamed

/-- Statement 3, the INSERT from a query into the new customers, keeps the facts in every execution of the step: the
sessions are another table than the target. -/
theorem advance_3 {clock : Option Clock} {index : Nat} {c next : Connection} {output : Output}
    {others : List StatementExecution} {sessions : Table} (kept : Kept sessions 3 c)
    (step : runScriptStep runContext clock index c requireName.statements[3].1 requireName.statements[3].2 =
      .continued output next others) :
    ∀ found ∈ (RunStep.continued output next others).executions, found.output.isError = false →
      Kept sessions 4 found.next := by
  obtain ⟨hres, hnamed⟩ := kept
  obtain ⟨h1, h2, h3, h4⟩ := resolveState_parts hres
  have law := runScriptStep_insertSelect_frame (found := by rw [hres]; with_unfolding_all exact rfl) step
  intro found member noError
  obtain ⟨rows, counters, nextEq⟩ := law found member noError
  rw [nextEq]
  refine ⟨?_, Database.tableNamed_setRows_other hnamed rows (by decide)⟩
  simp only [Connection.resolveState, Database.setRows]
  rw [h1, h2, h3, h4]
  with_unfolding_all rfl

/-- Statement 4, the DROP of the old customers, keeps the facts (the form of {name}`advance_0`). The sessions move
from position 1 to position 0. Proof sketch: the step law of the statement gives the next connection; the
resolution state is compared by evaluation. -/
theorem advance_4 {clock : Option Clock} {index : Nat} {c next : Connection} {output : Output}
    {others : List StatementExecution} {sessions : Table} (kept : Kept sessions 4 c)
    (step : runScriptStep runContext clock index c requireName.statements[4].1 requireName.statements[4].2 =
      .continued output next others) :
    ∀ found ∈ (RunStep.continued output next others).executions, found.output.isError = false →
      Kept sessions 5 found.next := by
  obtain ⟨hres, hnamed⟩ := kept
  obtain ⟨h1, h2, h3, h4⟩ := resolveState_parts hres
  obtain ⟨-, rfl, nextEq⟩ := runScriptStep_drop_plain (found := by rw [hres]; with_unfolding_all exact rfl) step
  intro found member _
  rw [single_next member]
  refine ⟨?_, ?_⟩
  · rw [nextEq]
    simp only [Connection.resolveState, Database.drop]
    rw [h1, h2, h3, h4]
    with_unfolding_all rfl
  · have moved := runScriptStep_drop_frame (found := by rw [hres]; with_unfolding_all exact rfl) step hnamed
      (by decide +kernel)
    rw [moved]
    exact congrArg (fun position => some (position, sessions)) (by decide)

end RebuildGuide
