import RebuildGuide
import Belay.Sqlite.Model.Programs.Scripts.SchemaPath

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! The facts that every execution of the rebuild keeps (ADR 0017, S6, part 3). The rebuild {lit}`makeStrict` has an
INSERT from a query, so a branch of a run can reach a connection that the model's own run does not reach. The
facts that hold in all branches are about the resolution state, which does not depend on the rows, and about the
table of the sessions, which the rebuild never writes. {lit}`Kept` states them after the first statements, and
the lemmas {lit}`advance_0` to {lit}`advance_4` (here) and {lit}`advance_5` to {lit}`advance_7`
({lit}`RebuildKeepsFinish`) show that each statement keeps them, in every execution of its step. The lemmas use the
general step laws of the model; this module holds only what is particular to the guide's script. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace RebuildGuide

/-- The name of the table of the sessions. -/
def sessionsName : Identifier := name! "sessions"

/-- The statements and final state obtained by resolving the rebuild on the sample catalog. -/
def rebuildPath : List Resolved.Statement × ResolveState :=
  (resolveFrom runContext 0 sample.raw.connection.resolveState (makeStrict.statements.map Prod.fst)).toOption.getD
    ([], sample.raw.connection.resolveState)

/-- Resolution succeeds for the entire rebuild. The kernel evaluates the resolver on its catalog. -/
theorem rebuild_resolves : resolveFrom runContext 0 sample.raw.connection.resolveState
    (makeStrict.statements.map Prod.fst) = .ok rebuildPath := by with_unfolding_all rfl

/-- The catalog, transaction and settings after the given number of statements of the rebuild. -/
def schemaAt (n : Nat) : ResolveState := sample.raw.connection.resolveState.atPrefix rebuildPath.1 n

/-- For each statement of the rebuild, any connection at its schema prefix resolves it to the
corresponding statement and the next prefix. Proof sketch: extract the position from {name}`rebuild_resolves`. -/
theorem resolutionAt (n : Nat) {c : Connection} (same : c.resolveState = schemaAt n)
    (bound : n < makeStrict.statements.length := by decide) :
    resolveStatement runContext c.resolveState makeStrict.statements[n].1 =
      .ok (rebuildPath.1.getD n .begin, schemaAt (n + 1)) := by
  have atStmt : (makeStrict.statements.map Prod.fst)[n]? = some makeStrict.statements[n].1 := by simp [bound]
  obtain ⟨r, atR, resolution⟩ := resolveFrom_atPrefix (resolved := rebuildPath.1) (final := rebuildPath.2) rebuild_resolves atStmt
  rw [same, List.getD_eq_getElem?_getD, atR]
  exact resolution

/-- Where the sessions are after the first statements: at position 1 until the drop of the customers, at position 0
after it. -/
def sessionsPosition (count : Nat) : Nat := if count ≤ 4 then 1 else 0

/-- For the table of the sessions, a number of statements and a connection: after that many statements of the rebuild,
the connection has the resolution state of the resolved prefix, and the name of the
sessions finds the given table at {name}`sessionsPosition`. In plain words, the catalog, the open transaction and
the settings are as in the resolved prefix, whatever the rows are, and the sessions are the same table with the same
rows. -/
def Kept (sessions : Table) (count : Nat) (connection : Connection) : Prop :=
  connection.resolveState = schemaAt count ∧
    connection.state.database.tableNamed sessionsName = some (sessionsPosition count, sessions)

/-- For every database of the guide's schema, counters and table of the sessions that the name finds at position 1: a
connection to the database satisfies {name}`Kept` before the first statement. Proof sketch: the resolution state
depends on the catalog only, and the sample has the same catalog. -/
theorem kept_start {db : Database} {counters : Counters} {sessions : Table}
    (pre : db.raw.catalog = sample.raw.catalog) (named : db.raw.tableNamed sessionsName = some (1, sessions)) :
    Kept sessions 0 (db.raw.connection counters) := by
  refine ⟨?_, by simpa [Database.Raw.connection, sessionsPosition] using named⟩
  have same : (db.raw.connection counters).resolveState = sample.raw.connection.resolveState := by
    simp [Database.Raw.connection, Connection.resolveState, pre]
  rw [same]
  with_unfolding_all rfl

/-- The single execution of a step with no further execution: its connection is the next connection. -/
theorem single_next {output : Output} {next : Connection} {found : StatementExecution}
    (member : found ∈ (RunStep.continued output next []).executions) : found.next = next := by
  simp only [RunStep.executions, List.mem_singleton] at member
  rw [member]

/-- For every connection that satisfies {name}`Kept` after 0 statements, and every execution of the step of statement
0 ({lit}`PRAGMA foreign_keys = OFF`) that has no error output: the connection of the execution satisfies
{name}`Kept` after 1 statement. The lemmas {lit}`advance_1` to {lit}`advance_7` have the same form for the later
statements. Proof sketch: the prefix law gives the schema, and {name}`runScriptStep_setting_frame` gives the sessions. -/
theorem advance_0 {clock : Option Clock} {index : Nat} {c next : Connection} {output : Output}
    {others : List StatementExecution} {sessions : Table} (kept : Kept sessions 0 c)
    (step : runScriptStep runContext clock index c makeStrict.statements[0].1 makeStrict.statements[0].2 =
      .continued output next others) :
    ∀ found ∈ (RunStep.continued output next others).executions, found.output.isError = false →
      Kept sessions 1 found.next := by
  have resolution := resolutionAt 0 kept.1
  intro found member ok
  refine ⟨runScriptStep_resolveState resolution step member ok, ?_⟩
  obtain rfl := runScriptStep_others step resolution (by with_unfolding_all rfl)
  rw [single_next member]
  rw [runScriptStep_setting_frame (found := by with_unfolding_all exact resolution) step]
  exact kept.2

/-- Statement 1, {lit}`BEGIN`, keeps the facts (the form of {name}`advance_0`). The transaction is closed before it,
as the resolution state shows. Proof sketch: the prefix law gives the schema, and the statement frame gives the sessions. -/
theorem advance_1 {clock : Option Clock} {index : Nat} {c next : Connection} {output : Output}
    {others : List StatementExecution} {sessions : Table} (kept : Kept sessions 1 c)
    (step : runScriptStep runContext clock index c makeStrict.statements[1].1 makeStrict.statements[1].2 =
      .continued output next others) :
    ∀ found ∈ (RunStep.continued output next others).executions, found.output.isError = false →
      Kept sessions 2 found.next := by
  have resolution := resolutionAt 1 kept.1
  intro found member ok
  refine ⟨runScriptStep_resolveState resolution step member ok, ?_⟩
  obtain rfl := runScriptStep_others step resolution (by with_unfolding_all rfl)
  rw [single_next member]
  rw [runScriptStep_begin_frame (found := by with_unfolding_all exact resolution) step]
  exact kept.2

/-- Statement 2, the CREATE TABLE of the new customers, keeps the facts (the form of {name}`advance_0`). Proof sketch:
the prefix law gives the schema, and the statement frame gives the sessions. -/
theorem advance_2 {clock : Option Clock} {index : Nat} {c next : Connection} {output : Output}
    {others : List StatementExecution} {sessions : Table} (kept : Kept sessions 2 c)
    (step : runScriptStep runContext clock index c makeStrict.statements[2].1 makeStrict.statements[2].2 =
      .continued output next others) :
    ∀ found ∈ (RunStep.continued output next others).executions, found.output.isError = false →
      Kept sessions 3 found.next := by
  have resolution := resolutionAt 2 kept.1
  intro found member ok
  refine ⟨runScriptStep_resolveState resolution step member ok, ?_⟩
  obtain rfl := runScriptStep_others step resolution (by with_unfolding_all rfl)
  rw [single_next member]
  exact runScriptStep_createTable_frame (found := by with_unfolding_all exact resolution) step kept.2

/-- Statement 3, the INSERT from a query into the new customers, keeps the facts in every execution of the step: the
sessions are another table than the target. -/
theorem advance_3 {clock : Option Clock} {index : Nat} {c next : Connection} {output : Output}
    {others : List StatementExecution} {sessions : Table} (kept : Kept sessions 3 c)
    (step : runScriptStep runContext clock index c makeStrict.statements[3].1 makeStrict.statements[3].2 =
      .continued output next others) :
    ∀ found ∈ (RunStep.continued output next others).executions, found.output.isError = false →
      Kept sessions 4 found.next := by
  have resolution := resolutionAt 3 kept.1
  intro found member ok
  refine ⟨runScriptStep_resolveState resolution step member ok, ?_⟩
  obtain ⟨rows, _, nextEq⟩ := runScriptStep_insertSelect_frame
    (found := by with_unfolding_all exact resolution) step found member ok
  rw [nextEq]
  exact Database.tableNamed_setRows_other kept.2 rows (by decide)

/-- Statement 4, the DROP of the old customers, keeps the facts (the form of {name}`advance_0`). The sessions move
from position 1 to position 0. Proof sketch: the prefix law gives the schema, and the statement frame gives the sessions. -/
theorem advance_4 {clock : Option Clock} {index : Nat} {c next : Connection} {output : Output}
    {others : List StatementExecution} {sessions : Table} (kept : Kept sessions 4 c)
    (step : runScriptStep runContext clock index c makeStrict.statements[4].1 makeStrict.statements[4].2 =
      .continued output next others) :
    ∀ found ∈ (RunStep.continued output next others).executions, found.output.isError = false →
      Kept sessions 5 found.next := by
  have resolution := resolutionAt 4 kept.1
  intro found member ok
  refine ⟨runScriptStep_resolveState resolution step member ok, ?_⟩
  obtain rfl := runScriptStep_others step resolution (by with_unfolding_all rfl)
  rw [single_next member]
  have moved := runScriptStep_drop_frame (found := by with_unfolding_all exact resolution) step kept.2
    (by decide +kernel)
  rw [moved]
  exact congrArg (fun position => some (position, sessions)) (by decide)

end RebuildGuide
