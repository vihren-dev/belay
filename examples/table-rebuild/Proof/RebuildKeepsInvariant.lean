import RebuildGuide
import Belay.Sqlite.Model.Programs.Scripts.TablePath

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2048

/-! The rebuild's resolution path and the tables it preserves. Each step can change
rows in other tables. The computed table position tracks each surviving table on
every successful branch, including the branches of INSERT from SELECT. -/

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

/-- At every position the prefix check reports, the original table is present. -/
def Tracks (table : Table) (start count : Nat) (c : Connection) : Prop :=
  sample.raw.connection.resolveState.TableAtPrefix rebuildPath.1 count start table c.state.database

/-- A connection at this prefix has the computed resolution state and retains the original sessions table
at the position that the table check reports. -/
def Kept (sessions : Table) (count : Nat) (c : Connection) : Prop :=
  c.resolveState = schemaAt count ∧ Tracks sessions 1 count c

/-- A database of the guide's schema with the given sessions table starts in the empty prefix.
Proof sketch: its catalog agrees with the sample and its table lookup gives the initial table. -/
theorem kept_start {db : Database} {counters : Counters} {sessions : Table}
    (pre : db.raw.catalog = sample.raw.catalog) (named : db.raw.tableNamed sessionsName = some (1, sessions)) :
    Kept sessions 0 (db.raw.connection counters) := by
  refine ⟨?_, ResolveState.tableAtPrefix_zero (Database.tableNamed_some named).2⟩
  change (db.raw.connection counters).resolveState = sample.raw.connection.resolveState
  simp [Database.Raw.connection, Connection.resolveState, pre]

/-- On each successful execution of the next statement, a tracked table is present at any
position the next prefix reports. Proof sketch: the prefix recurrence identifies the input
position. The checked frame of the resolved statement transports the table from there. -/
theorem tracks_step {n start : Nat} {table : Table} {c next : Connection} {clock : Option Clock}
    {index : Nat} {output : Output} {others : List StatementExecution} {found : StatementExecution}
    (bound : n < makeStrict.statements.length) (same : c.resolveState = schemaAt n)
    (tracked : Tracks table start n c)
    (step : runScriptStep runContext clock index c makeStrict.statements[n].1 makeStrict.statements[n].2 =
      .continued output next others) (member : found ∈ (RunStep.continued output next others).executions)
    (ok : found.output.isError = false) : Tracks table start (n + 1) found.next := by
  have atStmt : (makeStrict.statements.map Prod.fst)[n]? = some makeStrict.statements[n].1 := by simp [bound]
  exact runScriptStep_tableAtPrefix (resolved := rebuildPath.1) (final := rebuildPath.2)
    rebuild_resolves atStmt same tracked step member ok

/-- Each successful execution of a rebuild statement carries the schema and sessions table to
the next prefix. Proof sketch: use the schema path and the checked table frame. -/
theorem kept_step {n : Nat} {sessions : Table} {c next : Connection} {clock : Option Clock}
    {index : Nat} {output : Output} {others : List StatementExecution} {found : StatementExecution}
    (bound : n < makeStrict.statements.length) (kept : Kept sessions n c)
    (step : runScriptStep runContext clock index c makeStrict.statements[n].1 makeStrict.statements[n].2 =
      .continued output next others) (member : found ∈ (RunStep.continued output next others).executions)
    (ok : found.output.isError = false) : Kept sessions (n + 1) found.next :=
  ⟨runScriptStep_resolveState (resolutionAt n kept.1 bound) step member ok,
   tracks_step bound kept.1 kept.2 step member ok⟩

/-- The single execution of a step with no further execution: its connection is the next connection. -/
theorem single_next {output : Output} {next : Connection} {found : StatementExecution}
    (member : found ∈ (RunStep.continued output next []).executions) : found.next = next := by
  simp only [RunStep.executions, List.mem_singleton] at member
  rw [member]

end RebuildGuide
