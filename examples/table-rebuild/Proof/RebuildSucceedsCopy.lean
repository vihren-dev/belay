import RebuildCopyFacts
import Belay.Sqlite.Model.Programs.Scripts.CopyStep

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-! Claim 2 of the guide's table rebuild, the copy step (ADR 0017, S6, part 3). The rebuild {lit}`makeStrict`
succeeds on a database of the guide's schema whose customers fit the STRICT types of the new table. Its INSERT from
a query is the one statement that can fail for a reason of the data: the new customers table is STRICT, so a cell
must fit the declared type of its column. This module shows that the step continues without an error when every old
customer fits those types, from a connection that has the facts of the rebuild so far. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace RebuildGuide

/-- For a valid connection at the fourth statement, with the resolution state and tracked
tables of the rebuild, suppose every customer fits the new STRICT types. The copy continues.
Its main database changes only the target, which holds the old customers in scan order.
Every execution has a successful output. Proof sketch: the prefix gives the source and empty
target; their catalog definitions pass the checks of {name}`runScriptStep_copyOf`. -/
theorem copy_continues {clock : Option Clock} {index : Nat} {c : Connection} {customers : Table}
    (schema : c.resolveState = schemaAt 3) (tracked : Tracks customers 0 3 c)
    (presentNew : c.state.database.table 2 = some ⟨strictShape, []⟩) (valid : c.state.Holds (Database.Valid Profile.pinned))
    (fits : ∀ row ∈ customers.rows, LiteralData.typesFit strictShape row = true) :
    ∃ output next others, runScriptStep runContext clock index c makeStrict.statements[3].1 makeStrict.statements[3].2 =
      .continued output next others ∧ next.state.database = c.state.database.setRows 2 customers.scanRows ∧
      ∀ ex ∈ (RunStep.continued output next others).executions, ex.output.isError = false := by
  obtain ⟨after, resolved⟩ := copy_resolves
  have found : resolveStatement runContext c.resolveState makeStrict.statements[3].1 =
      .ok (.insertSelect 2 ((List.range 3).map .source) copyQuery [] [] none [] none, after) := by
    rw [schema]; exact resolved
  have present := tracked 0 (by decide +kernel)
  have shape := Database.tableAt_of_table present
  have catalog : c.state.database.catalog = (schemaAt 3).catalog := congrArg ResolveState.catalog schema
  have oldShape : customers.shape = sourceShape := by
    rw [catalog, show (schemaAt 3).catalog.tableAt 0 = some sourceShape by decide +kernel] at shape
    exact (Option.some.inj shape).symm
  have oldAlias : customers.shape.rowidAlias = some 0 := by rw [oldShape]; decide +kernel
  have oldWidth : customers.shape.columns.length = 3 := by rw [oldShape]; decide +kernel
  have compatible : customers.shape.copyCompatible strictShape (c.state.database.catalog.uniqueKeys 2 strictShape) =
      true := by rw [oldShape, catalog]; decide +kernel
  have newWidth : strictShape.columns.length = 3 := by decide +kernel
  have copy := runScriptStep_copyOf (context := runContext) (clock := clock) (index := index)
    (statement := makeStrict.statements[3].1) (parameters := makeStrict.statements[3].2) (after := after)
    ["id", "name", "email"] present presentNew compatible oldAlias rfl valid fits
  dsimp only at copy
  rw [oldWidth, newWidth] at copy
  obtain ⟨output, next, others, step, ok, database, _, alternatives⟩ := copy found
  refine ⟨output, next, others, step, database, ?_⟩
  intro ex member
  rcases List.mem_cons.mp member with rfl | alternative
  · exact ok
  · exact (alternatives _ alternative).1

end RebuildGuide
