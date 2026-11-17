import RebuildCopyFacts
import Belay.Sqlite.Model.Schema.Writes.CopyRun

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

/-- For a table of the customers, a number of statements and a connection: the facts about the customers that the
copy needs. The prefix check follows the original customers table, and just after the
creation of the new customers (3 statements) the table at position 2 holds no row. -/
def Held (customers : Table) (count : Nat) (connection : Connection) : Prop :=
  Tracks customers 0 count connection ∧
    (count = 3 → connection.state.database.rows.getD 2 [] = [])

/-- For every table of the customers whose rows all fit the STRICT types of the new customers
({name}`LiteralData.typesFit` on {name}`strictShape`), and every connection that has the facts of the rebuild before
the copy (the resolved schema and {name}`Held`) and a valid state: the step of the copy continues with an output that is no
error and no other execution. In plain words, copying the customers into the new, STRICT customers table never fails
when every old customer fits its types. The next database differs only at the target, where the copied
rows have the original rowids in scan order. The clock and the index are arbitrary. Proof sketch: the prefix gives the two shapes. The catalog admits only the scan order.
{name}`runStatement_copyOf` gives the exact database and excludes alternatives.
{name}`runScriptStep_insertSelect_ok` lifts this run to the script step. -/
theorem copy_continues {clock : Option Clock} {index : Nat} {c : Connection} {customers : Table}
    (schema : c.resolveState = schemaAt 3) (held : Held customers 3 c) (valid : c.state.Holds (Database.Valid Profile.pinned))
    (fits : ∀ row ∈ customers.rows, LiteralData.typesFit strictShape row = true) :
    ∃ output next, runScriptStep runContext clock index c makeStrict.statements[3].1 makeStrict.statements[3].2 =
      .continued output next [] ∧ output.isError = false ∧
      next.state.database = c.state.database.setRows 2 customers.scanRows := by
  obtain ⟨after, resolved⟩ := copy_resolves
  have found : resolveStatement runContext c.resolveState makeStrict.statements[3].1 =
      .ok (.insertSelect 2 ((List.range 3).map .source) copyQuery [] [] none [] none, after) := by
    rw [schema]; exact resolved
  have present := held.1 0 (by decide +kernel)
  have shape := Database.tableAt_of_table present
  have catalog : c.state.database.catalog = (schemaAt 3).catalog := congrArg ResolveState.catalog schema
  have oldShape : customers.shape = sourceShape := by
    rw [catalog, show (schemaAt 3).catalog.tableAt 0 = some sourceShape by decide +kernel] at shape
    exact (Option.some.inj shape).symm
  have atTwo : c.state.database.catalog.tableAt 2 = some strictShape := by rw [catalog]; decide +kernel
  have presentNew : c.state.database.table 2 = some ⟨strictShape, []⟩ := by
    have emptyRows := held.2 rfl
    unfold Database.table
    rw [atTwo]
    simp only [Option.map_some, emptyRows]
  have admitted := valid.1.admitted.table present
  have oldAlias : customers.shape.rowidAlias = some 0 := by rw [oldShape]; decide +kernel
  have oldWidth : customers.shape.columns.length = 3 := by rw [oldShape]; decide +kernel
  have single : Table.accessOrders c.state.database.catalog 0 customers = [customers.scanRows] :=
    Table.accessOrders_alias _ 0 customers 0 (by rw [oldShape]; decide +kernel) (fun row m => admitted.rowsAliased row m 0 oldAlias)
      (fun access m => by
        rw [catalog, oldShape] at m
        have keys : (schemaAt 3).catalog.accessKeys 0 sourceShape = [([{ term := .column 0 }], none)] := by decide +kernel
        simpa [keys] using m)
  have compatible : customers.shape.copyCompatible strictShape (c.state.database.catalog.uniqueKeys 2 strictShape) =
      true := by rw [oldShape, catalog]; decide +kernel
  have newWidth : strictShape.columns.length = 3 := by decide +kernel
  have run := runStatement_copyOf 0 (c.state.counters.view copyStatement.counterReads) makeStrict.statements[3].2
    c.state.database 0 2 customers ⟨strictShape, []⟩ ["id", "name", "email"] present presentNew compatible oldAlias rfl
    admitted (valid.1.notNull 0 customers present) fits
  dsimp only at run
  rw [oldWidth, newWidth] at run
  obtain ⟨ready, effect, unique, _⟩ := run
  obtain ⟨output, next, step, ok, nextEq⟩ := runScriptStep_insertSelect_ok (value := 0) found rfl rfl
    (by change (_ && _) = true; rw [Bool.and_eq_true]; exact ⟨ready, rfl⟩) effect (unique single)
  exact ⟨output, next, step, ok, by rw [nextEq]⟩

end RebuildGuide
