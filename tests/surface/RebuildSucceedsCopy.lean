import RebuildCopyFacts

set_option doc.verso true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-! Claim 2 of the guide's table rebuild, the copy step (ADR 0017, S6, part 3). The rebuild {lit}`requireName`
succeeds on a database of the guide's schema without a NULL name. Its INSERT from a query is the one statement that
can fail for a reason of the data: the new customers table asks that {lit}`name` is not NULL. This module shows that
the step continues without an error when the old customers hold no NULL name, from a connection that has the facts
of the rebuild so far. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
namespace RebuildGuide

/-- For every list, function and position at which the mapped list has a value: the list has an item there that the
function maps to the value. Proof sketch: unfold the lookup in a mapped list. -/
theorem exists_of_map_getElem? {α β : Type} {items : List α} {function : α → β} {position : Nat} {value : β}
    (mapped : (items.map function)[position]? = some value) : ∃ item, items[position]? = some item ∧ function item = value := by
  simpa [List.getElem?_map, Option.map_eq_some_iff] using mapped

/-- For a table of the customers, a number of statements and a connection: the facts about the customers that the
copy needs. Until the copy, the name of the customers finds the given table at position 0, and just after the
creation of the new customers (3 statements) the table at position 2 holds no row. -/
def Held (customers : Table) (count : Nat) (connection : Connection) : Prop :=
  (count ≤ 3 → connection.state.database.tableNamed customersName = some (0, customers)) ∧
    (count = 3 → connection.state.database.rows.getD 2 [] = [])

/-- For every table of the customers that holds no NULL name, and every connection that has the facts of the rebuild
before the copy ({name}`Kept`, {name}`Held`) and a valid state: the step of the copy continues with an output that is
no error and no other execution. In plain words, copying the customers into the new customers table, which asks for a
name, never fails when no old customer lacks a name, in the run of the model; the other branches of the step are
covered by {name}`runScriptStep_insertSelect_frame`. The clock and the index are arbitrary. Proof sketch: the facts
of the catalog ({name}`catalogFacts`) give the shapes and keys of both tables. The query has one production, the
rows of the customers in rowid order ({name}`Table.accessOrders_alias`); these rows are copied unchanged
({name}`insertSelectRows_copy`) and fit the new table ({name}`InsertFits.copy`), where a valid database gives the
NOT NULL of {lit}`email` and the premise gives that of {lit}`name`. Then {name}`runScriptStep_insertSelect_success`
applies. -/
theorem copy_continues {clock : Option Clock} {index : Nat} {c : Connection} {sessions customers : Table}
    (kept : Kept sessions 3 c) (held : Held customers 3 c) (valid : c.state.Holds (Database.Valid Profile.pinned))
    (named : ∀ row ∈ customers.rows, row.values[1]? ≠ some .null) :
    ∃ output next, runScriptStep runContext clock index c requireName.statements[3].1 requireName.statements[3].2 =
      .continued output next [] ∧ output.isError = false := by
  obtain ⟨after, resolved⟩ := copy_resolves
  have found : resolveStatement runContext c.resolveState requireName.statements[3].1 =
      .ok (.insertSelect 2 ((List.range 3).map .source) copyQuery [] [] none [] none, after) := by
    rw [kept.1]; exact resolved
  obtain ⟨lookup, present⟩ := Database.tableNamed_some (held.1 (by omega))
  have facts : catalogFacts c.state.database.catalog = true := by
    rw [(resolveState_parts kept.1).1]; exact catalogFacts_reached
  obtain ⟨oldOk, accessKeys, newShape, atTwo, newOk, uniqueKeys⟩ := catalogFacts_unpack facts lookup
  have presentNew : c.state.database.table 2 = some ⟨newShape, []⟩ := by
    have emptyRows := held.2 rfl
    unfold Database.table
    rw [atTwo]
    simp only [Option.map_some, emptyRows]
  simp only [oldFacts, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at oldOk
  obtain ⟨⟨⟨oldAlias, oldRowid⟩, oldNotNull⟩, oldAffinity⟩ := oldOk
  simp only [newFacts, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Option.isNone_iff_eq_none, List.isEmpty_iff]
    at newOk
  obtain ⟨⟨⟨⟨⟨newAlias, newReady⟩, newPlain⟩, newUnchecked⟩, newNotNull⟩, newAffinity⟩ := newOk
  have admitted := valid.1.admitted.table present
  have oldWidth : customers.shape.columns.length = 3 := by simpa using congrArg List.length oldNotNull
  have newWidth : newShape.columns.length = 3 := by simpa using congrArg List.length newNotNull
  have inRows : ∀ row ∈ customers.scanRows, row ∈ customers.rows := fun row m => customers.scanRows_perm.mem_iff.mp m
  have wide : ∀ row ∈ Resolved.sourceRows customers, row.length = 3 := by
    intro values m
    obtain ⟨row, inScan, rfl⟩ := List.mem_map.mp m
    rw [admitted.rowsWide row (inRows row inScan), oldWidth]
  let ctx := Resolved.statementContext 0 (c.state.counters.view copyStatement.counterReads) requireName.statements[3].2
    c.state.database []
  have quiet : ctx.Quiet := fun _ _ => ⟨rfl, rfl, rfl⟩
  have single : Table.accessOrders c.state.database.catalog 0 customers = [customers.scanRows] :=
    Table.accessOrders_alias _ 0 customers 0 oldRowid (fun row m => admitted.rowsAliased row m 0 oldAlias)
      (fun access m => by rw [accessKeys] at m; simpa using m)
  have certain : copyQuery.productions ctx c.state.database
      (!Resolved.Statement.collectsSource 2 copyQuery [] [] none) =
      some [{ rows := Resolved.sourceRows customers, failure := none }] := by
    rw [copyQuery.productions_scan_single ctx c.state.database 0 customers _ rfl
      copy_simple (by decide +kernel) quiet present single]
    rw [Resolved.Query.results_copy copy_simple ctx 3 rfl rfl _ wide]
  have storedNew : ∀ row ∈ customers.scanRows, row.Stored newShape.columns := fun row m =>
    Row.Stored.of_affinities (by rw [newAffinity, oldAffinity]) (admitted.rowsStored row (inRows row m))
  have fits : InsertFits (c.state.database.keys 2 ⟨newShape, []⟩) ⟨newShape, []⟩
      (insertSelectRows ctx newShape.columns ((List.range 3).map .source) (Resolved.sourceRows customers)) := by
    have copied := insertSelectRows_copy ctx newShape.columns (Resolved.sourceRows customers)
      (by rw [newWidth]; exact wide) (by
        intro values m
        obtain ⟨row, inScan, rfl⟩ := List.mem_map.mp m
        exact storedNew row inScan)
    rw [newWidth] at copied
    rw [copied]
    refine InsertFits.copy _ ⟨newShape, []⟩ 0 customers.scanRows rfl newAlias newReady
      (fun column m => (newPlain column m).1) (fun column m => (newPlain column m).2) newUnchecked ?_ ?_ ?_ storedNew ?_ ?_ ?_
    · intro key m
      have listed : key ∈ c.state.database.catalog.uniqueKeys 2 newShape := m
      rw [uniqueKeys] at listed
      simp only [List.mem_singleton] at listed
      subst listed
      exact ⟨rfl, rfl⟩
    · exact fun row m => admitted.rowsAliased row (inRows row m) 0 oldAlias
    · intro row m
      rw [admitted.rowsWide row (inRows row m), oldWidth, newWidth]
    · intro row m i column value atColumn atValue required
      have mapped : (newShape.columns.map CatalogColumn.notNull)[i]? = some column.notNull := by
        simp [List.getElem?_map, atColumn]
      rw [newNotNull] at mapped
      rcases i with _ | _ | _ | i
      · simp at mapped; simp [mapped] at required
      · exact fun isNull => named row (inRows row m) (by rw [atValue, isNull])
      · obtain ⟨oldColumn, atOld, oldRequired⟩ := exists_of_map_getElem?
          (show (customers.shape.columns.map CatalogColumn.notNull)[2]? = some true by rw [oldNotNull]; rfl)
        exact valid.1.notNull 0 customers present row (inRows row m) 2 oldColumn value atOld atValue oldRequired
      · simp at mapped
    · exact (customers.scanRows_perm.map Row.rowid).nodup_iff.mpr (admitted.rowidsDistinct)
    · exact fun row m => admitted.rowidsInRange row (inRows row m)
  obtain ⟨output, next, step, noError, -⟩ := runScriptStep_insertSelect_success (value := 0) (table := ⟨newShape, []⟩)
    (rows := Resolved.sourceRows customers) found rfl rfl presentNew certain fits rfl
    (fun source transfer => by
      exfalso
      unfold insertSelectTransferRowids at transfer
      split at transfer
      · simp [newAlias] at transfer
      · simp at transfer) rfl rfl rfl
  exact ⟨output, next, step, noError⟩

end RebuildGuide
