import Belay.Sqlite.Model.PlainScanProductions
import Belay.Sqlite.Model.IntegerCompareLaws
import Belay.Sqlite.Model.QueryLaws
import Belay.Sqlite.Model.SourceScanOrders

set_option doc.verso true

/-! The index of a rowid alias reads rows in scan order (ADR 0017, S6). A table with an {lit}`INTEGER PRIMARY KEY`
keeps its key as the rowid, so SQLite reads the table by the key in the order of the scan. The model lists the key
among the ways to read the table ({lit}`Catalog.accessKeys`); this module shows that this way gives the scan order,
so a query that reads such a table has one production. -/

namespace Belay.Sqlite.Model
open Resolved

/-- For every sort relation and item, and every list in which each item is at most the new item: inserting the new
item after its equals ({name}`insertStable`) puts it at the end. Proof sketch: induction on the list; the head is
at most the item, so the item goes after it. -/
theorem insertStable_append {α : Type} (le : α → α → Bool) (item : α) :
    ∀ items : List α, (∀ other ∈ items, le other item = true) → insertStable le item items = items ++ [item]
  | [], _ => rfl
  | head :: tail, below => by
    simp only [insertStable, below head (List.mem_cons_self ..), ite_true, List.cons_append, List.cons.injEq, true_and]
    exact insertStable_append le item tail fun other member => below other (List.mem_cons_of_mem _ member)

/-- For every sort relation and list that is in order by it: {name}`stableSort` keeps the list. In plain words,
sorting a sorted list changes nothing. Proof sketch: each item goes after the items before it
({name}`insertStable_append`), so the fold appends the items one after the other. -/
theorem stableSort_of_sorted {α : Type} (le : α → α → Bool) (items : List α) (sorted : items.Pairwise (le · ·)) :
    stableSort le items = items := by
  suffices ∀ (items start : List α), (start ++ items).Pairwise (le · ·) →
      items.foldl (fun sorted item => insertStable le item sorted) start = start ++ items from by
    have := this items [] (by simpa using sorted)
    simpa [stableSort] using this
  intro items
  induction items with
  | nil => intro start _; simp
  | cons item rest ih =>
    intro start ordered
    have before : ∀ other ∈ start, le other item = true := fun other member =>
      (List.pairwise_append.mp ordered).2.2 other member item (List.mem_cons_self ..)
    rw [List.foldl_cons, insertStable_append le item start before, ih (start ++ [item]) (by simpa using ordered)]
    simp

/-- For every table that has a rowid (it is no {lit}`WITHOUT ROWID` table) and whose rows hold their rowid, as an
integer, in the cell at a position: the order of the index on the cell at that position, ascending and under the
default collation, over the scan of the table is the scan. In plain words, reading such a table by the index of its
rowid alias gives the order of a full scan. Proof sketch: the scan is in order of the rowid
({name}`stableSort_sorted`), which is the order of the key cells; sorting a sorted list keeps it
({name}`stableSort_of_sorted`), and every row is in the index. -/
theorem Table.indexOrder_alias (table : Table) (position : Nat) (rowid : table.shape.withoutRowid = false)
    (aliased : ∀ row ∈ table.rows, row.values[position]? = some (.integer row.rowid)) :
    Table.indexOrder table.scanRows [{ term := .column position }] none = table.scanRows := by
  have scanSorted : table.scanRows.Pairwise (fun a b => decide (a.rowid ≤ b.rowid)) := by
    unfold Table.scanRows
    simp only [rowid, Bool.false_eq_true, ite_false]
    exact stableSort_sorted _ (fun a b c ab bc => by simp at *; omega) (fun a b => by simp; omega) _
  have inTable : ∀ row ∈ table.scanRows, row ∈ table.rows := fun row member => table.scanRows_perm.mem_iff.mp member
  have cell : ∀ row ∈ table.scanRows, [IndexKey.valueOf { term := .column position } row.values] = [.integer row.rowid] := by
    intro row member
    have := aliased row (inTable row member)
    simp [IndexKey.valueOf, List.getD_eq_getElem?_getD, this]
  unfold Table.indexOrder
  have everyRow : table.scanRows.filter (fun _ => true) = table.scanRows := List.filter_eq_self.mpr (fun _ _ => rfl)
  simp only [Option.all_none, everyRow, List.map_cons, List.map_nil]
  have keeps : stableSort (fun a b => (compareSort [(false, Collation.binary)]
      [IndexKey.valueOf { term := .column position } a.values] [IndexKey.valueOf { term := .column position } b.values]).isLE)
      table.scanRows = table.scanRows := by
    apply stableSort_of_sorted
    refine List.Pairwise.imp_of_mem (fun {a b} ma mb order => ?_) scanSorted
    rw [cell a ma, cell b mb]
    simp only [compareSort, compareTerm, Bool.false_eq_true, ite_false, Collation.compare_integer,
      List.headD_cons, Ordering.then_eq]
    have atMost : a.rowid ≤ b.rowid := by simpa using order
    simp only [Ord.compare, compareOfLessAndEq]
    split
    · rfl
    · split
      · rfl
      · omega
  rw [keeps]
  have none : (table.scanRows.filter fun row => !(table.scanRows.any (·.rowid == row.rowid))) = [] := by
    rw [List.filter_eq_nil_iff]
    intro row member
    have held : (table.scanRows.any fun other => other.rowid == row.rowid) = true :=
      List.any_eq_true.mpr ⟨row, member, by simp⟩
    simp [held]
  rw [none, List.append_nil]

/-- For every table that has a rowid and holds its rowid, as an integer, in the cell at a position, and every
catalog in which the only way to read the table besides its scan is the index of that cell (no other key, no
index): the table has one access order, the scan ({name}`Table.accessOrders`). In plain words, a table whose only
key is its rowid alias is read in one order. Proof sketch: {name}`Table.accessOrders_single` with
{name}`Table.indexOrder_alias`. -/
theorem Table.accessOrders_alias (catalog : Catalog) (position : Nat) (table : Table) (alias : Nat)
    (rowid : table.shape.withoutRowid = false)
    (aliased : ∀ row ∈ table.rows, row.values[alias]? = some (.integer row.rowid))
    (only : ∀ access ∈ catalog.accessKeys position table.shape, access = ([{ term := .column alias }], none)) :
    Table.accessOrders catalog position table = [table.scanRows] := by
  refine Table.accessOrders_single catalog position table fun access member => ?_
  rw [only access member]
  simp only []
  rw [Table.indexOrder_alias table alias rowid aliased]

end Belay.Sqlite.Model
