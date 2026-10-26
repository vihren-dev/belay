import Belay.Sqlite.Model.ForeignKeyAddColumnLink
import Belay.Sqlite.Model.ForeignKeyAddColumnPairs
import Belay.Sqlite.Model.AddColumnFromValid
import Belay.Sqlite.Model.ForeignKeyUpdateCoverage

set_option doc.verso true

/-! The premises of ADD COLUMN on the columns that a mapping reads in the extended table, and the
selected mapping that meets them from facts about the declarations and the parent indexes. -/

namespace Belay.Sqlite.Model

/-- The condition of ADD COLUMN on the declarations: if the target holds a table, every column of a
declaration of the table is a column of it. Without it a declaration that read a missing cell as
NULL reads the new cell. A target without a table requires nothing. The resolver builds declarations
from column names of the table, but the catalog type does not state this. -/
def Database.DeclarationsBelowAt (database : Database) (target : Nat) : Prop :=
  ∀ table, database.table target = some table → ∀ key ∈ table.shape.allForeignKeys,
    ∀ place ∈ key.columns, place < table.shape.columns.length

/-- The condition of ADD COLUMN on parent selection: if the catalog has a table at the target, it
selects its parents below its width ({name}`CatalogTable.SelectionBelow`). A target without a table
requires nothing. -/
def Database.SelectionBelowAt (database : Database) (target : Nat) : Prop :=
  ∀ shape, database.catalog.tableAt target = some shape → shape.SelectionBelow database.catalog target

/-- The dependencies of a supplied mapping on the table at the target, which ADD COLUMN extends:
* its rows are wide ({name}`Table.RowsWide`), so the new cell is the one after the last column;
* each child column that a declaration of the table reads ({name}`ForeignKeyLink.childReads`) is a
  column of the table;
* each parent key that a mapping finds in the table reads only columns of the table
  ({name}`ParentKey.ReadsBelow`).
Without the first the new cell lands in the cell of an old column. Without the second a declaration
that read a missing cell as NULL reads the new cell. Without the third a parent key that named a
missing column names the new one. -/
structure Database.AddColumnReads (database : Database) (mapping : ForeignKeyMapping) (target : Nat)
    (table : Table) : Prop where
  /-- Each row of the table has one cell for each column. -/
  wide : table.RowsWide
  /-- Each child column that a declaration of the table reads is a column of the table. -/
  children : ∀ key ∈ table.shape.allForeignKeys, ∀ position ∈ (mapping.link target key).childReads,
    position < table.shape.columns.length
  /-- Each parent key that the mapping finds in the table reads only columns of the table. -/
  parents : ∀ other otherTable, database.table other = some otherTable →
    ∀ key ∈ otherTable.shape.allForeignKeys, ∀ comparison, mapping.parent other key = .located target comparison →
      comparison.ReadsBelow table.shape.columns.length

/-- For every database with a table at the target: if the rows of the table are wide, every column
of a declaration of the table is a column of it, and the table selects its parents below its width
({name}`CatalogTable.SelectionBelow`), the table meets {name}`Database.AddColumnReads` under the
mapping that the catalog selects. Proof sketch: a link reads only declaration columns, because
each pair of a selected key has a child column of the declaration ({name}`Catalog.parentKey_pairs`);
a parent key located at the target reads only columns below its width by the same lemma. -/
theorem Database.AddColumnReads.of_selected (database : Database) {target : Nat} {table : Table}
    (found : database.table target = some table) (wide : table.RowsWide)
    (declared : ∀ key ∈ table.shape.allForeignKeys, ∀ place ∈ key.columns, place < table.shape.columns.length)
    (below : table.shape.SelectionBelow database.catalog target) :
    database.AddColumnReads database.catalog.foreignKeyMapping target table := by
  have shape := Database.tableAt_of_table found
  refine ⟨wide, ?_, ?_⟩
  · intro key inside position reads
    have columns := declared key inside
    simp only [ForeignKeyMapping.link, Catalog.foreignKeyMapping, ForeignKeyLink.childReads] at reads
    cases link : database.catalog.parentLink key with
    | missing => rw [link] at reads; exact columns position reads
    | mismatch _ => rw [link] at reads; exact columns position reads
    | located place comparison =>
      rw [link] at reads
      obtain ⟨parent, _, chosen⟩ := Catalog.parentLink_located link
      cases comparison with
      | rowid => exact columns position (List.mem_of_mem_take reads)
      | columns pairs =>
        obtain ⟨pair, inPairs, eq⟩ := List.mem_map.mp reads
        exact eq ▸ columns _ (Catalog.parentKey_pairs _ _ _ key pairs chosen pair inPairs).1
  · intro other otherTable otherFound key declaredKey comparison selected
    cases comparison with
    | rowid => trivial
    | columns pairs =>
      intro pair inPairs
      obtain ⟨parent, search, chosen⟩ := Catalog.parentLink_located (catalog := database.catalog) selected
      obtain ⟨object, atPlace, entry, _⟩ := Catalog.findTable_some database.catalog _ _ _ search
      have present : database.catalog.tableAt target = some parent := by
        obtain ⟨_, objectEntry⟩ := object
        cases entry
        simp [Catalog.tableAt, atPlace]
      rw [shape, Option.some.injEq] at present
      subst present
      exact (Catalog.parentKey_pairs _ _ _ key pairs chosen pair inPairs).2 below

end Belay.Sqlite.Model
