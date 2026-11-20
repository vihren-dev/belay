import Belay.Sqlite.Model.Schema.Writes.CopyInsertFits
import Belay.Sqlite.Model.Schema.Columns.CatalogTableLaws
import Belay.Sqlite.Model.Schema.Rows.GroupKeyConflictLaws

set_option doc.verso true

/-! Success premises for a literal INSERT into a valid database. -/

namespace Belay.Sqlite.Model

/-- The new rows of a literal INSERT, with their allocated rowids, alias cells and
generated cells. The shape is the target shape. Use this table to check constraints
on the incoming batch. An empty batch has no rows. -/
def LiteralData.insertedBatch (table : Table) (values : List (List Value)) : Table :=
  { table with rows := (inserted table values).rows.drop table.rows.length }

/-- For any table in a valid database, the literal cells fit under these conditions:
* Each input has one stored value per column and supplies an integer or NULL for a rowid alias.
* The rows of {name}`LiteralData.insertedBatch` meet NOT NULL, STRICT types and CHECK.
  Their rowids are in range and distinct, and each is absent from the old rows.
* For every target key the new rows are pairwise conflict-free, and each old row
  is conflict-free with each new row under {name}`LiteralData.keyEqual`.
  A key with a NULL term or an inapplicable partial-index filter causes no conflict.

An empty batch satisfies the incoming-row conditions. Proof sketch: validity supplies
the old rows' constraints and the affinity of the alias. Split each row check and
each pairwise check over the old prefix and the new suffix. -/
theorem InsertFits.of_valid {database : Database} {target : Nat} {table : Table}
    (valid : database.Valid profile) (found : database.table target = some table)
    (values : List (List Value))
    (aliasFree : ∀ cells ∈ values, LiteralData.aliasMismatch table.shape cells = false)
    (stored : ∀ cells ∈ values, cells.length = table.shape.columns.length ∧
      ∀ pair ∈ table.shape.columns.zip cells, Value.store pair.1.affinity pair.2 = pair.2) :
    let batch := LiteralData.insertedBatch table values
    batch.NotNull → batch.TypesFit → batch.ChecksHold → batch.RowidsInRange →
    batch.RowidsDistinct → (∀ old ∈ table.rows, ∀ newRow ∈ batch.rows, old.rowid ≠ newRow.rowid) →
    batch.KeysUnique (database.keys target table) →
    (∀ key ∈ database.keys target table, ∀ old ∈ table.rows, ∀ newRow ∈ batch.rows,
      LiteralData.keyEqual key old newRow = false) →
    InsertFits (database.keys target table) table values := by
  intro batch notNull typed checked bounded distinct freshIds unique freshKeys
  obtain ⟨added, appendRows⟩ := LiteralData.inserted_rows_prefix table values
  have batchRows : batch.rows = added := by simp [batch, LiteralData.insertedBatch, appendRows]
  have rows : (LiteralData.inserted table values).rows = table.rows ++ batch.rows := batchRows ▸ appendRows
  have batchShape : batch.shape = table.shape := rfl
  have shape := LiteralData.shape_inserted table values
  refine ⟨aliasFree, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨_, _, _, _, _, _, aliases, _⟩ := (CatalogTable.supported_iff _ _).mp
      (valid.admitted.catalogSupported.tableSupported (Database.tableAt_of_table found))
    cases alias : table.shape.rowidAlias with
    | none => simp [LiteralData.aliasReady, alias]
    | some pos =>
      obtain ⟨_, _, column, atColumn, _, affinity⟩ := aliases pos alias
      simp [LiteralData.aliasReady, alias, atColumn, affinity]
  · simpa [List.all_eq_true, LiteralData.storedForm] using stored
  · simpa only [LiteralData.notNullRows, batchShape, shape, rows, List.all_append, Bool.and_eq_true] using
      And.intro ((table.notNullRows_iff).2 (valid.notNull _ _ found)) (batch.notNullRows_iff.2 notNull)
  · simpa only [LiteralData.typedRows, batchShape, shape, rows, List.all_append, Bool.and_eq_true] using
      And.intro (table.typedRows_iff.2 (valid.typesFit _ _ found)) (batch.typedRows_iff.2 typed)
  · simpa only [LiteralData.checkedRows, batchShape, shape, rows, List.all_append, Bool.and_eq_true] using
      And.intro (table.checkedRows_iff.2 (valid.check _ _ found)) (batch.checkedRows_iff.2 checked)
  · apply (Table.keysUnique_iff ..).2
    intro key member
    rw [rows, List.pairwise_append]
    exact ⟨valid.unique _ _ found key member, unique key member, freshKeys key member⟩
  · apply (Table.rowidsDistinct_iff _).2
    rw [Table.RowidsDistinct, rows, List.map_append, List.nodup_append]
    refine ⟨valid.admitted.rowidsDistinct _ _ found, distinct, ?_⟩
    simpa only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] using freshIds
  · change (LiteralData.inserted table values).rowidsInRange = true
    apply (Table.rowidsInRange_iff _).2
    simpa only [Table.RowidsInRange, rows, List.mem_append, or_imp, forall_and] using
      And.intro (valid.admitted.rowidsInRange _ _ found) bounded

/-- Suppose a valid database contains a table with an explicit integer rowid alias,
no generated columns and an alias term in every unique key. The cells of any incoming
rows fit if each row carries its rowid in the alias, has the target width and stored
values, and satisfies NOT NULL, STRICT types and CHECK. The incoming rowids must be
in range, pairwise distinct and absent from the stored rowids. The target can already
contain rows. For other keys or generated cells use {name}`InsertFits.of_valid`.
Proof sketch: {name}`LiteralData.inserted_copy_rows` identifies the new rows. The alias
cells of both stored and incoming rows equal their rowids, so distinct rowids certify
every key on the alias. -/
theorem InsertFits.of_valid_alias {database : Database} {target : Nat} {table : Table}
    (valid : database.Valid profile) (found : database.table target = some table)
    {position : Nat} (alias : table.shape.rowidAlias = some position)
    (plain : ∀ column ∈ table.shape.columns, column.generated = none)
    (aliasKeys : ∀ key ∈ database.keys target table,
      ∃ collation, { term := .column position, collation } ∈ key.terms)
    (rows : List Row) (aliased : ∀ row ∈ rows, row.values[position]? = some (.integer row.rowid)) :
    let incoming := { table with rows }
    incoming.RowsWide → incoming.RowsStored → incoming.NotNull → incoming.TypesFit →
    incoming.ChecksHold → incoming.RowidsInRange → incoming.RowidsDistinct →
    (∀ old ∈ table.rows, ∀ newRow ∈ rows, old.rowid ≠ newRow.rowid) →
    InsertFits (database.keys target table) table (rows.map Row.values) := by
  intro incoming wide stored notNull typed checked bounded distinct fresh
  have written := LiteralData.inserted_copy_rows table.shape position alias plain rows table rfl aliased
  have batch : LiteralData.insertedBatch table (rows.map Row.values) = incoming := by
    simp [LiteralData.insertedBatch, incoming, written]
  have apart (key) (member : key ∈ database.keys target table) (a b : Row)
      (cellA : a.values[position]? = some (.integer a.rowid))
      (cellB : b.values[position]? = some (.integer b.rowid)) (different : a.rowid ≠ b.rowid) :
      LiteralData.keyEqual key a b = false := by
    obtain ⟨collation, term⟩ := aliasKeys key member
    apply Bool.eq_false_iff.mpr
    intro conflict
    have equal := LiteralData.keyEqual_column term conflict
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, cellA, cellB] at equal
    exact different (Collation.compare_integer_eq collation _ _ equal)
  apply of_valid valid found
  · rintro cells member
    obtain ⟨row, inRows, rfl⟩ := List.mem_map.mp member
    simp [LiteralData.aliasMismatch, alias, aliased row inRows]
  · rintro cells member
    obtain ⟨row, inRows, rfl⟩ := List.mem_map.mp member
    exact ⟨wide row inRows, (zip_forall_iff ..).2 (stored row inRows)⟩
  all_goals rw [batch]
  · exact notNull
  · exact typed
  · exact checked
  · exact bounded
  · exact distinct
  · exact fresh
  · intro key member
    exact (List.pairwise_map.mp distinct).imp_of_mem fun ha hb ne =>
      apart key member _ _ (aliased _ ha) (aliased _ hb) ne
  · exact fun key member old ho newRow hn => apart key member old newRow
      (valid.admitted.rowsAliased _ _ found old ho position alias) (aliased _ hn) (fresh _ ho _ hn)

end Belay.Sqlite.Model
