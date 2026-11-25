import ItemInsertSite

set_option doc.verso true

/-! A fixture module of {lit}`tests/surface_schema_script_test.py` (statement rule pilot, "Client claims"): the
outcome of the insert of one item into {lit}`items` on a valid database with arbitrary rows. The readiness check of
the kind rule of plain INSERT passes for every id. A new id satisfies {name}`Belay.Sqlite.Model.InsertFits`, so the
insert succeeds ({name}`Belay.Sqlite.Model.insertOutcome_of_fits`); an id that a stored row has fails with a
constraint violation. The facts use the data functions {name}`Belay.Sqlite.Model.LiteralData.insertReady` and
{name}`Belay.Sqlite.Model.insertOutcome` and no step of a statement. -/

namespace ItemInsertSite
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- For every row lists of a valid database with {name}`itemsCatalog`, id and name: the readiness check of the
insert of {name}`itemValues` into {name}`itemsTable` passes. The id need not be new. Proof sketch: the validity of
the database gives the constraints of the old table and the range of its rowids; the shape gives the alias and the
stored forms; an {lean}`Int64` is in range. -/
theorem items_ready (rows : List (List Row)) (valid : ({ catalog := itemsCatalog, rows } : Model.Database).Valid profile)
    (id : Int64) (name : String) :
    LiteralData.insertReady (({ catalog := itemsCatalog, rows } : Model.Database).keys 0 (itemsTable rows))
      (itemsTable rows) [itemValues id name] (LiteralData.inserted (itemsTable rows) [itemValues id name]) = true := by
  have found := items_table rows
  have before : LiteralData.tableReady (({ catalog := itemsCatalog, rows } : Model.Database).keys 0 (itemsTable rows))
      (itemsTable rows) = true :=
    (Table.constraints_iff _ _).2 ⟨valid.notNull _ _ found, valid.typesFit _ _ found, valid.check _ _ found,
      valid.unique _ _ found⟩
  have aliasOk : LiteralData.aliasReady (itemsTable rows).shape = true := by
    show LiteralData.aliasReady itemsShape = true
    decide
  have storedOk : [itemValues id name].all (fun values => values.length == (itemsTable rows).shape.columns.length &&
      ((itemsTable rows).shape.columns.zip values).all fun (column, value) =>
        LiteralData.storedForm column.affinity value) = true := by
    simp [itemValues, itemsShape, items_id_integer, items_name_text, LiteralData.storedForm, Value.store, numericStore]
  have boundedOk : (LiteralData.inserted (itemsTable rows) [itemValues id name]).rows.all
      (fun row => LiteralData.boundedInteger row.rowid) = true := by
    rw [items_inserted, List.all_append, Bool.and_eq_true]
    refine ⟨(Table.rowidsInRange_iff (itemsTable rows)).2 (valid.admitted.rowidsInRange _ _ found), ?_⟩
    simp only [itemRow, List.all_cons, List.all_nil, Bool.and_true, LiteralData.boundedInteger, decide_eq_true_eq]
    exact ⟨Int64.le_toInt id, Int64.toInt_lt id⟩
  simp only [LiteralData.insertReady, before, aliasOk, storedOk, boundedOk, Bool.and_self]

/-- For every row lists of a valid database with {name}`itemsCatalog`, id and name: if no stored row of
{lit}`items` has the id as its rowid, the row {name}`itemValues` fits the table ({name}`InsertFits`). Proof sketch:
{name}`InsertFits.of_valid_alias` with the row {name}`itemRow`; the one key is on the alias, and each fact of the
one new row follows from its two cells. -/
theorem items_fits (rows : List (List Row)) (valid : ({ catalog := itemsCatalog, rows } : Model.Database).Valid profile)
    (id : Int64) (name : String) (fresh : ∀ row ∈ rows.getD 0 [], row.rowid ≠ id.toInt) :
    InsertFits (({ catalog := itemsCatalog, rows } : Model.Database).keys 0 (itemsTable rows)) (itemsTable rows)
      [itemValues id name] := by
  refine InsertFits.of_valid_alias valid (items_table rows) (position := 0) rfl items_plain ?_ [itemRow id name]
    (by simp [itemRow, itemValues]) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [items_keys]
    simp [UniqueKey.ofColumns, itemsShape]
  · simp [Table.RowsWide, itemRow, itemValues, itemsShape]
  · intro row member position column value
    simp only [List.mem_singleton] at member
    subst member
    rcases position with _ | _ | _ <;> simp [itemRow, itemValues, itemsShape] <;> rintro rfl rfl <;>
      simp [items_id_integer, items_name_text, Value.store, numericStore]
  all_goals simp [Table.NotNull, Table.TypesFit, Table.ChecksHold, CatalogTable.allChecks, Table.RowidsInRange,
    Table.RowidsDistinct, validRowid, itemRow, itemValues, itemsShape]
  all_goals try (intro position column value; rcases position with _ | _ | _ <;> simp <;> rintro rfl rfl <;> simp)
  all_goals first | exact ⟨Int64.le_toInt id, Int64.toInt_lt id⟩ | simpa using fresh

/-- For every row lists, id and name such that a stored row of {lit}`items` has the id as its rowid, and for every
database and keys: the outcome of the insert of {name}`itemValues` is a constraint violation that keeps the
database. The theorem needs no validity. Proof sketch: the alias cell is an integer, and the new row repeats the
rowid of the stored row ({name}`LiteralData.rowidsDistinct_eq_false_of_repeated`), so
{name}`insertOutcome_constraintViolation` applies. -/
theorem items_taken_outcome (rows : List (List Row)) (id : Int64) (name : String)
    (taken : ∃ row ∈ rows.getD 0 [], row.rowid = id.toInt) (database : Model.Database) (keys : List UniqueKey) :
    insertOutcome database 0 keys (itemsTable rows) [itemValues id name]
      (LiteralData.inserted (itemsTable rows) [itemValues id name]) = .error (.constraintViolation, database) := by
  obtain ⟨row, member, same⟩ := taken
  refine insertOutcome_constraintViolation (fun _ added => ?_) (.inr ?_)
  · obtain rfl := List.mem_singleton.1 added
    rfl
  · exact LiteralData.rowidsDistinct_eq_false_of_repeated (items_inserted rows id name) member
      (List.mem_singleton_self (itemRow id name)) same

end ItemInsertSite
