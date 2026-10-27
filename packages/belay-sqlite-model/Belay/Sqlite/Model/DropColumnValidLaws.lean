import Belay.Sqlite.Model.DropColumnAdmittedLaws

set_option doc.verso true

/-! The remaining facts of a valid database after ALTER TABLE DROP COLUMN (ADR 0019, D4, ADR 0022, D3): the rows
stay shaped to the catalog, the STRICT types and CHECK constraints hold, and no two rows break a unique key.
{lit}`DropColumnAdmittedLaws.lean` has the other facts. -/

namespace Belay.Sqlite.Model

/-- For every shaped database and every drop that the model runs: the database after the drop is shaped
({name}`Database.RowsShaped`). Proof sketch: the rows have as many entries as the catalog has objects; a position
without a table in the catalog of the statement is one without a table before the drop, where the rows are empty
({name}`Catalog.tableAt_of_outline`, {name}`Catalog.tableAt_dropColumn_same`, {name}`rows_modify_getD`). -/
theorem Database.RowsShaped.dropColumn {database : Database} {position index : Nat} {stored : Catalog}
    (shaped : database.RowsShaped) (runs : database.runsDropColumn position index stored = true) :
    (database.dropColumn position index stored).RowsShaped := by
  obtain ⟨⟨shape, found, _, _⟩, same, _⟩ := Database.runsDropColumn_spec runs
  refine ⟨?_, fun other absent => ?_⟩
  · simp only [Database.dropColumn, List.length_modify]
    rw [Catalog.length_of_outline same, Catalog.length_dropColumn]
    exact shaped.1
  · have shapes := Catalog.tableAt_of_outline same other
    have absent : stored.tableAt other = none := absent
    rw [absent] at shapes
    by_cases here : position = other
    · subst here
      simp [Catalog.tableAt_dropColumn_same found] at shapes
    · have before : database.catalog.tableAt other = none := by
        rw [← Catalog.tableAt_dropColumn_other database.catalog index (Ne.symm here)]
        cases hd : (database.catalog.dropColumn position index).tableAt other with
        | none => rfl
        | some table => simp [hd] at shapes
      simp only [Database.dropColumn]
      rw [rows_modify_getD _ _ _ _ rfl]
      have empty := shaped.2 other before
      simp only [here, ↓reduceIte]
      exact empty

/-- For every database that has {name}`Database.TypesFit` and every drop that the model runs: the database after the
drop has it. Proof sketch: {name}`Table.TypesFit.dropColumn`. -/
theorem Database.TypesFit.dropColumn {database : Database} {position index : Nat} {stored : Catalog}
    (holds : database.TypesFit) (runs : database.runsDropColumn position index stored = true) :
    (database.dropColumn position index stored).TypesFit := by
  obtain ⟨⟨shape, found, _, _⟩, same, _⟩ := Database.runsDropColumn_spec runs
  exact Database.EveryTable.of_outline (fun _ _ _ rows shapes holds => holds.of_blankNames rows shapes)
    (Database.EveryTable.dropColumn found holds (fun _ _ _ kept => kept)
      (fun _ _ fits => Table.TypesFit.dropColumn fits index)) same

/-- For every database that has {name}`Database.ChecksHold` and every drop that the model runs: the database after
the drop has it. Proof sketch: the CHECK constraints that stay read no dropped cell, so
{name}`Table.ChecksHold.dropColumn` applies. -/
theorem Database.ChecksHold.dropColumn {database : Database} {position index : Nat} {stored : Catalog}
    (holds : database.ChecksHold) (runs : database.runsDropColumn position index stored = true) :
    (database.dropColumn position index stored).ChecksHold := by
  obtain ⟨⟨shape, found, clean, _⟩, same, _⟩ := Database.runsDropColumn_spec runs
  exact Database.EveryTable.of_outline (fun _ _ _ rows shapes holds => holds.of_blankNames rows shapes)
    (Database.EveryTable.dropColumn found holds (fun _ _ _ kept => kept)
      (fun table present checks => Table.ChecksHold.dropColumn checks
        (by rw [Database.table_shape found present]; exact clean))) same

/-- For every database that has {name}`Database.KeysUnique` and every drop that the model runs: the database after the
drop has it. Proof sketch: the unique keys of the table after the drop are the keys before it, changed by the drop
({name}`Catalog.uniqueKeys_dropColumn_same`), and none of them reads the column
({name}`Catalog.uniqueKeys_free`), so {name}`Table.KeysUnique.dropColumn` applies; the keys of every other table are
those before ({name}`Catalog.uniqueKeys_dropColumn_other`); the catalog of the statement has the outline of the
catalog after the drop ({name}`Database.KeysUnique.of_outline`). -/
theorem Database.KeysUnique.dropColumn {database : Database} {position index : Nat} {stored : Catalog}
    (holds : database.KeysUnique) (runs : database.runsDropColumn position index stored = true) :
    (database.dropColumn position index stored).KeysUnique := by
  obtain ⟨⟨shape, found, clean, indexes⟩, same, _⟩ := Database.runsDropColumn_spec runs
  exact Database.KeysUnique.of_outline
    (Database.EveryTable.dropColumn (fact' := fun other table =>
        table.KeysUnique ((database.catalog.dropColumn position index).uniqueKeys other table.shape)) found holds
      (fun other table different kept => by
        rw [Catalog.uniqueKeys_dropColumn_other database.catalog index table.shape different]
        exact kept)
      (fun table present kept => by
        have shaped := Database.table_shape found present
        subst shaped
        have clean := clean
        simp only [Table.dropColumn]
        rw [Catalog.uniqueKeys_dropColumn_same database.catalog clean]
        exact Table.KeysUnique.dropColumn kept index (Catalog.uniqueKeys_free clean indexes))) same

end Belay.Sqlite.Model
