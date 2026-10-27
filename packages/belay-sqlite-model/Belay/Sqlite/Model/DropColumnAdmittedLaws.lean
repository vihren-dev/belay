import Belay.Sqlite.Model.DropColumnDatabaseLaws

set_option doc.verso true

/-! The facts of an admitted and of a valid database after ALTER TABLE DROP COLUMN (ADR 0019, D4, ADR 0022, D3).
When the model runs the drop ({lit}`Database.runsDropColumn`), the database that {lit}`step` stores has every fact
about the rows that the database before it had. Each fact first holds for the database with the catalog after the
drop ({lit}`Database.EveryTable.dropColumn`), and then passes to the catalog of the statement, which has the same
outline ({lit}`Database.EveryTable.of_outline`). The catalog of the statement is supported by the resolver, and the
foreign-key facts are in separate files. -/

namespace Belay.Sqlite.Model

/-- For every database that the model drops a column of, and every table at the position: the table has the shape
of the catalog at the position. Proof sketch: the definition of {name}`Database.table`. -/
theorem Database.table_shape {database : Database} {position : Nat} {shape : CatalogTable} {table : Table}
    (found : database.catalog.tableAt position = some shape) (present : database.table position = some table) :
    table.shape = shape := by
  unfold Database.table at present
  rw [found] at present
  cases present
  rfl

/-- For every database that has {name}`Database.RowidsDistinct` and every drop that the model runs: the database
after the drop has it. Proof sketch: the drop keeps the rowids ({name}`Table.RowidsDistinct.dropColumn`). -/
theorem Database.RowidsDistinct.dropColumn {database : Database} {position index : Nat} {stored : Catalog}
    (holds : database.RowidsDistinct) (runs : database.runsDropColumn position index stored = true) :
    (database.dropColumn position index stored).RowidsDistinct := by
  obtain ⟨⟨shape, found, _, _⟩, same, _⟩ := Database.runsDropColumn_spec runs
  exact Database.RowidsDistinct.of_outline
    (Database.EveryTable.dropColumn found holds (fun _ _ _ kept => kept)
      (fun _ _ distinct => Table.RowidsDistinct.dropColumn distinct index)) same

/-- For every database that has {name}`Database.RowidsInRange` and every drop that the model runs: the database
after the drop has it. Proof sketch: the drop keeps the rowids ({name}`Table.RowidsInRange.dropColumn`). -/
theorem Database.RowidsInRange.dropColumn {database : Database} {position index : Nat} {stored : Catalog}
    (holds : database.RowidsInRange) (runs : database.runsDropColumn position index stored = true) :
    (database.dropColumn position index stored).RowidsInRange := by
  obtain ⟨⟨shape, found, _, _⟩, same, _⟩ := Database.runsDropColumn_spec runs
  exact Database.RowidsInRange.of_outline
    (Database.EveryTable.dropColumn found holds (fun _ _ _ kept => kept)
      (fun _ _ inRange => Table.RowidsInRange.dropColumn inRange index)) same

/-- For every database that has {name}`Database.RowsWide` and every drop that the model runs: the database after
the drop has it. Proof sketch: a row and the columns each lose one place ({name}`Table.RowsWide.dropColumn`). -/
theorem Database.RowsWide.dropColumn {database : Database} {position index : Nat} {stored : Catalog}
    (holds : database.RowsWide) (runs : database.runsDropColumn position index stored = true) :
    (database.dropColumn position index stored).RowsWide := by
  obtain ⟨⟨shape, found, clean, _⟩, same, _⟩ := Database.runsDropColumn_spec runs
  exact Database.RowsWide.of_outline
    (Database.EveryTable.dropColumn found holds (fun _ _ _ kept => kept)
      (fun table present wide => Table.RowsWide.dropColumn wide
        (by rw [Database.table_shape found present]; exact clean.inside))) same

/-- For every database that has {name}`Database.RowsStored` and every drop that the model runs: the database after
the drop has it. Proof sketch: {name}`Table.RowsStored.dropColumn`. -/
theorem Database.RowsStored.dropColumn {database : Database} {position index : Nat} {stored : Catalog}
    (holds : database.RowsStored) (runs : database.runsDropColumn position index stored = true) :
    (database.dropColumn position index stored).RowsStored := by
  obtain ⟨⟨shape, found, _, _⟩, same, _⟩ := Database.runsDropColumn_spec runs
  exact Database.RowsStored.of_outline
    (Database.EveryTable.dropColumn found holds (fun _ _ _ kept => kept)
      (fun _ _ stored => Table.RowsStored.dropColumn stored index)) same

/-- For every database that has {name}`Database.RowsAliased` and every drop that the model runs: the database after
the drop has it. Proof sketch: the column is not the rowid alias ({name}`CatalogTable.DropsCleanly`), so
{name}`Table.RowsAliased.dropColumn` applies. -/
theorem Database.RowsAliased.dropColumn {database : Database} {position index : Nat} {stored : Catalog}
    (holds : database.RowsAliased) (runs : database.runsDropColumn position index stored = true) :
    (database.dropColumn position index stored).RowsAliased := by
  obtain ⟨⟨shape, found, clean, _⟩, same, _⟩ := Database.runsDropColumn_spec runs
  exact Database.RowsAliased.of_outline
    (Database.EveryTable.dropColumn found holds (fun _ _ _ kept => kept)
      (fun table present aliased => Table.RowsAliased.dropColumn aliased
        (by rw [Database.table_shape found present]; exact clean.alias))) same

/-- For every database that has {name}`Database.NotNull` and every drop that the model runs: the database after
the drop has it. Proof sketch: {name}`Table.NotNull.dropColumn`. -/
theorem Database.NotNull.dropColumn {database : Database} {position index : Nat} {stored : Catalog}
    (holds : database.NotNull) (runs : database.runsDropColumn position index stored = true) :
    (database.dropColumn position index stored).NotNull := by
  obtain ⟨⟨shape, found, _, _⟩, same, _⟩ := Database.runsDropColumn_spec runs
  exact Database.EveryTable.of_outline (fun _ _ _ rows shapes holds => holds.of_blankNames rows shapes)
    (Database.EveryTable.dropColumn found holds (fun _ _ _ kept => kept)
      (fun _ _ notNull => Table.NotNull.dropColumn notNull index)) same

end Belay.Sqlite.Model
