import Belay.Sqlite.Model.OutlineTableLaws

set_option doc.verso true

/-! The facts about the rows of a database that a rename keeps. A database with the catalog of a
rename and the rows of the database before it has the facts about the rows of every table that
the database had, when the two catalogs have one outline ({lit}`CatalogOutline`): the tables are
at the same positions, with the same rows and the same shapes after the names are taken out. -/

namespace Belay.Sqlite.Model

/-- For every table of the database and the same table of a database that has another catalog
with one outline: the tables have the same rows and one shape after
{lit}`CatalogTable.blankNames`. Proof sketch: {name}`Catalog.tableAt_of_outline` at the position,
and the rows are the rows of the position in both databases. -/
theorem Database.table_of_outline {database : Database} {renamed : Catalog}
    (same : renamed.outline = database.catalog.outline) {position : Nat} {second : Table}
    (found : ({ database with catalog := renamed } : Database).table position = some second) :
    ∃ first, database.table position = some first ∧ second.rows = first.rows ∧
      first.shape.blankNames = second.shape.blankNames := by
  have shapes := Catalog.tableAt_of_outline same position
  unfold Database.table at found ⊢
  cases renamedShape : renamed.tableAt position with
  | none => simp [renamedShape] at found
  | some shape =>
    simp only [renamedShape, Option.map_some, Option.some.injEq] at found
    subst found
    cases oldShape : database.catalog.tableAt position with
    | none => simp [renamedShape, oldShape] at shapes
    | some oldTable =>
      simp only [renamedShape, oldShape, Option.map_some, Option.some.injEq] at shapes
      exact ⟨_, rfl, rfl, shapes.symm⟩

/-- For every fact about one table that holds again for a table with the same rows and one shape
after {lit}`CatalogTable.blankNames`, every database that has it in every table, and every catalog
with the outline of its catalog: the database with that catalog has it in every table. Proof
sketch: a table of the new database comes from a table of the old one
({name}`Database.table_of_outline`). -/
theorem Database.EveryTable.of_outline {fact : Nat → Table → Prop}
    (kept : ∀ position first second, second.rows = first.rows →
      first.shape.blankNames = second.shape.blankNames → fact position first → fact position second)
    {database : Database} (every : database.EveryTable fact) {renamed : Catalog}
    (same : renamed.outline = database.catalog.outline) :
    ({ database with catalog := renamed } : Database).EveryTable fact := by
  intro position second found
  obtain ⟨first, present, rows, shapes⟩ := Database.table_of_outline same found
  exact kept position first second rows shapes (every position first present)

/-- For every shaped database and every catalog with the outline of its catalog: the database with
that catalog is shaped ({name}`Database.RowsShaped`). Proof sketch: the catalog has the same
length, and a position without a table in the new catalog is one in the old catalog
({name}`Catalog.tableAt_of_outline`). -/
theorem Database.RowsShaped.of_outline {database : Database} (shaped : database.RowsShaped) {renamed : Catalog}
    (same : renamed.outline = database.catalog.outline) :
    ({ database with catalog := renamed } : Database).RowsShaped := by
  refine ⟨shaped.1.trans (Catalog.length_of_outline same).symm, fun position none => ?_⟩
  have shapes := Catalog.tableAt_of_outline same position
  rw [none] at shapes
  cases old : database.catalog.tableAt position with
  | none => exact shaped.2 position old
  | some table => simp [old] at shapes

/-- For every tables with the same rows and one shape after {lit}`CatalogTable.blankNames`: if the
first has {name}`Table.RowsWide`, the second has it. Proof sketch: the numbers of columns are equal
({name}`CatalogTable.columns_length_of_blankNames`). -/
theorem Table.RowsWide.of_blankNames {first second : Table} (rows : second.rows = first.rows)
    (same : first.shape.blankNames = second.shape.blankNames) (holds : first.RowsWide) : second.RowsWide := by
  intro row member
  rw [rows] at member
  exact (holds row member).trans (CatalogTable.columns_length_of_blankNames same)

/-- For every tables with the same rows and one shape after {lit}`CatalogTable.blankNames`: if the
first has {name}`Table.RowsStored`, the second has it. Proof sketch: a column of the second table
at a position is the blanked form of a column of the first, with the same affinity. -/
theorem Table.RowsStored.of_blankNames {first second : Table} (rows : second.rows = first.rows)
    (same : first.shape.blankNames = second.shape.blankNames) (holds : first.RowsStored) : second.RowsStored := by
  intro row member position column value found cell
  rw [rows] at member
  obtain ⟨other, foundFirst, blanked⟩ := CatalogTable.column_of_blankNames same.symm found
  have affinity : column.affinity = other.affinity := by
    have strict := congrArg CatalogColumn.strictType blanked
    have declared := congrArg CatalogColumn.declaredType blanked
    simp only [CatalogColumn.blankNames] at strict declared
    simp [CatalogColumn.affinity, strict, declared]
  rw [affinity]
  exact holds row member position other value foundFirst cell

/-- For every tables with the same rows and one shape after {lit}`CatalogTable.blankNames`: if the
first has {name}`Table.RowsAliased`, the second has it. Proof sketch: the rowid alias is not
blanked ({name}`CatalogTable.rowidAlias_of_blankNames`). -/
theorem Table.RowsAliased.of_blankNames {first second : Table} (rows : second.rows = first.rows)
    (same : first.shape.blankNames = second.shape.blankNames) (holds : first.RowsAliased) : second.RowsAliased := by
  intro row member
  rw [rows] at member
  rw [← CatalogTable.rowidAlias_of_blankNames same]
  exact holds row member

/-- For every database with {name}`Database.RowidsDistinct` and every catalog with the outline of its
catalog: the database with that catalog has it. Proof sketch: the rows are the same
({name}`Database.EveryTable.of_outline`). -/
theorem Database.RowidsDistinct.of_outline {database : Database} (holds : database.RowidsDistinct) {renamed : Catalog}
    (same : renamed.outline = database.catalog.outline) :
    ({ database with catalog := renamed } : Database).RowidsDistinct :=
  Database.EveryTable.of_outline (fun _ _ _ rows _ distinct => by simpa [Table.RowidsDistinct, rows] using distinct)
    holds same

/-- For every database with {name}`Database.RowidsInRange` and every catalog with the outline of its
catalog: the database with that catalog has it. Proof sketch: the rows are the same
({name}`Database.EveryTable.of_outline`). -/
theorem Database.RowidsInRange.of_outline {database : Database} (holds : database.RowidsInRange) {renamed : Catalog}
    (same : renamed.outline = database.catalog.outline) :
    ({ database with catalog := renamed } : Database).RowidsInRange :=
  Database.EveryTable.of_outline (fun _ _ _ rows _ inRange => by simpa [Table.RowidsInRange, rows] using inRange)
    holds same

/-- For every database with {name}`Database.RowsWide` and every catalog with the outline of its
catalog: the database with that catalog has it ({name}`Table.RowsWide.of_blankNames`). -/
theorem Database.RowsWide.of_outline {database : Database} (holds : database.RowsWide) {renamed : Catalog}
    (same : renamed.outline = database.catalog.outline) :
    ({ database with catalog := renamed } : Database).RowsWide :=
  Database.EveryTable.of_outline (fun _ _ _ rows shapes wide => Table.RowsWide.of_blankNames rows shapes wide) holds same

/-- For every database with {name}`Database.RowsStored` and every catalog with the outline of its
catalog: the database with that catalog has it ({name}`Table.RowsStored.of_blankNames`). -/
theorem Database.RowsStored.of_outline {database : Database} (holds : database.RowsStored) {renamed : Catalog}
    (same : renamed.outline = database.catalog.outline) :
    ({ database with catalog := renamed } : Database).RowsStored :=
  Database.EveryTable.of_outline (fun _ _ _ rows shapes stored => Table.RowsStored.of_blankNames rows shapes stored) holds same

/-- For every database with {name}`Database.RowsAliased` and every catalog with the outline of its
catalog: the database with that catalog has it ({name}`Table.RowsAliased.of_blankNames`). -/
theorem Database.RowsAliased.of_outline {database : Database} (holds : database.RowsAliased) {renamed : Catalog}
    (same : renamed.outline = database.catalog.outline) :
    ({ database with catalog := renamed } : Database).RowsAliased :=
  Database.EveryTable.of_outline (fun _ _ _ rows shapes aliased => Table.RowsAliased.of_blankNames rows shapes aliased) holds same

end Belay.Sqlite.Model
