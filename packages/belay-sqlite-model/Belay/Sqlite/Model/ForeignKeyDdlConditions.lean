import Belay.Sqlite.Model.ForeignKeyAddColumn
import Belay.Sqlite.Model.ForeignKeyAddColumnValid
import Belay.Sqlite.Model.ForeignKeyCreate
import Belay.Sqlite.Model.ForeignKeyDropCatalog

set_option doc.verso true

/-! Conditions on the schema statements for the run contracts of the foreign-key atoms. Each
condition is a fact about a catalog, or about a database and the rules of the statement. It never
states the atoms of the database after the statement. The selected mapping
({lit}`Catalog.foreignKeyMapping`) of a catalog reads the parent link of the catalog for each
declaration, so a fact about the parent links of two catalogs is a fact about the mappings. -/

namespace Belay.Sqlite.Model

/-- For every catalog and object: every declaration of every table of the catalog selects the same
parent link in the catalog with the object appended. The statement CREATE appends the object. An
index or a table can change the selected parent of an old declaration; a trigger cannot. -/
def Catalog.CreateKeepsSelection (catalog : Catalog) (object : CatalogObject) : Prop :=
  ∀ position shape, catalog.tableAt position = some shape → ∀ key ∈ shape.allForeignKeys,
    (catalog ++ [object]).parentLink key = catalog.parentLink key

/-- For every catalog and object: if the object is a table, every declaration of the table has
a located parent in the catalog with the object appended. Another object requires nothing. A
forward reference to a table that does not exist yet does not meet it. -/
def Catalog.CreateLocatesNewKeys (catalog : Catalog) (object : CatalogObject) : Prop :=
  ∀ shape, object.entry = .table shape → ∀ key ∈ shape.allForeignKeys,
    ((catalog ++ [object]).parentLink key).isLocated = true

/-- For every catalog and positions to drop: every declaration of every kept table selects, after
the drop, the parent link that it selected before, moved to the kept positions. A removed index
that supported a parent key, or a removed parent, does not meet it. -/
def Catalog.DropKeepsSelection (catalog : Catalog) (positions : List Nat) : Prop :=
  ∀ child shape, catalog.tableAt child = some shape → !positions.contains child →
    ∀ key ∈ shape.allForeignKeys,
      (catalog.drop positions).parentLink key = (catalog.parentLink key).transport (keptBelow positions)

/-- For every catalog and positions to drop: every located parent of every declaration of every kept
table is kept. -/
def Catalog.DropKeepsParents (catalog : Catalog) (positions : List Nat) : Prop :=
  ∀ child shape, catalog.tableAt child = some shape → !positions.contains child →
    ∀ key ∈ shape.allForeignKeys, ∀ parent comparison,
      catalog.parentLink key = .located parent comparison → !positions.contains parent

/-- For every catalog, target and column: every declaration of every table of the catalog selects
the same parent link in the catalog with the column added to the target. -/
def Catalog.AddColumnKeepsSelection (catalog : Catalog) (target : Nat) (column : CatalogColumn) : Prop :=
  ∀ position shape, catalog.tableAt position = some shape → ∀ key ∈ shape.allForeignKeys,
    (catalog.addColumn target column).parentLink key = catalog.parentLink key

/-- For every catalog, target and column: every declaration of the column has a located parent in
the catalog with the column added. A column without {lit}`REFERENCES` meets it. -/
def Catalog.AddColumnLocatesNewKeys (catalog : Catalog) (target : Nat) (column : CatalogColumn) : Prop :=
  ∀ key ∈ column.foreignKeys, ((catalog.addColumn target column).parentLink key).isLocated = true

/-- The conditions for the row atom, under the selected mapping, through ADD COLUMN of a column
to a target, where the flag tells that the statement refuses a populated table:
* the rows of the target are wide ({name}`Database.RowsWideAt`);
* the declarations of the target name only its columns ({name}`Database.DeclarationsBelowAt`);
* the target selects its parents below its width ({name}`Database.SelectionBelowAt`);
* for each added cell ({name}`AddedCell`) of a statement that does not refuse a populated table,
  each declaration of the column is satisfied by each old row with the cell appended. A column
  without {lit}`REFERENCES`, an empty table and a NULL cell meet the last item. -/
structure Database.AddColumnRowsCondition (database : Database) (target : Nat) (column : CatalogColumn)
    (refuses : Bool) : Prop where
  /-- Each row of the target has one cell for each column. -/
  wide : database.RowsWideAt target
  /-- Each declaration of the target names only columns of the target. -/
  declared : database.DeclarationsBelowAt target
  /-- The target selects its parents below its width. -/
  below : database.SelectionBelowAt target
  /-- Each declaration of the column is satisfied by each old row with the added cell appended. -/
  newKeys : ∀ table value, database.table target = some table → AddedCell table column value →
    (refuses = true → table.rows = []) → ∀ key ∈ column.foreignKeys, ∀ row ∈ table.rows,
      ((database.catalog.addColumn target column).foreignKeyMapping.link target key).satisfied
        (database.addColumn target column value) (row.appendValues [Value.store column.affinity value]) = true

/-- The conditions for the row atom, under the selected mapping, through a DROP that deletes the
rows of the first table with the rules of the statement: after the implicit DELETE of the first table
the catalog removal meets {name}`Database.DropForeignKeyFrame` at every clock, and a first position
without a table meets it for the input. The frame accepts a kept child whose rows all have NULL,
which permits the removal of a referenced parent after the DELETE. -/
def Database.EnforcedDropFrames (database : Database) (rules : Resolved.WriteRules) (positions : List Nat) : Prop :=
  (∀ clock target table, positions.head? = some target → database.table target = some table → ∀ after,
    (rowsKeys rules clock target (.delete target (table.scanRows.map (·.rowid)) false true false)
      database true).effect = .ok after → after.DropForeignKeyFrame positions after.catalog.foreignKeyMapping
        (after.catalog.drop positions).foreignKeyMapping) ∧
  (positions.head?.bind database.table = none → database.DropForeignKeyFrame positions
    database.catalog.foreignKeyMapping (database.catalog.drop positions).foreignKeyMapping)

/-- For every database and mapping: if the parent schemas of the database are compatible with the
mapping, they are compatible with the mapping that the catalog selects. Proof sketch: compatibility
makes the mapping equal to the selected parent link, which the selected mapping also reads. -/
theorem Database.ParentSchemasCompatible.selected {database : Database} {mapping : ForeignKeyMapping}
    (holds : database.ParentSchemasCompatible mapping) :
    database.ParentSchemasCompatible database.catalog.foreignKeyMapping := by
  intro position table present key declared
  obtain ⟨located, same⟩ := holds position table present key declared
  refine ⟨?_, rfl⟩
  change (database.catalog.parentLink key).isLocated = true
  rw [← same]
  exact located

/-- For every database with compatible parent schemas under a supplied mapping, and every object:
the catalog keeps the selected parent of every old declaration when CREATE appends the object
({name}`Catalog.CreateKeepsSelection`). So a statement for both atoms needs no premise for the
selection of old declarations. Proof sketch: {name}`Database.ParentSchemasCompatible.selection_append`
for the table at each position. -/
theorem Database.ParentSchemasCompatible.createKeepsSelection {database : Database} {mapping : ForeignKeyMapping}
    (holds : database.ParentSchemasCompatible mapping) (object : CatalogObject) :
    database.catalog.CreateKeepsSelection object :=
  fun position shape found key declared =>
    holds.selection_append [object] position { shape, rows := database.rows.getD position [] }
      (by simp only [Database.table, found, Option.map_some]) key declared

/-- For every database, target, column and flag: if the database meets
{name}`Database.AddColumnRowsCondition`, the catalog keeps the selected parent of every old
declaration when ADD COLUMN adds the column ({name}`Catalog.AddColumnKeepsSelection`). Proof sketch:
{name}`Catalog.parentLink_addColumn` for the selection of the target. -/
theorem Database.AddColumnRowsCondition.keepsSelection {database : Database} {target : Nat} {column : CatalogColumn}
    {refuses : Bool} (condition : database.AddColumnRowsCondition target column refuses) :
    database.catalog.AddColumnKeepsSelection target column :=
  fun _ _ _ key _ => Catalog.parentLink_addColumn database.catalog target column key condition.below

end Belay.Sqlite.Model
