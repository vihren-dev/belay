import Belay.Sqlite.Model.ForeignKeyMapping
import Belay.Sqlite.Model.DatabaseFactChecks

set_option doc.verso true

/-! Independent foreign-key facts. Row truth uses an explicit parent mapping and does not
require a supporting index. Parent-schema compatibility checks the current catalog's selection
even when a child table is empty. Both facts are outside {lit}`Database.Valid`. -/

namespace Belay.Sqlite.Model

/-- For every declared foreign key and stored child row, the supplied mapping finds a parent
row or a selected child key cell is NULL. Located comparisons select the NULL-test columns;
missing or mismatched targets use declaration columns and reject non-NULL keys. No keys or
no rows makes this true. Parent rows and column definitions come from the database; indexes
do not. Use {name}`Catalog.foreignKeyMapping` for current parent choices. -/
def Table.RowReferencesHold (mapping : ForeignKeyMapping) (database : Database) (position : Nat)
    (table : Table) : Prop :=
  ∀ key ∈ table.shape.allForeignKeys, ∀ row ∈ table.rows,
    (mapping.link position key).satisfied database row = true

/-- Every table and each of its declared foreign keys satisfies {name}`Table.RowReferencesHold`
under the supplied mapping. A database without foreign keys satisfies this fact. The mapping
cannot remove a declaration from this quantification. -/
def Database.RowReferencesHold (mapping : ForeignKeyMapping) (database : Database) : Prop :=
  database.EveryTable fun position table => table.RowReferencesHold mapping database position

/-- For every foreign key declared by the table, the supplied parent is located and equals
the catalog's selection. Empty tables still require compatible parent schemas. A table without
foreign keys requires nothing. -/
def Table.ParentSchemasCompatible (mapping : ForeignKeyMapping) (catalog : Catalog) (position : Nat)
    (table : Table) : Prop :=
  ∀ key ∈ table.shape.allForeignKeys,
    (mapping.parent position key).isLocated = true ∧ mapping.parent position key = catalog.parentLink key

/-- Every declared foreign key in every table satisfies {name}`Table.ParentSchemasCompatible`.
This depends on declarations and selected parent keys, regardless of stored rows. A database
without foreign keys satisfies it. -/
def Database.ParentSchemasCompatible (mapping : ForeignKeyMapping) (database : Database) : Prop :=
  database.EveryTable fun position table => table.ParentSchemasCompatible mapping database.catalog position

/-- Execute {name}`Table.RowReferencesHold` by checking every declared key and stored row. -/
def Table.rowReferencesHold (mapping : ForeignKeyMapping) (database : Database) (position : Nat)
    (table : Table) : Bool :=
  table.shape.allForeignKeys.all fun key => table.rows.all ((mapping.link position key).satisfied database)

/-- Execute {name}`Table.ParentSchemasCompatible`, including declarations without child rows. -/
def Table.parentSchemasCompatible (mapping : ForeignKeyMapping) (catalog : Catalog) (position : Nat)
    (table : Table) : Bool :=
  table.shape.allForeignKeys.all fun key =>
    (mapping.parent position key).isLocated && mapping.parent position key == catalog.parentLink key

/-- For every mapping, database, position and table, the row check returns true exactly when
{name}`Table.RowReferencesHold` holds. Proof sketch: expand each finite universal check. -/
theorem Table.rowReferencesHold_iff (mapping : ForeignKeyMapping) (database : Database) (position : Nat)
    (table : Table) : table.rowReferencesHold mapping database position = true ↔
      table.RowReferencesHold mapping database position := by
  simp [Table.rowReferencesHold, Table.RowReferencesHold]

/-- For every mapping, catalog, position and table, the schema check returns true exactly when
{name}`Table.ParentSchemasCompatible` holds. Proof sketch: expand the finite check and equality. -/
theorem Table.parentSchemasCompatible_iff (mapping : ForeignKeyMapping) (catalog : Catalog) (position : Nat)
    (table : Table) : table.parentSchemasCompatible mapping catalog position = true ↔
      table.ParentSchemasCompatible mapping catalog position := by
  simp [Table.parentSchemasCompatible, Table.ParentSchemasCompatible]

/-- Decide a table's row-reference fact with its executable check. -/
instance Table.decidableRowReferencesHold (mapping : ForeignKeyMapping) (database : Database) (position : Nat)
    (table : Table) : Decidable (table.RowReferencesHold mapping database position) :=
  decidable_of_iff _ (table.rowReferencesHold_iff mapping database position)

/-- Decide a table's parent-schema fact with its executable check. -/
instance Table.decidableParentSchemasCompatible (mapping : ForeignKeyMapping) (catalog : Catalog) (position : Nat)
    (table : Table) : Decidable (table.ParentSchemasCompatible mapping catalog position) :=
  decidable_of_iff _ (table.parentSchemasCompatible_iff mapping catalog position)

/-- Check {name}`Database.RowReferencesHold` at every table position. -/
def Database.rowReferencesHold (mapping : ForeignKeyMapping) (database : Database) : Bool :=
  database.everyTable fun position table => table.rowReferencesHold mapping database position

/-- Check {name}`Database.ParentSchemasCompatible` at every table position. -/
def Database.parentSchemasCompatible (mapping : ForeignKeyMapping) (database : Database) : Bool :=
  database.everyTable fun position table => table.parentSchemasCompatible mapping database.catalog position

/-- For every mapping and database, the database row check returns true exactly when every
table satisfies the row atom. Proof sketch: apply the finite table traversal equivalence. -/
theorem Database.rowReferencesHold_iff (mapping : ForeignKeyMapping) (database : Database) :
    database.rowReferencesHold mapping = true ↔ database.RowReferencesHold mapping :=
  database.everyTable_iff fun position table => table.rowReferencesHold_iff mapping database position

/-- For every mapping and database, the database schema check returns true exactly when every
table satisfies the schema atom. Proof sketch: apply the finite table traversal equivalence. -/
theorem Database.parentSchemasCompatible_iff (mapping : ForeignKeyMapping) (database : Database) :
    database.parentSchemasCompatible mapping = true ↔ database.ParentSchemasCompatible mapping :=
  database.everyTable_iff fun position table => table.parentSchemasCompatible_iff mapping database.catalog position

/-- Decide the database row-reference fact with its executable check. -/
instance Database.decidableRowReferencesHold (mapping : ForeignKeyMapping) (database : Database) :
    Decidable (database.RowReferencesHold mapping) :=
  decidable_of_iff _ (database.rowReferencesHold_iff mapping)

/-- Decide the database parent-schema fact with its executable check. -/
instance Database.decidableParentSchemasCompatible (mapping : ForeignKeyMapping) (database : Database) :
    Decidable (database.ParentSchemasCompatible mapping) :=
  decidable_of_iff _ (database.parentSchemasCompatible_iff mapping)

end Belay.Sqlite.Model
