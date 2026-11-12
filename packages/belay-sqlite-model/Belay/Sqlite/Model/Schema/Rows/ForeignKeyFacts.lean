import Belay.Sqlite.Model.Schema.ForeignKeys.ForeignKeyFacts

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Execute {name}`Table.RowReferencesHold` by checking every declared key and stored row. -/
def Table.rowReferencesHold (mapping : ForeignKeyMapping) (database : Database) (position : Nat)
    (table : Table) : Bool :=
  table.shape.allForeignKeys.all fun key => table.rows.all ((mapping.link position key).satisfied database)

/-- For every mapping, database, position and table, the row check returns true exactly when
{name}`Table.RowReferencesHold` holds. Proof sketch: expand each finite universal check. -/
theorem Table.rowReferencesHold_iff (mapping : ForeignKeyMapping) (database : Database) (position : Nat)
    (table : Table) : table.rowReferencesHold mapping database position = true ↔
      table.RowReferencesHold mapping database position := by
  simp [Table.rowReferencesHold, Table.RowReferencesHold]

/-- Decide a table's row-reference fact with its executable check. -/
instance Table.decidableRowReferencesHold (mapping : ForeignKeyMapping) (database : Database) (position : Nat)
    (table : Table) : Decidable (table.RowReferencesHold mapping database position) :=
  decidable_of_iff _ (table.rowReferencesHold_iff mapping database position)

/-- Check {name}`Database.RowReferencesHold` at every table position. -/
def Database.rowReferencesHold (mapping : ForeignKeyMapping) (database : Database) : Bool :=
  database.everyTable fun position table => table.rowReferencesHold mapping database position

/-- For every mapping and database, the database row check returns true exactly when every
table satisfies the row atom. Proof sketch: apply the finite table traversal equivalence. -/
theorem Database.rowReferencesHold_iff (mapping : ForeignKeyMapping) (database : Database) :
    database.rowReferencesHold mapping = true ↔ database.RowReferencesHold mapping :=
  database.everyTable_iff fun position table => table.rowReferencesHold_iff mapping database position

/-- Decide the database row-reference fact with its executable check. -/
instance Database.decidableRowReferencesHold (mapping : ForeignKeyMapping) (database : Database) :
    Decidable (database.RowReferencesHold mapping) :=
  decidable_of_iff _ (database.rowReferencesHold_iff mapping)

end Belay.Sqlite.Model
