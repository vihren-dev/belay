import Belay.Sqlite.Model.ForeignKeyAddColumnReads

set_option doc.verso true

/-! Foreign-key atoms through ADD COLUMN on a database, with separate row-mapping and
parent-selection premises. The new column adds declarations to its table and one cell to each
row of it. -/

namespace Belay.Sqlite.Model

/-- For every shape, column and key: the key is a declaration of the shape with the column appended
exactly when it is a declaration of the shape or of the column. Proof sketch: the declarations are
those of the columns, then those of the table constraints. -/
theorem CatalogTable.mem_allForeignKeys_appendColumn (shape : CatalogTable) (column : CatalogColumn)
    (key : ForeignKey) :
    key ∈ ({shape with columns := shape.columns ++ [column]} : CatalogTable).allForeignKeys ↔
      key ∈ shape.allForeignKeys ∨ key ∈ column.foreignKeys := by
  simp only [CatalogTable.allForeignKeys, List.flatMap_append, List.flatMap_singleton, List.mem_append]
  constructor
  · rintro ((inColumns | inNew) | inTable)
    · exact .inl (.inl inColumns)
    · exact .inr inNew
    · exact .inl (.inr inTable)
  · rintro ((inColumns | inTable) | inNew)
    · exact .inl (.inl inColumns)
    · exact .inr inTable
    · exact .inl (.inr inNew)

/-- For every database, supplied mappings and an ADD COLUMN at a target that holds a table: if the
database has row references under the first mapping, the table meets {name}`Database.AddColumnReads`,
the second mapping agrees with the first on every old declaration, and each new declaration of
the column is satisfied by each old row with the new cell appended, the database after
{name}`Database.addColumn` has row references under the second mapping. Rows of other tables are
unchanged and the parent selection may change. Proof sketch: an old declaration keeps its
comparison for the old row ({name}`ForeignKeyLink.satisfied_addColumn`) and for the row with the cell
appended ({name}`ForeignKeyLink.satisfied_append`); the new declarations are the last premise. -/
theorem Database.RowReferencesHold.addColumn {database : Database} {mapping nextMapping : ForeignKeyMapping}
    (holds : database.RowReferencesHold mapping) {target : Nat} {table : Table}
    (found : database.table target = some table) (reads : database.AddColumnReads mapping target table)
    (column : CatalogColumn) (value : Value)
    (same : ∀ position oldTable, database.table position = some oldTable →
      ∀ key ∈ oldTable.shape.allForeignKeys, nextMapping.parent position key = mapping.parent position key)
    (newKeys : ∀ key ∈ column.foreignKeys, ∀ row ∈ table.rows,
      (nextMapping.link target key).satisfied (database.addColumn target column value)
        (row.appendValues [Value.store column.affinity value]) = true) :
    (database.addColumn target column value).RowReferencesHold nextMapping := by
  intro position grown present key declared row member
  have unchanged : ∀ oldTable, database.table position = some oldTable → key ∈ oldTable.shape.allForeignKeys →
      ∀ old ∈ oldTable.rows, (nextMapping.link position key).satisfied (database.addColumn target column value) old =
        true := by
    intro oldTable oldFound oldDeclared old oldMember
    have link : nextMapping.link position key = mapping.link position key := by
      simp only [ForeignKeyMapping.link, same position oldTable oldFound key oldDeclared]
    rw [link, ForeignKeyLink.satisfied_addColumn database target column value found reads.wide _ old
      fun comparison selected => reads.parents position oldTable oldFound key oldDeclared comparison selected]
    exact holds position oldTable oldFound key oldDeclared old oldMember
  by_cases here : position = target
  · subst here
    rw [Database.table_addColumn column value found, Option.some.injEq] at present
    subst present
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    rcases (CatalogTable.mem_allForeignKeys_appendColumn table.shape column key).mp declared with oldDeclared | fresh
    · have link : nextMapping.link position key = mapping.link position key := by
        simp only [ForeignKeyMapping.link, same position table found key oldDeclared]
      rw [ForeignKeyLink.satisfied_append _ _ _ _ (by
        rw [link]
        have width := reads.wide old oldMember
        intro place inside
        exact width ▸ reads.children key oldDeclared place inside)]
      exact unchanged table found oldDeclared old oldMember
    · exact newKeys key fresh old oldMember
  · rw [Database.table_addColumn_other database column value here] at present
    exact unchanged grown present declared row member

/-- For every database, supplied mappings and an ADD COLUMN at a target that holds a table: if the
database has compatible parent schemas under the first mapping, the second mapping agrees with it
on every old declaration, the catalog with the column selects the same parent link for every old
declaration, and every declaration of the column has a located parent in the second mapping equal to
the selection of the catalog with the column, the database after {name}`Database.addColumn` has
compatible parent schemas under the second mapping. Stored rows are not read. The last premise
is empty for a column without {lit}`REFERENCES`. Proof sketch: an old declaration keeps its
located mapping and its selection; a new declaration is the last premise. -/
theorem Database.ParentSchemasCompatible.addColumn {database : Database} {mapping nextMapping : ForeignKeyMapping}
    (holds : database.ParentSchemasCompatible mapping) {target : Nat} {table : Table}
    (found : database.table target = some table) (column : CatalogColumn) (value : Value)
    (same : ∀ position oldTable, database.table position = some oldTable →
      ∀ key ∈ oldTable.shape.allForeignKeys, nextMapping.parent position key = mapping.parent position key)
    (selection : ∀ position oldTable, database.table position = some oldTable →
      ∀ key ∈ oldTable.shape.allForeignKeys,
        (database.catalog.addColumn target column).parentLink key = database.catalog.parentLink key)
    (newKeys : ∀ key ∈ column.foreignKeys,
      (nextMapping.parent target key).isLocated = true ∧
        nextMapping.parent target key = (database.catalog.addColumn target column).parentLink key) :
    (database.addColumn target column value).ParentSchemasCompatible nextMapping := by
  intro position grown present key declared
  have unchanged : ∀ oldTable, database.table position = some oldTable → key ∈ oldTable.shape.allForeignKeys →
      (nextMapping.parent position key).isLocated = true ∧
        nextMapping.parent position key = (database.catalog.addColumn target column).parentLink key := by
    intro oldTable oldFound oldDeclared
    rw [same position oldTable oldFound key oldDeclared, selection position oldTable oldFound key oldDeclared]
    exact holds position oldTable oldFound key oldDeclared
  by_cases here : position = target
  · subst here
    rw [Database.table_addColumn column value found, Option.some.injEq] at present
    subst present
    rcases (CatalogTable.mem_allForeignKeys_appendColumn table.shape column key).mp declared with oldDeclared | fresh
    · exact unchanged table found oldDeclared
    · exact newKeys key fresh
  · rw [Database.table_addColumn_other database column value here] at present
    exact unchanged grown present declared

end Belay.Sqlite.Model
