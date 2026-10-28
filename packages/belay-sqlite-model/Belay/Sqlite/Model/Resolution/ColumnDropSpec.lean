import Belay.Sqlite.Model.Resolution.ColumnDropCatalog

set_option doc.verso true

/-! What a table that can lose a column tells ({lit}`CatalogTable.droppable`), as facts for proofs. The facts
say that no key, rowid alias, CHECK constraint, generated expression or foreign key of the columns that stay
names the column at the index, so every position that the table keeps has an image after the drop
({lit}`dropPosition`). -/

namespace Belay.Sqlite.Model

/-- The CHECK constraints of the table that stay when the column at the index is dropped: those of the
other columns in column order, then those of the table constraints. -/
def CatalogTable.checksAfterDrop (index : Nat) (table : CatalogTable) : List CheckConstraint :=
  (table.columns.eraseIdx index).flatMap (·.checks) ++ table.checks

/-- The facts that a table gives when the column at the index can leave it: the index is inside the
columns, and no key, rowid alias, CHECK constraint that stays, generated expression that stays or foreign key
that stays names the column. -/
structure CatalogTable.DropsCleanly (index : Nat) (table : CatalogTable) : Prop where
  /-- The index is the position of a column. -/
  inside : index < table.columns.length
  /-- The primary key does not name the column. -/
  primary : ∀ position ∈ table.primaryKey, position ≠ index
  /-- No UNIQUE key names the column. -/
  keys : ∀ key ∈ table.uniqueKeys, ∀ position ∈ key, position ≠ index
  /-- The column is not the rowid alias. -/
  alias : table.rowidAlias ≠ some index
  /-- No CHECK constraint that stays reads the column. -/
  checks : ∀ check ∈ table.checksAfterDrop index, check.condition.readsColumn index = false
  /-- No generated expression of another column reads the column. -/
  generated : ∀ column ∈ table.columns.eraseIdx index, ∀ how, column.generated = some how →
    how.expression.readsColumn index = false
  /-- No foreign key that stays names the column. -/
  foreign : ∀ column ∈ table.columns.eraseIdx index, ∀ key ∈ column.foreignKeys, index ∉ key.columns
  /-- No foreign key of the table constraints names the column. -/
  tableForeign : ∀ key ∈ table.foreignKeys, index ∉ key.columns

/-- For every table that passes {name}`CatalogTable.droppable`, the facts of
{name}`CatalogTable.DropsCleanly` hold. Proof sketch: unfold the Boolean tests into membership facts. -/
theorem CatalogTable.droppable_spec {index : Nat} {table : CatalogTable} (ok : table.droppable index = true) :
    table.DropsCleanly index := by
  simp [CatalogTable.droppable, CatalogTable.independentOf] at ok
  obtain ⟨⟨⟨⟨⟨inside, _⟩, primary⟩, alias⟩, keys⟩, ⟨⟨columns, ownChecks⟩, foreign⟩⟩ := ok
  refine ⟨inside, fun position member same => primary (same ▸ member),
    fun key member position inKey same => keys key member (same ▸ inKey), alias, ?_, ?_, ?_, foreign⟩
  · intro check member
    rcases List.mem_append.mp member with inColumns | inTable
    · obtain ⟨column, inColumn, inChecks⟩ := List.mem_flatMap.mp inColumns
      exact (columns column inColumn).1.1 check inChecks
    · exact ownChecks check inTable
  · intro column member how generated
    have := (columns column member).1.2
    simpa [generated] using this
  · intro column member key inKey
    exact (columns column member).2 key inKey

end Belay.Sqlite.Model
