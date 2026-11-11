import Belay.Sqlite.Model.Schema.Writes.ForeignKeyAssignmentCoverage

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every wide aliased row and literal cells covered by a changed list that omits
the alias, the action keeps its rowid if the alias column is not generated. Proof sketch:
rewrite to assignment, preserve the alias cell, and then preserve the rowid. -/
theorem setCells_rowid_of_unmoved (shape : CatalogTable) (cells : List (Nat × Value)) (old : Row)
    (wide : old.values.length = shape.columns.length) (changed : List Nat)
    (covered : ∀ pair ∈ cells, pair.1 ∈ changed)
    (aliased : old.Aliased shape.rowidAlias)
    (plain : ∀ position, shape.rowidAlias = some position →
      ∀ column, shape.columns[position]? = some column → column.generated = none)
    (unmoved : shape.rowidAlias.any changed.contains = false) :
    (setCells shape cells old).rowid = old.rowid := by
  rw [setCells_eq_assignFrom]
  apply LiteralData.movedRowid_rowid_of_aliased (new := LiteralData.assignFrom (.plain 0)
    shape.columns (cells.map fun (position, value) => (position, Resolved.Expr.literal value)) [] old) aliased rfl
  intro position alias
  apply LiteralData.assignFrom_coverage _ _ _ _ _ wide changed ?_ position (plain position alias) ?_
  · intro pair member
    obtain ⟨source, inside, same⟩ := List.mem_map.mp member
    subst pair
    exact covered source inside
  · left
    simpa [alias] using unmoved

end Belay.Sqlite.Model
