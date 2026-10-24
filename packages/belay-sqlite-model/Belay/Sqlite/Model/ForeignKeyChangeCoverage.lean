import Belay.Sqlite.Model.ForeignKeyActionCoverage
set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every wide, correctly aliased old row, a change keeps each unmarked or absent
column and keeps the rowid when its alias is unmarked. The changed list can overapproximate
effects. Use this primitive for custom changes; assignment helpers discharge it structurally. -/
structure RowChange.Covers (shape : CatalogTable) (changed : List Nat) (change : Row → Row) : Prop where
  /-- Every wide, aliased old row keeps cells outside the changed list or table columns. -/
  cells : ∀ old, old.values.length = shape.columns.length → old.Aliased shape.rowidAlias →
    ∀ position, position ∉ changed ∨ shape.columns[position]? = none →
      old.values.getD position .null = (change old).values.getD position .null
  /-- Every wide, aliased old row keeps its rowid when the alias is outside the changed list. -/
  rowid : ∀ old, old.values.length = shape.columns.length → old.Aliased shape.rowidAlias →
    shape.rowidAlias.any changed.contains = false → (change old).rowid = old.rowid

/-- For any assignments covered by the changed list, if each unmarked column is
nongenerated, the actual assignment and alias update cover all effects on every wide,
aliased input row. Marked generated columns need no such restriction.
Proof sketch: apply assignment coverage to each untouched cell and the unmoved alias. -/
theorem RowChange.Covers.assignFrom (context : Resolved.EvalContext) (shape : CatalogTable)
    (assignments : List (Nat × Resolved.Expr)) (cells : Row → List Value) (changed : List Nat)
    (covered : ∀ pair ∈ assignments, pair.1 ∈ changed)
    (plain : ∀ position ∉ changed, ∀ column, shape.columns[position]? = some column → column.generated = none) :
    Covers shape changed (fun old => LiteralData.movedRowid shape.rowidAlias
      (LiteralData.assignFrom context shape.columns assignments (cells old) old)) where
  cells old wide _ position outside := by
    rw [LiteralData.movedRowid_values]
    apply LiteralData.assignFrom_coverage context shape assignments (cells old) old wide changed covered position ?_ outside
    intro column atColumn
    rcases outside with untouched | absent
    · exact plain position untouched column atColumn
    · rw [atColumn] at absent; cases absent
  rowid old wide aliased unmoved := by
    apply LiteralData.movedRowid_rowid_of_aliased
      (new := LiteralData.assignFrom context shape.columns assignments (cells old) old) aliased rfl
    intro position alias
    have outside : position ∉ changed := by simpa [alias] using unmoved
    exact LiteralData.assignFrom_coverage context shape assignments (cells old) old wide changed covered
      position (plain position outside) (.inl outside)

/-- For literal assignments covered by the changed list and nongenerated unmarked
columns, the actual action change covers all effects on wide, aliased inputs.
Proof sketch: rewrite literal cell updates as assignments and use their coverage theorem. -/
theorem RowChange.Covers.of_setCells (shape : CatalogTable) (cells : List (Nat × Value)) (changed : List Nat)
    (covered : ∀ pair ∈ cells, pair.1 ∈ changed)
    (plain : ∀ position ∉ changed, ∀ column, shape.columns[position]? = some column → column.generated = none) :
    Covers shape changed (setCells shape cells) := by
  have same : setCells shape cells = fun old => LiteralData.movedRowid shape.rowidAlias
      (LiteralData.assignFrom (.plain 0) shape.columns
        (cells.map fun (position, value) => (position, Resolved.Expr.literal value)) [] old) := by
    funext old
    exact setCells_eq_assignFrom shape cells old
  rw [same]
  apply Covers.assignFrom _ _ _ (fun _ => []) _ ?_ plain
  intro pair member
  obtain ⟨source, inside, equal⟩ := List.mem_map.mp member
  subst pair
  exact covered source inside

end Belay.Sqlite.Model
