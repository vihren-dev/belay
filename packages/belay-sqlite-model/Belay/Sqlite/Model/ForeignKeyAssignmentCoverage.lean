import Belay.Sqlite.Model.ForeignKeyWrites
import Belay.Sqlite.Model.AdmittedUpdateRows
import Belay.Sqlite.Model.CatalogTableLaws

set_option doc.verso true

/-! Actual assignment constructors preserve unmarked cells and unmoved rowids. -/

namespace Belay.Sqlite.Model


/-- For every shape and assigned list, each assigned position remains in the generated
column dependency closure. Proof sketch: both folds only retain or append positions. -/
theorem CatalogTable.assigned_mem_changedColumns (shape : CatalogTable) (assigned : List Nat) :
    ∀ position ∈ assigned, position ∈ shape.changedColumns assigned := by
  unfold CatalogTable.changedColumns
  apply LiteralData.foldl_invariant (fun changed => ∀ position ∈ assigned, position ∈ changed)
  · intro position member
    exact member
  · intro changed _ _ before
    apply LiteralData.foldl_invariant (fun changed => ∀ position ∈ assigned, position ∈ changed) _ _ changed before
    intro reached item _ before
    repeat' (first | split | dsimp only)
    all_goals first
      | exact before
      | (intro position member; exact List.mem_append_left _ (before position member))

/-- For every wide row and assignments covered by the changed list, an unmarked or
absent cell keeps its value when its column is not generated. Generated columns elsewhere
are unrestricted. Proof sketch: an existing cell is unassigned; absent cells stay outside
the preserved width. The generated-cell counterexample explains the column premise. -/
theorem LiteralData.assignFrom_coverage (context : Resolved.EvalContext) (shape : CatalogTable)
    (assignments : List (Nat × Resolved.Expr)) (cells : List Value) (old : Row)
    (wide : old.values.length = shape.columns.length)
    (changed : List Nat) (covered : ∀ pair ∈ assignments, pair.1 ∈ changed)
    (position : Nat) (plain : ∀ column, shape.columns[position]? = some column → column.generated = none)
    (outside : position ∉ changed ∨ shape.columns[position]? = none) :
    old.values.getD position .null = (assignFrom context shape.columns assignments cells old).values.getD position .null := by
  cases columnAt : shape.columns[position]? with
  | none =>
    have beyond : shape.columns.length ≤ position := List.getElem?_eq_none_iff.mp columnAt
    have sameLength := assignFrom_length context shape.columns assignments cells old
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  | some column =>
    have notChanged : position ∉ changed := by
      rcases outside with untouched | absent
      · exact untouched
      · rw [columnAt] at absent; cases absent
    have notAssigned : ∀ pair ∈ assignments, pair.1 ≠ position := by
      intro pair member equal
      apply notChanged
      exact equal ▸ covered pair member
    have same := assignFrom_unassigned context shape.columns assignments cells old columnAt
      (plain column columnAt) notAssigned
    simp only [List.getD_eq_getElem?_getD, same]

/-- For every shape, literal assignments and row, the action update equals ordinary
literal assignment followed by alias movement. Proof sketch: both folds store the same
values and recompute generated cells, so actions can reuse the assignment laws. -/
theorem setCells_eq_assignFrom (shape : CatalogTable) (cells : List (Nat × Value)) (row : Row) :
    setCells shape cells row = LiteralData.movedRowid shape.rowidAlias
      (LiteralData.assignFrom (.plain 0) shape.columns (cells.map fun (position, value) => (position, Resolved.Expr.literal value))
        [] row) := by
  simp only [setCells, LiteralData.assignFrom, List.foldl_map, Resolved.Expr.eval, Resolved.Expr.evaluate]

/-- For every wide row and resolved assignments, an unmarked or absent cell keeps its
value after assignment and alias movement if that column is not generated. Proof sketch:
assigned positions remain in {name}`CatalogTable.changedColumns`, and alias movement
keeps values. This is the change function constructed by {name}`updateKeys`. -/
theorem LiteralData.assign_coverage (context : Resolved.EvalContext) (shape : CatalogTable)
    (assignments : List (Nat × Resolved.Expr)) (old : Row)
    (wide : old.values.length = shape.columns.length)
    (position : Nat) (plain : ∀ column, shape.columns[position]? = some column → column.generated = none)
    (outside : position ∉ shape.changedColumns (assignments.map Prod.fst) ∨ shape.columns[position]? = none) :
    old.values.getD position .null = (movedRowid shape.rowidAlias
      (assign context shape.columns assignments old)).values.getD position .null := by
  rw [movedRowid_values]
  exact assignFrom_coverage context shape assignments old.values old wide _
    (fun pair member => shape.assigned_mem_changedColumns _ _ (List.mem_map.mpr ⟨pair, member, rfl⟩))
    position plain outside

/-- For every wide row and literal action cells covered by the changed list, an unmarked
or absent cell keeps its value if that column is not generated. Proof sketch: rewrite
the action as literal assignment with {name}`setCells_eq_assignFrom`. -/
theorem setCells_coverage (shape : CatalogTable) (cells : List (Nat × Value)) (old : Row)
    (wide : old.values.length = shape.columns.length) (changed : List Nat)
    (covered : ∀ pair ∈ cells, pair.1 ∈ changed)
    (position : Nat) (plain : ∀ column, shape.columns[position]? = some column → column.generated = none)
    (outside : position ∉ changed ∨ shape.columns[position]? = none) :
    old.values.getD position .null = (setCells shape cells old).values.getD position .null := by
  rw [setCells_eq_assignFrom, LiteralData.movedRowid_values]
  apply LiteralData.assignFrom_coverage _ _ _ _ _ wide changed ?_ position plain outside
  intro pair member
  obtain ⟨source, inside, same⟩ := List.mem_map.mp member
  subst pair
  exact covered source inside

/-- For every supported table with a rowid alias, the alias belongs to its primary key.
Proof sketch: {name}`CatalogTable.supported_iff` gives that singleton primary key. -/
theorem CatalogTable.alias_primaryKey {shape : CatalogTable} {limits : Limits}
    (supported : shape.supported limits = true) {alias : Nat} (found : shape.rowidAlias = some alias) :
    alias ∈ shape.primaryKey := by
  have facts := (shape.supported_iff limits).mp supported
  have key := (facts.2.2.2.2.2.2.1 alias found).1
  simp [key]

/-- For every old aliased row and new row with the same rowid and alias-cell value,
alias movement preserves the old rowid. Without an alias only rowid equality is required.
Proof sketch: an alias cell is the old integer rowid; otherwise movement does nothing. -/
theorem LiteralData.movedRowid_rowid_of_aliased {alias : Option Nat} {old new : Row}
    (aliased : old.Aliased alias) (sameId : new.rowid = old.rowid)
    (sameCell : ∀ position, alias = some position →
      old.values.getD position .null = new.values.getD position .null) :
    (movedRowid alias new).rowid = old.rowid := by
  cases found : alias with
  | none => simpa [movedRowid, found] using sameId
  | some position =>
    have oldCell := aliased position found
    have same := sameCell position found
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, oldCell] at same
    cases newCell : new.values[position]? with
    | none => simp [newCell] at same
    | some value =>
      simp only [newCell, Option.getD_some] at same
      subst value
      simp [movedRowid, newCell]

/-- For every wide aliased row and resolved assignments, the changed list omitting the
alias preserves the rowid if its column is not generated. Proof sketch: assignment keeps
the alias cell, and {name}`LiteralData.movedRowid_rowid_of_aliased` keeps the rowid. -/
theorem LiteralData.assign_rowid_of_unmoved (context : Resolved.EvalContext) (shape : CatalogTable)
    (assignments : List (Nat × Resolved.Expr)) (old : Row)
    (wide : old.values.length = shape.columns.length)
    (aliased : old.Aliased shape.rowidAlias)
    (plain : ∀ position, shape.rowidAlias = some position →
      ∀ column, shape.columns[position]? = some column → column.generated = none)
    (unmoved : shape.rowidAlias.any (shape.changedColumns (assignments.map Prod.fst)).contains = false) :
    (movedRowid shape.rowidAlias (assign context shape.columns assignments old)).rowid = old.rowid := by
  apply movedRowid_rowid_of_aliased (new := assign context shape.columns assignments old) aliased rfl
  intro position alias
  apply assignFrom_coverage context shape assignments old.values old wide _
    (fun pair member => shape.assigned_mem_changedColumns _ _ (List.mem_map.mpr ⟨pair, member, rfl⟩))
    position (plain position alias)
  left
  simpa [alias] using unmoved

end Belay.Sqlite.Model
