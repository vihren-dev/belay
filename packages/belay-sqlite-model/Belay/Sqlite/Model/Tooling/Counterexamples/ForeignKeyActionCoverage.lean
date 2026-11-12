import Belay.Sqlite.Model.Schema.Writes.ForeignKeyAssignmentCoverage

set_option doc.verso true

/-! Mapped foreign-key actions use exactly their reported assigned targets. -/

namespace Belay.Sqlite.Model

/-- A successful optional value map retains the original list of target positions. -/
private theorem mapM_pairs (source : List Nat) (get : Nat → Option Value)
    {cells : List (Nat × Value)} (found : source.mapM (fun position => (get position).map (position, ·)) = some cells) :
    cells.map Prod.fst = source := by
  induction source generalizing cells with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at found
    subst cells
    rfl
  | cons head tail ih =>
    simp only [List.mapM_cons, bind, Option.bind] at found
    cases valueAt : get head with
    | none => simp [valueAt] at found
    | some value =>
      cases tailAt : tail.mapM (fun position => (get position).map (position, ·)) with
      | none => simp [valueAt, tailAt] at found
      | some rest =>
        simp only [valueAt, tailAt, Option.map_some, pure, Option.some.injEq] at found
        subst cells
        simp only [List.map_cons, ih tailAt]

/-- For every successful CASCADE, SET NULL or SET DEFAULT cell list, its targets equal
the selected child projection in order, including repeated columns. NO ACTION and RESTRICT
are outside this law. Proof sketch: the three constructors map that projection directly. -/
theorem actionCells_positions {child parent : CatalogTable} {link : ForeignKeyLink} {key : ParentKey}
    {new : Row} {action : Syntax.ForeignKeyAction} {cells : List (Nat × Value)}
    (active : action = .cascade ∨ action = .setNull ∨ action = .setDefault)
    (found : actionCells child parent link key new action = some cells) :
    cells.map Prod.fst = childPositions link key := by
  rcases active with same | same | same <;> subst action
  · simp only [actionCells, Option.some.injEq] at found
    subst cells
    simp only [List.map_map, Function.comp_def, List.zipIdx_map_fst]
  · simp only [actionCells, Option.some.injEq] at found
    subst cells
    simp only [List.map_map, Function.comp_def, List.map_id']
  · exact mapM_pairs _ _ found

/-- For every successful writing action and wide child row, an unmarked or absent cell
keeps its value if its column is not generated. The changed list is the closure of the
selected child projection. Proof sketch: {name}`actionCells_positions` supplies assignment
coverage to {name}`setCells_coverage`. -/
theorem actionCells_coverage {child parent : CatalogTable} {link : ForeignKeyLink} {key : ParentKey}
    {new old : Row} {action : Syntax.ForeignKeyAction} {cells : List (Nat × Value)}
    (active : action = .cascade ∨ action = .setNull ∨ action = .setDefault)
    (found : actionCells child parent link key new action = some cells)
    (wide : old.values.length = child.columns.length)
    (position : Nat) (plain : ∀ column, child.columns[position]? = some column → column.generated = none)
    (outside : position ∉ child.changedColumns (childPositions link key) ∨ child.columns[position]? = none) :
    old.values.getD position .null = (setCells child cells old).values.getD position .null := by
  apply setCells_coverage child cells old wide _ ?_ position plain outside
  intro pair member
  apply child.assigned_mem_changedColumns
  rw [← actionCells_positions active found]
  exact List.mem_map.mpr ⟨pair, member, rfl⟩

end Belay.Sqlite.Model
