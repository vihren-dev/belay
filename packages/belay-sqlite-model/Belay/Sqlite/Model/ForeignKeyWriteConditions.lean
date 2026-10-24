import Belay.Sqlite.Model.ForeignKeyCounterWrites

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Conditions on row-engine rules for selected row-reference preservation: enforcement
is on, schema comparisons hold for future stored values, generated programs and actions
satisfy their effect conditions, and every credited fuel level has the BEFORE target frame.
These conditions describe inputs and intermediate effects, not the final row atom. -/
structure Resolved.WriteRules.ForeignKeyConditions (profile : Profile) (catalog : Catalog)
    (rules : Resolved.WriteRules) : Prop where
  /-- The actual row engine checks catalog-selected foreign keys. -/
  enforced : rules.keys = true
  /-- Every selected comparison is consistent for future stored rows and checked parent keys. -/
  comparisons : catalog.ForeignKeyComparisons
  /-- Every generated trigger step satisfies its explicit UPDATE effect conditions. -/
  programs : ProgramsForeignKeySafe catalog rules.programs
  /-- Every generated writing FK action satisfies its explicit UPDATE effect conditions. -/
  actions : ActionsForeignKeySafe catalog
  /-- At every fuel, a continuing BEFORE UPDATE sequence retains the target rows. -/
  before : ∀ fuel, (NestedRun.credited (runRows catalog catalog.foreignKeyLinks fuel)).BeforeUpdateFrame profile catalog rules.programs

/-- Structural conditions for ordinary resolved UPDATE assignments: unmarked columns
are nongenerated, and any processed low-level stale parent scan has another child table.
The raw row-change contract remains available for changes with other proved coverage facts.
These conditions quantify catalog definitions rather than input or final row validity. -/
structure ForeignKeyAssignmentConditions (catalog : Catalog) (position : Nat)
    (assignments : List (Nat × Resolved.Expr)) : Prop where
  /-- Every unmarked column of every actual target shape is nongenerated. -/
  plain : ∀ shape, catalog.tableAt position = some shape → ∀ cell ∉ shape.changedColumns (assignments.map Prod.fst),
    ∀ column, shape.columns[cell]? = some column → column.generated = none
  /-- Every processed parent link has a different child when the update retains a stale row. -/
  scans : ∀ name shape, catalog[position]? = some {name, entry := .table shape} →
    (updateLevel catalog.foreignKeyLinks position name shape (shape.changedColumns (assignments.map Prod.fst)) ≤ 1 ∧
      (shape.rowidAlias.any (shape.changedColumns (assignments.map Prod.fst)).contains ||
        (shape.withoutRowid && shape.primaryKey.any (shape.changedColumns (assignments.map Prod.fst)).contains)) = false) →
    ∀ link ∈ (parentLinks catalog.foreignKeyLinks position).filter
      (·.key.parentChanged shape (shape.changedColumns (assignments.map Prod.fst))), link.child ≠ position

/-- For any structural assignment conditions and actual target shape, every evaluation
context and source-cell function generates raw UPDATE work with complete effects and safe
stale scans. Proof sketch: assignment targets remain in the changed closure; assignment
coverage preserves every other cell and unmarked rowid alias, while the scan condition is
read from the same target definition. -/
theorem ForeignKeyAssignmentConditions.work {catalog : Catalog} {position : Nat}
    {assignments : List (Nat × Resolved.Expr)} (conditions : ForeignKeyAssignmentConditions catalog position assignments)
    (shape : CatalogTable) (found : catalog.tableAt position = some shape)
    (context : Resolved.EvalContext) (cells : Row → List Value) :
    ForeignKeyUpdateConditions catalog position
      (fun row => LiteralData.movedRowid shape.rowidAlias
        (LiteralData.assignFrom context shape.columns assignments (cells row) row))
      (shape.changedColumns (assignments.map Prod.fst)) where
  cells other atOther := by
    have same : other = shape := Option.some.inj (atOther.symm.trans found)
    subst other
    exact RowChange.Covers.assignFrom context shape assignments cells _
      (fun pair member => shape.assigned_mem_changedColumns _ _ (List.mem_map.mpr ⟨pair, member, rfl⟩))
      (conditions.plain shape found)
  scans name other atOther := by
    have selected : catalog.tableAt position = some other := by simp only [Catalog.tableAt, atOther]
    have same : other = shape := Option.some.inj (selected.symm.trans found)
    subst other
    exact conditions.scans name shape atOther

end Belay.Sqlite.Model
