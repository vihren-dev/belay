import Belay.Sqlite.Model.ForeignKeyUpdateChecks

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Input-independent conditions for an UPDATE change: all reported effects cover the
actual cells and rowid, and low-level stale parent scans cannot scan the target as a child.
These are effect/mapping facts, not assumptions about the final database's validity. -/
structure ForeignKeyUpdateConditions (catalog : Catalog) (position : Nat) (change : Row → Row) (changed : List Nat) : Prop where
  /-- Every actual target shape has complete cell and rowid coverage for this change. -/
  cells : ∀ shape, catalog.tableAt position = some shape → RowChange.Covers shape changed change
  /-- When a stale row can be scanned, no processed parent link has the updated table as its child. -/
  scans : ∀ name shape, catalog[position]? = some {name, entry := .table shape} →
    (updateLevel catalog.foreignKeyLinks position name shape changed ≤ 1 ∧
      (shape.rowidAlias.any changed.contains || (shape.withoutRowid && shape.primaryKey.any changed.contains)) = false) →
    ∀ link ∈ (parentLinks catalog.foreignKeyLinks position).filter (·.key.parentChanged shape changed), link.child ≠ position

/-- Raw UPDATE work has the explicit cell and stale-scan conditions; INSERT and DELETE
work require nothing here. This permits custom raw changes through a proved effect contract. -/
def RowWork.ForeignKeySafe (catalog : Catalog) : RowWork → Prop
  | .update position change _ changed _ _ => ForeignKeyUpdateConditions catalog position change changed
  | .insert .. | .delete .. => True

/-- Each trigger UPDATE's actual assignment constructor satisfies the UPDATE conditions
for every target shape, evaluation context and trigger-cell list. Other trigger steps
require nothing here. This covers generated work before any nested input is chosen. -/
def Resolved.Step.ForeignKeySafe (catalog : Catalog) : Resolved.Step → Prop
  | .update position assignments _ _ => ∀ shape, catalog.tableAt position = some shape →
      ∀ context cells, ForeignKeyUpdateConditions catalog position
        (fun row => LiteralData.movedRowid shape.rowidAlias
          (LiteralData.assignFrom context shape.columns assignments (row.values ++ cells) row))
        (shape.changedColumns (assignments.map Prod.fst))
  | .insert .. | .delete .. | .query .. | .raise .. => True

/-- Every step of every supplied trigger program has its generated-work conditions.
Empty program lists and empty bodies impose no conditions. -/
def ProgramsForeignKeySafe (catalog : Catalog) (programs : List Resolved.Program) : Prop :=
  ∀ program ∈ programs, ∀ step ∈ program.body, step.ForeignKeySafe catalog

/-- For every catalog link and selected writing action, each actual successful cell
construction satisfies the UPDATE conditions at the child. Both action forms and every
parent lookup position, new row and returned cell list are covered. NO ACTION, RESTRICT
and failed cell constructions impose nothing; cascaded DELETE needs no UPDATE condition. -/
def ActionsForeignKeySafe (catalog : Catalog) : Prop :=
  ∀ link ∈ catalog.foreignKeyLinks, ∀ action,
    (action = link.key.onDelete ∨ action = link.key.onUpdate) →
    (action = .cascade ∨ action = .setNull ∨ action = .setDefault) →
    ∀ position parentPosition key parent child new cells,
    link.parent = .located parentPosition key → catalog.tableAt position = some parent →
    catalog.tableAt link.child = some child → actionCells child parent link key new action = some cells →
    ForeignKeyUpdateConditions catalog link.child (setCells child cells) (child.changedColumns (childPositions link key))

/-- For every frame with the supplied programs, permitted raw work and good input,
the nested runner preserves the foreign-key success/stop contract. Other frames or unsafe
work impose nothing. This is the induction hypothesis for the actual row engine. -/
def NestedRun.ForeignKeyKeeps (profile : Profile) (catalog : Catalog) (programs : List Resolved.Program)
    (nested : NestedRun) : Prop :=
  ∀ frame work state, frame.programs = programs → work.ForeignKeySafe catalog → KeyState.ForeignKeyInvariant profile catalog state →
    ResultHolds (KeyState.ForeignKeyInvariant profile catalog) (KeyStop.ForeignKeyInvariant profile catalog) (nested frame work state)

/-- For every matching frame and admitted input, a successful BEFORE UPDATE program
sequence that continues the row keeps the target table's rows. Ended or failed sequences
impose nothing here. Other tables can change. This target frame ensures that UPDATE's
captured old row remains available without assuming the final row-reference atom. -/
def NestedRun.BeforeUpdateFrame (profile : Profile) (catalog : Catalog) (programs : List Resolved.Program)
    (nested : NestedRun) : Prop :=
  ∀ frame position assigned cells state reached ended, frame.programs = programs →
    (state.database catalog).Admitted profile →
    runPrograms catalog nested frame position .before (.update (some assigned)) cells state = .ok (reached, ended) →
    ended = false → (reached.database catalog).rowsAt position = (state.database catalog).rowsAt position

/-- For an actual target shape with nongenerated unmarked columns and no self-child parent
links, the resolved assignment constructor satisfies the UPDATE conditions for every
context and input-cell function. Self links can instead use the primitive scan condition.
Proof sketch: assigned positions stay in the changed closure; all remaining cells and
an unmarked alias are fixed by assignment coverage, and every scanned parent is separate. -/
theorem ForeignKeyUpdateConditions.assignFrom {catalog : Catalog} {position : Nat}
    (shape : CatalogTable) (found : catalog.tableAt position = some shape)
    (context : Resolved.EvalContext) (assignments : List (Nat × Resolved.Expr)) (cells : Row → List Value)
    (plain : ∀ cell ∉ shape.changedColumns (assignments.map Prod.fst), ∀ column,
      shape.columns[cell]? = some column → column.generated = none)
    (apart : ∀ link ∈ parentLinks catalog.foreignKeyLinks position, link.child ≠ position) :
    ForeignKeyUpdateConditions catalog position
      (fun row => LiteralData.movedRowid shape.rowidAlias
        (LiteralData.assignFrom context shape.columns assignments (cells row) row))
      (shape.changedColumns (assignments.map Prod.fst)) where
  cells other atOther := by
    have same : other = shape := Option.some.inj (atOther.symm.trans found)
    subst other
    exact RowChange.Covers.assignFrom context shape assignments cells _
      (fun pair member => shape.assigned_mem_changedColumns _ _ (List.mem_map.mpr ⟨pair, member, rfl⟩)) plain
  scans _ _ _ _ link member := apart link (List.mem_filter.mp member).1

end Belay.Sqlite.Model
