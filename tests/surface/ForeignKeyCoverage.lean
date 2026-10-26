import Belay
import Belay.Sqlite.Model.ForeignKeyUpdateCoverage
import Belay.Sqlite.Model.ForeignKeyActionCoverage
import Belay.Sqlite.Model.ForeignKeyReplaceFrame

set_option doc.verso true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 1074

/-! Actual UPDATE assignments and mapped actions discharge the FK cell-frame premises. -/

open Belay.Sqlite
open Belay.Sqlite.Model
namespace ForeignKeyCoverageFixture

/-- Repeated parent columns select the child's first column twice; the last is payload. -/
def input : Belay.Sqlite.Database := db! r"
  CREATE TABLE p(a,b,PRIMARY KEY(a,a));
  CREATE TABLE c(x,y,z,FOREIGN KEY(x,y) REFERENCES p(a,b));
  INSERT INTO p VALUES(1,2); INSERT INTO c VALUES(1,99,0);"

/-- The child table used by the generic assignment and frame laws. -/
def child : Table := (input.raw.table 1).getD { shape := { columns := [] }, rows := [] }

/-- The parent shape supplies values for the mapped action. -/
def parent : Table := (input.raw.table 0).getD { shape := { columns := [] }, rows := [] }

/-- The catalog-selected repeated-column link. -/
def link : ForeignKeyLink := input.raw.catalog.foreignKeyLinks.headD
  { child := 1
    key := { table := .ofString "p", columns := [0,1], referenced := [], onDelete := .noAction, onUpdate := .noAction }
    parent := .located 0 (.columns [(0,0),(0,0)]) }

/-- The real repeated-column comparison chosen by the catalog. -/
def key : ParentKey := .columns [(0,0),(0,0)]

/-- The actual catalog selects the repeated first child column, rather than both declarations. -/
theorem selectedTargets : link.parent = .located 0 key ∧ childPositions link key = [0,0] := by decide +kernel

/-- The existing child row before payload assignment. -/
def old : Row := { rowid := 1, values := [.integer 1, .integer 99, .integer 0] }

/-- The resolved payload assignment reports its actual assigned column. -/
def assignments : List (Nat × Resolved.Expr) := [(2, .literal (.integer 7))]

/-- The change function constructed by the ordinary UPDATE entry point. -/
def new : Row := LiteralData.movedRowid child.shape.rowidAlias
  (LiteralData.assign (.plain 0) child.shape.columns assignments old)

/-- Every cell outside the computed changed list is preserved by the actual assignment. -/
theorem payloadCells (position : Nat)
    (outside : position ∉ child.shape.changedColumns (assignments.map Prod.fst) ∨ child.shape.columns[position]? = none) :
    old.values.getD position .null = new.values.getD position .null := by
  apply LiteralData.assign_coverage (.plain 0) child.shape assignments old rfl position ?_ outside
  intro column found
  have all : ∀ value ∈ child.shape.columns, value.generated = none := by decide +kernel
  exact all column (List.mem_of_getElem? found)

/-- The real level-zero selection and assignment facts prove the full violation-count frame. -/
theorem payloadCount :
    (input.raw.setRows 1 (LiteralData.replaceRow child old new).rows).foreignKeyViolations = input.raw.foreignKeyViolations := by
  have coverage := Catalog.updateLevel_zero_agrees (catalog := input.raw.catalog) (position := 1)
    (name := .ofString "c") (table := child.shape)
    (changed := child.shape.changedColumns (assignments.map Prod.fst)) (old := old) (new := new)
    rfl rfl (by intro alias found; cases found) (by intro alias found; cases found)
    (by intro alias found; cases found) payloadCells
  exact Database.foreignKeyViolations_replace_unchanged rfl (by decide +kernel)
    (by unfold Table.RowidsDistinct; decide +kernel) old new (by decide +kernel) coverage.1 coverage.2

/-- Every writing action on the repeated key keeps the unused declaration column unchanged. -/
theorem actionKeepsUnused (action : Syntax.ForeignKeyAction) (cells : List (Nat × Value))
    (active : action = .cascade ∨ action = .setNull ∨ action = .setDefault)
    (found : actionCells child.shape parent.shape link key { rowid := 1, values := [.integer 7, .integer 2] }
      action = some cells) :
    (setCells child.shape cells old).values.getD 1 .null = .integer 99 := by
  have kept := actionCells_coverage active found (old := old) rfl 1
    (by intro column atColumn; cases atColumn; rfl) (.inl (by decide +kernel))
  exact kept.symm

/-- A supported rowid alias plus an independent payload column. -/
def aliasShape : CatalogTable :=
  { columns := [{ name := .ofString "id", declaredType := some "INTEGER" }, { name := .ofString "x", declaredType := none }]
    primaryKey := [0], rowidAlias := some 0 }

/-- The table's supported schema discharges the alias-membership premise of parent coverage. -/
theorem aliasPrimary : 0 ∈ aliasShape.primaryKey :=
  CatalogTable.alias_primaryKey (limits := Profile.pinned.limits) (by decide +kernel) rfl

/-- An UPDATE of a payload keeps the rowid through the generic alias theorem. -/
theorem payloadKeepsRowid :
    (LiteralData.movedRowid aliasShape.rowidAlias
      (LiteralData.assign (.plain 0) aliasShape.columns [(1, .literal (.integer 9))]
        { rowid := 3, values := [.integer 3, .integer 0] })).rowid = 3 := by
  apply LiteralData.assign_rowid_of_unmoved (.plain 0) aliasShape _ _ rfl
    (by intro position atAlias; cases atAlias; rfl) ?_ rfl
  intro position atAlias column atColumn
  cases atAlias
  cases atColumn
  rfl

end ForeignKeyCoverageFixture

#print axioms Belay.Sqlite.Model.matchIndex_child_mem
#print axioms Belay.Sqlite.Model.matchIndex_parent_unchanged
#print axioms Belay.Sqlite.Model.Catalog.parentKey_child_mem
#print axioms Belay.Sqlite.Model.Catalog.parentLink_child_mem
#print axioms Belay.Sqlite.Model.ForeignKeyLink.childAgrees_of_unchanged
#print axioms Belay.Sqlite.Model.Catalog.parentIndexes_primary_column
#print axioms Belay.Sqlite.Model.Catalog.parentKey_columns_unchanged
#print axioms Belay.Sqlite.Model.Catalog.parentKey_rowid_named
#print axioms Belay.Sqlite.Model.Catalog.parentKey_rowid_unchanged
#print axioms Belay.Sqlite.Model.Catalog.parentKey_rowAgrees
#print axioms Belay.Sqlite.Model.CatalogTable.assigned_mem_changedColumns
#print axioms Belay.Sqlite.Model.LiteralData.assignFrom_coverage
#print axioms Belay.Sqlite.Model.setCells_eq_assignFrom
#print axioms Belay.Sqlite.Model.LiteralData.assign_coverage
#print axioms Belay.Sqlite.Model.setCells_coverage
#print axioms Belay.Sqlite.Model.CatalogTable.alias_primaryKey
#print axioms Belay.Sqlite.Model.LiteralData.movedRowid_rowid_of_aliased
#print axioms Belay.Sqlite.Model.LiteralData.assign_rowid_of_unmoved
#print axioms Belay.Sqlite.Model.Catalog.parentLink_selfReferences
#print axioms Belay.Sqlite.Model.Catalog.updateChildren_unchanged
#print axioms Belay.Sqlite.Model.Catalog.parentLink_located
#print axioms Belay.Sqlite.Model.Catalog.updateParents_unchanged
#print axioms Belay.Sqlite.Model.updateLevel_zero_checks
#print axioms Belay.Sqlite.Model.Catalog.updateLevel_zero_agrees
#print axioms Belay.Sqlite.Model.actionCells_positions
#print axioms Belay.Sqlite.Model.actionCells_coverage
#print axioms Belay.Sqlite.Model.setCells_rowid_of_unmoved
#print axioms ForeignKeyCoverageFixture.selectedTargets
#print axioms ForeignKeyCoverageFixture.payloadCells
#print axioms ForeignKeyCoverageFixture.payloadCount
#print axioms ForeignKeyCoverageFixture.actionKeepsUnused
#print axioms ForeignKeyCoverageFixture.aliasPrimary
#print axioms ForeignKeyCoverageFixture.payloadKeepsRowid
