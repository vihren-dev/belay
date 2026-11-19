import Belay.Sqlite.Model.Schema.Ddl.CatalogOutline
import Belay.Sqlite.Model.Schema.Ddl.RenameCatalog
import Belay.Sqlite.Model.Schema.Columns.ResolveFinishShaped

set_option doc.verso true

/-! Renaming an object preserves the information that execution keeps in its catalog outline. -/

namespace Belay.Sqlite.Model

open Syntax

/-- A successful traversal preserves the list of projections if each successful edit preserves its projection. -/
private theorem mapM_some_keeps {α β : Type} (edit : α → Option α) (project : α → β)
    (keeps : ∀ a b, edit a = some b → project b = project a) :
    ∀ {xs ys : List α}, xs.mapM edit = some ys → ys.map project = xs.map project
  | [], _, ok => by simpa using congrArg (List.map project) (Option.some.inj ok).symm
  | x :: xs, _, ok => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at ok
    obtain ⟨y, first, ys, rest, rfl⟩ := ok
    simp only [List.map_cons, keeps _ _ first, mapM_some_keeps edit project keeps rest]

/-- Editing a CHECK changes only its label and its source. -/
private theorem checks_blank (target : LabelTarget) (style : RenameStyle) (new : Identifier)
    {xs ys : List CheckConstraint} (ok : xs.mapM (·.rename target style new) = some ys) :
    ys.map CheckConstraint.blankNames = xs.map CheckConstraint.blankNames := by
  apply mapM_some_keeps _ _ _ ok
  intro check result found
  unfold CheckConstraint.rename at found
  split at found
  · cases found; rfl
  · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp found
    rfl

/-- Renaming all checks on a table preserves its shape with the names erased. -/
private theorem renameChecks_blank {table result : CatalogTable} {target : LabelTarget}
    {style : RenameStyle} {new : Identifier} (ok : table.renameChecks target style new = some result) :
    result.blankNames = table.blankNames := by
  simp only [CatalogTable.renameChecks, bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at ok
  obtain ⟨columns, cols, checks, checked, rfl⟩ := ok
  have columnEq := mapM_some_keeps _ CatalogColumn.blankNames (fun col result found => by
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at found
    obtain ⟨_, h, rfl⟩ := found
    simp [CatalogColumn.blankNames, checks_blank target style new h]) cols
  simp only [CatalogTable.blankNames, columnEq, checks_blank target style new checked]

/-- Changing only the parent names of foreign keys preserves the table shape with names erased. -/
private theorem foreignKeys_blank (table : CatalogTable) (change : ForeignKey → ForeignKey)
    (same : ∀ k, (change k).blankNames = k.blankNames) :
    (table.mapForeignKeys change).blankNames = table.blankNames := by
  simp [CatalogTable.mapForeignKeys, CatalogTable.blankNames, CatalogColumn.blankNames,
    List.map_map, Function.comp_def, same]

/-- Changing a column name at any position leaves the list of blank columns intact. -/
private theorem renameColumn_blank (columns : List CatalogColumn) (index : Nat) (new : Identifier) :
    (columns.modify index (fun col => { col with name := new })).map CatalogColumn.blankNames =
      columns.map CatalogColumn.blankNames := by
  induction columns generalizing index with
  | nil => simp
  | cons col rest ih =>
    cases index with
    | zero => rfl
    | succ i => exact congrArg (col.blankNames :: ·) (ih i)

/-- Changing the parent table or parent column names preserves every blank foreign key. -/
private theorem foreignKeyChange_blank (request : RenameRequest) (old column : Identifier) (key : ForeignKey) :
    (request.foreignKeyChange old column key).blankNames = key.blankNames := by
  unfold RenameRequest.foreignKeyChange
  cases request.target <;> simp only [ForeignKey.renameParent, ForeignKey.renameParentColumn] <;> split <;> rfl

/-- The successful edit of the table named in the ALTER statement preserves its blank shape. -/
private theorem ownTable_blank {request : RenameRequest} {old column : Identifier} {table result : CatalogTable}
    (ok : request.renameOwnTable old column table = some result) : result.blankNames = table.blankNames := by
  unfold RenameRequest.renameOwnTable at ok
  split at ok
  · unfold CatalogTable.renamedTable at ok
    obtain ⟨checked, h, rfl⟩ := Option.map_eq_some_iff.mp ok
    rw [foreignKeys_blank, renameChecks_blank h]
    intro key; unfold ForeignKey.renameParent; split <;> rfl
  · simp only [CatalogTable.renamedColumn, Option.map_eq_some_iff] at ok
    obtain ⟨_, ⟨_, ⟨checked, h, rfl⟩, rfl⟩, rfl⟩ := ok
    change ((checked.renameColumnAt _ _).mapForeignKeys _).blankNames = _
    rw [foreignKeys_blank]
    · rw [← renameChecks_blank h]
      simp [CatalogTable.renameColumnAt, CatalogTable.blankNames, renameColumn_blank]
    · intro key; unfold ForeignKey.renameParentColumn; split <;> rfl
  · cases ok

/-- Each successful object edit preserves the outline of that entry. -/
private theorem renameObject_outline {context : ResolveContext} {catalog : Catalog} {request : RenameRequest}
    {old column : Identifier} {position : Nat} {object result : CatalogObject}
    (ok : renameObject context catalog request old column position object = .ok result) :
    result.entry.outline = object.entry.outline := by
  unfold renameObject at ok
  split at ok <;> rename_i entry
  · repeat' split at ok
    all_goals first
      | (cases ok; done)
      | (cases ok; simp only [entry, CatalogEntry.outline]; exact congrArg _ (ownTable_blank (by assumption)))
      | (cases ok; simp only [entry, CatalogEntry.outline]; exact congrArg _ (foreignKeys_blank _ _ (foreignKeyChange_blank request old column)))
  · cases ok; rfl
  all_goals
    simp only [Functor.map, Except.map] at ok
    split at ok <;> cases ok
    simp [entry, CatalogEntry.outline]

/-- Every successful {name}`renameCatalog` preserves the input catalog's outline.
Proof sketch: each object edit preserves its entry outline. Mapping those equalities over
the objects in position order gives the same list. The final checks return that list of objects. -/
theorem renameCatalog_sameOutline {context : ResolveContext} {catalog renamed : Catalog}
    {request : RenameRequest} {old column : Identifier}
    (ok : renameCatalog context catalog request old column = .ok renamed) :
    catalog.sameOutline renamed = true := by
  unfold renameCatalog at ok
  simp only [exceptBind_eq_ok] at ok
  obtain ⟨stored, first, _, _, last⟩ := ok
  split at last <;> cases last
  have same := mapM_ok_map_eq _ (fun object : CatalogObject => object.entry.outline)
    (fun item : CatalogObject × Nat => item.1.entry.outline)
    (fun _ _ h => renameObject_outline h) first
  rw [show catalog.zipIdx.map (fun item => item.1.entry.outline) =
      catalog.outline by
    change List.map ((fun (o : CatalogObject) => o.entry.outline) ∘ Prod.fst) _ = _
    rw [← List.map_map, List.zipIdx_map_fst]
    rfl] at same
  simpa [Catalog.sameOutline, Catalog.outline] using same

end Belay.Sqlite.Model
