import Belay.Sqlite.Model.Resolution.ParentKeys

set_option doc.verso true

/-! What a rename leaves in a catalog. A rename of a table or a column changes names: of the
object, of columns, in the labels of CHECK constraints and in the foreign keys that name a parent.
It changes no position, no kind of object, no type, no key and no resolved expression. The
{lit}`outline` of a catalog is the catalog with these names taken out. Two catalogs with one outline
give the same facts about the rows of every table, and the run of a rename checks the outline
({lit}`step`), so a law about rows needs no fact about the resolver. -/

namespace Belay.Sqlite.Model

/-- The CHECK constraint without its label and its source text, the two places where a rename
writes a new name. -/
def CheckConstraint.blankNames (check : CheckConstraint) : CheckConstraint :=
  { check with label := "", source := none }

/-- The foreign key without the names of its parent table and parent columns, the places where a
rename writes a new name. The positions of its child columns stay. -/
def ForeignKey.blankNames (key : ForeignKey) : ForeignKey :=
  { key with table := Identifier.ofString "", referenced := [] }

/-- The column without its name and without the names in its CHECK constraints and foreign keys. -/
def CatalogColumn.blankNames (column : CatalogColumn) : CatalogColumn :=
  { column with
    name := Identifier.ofString ""
    checks := column.checks.map CheckConstraint.blankNames
    foreignKeys := column.foreignKeys.map ForeignKey.blankNames }

/-- The table without the names of its columns and without the names in its CHECK constraints and
foreign keys, and without the note that a column rename quoted a name ({name}`CatalogTable.quotedRename`). -/
def CatalogTable.blankNames (table : CatalogTable) : CatalogTable :=
  { table with
    columns := table.columns.map CatalogColumn.blankNames
    checks := table.checks.map CheckConstraint.blankNames
    foreignKeys := table.foreignKeys.map ForeignKey.blankNames
    quotedRename := false }

/-- The part of a catalog object that a rename keeps: a table without names, an index as it is,
and only the kind of a view or a trigger, whose definitions are syntax that a rename rewrites. -/
inductive CatalogOutline where
  /-- A table without names ({name}`CatalogTable.blankNames`). -/
  | table (shape : CatalogTable)
  /-- A view. -/
  | view
  /-- An index, which names its table by position. -/
  | index (index : CatalogIndex)
  /-- A trigger. -/
  | trigger
  deriving DecidableEq

/-- The outline of the content of a catalog object ({name}`CatalogOutline`). -/
def CatalogEntry.outline : CatalogEntry → CatalogOutline
  | .table shape => .table shape.blankNames
  | .view _ => .view
  | .index definition => .index definition
  | .trigger _ => .trigger

/-- The outlines of the objects of a catalog, in order. Two catalogs have the same outline when
one is the other after a rename of a table or of a column. -/
def Catalog.outline (catalog : Catalog) : List CatalogOutline := catalog.map (·.entry.outline)

/-- For every catalogs with one outline, the catalogs have the same length. Proof sketch: the
lengths of the outlines are the lengths of the catalogs. -/
theorem Catalog.length_of_outline {old new : Catalog} (same : new.outline = old.outline) :
    new.length = old.length := by
  simpa [Catalog.outline] using congrArg List.length same

/-- For every catalogs with one outline and every position: the table of the new catalog at the
position is absent exactly when that of the old catalog is, and else has the same shape after
{name}`CatalogTable.blankNames`. Proof sketch: the outline at the position is the same, and a case
on the entry of each catalog at the position. -/
theorem Catalog.tableAt_of_outline {old new : Catalog} (same : new.outline = old.outline) (position : Nat) :
    (new.tableAt position).map CatalogTable.blankNames = (old.tableAt position).map CatalogTable.blankNames := by
  have at_position := congrArg (·[position]?) same
  simp only [Catalog.outline, List.getElem?_map] at at_position
  unfold Catalog.tableAt
  cases hn : new[position]? with
  | none => cases ho : old[position]? with
    | none => rfl
    | some object => simp [hn, ho] at at_position
  | some newObject => cases ho : old[position]? with
    | none => simp [hn, ho] at at_position
    | some oldObject =>
      rcases newObject with ⟨_, newEntry⟩
      rcases oldObject with ⟨_, oldEntry⟩
      simp only [hn, ho, Option.map_some, Option.some.injEq] at at_position
      cases newEntry <;> cases oldEntry <;> simp_all [CatalogEntry.outline, CatalogOutline.table.injEq]

/-- The parent that the foreign keys of each table select, in the order of the objects of the
catalog and of {name}`CatalogTable.allForeignKeys`: the parent table and parent key that
{name}`Catalog.parentLink` finds by name. An object that is not a table has none. A rename writes the
new name of a parent in the foreign keys that name it, so it leaves these links as they are. -/
def Catalog.selectedParents (catalog : Catalog) : List (List ParentLink) :=
  catalog.map fun object => match object.entry with
    | .table table => table.allForeignKeys.map catalog.parentLink
    | .index _ | .view _ | .trigger _ => []

/-- Whether the new catalog is the old catalog after a change of names: it has the same outline
({name}`Catalog.outline`). The run of a rename stores the new catalog only then. A rename can make a foreign
key find a parent that it did not find before (the key named the new name of the table, and no table had it),
so the foreign keys of the new catalog need not select the same parents; the statement theorems about foreign keys
name that as a condition of the rename ({lit}`Resolved.Statement.ForeignKeyRowsCondition`). -/
def Catalog.sameOutline (old new : Catalog) : Bool := new.outline == old.outline

/-- For every catalogs that pass {name}`Catalog.sameOutline`: the outlines are equal. Proof sketch: the test is an
equality test. -/
theorem Catalog.sameOutline_eq {old new : Catalog} (same : old.sameOutline new = true) :
    new.outline = old.outline := by
  simpa [Catalog.sameOutline] using same

/-- Whether the new catalog is the old catalog after a change that keeps the outline and the parent
that each foreign key selects ({name}`Catalog.outline`, {name}`Catalog.selectedParents`). The run of DROP COLUMN
stores the catalog of its statement only then. -/
def Catalog.keepsOutline (old new : Catalog) : Bool :=
  new.outline == old.outline && new.selectedParents == old.selectedParents

/-- For every catalogs that pass {name}`Catalog.keepsOutline`: the outlines are equal and the
selected parents are equal. Proof sketch: both tests of the conjunction are equality tests. -/
theorem Catalog.keepsOutline_eq {old new : Catalog} (kept : old.keepsOutline new = true) :
    new.outline = old.outline ∧ new.selectedParents = old.selectedParents := by
  simpa [Catalog.keepsOutline] using kept

end Belay.Sqlite.Model
