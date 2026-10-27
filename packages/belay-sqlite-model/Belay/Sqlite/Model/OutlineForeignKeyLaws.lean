import Belay.Sqlite.Model.ForeignKeyFacts
import Belay.Sqlite.Model.OutlineKeyLaws

set_option doc.verso true

/-! The foreign-key facts that a rename keeps. A rename writes the new name of a table or a
column into the foreign keys that name it, and the run of a rename stores the new catalog only
when each foreign key selects the same parent ({lit}`Catalog.selectedParents`). A child row then
finds its parent in the same rows by the same child columns, so a database that has its row
references and compatible parent schemas keeps both. -/

namespace Belay.Sqlite.Model

/-- The foreign keys of the blanked table are the blanked foreign keys of the table, in the same
order. Proof sketch: the lists of the columns map and flatten. -/
theorem CatalogTable.allForeignKeys_blankNames (table : CatalogTable) :
    table.blankNames.allForeignKeys = table.allForeignKeys.map ForeignKey.blankNames := by
  simp [CatalogTable.allForeignKeys, CatalogTable.blankNames, List.flatMap_map, List.map_flatMap, CatalogColumn.blankNames]

/-- For every foreign keys that have one form after {name}`ForeignKey.blankNames`: the same child
columns. Proof sketch: blanking keeps the columns. -/
theorem ForeignKey.columns_of_blankNames {first second : ForeignKey} (same : first.blankNames = second.blankNames) :
    first.columns = second.columns :=
  congrArg (fun key => key.columns) same

/-- For every tables with one shape after {name}`CatalogTable.blankNames` and every foreign key of
the second table: the first table has a foreign key with the same blanked form at the same place,
and two functions that agree on the keys of the tables in order agree there. Proof sketch: the
blanked lists of foreign keys are equal ({name}`CatalogTable.allForeignKeys_blankNames`), so the
keys at an index have equal forms, and a list of values mapped from the keys agrees at the index. -/
theorem CatalogTable.foreignKey_of_blankNames {first second : CatalogTable}
    (same : first.blankNames = second.blankNames) {firstValue secondValue : ForeignKey → ParentLink}
    (values : second.allForeignKeys.map secondValue = first.allForeignKeys.map firstValue)
    {key : ForeignKey} (member : key ∈ second.allForeignKeys) :
    ∃ other ∈ first.allForeignKeys, other.blankNames = key.blankNames ∧ firstValue other = secondValue key := by
  have blanked := congrArg CatalogTable.allForeignKeys same
  rw [CatalogTable.allForeignKeys_blankNames, CatalogTable.allForeignKeys_blankNames] at blanked
  obtain ⟨index, below, found⟩ := List.getElem_of_mem member
  have lengths : first.allForeignKeys.length = second.allForeignKeys.length := by
    simpa using congrArg List.length blanked
  have belowFirst : index < first.allForeignKeys.length := lengths ▸ below
  refine ⟨first.allForeignKeys[index], List.getElem_mem belowFirst, ?_, ?_⟩
  · have at_index := congrArg (·[index]?) blanked
    simp only [List.getElem?_map, List.getElem?_eq_getElem belowFirst, List.getElem?_eq_getElem below, Option.map_some,
      Option.some.injEq] at at_index
    rw [at_index, found]
  · have at_index := congrArg (·[index]?) values
    simp only [List.getElem?_map, List.getElem?_eq_getElem belowFirst, List.getElem?_eq_getElem below, Option.map_some,
      Option.some.injEq] at at_index
    rw [← at_index, found]

/-- For every tables with one shape after {name}`CatalogTable.blankNames`: the index lookup of
{name}`indexHolds` is the same function. Proof sketch: it reads the affinity and the collation of
the parent column at each position, and the column of the other table at the position is the blanked
form of the column ({name}`CatalogTable.column_of_blankNames`). -/
theorem indexHolds_of_blankNames {first second : CatalogTable} (same : first.blankNames = second.blankNames) :
    indexHolds second = indexHolds first := by
  funext pairs values row
  unfold indexHolds
  congr 1
  funext entry
  obtain ⟨⟨_, position⟩, value⟩ := entry
  dsimp only
  cases found : first.columns[position]? with
  | none =>
    cases other : second.columns[position]? with
    | none => rfl
    | some column =>
      obtain ⟨back, backFound, _⟩ := CatalogTable.column_of_blankNames same.symm other
      simp [found] at backFound
  | some column =>
    obtain ⟨other, otherFound, blanked⟩ := CatalogTable.column_of_blankNames same found
    have declared := congrArg CatalogColumn.declaredType blanked
    have strict := congrArg CatalogColumn.strictType blanked
    have collation := congrArg CatalogColumn.collation blanked
    simp only [CatalogColumn.blankNames] at declared strict collation
    simp [otherFound, indexAffinity, CatalogColumn.affinity, declared, strict, collation]

/-- For every tables with one shape after {name}`CatalogTable.blankNames`, links with the same
child columns and every key: the lookup of a parent row {name}`parentFound` gives the same
result. Proof sketch: the child values read the child columns only, and the index lookup is the
same function ({name}`indexHolds_of_blankNames`). -/
theorem parentFound_of_blankNames {first second : CatalogTable} (same : first.blankNames = second.blankNames)
    {firstLink secondLink : ForeignKeyLink} (columns : secondLink.key.columns = firstLink.key.columns)
    (key : ParentKey) (values : List Value) (rows : List Row) (itself : Option Row) :
    parentFound second key secondLink values rows itself = parentFound first key firstLink values rows itself := by
  have keyed : childValues secondLink key values = childValues firstLink key values := by
    cases key <;> simp [childValues, childPositions, columns]
  unfold parentFound
  rw [keyed, indexHolds_of_blankNames same]

/-- For every database and catalog with its outline, and position: the rows at the position in the
database with the catalog are the rows of the database. Proof sketch: the table at the position is
absent in both catalogs or in neither ({name}`Catalog.tableAt_of_outline`), and the rows are those of the
database. -/
theorem Database.rowsAt_of_outline {database : Database} {renamed : Catalog}
    (same : renamed.outline = database.catalog.outline) (position : Nat) :
    ({ database with catalog := renamed } : Database).rowsAt position = database.rowsAt position := by
  have shapes := Catalog.tableAt_of_outline same position
  unfold Database.rowsAt Database.table
  cases renamedShape : renamed.tableAt position with
  | none =>
    cases oldShape : database.catalog.tableAt position with
    | none => rfl
    | some shape => simp [renamedShape, oldShape] at shapes
  | some shape =>
    cases oldShape : database.catalog.tableAt position with
    | none => simp [renamedShape, oldShape] at shapes
    | some other => simp

/-- For every database, catalog with its outline and links of one position with the same child
columns and the same parent: a row satisfies the link in the database with the catalog exactly
when it satisfies the link in the database ({name}`ForeignKeyLink.satisfied`). Proof sketch: the
NULL test and the child values read the child columns and the parent; the parent row is looked up
in the same rows ({name}`Database.rowsAt_of_outline`) of a parent table with the same shape after the
names ({name}`parentFound_of_blankNames`). -/
theorem ForeignKeyLink.satisfied_of_outline {database : Database} {renamed : Catalog}
    (same : renamed.outline = database.catalog.outline) {firstLink secondLink : ForeignKeyLink}
    (columns : secondLink.key.columns = firstLink.key.columns) (parent : secondLink.parent = firstLink.parent)
    (row : Row) :
    secondLink.satisfied { database with catalog := renamed } row = firstLink.satisfied database row := by
  have keyed : ∀ key, childValues secondLink key row.values = childValues firstLink key row.values := by
    intro key
    cases key <;> simp [childValues, childPositions, columns]
  unfold ForeignKeyLink.satisfied ForeignKeyLink.hasNull
  rw [parent]
  cases firstLink.parent with
  | missing => simp [columns]
  | mismatch position => simp [columns]
  | located position key =>
    simp only [keyed]
    congr 1
    have shapes := Catalog.tableAt_of_outline same position
    cases renamedShape : renamed.tableAt position with
    | none =>
      cases oldShape : database.catalog.tableAt position with
      | none => simp
      | some shape => simp [renamedShape, oldShape] at shapes
    | some shape =>
      cases oldShape : database.catalog.tableAt position with
      | none => simp [renamedShape, oldShape] at shapes
      | some other =>
        simp only [renamedShape, oldShape, Option.map_some, Option.some.injEq] at shapes
        rw [Database.rowsAt_of_outline same]
        exact parentFound_of_blankNames shapes.symm columns key row.values _ none

end Belay.Sqlite.Model
