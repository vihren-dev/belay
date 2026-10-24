import Belay.Sqlite.Model.Resolution.PragmaRows
import Belay.Sqlite.Model.TableInfoResolution

set_option doc.verso true

/-! The facts of the schema that {lit}`pragma_table_info('t')` states (ADR 0017, S4): the table lookup ignores ASCII case,
the rows of the pragma for a table of the catalog are the columns of the table that are not generated, and the name column
of a row is the name of its column as text. -/

namespace Belay.Sqlite.Model

/-- For every catalog and two names that are the same name for SQLite (equal after ASCII lowercase,
{name}`Identifier.sameName`), the catalog finds the same table for both. The formula says nothing of names that differ
after ASCII lowercase, such as {lit}`É` and {lit}`é`. Proof sketch: the lookup tests {name}`Identifier.sameName` of
each object with the name, and the test with a name equals the test with the other name when the two names have equal
folds. -/
theorem Catalog.findTable_sameName (catalog : Catalog) (left right : Identifier) (same : left.sameName right = true) :
    catalog.findTable left = catalog.findTable right := by
  have folds : left.folded = right.folded := by simpa [Identifier.sameName] using same
  have test : ∀ object : CatalogObject, object.name.sameName left = object.name.sameName right := by
    intro object
    simp [Identifier.sameName, folds]
  simp [Catalog.findTable, Catalog.find, test]

/-- For every catalog and name for which the catalog finds a table, the rows of {lit}`pragma_table_info` for the name are
the rows of the table that the pragma gives ({name}`CatalogTable.infoRows`). Proof sketch: the definition of
{name}`Catalog.tableInfoRows` for a name that the catalog finds. -/
theorem Catalog.tableInfoRows_of_findTable (catalog : Catalog) (name : Identifier) (position : Nat) (table : CatalogTable)
    (found : catalog.findTable name = some (position, table)) : catalog.tableInfoRows name = some table.infoRows := by
  simp [Catalog.tableInfoRows, found]

/-- Every pair of the indexed list has a first part that is an item of the list. Proof sketch: the first parts of the
indexed list are the list ({name}`List.zipIdx_map_fst`). -/
theorem List.mem_of_mem_zipIdx_fst {α : Type} {list : List α} {start : Nat} {pair : α × Nat} (member : pair ∈ list.zipIdx start) :
    pair.1 ∈ list := by
  have := List.mem_map_of_mem (f := Prod.fst) member
  rwa [List.zipIdx_map_fst] at this

/-- Every item of a list is the first part of some pair of the indexed list. Proof sketch: the first parts of the indexed
list are the list ({name}`List.zipIdx_map_fst`). -/
theorem List.exists_mem_zipIdx_of_mem {α : Type} {list : List α} {start : Nat} {item : α} (member : item ∈ list) :
    ∃ index, (item, index) ∈ list.zipIdx start := by
  have : item ∈ (list.zipIdx start).map Prod.fst := by rwa [List.zipIdx_map_fst]
  obtain ⟨⟨found, index⟩, inside, rfl⟩ := List.mem_map.mp this
  exact ⟨index, inside⟩

/-- For every table, argument and test {lit}`Q` of a value, some row of the pragma {lit}`pragma_table_info` for the table
(a row of {name}`CatalogTable.infoRows` with the argument and NULL as its two hidden cells) passes the test with its name
column (cell 1) exactly when the table has a column that is not generated whose name, as text, passes the test. The test
sees the bytes of the name, so a test of equality with a text is a comparison of bytes and the case of the letters
matters. Proof sketch: a row of the pragma is the row of {name}`tableInfoRow` of one stored column followed by the two
hidden cells, so its cell 1 is the text of the name of the column; the stored columns are the columns that are not
generated, and the index lists keep the items. -/
theorem CatalogTable.exists_pragmaRow_name (table : CatalogTable) (argument : List UInt8) (test : Value → Prop) :
    (∃ row ∈ table.infoRows.map (· ++ [Value.text argument, Value.null]), test (row[1]?.getD Value.null)) ↔
      ∃ column ∈ table.columns, column.generated.isNone = true ∧ test (.text column.name.bytes) := by
  unfold CatalogTable.infoRows
  simp only [List.mem_map]
  constructor
  · rintro ⟨row, ⟨info, ⟨⟨⟨column, position⟩, cid⟩, member, rfl⟩, rfl⟩, named⟩
    have stored := List.mem_of_mem_zipIdx_fst member
    simp only at stored
    obtain ⟨inColumns, generated⟩ := List.mem_filter.mp stored
    exact ⟨column, List.mem_of_mem_zipIdx_fst inColumns, by simpa using generated, by simpa [tableInfoRow] using named⟩
  · rintro ⟨column, inColumns, generated, named⟩
    obtain ⟨position, indexed⟩ := List.exists_mem_zipIdx_of_mem (start := 0) inColumns
    obtain ⟨cid, stored⟩ := List.exists_mem_zipIdx_of_mem (start := 0)
      (List.mem_filter (p := fun pair : CatalogColumn × Nat => pair.fst.generated.isNone).mpr ⟨indexed, generated⟩)
    exact ⟨_, ⟨_, ⟨_, stored, rfl⟩, rfl⟩, by simpa [tableInfoRow] using named⟩

/-- For every value and bytes, the value compares equal to the text of the bytes under {lit}`BINARY` exactly when the value is that
text. The formula includes a NULL and the numbers: they rank below a text, so they never compare equal to it. Proof
sketch: a value of another storage class has another rank; a text has the same rank and number, so only the bytes are
compared. -/
theorem Collation.binary_compare_text (value : Value) (bytes : List UInt8) :
    Collation.binary.compare value (.text bytes) = .eq ↔ value = .text bytes := by
  cases value <;> simp [Collation.compare, Collation.key, Value.compare, compareLex, compareOn, Value.rank, Value.scaled,
    Value.bytes, Ordering.then]
  rename_i bits
  by_cases ranked : (realScaled bits).isSome = true <;> simp [ranked]

/-- For every reference, argument and rows, the unqualified name {lit}`name` resolves in the scope of
{lit}`pragma_table_info` ({name}`tableInfoScope`) to the cell 1 of the pragma, read alone. Proof sketch: the scope has
one source with the eight cells of {name}`pragmaSource`, and only cell 1 has the name; the computation does not read the
name of the source. -/
theorem tableInfoScope_resolveName_name (reference : Syntax.TableReference) (argument : List UInt8)
    (rows : List (List Value)) :
    (tableInfoScope reference argument rows).resolveName (name! "name") = .found 1 [1] := by
  have position : columnPosition (tableInfoNames.map (fun name =>
      ({ name := Identifier.ofString name, declaredType := none } : CatalogColumn)) ++
      [{ name := Identifier.ofString "arg", declaredType := none }, { name := Identifier.ofString "schema", declaredType := none }])
      (name! "name") = some 1 := by
    decide +kernel
  simp [tableInfoScope, pragmaSource, Scope.place, Scope.resolveName, Scope.depths, Scope.resolveAt, Scope.resolveStep,
    position]

/-- For every reference, argument, rows, quote kind, shapes and misuse flag, the name {lit}`name` resolves in the scope of
{lit}`pragma_table_info` ({name}`tableInfoScope`) to cell 1 of the pragma, with the affinity {lit}`BLOB` of a column without
a declared type, which converts nothing. Proof sketch: the name resolves to cell 1 alone ({name}`tableInfoScope_resolveName_name`), and the cell is neither an
argument cell nor a trigger cell. -/
theorem resolveOperand_tableInfo_name (dqs : Bool) (reference : Syntax.TableReference) (argument : List UInt8)
    (rows : List (List Value)) (quote : Syntax.QuoteKind) (shapes : SubqueryShapes) (misuse : Bool) :
    resolveOperand dqs (tableInfoScope reference argument rows) shapes misuse (.identifier (name! "name") quote) =
      .ok (.column 1, some .blob) := by
  simp only [resolveOperand, tableInfoScope_resolveName_name]
  simp [Scope.nameRead, Scope.nameOperand, tableInfoScope, pragmaSource, Scope.place, Scope.argumentCell,
    Scope.triggerCell, Scope.columns, tableInfoNames, CatalogColumn.affinity, affinityOf]

/-- For every reference, argument and rows, the collation of cell 1 of the pragma {lit}`pragma_table_info`, which holds the
name, is {lit}`BINARY` ({name}`tableInfoScope`): the cells of the pragma have no declared collation, so the comparison of the
name with a text compares bytes. Proof sketch: the scope has the eight cells of {name}`pragmaSource`, which have the
default collation. -/
theorem tableInfoScope_collation_name (reference : Syntax.TableReference) (argument : List UInt8)
    (rows : List (List Value)) :
    (tableInfoScope reference argument rows).columns[1]?.map (·.collation) = some Collation.binary := by
  simp [tableInfoScope, pragmaSource, Scope.place, tableInfoNames, Scope.columns]

end Belay.Sqlite.Model
