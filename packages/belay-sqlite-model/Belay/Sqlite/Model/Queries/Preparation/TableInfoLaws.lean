import Belay.Sqlite.Model.Queries.Preparation.TableInfoResolution
import Belay.Sqlite.Model.Queries.Select.OperandArms

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every catalog and name for which the catalog finds a table, the rows of {lit}`pragma_table_info` for the name are
the rows of the table that the pragma gives ({name}`CatalogTable.infoRows`). Proof sketch: the definition of
{name}`Catalog.tableInfoRows` for a name that the catalog finds. -/
theorem Catalog.tableInfoRows_of_findTable (catalog : Catalog) (name : Identifier) (position : Nat) (table : CatalogTable)
    (found : catalog.findTable name = some (position, table)) : catalog.tableInfoRows name = some table.infoRows := by
  simp [Catalog.tableInfoRows, found]

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
  simp only [traced_arms, tableInfoScope_resolveName_name]
  simp [Scope.nameRead, Scope.nameOperand, Scope.affinityAt, tableInfoScope, pragmaSource, Scope.place, Scope.argumentCell,
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
