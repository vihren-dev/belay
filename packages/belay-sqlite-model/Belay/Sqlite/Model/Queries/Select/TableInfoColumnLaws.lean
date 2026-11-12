import Belay.Sqlite.Model.Queries.Preparation.TableInfoLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every table-info reference, argument and rows, the unqualified name
{lit}`type` resolves to the declared-type cell at position 2. Proof sketch: the
pragma's fixed visible column names put only {lit}`type` at that position. -/
theorem tableInfoScope_resolveName_type (reference : Syntax.TableReference) (argument : List UInt8)
    (rows : List (List Value)) :
    (tableInfoScope reference argument rows).resolveName (name! "type") = .found 2 [2] := by
  have position : columnPosition (tableInfoNames.map (fun name =>
      ({ name := Identifier.ofString name, declaredType := none } : CatalogColumn)) ++
      [{ name := Identifier.ofString "arg", declaredType := none },
       { name := Identifier.ofString "schema", declaredType := none }]) (name! "type") = some 2 := by
    decide +kernel
  simp [tableInfoScope, pragmaSource, Scope.place, Scope.resolveName, Scope.depths,
    Scope.resolveAt, Scope.resolveStep, position]

/-- For every table-info reference, argument, rows, quote kind, subquery shapes and
misuse flag, the name {lit}`type` resolves to column 2 with BLOB affinity, which
converts no value. Proof sketch: use {name}`tableInfoScope_resolveName_type` and
read the fixed column's affinity. -/
theorem resolveOperand_tableInfo_type (dqs : Bool) (reference : Syntax.TableReference)
    (argument : List UInt8) (rows : List (List Value)) (quote : Syntax.QuoteKind)
    (shapes : SubqueryShapes) (misuse : Bool) :
    resolveOperand dqs (tableInfoScope reference argument rows) shapes misuse
        (.identifier (name! "type") quote) = .ok (.column 2, some .blob) := by
  simp only [traced_arms, tableInfoScope_resolveName_type]
  simp [Scope.nameRead, Scope.nameOperand, Scope.affinityAt, tableInfoScope, pragmaSource, Scope.place,
    Scope.argumentCell, Scope.triggerCell, Scope.columns, tableInfoNames,
    CatalogColumn.affinity, affinityOf]

/-- For every table-info reference, argument and rows, its declared-type cell uses
BINARY collation. Proof sketch: the fixed pragma columns declare no collation. -/
theorem tableInfoScope_collation_type (reference : Syntax.TableReference) (argument : List UInt8)
    (rows : List (List Value)) :
    (tableInfoScope reference argument rows).columns[2]?.map (·.collation) = some Collation.binary := by
  simp [tableInfoScope, pragmaSource, Scope.place, tableInfoNames, Scope.columns]

end Belay.Sqlite.Model
