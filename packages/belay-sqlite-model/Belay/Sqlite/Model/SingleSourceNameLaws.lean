import Belay.Sqlite.Model.SimpleSourceResolution

set_option doc.verso true

/-! The resolution of the name of a column in the scope of one source (ADR 0017, S4): the columns of
the scope of a table, and the laws that a name which the table has resolves to its column at its
position, with the affinity of the column. A law covers the names that the table has and says
nothing about the others, which can be a double-quoted text. -/

namespace Belay.Sqlite.Model

variable {dqs : Bool} {scope : Scope} {shapes : SubqueryShapes} {misuse : Bool}

/-- The columns of the scope of one source are the columns of the source. Proof sketch: the
definitions compute. -/
theorem Scope.columns_single (source : Identifier) (columns : List CatalogColumn) (hasRowid : Bool) :
    (Scope.single source columns hasRowid).columns = columns := by
  simp [Scope.columns, Scope.single]

/-- The columns of the scope of one source read from the catalog are the columns of the source. Proof
sketch: the definitions compute. -/
theorem Scope.columns_singleAt (position : Option Nat) (source : Identifier) (columns : List CatalogColumn)
    (hasRowid : Bool) : (Scope.singleAt position source columns hasRowid).columns = columns := by
  simp [Scope.columns, Scope.singleAt]

/-- In the scope of one source read from the catalog, an unqualified name that names the column at
position {lit}`index` resolves to that column alone. Proof sketch: as {lit}`resolveName_one_source`. -/
theorem resolveName_one_source_at {position : Option Nat} {name : Identifier} {source : Identifier}
    {columns : List CatalogColumn} {hasRowid : Bool} {index : Nat} (found : columnPosition columns name = some index) :
    (Scope.singleAt position source columns hasRowid).resolveName name = .found index [index] := by
  simp [Scope.resolveName, Scope.depths, Scope.singleAt, Scope.resolveAt, Scope.resolveStep, found]

/-- In the scope of one source, an unqualified name that names the column at position {lit}`index`
resolves to that column alone. Proof sketch: the scope has one source at depth 0 that is no
trigger's row, so the name resolves to the first column of the name in it
({name}`Scope.resolveStep`). -/
theorem resolveName_one_source {name : Identifier} {source : Identifier} {columns : List CatalogColumn}
    {hasRowid : Bool} {index : Nat} (found : columnPosition columns name = some index) :
    (Scope.single source columns hasRowid).resolveName name = .found index [index] := by
  simp [Scope.resolveName, Scope.depths, Scope.single, Scope.resolveAt, Scope.resolveStep, found]

/-- In the scope of one source, an unqualified name that names the column at position {lit}`index`
resolves to that column, with the affinity of the column. The law covers a name that the scope finds and says nothing about a name that it does not find. Proof sketch: the name resolves to the
column alone ({name}`resolveName_one_source`), and no cell of the source is an argument cell or a
trigger cell. -/
theorem resolveOperand_identifier_single {name : Identifier} {quote : Syntax.QuoteKind} {source : Identifier}
    {columns : List CatalogColumn} {hasRowid : Bool} {index : Nat} (found : columnPosition columns name = some index) :
    resolveOperand dqs (Scope.single source columns hasRowid) shapes misuse (.identifier name quote) =
      .ok (.column index, columns[index]?.map CatalogColumn.affinity) := by
  simp only [traced_arms, resolveName_one_source found]
  simp [Scope.nameRead, Scope.nameOperand, Scope.affinityAt, Scope.single, Scope.argumentCell, Scope.triggerCell, Scope.columns]

/-- In the scope of one source read from the catalog, an unqualified name that names the column at
position {lit}`index` resolves to that column, with the affinity of the column. The law covers a name that the
scope finds and says nothing about a name that it does not find. Proof sketch: as
{name}`resolveOperand_identifier_single`, with {name}`resolveName_one_source_at`. -/
theorem resolveOperand_identifier_singleAt {position : Option Nat} {name : Identifier} {quote : Syntax.QuoteKind}
    {source : Identifier} {columns : List CatalogColumn} {hasRowid : Bool} {index : Nat}
    (found : columnPosition columns name = some index) :
    resolveOperand dqs (Scope.singleAt position source columns hasRowid) shapes misuse (.identifier name quote) =
      .ok (.column index, columns[index]?.map CatalogColumn.affinity) := by
  simp only [traced_arms, resolveName_one_source_at found]
  simp [Scope.nameRead, Scope.nameOperand, Scope.affinityAt, Scope.singleAt, Scope.argumentCell, Scope.triggerCell,
    Scope.columns]

/-- A name of a column of the table at a catalog position resolves to the column at its position,
with its affinity. The law covers a name that the table has and says nothing about a name that it does not have. Proof sketch: {name}`tableScope` is the scope of one source, so this is
{name}`resolveOperand_identifier_singleAt`. -/
theorem resolveOperand_identifier_table {catalog : Catalog} {reference : Syntax.TableReference}
    {position : Nat} {table : CatalogTable} {name : Identifier} {quote : Syntax.QuoteKind} {index : Nat}
    (found : columnPosition table.columns name = some index) :
    resolveOperand dqs (tableScope catalog reference position table) shapes misuse (.identifier name quote) =
      .ok (.column index, table.columns[index]?.map CatalogColumn.affinity) :=
  resolveOperand_identifier_singleAt found

end Belay.Sqlite.Model
