import Belay.Sqlite.Model.Queries.Select.SelectNoFromResolution
import Belay.Sqlite.Model.Queries.Select.SubquerySelectResolution
import Belay.Sqlite.Model.Queries.Evaluation.SelectOneResolution

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The shape of a subquery with one result column that no query surrounds and that is no compound: its
affinity, the explicit collation and the column collation of its result column, and the lowest cell position
{lit}`lowest` that it reads. Supply the declaration of its origin column through
{lit}`originType`; omit it for an expression without a column origin. The
optional FLEXNUM flag defaults to false for a physical table's expression. -/
def scalarShape (affinity : Option Affinity) (explicitCollation columnCollation : Option Collation)
    (lowest : Option Nat) (originType : Option String := none) (flexibleNumeric : Bool := false) : SubqueryShape :=
  { parent := none, columns := 1, affinity, originType, flexibleNumeric,
    explicitCollation, columnCollation, lowest, derived := false }

/-- For every catalog, table reference, position, table, name and quote kind, if the table has a column of that name at
a position, the column collation of the name in the scope of the table ({name}`Syntax.Expr.columnCollation`) is the collation of the
column at that position. The formula requires nothing of a name that the table does not have. Proof sketch:
the name resolves to the column alone ({name}`resolveName_one_source`), and the scope of the table has the columns
of the table ({name}`Scope.columns_single`). -/
theorem Syntax.Expr.columnCollation_identifier_table {catalog : Catalog} {reference : Syntax.TableReference}
    {position : Nat} {table : CatalogTable} {name : Identifier} {quote : Syntax.QuoteKind} {index : Nat}
    (found : columnPosition table.columns name = some index) :
    (Syntax.Expr.identifier name quote).columnCollation (tableScope catalog reference position table) =
      table.columns[index]?.map (·.collation) := by
  simp [Syntax.Expr.columnCollation, tableScope, resolveName_one_source_at found, Scope.columns_singleAt]

/-- For a name that selects a column of a physical table, its origin type is
that column's declaration. Proof sketch: name resolution selects one cell of
the ordinary table scope, whose columns are the table's columns. -/
theorem Syntax.Expr.originType_identifier_table {catalog : Catalog} {reference : Syntax.TableReference}
    {position : Nat} {table : CatalogTable} {name : Identifier} {quote : Syntax.QuoteKind} {index : Nat}
    (found : columnPosition table.columns name = some index) (shapes : SubqueryShapes) :
    (Syntax.Expr.identifier name quote).originType (tableScope catalog reference position table) shapes =
      table.columns[index]?.bind (·.declaredType) := by
  simp only [Syntax.Expr.originType, tableScope, resolveName_one_source_at found]
  simp [Scope.nameOriginType, Scope.originTypeAt, Scope.columns, Scope.triggerCell, Scope.singleAt]

/-- For every scope, shapes, subquery syntax with one expression column and no parent, and resolved query with one column,
the shape that resolution records for the subquery is the shape of a one-column subquery ({name}`scalarShape`) with the
affinity given, the collations of the expression ({name}`firstCollations`), its
declared-type origin, FLEXNUM flag, and some lowest position. Proof sketch:
the subquery has no parent and one resolved column, and the lowest position is a fold that the lemma leaves open. -/
theorem subqueryShape_scalar (scope : Scope) (shapes : SubqueryShapes) (value : Syntax.Expr) (alias : Option Identifier)
    (text : String) (source : Option Syntax.TableReference) (filter : Option Syntax.Expr) (query : Resolved.Query)
    (affinity : Option Affinity) (one : query.columns.length = 1) :
    ∃ lowest, subqueryShape scope shapes (Syntax.Subquery.mk [.expression value alias text] source [] filter [] [] none none
      none none false none none) query affinity =
        scalarShape affinity value.explicitCollation (value.columnCollation scope) lowest
          (value.originType scope shapes) (value.flexibleNumeric scope shapes) :=
  by simp [subqueryShape, firstCollations, one, scalarShape, resultOriginTypes, resultFlexibleNumerics]

end Belay.Sqlite.Model
