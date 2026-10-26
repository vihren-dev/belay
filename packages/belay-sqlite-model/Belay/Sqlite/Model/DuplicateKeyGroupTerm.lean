import Belay.Sqlite.Model.CountStatementResolution
import Belay.Sqlite.Model.ScalarSubqueryResolution
import Belay.Sqlite.Model.Resolution.QueryAggregatesArms

set_option doc.verso true

/-! The resolution of the grouping term of the duplicate-key query (ADR 0017, S4 and S6), and of its condition
{lit}`HAVING count(*) > 1`: the lemmas take the resolved scope as a hypothesis, because the catalog is free. -/

namespace Belay.Sqlite.Model

/-- The grouping term {lit}`k` resolves ({name}`resolveGroupTerm`), for a query whose one result column has no alias and
resolves to the given output (a scalar expression, a name and an affinity) under the given collation, in a scope and
with shapes of subqueries, to the key {lit}`key` under the collation {lit}`collation`. The formula is exactly that
equation of the resolver: resolution succeeds, and its result is that key and that collation. It restricts the term
only as the resolver does, so the cases are those of the resolver: a name of a column of the scope (also under one
{lit}`COLLATE`) or a qualified name resolves to the column, and a name that is no column can resolve in the other ways
that {name}`resolveOperand` allows, such as a quoted text when the profile allows it ({lit}`dqs`) or the constants
{lit}`TRUE` and {lit}`FALSE`. The collation is the explicit one if there is one, else the collation of the column,
else {lit}`BINARY`. A parameter resolves to a constant value, and the result-column number {lit}`1` to the result
column, both with {lit}`BINARY`. A term that the resolver rejects, such as an aggregate call, a number other than
{lit}`1` or an expression, makes the equation false. -/
def GroupTermResolvesIn (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes)
    (output : Resolved.Output × String × Option Affinity) (outputCollation : Collation) (term : Syntax.Expr)
    (key : Resolved.Expr) (collation : Collation) : Prop :=
  resolveGroupTerm dqs scope shapes [none] [output] [outputCollation] 0 term = .ok (key, collation)

/-- The grouping term {lit}`k` resolves ({name}`GroupTermResolvesIn`), for a query whose one result column is the literal
one named {lit}`"1"`, without alias and under {lit}`BINARY`, to the key {lit}`key` under the collation
{lit}`collation`. -/
def GroupTermResolves (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (term : Syntax.Expr) (key : Resolved.Expr)
    (collation : Collation) : Prop :=
  GroupTermResolvesIn dqs scope shapes (.scalar (.literal (.integer 1)), "1", none) .binary term key collation

/-- The grouping term resolves for the query whose result column is the literal one ({name}`GroupTermResolves`) exactly
when it resolves for the generic result column with the collation of the literal. Proof sketch: the collation of a
numeric literal is {lit}`BINARY`. -/
theorem GroupTermResolves.toIn {dqs : Bool} {scope : Scope} {shapes : SubqueryShapes} {term : Syntax.Expr}
    {key : Resolved.Expr} {collation : Collation} (resolves : GroupTermResolves dqs scope shapes term key collation) :
    GroupTermResolvesIn dqs scope shapes (.scalar (.literal (.integer 1)), "1", none)
      ((Syntax.Expr.numeric "1").collationIn scope) term key collation := by
  have binary : (Syntax.Expr.numeric "1").collationIn scope = .binary := by
    simp [Syntax.Expr.collationIn, Syntax.Expr.explicitCollation, Syntax.Expr.columnCollation]
  rw [binary]
  exact resolves

/-- For every catalog, table reference, position, table, shapes, result column, name and quote kind, if the table has a
column of that name at a position, the grouping term of that name resolves, in the scope of the table, to the cell of
that column under the collation of the column ({lit}`BINARY` when the column has none). The formula requires nothing of
a name that the table does not have. Proof sketch: the name resolves to the column alone
({name}`resolveName_one_source`) and the collation is the column collation of
{name}`Syntax.Expr.columnCollation_identifier_table`. -/
theorem GroupTermResolvesIn.identifier_table {dqs : Bool} {catalog : Catalog} {reference : Syntax.TableReference}
    {position : Nat} {table : CatalogTable} {shapes : SubqueryShapes} {output : Resolved.Output × String × Option Affinity}
    {outputCollation : Collation} {name : Identifier} {quote : Syntax.QuoteKind}
    {index : Nat} (found : columnPosition table.columns name = some index) :
    GroupTermResolvesIn dqs (tableScope catalog reference position table) shapes output outputCollation
      (.identifier name quote) (.column index) ((table.columns[index]?.map (·.collation)).getD .binary) := by
  have resolved : (tableScope catalog reference position table).resolveName name = .found index [index] :=
    resolveName_one_source_at found
  have collation := Syntax.Expr.columnCollation_identifier_table (catalog := catalog) (reference := reference)
    (position := position) (quote := quote) found
  unfold GroupTermResolvesIn
  rw [resolveGroupTerm_identifier_found (found := resolved) ..]
  simp only [tableScope, Scope.singleAt] at collation
  simp [tableScope, Scope.nameRead, Scope.nameOperand, Scope.singleAt, Scope.argumentCell, Scope.triggerCell,
    Syntax.Expr.collationIn, Syntax.Expr.explicitCollation, collation]
  rfl

/-- For every catalog, table reference, position, table, shapes, name and quote kind, if the table has a column of that
name at a position, the grouping term of that name resolves, for the query whose result column is the literal one, in
the scope of the table, to the cell of that column under the collation of the column. Proof sketch:
{name}`GroupTermResolvesIn.identifier_table`. -/
theorem GroupTermResolves.identifier_table {dqs : Bool} {catalog : Catalog} {reference : Syntax.TableReference}
    {position : Nat} {table : CatalogTable} {shapes : SubqueryShapes} {name : Identifier} {quote : Syntax.QuoteKind}
    {index : Nat} (found : columnPosition table.columns name = some index) :
    GroupTermResolves dqs (tableScope catalog reference position table) shapes (.identifier name quote) (.column index)
      ((table.columns[index]?.map (·.collation)).getD .binary) :=
  GroupTermResolvesIn.identifier_table found

/-- For every scope, shapes and name of a call, the condition {lit}`count(*) > 1` resolves, when the
aggregate calls of the query are the one call {lit}`count(*)`, to the comparison of the value of aggregate 0 with
the literal one, under {lit}`BINARY`, with no affinity. Proof sketch: unfold the resolver; the call is the aggregate
with index 0, and neither operand names a column. -/
theorem resolveOperand_moreThanOne (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (name : String)
    (aggregates : shapes.aggregates = [.callStar name]) :
    resolveOperand dqs scope shapes false (.compare .gt (.callStar name) (.numeric "1")) =
      .ok (.compare .gt none (.aggregateValue 0) (.literal (.integer 1)) .binary, none) := by
  have literal : queryNumeric "1" false = .ok (.integer 1) := by rfl
  simp [traced_arms, aggregates, Syntax.Expr.indexIn, Syntax.Expr.same, literal, truthTest, comparisonAffinity,
    comparisonCollation, Syntax.Expr.explicitCollation, Syntax.Expr.columnCollation, Bind.bind, Except.bind]
  rfl

end Belay.Sqlite.Model
