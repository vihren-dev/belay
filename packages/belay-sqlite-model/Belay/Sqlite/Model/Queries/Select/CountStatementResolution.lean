import Belay.Sqlite.Model.Queries.Preparation.CountSelectResolution
import Belay.Sqlite.Model.Queries.Select.SubquerySelectResolution
import Belay.Sqlite.Model.Queries.Evaluation.SelectOneResolution

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The shape of a scalar subquery {lit}`(SELECT count(*) …)` that no query surrounds: one result column, with
no affinity and no collation, that is no derived table, and that reads the lowest cell position
{lit}`lowest`. -/
def countShape (lowest : Option Nat) : SubqueryShape :=
  { parent := none, columns := 1, affinity := none, explicitCollation := none, columnCollation := none, lowest,
    derived := false }

/-- For every scope, shapes, subquery syntax of the form {lit}`SELECT count(*) …` and resolved count query, the shape
that resolution records for the subquery is the shape of a count query ({name}`countShape`) for some lowest
position. Proof sketch: the subquery has no parent, its resolved query has one column, its result column
{lit}`count(*)` has no affinity and no collation, and the lowest position is a fold that the lemma leaves
open. -/
theorem subqueryShape_count (scope : Scope) (shapes : SubqueryShapes) (source : Option Syntax.TableReference)
    (filter : Option Syntax.Expr) (name : String) (alias : Option Identifier) (text : String) (query : Resolved.Query)
    (columns : query.columns = [.aggregate .countRows]) :
    ∃ lowest, subqueryShape scope shapes (Syntax.Subquery.mk [.expression (.callStar name) alias text] source []
      filter [] [] none none none none false none none) query none = countShape lowest := by
  simp [subqueryShape, firstCollations, Syntax.Expr.explicitCollation, Syntax.Expr.columnCollation, columns, countShape,
    resultOriginTypes, Syntax.Expr.originType, resultFlexibleNumerics, Syntax.Expr.flexibleNumeric]

end Belay.Sqlite.Model
