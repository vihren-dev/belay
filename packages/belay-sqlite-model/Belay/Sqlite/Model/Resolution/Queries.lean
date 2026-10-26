import Belay.Sqlite.Model.Resolution.StatementCatalog
import Belay.Sqlite.Model.Resolution.SourceList
import Belay.Sqlite.Model.Resolution.QueryTerms
import Belay.Sqlite.Model.Resolution.QueryAggregates
import Belay.Sqlite.Model.Resolution.QueryBodyTraced

set_option doc.verso true

/-! The resolution of the clauses of a query without its trace: {lit}`resolveQueryBody` is the
projection of {lit}`resolveQueryBodyTraced`, whose steps and paths {lit}`QueryBodyTraced.lean`
describes. This file also has the collations of the first result column of a subquery. -/

namespace Belay.Sqlite.Model

/-- The explicit collation and the column collation of the first result column, as
{name}`inCollation` needs them for a subquery: those of its expression, or the collation of
the first expanded operand of {lit}`*` or {lit}`x.*`. -/
def firstCollations (scope : Scope) : List Syntax.ResultColumn → Option Collation × Option Collation
  | .expression value _ _ :: _ => (value.explicitCollation, value.columnCollation scope)
  | .star :: _ => (none, (scope.visible.head?.bind fun (position, column) => scope.starCollation position column))
  | .sourceStar name :: _ => (none, ((scope.starColumns? name).bind (·.head?)).bind fun (position, column) => scope.starCollation position column)
  | [] => (none, none)

/-- The resolved {lit}`ORDER BY` term {lit}`item`: {name}`resolveOrderTermTraced` without its trace. -/
def resolveOrderTerm (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes)
    (aliases : List (Option Identifier)) (visibleAliases : List Identifier)
    (outputs : List (Resolved.Output × String × Option Affinity)) (collations : List Collation)
    (grouped : List Resolved.Expr) (aggregate distinct : Bool) (item : Nat) (term : Syntax.OrderTerm) :
    Except ValueIssue Resolved.SortTerm :=
  (resolveOrderTermTraced dqs scope shapes aliases visibleAliases outputs collations grouped aggregate distinct
    item term).drop

/-- The resolved clauses of a query over its scope and the affinity of its first result column:
{name}`resolveQueryBodyTraced` without its trace. -/
def resolveQueryBody (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (outerAliases : List Identifier)
    (pending : List PendingSource) (query : Syntax.Subquery) : Except ValueIssue (Resolved.Query × Option Affinity) :=
  (resolveQueryBodyTraced dqs scope shapes outerAliases pending query).drop

/-- For every input: the projection of the traced query body is {name}`resolveQueryBody`. A proof that
meets the projection inside a traced resolver rewrites it with this equation. Proof sketch: both sides
are equal by definition. -/
theorem resolveQueryBodyTraced_drop (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes)
    (outerAliases : List Identifier) (pending : List PendingSource) (query : Syntax.Subquery) :
    (resolveQueryBodyTraced dqs scope shapes outerAliases pending query).drop =
      resolveQueryBody dqs scope shapes outerAliases pending query := rfl

end Belay.Sqlite.Model
