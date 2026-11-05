import Belay.Sqlite.Model.Resolution.QueryAggregates

set_option doc.verso true

/-! The equations of {lit}`resolveAggregateCall` and {lit}`resolveGroupTerm` in the shape that the
functions had before the name trace was threaded through them: proofs about the aggregates of a
query and its grouping terms unfold them with {lit}`simp only [traced_arms]` and meet the same
steps as before. -/

namespace Belay.Sqlite.Model

/-- For every scope, shapes and function name: the call with a star in place of its arguments, for
example {lit}`count(*)`, is the aggregate that counts rows. Proof
sketch: both sides are equal by definition. -/
@[traced_arms] theorem resolveAggregateCall_callStar (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes)
    (name : String) : resolveAggregateCall dqs scope shapes (.callStar name) = .ok .countRows := rfl

/-- For every grouping term that is an unqualified name which a column of the scope has: the term
reads that column, with the collation of the term, and an issue is moved to the term. Proof sketch:
unfold the traced form; the name is found, so the lookup of the operand is the read of the column. -/
@[traced_arms] theorem resolveGroupTerm_identifier_found (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes)
    (aliases : List (Option Identifier)) (outputs : List (Resolved.Output × String × Option Affinity))
    (collations : List Collation) (item : Nat) (name : Identifier) (quote : Syntax.QuoteKind) (position : Nat)
    (reads : List Nat) (found : scope.resolveName name = .found position reads) :
    resolveGroupTerm dqs scope shapes aliases outputs collations item (.identifier name quote) =
      ((scope.nameRead reads).map fun operand => (operand.1, (Syntax.Expr.identifier name quote).collationIn scope)).mapError
        (ValueIssue.under [4, item]) := by
  simp only [resolveGroupTerm, resolveGroupTermTraced, found, identifierTraced, traced_drop]
  cases scope.nameRead reads <;> rfl

/-- For every grouping term that is a collated column ({name}`Syntax.Expr.collatedColumn`: a name
under one {lit}`COLLATE` that reads a column of the scope, or any qualified name under one
{lit}`COLLATE`, which enters operand resolution even when its lookup fails), the term resolves as
its operand does, with the collation of the term, and an issue is moved to the term. The formula
requires nothing of any other term under {lit}`COLLATE`. Proof sketch: unfold the traced form; the
hypothesis selects the operand branch. -/
theorem resolveGroupTerm_collatedColumn (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes)
    (aliases : List (Option Identifier)) (outputs : List (Resolved.Output × String × Option Affinity))
    (collations : List Collation) (item : Nat) (operand : Syntax.Expr) (name : Identifier)
    (collated : (Syntax.Expr.collate operand name).collatedColumn scope = true) :
    resolveGroupTerm dqs scope shapes aliases outputs collations item (.collate operand name) =
      ((resolveOperand dqs scope shapes true (.collate operand name)).map fun resolved =>
        (resolved.1, (Syntax.Expr.collate operand name).collationIn scope)).mapError (ValueIssue.under [4, item]) := by
  simp only [resolveGroupTerm, resolveGroupTermTraced, resolveOperand, collated, ite_true, traced_drop]
  cases (resolveOperandTraced dqs scope shapes true (operand.collate name)).drop <;> rfl

/-- For every grouping term that is not a name, not under {lit}`COLLATE` and not an integer
({name}`columnNumber`), the term resolves as an expression ({name}`resolveGroupExpressionTraced`).
For example {lit}`GROUP BY lower(a)`, {lit}`GROUP BY a+0` and {lit}`GROUP BY 1.0`. Proof sketch:
split on the form of the term; the hypotheses close the name, {lit}`COLLATE` and integer cases. -/
theorem resolveGroupTerm_expression (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes)
    (aliases : List (Option Identifier)) (outputs : List (Resolved.Output × String × Option Affinity))
    (collations : List Collation) (item : Nat) (term : Syntax.Expr)
    (notName : ∀ name quote, term ≠ .identifier name quote) (notCollate : ∀ operand name, term ≠ .collate operand name)
    (number : columnNumber term = none) :
    resolveGroupTerm dqs scope shapes aliases outputs collations item term =
      (resolveGroupExpressionTraced dqs scope shapes aliases item term).drop := by
  cases term <;> simp_all [resolveGroupTerm, resolveGroupTermTraced]

/-- For every grouping term that is an expression with no aggregate call, no subquery and no
result alias of {lit}`aliases`, the term resolves as a {lit}`WHERE` operand does
({name}`resolveOperand`), with the collation of the term, and an issue is moved to the term.
Proof sketch: the three conditions are false, so the traced form is the traced operand. -/
theorem resolveGroupExpression_operand (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes)
    (aliases : List (Option Identifier)) (item : Nat) (term : Syntax.Expr) (noAggregates : term.aggregateCalls = [])
    (noSubquery : term.hasSubquery = false) (noAlias : namesAlias scope (aliases.filterMap id) term = false) :
    (resolveGroupExpressionTraced dqs scope shapes aliases item term).drop =
      ((resolveOperand dqs scope shapes true term).map fun resolved => (resolved.1, term.collationIn scope)).mapError
        (ValueIssue.under [4, item]) := by
  simp only [resolveGroupExpressionTraced, noAggregates, noSubquery, noAlias, resolveOperand, List.isEmpty_nil,
    Bool.not_true, Bool.false_eq_true, ite_false, traced_drop]
  cases (resolveOperandTraced dqs scope shapes true term).drop <;> rfl

end Belay.Sqlite.Model
