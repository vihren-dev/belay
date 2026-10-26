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

/-- For every grouping term that is an expression under one {lit}`COLLATE`: if the term is a collated column
({name}`Syntax.Expr.collatedColumn`: an unqualified name that reads a column of the scope, or any qualified
name, which enters operand resolution even when its lookup fails), it resolves as its operand does, with
the collation of the term, and an issue is moved to the term; any other term is
{name}`RestrictionKind.groupByTerm`. Proof sketch: unfold the traced form and split on whether the term is a
collated column; the operand is the traced operand of the term. -/
@[traced_arms] theorem resolveGroupTerm_collate (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes)
    (aliases : List (Option Identifier)) (outputs : List (Resolved.Output × String × Option Affinity))
    (collations : List Collation) (item : Nat) (operand : Syntax.Expr) (name : Identifier) :
    resolveGroupTerm dqs scope shapes aliases outputs collations item (.collate operand name) =
      if (Syntax.Expr.collate operand name).collatedColumn scope then
        ((resolveOperand dqs scope shapes true (.collate operand name)).map fun resolved =>
          (resolved.1, (Syntax.Expr.collate operand name).collationIn scope)).mapError (ValueIssue.under [4, item])
      else .error (.restriction [4, item] .groupByTerm) := by
  simp only [resolveGroupTerm, resolveGroupTermTraced, resolveOperand]
  split
  · simp only [traced_drop]
    cases (resolveOperandTraced dqs scope shapes true (operand.collate name)).drop <;> rfl
  · simp [traced_drop]

end Belay.Sqlite.Model
