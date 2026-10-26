import Belay.Sqlite.Model.Resolution.QueryExprs
import Belay.Sqlite.Model.Resolution.QueryTerms
import Belay.Sqlite.Model.Resolution.TracedList

set_option doc.verso true

/-! The aggregates of a query (ADR 0018, D3): the aggregate calls of its result columns,
{lit}`HAVING` and {lit}`ORDER BY`, which resolution lists so that an expression names one by its
index ({lit}`Resolved.Expr.aggregateValue`), and the resolution of one aggregate call. -/

namespace Belay.Sqlite.Model

mutual
/-- The aggregate calls of an expression as written ({name}`aggregateCall`), in written order,
without the calls inside their arguments, which are SQLite's {lit}`misuse of aggregate function`.
A subquery's expressions are not parts of the expression that names it. -/
def Syntax.Expr.aggregateCalls (expression : Syntax.Expr) : List Syntax.Expr :=
  if aggregateCall expression then [expression] else match expression with
  | .compare _ left right | .and left right | .or left right | .arithmetic _ left right | .concatenate left right =>
    left.aggregateCalls ++ right.aggregateCalls
  | .not operand | .isNull operand _ | .negate operand | .positive operand | .cast operand _ | .collate operand _
  | .inQuery operand .. => operand.aggregateCalls
  | .call _ arguments | .caseOf arguments _ => Syntax.Expr.aggregateCallsIn arguments
  | .inList operand values _ => operand.aggregateCalls ++ Syntax.Expr.aggregateCallsIn values
  | .between operand low high _ => operand.aggregateCalls ++ low.aggregateCalls ++ high.aggregateCalls
  | .null | .numeric _ | .string _ | .blob _ | .parameter _ | .currentTime _ | .identifier .. | .qualified ..
  | .callStar _ | .exists _ | .subquery _ | .raise .. => []

/-- The aggregate calls of each expression in order ({name}`Syntax.Expr.aggregateCalls`). -/
def Syntax.Expr.aggregateCallsIn : List Syntax.Expr → List Syntax.Expr
  | [] => []
  | expression :: rest => expression.aggregateCalls ++ Syntax.Expr.aggregateCallsIn rest
end

mutual
/-- The path of the first aggregate call that is the same as {lit}`target` in an expression, in the
layout of the paths of {name}`resolveOperandTraced`, in the order of
{name}`Syntax.Expr.aggregateCalls`; none when there is no such call. -/
def Syntax.Expr.callPath? (expression target : Syntax.Expr) : Option (List Nat) :=
  if aggregateCall expression then (if target.same expression then some [] else none) else match expression with
  | .compare _ left right | .arithmetic _ left right =>
    (left.callPath? target).map ([1] ++ ·) <|> (right.callPath? target).map ([2] ++ ·)
  | .and left right | .or left right | .concatenate left right =>
    (left.callPath? target).map ([0] ++ ·) <|> (right.callPath? target).map ([1] ++ ·)
  | .not operand | .isNull operand _ | .negate operand | .positive operand | .cast operand _ | .collate operand _
  | .inQuery operand .. => (operand.callPath? target).map ([0] ++ ·)
  | .call _ arguments => Syntax.Expr.callPathIn target [1] 0 arguments
  | .caseOf arguments _ => Syntax.Expr.callPathIn target [0] 0 arguments
  | .inList operand values _ =>
    (operand.callPath? target).map ([0] ++ ·) <|> Syntax.Expr.callPathIn target [1] 0 values
  | .between operand low high _ =>
    (operand.callPath? target).map ([0] ++ ·) <|> (low.callPath? target).map ([1] ++ ·)
      <|> (high.callPath? target).map ([2] ++ ·)
  | .null | .numeric _ | .string _ | .blob _ | .parameter _ | .currentTime _ | .identifier .. | .qualified ..
  | .callStar _ | .exists _ | .subquery _ | .raise .. => none

/-- The path of the first aggregate call that is the same as {lit}`target` in a list of expressions,
as {lit}`prefix_` followed by the position, counted from {lit}`index`. -/
def Syntax.Expr.callPathIn (target : Syntax.Expr) (prefix_ : List Nat) (index : Nat) : List Syntax.Expr → Option (List Nat)
  | [] => none
  | expression :: rest =>
    (expression.callPath? target).map (prefix_ ++ [index] ++ ·) <|> Syntax.Expr.callPathIn target prefix_ (index + 1) rest
end

/-- Resolve one aggregate call ({name}`aggregateCall`): {lit}`count(*)` and {lit}`count()` count the
rows, an aggregate of one or two operands resolves them with aggregates as misuse. An operand
that reads a cell of a query around the current one is {name}`RestrictionKind.outerAggregate`,
and a JSON aggregate over a value whose JSON subtype the model does not describe is
{name}`RestrictionKind.jsonSubtype`. The issue and the occurrences of operand {lit}`k` are at {lit}`[1, k]`. -/
def resolveAggregateCallTraced (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) :
    Syntax.Expr → Traced ValueIssue Resolved.Aggregate
  | .callStar _ | .call _ [] => pure .countRows
  | .call name [operand] => match aggregateNamed name with
    | some aggregate => do
      let (resolved, _) ← (resolveOperandTraced dqs scope shapes true operand).under [1, 0]
      if resolved.readsUnder shapes shapes.outer then throw (.restriction [] .outerAggregate)
      if (aggregate resolved).writesJson && resolved.subtypeUndescribed then throw (.restriction [1, 0] .jsonSubtype)
      pure ((aggregate resolved).withCollation (operand.collationIn scope))
    | none => throw (.restriction [] .aggregateInExpression)
  | .call name [first, second] => match pairAggregateNamed name with
    | some aggregate => do
      let (label, _) ← (resolveOperandTraced dqs scope shapes true first).under [1, 0]
      let (operand, _) ← (resolveOperandTraced dqs scope shapes true second).under [1, 1]
      if (Resolved.Expr.coalesce label operand).readsUnder shapes shapes.outer then
        throw (.restriction [] .outerAggregate)
      if operand.subtypeUndescribed then throw (.restriction [1, 1] .jsonSubtype)
      pure (aggregate label operand)
    | none => throw (.restriction [] .aggregateInExpression)
  | .call _ (_ :: _ :: _ :: _) | .null | .numeric _ | .string _ | .blob _ | .parameter _ | .currentTime _ | .identifier ..
  | .qualified .. | .negate _ | .positive _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .arithmetic ..
  | .cast .. | .collate .. | .exists _ | .inQuery .. | .subquery _ | .inList .. | .between .. | .caseOf ..
  | .concatenate .. | .raise .. => throw (.restriction [] .aggregateInExpression)

/-- The aggregate that one call stands for: {name}`resolveAggregateCallTraced` without its trace. -/
def resolveAggregateCall (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (call : Syntax.Expr) :
    Except ValueIssue Resolved.Aggregate :=
  (resolveAggregateCallTraced dqs scope shapes call).drop

/-- Resolve {lit}`GROUP BY` term {lit}`item` of a query whose result columns are {lit}`outputs`,
with aliases {lit}`aliases` and collations {lit}`collations`: a column name, also under one
{lit}`COLLATE`, or a qualified name, with its collation; a result column number or alias, with
the column's collation; a parameter, as a constant value that names no result column (ADR 0019,
D1); an aggregate, also inside the result column that a number or an alias
names, is SQLite's {lit}`aggregate functions are not allowed in the GROUP BY clause`; any other term is {name}`RestrictionKind.groupByTerm`.
A name is a column of the scope first and a result alias second; the occurrence of an alias is the
result column that it names, and a name that is neither lists the aliases among its candidates. -/
def resolveGroupTermTraced (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (aliases : List (Option Identifier))
    (outputs : List (Resolved.Output × String × Option Affinity)) (collations : List Collation) (item : Nat)
    (term : Syntax.Expr) : Traced ValueIssue (Resolved.Expr × Collation) :=
  let grouped := fun (column : Nat) => match outputs[column]? with
    | some (.scalar expression, _) =>
      if expression.any (· matches .aggregateValue _) then .error (.prepare .aggregateInGroupBy)
      else .ok (expression, collations.getD column .binary)
    | some (.aggregate _, _) | none => .error (.prepare .aggregateInGroupBy)
  let operand := fun (resolved : Traced ValueIssue Operand) =>
    (resolved.under [4, item]).map (·.1, term.collationIn scope)
  match term with
    | .identifier name quote => match scope.resolveName name, aliasIndex aliases name with
      | .missing, some column => do
        Traced.record { aliasUseOccurrence name quote column with path := [4, item] }
        Traced.lift (grouped column)
      | .found .., _ | .missing, none | .ambiguous, _ =>
        operand (identifierTraced dqs scope name quote (aliasCandidates aliases))
    | .callStar name | .call name [] | .call name [_] =>
      throw (if aggregateCall term then .prepare .aggregateInGroupBy else (callIssue name).under [4, item])
    | .numeric _ | .negate _ => match namedResult aliases term with
      | some (.ok column) => Traced.lift (grouped column)
      | some (.error ()) => throw (.prepare (.groupByOutOfRange (item + 1) outputs.length))
      | none => throw (.restriction [4, item] .groupByTerm)
    | .qualified .. | .parameter _ => operand (resolveOperandTraced dqs scope shapes true term)
    | .collate .. =>
      if term.collatedColumn scope then operand (resolveOperandTraced dqs scope shapes true term)
      else throw (.restriction [4, item] .groupByTerm)
    | .call _ (_ :: _ :: _) | .null | .string _ | .blob _ | .currentTime _ | .positive _ | .compare ..
    | .and .. | .or .. | .not _ | .isNull .. | .arithmetic .. | .cast .. | .exists _ | .inQuery .. | .subquery _
    | .inList .. | .between .. | .caseOf .. | .concatenate .. | .raise .. =>
      throw (.restriction [4, item] .groupByTerm)

/-- The resolved grouping term {lit}`item`: {name}`resolveGroupTermTraced` without its trace. -/
def resolveGroupTerm (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (aliases : List (Option Identifier))
    (outputs : List (Resolved.Output × String × Option Affinity)) (collations : List Collation) (item : Nat)
    (term : Syntax.Expr) : Except ValueIssue (Resolved.Expr × Collation) :=
  (resolveGroupTermTraced dqs scope shapes aliases outputs collations item term).drop

end Belay.Sqlite.Model
