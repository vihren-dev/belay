import Belay.Sqlite.Model.Resolution.QueryExprs
import Belay.Sqlite.Model.Queries.Select.QueryTerms
import Belay.Sqlite.Model.Queries.Preparation.TracedList

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

mutual
/-- Whether an expression as written has a subquery: {lit}`EXISTS`, {lit}`IN (query)` or a scalar
subquery, anywhere in it. -/
def Syntax.Expr.hasSubquery : Syntax.Expr → Bool
  | .exists _ | .inQuery .. | .subquery _ => true
  | .compare _ left right | .and left right | .or left right | .arithmetic _ left right | .concatenate left right =>
    left.hasSubquery || right.hasSubquery
  | .not operand | .isNull operand _ | .negate operand | .positive operand | .cast operand _ | .collate operand _ =>
    operand.hasSubquery
  | .call _ arguments | .caseOf arguments _ => Syntax.Expr.hasSubqueryIn arguments
  | .inList operand values _ => operand.hasSubquery || Syntax.Expr.hasSubqueryIn values
  | .between operand low high _ => operand.hasSubquery || low.hasSubquery || high.hasSubquery
  | .null | .numeric _ | .string _ | .blob _ | .parameter _ | .currentTime _ | .identifier .. | .qualified ..
  | .callStar _ | .raise .. => false

/-- Whether some expression has a subquery ({name}`Syntax.Expr.hasSubquery`). -/
def Syntax.Expr.hasSubqueryIn : List Syntax.Expr → Bool
  | [] => false
  | expression :: rest => expression.hasSubquery || Syntax.Expr.hasSubqueryIn rest
end

/-- Resolve {lit}`GROUP BY` term {lit}`item` that is an expression (ADR 0030, D4), in a query whose
result columns have the aliases {lit}`aliases`: an aggregate anywhere in the term is SQLite's
{lit}`aggregate functions are not allowed in the GROUP BY clause`; a subquery is
{name}`RestrictionKind.groupByTerm`; a result alias inside the term is
{name}`RestrictionKind.aliasInExpression`; any other term resolves as a {lit}`WHERE` operand does,
with its collation ({lit}`Syntax.Expr.collationIn`). For example {lit}`GROUP BY lower(a)` resolves
to the call of {lit}`lower` on the column. -/
def resolveGroupExpressionTraced (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes)
    (aliases : List (Option Identifier)) (item : Nat) (term : Syntax.Expr) : Traced ValueIssue (Resolved.Expr × Collation) :=
  if !term.aggregateCalls.isEmpty then throw (.prepare .aggregateInGroupBy)
  else if term.hasSubquery then throw (.restriction [4, item] .groupByTerm)
  else if namesAlias scope (aliases.filterMap id) term then throw (aliasInExpression.under [4, item])
  else ((resolveOperandTraced dqs scope shapes true term).under [4, item]).map (·.1, term.collationIn scope)

/-- Resolve {lit}`GROUP BY` term {lit}`item` of a query whose result columns are {lit}`outputs`,
with aliases {lit}`aliases` and collations {lit}`collations` (ADR 0030, D4):
- a name is a column of the scope first and a result alias second; the occurrence of an alias is
  the result column that it names, and a name that is neither lists the aliases among its
  candidates;
- an integer ({name}`columnNumber`) names its result column, and one out of range is SQLite's
  {lit}`GROUP BY term out of range` error;
- the result column that a number or an alias names gives its expression and collation;
- a number or an alias under {lit}`COLLATE` names its result column in the same way, with the
  explicit collation, as SQLite reads the term without {lit}`COLLATE` (ADR 0030, D4 note); an
  unknown collation name there is {name}`RestrictionKind.unknownCollation`, as in any other
  expression;
- every other term is an expression ({name}`resolveGroupExpressionTraced`).

An aggregate, also inside the result column that a number or an alias names, is SQLite's
{lit}`aggregate functions are not allowed in the GROUP BY clause`. A result alias inside a larger
term is {name}`RestrictionKind.aliasInExpression`. A subquery is
{name}`RestrictionKind.groupByTerm`. -/
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
  let numbered := fun (number : Int) (collation : Option Collation) =>
    if 1 ≤ number ∧ number ≤ (outputs.length : Int) then
      Traced.lift ((grouped (number.toNat - 1)).map fun (key, own) => (key, collation.getD own))
    else throw (.prepare (.groupByOutOfRange (item + 1) outputs.length))
  match term with
    | .identifier name quote => match scope.resolveName name, aliasIndex aliases name with
      | .missing, some column => do
        Traced.record { aliasUseOccurrence name quote column with path := [4, item] }
        Traced.lift (grouped column)
      | .found .., _ | .missing, none | .ambiguous, _ =>
        operand (identifierTraced dqs scope name quote (aliasCandidates aliases))
    | .collate .. =>
      if term.collatedColumn scope then operand (resolveOperandTraced dqs scope shapes true term)
      else match columnNumber term.withoutCollate.1, term.withoutCollate.1 with
        | some number, _ => do
          unless term.withoutCollate.2 do throw (.restriction [4, item] .unknownCollation)
          numbered number (some (term.collationIn scope))
        | none, .identifier name quote => match scope.resolveName name, aliasIndex aliases name with
          | .missing, some column => do
            unless term.withoutCollate.2 do throw (.restriction [4, item] .unknownCollation)
            Traced.record { aliasUseOccurrence name quote column with path := [4, item] }
            Traced.lift ((grouped column).map fun (key, _) => (key, term.collationIn scope))
          | .found .., _ | .missing, none | .ambiguous, _ => resolveGroupExpressionTraced dqs scope shapes aliases item term
        | none, _ => resolveGroupExpressionTraced dqs scope shapes aliases item term
    | .null | .numeric _ | .string _ | .blob _ | .parameter _ | .currentTime _ | .qualified .. | .negate _
    | .positive _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. | .arithmetic ..
    | .cast .. | .exists _ | .inQuery .. | .subquery _ | .inList .. | .between .. | .caseOf .. | .concatenate ..
    | .raise .. => match columnNumber term with
      | some number => numbered number none
      | none => resolveGroupExpressionTraced dqs scope shapes aliases item term

/-- The resolved grouping term {lit}`item`: {name}`resolveGroupTermTraced` without its trace. -/
def resolveGroupTerm (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (aliases : List (Option Identifier))
    (outputs : List (Resolved.Output × String × Option Affinity)) (collations : List Collation) (item : Nat)
    (term : Syntax.Expr) : Except ValueIssue (Resolved.Expr × Collation) :=
  (resolveGroupTermTraced dqs scope shapes aliases outputs collations item term).drop

end Belay.Sqlite.Model
