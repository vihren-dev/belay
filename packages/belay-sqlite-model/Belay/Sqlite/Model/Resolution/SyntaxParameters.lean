import Belay.Sqlite.Model.Resolution.Syntax

set_option doc.verso true

/-! Whether syntax as written has a parameter (ADR 0019, D1). SQLite refuses a parameter in a
{lit}`CHECK` constraint, a generated column, an index expression, the {lit}`WHERE` of a partial
index and anywhere in a trigger, so resolution reads it from the syntax before it resolves
names. The subqueries of a statement are in its list of subqueries, so each test reads them
there. -/

namespace Belay.Sqlite.Model.Syntax

mutual
/-- Whether an expression has a parameter anywhere in it. -/
def Expr.hasParameter : Expr → Bool
  | .parameter _ => true
  | .compare _ left right | .and left right | .or left right | .arithmetic _ left right | .concatenate left right =>
    left.hasParameter || right.hasParameter
  | .not operand | .isNull operand _ | .negate operand | .positive operand | .cast operand _
  | .collate operand _ | .inQuery operand .. => operand.hasParameter
  | .call _ arguments | .caseOf arguments _ => Expr.anyParameter arguments
  | .inList operand values _ => operand.hasParameter || Expr.anyParameter values
  | .between operand low high _ => operand.hasParameter || low.hasParameter || high.hasParameter
  | .raise _ (some message) => message.hasParameter
  | .raise _ none | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .identifier .. | .qualified ..
  | .callStar _ | .exists _ | .subquery _ => false

/-- Whether some expression of the list has a parameter ({name}`Expr.hasParameter`). -/
def Expr.anyParameter : List Expr → Bool
  | [] => false
  | expression :: rest => expression.hasParameter || Expr.anyParameter rest
end

/-- Whether an optional expression has a parameter. -/
def Expr.optionParameter : Option Expr → Bool
  | some expression => expression.hasParameter
  | none => false

/-- Whether a result column has a parameter; {lit}`*` and {lit}`source.*` have none. -/
def ResultColumn.hasParameter : ResultColumn → Bool
  | .expression value _ _ => value.hasParameter
  | .star | .sourceStar _ => false

/-- Whether the arguments of a table-valued function have a parameter. -/
def TableReference.hasParameter (reference : TableReference) : Bool :=
  (reference.arguments.map Expr.anyParameter).getD false

/-- Whether a join has a parameter, in its table or its {lit}`ON` condition. -/
def Join.hasParameter (join : Join) : Bool :=
  join.source.hasParameter || Expr.optionParameter join.condition

/-- Whether the clauses of a query have a parameter: its result columns, sources, joins,
{lit}`WHERE`, {lit}`GROUP BY`, {lit}`HAVING`, {lit}`ORDER BY`, {lit}`LIMIT` and {lit}`OFFSET`. -/
def queryHasParameter (columns : List ResultColumn) (source : Option TableReference) (joins : List Join)
    (filter : Option Expr) (groupBy : List Expr) (having : Option Expr) (orderBy : List OrderTerm)
    (limit offset : Option Expr) : Bool :=
  columns.any ResultColumn.hasParameter || (source.map TableReference.hasParameter).getD false ||
    joins.any Join.hasParameter || Expr.optionParameter filter || Expr.anyParameter groupBy ||
    Expr.optionParameter having || Expr.anyParameter (orderBy.map (·.expression)) ||
    Expr.optionParameter limit || Expr.optionParameter offset

/-- Whether a subquery has a parameter in its clauses ({name}`queryHasParameter`). -/
def Subquery.hasParameter (query : Subquery) : Bool :=
  queryHasParameter query.columns query.source query.joins query.filter query.groupBy query.having query.orderBy
    query.limit query.offset

/-- Whether assignments of {lit}`SET` have a parameter in their values. -/
def assignmentsHaveParameter (assignments : List (Identifier × Expr)) : Bool :=
  Expr.anyParameter (assignments.map (·.2))

/-- Whether an {lit}`ON CONFLICT` clause has a parameter in its {lit}`DO UPDATE`. -/
def ConflictClause.hasParameter (clause : ConflictClause) : Bool :=
  match clause.action with
  | .update assignments filter => assignmentsHaveParameter assignments || Expr.optionParameter filter
  | .nothing => false

/-- Whether a statement of a trigger's body has a parameter, also in its subqueries. -/
def BodyStatement.hasParameter : BodyStatement → Bool
  | .insert _ _ rows conflicts _ subqueries =>
    rows.any Expr.anyParameter || conflicts.any ConflictClause.hasParameter || subqueries.any Subquery.hasParameter
  | .update _ assignments filter subqueries =>
    assignmentsHaveParameter assignments || Expr.optionParameter filter || subqueries.any Subquery.hasParameter
  | .delete _ filter subqueries => Expr.optionParameter filter || subqueries.any Subquery.hasParameter
  | .select columns source joins filter groupBy orderBy limit offset subqueries having _ =>
    queryHasParameter columns source joins filter groupBy having orderBy limit offset ||
      subqueries.any Subquery.hasParameter

end Belay.Sqlite.Model.Syntax
