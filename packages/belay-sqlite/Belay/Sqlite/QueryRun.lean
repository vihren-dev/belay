import Belay.Sqlite.QueryEval
import Belay.Sqlite.Resolution.ExprAny

set_option doc.verso true

/-! A query over its source rows: its result rows, whether SQLite stops it with
{lit}`integer overflow`, and whether a JSON function of it fails (ADR 0013, D2). SQLite
does not evaluate a row that {lit}`WHERE`, {lit}`LIMIT` or {lit}`OFFSET` leaves out, and
evaluates a constant {lit}`WHERE` term once before it reads the rows; the fault of a query
follows these rules from the faults of its expressions ({lit}`Expr.evaluate`). -/

namespace Belay.Sqlite.Resolved

/-- Whether some JSON call of one of the expressions may fail over one of the rows. -/
def anyMayFail (clock : Int) (rows : List (List Value)) (expressions : List Expr) : Bool :=
  rows.any fun row => expressions.any (·.mayFailOn clock row)

/-- The scalar result columns of a query. -/
def Output.scalars : Output → List Expr
  | .scalar term => [term]
  | .aggregate _ => []

/-- The expressions that an aggregate result column evaluates over each row; none for a
scalar or {lit}`COUNT(*)`. A value of {lit}`json_group_array` or {lit}`json_group_object` is
written as {lit}`json_array` writes it, so it is the call {lit}`json_array(value)`, whose fault
is that of writing the value (a BLOB is JSONB, which the model does not describe). -/
def Output.operands : Output → List Expr
  | .scalar _ | .aggregate .countRows => []
  | .aggregate (.count operand) | .aggregate (.min operand _) | .aggregate (.max operand _)
  | .aggregate (.sum operand) | .aggregate (.avg operand) => [operand]
  | .aggregate (.jsonGroupArray operand) => [.json .array (.cons operand .nil)]
  | .aggregate (.jsonGroupObject label value) => [label, .json .array (.cons value .nil)]

/-- The expressions of an {lit}`ORDER BY` key: an expression, or none for a result
column, which the result columns already cover. -/
def SortKey.expressions : SortKey → List Expr
  | .expression term => [term]
  | .output _ => []

/-- The expressions that a query evaluates over each row that passes {lit}`WHERE`: the
result columns, the aggregate operands, and the {lit}`GROUP BY` and {lit}`ORDER BY`
keys. -/
def Query.keptExpressions (query : Query) : List Expr :=
  query.columns.flatMap Output.scalars ++ query.columns.flatMap Output.operands ++ query.groupBy.map Prod.fst ++
    query.orderBy.flatMap (·.key.expressions)

/-- The expressions of a source of {lit}`FROM`: the arguments of a {lit}`json_each` source,
and the {lit}`ON` condition. -/
def QuerySource.expressions (join : QuerySource) : List Expr :=
  (match join.source with
    | .each json path => json :: path.toList
    | .table _ | .subquery => []) ++ join.condition.toList

/-- Whether the query joins sources: it has more than one, or a {lit}`json_each` source. -/
def Query.joined (query : Query) : Bool :=
  query.sources.length > 1 || query.sources.any (·.source.isEach)

/-- Every expression of a query: {lit}`WHERE`, the expressions of its sources
({name}`QuerySource.expressions`) and {name}`Query.keptExpressions`. -/
def Query.expressions (query : Query) : List Expr :=
  query.filter.toList ++ query.sources.flatMap QuerySource.expressions ++ query.keptExpressions

/-- Whether some fallible call of the query ({name}`Expr.isFallibleCall`: a JSON call or a
function that can fail) may fail over its source rows. The row with no cells, {lit}`[]`,
reads NULL in every column. A query that joins sources ({name}`Query.joined`) and has a
fallible call may fail, because SQLite may evaluate a condition over a part of
a joined row. The failures of {lit}`json_each` itself are not JSON calls of an
expression; {lit}`Query.source` gives their fault. Otherwise:
* {lit}`WHERE` over every source row and over {lit}`[]`, because SQLite evaluates a
  constant term once before it reads the rows (checked: {lit}`DELETE FROM t WHERE
  json_extract('x', '$')` fails over an empty table);
* the result columns, aggregate operands, and {lit}`GROUP BY` and {lit}`ORDER BY` keys
  over every row that passes {lit}`WHERE`, and in an aggregate query also over {lit}`[]`,
  because SQLite evaluates the result row of an empty group over NULL cells. -/
def Query.mayFail (clock : Int) (query : Query) (rows : List (List Value)) : Bool :=
  if query.joined then query.expressions.any (·.any Expr.isFallibleCall)
  else
    let kept := filtered clock query rows ++ if query.aggregate then [[]] else []
    anyMayFail clock ([] :: rows) query.filter.toList ||
    anyMayFail clock kept query.keptExpressions

/-- For every clock value, row and expression without a fallible call at any depth
({name}`Expr.isFallibleCall`, {name}`Expr.any`), the fault of the expression over the row at
the clock value is {lean}`Fault.none`. Proof sketch: induction over the mutual expression and argument types;
every node joins or softens the faults of its parts, which are all {lean}`Fault.none`, and a
scalar function that cannot fail gives a value ({name}`ScalarFunction.apply_ok`). -/
theorem Expr.fault_of_plain (clock : Int) (row : List Value) (expression : Expr)
    (plain : expression.any Expr.isFallibleCall = false) : (expression.evaluate clock row).2 = .none := by
  induction expression using Expr.rec
    (motive_2 := fun arguments => arguments.any Expr.isFallibleCall = false → (arguments.evaluate clock row).2 = .none) <;>
    simp_all [Expr.any, Arguments.any, Expr.isFallibleCall, Expr.evaluate, Arguments.evaluate, Fault.join, Fault.soften]
  case scalar function arguments ih =>
    have safe := plain.1
    have quiet := ih
    cases function
    case iif =>
      cases arguments with
      | nil => simp [Expr.evaluate]
      | cons head tail =>
        simp only [Arguments.evaluate] at quiet
        simp only [Expr.evaluate]
        rcases first : (head.evaluate clock row).2 with _ | _ | _ <;>
          rcases later : (tail.evaluate clock row).2 with _ | _ | _ <;>
          simp_all [Fault.join, Fault.soften]
    all_goals
      obtain ⟨value, ok⟩ := ScalarFunction.apply_ok _ (arguments.evaluate clock row).1 safe
      simp [Expr.evaluate, ok, quiet, Fault.join, Fault.ofFunction]

/-- For every clock value, all rows and every query without a fallible call in any of its
expressions ({name}`Query.expressions`), no call of the query may fail over the rows at
the clock value ({name}`Query.mayFail`). Proof sketch: each expression that {name}`Query.mayFail`
evaluates is one of {name}`Query.expressions`, so {name}`Expr.fault_of_plain` applies to
it. -/
theorem Query.mayFail_of_plain (clock : Int) (query : Query) (rows : List (List Value))
    (plain : query.expressions.all (!·.any Expr.isFallibleCall) = true) : query.mayFail clock rows = false := by
  simp only [List.all_eq_true, Bool.not_eq_true'] at plain
  unfold Query.mayFail anyMayFail
  split
  · simpa using plain
  · simp only [Bool.or_eq_false_iff, List.any_eq_false, Bool.not_eq_true]
    refine ⟨fun _ _ expression member => ?_, fun _ _ expression member => ?_⟩ <;>
      simp [Expr.mayFailOn, Expr.fault_of_plain clock _ _ (plain expression (by simp_all [Query.expressions]))]

/-- Whether SQLite certainly reports a JSON failure of the query over its source rows,
which the model describes only for a query without {lit}`FROM` (no source) and without {lit}`LIMIT 0` (checked natively): its {lit}`WHERE`
fails on the one row; or the row passes {lit}`WHERE` and an aggregate operand fails, also
with {lit}`OFFSET`; or the row passes, no {lit}`OFFSET` skips it, and a scalar result column
fails. -/
def Query.mustFail (clock : Int) (query : Query) (rows : List (List Value)) : Bool :=
  query.sources.isEmpty && query.limit != some 0 && rows.any fun row =>
    query.filter.any (·.mustFailOn clock row) ||
    (query.filter.all (fun condition => truthy (condition.eval clock row)) &&
      ((query.columns.flatMap Output.operands).any (·.mustFailOn clock row) ||
        (query.offset == 0 && (query.columns.flatMap Output.scalars).any (·.mustFailOn clock row))))

/-- Whether a query fails over its source rows, so that SQLite stops the statement with the
{lit}`integer overflow` error: an aggregate query without {lit}`LIMIT 0` in which an
aggregate of a result column fails ({name}`Aggregate.fails`) for some group. With
{lit}`LIMIT 0`, SQLite skips the evaluation and returns no rows. -/
def Query.fails (clock : Int) (query : Query) (rows : List (List Value)) : Bool :=
  query.aggregate && query.limit != some 0 && (queryGroups clock query (filtered clock query rows)).any fun group =>
    query.columns.any fun
      | .aggregate aggregate => aggregate.fails clock group
      | .scalar _ => false

/-- A query run over its source rows: the result rows, the fault of its JSON calls, and
whether an aggregate overflows. -/
structure QueryRun where
  /-- The result rows ({name}`Query.results`). -/
  rows : List (List Value)
  /-- {lean}`Fault.must` when SQLite certainly reports a JSON failure ({name}`Query.mustFail`),
  else {lean}`Fault.may` when a JSON call may fail ({name}`Query.mayFail`), else
  {lean}`Fault.none`. -/
  fault : Fault
  /-- Whether SQLite stops the query with {lit}`integer overflow` ({name}`Query.fails`). -/
  overflow : Bool

/-- Run the query over its source rows ({lit}`Query.source`): its result rows, its fault and
its overflow. -/
def Query.run (clock : Int) (query : Query) (rows : List (List Value)) : QueryRun where
  rows := query.results clock rows
  fault := if query.mustFail clock rows then .must else if query.mayFail clock rows then .may else .none
  overflow := query.fails clock rows

end Belay.Sqlite.Resolved
