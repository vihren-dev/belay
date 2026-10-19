import Belay.Sqlite.Declarations
import Belay.Sqlite.Operators
import Belay.Sqlite.Comparison
import Belay.Sqlite.Resolution.JsonFunction
import Belay.Sqlite.Resolution.DateFunction
import Belay.Sqlite.ClockText

set_option doc.verso true

/-! The resolved form of a single-table query of ADR 0012, slice 1: what
{lit}`resolve` gives for a {lit}`SELECT` and what the Queries level evaluates.
Names are already table positions, and the affinity rules of a comparison are
already applied to its literal operands, so evaluation needs no catalog. -/

namespace Belay.Sqlite.Resolved

mutual
/-- A scalar expression over one row of the source table. Its value is a stored
value; the comparisons and logical operators give the integers 1 and 0, or NULL. -/
inductive Expr where
  /-- The value of the column at a table position. -/
  | column (position : Nat)
  /-- A literal value, after the affinity of a comparison is applied to it. -/
  | literal (value : Value)
  /-- A comparison of two operands, with the affinity that SQLite applies to them
  ({lit}`comparisonAffinity`; none applies no conversion) and the collation that resolution
  chose for it (ADR 0014, D3), {lit}`BINARY` when none is written. -/
  | compare (operator : Comparison) (affinity : Option Affinity) (left right : Expr)
      (collation : Collation := .binary)
  /-- {lit}`AND`, with SQLite's three-valued logic. -/
  | and (left right : Expr)
  /-- {lit}`OR`, with SQLite's three-valued logic. -/
  | or (left right : Expr)
  /-- {lit}`NOT`, with SQLite's three-valued logic. -/
  | not (operand : Expr)
  /-- {lit}`IS NULL`, or {lit}`IS NOT NULL` when {lit}`negated` is true. -/
  | isNull (operand : Expr) (negated : Bool)
  /-- An arithmetic operator between two operands. -/
  | arithmetic (operator : ArithmeticOperator) (left right : Expr)
  /-- {lit}`CAST` to the affinity of the written type name. -/
  | cast (affinity : Affinity) (operand : Expr)
  /-- {lit}`COALESCE`: the first operand when it is not NULL, else the second. -/
  | coalesce (first rest : Expr)
  /-- A call of a JSON function with its arguments in written order. -/
  | json (function : JsonFunction) (arguments : Arguments)
  /-- {lit}`CURRENT_TIME`, {lit}`CURRENT_DATE` or {lit}`CURRENT_TIMESTAMP`: the statement's clock
  value as text, which evaluation computes from the clock value it is given. -/
  | now (keyword : TimeKeyword)
  /-- A call of a date and time function with its arguments in written order; {lit}`now`
  and a call without a time value read the clock value that evaluation is given. -/
  | date (function : DateFunction) (arguments : Arguments)
  deriving Repr, DecidableEq

/-- The arguments of a call in written order, as a list that is mutual with
{lit}`Expr`, so equality stays derivable and recursion stays structural. -/
inductive Arguments where
  /-- No more arguments. -/
  | nil
  /-- An argument and the arguments after it. -/
  | cons (head : Expr) (tail : Arguments)
  deriving Repr, DecidableEq
end

/-- An aggregate function of slice 1, over the rows of one group. -/
inductive Aggregate where
  /-- {lit}`COUNT(*)`: the number of rows. -/
  | countRows
  /-- {lit}`COUNT(x)`: the number of rows where the operand is not NULL. -/
  | count (operand : Expr)
  /-- {lit}`MIN(x)`: the least operand value that is not NULL under the operand's collation,
  or NULL. -/
  | min (operand : Expr) (collation : Collation := .binary)
  /-- {lit}`MAX(x)`: the greatest operand value that is not NULL under the operand's
  collation, or NULL. -/
  | max (operand : Expr) (collation : Collation := .binary)
  /-- {lit}`SUM(x)`: the sum of the operand values that are not NULL, by
  {lit}`SumState.sumValue`; it fails on an integer overflow. -/
  | sum (operand : Expr)
  /-- {lit}`AVG(x)`: the average of the operand values that are not NULL, by
  {lit}`SumState.averageValue`. -/
  | avg (operand : Expr)
  deriving Repr, DecidableEq

/-- Whether an aggregate can fail while the statement runs: {lit}`SUM`, on an integer
overflow. -/
def Aggregate.canFail : Aggregate → Bool
  | .sum _ => true
  | .countRows | .count _ | .min .. | .max .. | .avg _ => false

/-- One result column: an expression over a row, or, in an aggregate query, an
aggregate over a group or an expression over the group's first row, which
{lit}`resolve` admits only when the expression uses only grouping terms. -/
inductive Output where
  /-- An expression over the row, or over the first row of a group. -/
  | scalar (expression : Expr)
  /-- An aggregate over the rows of a group. -/
  | aggregate (aggregate : Aggregate)
  deriving Repr, DecidableEq

/-- Whether a result column can fail while the statement runs: an aggregate that
{name}`Aggregate.canFail`. -/
def Output.canFail : Output → Bool
  | .aggregate function => function.canFail
  | .scalar _ => false

/-- The value that one {lit}`ORDER BY` term sorts by: an expression over the source
row (only in a query that is not an aggregate query), or a result column. -/
inductive SortKey where
  /-- An expression over the source row. -/
  | expression (expression : Expr)
  /-- The result column at a zero-based index. -/
  | output (index : Nat)
  deriving Repr, DecidableEq

/-- One {lit}`ORDER BY` term: the value it sorts by, whether it is {lit}`DESC`, and the
collation of its expression ({lit}`BINARY` when none applies). -/
structure SortTerm where
  /-- The value the term sorts by. -/
  key : SortKey
  /-- Whether the term is {lit}`DESC`. -/
  descending : Bool := false
  /-- The collation of the term's expression. -/
  collation : Collation := .binary
  deriving Repr, DecidableEq

/-- The kind of a resolved join: inner, or left, right or full outer. -/
inductive JoinKind where
  /-- An inner join: the rows of the product for which the condition is true. -/
  | inner
  /-- A left outer join: the inner join, and each left row that no right row matches,
  with NULL in every right column. -/
  | left
  /-- A right outer join: the inner join, and each right row that no row of the left
  input matches, with NULL in every column of the left input. -/
  | right
  /-- A full outer join: the inner join and the added rows of both a left and a right
  join. -/
  | full
  deriving Repr, DecidableEq

/-- A source of a {lit}`FROM` clause (ADR 0013, D5): a table, a {lit}`json_each(json [, path])`
call whose arguments read the joined row before it, or a subquery. -/
inductive Source where
  /-- The table at the catalog position, with its rows in rowid order. -/
  | table (position : Nat)
  /-- {lit}`json_each` with its JSON argument and optional path, over the row before it
  (ADR 0012, amendment 5, slice 6d). -/
  | each (json : Expr) (path : Option Expr)
  /-- A subquery. Resolution does not give it yet (ADR 0013, amendment 2); its payload
  comes with the subquery ADR, and execution treats it as unmodeled. -/
  | subquery
  deriving Repr, DecidableEq

/-- Whether the source is {lit}`json_each`. -/
def Source.isEach : Source → Bool
  | .each .. => true
  | .table _ | .subquery => false

/-- One source of {lit}`FROM` in written order: how it joins the row so far, the source,
and its {lit}`ON` condition over the row so far and its cells; {lean}`(none : Option Expr)`
for no condition. The first source is an inner join without a condition. -/
structure QuerySource where
  /-- The kind of the join with the sources before it. -/
  kind : JoinKind
  /-- The source. -/
  source : Source
  /-- The {lit}`ON` condition, over the cells of the sources up to this one. -/
  condition : Option Expr
  deriving Repr, DecidableEq

/-- The first source of a {lit}`FROM`: the table at the catalog position, as an inner join
without a condition. -/
def QuerySource.first (position : Nat) : QuerySource := { kind := .inner, source := .table position, condition := none }

/-- A resolved {lit}`SELECT`: its sources, the {lit}`WHERE` condition, whether it is an
aggregate query with its grouping terms, the result columns with their names, the
{lit}`ORDER BY` terms with a flag for {lit}`DESC`, and the window. Use
{lean}`(none : Option Nat)` for no {lit}`LIMIT`. -/
structure Query where
  /-- The sources of {lit}`FROM` in written order; empty for a {lit}`SELECT` without
  {lit}`FROM`, whose source is one row with no columns. An expression names a cell by its
  position in the concatenated row of all sources. -/
  sources : List QuerySource
  /-- The {lit}`WHERE` condition, or {lean}`(none : Option Expr)` for every row. -/
  filter : Option Expr
  /-- Whether the query is an aggregate query: it has {lit}`GROUP BY` or an aggregate. -/
  aggregate : Bool
  /-- The {lit}`GROUP BY` terms, each with the collation that decides when two values are one
  group; empty for one group of all rows. -/
  groupBy : List (Expr × Collation)
  /-- The result columns, in order. -/
  columns : List Output
  /-- The name of each result column. -/
  names : List String
  /-- The {lit}`ORDER BY` terms. -/
  orderBy : List SortTerm
  /-- The number of rows that {lit}`OFFSET` skips; zero without {lit}`OFFSET`. -/
  offset : Nat
  /-- The {lit}`LIMIT`, or {lean}`(none : Option Nat)` for no limit. -/
  limit : Option Nat
  deriving Repr, DecidableEq

end Belay.Sqlite.Resolved
