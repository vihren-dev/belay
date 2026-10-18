import Belay.Sqlite.Resolution.Writes
import Belay.Sqlite.Resolution.JoinUsing

set_option doc.verso true

/-! Resolution of the {lit}`FROM` of a {lit}`SELECT` (ADR 0012, amendment 2): the tables
and their names, the joins, and their {lit}`ON` conditions. The paths follow
{lit}`Syntax.Statement.select`: child 1 is the first table and child 2 the joins; in a
join, child 0 is its operator, child 1 its table, child 2 its {lit}`ON` condition and
child 3 its {lit}`USING` list. -/

namespace Belay.Sqlite

mutual
/-- Whether every column that the expression reads has a position below the bound: the
expression reads only the tables whose cells come before it in the joined row. -/
def Resolved.Expr.readsBelow (bound : Nat) : Resolved.Expr → Bool
  | .column position => position < bound
  | .literal _ | .now _ => true
  | .compare _ _ left right | .and left right | .or left right | .arithmetic _ left right | .coalesce left right =>
    left.readsBelow bound && right.readsBelow bound
  | .not operand | .isNull operand _ | .cast _ operand => operand.readsBelow bound
  | .json _ arguments | .date _ arguments _ => arguments.readsBelow bound

/-- Whether every argument reads only columns below the bound. -/
def Resolved.Arguments.readsBelow (bound : Nat) : Resolved.Arguments → Bool
  | .nil => true
  | .cons head tail => head.readsBelow bound && tail.readsBelow bound
end

/-- The columns of {lit}`source.*` ({name}`Scope.starColumns?`) with their expansions
({name}`Scope.starOperand`) and their names, or SQLite's {lit}`no such table: source` when no source has the name. -/
def sourceStarColumns (scope : Scope) (source : String) : Except ValueIssue (List (Resolved.Expr × String)) :=
  match scope.starColumns? source with
  | some columns => columns.mapM fun (position, column) => (·.1, column.name) <$> scope.starOperand position column
  | none => .error (.prepare (.noSuchSource source))

/-- The number of tables in a join that SQLite accepts ({lit}`SQLITE_MAX_SRCLIST`). -/
def maximumJoinTables : Nat := 64

/-- The source of one table reference at {lit}`path`: the table's catalog position and the
source with its name (the alias, else the table name as declared, as SQLite names it in
messages). A missing table is SQLite's
{lit}`no such table: %s`; one of SQLite's own tables is a model restriction, as in a
query of one table. -/
def resolveTableReference (catalog : Catalog) (path : List Nat) (reference : Syntax.TableReference) :
    Except ValueIssue (Nat × ScopeSource) :=
  match catalog.findTable reference.table with
  | some (position, table) =>
    let declared := (catalog[position]?.map (·.name)).getD reference.table
    .ok (position, { name := reference.alias.getD declared, columns := table.columns })
  | none =>
    if reservedName reference.table then .error (.restriction path .systemTable)
    else .error (.prepare (.noSuchTable reference.table))

/-- The flags that the keywords of a join operator set, as SQLite's {lit}`sqlite3JoinType`
gives them: {lit}`NATURAL`, {lit}`LEFT`, {lit}`RIGHT`, {lit}`OUTER` and {lit}`INNER`
({lit}`CROSS` is an inner join), and whether a word is none of these. -/
structure JoinFlags where
  /-- {lit}`NATURAL`. -/
  natural : Bool := false
  /-- {lit}`LEFT` or {lit}`FULL`. -/
  left : Bool := false
  /-- {lit}`RIGHT` or {lit}`FULL`. -/
  right : Bool := false
  /-- {lit}`OUTER`, {lit}`LEFT`, {lit}`RIGHT` or {lit}`FULL`. -/
  outer : Bool := false
  /-- {lit}`INNER` or {lit}`CROSS`. -/
  inner : Bool := false
  /-- A word that is not a join keyword. -/
  error : Bool := false

/-- The flags after one more keyword, compared without ASCII case. -/
def JoinFlags.add (flags : JoinFlags) (word : String) : JoinFlags :=
  match normalizeIdentifier word with
  | "natural" => { flags with natural := true }
  | "left" => { flags with left := true, outer := true }
  | "outer" => { flags with outer := true }
  | "right" => { flags with right := true, outer := true }
  | "full" => { flags with left := true, right := true, outer := true }
  | "inner" | "cross" => { flags with inner := true }
  | _ => { flags with error := true }

/-- The kind of a join operator and whether it has {lit}`NATURAL`, from its keywords as
written, as SQLite's {lit}`sqlite3JoinType` reads them: the words in any order, also
repeated, so {lean}`joinOperator ["OUTER", "LEFT"]` is a left join without {lit}`NATURAL`
(checked natively). None for the forms SQLite refuses with {lit}`unknown join type`: a word
that is not a join keyword, {lit}`INNER` or {lit}`CROSS` with {lit}`OUTER`, and {lit}`OUTER`
alone. -/
def joinOperator (words : List String) : Option (Resolved.JoinKind × Bool) :=
  let flags := words.foldl JoinFlags.add {}
  if flags.error || (flags.inner && flags.outer) || (flags.outer && !flags.left && !flags.right) then none
  else
    let kind : Resolved.JoinKind :=
      if flags.left && flags.right then .full else if flags.left then .left else if flags.right then .right
      else .inner
    some (kind, flags.natural)

/-- The rule by which a join of the kind changes an unqualified name of a column that it
merges: an inner or left join keeps the left result, a right join takes its own column,
and a full join coalesces them. -/
def Resolved.JoinKind.mergeRule : Resolved.JoinKind → MergeRule
  | .right => .takeRight
  | .full => .coalesce
  | .inner | .left => .keepLeft

/-- Whether a parsed join operator is a right or full join. -/
def rightOrFull : Option (Resolved.JoinKind × Bool) → Bool
  | some (.right, _) | some (.full, _) => true
  | some (.inner, _) | some (.left, _) | none => false

/-- The joined sources of the joins in order, each with its parsed operator
({name}`joinOperator`), with their merged columns and merge rules, and the kind and
condition of each join ({name}`mergeJoin`), after the sources of {lit}`left`;
{lit}`coalesced` says whether the {lit}`FROM` has a right or full join; {lit}`item` is the
position of the first join. An operator that SQLite refuses is a model restriction, checked
before the join's {lit}`USING` and {lit}`NATURAL` errors. -/
def mergeJoins (coalesced : Bool) (left : Scope) (item : Nat) :
    List (Syntax.Join × Option (Resolved.JoinKind × Bool) × ScopeSource) →
      Except ValueIssue (Scope × List (Resolved.JoinKind × JoinCondition))
  | [] => .ok (left, [])
  | (join, operator, right) :: rest => do
    let some (kind, natural) := operator | throw (.restriction [2, item, 0] .joinOperator)
    let (merged, condition) ← mergeJoin left right natural coalesced kind.mergeRule item join
    let (scope, conditions) ← mergeJoins coalesced (left ++ [merged]) (item + 1) rest
    .ok (scope, (kind, condition) :: conditions)

/-- Resolve the condition of the source at {lit}`index` of the scope: a merged condition is
resolved already; a written one resolves over the whole scope, as SQLite does, and then
must read only the sources up to this one, which the model evaluates while it joins
({name}`RestrictionKind.laterTableInOn`). -/
def resolveJoinCondition (dqs : Bool) (scope : Scope) (index : Nat) : JoinCondition → Except ValueIssue (Option Resolved.Expr)
  | .none => .ok none
  | .merged condition => .ok (some condition)
  | .written path term => do
    let resolved ← condition path (resolveOperand dqs scope true term)
    let bound := (scope.take (index + 1)).foldl (fun width source => width + source.columns.length) 0
    if resolved.readsBelow bound then .ok (some resolved)
    else throw (.restriction path .laterTableInOn)

end Belay.Sqlite
