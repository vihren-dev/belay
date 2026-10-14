import Belay.Sqlite.Resolution.Writes

set_option doc.verso true

/-! Resolution of the {lit}`FROM` of a {lit}`SELECT` (ADR 0012, amendment 2): the tables
and their names, the joins, and their {lit}`ON` conditions. The paths follow
{lit}`Syntax.Statement.select`: child 1 is the first table and child 2 the joins; in a
join, child 0 is its operator, child 1 its table, child 2 its {lit}`ON` condition and
child 3 its {lit}`USING` list. -/

namespace Belay.Sqlite

/-- Whether every column that the expression reads has a position below the bound: the
expression reads only the tables whose cells come before it in the joined row. -/
def Resolved.Expr.readsBelow (bound : Nat) : Resolved.Expr → Bool
  | .column position => position < bound
  | .literal _ => true
  | .compare _ left right | .and left right | .or left right | .arithmetic _ left right | .coalesce left right =>
    left.readsBelow bound && right.readsBelow bound
  | .not operand | .isNull operand _ | .cast _ operand => operand.readsBelow bound

/-- The number of tables in a join that SQLite accepts ({lit}`SQLITE_MAX_SRCLIST`). -/
def maximumJoinTables : Nat := 64

/-- The source of one table reference at {lit}`path`: the table's catalog position and the
source with its name (the alias, else the table name). A missing table is SQLite's
{lit}`no such table: %s`; one of SQLite's own tables is a model restriction, as in a
query of one table. -/
def resolveTableReference (catalog : Catalog) (path : List Nat) (reference : Syntax.TableReference) :
    Except ValueIssue (Nat × Source) :=
  match catalog.findTable reference.table with
  | some (position, table) => .ok (position, { name := reference.alias.getD reference.table, columns := table.columns })
  | none =>
    if reservedName reference.table then .error (.restriction path .systemTable)
    else .error (.prepare (.noSuchTable reference.table))

/-- The kind of a join operator and whether it has {lit}`NATURAL`, from its keywords as
written, which SQLite compares without ASCII case: {lean}`joinOperator ["Left", "OUTER"]`
is a left join without {lit}`NATURAL`. None for keywords that the model does not
describe, such as {lean}`["OUTER", "LEFT"]`, which SQLite also accepts. -/
def joinOperator (words : List String) : Option (Syntax.JoinKind × Bool) :=
  let folded := words.map normalizeIdentifier
  let (natural, rest) := match folded with
    | "natural" :: rest => (true, rest)
    | rest => (false, rest)
  let kind : Option Syntax.JoinKind := match rest with
    | [] | ["inner"] | ["cross"] => some .inner
    | ["left"] | ["left", "outer"] => some .left
    | ["right"] | ["right", "outer"] => some .right
    | ["full"] | ["full", "outer"] => some .full
    | _ => none
  kind.map (·, natural)

/-- The model restriction of a join form that slice 4 does not describe, if it is one:
another join operator, {lit}`NATURAL`, {lit}`USING`, or a {lit}`RIGHT` or {lit}`FULL`
join. -/
def joinFormIssue (item : Nat) (join : Syntax.Join) : Option ValueIssue :=
  match joinOperator join.operator with
  | none => some (.restriction [2, item, 0] .joinOperator)
  | some (_, true) => some (.restriction [2, item, 0] .naturalJoin)
  | some (kind, false) =>
    if join.usingColumns.isSome then some (.restriction [2, item, 3] .joinUsing)
    else match kind with
      | .right | .full => some (.restriction [2, item, 0] .rightOrFullJoin)
      | .inner | .left => none

/-- The kind of a resolved join: left for a left join operator, else inner, which is
right for every join that {name}`joinFormIssue` accepts. -/
def Syntax.Join.resolvedKind (join : Syntax.Join) : Resolved.JoinKind :=
  match joinOperator join.operator with
  | some (.left, _) => .left
  | _ => .inner

/-- Resolve the tables of {lit}`FROM`: the first table's position, the positions of the
joined tables, and the scope of all sources, in order. More than
{name}`maximumJoinTables` tables is SQLite's {lit}`at most 64 tables in a join`; a join form
that the model does not describe ({name}`joinFormIssue`) and two sources with the same
folded name are model restrictions. -/
def resolveTables (catalog : Catalog) (source : Syntax.TableReference) (joins : List Syntax.Join) :
    Except ValueIssue (Nat × List Nat × Scope) := do
  if joins.length + 1 > maximumJoinTables then throw (.prepare .tooManyTables)
  let (first, firstSource) ← resolveTableReference catalog [1] source
  let joined ← resolveAll (fun item (join : Syntax.Join) => do
    let resolved ← resolveTableReference catalog [2, item, 1] join.source
    match joinFormIssue item join with
    | some issue => throw issue
    | none => .ok resolved) joins
  let scope := firstSource :: joined.map Prod.snd
  match findPosition (fun (item, source) => scope.take item |>.any fun earlier =>
      normalizeIdentifier earlier.name == normalizeIdentifier source.name) (scope.mapIdx fun item source => (item, source)) with
  | some (item, _) => throw (.restriction (if item == 0 then [1] else [2, item - 1, 1]) .duplicateSource)
  | none => .ok (first, joined.map Prod.fst, scope)

/-- Resolve the {lit}`ON` condition of the join at {lit}`item` over the whole scope, as
SQLite does, then require that it reads only the tables up to the joined one, which the
model evaluates while it joins ({name}`RestrictionKind.laterTableInOn`). -/
def resolveJoinCondition (dqs : Bool) (scope : Scope) (item : Nat) (join : Syntax.Join) :
    Except ValueIssue (Option Resolved.Expr) :=
  match join.condition with
  | none => .ok none
  | some term => do
    let resolved ← condition [2, item, 2] (resolveOperand dqs scope true term)
    let bound := (scope.take (item + 2)).foldl (fun width source => width + source.columns.length) 0
    if resolved.readsBelow bound then .ok (some resolved)
    else throw (.restriction [2, item, 2] .laterTableInOn)

end Belay.Sqlite
