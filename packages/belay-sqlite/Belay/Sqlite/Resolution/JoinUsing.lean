import Belay.Sqlite.Resolution.Values
import Belay.Sqlite.Resolution.Scope
import Belay.Sqlite.Resolution.Syntax

set_option doc.verso true

/-! {lit}`USING` and {lit}`NATURAL` joins (ADR 0012, amendment 2, owner decision 1;
slice 4b). Each is an inner or left join with a generated {lit}`ON` condition: for each
merged name {lit}`c`, {lit}`left.c = right.c`, where {lit}`left.c` is the left-most
column {lit}`c` of the left input. The right column of each pair is merged
({name}`Belay.Sqlite.Source.merged`), so {lit}`*` and unqualified names see only the left one. The
condition is written syntax with qualified names, so it resolves with the comparison
rules and restrictions of a written {lit}`ON` condition. -/

namespace Belay.Sqlite

/-- The name of the left-most source of the scope with a column of the folded name, and
that column's name as declared; none when no source has one. A merged column has a
column of the same name in an earlier source, so the result is never merged. -/
def Scope.leftMost (scope : Scope) (name : String) : Option (String × String) :=
  scope.findSome? fun source =>
    (columnPosition source.columns name).bind fun position =>
      source.columns[position]?.map fun column => (source.name, column.name)

/-- A name of {lit}`USING`, as written, when it names a column of the joined source and of
the left input; else SQLite's {name}`PrepareError.joinUsingColumn`. -/
def usingNameChecked (left : Scope) (right : Source) (name : String) : Except ValueIssue String :=
  if (columnPosition right.columns name).isSome && (left.leftMost name).isSome then .ok name
  else .error (.prepare (.joinUsingColumn name))

/-- The names that a join merges, as written: for {lit}`NATURAL`, every column of the
joined source whose name also names a column of the left input, in the joined table's
order; for {lit}`USING`, its names, each of which must name a column of both
({name}`PrepareError.joinUsingColumn` otherwise). None for a join with neither, and
SQLite's {name}`PrepareError.naturalJoinCondition` for {lit}`NATURAL` with {lit}`ON` or
{lit}`USING`. -/
def mergedNames (left : Scope) (right : Source) (natural : Bool) (join : Syntax.Join) :
    Except ValueIssue (Option (List String)) :=
  if natural then
    if join.condition.isSome || join.usingColumns.isSome then .error (.prepare .naturalJoinCondition)
    else .ok (some (right.columns.filterMap fun column => (left.leftMost column.name).map fun _ => column.name))
  else match join.usingColumns with
    | none => .ok none
    | some names => (names.mapM (usingNameChecked left right)).map some

/-- The generated condition of the merged names: the conjunction, in order, of
{lit}`left.c = right.c` for each name {lit}`c`, with qualified names of the left-most left
source and of the joined source; none for no name, which is a cross join. -/
def mergedCondition (left : Scope) (right : Source) (names : List String) : Option Syntax.Expr :=
  let equalities := names.filterMap fun name => do
    let (source, column) ← left.leftMost name
    let position ← columnPosition right.columns name
    let joined ← right.columns[position]?
    some (Syntax.Expr.equals (.qualified source column) (.qualified right.name joined.name))
  match equalities with
  | [] => none
  | first :: rest => some (rest.foldl .and first)

/-- The joined source with its merged columns, and the join's condition with the path of
its issues: the written {lit}`ON` condition at child 2, or the condition of the merged
names ({name}`mergedCondition`) at child 3 for {lit}`USING` and child 0 for
{lit}`NATURAL`. The left input is every earlier source; {lit}`item` is the join's
position. -/
def mergeJoin (left : Scope) (right : Source) (natural : Bool) (item : Nat) (join : Syntax.Join) :
    Except ValueIssue (Source × Option (List Nat × Syntax.Expr)) := do
  match ← mergedNames left right natural join with
  | none => .ok (right, join.condition.map ([2, item, 2], ·))
  | some names =>
    let merged := names.filterMap (columnPosition right.columns ·)
    .ok ({ right with merged }, (mergedCondition left right names).map ((if natural then [2, item, 0] else [2, item, 3]), ·))

/-- For every left scope, joined source, item and join that has neither {lit}`NATURAL` nor
{lit}`USING`, {name}`mergeJoin` merges no column and gives the written {lit}`ON` condition,
if any, at child 2: such a join resolves as in slice 4. -/
theorem mergeJoin_written (left : Scope) (right : Source) (item : Nat) (join : Syntax.Join)
    (noUsing : join.usingColumns = none) :
    mergeJoin left right false item join = .ok (right, join.condition.map ([2, item, 2], ·)) := by
  simp [mergeJoin, mergedNames, noUsing, bind, Except.bind]

/-- For every left scope, joined source and list of names that each name a column of
the joined source and of the left input, {name}`usingNameChecked` accepts them all, in order. Proof sketch:
induction on the names; the assumption for the first name makes its check succeed, and
the assumption for the other names gives the induction hypothesis. -/
theorem usingNames_checked (left : Scope) (right : Source) (names : List String)
    (both : ∀ name ∈ names, (columnPosition right.columns name).isSome ∧ (left.leftMost name).isSome) :
    names.mapM (usingNameChecked left right) = .ok names := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
    have head := both name (by simp)
    have tail := ih (fun other member => both other (by simp [member]))
    rw [List.mapM_cons, tail]
    simp [usingNameChecked, head.1, head.2, bind, Except.bind, pure, Except.pure]

/-- For every left scope, joined source, item and join with {lit}`USING` names that each
name a column of the joined source and of the left input, {name}`mergeJoin` merges the
joined columns of those names and gives the conjunction of their equalities
({name}`mergedCondition`) at child 3. -/
theorem mergeJoin_using (left : Scope) (right : Source) (item : Nat) (join : Syntax.Join) (names : List String)
    (written : join.usingColumns = some names)
    (both : ∀ name ∈ names, (columnPosition right.columns name).isSome ∧ (left.leftMost name).isSome) :
    mergeJoin left right false item join =
      .ok ({ right with merged := names.filterMap (columnPosition right.columns ·) },
        (mergedCondition left right names).map ([2, item, 3], ·)) := by
  unfold mergeJoin mergedNames
  simp only [Bool.false_eq_true, ite_false, written]
  rw [usingNames_checked left right names both]
  rfl

/-- For every left scope, joined source, item and {lit}`NATURAL` join without {lit}`ON`
and {lit}`USING`, {name}`mergeJoin` merges the columns of the joined source whose names
the left input also has, and gives the conjunction of their equalities
({name}`mergedCondition`) at child 0; with no common name, there is no condition, a
cross join. -/
theorem mergeJoin_natural (left : Scope) (right : Source) (item : Nat) (join : Syntax.Join)
    (noOn : join.condition = none) (noUsing : join.usingColumns = none) :
    let names := right.columns.filterMap fun column => (left.leftMost column.name).map fun _ => column.name
    mergeJoin left right true item join =
      .ok ({ right with merged := names.filterMap (columnPosition right.columns ·) },
        (mergedCondition left right names).map ([2, item, 0], ·)) := by
  simp [mergeJoin, mergedNames, noOn, noUsing, bind, Except.bind]

end Belay.Sqlite
