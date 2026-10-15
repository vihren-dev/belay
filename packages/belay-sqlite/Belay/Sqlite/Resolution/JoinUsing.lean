import Belay.Sqlite.Resolution.MergedLeft

set_option doc.verso true

/-! {lit}`USING` and {lit}`NATURAL` joins (ADR 0012, amendment 2, owner decision 1, and
amendment 3; slices 4b and 4d). Each is its join with a generated {lit}`ON` condition: for
each merged name {lit}`c`, {lit}`left.c = right.c`, where {lit}`left.c` is the left side
of {lit}`MergedLeft.lean`. The right column of each pair is merged
({name}`Belay.Sqlite.Source.merged`), and the join's kind gives the
{name}`Belay.Sqlite.MergeRule` of unqualified names. The condition is written syntax,
so it resolves with the comparison rules and restrictions of a written {lit}`ON`
condition. -/

namespace Belay.Sqlite

/-- A name of {lit}`USING`, as written, when it names a column of the joined source and of
the left input; else SQLite's {name}`PrepareError.joinUsingColumn`. With
{lit}`coalesced` (a right or full join in the {lit}`FROM`), the name must then pass
{name}`usingReferenceChecked`. -/
def usingNameChecked (coalesced : Bool) (left : Scope) (right : Source) (name : String) :
    Except ValueIssue String :=
  if (columnPosition right.columns name).isSome && (left.leftMost name).isSome then
    if coalesced then usingReferenceChecked left name else .ok name
  else .error (.prepare (.joinUsingColumn name))

/-- The names that a join merges, as written: for {lit}`NATURAL`, every column of the
joined source whose name also names a column of the left input, in the joined table's
order; for {lit}`USING`, its names, each of which must name a column of both
({name}`PrepareError.joinUsingColumn` otherwise). With {lit}`coalesced`, each name must
also pass {name}`usingReferenceChecked`, in order. None for a join with neither, and
SQLite's {name}`PrepareError.naturalJoinCondition` for {lit}`NATURAL` with {lit}`ON` or
{lit}`USING`. -/
def mergedNames (coalesced : Bool) (left : Scope) (right : Source) (natural : Bool) (join : Syntax.Join) :
    Except ValueIssue (Option (List String)) :=
  if natural then
    if join.condition.isSome || join.usingColumns.isSome then .error (.prepare .naturalJoinCondition)
    else
      let names := right.columns.filterMap fun column => (left.leftMost column.name).map fun _ => column.name
      if coalesced then (names.mapM (usingReferenceChecked left)).map some else .ok (some names)
  else match join.usingColumns with
    | none => .ok none
    | some names => (names.mapM (usingNameChecked coalesced left right)).map some

/-- The generated condition of the merged names: the conjunction, in order, of
{lit}`left = right.c` for each name {lit}`c`, with the left side of {name}`mergedLeft`
and the qualified column of the joined source; none for no name, which is a cross
join. -/
def mergedCondition (coalesced : Bool) (left : Scope) (right : Source) (names : List String) : Option Syntax.Expr :=
  let equalities := names.filterMap fun name => do
    let leftSide ← mergedLeft coalesced left name
    let position ← columnPosition right.columns name
    let joined ← right.columns[position]?
    some (Syntax.Expr.equals leftSide (.qualified right.name joined.name))
  match equalities with
  | [] => none
  | first :: rest => some (rest.foldl .and first)

/-- The joined source with its merged columns and the merge rule of its join, which also
tells later expansions of {lit}`*` whether a right or full join follows, and the
join's condition with the path of its issues: the written {lit}`ON` condition at child 2,
or the condition of the merged names ({name}`mergedCondition`) at child 3 for
{lit}`USING` and child 0 for {lit}`NATURAL`. The left input is every earlier source;
{lit}`coalesced` says whether the {lit}`FROM` has a right or full join; {lit}`item` is the
join's position. -/
def mergeJoin (left : Scope) (right : Source) (natural coalesced : Bool) (rule : MergeRule) (item : Nat)
    (join : Syntax.Join) : Except ValueIssue (Source × Option (List Nat × Syntax.Expr)) := do
  match ← mergedNames coalesced left right natural join with
  | none => .ok ({ right with mergeRule := rule }, join.condition.map ([2, item, 2], ·))
  | some names =>
    let merged := names.filterMap (columnPosition right.columns ·)
    .ok ({ right with merged, mergeRule := rule },
      (mergedCondition coalesced left right names).map ((if natural then [2, item, 0] else [2, item, 3]), ·))

/-- For every left scope, joined source, flag, rule, item and join that has neither
{lit}`NATURAL` nor {lit}`USING`, {name}`mergeJoin` merges no column, records the rule, and
gives the written {lit}`ON` condition, if any, at child 2: such a join resolves as in
slice 4. -/
theorem mergeJoin_written (left : Scope) (right : Source) (coalesced : Bool) (rule : MergeRule) (item : Nat)
    (join : Syntax.Join) (noUsing : join.usingColumns = none) :
    mergeJoin left right false coalesced rule item join =
      .ok ({ right with mergeRule := rule }, join.condition.map ([2, item, 2], ·)) := by
  simp [mergeJoin, mergedNames, noUsing, bind, Except.bind]

/-- For every left scope, joined source and list of names that each name a column of
the joined source and of the left input, {name}`usingNameChecked` without
{lit}`coalesced` accepts them all, in order. Proof sketch: induction on the names; the
assumption for the first name makes its check succeed, and the assumption for the other
names gives the induction hypothesis. -/
theorem usingNames_checked (left : Scope) (right : Source) (names : List String)
    (both : ∀ name ∈ names, (columnPosition right.columns name).isSome ∧ (left.leftMost name).isSome) :
    names.mapM (usingNameChecked false left right) = .ok names := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
    have head := both name (by simp)
    have tail := ih (fun other member => both other (by simp [member]))
    rw [List.mapM_cons, tail]
    simp [usingNameChecked, head.1, head.2, bind, Except.bind, pure, Except.pure]

/-- For every left scope, joined source, rule, item and join with {lit}`USING` names that
each name a column of the joined source and of the left input, in a {lit}`FROM` without
right and full joins, {name}`mergeJoin` merges the joined columns of those names under
the rule and gives the conjunction of their equalities with the left-most left columns
({name}`mergedCondition`) at child 3, as in slice 4b. -/
theorem mergeJoin_using (left : Scope) (right : Source) (rule : MergeRule) (item : Nat) (join : Syntax.Join)
    (names : List String) (written : join.usingColumns = some names)
    (both : ∀ name ∈ names, (columnPosition right.columns name).isSome ∧ (left.leftMost name).isSome) :
    mergeJoin left right false false rule item join =
      .ok ({ right with merged := names.filterMap (columnPosition right.columns ·), mergeRule := rule },
        (mergedCondition false left right names).map ([2, item, 3], ·)) := by
  unfold mergeJoin mergedNames
  simp only [Bool.false_eq_true, ite_false, written]
  rw [usingNames_checked left right names both]
  rfl

/-- For every left scope, joined source, rule, item and {lit}`NATURAL` join without
{lit}`ON` and {lit}`USING`, in a {lit}`FROM` without right and full joins, {name}`mergeJoin`
merges the columns of the joined source whose names the left input also has, under the
rule, and gives the conjunction of their equalities with the left-most left columns
({name}`mergedCondition`) at child 0, as in slice 4b; with no common name, there is no
condition, a cross join. -/
theorem mergeJoin_natural (left : Scope) (right : Source) (rule : MergeRule) (item : Nat) (join : Syntax.Join)
    (noOn : join.condition = none) (noUsing : join.usingColumns = none) :
    let names := right.columns.filterMap fun column => (left.leftMost column.name).map fun _ => column.name
    mergeJoin left right true false rule item join =
      .ok ({ right with merged := names.filterMap (columnPosition right.columns ·), mergeRule := rule },
        (mergedCondition false left right names).map ([2, item, 0], ·)) := by
  simp [mergeJoin, mergedNames, noOn, noUsing, bind, Except.bind]

end Belay.Sqlite
