import Belay.Sqlite.Model.Resolution.MergedLeft
import Belay.Sqlite.Model.Resolution.ScopeBindings
import Belay.Sqlite.Model.Resolution.TracedList

set_option doc.verso true

/-! {lit}`USING` and {lit}`NATURAL` joins (ADR 0012, amendment 2, owner decision 1, and
amendment 3; slices 4b and 4d): the names that a join merges. The name trace holds one occurrence
for each name of {lit}`USING`, at child 3 of its join, in the order of the list. -/

namespace Belay.Sqlite.Model

/-- The occurrence of a name of {lit}`USING` at {lit}`path`. -/
def usingOccurrence (path : List Nat) (name : Identifier) (result : NameResult) : NameOccurrence :=
  { path, role := .columnReference, name := some name, result }

/-- The columns that a name of {lit}`USING` binds: the left-most column of the left input with the
name (every column of it when {lit}`coalesced`) and the column of the joined source, which is at
{lit}`rightIndex` among the sources of its {lit}`FROM`. -/
def usingBindings (coalesced : Bool) (left : Scope) (right : ScopeSource) (rightIndex : Nat) (name : Identifier) :
    List Binding :=
  let positions := left.namedPositions name
  left.bindingsAt (if coalesced then positions else positions.take 1) ++
    ((columnPosition right.columns name).bind fun index =>
      right.columns[index]?.map (right.binding rightIndex index)).toList

/-- The columns of the joined source that the left input also has: the names that {lit}`USING`
may list. -/
def usingCandidates (left : Scope) (right : ScopeSource) (rightIndex : Nat) : List Candidate :=
  right.candidates rightIndex fun index => (right.columns[index]?.map (left.hasColumn ·.name)).getD false

/-- A name of {lit}`USING`, as written, when it names a column of the joined source and of
the left input; else SQLite's {name}`ExprError.joinUsingColumn`. With
{lit}`coalesced` (a right or full join in the {lit}`FROM`), the name must then be unambiguous
({name}`usingReferenceChecked`). The name is recorded at {lit}`path` with the columns that it binds, or
with the candidates that it could have been; {lit}`rightIndex` is the position of the joined source. -/
def usingNameCheckedTraced (coalesced : Bool) (left : Scope) (right : ScopeSource) (name : Identifier)
    (path : List Nat := []) (rightIndex : Nat := 0) : Traced ValueIssue Identifier :=
  if (columnPosition right.columns name).isSome && left.hasColumn name then
    if coalesced then
      if left.usingUnambiguous name then do
        Traced.record (usingOccurrence path name (.found (usingBindings coalesced left right rightIndex name)))
        pure name
      else do
        Traced.record (usingOccurrence path name
          (.ambiguous ((left.bindingsAt (left.namedPositions name)).map .column)))
        throw (.prepare (.ambiguousUsingReference name))
    else do
      Traced.record (usingOccurrence path name (.found (usingBindings coalesced left right rightIndex name)))
      pure name
  else do
    Traced.record (usingOccurrence path name (.missing .error (usingCandidates left right rightIndex)))
    throw (.prepare (.joinUsingColumn name))

/-- A name of {lit}`USING`: {name}`usingNameCheckedTraced` without its trace. -/
def usingNameChecked (coalesced : Bool) (left : Scope) (right : ScopeSource) (name : Identifier) :
    Except ValueIssue Identifier :=
  (usingNameCheckedTraced coalesced left right name).drop

/-- For every path and position of the joined source: they change only the trace of a name of
{lit}`USING`, not its result. Proof sketch: unfold both sides; they split on the same conditions and
the records leave the result unchanged. -/
@[traced_drop] theorem drop_usingNameCheckedTraced (coalesced : Bool) (left : Scope) (right : ScopeSource)
    (name : Identifier) (path : List Nat) (rightIndex : Nat) :
    (usingNameCheckedTraced coalesced left right name path rightIndex).drop = usingNameChecked coalesced left right name := by
  simp only [usingNameChecked, usingNameCheckedTraced, traced_drop]

/-- For every item function that ignores the position, list and start: resolving the list in order
is the monadic map. Proof sketch: induction on the list; both sides run the function on the first
item, then on the rest. -/
theorem resolveAllFrom_const (resolveOne : α → Except ε β) (start : Nat) (items : List α) :
    resolveAllFrom (fun _ => resolveOne) start items = items.mapM resolveOne := by
  induction items generalizing start with
  | nil => rfl
  | cons item rest ih => simp [resolveAllFrom, List.mapM_cons, ih]

/-- For every item function that ignores the position, and list: {name}`resolveAll` is the monadic
map. Proof sketch: it is {name}`resolveAllFrom_const` from position zero. -/
theorem resolveAll_const (resolveOne : α → Except ε β) (items : List α) :
    resolveAll (fun _ => resolveOne) items = items.mapM resolveOne := resolveAllFrom_const resolveOne 0 items

/-- The names that a join merges, as written: for {lit}`NATURAL`, every column of the
joined source whose name also names a column of the left input, in the joined table's
order; for {lit}`USING`, its names, each of which must name a column of both
({name}`ExprError.joinUsingColumn` otherwise). With {lit}`coalesced`, each name must
also pass {name}`usingReferenceChecked`, in order. None for a join with neither, and
SQLite's {name}`ExprError.naturalJoinCondition` for {lit}`NATURAL` with {lit}`ON` or
{lit}`USING`. The names of {lit}`USING` are recorded at child 3 of the join at {lit}`item`; the names of
{lit}`NATURAL` are not written, so they have no occurrence. -/
def mergedNamesTraced (coalesced : Bool) (left : Scope) (right : ScopeSource) (natural : Bool) (join : Syntax.Join)
    (item : Nat := 0) (rightIndex : Nat := 0) : Traced ValueIssue (Option (List Identifier)) :=
  if natural then
    if join.condition.isSome || join.usingColumns.isSome then throw (.prepare .naturalJoinCondition)
    else
      let names := right.columns.filterMap fun column => if left.hasColumn column.name then some column.name else none
      if coalesced then Traced.lift ((names.mapM (usingReferenceChecked left)).map some) else pure (some names)
  else match join.usingColumns with
    | none => pure none
    | some names => do
      pure (some (← resolveAllTraced (fun position name =>
        usingNameCheckedTraced coalesced left right name [2, item, 3, position] rightIndex) names))

/-- The names that a join merges: {name}`mergedNamesTraced` without its trace. -/
def mergedNames (coalesced : Bool) (left : Scope) (right : ScopeSource) (natural : Bool) (join : Syntax.Join) :
    Except ValueIssue (Option (List Identifier)) :=
  (mergedNamesTraced coalesced left right natural join).drop

end Belay.Sqlite.Model
