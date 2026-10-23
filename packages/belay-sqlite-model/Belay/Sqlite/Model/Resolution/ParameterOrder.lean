import Belay.Sqlite.Model.Resolution.QueryExprs

set_option doc.verso true

/-! Where SQLite reports a parameter that it prohibits (ADR 0019, D1). SQLite gives
{lit}`parameters prohibited in ...` while it walks the names of a {lit}`CHECK` constraint, a
generated column, an index expression or the filter of a partial index. Each error of the walk
replaces the message of an earlier one. A parameter, a name that does not resolve and a
subquery stop the walk, but the argument list of a function call and the operand of
{lit}`ISNULL` or {lit}`NOTNULL` end the stop, and the walk goes on after them. {lit}`x IS name`
resolves the name before {lit}`x`, and {lit}`x IN ()` has no operand. The errors of functions,
of {lit}`.` and of collations come after the walk (checked natively, 3.51.0). -/

namespace Belay.Sqlite.Model

/-- The last error of SQLite's walk of names so far: a parameter, a name with its error, or a
subquery, whose error resolution gives. -/
inductive WalkError where
  /-- A parameter. -/
  | parameter
  /-- A name that does not resolve, with the error of its resolution. -/
  | name (issue : ValueIssue)
  /-- A subquery, which SQLite prohibits there. -/
  | subquery

/-- The state of the walk: the last error, and whether the walk stopped. -/
abbrev WalkState := Option WalkError × Bool

/-- The error of a name as {name}`resolveOperand` reports it with a prepare error, or none for
a name that resolves, a double-quoted text and the restriction of a rowid name. -/
def nameError (dqs : Bool) (scope : Scope) (name : Syntax.Expr) : Option ValueIssue :=
  match resolveOperand dqs scope {} true name with
  | .error issue@(.prepare _) => some issue
  | .error (.restriction ..) | .ok _ => none

/-- A bare name, also under {lit}`COLLATE`, which SQLite resolves first on the right of
{lit}`IS` and {lit}`IS NOT`. -/
def bareName : Syntax.Expr → Option Syntax.Expr
  | name@(.identifier ..) => some name
  | .collate operand _ => bareName operand
  | .null | .numeric _ | .string _ | .blob _ | .parameter _ | .currentTime _ | .qualified .. | .negate _
  | .positive _ | .compare .. | .and .. | .or .. | .not _ | .isNull .. | .callStar _ | .call .. | .arithmetic ..
  | .cast .. | .exists _ | .inQuery .. | .subquery _ | .inList .. | .between .. | .caseOf .. | .concatenate ..
  | .raise .. => none

/-- One step of the walk at a name: its error stops the walk. -/
def walkName (dqs : Bool) (scope : Scope) (name : Syntax.Expr) (state : WalkState) : WalkState :=
  match nameError dqs scope name with
  | some issue => (some (.name issue), true)
  | none => state

/-- Whether the operator is {lit}`IS` or {lit}`IS NOT`. -/
def isTest : Comparison → Bool
  | .is | .isNot => true
  | .eq | .ne | .lt | .le | .gt | .ge => false

/-- The walk after a step: the state of the step when it stopped, else the next walk from it. -/
def WalkState.andThen (first : WalkState) (next : WalkState → WalkState) : WalkState :=
  if first.2 then first else next first

mutual
/-- SQLite's walk of the names of an expression in its order, from a state that has not
stopped: the state after it. -/
def walkParameters (dqs : Bool) (scope : Scope) (state : WalkState) : Syntax.Expr → WalkState
  | .parameter _ => (some .parameter, true)
  | name@(.identifier ..) | name@(.qualified ..) => walkName dqs scope name state
  | .exists _ | .subquery _ | .inQuery .. => (some .subquery, true)
  | .compare operator left right =>
    if isTest operator && right matches .null then ((walkParameters dqs scope state left).1, false)
    else
      let first := match isTest operator, bareName right with
        | true, some name => walkName dqs scope name state
        | true, none | false, _ => state
      first.andThen fun next =>
        (walkParameters dqs scope next left).andThen fun next => walkParameters dqs scope next right
  | .and left right | .or left right | .arithmetic _ left right | .concatenate left right =>
    (walkParameters dqs scope state left).andThen fun next => walkParameters dqs scope next right
  | .isNull operand _ => ((walkParameters dqs scope state operand).1, false)
  | .not operand | .negate operand | .positive operand | .cast operand _ | .collate operand _ =>
    walkParameters dqs scope state operand
  | .call _ arguments => ((walkList dqs scope state arguments).1, false)
  | .caseOf arguments _ => walkList dqs scope state arguments
  | .inList operand values _ =>
    if values.isEmpty then state
    else (walkParameters dqs scope state operand).andThen fun next => walkList dqs scope next values
  | .between operand low high _ =>
    (walkParameters dqs scope state operand).andThen fun next =>
      (walkParameters dqs scope next low).andThen fun next => walkParameters dqs scope next high
  | .raise _ (some message) => walkParameters dqs scope state message
  | .raise _ none | .null | .numeric _ | .string _ | .blob _ | .currentTime _ | .callStar _ => state

/-- The walk of a list in order, up to the first expression that stops it. -/
def walkList (dqs : Bool) (scope : Scope) (state : WalkState) : List Syntax.Expr → WalkState
  | [] => state
  | expression :: rest =>
    (walkParameters dqs scope state expression).andThen fun next => walkList dqs scope next rest
end

/-- SQLite's error where a parameter is prohibited, after its walk of names
({name}`walkParameters`): the error of the parameter when it is the last error, the error of
the name when a name is; else nothing, and the resolution of the expression reports its own
errors. -/
def prohibitParameter (dqs : Bool) (scope : Scope) (error : ExprError) (expression : Syntax.Expr) :
    Except ValueIssue Unit :=
  match (walkParameters dqs scope (none, false) expression).1 with
  | some .parameter => throw (.prepare error)
  | some (.name issue) => throw issue
  | some .subquery | none => pure ()

end Belay.Sqlite.Model
