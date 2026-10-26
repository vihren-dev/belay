import Belay.Sqlite.Model.Resolution.Returning

set_option doc.verso true

/-! The {lit}`SET` assignments of UPDATE and of {lit}`ON CONFLICT DO UPDATE`: each value
is an expression over the sources in scope, resolved as in {lit}`SELECT`, and a value
that names no column folds to the literal of its stored value. -/

namespace Belay.Sqlite.Model

/-- The resolved value of one {lit}`SET` assignment for the column at
{lit}`position`: the literal of its stored value ({name}`Value.store`) when the
expression names no column and reads no clock and no parameter (so any clock value, 0 here,
gives its value), otherwise the expression, which the
execution evaluates on the old row, at the statement's clock value, and stores. -/
def assignedExpression (scope : Scope) (position : Nat) (expression : Syntax.Expr)
    (resolved : Resolved.Expr) : Resolved.Expr :=
  if mentionsColumn scope expression || resolved.readsClock || resolved.readsRunValue then resolved
  else .literal (Value.store (columnAffinity scope.columns position) (resolved.eval (.plain 0) []))

/-- The occurrence of a column name that sets a column of the table, at {lit}`path`: the column of the
table that the name gives, else the columns of the table (the first source of the scope) as
candidates. {lit}`use` says what a missing name is: a rowid name that the model refuses, or no such
column. -/
def columnTargetOccurrence (scope : Scope) (path : List Nat) (name : Identifier) (position : Option Nat)
    (use : MissingUse) : NameOccurrence :=
  { path, role := .columnTarget, name := some name,
    result := match position with
      | some position => .found (scope.bindingsAt [position])
      | none => .missing use (Scope.columnCandidates (scope.take 1)) }

/-- The column that the name of an assignment at {lit}`item` sets: a column of the table, or, for a
table with a rowid, a rowid name ({lit}`rowid`, {lit}`_rowid_` or {lit}`oid`), which sets the
rowid: the column of the rowid alias, and the restriction {name}`RestrictionKind.rowidName` for a
table without one. -/
def assignedPosition (scope : Scope) (rowid : Option (Option Nat)) (item : Nat) (name : Identifier) :
    Except ValueIssue Nat :=
  match columnPosition scope.columns name, rowid with
  | some position, _ => .ok position
  | none, some alias => if !rowidName name then .error (.prepare (.noSuchColumn name)) else match alias with
    | some position => .ok position
    | none => .error (.restriction [item, 0] .rowidName)
  | none, none => .error (.prepare (.noSuchColumn name))

/-- Resolve one {lit}`SET` assignment at item {lit}`item`, in SQLite's order
({lit}`sqlite3Update`): the expression first, then the column name. The column name
must name a column of the table ({lit}`no such column: %s`), or, for a table with a rowid, be a
rowid name ({name}`assignedPosition`). A
generated column is the issue {lit}`generated` of its name. A value that reads the
row for a column of a unique key ({lit}`keyColumns`) is a model restriction, and so is a
value that names no column and whose JSON function may fail. The value may name the
statement's subqueries ({lit}`shapes`). Paths are relative to the assignment list: part 0 of an
assignment is the column and part 1 the value. In a
trigger's body, {lit}`around` is the trigger's rows (ADR 0018, D5): the value sees them, and a
value that reads only them does not read the row; elsewhere it is empty. -/
def resolveAssignmentTraced (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (keyColumns : List Nat)
    (generated : Identifier → ValueIssue) (rowid : Option (Option Nat)) (item : Nat) (around : Scope := []) :
    Identifier × Syntax.Expr → Traced ValueIssue (Nat × Resolved.Expr)
  | (name, value) => do
    let operand ← (resolveOperandTraced dqs (scope ++ around) shapes true value).under [item, 1]
    let located := assignedPosition scope rowid item name
    Traced.record (columnTargetOccurrence scope [item, 0] name located.toOption
      (if rowid.isSome && rowidName name && (columnPosition scope.columns name).isNone then .rowidName else .error))
    let position ← located
    if (scope.columns[position]?.bind (·.generated)).isSome then throw (generated name)
    else if mentionsColumn scope value && keyColumns.contains position then
      throw (.restriction [item, 1] .rowDependentKey)
    else if !mentionsColumn (scope ++ around) value && !operand.1.readsClock && !operand.1.readsRunValue &&
        operand.1.mayFailOn (.plain 0) [] then
      throw (.restriction [item, 1] .constantFunctionError)
    else pure (position, assignedExpression (scope ++ around) position value operand.1)

/-- Resolve one {lit}`SET` assignment: {name}`resolveAssignmentTraced` without its trace. -/
def resolveAssignment (dqs : Bool) (scope : Scope) (shapes : SubqueryShapes) (keyColumns : List Nat)
    (generated : Identifier → ValueIssue) (rowid : Option (Option Nat)) (item : Nat) (around : Scope := []) :
    Identifier × Syntax.Expr → Except ValueIssue (Nat × Resolved.Expr) :=
  fun assignment => (resolveAssignmentTraced dqs scope shapes keyColumns generated rowid item around assignment).drop

end Belay.Sqlite.Model
