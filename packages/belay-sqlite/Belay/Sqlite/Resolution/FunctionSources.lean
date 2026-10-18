import Belay.Sqlite.Resolution.Sources

set_option doc.verso true

/-! Resolution of the {lit}`json_each` sources of {lit}`FROM` (ADR 0012, amendment 5, slice
6d; ADR 0013, D5): the reference and its columns, and its arguments, which read the
sources before it. The paths follow {lit}`Syntax.Statement.select` as in
{lit}`Sources.lean`; in a source, child 2 is the list of its arguments. -/

namespace Belay.Sqlite

/-- The columns of {lit}`json_each` in SQLite's order, without declared types: the eight
that {lit}`*` shows, then the hidden {lit}`json` and {lit}`root`. -/
def eachColumns : List CatalogColumn :=
  ["key", "value", "type", "atom", "id", "parent", "fullkey", "path", "json", "root"].map
    fun name => { name, declaredType := none }

/-- The positions of the hidden columns {lit}`json` and {lit}`root` in
{name}`eachColumns`. -/
def eachHidden : List Nat := [8, 9]

/-- The largest number of arguments of {lit}`json_each` that SQLite accepts: the JSON and
the path ({lit}`too many arguments on json_each() - max 2`). -/
def maximumEachArguments : Nat := 2

/-- The source of one {lit}`json_each` reference at {lit}`path` with its arguments as
written, or the issue of a form that the model does not describe: another function or no
argument ({name}`RestrictionKind.tableFunction`), and more than
{name}`maximumEachArguments` arguments, which SQLite refuses. Its name is the alias, else
{lit}`json_each`, as SQLite names it in messages; two of its columns are hidden. -/
def eachReference (path : List Nat) (reference : Syntax.TableReference) (arguments : List Syntax.Expr) :
    Except ValueIssue ScopeSource :=
  if normalizeIdentifier reference.table != "json_each" || arguments.isEmpty then
    .error (.restriction path .tableFunction)
  else if arguments.length > maximumEachArguments then .error (.prepare .tooManyEachArguments)
  else .ok { name := reference.alias.getD "json_each", columns := eachColumns, hidden := eachHidden }

/-- Resolve the arguments of the {lit}`json_each` source at {lit}`index` of the scope, whose
reference is at {lit}`path`: each argument resolves over the whole scope, as SQLite does,
and then must read only the sources before it
({name}`RestrictionKind.laterSourceInArguments`). The first argument is the JSON and the
second, if any, the path. -/
def resolveEachArguments (dqs : Bool) (scope : Scope) (index : Nat) (path : List Nat)
    (arguments : List Syntax.Expr) : Except ValueIssue Resolved.Source := do
  let bound := (scope.take index).foldl (fun width source => width + source.columns.length) 0
  let resolved ← resolveAll (fun position argument => do
    let (resolved, _) ← (resolveOperand dqs scope true argument).mapError (·.under (path ++ [2, position]))
    if resolved.readsBelow bound then .ok resolved
    else .error (.restriction (path ++ [2, position]) .laterSourceInArguments)) arguments
  match resolved with
  | json :: rest => .ok (.each json rest.head?)
  | [] => .error (.restriction path .tableFunction)

end Belay.Sqlite
