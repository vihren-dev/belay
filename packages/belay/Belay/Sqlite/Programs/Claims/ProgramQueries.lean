import Lean.Elab.Tactic.Basic
import Belay.Sqlite.Programs.Reasoning.Program

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite.Model Lean Elab Tactic

/-- The value of {lit}`query` for the output of its statement:

* {name}`Output.rows`: the rows;
* {name}`Output.done`: no rows;
* {name}`Output.error`: the error code;
* {name}`Output.oneOf`: the first result, in the order of {name}`compareResults`, so that the run of
  a program is one run that SQLite permits; no rows for a list without results;
* {name}`Output.unmodeled`: no rows. A run does not give this output to a program; it ends the
  program. -/
def queryResult : Output → Except Nat (List (List Value))
  | .rows rows => .ok rows
  | .done _ => .ok []
  | .error code => .error code
  | .oneOf results => .ok (results.headD [])
  | .unmodeled _ => .ok []

/-- The only value of a query result: {lit}`some v` for exactly one row of one column {lit}`v`,
and {lean}`(none : Option Value)` for no row, for more rows or columns, and for an error. -/
def singleValue : Except Nat (List (List Value)) → Option Value
  | .ok [[value]] => some value
  | .ok _ | .error _ => none

/-- The tactic that proves the argument {lit}`one` of {lit}`query` and {lit}`single`, or gives an
error that says what the argument must be. It tries {lit}`decide`, then {lit}`rfl`, because a
script with a value {lit}`$x` or with an argument holds a free variable, which {lit}`decide`
refuses. -/
elab "check_one_statement" : tactic => do
  try evalTactic (← `(tactic| first | decide | exact rfl))
  catch _ => throwError "query and single take a script of exactly one statement; send the other statements with send, or write each one in its own query"

/-- {lit}`query s`: the program that sends the statement of script {lit}`s`, a script of exactly
one statement; its value is the rows of the statement ({name}`queryResult`):
{lean}`(.ok [] : Except Nat (List (List Value)))` for a statement without rows, or
{lit}`.error code`. For example, {lit}`query (sql r"SELECT 1")` gives {lit}`.ok [[1]]`. -/
def query (script : Script) (one : script.statements.length = 1 := by check_one_statement) :
    Sql (Except Nat (List (List Value))) :=
  let (statement, values) := script.statements[0]'(by rw [one]; exact Nat.one_pos)
  .exec statement values fun output => .pure (queryResult output)

/-- {lit}`single s`: the program that sends the statement of script {lit}`s`, a script of
exactly one statement; its value is {lit}`some v` when the statement gives exactly one row of
one column {lit}`v`, and none for no row, for more rows or columns, and for an error
({name}`singleValue` of {name}`query`). Use {name}`query` to tell these cases apart. -/
def single (script : Script) (one : script.statements.length = 1 := by check_one_statement) : Sql (Option Value) :=
  (query script one).map singleValue

/-- Whether no output is an error ({name}`Output.isError`) or ends a run
({name}`Output.endsRun`). For example, {lit}`outputs.allOk` after {lit}`let outputs ← send s` tells
whether every statement of {lit}`s` succeeded. Dot notation finds it under {lit}`open Belay.Sqlite`. -/
def List.allOk (outputs : List Output) : Bool :=
  outputs.all fun output => !output.isError && !output.endsRun

end Belay.Sqlite
