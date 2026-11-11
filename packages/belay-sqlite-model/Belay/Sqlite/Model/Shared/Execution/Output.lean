import Belay.Sqlite.Model.Shared.Execution.PossibleResults
import Belay.Sqlite.Model.Shared.Execution.StatementOutput

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The output of one statement. For example, an UPDATE that changes one row gives
{lean}`Output.done 1`, and a query with one row of one integer gives
{lean}`Output.rows [[.integer 1]]`. -/
inductive Output where
  /-- A statement that returns rows: a query, or a write with {lit}`RETURNING`. Without an
  order that SQLite promises, the rows are in the normal form ({name}`Resolved.normalForm`). -/
  | rows (rows : List (List Value))
  /-- A statement that returns no rows, with the number of rows that it changed: 0 for a
  statement that is not INSERT, UPDATE or DELETE. -/
  | done (changes : Nat)
  /-- A statement that failed, with SQLite's primary result code
  ({name}`ExecutionError.primaryCode`). -/
  | error (code : Nat)
  /-- A query whose rows depend on an order that SQLite does not promise, with one entry for
  each result that SQLite may give, in a fixed order ({lit}`compareResults`). -/
  | oneOf (results : List (List (List Value)))
  /-- A statement that the model does not describe, with the reason. A run stops at it. -/
  | unmodeled (reason : String)
  deriving DecidableEq

/-- Whether the output ends a run: only {name}`Output.unmodeled` does. -/
def Output.endsRun : Output → Bool
  | .unmodeled _ => true
  | .rows _ | .done _ | .error _ | .oneOf _ => false

/-- Whether the output is a statement's error: only {name}`Output.error` is. -/
def Output.isError : Output → Bool
  | .error _ => true
  | .rows _ | .done _ | .oneOf _ | .unmodeled _ => false

/-- The reason of a statement whose run the model does not describe on the database: its
support check fails, or it writes to a position without a table. -/
def unmodeledHere : String :=
  "the model does not describe what SQLite does for this statement on this database"

/-- The order of two results of a query: row by row by {name}`Resolved.compareRows`, a result
with fewer rows first when its rows begin the other. -/
def compareResults : List (List Value) → List (List Value) → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | first :: rest, other :: others => (Resolved.compareRows first other).then (compareResults rest others)

/-- The output of a query from the results that SQLite may give for it: one result as
{name}`Output.rows`, more than one different result as {name}`Output.oneOf`, each result
once, sorted by {name}`compareResults`, so that the output does not depend on the order in
which the model finds the results. -/
def Output.ofResults (results : List (List (List Value))) : Output :=
  match Resolved.stableSort (fun a b => (compareResults a b).isLE) results.eraseDups with
  | [result] => .rows result
  | [] => .unmodeled "the model gives no result for this query"
  | first :: second :: rest => .oneOf (first :: second :: rest)

/-- Whether a write statement returns rows: a write with {lit}`RETURNING` expressions. -/
def Resolved.Statement.returnsRows : Resolved.Statement → Bool
  | .insert _ _ returning .. | .upsert _ _ _ returning .. | .insertSelect _ _ _ _ returning .. | .update _ _ _ returning .. | .delete _ _ returning .. =>
    !returning.isEmpty
  | .createTable .. | .createView .. | .createIndex .. | .createTrigger .. | .addColumn .. | .rewrite _ | .dropColumn .. | .drop .. | .begin | .commit
  | .rollback | .prepareError _ | .query .. | .setting .. => false

end Belay.Sqlite.Model
