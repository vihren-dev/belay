import Belay.Sqlite.Model.Shared.Execution.Execution

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The state of a write that checks foreign keys: the stored rows of each catalog position,
the counter of violations, the positions of the tables that the actions changed, and the rows
that the statement itself wrote, in order. The catalog does not change during the write, so it
is not part of the state. Start from the rows of the input database with the other fields
empty. -/
structure KeyState where
  /-- The stored rows of each catalog position so far ({name}`Database.rows`). -/
  rows : List (List Row)
  /-- SQLite's counter of immediate foreign-key violations ({lit}`nFkConstraint`). -/
  counter : Int := 0
  /-- The catalog positions of the tables whose rows an action changed. -/
  acted : List Nat := []
  /-- The rows that the statement wrote: the new rows of INSERT and UPDATE, the old rows of
  DELETE. -/
  written : List Row := []
  /-- Whether a statement of a trigger's body with subqueries ran (ADR 0018, D5), whose
  subqueries read the tables while the write changes them. -/
  subqueried : Bool := false
  /-- The rows that the write at the current level counted: the rows that it inserted, updated
  or deleted, except the rows that REPLACE deletes (ADR 0024, D2). At the top level they are the
  rows of {lit}`changes()`. -/
  own : Nat := 0
  /-- The rows of the nested writes of programs and actions that completed, which count for
  {lit}`total_changes()` also when the statement fails later. -/
  credited : Nat := 0
  /-- The rowid of the last row that the statement itself inserted into a table with a rowid,
  which {lit}`last_insert_rowid()` takes; none when it inserted none. -/
  inserted : Option Int := none

/-- The failure of a row that stops the statement and keeps the rows that it reached: the FAIL
algorithm or the ROLLBACK algorithm of a failed constraint or of {lit}`RAISE`. -/
inductive StopAlgorithm where
  /-- FAIL ({lean}`ExecutionError.constraintFail`). -/
  | fail
  /-- ROLLBACK ({lean}`ExecutionError.constraintRollback`). -/
  | rollback
  deriving Repr, DecidableEq

/-- Why a write that runs row by row stops: the error of the statement, a FAIL or ROLLBACK
failure with the state that it reached, or a case that the model does not describe, such as
writes nested deeper than the fuel. -/
inductive KeyStop where
  /-- The statement fails with the error and keeps nothing; the state is the state when it
  failed, which gives its counts (ADR 0024, D2). -/
  | error (reason : ExecutionError) (state : KeyState)
  /-- The statement stops with the algorithm and the state that it reached. -/
  | stopped (algorithm : StopAlgorithm) (state : KeyState)
  /-- The model does not describe the statement on the database. -/
  | undescribed

end Belay.Sqlite.Model
