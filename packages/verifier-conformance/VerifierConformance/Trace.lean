import Belay.Sqlite.Model.SqlExecution

/-! ADR 0004 observations follow production transitions, including open transactions.
An observation holds the database itself, with its catalog, so the schema after each
statement comes from execution. This module neither executes SQLite nor asserts native
correspondence. -/

namespace Belay.Sqlite.Model.Conformance

/-- Insert a row in physical order using structural recursion the kernel reduces. -/
def insertByRowid (row : Row) : List Row → List Row
  | [] => [row]
  | head :: rest =>
    if row.rowid ≤ head.rowid then row :: head :: rest else head :: insertByRowid row rest

/-- Rows in rowid order, so storage order does not affect a comparison.
ponytail: quadratic sorting suits small fixtures; replace with a kernel-reducible
merge sort if measured corpus sizes make this a bottleneck. -/
def sortRows (rows : List Row) : List Row := rows.foldr insertByRowid []

/-- Observe a database: its catalog, and the rows of each object in rowid order. -/
def observeDatabase (database : Database) : Database :=
  { database with rows := database.rows.map sortRows }

/-- A snapshot preserves both views and the exact modeled failure position. -/
structure Observation where
  visible : Database
  persisted : Database
  transactionOpen : Bool
  error : Option (Nat × ExecutionError)
  deriving Repr, DecidableEq

/-- Observe terminal and intermediate outcomes using the production view helpers. -/
def observeOutcome (outcome : Outcome) : Observation :=
  { visible := observeDatabase outcome.database
    persisted := observeDatabase outcome.persistedDatabase
    transactionOpen := match outcome with | .pending .. => true | _ => false
    error := match outcome with
      | .success _ => none
      | .failure position reason _ => some (position, reason)
      | .pending _ _ error => error }

/-- An intermediate state is observed without closing or committing its transaction. -/
def observeState (state : SqlState) : Observation :=
  observeOutcome (state.finish (.success state.database))

end Belay.Sqlite.Model.Conformance
