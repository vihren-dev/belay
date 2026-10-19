import Belay.Sqlite.SqlExecution

/-! ADR 0004 observations follow production transitions, including open transactions.
An observation holds the database itself, with its catalog, so the schema after each
statement comes from execution. This module neither executes SQLite nor asserts native
correspondence. -/

namespace Belay.Sqlite.Conformance

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

/-- Include the initial snapshot and each executed statement; a halt ends the trace. -/
def traceFrom (position : Nat) (script : List Resolved.Statement)
    (state : SqlState) : List Observation :=
  observeState state ::
    match script with
    | [] => []
    | statement :: rest => match advance position statement state with
      | .next next => traceFrom (position + 1) rest next
      | .halt outcome => [observeOutcome outcome]

/-- A complete case begins outside a transaction, just like runSql. -/
def trace (script : List Resolved.Statement) (initial : Database) : List Observation :=
  traceFrom 0 script { database := initial }

/-- Instrumentation ends at precisely the production evaluator's outcome. -/
theorem traceFrom_final (position : Nat)
    (script : List Resolved.Statement) (state : SqlState) :
    (traceFrom position script state).getLast? =
      some (observeOutcome (runSqlFrom position script state)) := by
  induction script generalizing position state with
  | nil => simp [traceFrom, runSqlFrom, observeState]
  | cons statement rest ih =>
    cases h : advance position statement state with
    | next next =>
      simp [traceFrom, runSqlFrom, h, List.getLast?_cons, ih]
    | halt outcome => simp [traceFrom, runSqlFrom, h]

/-- Concrete conformance traces and verifier proofs refer to the same execution. -/
theorem trace_final (script : List Resolved.Statement) (initial : Database) :
    (trace script initial).getLast? =
      some (observeOutcome (runSql script initial)) :=
  traceFrom_final 0 script { database := initial }

end Belay.Sqlite.Conformance
