import Belay.Sqlite.SqlExecution

/-! ADR 0004 observations follow production transitions, including open transactions.
Tables are observed by catalog position up to a bound that the caller derives from
the resolution. This module neither executes SQLite nor asserts native
correspondence. -/

namespace Belay.Sqlite.Conformance

/-- The table at each catalog position below the bound, with rows in rowid order;
{name}`Option.none` where no table is stored. -/
abbrev Tables := List (Option Table)

/-- Insert a row in physical order using structural recursion the kernel reduces. -/
def insertByRowid (row : Row) : List Row → List Row
  | [] => [row]
  | head :: rest =>
    if row.rowid ≤ head.rowid then row :: head :: rest else head :: insertByRowid row rest

/-- Rows in rowid order, so storage order does not affect a comparison.
ponytail: quadratic sorting suits small fixtures; replace with a kernel-reducible
merge sort if measured corpus sizes make this a bottleneck. -/
def sortRows (rows : List Row) : List Row := rows.foldr insertByRowid []

/-- Observe the tables at positions below the bound, with rows in rowid order. -/
def observeTables (count : Nat) (database : Database) : Tables :=
  (List.range count).map fun position => (database position).map fun table =>
    { table with rows := sortRows table.rows }

/-- A snapshot preserves both views and the exact modeled failure position. -/
structure Observation where
  visible : Tables
  persisted : Tables
  transactionOpen : Bool
  error : Option (Nat × ExecutionError)
  deriving Repr, DecidableEq

/-- Observe terminal and intermediate outcomes using the production view helpers. -/
def observeOutcome (count : Nat) (outcome : Outcome) : Observation :=
  { visible := observeTables count outcome.database
    persisted := observeTables count outcome.persistedDatabase
    transactionOpen := match outcome with | .pending .. => true | _ => false
    error := match outcome with
      | .success _ => none
      | .failure position reason _ => some (position, reason)
      | .pending _ _ error => error }

/-- An intermediate state is observed without closing or committing its transaction. -/
def observeState (count : Nat) (state : SqlState) : Observation :=
  observeOutcome count (state.finish (.success state.database))

/-- Include the initial snapshot and each executed statement; a halt ends the trace. -/
def traceFrom (count : Nat) (position : Nat) (script : List Resolved.Statement)
    (state : SqlState) : List Observation :=
  observeState count state ::
    match script with
    | [] => []
    | statement :: rest => match advance position statement state with
      | .next next => traceFrom count (position + 1) rest next
      | .halt outcome => [observeOutcome count outcome]

/-- A complete case begins outside a transaction, just like runSql. -/
def trace (count : Nat) (script : List Resolved.Statement) (initial : Database) : List Observation :=
  traceFrom count 0 script { database := initial }

/-- Instrumentation ends at precisely the production evaluator's outcome. -/
theorem traceFrom_final (count : Nat) (position : Nat)
    (script : List Resolved.Statement) (state : SqlState) :
    (traceFrom count position script state).getLast? =
      some (observeOutcome count (runSqlFrom position script state)) := by
  induction script generalizing position state with
  | nil => simp [traceFrom, runSqlFrom, observeState]
  | cons statement rest ih =>
    cases h : advance position statement state with
    | next next =>
      simp [traceFrom, runSqlFrom, h, List.getLast?_cons, ih]
    | halt outcome => simp [traceFrom, runSqlFrom, h]

/-- Concrete conformance traces and verifier proofs refer to the same execution. -/
theorem trace_final (count : Nat) (script : List Resolved.Statement) (initial : Database) :
    (trace count script initial).getLast? =
      some (observeOutcome count (runSql script initial)) :=
  traceFrom_final count 0 script { database := initial }

end Belay.Sqlite.Conformance
