import VerifierConformance.Native
import Belay.Sqlite.Model.ScriptRun
import Belay.Sqlite.Model.QueryStepOutput

set_option doc.verso true

/-! Native-style observations of stored views. The ordinary resolver supplies their
current columns and the ordinary statement runner supplies their rows. Observation
does not write those rows into the database or change the caller's connection. -/

namespace Belay.Sqlite.Model.Conformance

/-- Why an observation cannot supply a view. SQL preparation and execution failures
remain failures; a model restriction or unavailable context remains explicitly unmodeled. -/
inductive ViewObservationIssue where
  /-- The ordinary query resolver refused the view or its body. -/
  | resolution (issue : SourceIssue)
  /-- The ordinary runner returned an error or an unmodeled result. -/
  | output (output : Output)
  /-- The observer received an unexpected source shape. -/
  | shape
  /-- An issue of the named view; the report names the view so that the user can repair it. -/
  | named (view : Identifier) (issue : ViewObservationIssue)
  deriving DecidableEq

/-- SQLite's primary result code for an SQL error: it also reports a view that cannot be
prepared. -/
def sqlErrorCode : Nat := 1

/-- The primary result code that SQLite gives when it reads a view that fails, or none when
the observation is unavailable for another reason. A preparation failure of the view or of its
body, such as a missing table or a cycle, and an error of its execution are failures that
SQLite reports and that a recording keeps; a model restriction and an unmodeled output are not,
so they stay out of scope. -/
def ViewObservationIssue.failureCode : ViewObservationIssue → Option Nat
  | .named _ issue => issue.failureCode
  | .resolution (.value (.prepare _)) | .resolution (.noSuchTable _) => some sqlErrorCode
  | .resolution (.value (.restriction ..)) => none
  | .output (.error code) => some code
  | .output (.rows _) | .output (.oneOf _) | .output (.done _) | .output (.unmodeled _) | .shape => none

/-- Rows of a readable view. All alternatives must have the same complete multiset;
ordering differences are removed with {name}`Resolved.normalForm`. Distinct multisets,
an empty alternative list and a non-query output cannot supply one native snapshot. -/
def viewObservationRows : Output → Except ViewObservationIssue (List (List Value))
  | .rows rows => .ok rows
  | .oneOf (first :: rest) =>
    if rest.all (fun rows => Resolved.normalForm rows == Resolved.normalForm first) then .ok first
    else .error (.output (.unmodeled "view observation has more than one possible row multiset"))
  | .oneOf [] => .error (.output (.unmodeled "view observation has no possible result"))
  | output@(.done _) | output@(.error _) | output@(.unmodeled _) => .error (.output output)

/-- Observe the current columns and rows of a named view through {lit}`SELECT * FROM` that view.
Use the writer's actual counters for a visible snapshot and new-connection counters
for the separate committed reader while a transaction is open. An omitted clock is
unknown, not time zero: a clock-reading view then returns an unmodeled issue.
Broken views retain their preparation or execution failure. -/
def observeView (profile : Profile) (clock : Option Int) (counters : Counters)
    (database : Database) (name : Identifier) : Except ViewObservationIssue NativeTable := do
  let written : Syntax.Subquery :=
    { columns := [.star], source := some { table := name, alias := none }, joins := [], filter := none,
      groupBy := [], orderBy := [], limit := none, offset := none, parent := none }
  let (query, subqueries, scope) ←
    (resolveSelectDetails { profile, mode := .execution } database.catalog written []).mapError .resolution
  let [source] := scope | throw .shape
  let output := resolvedStepOutput (clock.map fun value _ => value) 0
    { state := { database, counters } } [] (.query query subqueries)
  let rows ← viewObservationRows output
  let columns : List NativeColumn := source.columns.map fun column =>
    { name := column.name, declaredType := column.declaredType.getD "", notNull := false,
      defaultValue := none }
  pure {
    name, columns, primaryKey := [], uniqueKeys := [], indexes := [],
    rows := rows.map fun values => { rowid := 0, values } }

end Belay.Sqlite.Model.Conformance
