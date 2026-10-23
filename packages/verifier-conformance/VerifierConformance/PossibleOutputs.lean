import VerifierConformance.Outputs
import Belay.Sqlite.Model.PossibleResults

set_option doc.verso true

/-! The results that SQLite may give for a statement's query (ADR 0018, D6) in the comparison of
outputs: the rows that SQLite gave, with the rows of each tie group of the native evidence in
normal form, must be one of the model's results ({lit}`Query.possibleResults`). -/

namespace Belay.Sqlite.Model.Conformance

/-- The results that SQLite may give for a statement, for a query that succeeds
({name}`Resolved.Query.possibleOn`); none for every other statement and for a query that fails. -/
def possibleOutput (clock : Int) (statement : Resolved.Statement) (before : SqlState) (transition : SqlTransition) :
    Option (List (List ResultRow)) :=
  match statement, transition with
  | .query query subqueries, .next _ => query.possibleOn clock before.database subqueries
  | .query .., .halt _ => none
  | .createTable .., _ | .createIndex .., _ | .createTrigger .., _ | .addColumn .., _ | .drop .., _ | .begin, _
  | .commit, _ | .rollback, _ | .insert .., _ | .upsert .., _ | .update .., _ | .delete .., _ | .prepareError _, _
  | .setting _, _ => none

/-- The rows of tie groups from the front of a result, each group's rows in normal form
({name}`Resolved.normalForm`), and the rows after the groups as they are. -/
def normalGroups : List OutputGroup → List ResultRow → List ResultRow
  | [], rows => rows
  | group :: groups, rows => Resolved.normalForm (rows.take group.count) ++ normalGroups groups (rows.drop group.count)

/-- The rows that SQLite gave in the model's normal form: with tie groups, each group's rows in
normal form ({name}`normalGroups`); without them, as SQLite promises no order, all rows. -/
def NativeOutput.normalRows (native : NativeOutput) : List ResultRow :=
  match native.groups with
  | some groups => normalGroups groups native.result.rows
  | none => Resolved.normalForm native.result.rows

/-- Whether the rows that SQLite gave are one of the model's results, when the model gives a list
({name}`possibleOutput`); true for a statement without one. -/
def NativeOutput.fits (native : NativeOutput) (possible : Option (List (List ResultRow))) : Bool :=
  possible.all (·.contains native.normalRows)

end Belay.Sqlite.Model.Conformance
