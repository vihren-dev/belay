import Belay.Sqlite.Model.PossibleResultsLaws
import Belay.Sqlite.Model.SimpleResultsLaws
import Belay.Sqlite.Model.SimpleTableOutput

set_option doc.verso true

/-! The exact output of a calm simple query of one table (ADR 0017, S6): its step gives the rows
of the one result in normal form, whatever the clock and the index. A query without
{lit}`ORDER BY` has one tie group, so SQLite may give only that one result. -/

namespace Belay.Sqlite.Model

/-- For every nonempty list of records, the tie groups without {lit}`ORDER BY` terms are the records
as one group. Proof sketch: induction on the records; each record is equal to the first record of the
group after it, because no term separates them. -/
theorem Resolved.tieGroups_nil_directions : ∀ records : List Resolved.Record, records ≠ [] →
    Resolved.tieGroups [] records = [records]
  | [], h => absurd rfl h
  | [record], _ => by simp [Resolved.tieGroups]
  | record :: next :: more, _ => by
    have rest := Resolved.tieGroups_nil_directions (next :: more) (List.cons_ne_nil _ _)
    rw [Resolved.tieGroups, rest]
    simp [Resolved.compareSort]

/-- For every simple query, context and rows, the only result that SQLite may give is the normal
form of the one result of the model. Proof sketch: no term orders the records, so the sort keeps them
({name}`Resolved.stableSort_of_total`) and they are one group ({name}`Resolved.tieGroups_nil_directions`);
the window takes the whole group, which is its one choice. -/
theorem Resolved.Query.Simple.possibleResults_eq {query : Resolved.Query} (simple : query.Simple)
    (context : Resolved.EvalContext) (rows : List (List Value)) :
    query.possibleResults context rows = [Resolved.normalForm (query.results context rows)] := by
  have sorted : query.sortedRecords context rows = query.uniqueRecords context rows := by
    unfold Resolved.Query.sortedRecords
    exact Resolved.stableSort_of_total _ (by simp [simple.orderBy, Resolved.compareSort]) _
  have results : query.results context rows = (query.uniqueRecords context rows).map Prod.fst := by
    rw [Resolved.Query.results_window]
    simp [simple.offset, Resolved.Query.stop, simple.limit, Resolved.windowRows, sorted]
  unfold Resolved.Query.possibleResults Resolved.Query.tieGroupRows
  rw [sorted]
  simp only [simple.orderBy, List.map_nil]
  by_cases empty : query.uniqueRecords context rows = []
  · simp [empty, results, Resolved.tieGroups, Resolved.windowChoices, Resolved.choiceResults,
      Resolved.distinctLists, Resolved.normalForm, Resolved.stableSort]
  · rw [Resolved.tieGroups_nil_directions _ empty]
    simp [results, Resolved.windowChoices, simple.offset, Resolved.Query.stop, simple.limit,
      Resolved.groupChoices, Resolved.groupSlice, Resolved.windowRows, Resolved.choiceResults,
      Resolved.distinctLists]

/-- For every result, the output of the only possible result is that result as rows. Proof sketch:
one result has no repeat, and the sort of one item keeps it. -/
theorem Output.ofResults_singleton (result : List (List Value)) : Output.ofResults [result] = .rows result := by
  have erased : [result].eraseDups = [result] := by simp [List.eraseDups_cons]
  simp [Output.ofResults, erased, Resolved.stableSort, Resolved.insertStable]

/-- For every statement that reads no clock, the output of its step does not depend on the clock
of the run or on the index. Proof sketch: such a statement runs at the clock value 0 whatever the
clock is ({name}`statementClock`). -/
theorem resolvedStepOutput_clock_free (clock : Option Clock) (index : Nat) (connection : Connection)
    (parameters : List Value) (statement : Resolved.Statement) (noClock : statement.readsClock = false) :
    resolvedStepOutput clock index connection parameters statement =
      resolvedStepOutput none index connection parameters statement := by
  simp only [resolvedStepOutput, statementClock, noClock, Bool.false_eq_true, ite_false]

/-- For every connection, values and calm statement of a simple query without subqueries, over source
rows of the query that have no fault, the output of its step with any clock and index is the rows of the
one result of the query over those rows, in normal form, with the values bound to the parameters. Proof
sketch: {name}`resolvedStepOutput_query`; the statement has no fault, so the model describes it and
{name}`Resolved.Query.outputOn_clean` gives the possible results of
{name}`Resolved.Query.Simple.possibleResults_eq`. -/
theorem resolvedStepOutput_simple_rows (clock : Option Clock) (index : Nat) (connection : Connection)
    (parameters : List Value) (query : Resolved.Query) (simple : query.Simple) (source : Resolved.SourceRows)
    (calm : (Resolved.Statement.query query []).Calm)
    (found : ∀ context, query.source context connection.state.database = some source)
    (clean : source.fault = .none) :
    resolvedStepOutput clock index connection parameters (.query query []) =
      .rows (Resolved.normalForm (query.results (Resolved.EvalContext.bound parameters) source.rows)) := by
  have context := Connection.queryContext_of_calm connection parameters query calm
  have run := simple.run_of_faultless (connection.queryContext parameters query []) calm.query_plain source.rows
    (calm.faultless_nil connection parameters)
  rw [resolvedStepOutput_clock_free clock index _ _ _ calm.readsClock,
    resolvedStepOutput_query index connection parameters query [] calm.readsClock (calm.firstUnknown _)]
  have hrun := connection.runOn_of_found parameters query [] source (found _)
  have described : query.described 0
      (connection.state.counters.view (Resolved.Statement.query query []).counterReads) parameters
      connection.state.database [] = true := by
    unfold Resolved.Query.described
    rw [hrun, run]
    simp [calm.subqueries_plain, clean]
  split
  · rw [Resolved.Query.outputOn_clean query 0 _ parameters connection.state.database [] source query (found _)
        (simple.bindWindow parameters) (by rw [run]) (by rw [run]) (by rw [run]; simp),
      simple.possibleResults_eq, Output.ofResults_singleton]
    exact congrArg (fun context => Output.rows (Resolved.normalForm (query.results context source.rows))) context
  · rename_i notDescribed
    exact absurd described notDescribed

/-- For every connection, values, table at a catalog position of the database of the connection,
and calm statement of the simple query of that table, the output of its step with any clock and index
is the rows of the one result of the query over the scan of the table, in normal form, with the values
bound to the parameters. Proof sketch: {name}`resolvedStepOutput_simple_rows` with the source rows of
{name}`Resolved.Query.source_first`. -/
theorem resolvedStepOutput_simpleTable_rows (clock : Option Clock) (index position : Nat)
    (connection : Connection) (parameters : List Value) (table : Table) (condition : Option Resolved.Expr)
    (columns : List Resolved.Output) (names : List String)
    (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query
      (Resolved.Query.simple [Resolved.QuerySource.first position] condition columns names) []).Calm) :
    resolvedStepOutput clock index connection parameters
      (.query (Resolved.Query.simple [Resolved.QuerySource.first position] condition columns names) []) =
      .rows (Resolved.normalForm ((Resolved.Query.simple [Resolved.QuerySource.first position] condition columns
        names).results (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table))) :=
  resolvedStepOutput_simple_rows clock index connection parameters _ (Resolved.Query.simple_isSimple _ _ _ _)
    { rows := Resolved.sourceRows table, width := table.shape.columns.length, fault := .none } calm
    (fun context => Resolved.Query.source_first context _ connection.state.database position table rfl present) rfl

end Belay.Sqlite.Model
