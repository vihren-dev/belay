import Belay

set_option doc.verso true

/-! Retain the output of a calm single-table scan, the output of a ready query and the
property of every possible result. The scan uses the exact query equation with its
six data checks. The other two statements use the general output projection. -/

namespace Belay.Sqlite.Model.ReplacedQueries
open Resolved

/-- Retain the original premises and conclusion of {lit}`runScriptStep_simpleTable_output`. -/
theorem runScriptStep_simpleTable_output (context : ResolveContext) (clock : Option Clock) (index : Nat)
    (connection : Connection) (statement : Syntax.Statement) (parameters : List Value) (position : Nat)
    (table : Table) (filter : Option Expr) (columns : List Resolved.Output) (names : List String)
    {afterState : ResolveState}
    (resolved : resolveStatement context connection.resolveState statement =
      .ok (.query (Query.simple [QuerySource.first position] filter columns names) [], afterState))
    (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query (Query.simple [QuerySource.first position] filter columns names) []).Calm) :
    (runScriptStep context clock index connection statement parameters).output =
      .rows (normalForm ((Query.simple [QuerySource.first position] filter columns names).results
        (EvalContext.bound parameters) (sourceRows table))) := by
  simp [runScriptStep_query_eq resolved, statementClock, calm.readsClock, calm.counterReads,
      Query.simpleTable_checks parameters present calm, List.eraseDups_cons, Resolved.stableSort,
      Resolved.insertStable, RunStep.output]

#print axioms runScriptStep_simpleTable_output

/-- Retain the original premises and conclusion of {lit}`runScriptStep_select`. -/
theorem runScriptStep_select (context : ResolveContext) (clock : Option Clock) (index : Nat)
    (connection : Connection) (statement : Syntax.Statement) (parameters : List Value) {query : Resolved.Query}
    {subqueries : List Resolved.Query} {after : ResolveState} {value : Int} {source : Resolved.SourceRows}
    {bound : Resolved.Query}
    (resolved : resolveStatement context connection.resolveState statement = .ok (.query query subqueries, after))
    (clocked : statementClock clock index (.query query subqueries) = some value)
    (ready : connection.SelectReady value parameters query subqueries source bound) :
    (runScriptStep context clock index connection statement parameters).output =
      Output.ofResults (bound.possibleResults (connection.queryContextAt value parameters query subqueries) source.rows) := by
  rw [runScriptStep_output, resolved]
  exact resolvedStepOutput_select clock index connection parameters clocked ready

#print axioms runScriptStep_select

/-- Retain the original premises and conclusion of {lit}`runScriptStep_select_returnsResult`. -/
theorem runScriptStep_select_returnsResult (context : ResolveContext) (clock : Option Clock) (index : Nat)
    (connection : Connection) (statement : Syntax.Statement) (parameters : List Value) {query : Resolved.Query}
    {subqueries : List Resolved.Query} {after : ResolveState} {value : Int} {source : Resolved.SourceRows}
    {bound : Resolved.Query}
    (resolved : resolveStatement context connection.resolveState statement = .ok (.query query subqueries, after))
    (clocked : statementClock clock index (.query query subqueries) = some value)
    (ready : connection.SelectReady value parameters query subqueries source bound)
    (property : List (List Value) → Prop) :
    (runScriptStep context clock index connection statement parameters).output.returnsResult property ↔
      ∀ result ∈ bound.possibleResults (connection.queryContextAt value parameters query subqueries) source.rows,
        property result := by
  rw [runScriptStep_select context clock index connection statement parameters resolved clocked ready,
    Output.returnsResult_ofResults]
  exact and_iff_right (Resolved.Query.possibleResults_ne_nil _ _ _)

#print axioms runScriptStep_select_returnsResult

end Belay.Sqlite.Model.ReplacedQueries
