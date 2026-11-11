import Belay.Sqlite.Model.Programs.Claims.SelectExecutionRule
import Belay.Sqlite.Model.Tooling.Counterexamples.OutputResultsLaws

set_option doc.verso true

/-! The execution rule of a SELECT (ADR 0027, D5): the output of the step of a query statement
that the model describes, with no fault and a bound window, is the output of every result that
the model permits ({name}`Belay.Sqlite.Model.Resolved.Query.possibleResults`). Its premises are the
readiness conditions of the step: the source rows, no possible fault of the source or of a
nested subquery, and a run without mismatch, overflow or fault. A pure-value proof cannot drop
them: {name}`Belay.Sqlite.Model.Resolved.Query.outputOn_clean` alone permits a possible fault. -/

namespace Belay.Sqlite.Model

/-- For every resolution context, clock, index, connection, statement, values and property
{lit}`Q` of a result, under the premises of {name}`runScriptStep_select`: the output of the step
returns a result with {lit}`Q` ({name}`Output.returnsResult`) exactly when every result that
the model permits has {lit}`Q`. Proof sketch: {name}`Output.returnsResult_ofResults`; the list of
possible results is not empty ({name}`Resolved.Query.possibleResults_ne_nil`). -/
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

end Belay.Sqlite.Model
