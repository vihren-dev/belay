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

/-- Every result a query permits has the property exactly when its normalized output returns
the property. A bound query always permits at least one result. -/
theorem Resolved.Query.returnsResult_possible (bound : Resolved.Query) (context : Resolved.EvalContext)
    (rows : List (List Value)) (property : List (List Value) → Prop) :
    (Belay.Sqlite.Model.Output.ofResults (bound.possibleResults context rows)).returnsResult property ↔
      ∀ result ∈ bound.possibleResults context rows, property result := by
  rw [Output.returnsResult_ofResults]
  exact and_iff_right (Resolved.Query.possibleResults_ne_nil _ _ _)

end Belay.Sqlite.Model
