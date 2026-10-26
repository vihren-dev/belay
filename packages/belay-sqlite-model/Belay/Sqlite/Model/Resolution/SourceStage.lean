import Belay.Sqlite.Model.Resolution.Sources
import Belay.Sqlite.Model.Resolution.WriteStages

set_option doc.verso true

/-! The stage of a write that reads the sources of its subqueries, with the name trace. -/

namespace Belay.Sqlite.Model

/-- Run a stage of a write that fails with a source issue, then the stage that its value selects. A
missing table or a prepare error ends the resolution as a prepare error that keeps the catalog, and a
restriction as a model restriction. The paths of the occurrences and of the restrictions of the stage are
those of the statement already. -/
def Traced.sourceStage (catalog : Catalog) (step : Traced SourceIssue α) (next : α → TracedResolution) :
    TracedResolution :=
  match step.drop with
  | .error (.noSuchTable name) => ⟨prepareError catalog (.noSuchTable name), step.trace⟩
  | .error (.value issue) => ⟨issueResolution catalog [] issue, step.trace⟩
  | .ok value => ⟨(next value).drop, step.trace ++ (next value).trace⟩

/-- For every stage and continuation: the projection of a source stage is the choice on the projection
of the stage, as the write resolvers had it before the trace. Proof sketch: split on the result of the
stage; both sides are equal by definition. -/
@[traced_drop] theorem Traced.drop_sourceStage (catalog : Catalog) (step : Traced SourceIssue α)
    (next : α → TracedResolution) :
    (Traced.sourceStage catalog step next).drop = match step.drop with
      | .error (.noSuchTable name) => prepareError catalog (.noSuchTable name)
      | .error (.value issue) => issueResolution catalog [] issue
      | .ok value => (next value).drop := by
  unfold Traced.sourceStage
  split <;> rfl

end Belay.Sqlite.Model
