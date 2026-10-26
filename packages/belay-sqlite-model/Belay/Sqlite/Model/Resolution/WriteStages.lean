import Belay.Sqlite.Model.Resolution.Context
import Belay.Sqlite.Model.Resolution.SourceRecords
import Belay.Sqlite.Model.Resolution.TracedList
import Belay.Sqlite.Model.Resolution.ReservedNames

set_option doc.verso true

/-! The steps of a write with the name trace. INSERT, UPDATE and DELETE resolve their parts in
stages: a stage that fails with a value issue ends the resolution with that issue, a stage that
works gives its value to the next stage. The trace of a stage holds the occurrences of its
names below the node of the stage, also when the stage fails. -/

namespace Belay.Sqlite.Model

/-- The traced resolution of one statement: the resolved statement and the catalog after it, or a
model restriction inside the statement, with the names that were decided. -/
abbrev TracedResolution := Traced NodeRestriction (Resolved.Statement × Catalog)

/-- Run a stage of a write at the child {lit}`path` of the statement, then the stage that its value
selects. A value issue ends the resolution as {name}`issueResolution` gives it: a prepare error or a
restriction at the path of the stage. The trace holds the occurrences of the stage below its path,
and, when the stage works, those of the stages after it. -/
def Traced.stage (catalog : Catalog) (path : List Nat) (step : Traced ValueIssue α)
    (next : α → TracedResolution) : TracedResolution :=
  match step.drop with
  | .error issue => ⟨issueResolution catalog path issue, step.trace.map (NameOccurrence.under path)⟩
  | .ok value => ⟨(next value).drop, step.trace.map (NameOccurrence.under path) ++ (next value).trace⟩

/-- For every stage and continuation: the projection of a stage is the choice on the projection of
the stage, as the write resolvers had it before the trace. Proof sketch: split on the result of the
stage; both sides are equal by definition. -/
@[traced_drop] theorem Traced.drop_stage (catalog : Catalog) (path : List Nat) (step : Traced ValueIssue α)
    (next : α → TracedResolution) :
    (Traced.stage catalog path step next).drop = match step.drop with
      | .error issue => issueResolution catalog path issue
      | .ok value => (next value).drop := by
  unfold Traced.stage
  cases step.drop <;> rfl

/-- The occurrence of the table that a write names, at child 0 of the statement. The table is a
source of kind {name}`SourceKind.baseTable` or {name}`SourceKind.storedView` with its catalog
position, else missing with the tables and views of the catalog as candidates; a name of one of
SQLite's own tables is refused when {lit}`refusesSystem` is true. -/
def writeTargetOccurrence (catalog : Catalog) (table : Identifier) (refusesSystem : Bool) : NameOccurrence :=
  let declared := fun position => (catalog[position]?.map (·.name)).getD table
  tableOccurrence [] table
    (match catalog.findTable table with
      | some (position, _) => .source { kind := .baseTable, name := declared position, index := 0, depth := 0,
                                          position := some position }
      | none => match catalog.findView table with
        | some (position, _) => .source { kind := .storedView, name := declared position, index := 0, depth := 0,
                                            position := some position }
        | none => if refusesSystem && reservedName table then .unreached .refused
          else .missing .error catalog.referenceCandidates)

/-- Look up the table of a write and record it ({name}`writeTargetOccurrence`). A table of the
catalog goes on with {lit}`found`, which gets its catalog position and the table; a view is
{lit}`viewCase`; any other name is {lit}`missingCase`. -/
def Traced.withTarget (catalog : Catalog) (table : Identifier) (refusesSystem : Bool)
    (viewCase missingCase : TracedResolution) (found : Nat → CatalogTable → TracedResolution) :
    TracedResolution :=
  let rest : TracedResolution := match catalog.findTable table with
    | some (position, entry) => found position entry
    | none => if (catalog.findView table).isSome then viewCase else missingCase
  ⟨rest.drop, writeTargetOccurrence catalog table refusesSystem :: rest.trace⟩

/-- For every lookup: the projection of a lookup is the choice on the catalog, as the write
resolvers had it before the trace. Proof sketch: split on the lookup; both sides are equal by definition. -/
@[traced_drop] theorem Traced.drop_withTarget (catalog : Catalog) (table : Identifier) (refusesSystem : Bool)
    (viewCase missingCase : TracedResolution) (found : Nat → CatalogTable → TracedResolution) :
    (Traced.withTarget catalog table refusesSystem viewCase missingCase found).drop =
      match catalog.findTable table with
      | some (position, entry) => (found position entry).drop
      | none => if (catalog.findView table).isSome then viewCase.drop else missingCase.drop := by
  unfold Traced.withTarget
  dsimp only
  split
  · rfl
  · split <;> rfl

end Belay.Sqlite.Model
