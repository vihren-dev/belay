import Belay.Sqlite.Model.Schema.Ddl.RenameEdits
import Belay.Sqlite.Model.Schema.Triggers.TriggerPrograms
import Belay.Sqlite.Model.Queries.Preparation.RenameDependents

set_option doc.verso true

/-! The views and triggers of the catalog under a rename (ADR 0019, D4). A view and a trigger are syntax that
resolves at each use, so SQLite rewrites their text. The model reads their names from the name trace of their
resolution over the catalog before the rename ({name}`Belay.Sqlite.Model.RenameRequest.edits`), and writes the new name at those
places. SQLite resolves each definition for this, so a definition that does not resolve is an error of the
rename, and so is a rewritten definition that does not resolve in the catalog after it. -/

namespace Belay.Sqlite.Model

open Syntax

/-- The failure as the resolution of the statement, which leaves the catalog as it is. -/
def RenameFailure.resolution (catalog : Catalog) : RenameFailure → StatementResolution
  | .restricted kind => restrict [] kind
  | .prepare error => prepareError catalog error

/-- The failure of an object: a prepare error of its definition that the rename reports
({name}`PrepareError.raisedByRename`) becomes the error of the object; any other prepare error is a
restriction, because the model then has no complete trace of the names of the definition; a restriction
stays. -/
def RenameFailure.inObject (kind : DependentKind) (name : Identifier) (phase : DependentPhase) :
    RenameFailure → RenameFailure
  | .restricted reason => .restricted reason
  | .prepare error =>
    if error.raisedByRename then .prepare (.dependentObject kind name phase error) else .restricted .alterRename

/-- Whether the view resolves over the catalog; the failure is the error of the view. -/
def checkView (context : ResolveContext) (catalog : Catalog) (name : Identifier) (phase : DependentPhase)
    (view : CatalogView) : Except RenameFailure Unit :=
  match (viewResolution context catalog view).drop with
  | .ok _ => .ok ()
  | .error issue => .error (issue.failure.inObject .view name phase)

/-- Whether the trigger at the position resolves over the catalog; the failure is the error of the trigger. -/
def checkTrigger (context : ResolveContext) (catalog : Catalog) (position : Nat) (name : Identifier)
    (phase : DependentPhase) (trigger : CatalogTrigger) : Except RenameFailure Unit :=
  match (resolveProgramTraced context catalog position trigger).drop with
  | .error restriction => .error (.restricted restriction.kind)
  | .ok (.error error) => .error ((RenameFailure.prepare error).inObject .trigger name phase)
  | .ok (.ok _) => .ok ()

/-- The view after the rename. The edits come from the resolution of the view over the catalog before the
rename; a view that does not resolve there is the error of the rename. -/
def renameView (context : ResolveContext) (catalog : Catalog) (request : RenameRequest) (name : Identifier)
    (view : CatalogView) : Except RenameFailure CatalogView := do
  let resolution := viewResolution context catalog view
  match resolution.drop with
  | .error issue => throw (issue.failure.inObject .view name .current)
  | .ok _ => pure ()
  let edits ← (request.edits false resolution.trace).mapError .restricted
  match view.renameAll edits with
  | some renamed => pure renamed
  | none => throw (.restricted .alterRename)

/-- The table and the {lit}`UPDATE OF` columns of a trigger on the renamed table after the rename: a table rename
writes the new name of the table; a column rename writes the new name of the column in the list of
{lit}`UPDATE OF`, where {lit}`oldColumn` is the name that the column had. -/
def CatalogTrigger.renameHeader (request : RenameRequest) (oldColumn : Identifier) (trigger : CatalogTrigger) :
    CatalogTrigger :=
  match request.target with
  | .table _ => { trigger with table := request.new }
  | .column _ _ => match trigger.event with
    | .update names => { trigger with event := .update (names.map fun name =>
        if name.sameName oldColumn then request.new else name) }
    | .insert | .delete => trigger

/-- The trigger at the position after the rename, as {name}`renameView` rewrites a view: the names of its
condition and body by the trace of its program, and its table and columns by their names. The rows
{lit}`NEW` and {lit}`OLD` have the columns of the table of the trigger, so they are renamed when that is the table
of the rename. -/
def renameTrigger (context : ResolveContext) (catalog : Catalog) (request : RenameRequest) (oldColumn : Identifier)
    (position : Nat) (name : Identifier) (trigger : CatalogTrigger) : Except RenameFailure CatalogTrigger := do
  let resolution := resolveProgramTraced context catalog position trigger
  match resolution.drop with
  | .error restriction => throw (.restricted restriction.kind)
  | .ok (.error error) => throw ((RenameFailure.prepare error).inObject .trigger name .current)
  | .ok (.ok _) => pure ()
  if trigger.body.any BodyStatement.hasConflictClauses then throw (.restricted .alterRename)
  let renamedTable := match request.target with
    | .table table | .column table _ => (catalog.findTable trigger.table).map (·.1) == some table
  let edits ← (request.edits renamedTable resolution.trace).mapError .restricted
  match trigger.renameAll edits with
  | some renamed => pure (if renamedTable then renamed.renameHeader request oldColumn else renamed)
  | none => throw (.restricted .alterRename)

end Belay.Sqlite.Model
