import Belay.Sqlite.Model.Queries.Preparation.RenameEdits
import Belay.Sqlite.Model.Queries.Preparation.RenameVerdict
import Belay.Sqlite.Model.Queries.Preparation.TriggerPrograms

set_option doc.verso true

namespace Belay.Sqlite.Model

open Syntax

/-- Why a rename does not run: a restriction of the model, or a prepare error of SQLite. -/
inductive RenameFailure where
  /-- The model does not describe how SQLite renames the names of the definition. -/
  | restricted (kind : RestrictionKind)
  /-- SQLite reports the error and changes nothing. -/
  | prepare (error : PrepareError)

/-- The failure that an issue of the resolution of a query is. -/
def SourceIssue.failure : SourceIssue → RenameFailure
  | .noSuchTable name => .prepare (.noSuchTable name)
  | .value (.prepare error) => .prepare (.expression error)
  | .value (.restriction _ kind) => .restricted kind

/-- The result of the resolution of the query of a view over a catalog, with the name trace. -/
def viewResolution (context : ResolveContext) (catalog : Catalog) (view : CatalogView) :
    Traced SourceIssue (Resolved.Query × List Resolved.Query × Scope) :=
  resolveSelectDetailsTraced context catalog view.query view.subqueries

/-- Whether the statement is an INSERT with {lit}`ON CONFLICT` clauses. The names of a clause (its target and its
update) are not on the paths of the trace, so a rename of such a trigger is a restriction of the model. -/
def BodyStatement.hasConflictClauses : BodyStatement → Bool
  | .insert _ _ _ conflicts _ _ => !conflicts.isEmpty
  | .update .. | .delete .. | .select .. => false

end Belay.Sqlite.Model
