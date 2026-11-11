import Belay.Sqlite.Model.Frontend.Codecs.Resolution
import Belay.Sqlite.Model.Queries.Preparation.RestrictionText
import Belay.Sqlite.Model.Queries.Preparation.SchemaScript

set_option doc.verso true

/-! JSON transport and closed kernel terms for statement syntax, catalogs and
resolved statements, and the structural record of a schema and a script. A
program that maps SQL text to statements writes the record, and a program that
resolves the statements reads it. -/

namespace Belay.Sqlite.Model

deriving instance Lean.ToJson for ViewError

deriving instance Lean.ToJson for DropColumnError
deriving instance Lean.ToJson for CommonTableError
deriving instance Lean.ToJson for ExprError

/-- A prepare error as JSON, in one flat form: a statement error as its own constructor, and an {name}`ExprError` as that error's constructor, so the wire form
does not show the split of the two types. For example, {lit}`no such table: t` is
{lit}`{"noSuchTable": {"name": "t"}}` and {lit}`no such column: a` is
{lit}`{"noSuchColumn": {"name": "a"}}`, the derived form of each constructor. -/
def PrepareError.toJson : PrepareError → Lean.Json
    | .viewVariables => Lean.Json.str "viewVariables"
    | .tableExists name => Lean.Json.mkObj [("tableExists", Lean.Json.mkObj [("name", Lean.toJson name)])]
    | .viewExists name => Lean.Json.mkObj [("viewExists", Lean.Json.mkObj [("name", Lean.toJson name)])]
    | .indexNameUsed name => Lean.Json.mkObj [("indexNameUsed", Lean.Json.mkObj [("name", Lean.toJson name)])]
    | .tableNameUsed name => Lean.Json.mkObj [("tableNameUsed", Lean.Json.mkObj [("name", Lean.toJson name)])]
    | .indexExists name => Lean.Json.mkObj [("indexExists", Lean.Json.mkObj [("name", Lean.toJson name)])]
    | .noSuchTable name => Lean.Json.mkObj [("noSuchTable", Lean.Json.mkObj [("name", Lean.toJson name)])]
    | .noSuchView name => Lean.Json.mkObj [("noSuchView", Lean.Json.mkObj [("name", Lean.toJson name)])]
    | .useDropTable name => Lean.Json.mkObj [("useDropTable", Lean.Json.mkObj [("name", Lean.toJson name)])]
    | .useDropView name => Lean.Json.mkObj [("useDropView", Lean.Json.mkObj [("name", Lean.toJson name)])]
    | .noSuchIndex name => Lean.Json.mkObj [("noSuchIndex", Lean.Json.mkObj [("name", Lean.toJson name)])]
    | .tableMayNotBeDropped name =>
      Lean.Json.mkObj [("tableMayNotBeDropped", Lean.Json.mkObj [("name", Lean.toJson name)])]
    | .noSuchReferencedTable name =>
      Lean.Json.mkObj [("noSuchReferencedTable", Lean.Json.mkObj [("name", Lean.toJson name)])]
    | .foreignKeyMismatch child parent =>
      Lean.Json.mkObj [("foreignKeyMismatch", Lean.Json.mkObj [("child", Lean.toJson child), ("parent", Lean.toJson parent)])]
    | .noSuchTrigger name => Lean.Json.mkObj [("noSuchTrigger", Lean.Json.mkObj [("name", Lean.toJson name)])]
    | .triggerExists name => Lean.Json.mkObj [("triggerExists", Lean.Json.mkObj [("name", Lean.toJson name)])]
    | .viewModify name => Lean.Json.mkObj [("viewModify", Lean.Json.mkObj [("name", Lean.toJson name)])]
    | .viewNotIndexed => Lean.Json.str "viewNotIndexed"
    | .viewAddColumn => Lean.Json.str "viewAddColumn"
    | .renameTargetTaken name => Lean.Json.mkObj [("renameTargetTaken", Lean.Json.mkObj [("name", Lean.toJson name)])]
    | .viewNotAltered name => Lean.Json.mkObj [("viewNotAltered", Lean.Json.mkObj [("name", Lean.toJson name)])]
    | .viewColumnsNotRenamed name =>
      Lean.Json.mkObj [("viewColumnsNotRenamed", Lean.Json.mkObj [("name", Lean.toJson name)])]
    | .renameNoSuchColumn token => Lean.Json.mkObj [("renameNoSuchColumn", Lean.Json.mkObj [("token", Lean.toJson token)])]
    | .viewTrigger before name =>
      Lean.Json.mkObj [("viewTrigger", Lean.Json.mkObj [("before", Lean.toJson before), ("name", Lean.toJson name)])]
    | .dropColumn error => Lean.Json.mkObj [("dropColumn", Lean.toJson error)]
    | .dependentObject kind name phase error =>
      Lean.Json.mkObj [("dependentObject", Lean.Json.mkObj [("kind", Lean.toJson kind), ("name", Lean.toJson name),
        ("phase", Lean.toJson phase), ("error", error.toJson)])]
    | .expression error => Lean.toJson error

instance : Lean.ToJson PrepareError := ⟨PrepareError.toJson⟩

/-- A model restriction as JSON: the statement index, the path, the message that users
read as {lit}`reason`, and the stable id of its kind as {lit}`restriction`. -/
instance : Lean.ToJson Restriction where
  toJson restriction := Lean.Json.mkObj [("statement", Lean.toJson restriction.statement),
    ("path", Lean.toJson restriction.path), ("reason", Lean.toJson restriction.reason),
    ("restriction", Lean.toJson restriction.kind.id)]

deriving instance Lean.ToJson for ScriptIssue

deriving instance Lean.ToExpr for Limits
deriving instance Lean.ToExpr for Profile

deriving instance Lean.ToExpr for ViewError
deriving instance Lean.ToExpr for CommonTableError
deriving instance Lean.ToExpr for ExprError

deriving instance Lean.ToExpr for DropColumnError
deriving instance Lean.ToExpr for PrepareError

deriving instance Lean.ToExpr for Resolved.Statement

end Belay.Sqlite.Model
