import Belay.Sqlite.Model.Shared.Resolved.Resolved

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Why a schema and a script have no resolution. SQLite refuses to prepare a
schema statement, or the model does not describe a schema or script statement. -/
inductive ScriptIssue where
  /-- The model does not describe this schema statement. -/
  | schemaRestricted (restriction : Restriction)
  /-- SQLite refuses to prepare the schema statement at this zero-based index. -/
  | schemaPrepareError (statement : Nat) (error : PrepareError)
  /-- The model does not describe this script statement. -/
  | scriptRestricted (restriction : Restriction)
  deriving Repr, DecidableEq

/-- Whether a schema statement can describe a catalog: CREATE TABLE, CREATE VIEW, CREATE INDEX or CREATE
TRIGGER. -/
def Syntax.Statement.describesCatalog : Syntax.Statement → Bool
  | .createTable .. | .createView .. | .createIndex .. | .createTrigger .. => true
  | .addColumn .. | .renameTable .. | .renameColumn .. | .dropColumn .. | .dropTable .. | .dropView .. | .dropIndex .. | .dropTrigger .. | .begin | .commit | .rollback | .insert .. | .insertSelect .. | .update ..
  | .delete .. | .select .. | .pragma _ => false

/-- The first schema statement that cannot describe a catalog, as a restriction. -/
def schemaStatementRestriction (schema : List Syntax.Statement) : Option Restriction :=
  (findPosition (!·.describesCatalog) schema).map fun (index, _) =>
    { statement := index, path := [], kind := .schemaStatement }

/-- The prepare error of a resolved statement, if it is one. -/
def Resolved.Statement.prepareError? : Resolved.Statement → Option PrepareError
  | .prepareError error => some error
  | .createTable .. | .createView .. | .createIndex .. | .createTrigger .. | .addColumn .. | .rewrite _ | .dropColumn .. | .drop .. | .begin
  | .commit | .rollback | .insert .. | .upsert .. | .insertSelect .. | .update .. | .delete .. | .query .. | .setting .. => none

/-- The zero-based index and error of the first prepare error in a list of
resolved statements, from a starting index. -/
def firstPrepareErrorFrom (index : Nat) : List Resolved.Statement → Option (Nat × PrepareError)
  | [] => none
  | statement :: rest => match statement.prepareError? with
    | some error => some (index, error)
    | none => firstPrepareErrorFrom (index + 1) rest

end Belay.Sqlite.Model
