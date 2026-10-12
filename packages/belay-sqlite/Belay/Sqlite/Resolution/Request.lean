import Belay.Sqlite.Resolution.Resolve

set_option doc.verso true

/-! The resolution of one verification request: the schema statements, which
describe the starting catalog, and the migration statements, which the execution
semantics runs. The verifier computes the generated inputs with
{lit}`resolveRequest`, and the gates compute it again to check them. -/

namespace Belay.Sqlite

/-- Why a request has no generated inputs. A schema statement that SQLite refuses
to prepare is an error in the input; a model restriction refuses the request as
unsupported. -/
inductive RequestIssue where
  /-- The model does not describe this schema statement. -/
  | schemaRestricted (restriction : Restriction)
  /-- SQLite refuses to prepare the schema statement at this zero-based index. -/
  | schemaPrepareError (statement : Nat) (error : PrepareError)
  /-- The model does not describe this migration statement. -/
  | migrationRestricted (restriction : Restriction)
  deriving Repr, DecidableEq

/-- The generated inputs of a request. The catalogs and the resolved statements
are results of {name}`resolve`; the profile and the statements are the inputs. -/
structure ResolvedRequest where
  /-- The execution profile. -/
  profile : Profile
  /-- The schema statements as written. -/
  schema : List Syntax.Statement
  /-- The catalog that the schema statements describe. -/
  startCatalog : Catalog
  /-- The migration statements as written. -/
  script : List Syntax.Statement
  /-- The migration statements after resolution against the starting catalog. -/
  resolved : List Resolved.Statement
  /-- The catalog after every migration statement succeeds. -/
  nextCatalog : Catalog
  deriving Repr, DecidableEq

/-- Whether a schema statement can describe a catalog: CREATE TABLE or CREATE INDEX. -/
def Syntax.Statement.describesCatalog : Syntax.Statement → Bool
  | .createTable .. | .createIndex .. => true
  | .addColumn .. | .begin | .commit | .rollback | .insert .. | .update .. => false

/-- The first schema statement that cannot describe a catalog, as a restriction. -/
def schemaStatementRestriction (schema : List Syntax.Statement) : Option Restriction :=
  (findPosition (!·.describesCatalog) schema).map fun (index, _) =>
    { statement := index, path := [], reason := "a schema contains only CREATE TABLE and CREATE INDEX statements; move the other statement to the migration" }

/-- The index and error of the first prepare error in a list of resolved statements. -/
def firstPrepareError (statements : List Resolved.Statement) : Option (Nat × PrepareError) :=
  (findPosition (fun | .prepareError _ => true | _ => false) statements).bind fun
    | (index, .prepareError error) => some (index, error)
    | _ => none

/-- Resolve a request. The schema statements resolve in description mode against
the empty catalog; each must be CREATE TABLE or CREATE INDEX and must prepare
without an error. The migration statements resolve in execution mode against the
resulting catalog; a prepare error there stays in the resolved statements. -/
def resolveRequest (profile : Profile) (schema script : List Syntax.Statement) :
    Except RequestIssue ResolvedRequest :=
  match schemaStatementRestriction schema with
  | some restriction => .error (.schemaRestricted restriction)
  | none =>
    match resolve { profile, mode := .description } [] schema with
    | .restricted restriction => .error (.schemaRestricted restriction)
    | .resolved described startCatalog =>
      match firstPrepareError described with
      | some (index, error) => .error (.schemaPrepareError index error)
      | none =>
        match resolve { profile, mode := .execution } startCatalog script with
        | .restricted restriction => .error (.migrationRestricted restriction)
        | .resolved resolved nextCatalog => .ok { profile, schema, startCatalog, script, resolved, nextCatalog }

end Belay.Sqlite
