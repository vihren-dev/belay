import Belay.Sqlite.Codec

set_option doc.verso true

/-! JSON transport and closed kernel terms for statement syntax, catalogs and
resolved statements, and the structural record of a request. The frontend writes
the record; the resolver and the gates read it. -/

namespace Belay.Sqlite

deriving instance Lean.FromJson, Lean.ToJson for Syntax.Expr, Syntax.ColumnConstraint
deriving instance Lean.FromJson, Lean.ToJson for Syntax.ColumnDefinition, Syntax.TableConstraint
deriving instance Lean.FromJson, Lean.ToJson for Syntax.Statement
deriving instance Lean.ToJson for PrepareError, Restriction, RequestIssue

-- One command per type: a combined `deriving instance` treats its types as one group.
deriving instance Lean.ToExpr for Syntax.Expr
deriving instance Lean.ToExpr for Syntax.ColumnConstraint
deriving instance Lean.ToExpr for Syntax.ColumnDefinition
deriving instance Lean.ToExpr for Syntax.TableConstraint
deriving instance Lean.ToExpr for Syntax.Statement
deriving instance Lean.ToExpr for Limits
deriving instance Lean.ToExpr for Profile
deriving instance Lean.ToExpr for CatalogColumn
deriving instance Lean.ToExpr for CatalogTable
deriving instance Lean.ToExpr for CatalogIndex
deriving instance Lean.ToExpr for CatalogEntry
deriving instance Lean.ToExpr for CatalogObject
deriving instance Lean.ToExpr for PrepareError
deriving instance Lean.ToExpr for Resolved.Statement

/-- The structural record of a request, version 2: the SQLite release and build
of the profile, and the schema and migration statements as written. Use an empty
schema list for an empty starting catalog. -/
structure RequestRecord where
  /-- The wire format version; supported records use 2. -/
  version : Nat
  /-- The SQLite release, for example {lit}`3.51.0`. -/
  release : String
  /-- The {lit}`sqlite_source_id()` of the build. -/
  sourceId : String
  /-- The schema statements as written. -/
  schema : List Syntax.Statement
  /-- The migration statements as written. -/
  script : List Syntax.Statement
  deriving Lean.FromJson, Lean.ToJson

/-- The profile of a record: the documented defaults of its release and build,
until a measured profile can be given. -/
def RequestRecord.profile (record : RequestRecord) : Profile :=
  Profile.documented record.release record.sourceId

/-- Resolve the request that a record describes. -/
def RequestRecord.resolve (record : RequestRecord) : Except RequestIssue ResolvedRequest :=
  resolveRequest record.profile record.schema record.script

/-- Decode a request record, and refuse other versions. -/
def decodeRequestRecord (json : Lean.Json) : Except String RequestRecord := do
  let record : RequestRecord ← Lean.fromJson? json
  unless record.version == 2 do
    throw s!"request record version {record.version} is unsupported; only version 2 is supported. Regenerate the record with a matching frontend."
  return record

end Belay.Sqlite
