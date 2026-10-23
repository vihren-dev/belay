import Lean
import Belay.Sqlite.Model.Declarations
import Belay.Sqlite.Model.Comparison
import Belay.Sqlite.Model.QueryEval
import Belay.Sqlite.Model.QueryJoins
import Belay.Sqlite.Model.QueryFunctions
import Belay.Sqlite.Model.Database
import Belay.Sqlite.Model.Execution
import Belay.Sqlite.Model.LiteralData
import Belay.Sqlite.Model.SqlExecution
import Belay.Sqlite.Model.RowUpdate
import Belay.Sqlite.Model.UpsertRun
import Belay.Sqlite.Model.Resolution.Profile
import Belay.Sqlite.Model.Resolution.Syntax
import Belay.Sqlite.Model.Resolution.Catalog
import Belay.Sqlite.Model.Resolution.Resolved
import Belay.Sqlite.Model.Resolution.RestrictionRegistry
import Belay.Sqlite.Model.Resolution.Values
import Belay.Sqlite.Model.Resolution.ReadDefaults
import Belay.Sqlite.Model.Resolution.Context
import Belay.Sqlite.Model.Resolution.Definitions
import Belay.Sqlite.Model.Resolution.AddColumn
import Belay.Sqlite.Model.Resolution.Writes
import Belay.Sqlite.Model.Resolution.Resolve
import Belay.Sqlite.Model.Resolution.Messages
import Belay.Sqlite.Model.Resolution.SchemaScript

set_option doc.verso true

/-! JSON transport and closed kernel terms for SQLite values and rows. Decoding
constructs data; the kernel still checks every proposition about those values.
{lit}`Belay.Sqlite.Model.Codec.Resolution` adds statement syntax, catalogs and resolved
statements.

This module imports {module}`Lean`; the model's modules, such as
{module}`Belay.Sqlite.Model.Declarations`, do not. It imports only the model's definitions,
so that programs that use it, such as the conformance runner, do not compile the
model's proofs. -/

namespace Belay.Sqlite.Model

/-- Byte transport rejects overflow instead of wrapping corrupt TEXT/BLOB data. -/
instance : Lean.FromJson UInt8 where
  fromJson? json := do
    let value ← json.getNat?
    if value < 256 then return UInt8.ofNat value else throw "byte outside 0..255"

/-- Encode bytes as JSON integers. REAL payloads use UInt64 decimal strings. -/
instance : Lean.ToJson UInt8 where
  toJson value := Lean.toJson value.toNat

/-- A name is a JSON string, as the frontend writes it; its bytes are the string's UTF-8
bytes. -/
instance : Lean.FromJson Identifier where
  fromJson? json := Identifier.ofString <$> json.getStr?

/-- A name as a JSON string: its text ({name}`Identifier.text`). -/
instance : Lean.ToJson Identifier where
  toJson name := Lean.Json.str name.text

deriving instance Lean.ToExpr for Identifier
deriving instance Lean.FromJson, Lean.ToJson for Value, Row

-- Decoded values become closed kernel terms without elaborating generated source.
-- One command per type: a combined `deriving instance` treats its types as one group.
deriving instance Lean.ToExpr for Value
deriving instance Lean.ToExpr for Row

end Belay.Sqlite.Model
