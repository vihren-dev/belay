import Lean
import Belay.Sqlite.Model

set_option doc.verso true

/-! JSON transport and closed kernel terms for SQLite values and rows. Decoding
constructs data; the kernel still checks every proposition about those values.
{lit}`Belay.Sqlite.Model.Codec.Resolution` adds statement syntax, catalogs and resolved
statements.

This module imports {module}`Lean`; the {module}`Belay.Sqlite.Model` core does not. -/

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
