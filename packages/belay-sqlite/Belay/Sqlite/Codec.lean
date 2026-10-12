import Lean
import Belay.Sqlite

set_option doc.verso true

/-! JSON transport and closed kernel terms for SQLite values and rows. Decoding
constructs data; the kernel still checks every proposition about those values.
{lit}`Belay.Sqlite.Codec.Resolution` adds statement syntax, catalogs and resolved
statements.

This module imports {module}`Lean`; the {module}`Belay.Sqlite` core does not. -/

namespace Belay.Sqlite

/-- Byte transport rejects overflow instead of wrapping corrupt TEXT/BLOB data. -/
instance : Lean.FromJson UInt8 where
  fromJson? json := do
    let value ← json.getNat?
    if value < 256 then return UInt8.ofNat value else throw "byte outside 0..255"

/-- Encode bytes as JSON integers. REAL payloads use UInt64 decimal strings. -/
instance : Lean.ToJson UInt8 where
  toJson value := Lean.toJson value.toNat

deriving instance Lean.FromJson, Lean.ToJson for Value, Row

-- Decoded values become closed kernel terms without elaborating generated source.
-- One command per type: a combined `deriving instance` treats its types as one group.
deriving instance Lean.ToExpr for Value
deriving instance Lean.ToExpr for Row

end Belay.Sqlite
