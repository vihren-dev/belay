import Belay.Sqlite.Codec.Resolution
import VerifierConformance.Case

/-! Conformance-case transport. The structural codecs for model types live in
`Belay.Sqlite.Codec`, shared with ADR 0003's bundle checker. These codecs are transport,
not a proof oracle. The pure checker has no JSON dependency. -/

open Belay.Sqlite

namespace Belay.Sqlite

deriving instance Lean.FromJson, Lean.ToJson for Limits, Profile
deriving instance Lean.FromJson, Lean.ToJson for Conformance.ErrorPhase
deriving instance Lean.FromJson, Lean.ToJson for Conformance.NativeColumn

/-- A native index as JSON: {lit}`name`, {lit}`columns` (a number for a column key, null for an
expression), {lit}`unique`, and {lit}`descending` and {lit}`partial` only when an index has a
descending term or is partial, so the records of indexes without them keep their form. -/
instance : Lean.ToJson Conformance.NativeIndex where
  toJson index := Lean.Json.mkObj ([("name", Lean.toJson index.name), ("columns", Lean.toJson index.columns),
      ("unique", Lean.toJson index.unique)] ++
    (if index.descending.isEmpty then [] else [("descending", Lean.toJson index.descending)]) ++
    (if index.isPartial then [("partial", Lean.toJson true)] else []))

/-- Read a native index ({name}`Conformance.NativeIndex`); a missing {lit}`descending` is every
term ascending and a missing {lit}`partial` is a full index. -/
instance : Lean.FromJson Conformance.NativeIndex where
  fromJson? json := do
    let descending : List Bool ← (json.getObjValAs? (List Bool) "descending").toOption.getD [] |> pure
    let isPartial : Bool ← (json.getObjValAs? Bool "partial").toOption.getD false |> pure
    return { name := ← json.getObjValAs? Identifier "name", columns := ← json.getObjValAs? (List (Option Nat)) "columns",
             unique := ← json.getObjValAs? Bool "unique", descending := Conformance.sortOrders descending, isPartial }

/-- A native table as JSON, with {lit}`withoutRowid` only for a {lit}`WITHOUT ROWID` table, so the
records of other tables keep their form. -/
instance : Lean.ToJson Conformance.NativeTable where
  toJson table := Lean.Json.mkObj ([("name", Lean.toJson table.name), ("columns", Lean.toJson table.columns),
      ("primaryKey", Lean.toJson table.primaryKey), ("uniqueKeys", Lean.toJson table.uniqueKeys),
      ("indexes", Lean.toJson table.indexes), ("rows", Lean.toJson table.rows)] ++
    (if table.withoutRowid then [("withoutRowid", Lean.toJson true)] else []))

/-- Read a native table ({name}`Conformance.NativeTable`); a missing {lit}`withoutRowid` is a
table with a rowid. -/
instance : Lean.FromJson Conformance.NativeTable where
  fromJson? json := do
    let withoutRowid : Bool := (json.getObjValAs? Bool "withoutRowid").toOption.getD false
    return { name := ← json.getObjValAs? Identifier "name", columns := ← json.getObjValAs? _ "columns",
             primaryKey := ← json.getObjValAs? _ "primaryKey", uniqueKeys := ← json.getObjValAs? _ "uniqueKeys",
             indexes := ← json.getObjValAs? _ "indexes", rows := ← json.getObjValAs? _ "rows", withoutRowid }

deriving instance Lean.FromJson, Lean.ToJson for Conformance.NativeObservation
deriving instance Lean.FromJson, Lean.ToJson for Conformance.StatementOutput, Conformance.OutputGroup,
  Conformance.NativeOutput
deriving instance Lean.FromJson, Lean.ToJson for Conformance.Case

namespace Conformance

/-- The supported case version: {assert}`caseVersion = 5`. Version 5 retains default
source spelling in statement syntax. Version 4 lacked that spelling. -/
def caseVersion : Nat := 5

/-- Check one native table: folded-name uniqueness is checked by the caller; here,
distinct bounded rowids, except in a {lit}`WITHOUT ROWID` table, and one cell per column. -/
def checkNativeTable (table : NativeTable) : Except String Unit := do
  unless table.withoutRowid || (table.rows.map Row.rowid).eraseDups.length == table.rows.length do
    throw "duplicate physical rowid"
  for row in table.rows do
    unless LiteralData.boundedInteger row.rowid && row.values.length == table.columns.length do
      throw "invalid physical rowid or row width"

/-- Decode without silently accepting unsupported versions or malformed finite fixtures. -/
def decodeCase (json : Lean.Json) : Except String Case := do
  let c : Case ← Lean.fromJson? json
  unless c.version == caseVersion do throw s!"unsupported conformance case version {c.version}; regenerate the case"
  unless !(c.nativeTrace.isEmpty) do throw "missing initial native observation"
  for tables in c.initial :: c.nativeTrace.flatMap (fun n => [n.visible, n.persisted]) do
    unless (tables.map (·.name.folded)).eraseDups.length == tables.length do
      throw "duplicate table name"
    for table in tables do checkNativeTable table
  for (n, position) in c.nativeTrace.zipIdx do
    unless n.extendedCode % 256 == n.primaryCode do throw "inconsistent SQLite result codes"
    unless n.primaryCode != 0 || n.phase.isNone do
      throw s!"native observation {position} has an error phase but result code 0; record the case again, \
        so that a successful observation has a null phase"
  unless c.clocks.isEmpty || c.clocks.length + 1 == c.nativeTrace.length do
    throw "clock trace length mismatch: give one clock value for each executed statement, or none"
  match c.outputs with
  | none => unless c.parameters.isEmpty do throw "parameters require outputs"
  | some outputs =>
    unless outputs.length + 1 == c.nativeTrace.length && c.parameters.length == outputs.length do
      throw "output/parameter trace length mismatch"
    for output in outputs do
      unless matchesOutput output.result output.result output.groups do
        throw "invalid native output shape or groups"
  return c

end Conformance
end Belay.Sqlite
