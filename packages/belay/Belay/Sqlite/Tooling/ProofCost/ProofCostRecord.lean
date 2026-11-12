import Lean.Data.Json

set_option doc.verso true

/-! The stored record of the proof-cost collector (ADR 0017, S7). A record says how many
internal heartbeat units Lean spent on the body of one named proof, and carries what a later
comparison needs: the compiler, the measurement scheme with its async mode, the unit, and a hash
of the module's source text. The record has no absolute path, so a relocated package keeps its
identities. This module imports no Lake and no elaborator code, so the collector and the checker
read the same type. -/

namespace Belay.Sqlite

open Lean

/-- The kind of declaration whose body a record measures. -/
inductive ProofCostKind where
  /-- A theorem. -/
  | thm
  /-- A definition whose type is a proposition, so its value is a proof. A definition of a
  proposition is not one: its type is {lean}`Prop`, not a proposition. -/
  | proofDefinition
  /-- An anonymous {lit}`example`. Lean does not store its type, so the collector cannot say
  whether it proves a proposition. -/
  | anonymousExample
  deriving BEq, Repr, Inhabited, ToJson, FromJson

/-- How stable the name of a record is across edits of the source. -/
inductive ProofCostIdentity where
  /-- A public, qualified name. A baseline can match it. -/
  | stable
  /-- A private name. Lean numbers private names, and edits can change the number. -/
  | privateName
  /-- An anonymous example. Its name is a source offset, which any edit above it moves. -/
  | anonymous
  deriving BEq, Repr, Inhabited, ToJson, FromJson

/-- What happened to the measurement of one body. A body that was not measured has no record. -/
inductive ProofCostStatus where
  /-- The body elaborated and its count is exact. -/
  | completed
  /-- The body's elaboration failed. -/
  | failed
  /-- Lean's native counters are {lean}`Float`; the count cannot be exact. -/
  | precisionUnavailable
  deriving BEq, Repr, Inhabited, ToJson, FromJson

/-- The number of internal heartbeats in one budget unit of {lit}`maxHeartbeats`. -/
def heartbeatsPerBudgetUnit : Nat := 1000

/-- The unit of a stored count: one internal heartbeat. One Lean budget unit
({lit}`maxHeartbeats`) is {lean}`heartbeatsPerBudgetUnit` internal heartbeats. -/
def proofCostUnit : String := "internal-heartbeat"

/-- The name of the environment extension that stores the records in a compiled module. The
checker finds the records of a module under this name, without running the collector. -/
def proofCostExtensionName : Name := `Belay.Sqlite.proofCosts

/-- One measurement of a proof body, in exact internal heartbeat units. -/
structure ProofCostRecord where
  /-- The module that declares the proof, independent of its file location. -/
  module : String
  /-- The qualified name as Lean prints it; anonymous examples add {lit}`@` and a source offset. -/
  declaration : String
  /-- Which kind of declaration this is. -/
  kind : ProofCostKind
  /-- How stable {lit}`declaration` is. -/
  identity : ProofCostIdentity
  /-- Whether {lit}`heartbeats` can be trusted. -/
  status : ProofCostStatus
  /-- The exact count of the body, when {lit}`status` is {lean}`ProofCostStatus.completed`. -/
  heartbeats : Option Nat
  /-- The unit of {lit}`heartbeats`, see {lean}`proofCostUnit`. -/
  unit : String := proofCostUnit
  /-- Counts of different compilers are never compared. -/
  compiler : String := Lean.versionString
  /-- The measured boundary and the async mode of the compile. Counts of different schemes are
  never compared. -/
  scheme : String
  /-- The hash of the module's source text when it was compiled, to notice a later edit. -/
  sourceHash : UInt64
  deriving BEq, Inhabited, ToJson, FromJson

end Belay.Sqlite
