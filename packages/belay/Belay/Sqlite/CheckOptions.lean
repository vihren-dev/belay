import Belay.Sqlite.CheckOperation

set_option doc.verso true

/-! The explicit command and searched tactic share these finite controls. Heartbeats bound
cooperative work, not elapsed time. The programmatic checker accepts custom policies directly. -/

/-- A finite Lean heartbeat budget for SQL checks; zero returns unknown without searching. -/
register_option sql.checkBudget : Nat := {
  defValue := 100000
  descr := "SQL checking budget in Lean heartbeat units (zero disables checking)" }

/-- Reduction depth for a SQL check; zero disables it. The caller's depth is restored. -/
register_option sql.checkRecursionLimit : Nat := {
  defValue := Belay.Sqlite.Check.defaultRecursionLimit
  descr := "finite reduction depth for SQL checking" }

/-- Seed for the shared Plausible proposals; leave zero for reproducible defaults. -/
register_option sql.checkSeed : Nat := {
  defValue := 0
  descr := "seed for SQL counterexample sampling" }

/-- Size parameter for the shared sampler; row and candidate bounds still apply. -/
register_option sql.checkSize : Nat := {
  defValue := 2
  descr := "size parameter for SQL counterexample sampling" }

/-- Maximum rows in each sampled table; explicit witnesses retain their own rows. -/
register_option sql.checkMaxRows : Nat := {
  defValue := 2
  descr := "maximum generated rows per SQL table" }

/-- Seeded proposals after the targeted proposals for each parameter value. -/
register_option sql.checkRandomSamples : Nat := {
  defValue := 4
  descr := "random SQL database proposals per parameter value" }

/-- Maximum candidates, including supplied witnesses; zero skips all candidates. -/
register_option sql.checkCandidates : Nat := {
  defValue := 128
  descr := "maximum SQL counterexample candidates" }

/-- Maximum shrink attempts after a checked witness; zero retains that witness directly. -/
register_option sql.checkShrinkAttempts : Nat := {
  defValue := 16
  descr := "maximum checked SQL counterexample shrink attempts" }

namespace Belay.Sqlite.Check
open Lean

/-- Read the shared sampling controls. Explicit terms can then extend this configuration;
programmatic callers can instead construct {name}`SampleConfig` themselves. -/
def configuredSamples (options : Options) : SampleConfig := {
  seed := sql.checkSeed.get options
  size := sql.checkSize.get options
  maxRows := sql.checkMaxRows.get options
  randomSamples := sql.checkRandomSamples.get options
  candidates := sql.checkCandidates.get options }

end Belay.Sqlite.Check
