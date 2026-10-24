import Belay.Sqlite.CheckData
import Belay.Sqlite.SampleDatabases

set_option doc.verso true

/-! Cooperative use of Plausible's fixed random choices. Generation is untrusted; each draw
uses finite literal inputs and checks resources, while row assembly and validity remain checked. -/

namespace Belay.Sqlite.Check

open Lean Elab Term Meta

/-- Execute one fixed Plausible choice with its ordinary generator state. Callers below bound
the choice range so the pinned standard generator needs one random step. This helper never
evaluates a Lean expression or accepts a user-supplied generator through the checking API. -/
private def draw (generator : Plausible.Gen α) (size : Nat) : StateT StdGen TermElabM α := do
  checkSystem "SQL random draw"
  let .ok (value, next) := (generator ⟨← get⟩).run ⟨size⟩
    | throwError "SQL sampling could not produce a bounded choice"
  set next.down
  checkSystem "SQL random draw"
  return value

/-- Draw a row count with the same Plausible primitive as ordinary sampling. The background
limit is {name}`maxRandomRows`; larger requests remain available through the explicit sampler. Resource
checks surround the finite standard-generator step. -/
def drawRowCount (maxRows size : Nat) : StateT StdGen TermElabM Nat := do
  if maxRows > maxRandomRows then throwError "SQL sampling reached its row-count limit"
  return (← draw (Plausible.Gen.choose Nat 0 maxRows (Nat.zero_le _)) size).val

/-- Draw from the shared SQL value distribution, retaining Plausible's generator state.
At most {name}`maxRandomValues` supplied constants precede the ordinary boundary values. The inputs come from
normalized literal data in the background checker; no supplied expression runs natively. -/
def drawValue (constants : List Value) (size : Nat) : StateT StdGen TermElabM Value := do
  if (constants.take (maxRandomValues + 1)).length > maxRandomValues then
    throwError "SQL sampling reached its value-pool limit"
  draw (Sampling.value constants) size

/-- Assemble one cell matrix through the existing affinity and validity functions. A rejected
matrix yields no candidate; the background caller reduces this pure computation cooperatively. -/
def cellsData (base : Database.Raw) (cells : List (List (List Value))) : Option Database.Raw :=
  (Sampling.validated (Sampling.withCells base cells)).map (·.raw)

/-- Count literal bytes before reifying a selected value. Input values already satisfy the
normalizer's finite limits, so this traversal cannot inspect an arbitrary computation. -/
private def valueBytes : Value → Nat
  | .null => 0
  | .integer number => number.natAbs.log2 / 8 + 1
  | .real _ => 8
  | .text bytes | .blob bytes => bytes.length

/-- Generate one proposal from already-normalized literal data. The traversal and random
draw order match ordinary Plausible sampling. Every count/cell draw checks cancellation and
heartbeats. A proposal respects {name}`maxRandomCells` and {name}`maxLiteralBytes`; pure affinity/constraint
work is reduced separately before decoding. The result
still needs the original claim's certificate and replay before it can be reported. -/
def randomCandidate (base : Database.Raw) (constants : List Value) (maxRows seed size : Nat) :
    TermElabM (Option Database.Raw) := do
  checkSystem "SQL random seed"
  if seed.log2 > maxSeedBits then throwError "SQL sampling reached its seed-size limit"
  let counts ← IO.mkRef (0, 0)
  let cell : StateT StdGen TermElabM Value := do
    let value ← drawValue constants size
    let (cells, bytes) ← counts.get
    let bytes := bytes + valueBytes value
    if cells >= maxRandomCells || bytes > maxLiteralBytes then
      throwError "SQL sampling reached its cell-data limit"
    counts.set (cells + 1, bytes)
    return value
  let (cells, _) ← (Sampling.selectCells base.catalog (drawRowCount maxRows size)
    cell (checkSystem "SQL random rows")).run (mkStdGen seed)
  dataValue (Option Database.Raw) (mkApp2 (mkConst ``cellsData) (toExpr base) (toExpr cells))

end Belay.Sqlite.Check
