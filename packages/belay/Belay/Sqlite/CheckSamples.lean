import Belay.Sqlite.CheckClaim
import Belay.Sqlite.CheckBudget
import Belay.Sqlite.SampleScriptHints
import Belay.Sqlite.SampleShrink
import Belay.Sqlite.CheckData
import Belay.Sqlite.CheckRandom

set_option doc.verso true

/-! Default search proposals reuse the SQL/Plausible sampling layer. Every result remains an
untrusted witness proposal until the shared checker proves the original claim's negation. -/

namespace Belay.Sqlite.Check

open Lean Meta Elab Term

/-- Finite search controls. The order is explicit witnesses first, then each configured
parameter value with empty/targeted databases followed by seeded Plausible proposals.
A finite candidate set has no implication for a universal claim that it does not refute. -/
structure SampleConfig where
  /-- Explicit candidates, tried before inferred ones; use an empty array for inference alone. -/
  witnesses : Array Witness := #[]
  /-- Optional validated schema/base expression, for constraints or SQL without visible names. -/
  schema : Option Expr := none
  /-- Additional quantified inputs by binder name; use an empty array when none are needed. -/
  named : Array (Name × Expr) := #[]
  /-- An environment candidate; the default is complete. Claim premises, including
  completeness when required, are checked before a candidate can refute the claim. -/
  environment : Expr := mkConst ``candidateEnvironment
  /-- Boundary values for otherwise unassigned Value binders, in stable order. -/
  values : List Value := Sampling.boundaryValues
  /-- Seed of the first Plausible proposal; later proposals increment it. -/
  seed : Nat := 0
  /-- Plausible's size parameter; two is sufficient for the default small examples. -/
  size : Nat := 2
  /-- Maximum rows per physical table in generated proposals. -/
  maxRows : Nat := 2
  /-- Number of Plausible proposals after each finite targeted sequence. -/
  randomSamples : Nat := 4
  /-- Maximum total candidates, including explicit and targeted candidates; zero disables search. -/
  candidates : Nat := 128

/-- Infer the shared schema and constants once for each set of parameter values. The
background caller reduces this pure computation before decoding its raw result. With no named
SQL source, use the ordinary one-table default schema so plain Lean predicates also receive
nonempty catalogs. An explicitly supplied schema always takes priority. -/
def inferredData (scripts : List Script) (schema : Option Database) : Database.Raw × List Value :=
  let found := scripts.foldl (fun hints script => hints.append (Sampling.scriptHints script))
    ({} : Sampling.SchemaHints)
  let inferred := if found.sources.isEmpty then Sampling.defaultSchema
    else found.schema.getD Sampling.defaultSchema
  ((schema.getD inferred).raw, found.expressions.values)

/-- Select one candidate from the existing targeted sampler, retaining its order and
constraint rejection. Reduction need not construct or decode the later candidates. -/
def targetedData (base : Database) (constants : List Value) (index : Nat) : Option Database.Raw :=
  ((Sampling.targeted base constants)[index]?).map (·.raw)

/-- Visit explicit witnesses, then empty, targeted and seeded candidates in order, stopping
at the first accepted result. Each generated proposal is reduced separately under the caller's
budget. Rejected candidates restore speculative state; exhaustion and cancellation propagate.
The callback can demand a certificate plus replay, or impose another acceptance condition.
Finite search failure supplies no evidence for a universal proposition. -/
def visitCandidates (proposition : Expr) (config : SampleConfig)
    (accept : Witness → TermElabM α) : TermElabM (Option α) := do
  let mut tried := 0
  for witness in config.witnesses do
    if tried >= config.candidates then return none
    tried := tried + 1
    if let some result ← attempt (accept witness) then return some result
  for value in config.values do
    if tried >= config.candidates then return none
    let initial : Witness :=
      { database := mkConst ``Database.empty, environment := config.environment, named := config.named }
    let some witness ← attempt (fillValueInputs proposition initial value) | continue
    tried := tried + 1
    if let some result ← attempt (accept witness) then return some result
    if tried >= config.candidates then return none
    let sites := (← attempt (querySites proposition witness.choose witness.database)).getD {}
    let scripts ← sites.sites.filterMapM fun site => do
      if (← attempt (scriptValue site.script)).isSome then return some site.script
      return none
    let scripts ← mkListLit (mkConst ``Script) scripts.toList
    let schema := match config.schema with
      | some expression => mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``Database) expression
      | none => mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Database)
    let some (base, constants) ← attempt <| dataValue (Database.Raw × List Value)
      (mkApp2 (mkConst ``inferredData) scripts schema) | continue
    let baseExpression := config.schema.getD (databaseExpr base)
    -- The targeted list has at most this many entries; rejected constraints shorten it.
    for (random, count) in [(false, 1 + Sampling.boundaryRows.length + constants.length),
                            (true, config.randomSamples)] do
      for index in [0:count] do
        checkSystem "SQL candidate generation"
        if tried >= config.candidates then return none
        let some (some raw) ← attempt (if random then
            randomCandidate base constants config.maxRows (config.seed + index) config.size
          else dataValue (Option Database.Raw)
            (mkApp3 (mkConst ``targetedData) baseExpression (toExpr constants) (toExpr index))) | continue
        if raw.rows.any (fun rows => rows.length > config.maxRows) then continue
        let expression := if raw == base then baseExpression else databaseExpr raw
        tried := tried + 1
        if let some result ← attempt (accept { witness with database := expression }) then return some result
    -- No inferred Value binder means later parameter values would repeat this sequence.
    if witness.named == config.named then return none
  return none

end Belay.Sqlite.Check
