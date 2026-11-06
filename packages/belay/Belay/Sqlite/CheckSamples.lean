import Belay.Sqlite.CheckDomain
import Belay.Sqlite.CheckBudget
import Belay.Sqlite.SampleScriptHints
import Belay.Sqlite.SampleShrink
import Belay.Sqlite.CheckData
import Belay.Sqlite.CheckScreen
import Belay.Sqlite.SampleCandidates

set_option doc.verso true

/-! Default search proposals reuse the SQL/Plausible sampling layer. Every result remains an
untrusted witness proposal until the shared checker proves the original claim's negation. -/

namespace Belay.Sqlite.Check

open Lean Meta Elab Term

/-- Finite search controls. The order is explicit witnesses first, then for each configured
parameter value the databases that the claim names and the generated candidates that the screen
accepts ({name}`Sampling.candidates`). A finite candidate set has no implication for a universal
claim that it does not refute. -/
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
  /-- Number of seeded Plausible proposals after the small table contents. -/
  randomSamples : Nat := 4
  /-- Maximum total candidates, including explicit witnesses, named databases and screened
  candidates; zero disables search. -/
  candidates : Nat := 10000
  /-- The time limit of the compiled work of the check, in milliseconds. -/
  timeLimit : Nat := defaultTimeLimit
  /-- The screen of the generated candidates. None uses the compiled screen of the claim
  ({name}`compileScreen`); a caller can supply another one, for example one that accepts every
  database, which leaves every decision to certification. -/
  screen : Option Screen := none

/-- Infer the shared schema and constants once for each set of parameter values. The
background caller computes it with compiled code and checks it in the kernel. With no named
SQL source, use the ordinary one-table default schema so plain Lean predicates also receive
nonempty catalogs. An explicitly supplied schema always takes priority. -/
def inferredData (scripts : List Script) (schema : Option Database) : Database.Raw × List Value :=
  let found := scripts.foldl (fun hints script => hints.append (Sampling.scriptHints script))
    ({} : Sampling.SchemaHints)
  let inferred := if found.sources.isEmpty then Sampling.defaultSchema
    else found.schema.getD Sampling.defaultSchema
  ((schema.getD inferred).raw, found.expressions.values)

/-- Visit explicit witnesses, then, for each configured value, the empty database, the databases
that the claim's equality premises name ({name}`domainDatabases`) and the generated candidates
({name}`Sampling.candidates`) that the screen accepts, in order, stopping at the first accepted
result. The screen is {name}`SampleConfig.screen`, else the compiled screen of the claim
({name}`compileScreen`). A claim without a screen gets only the explicit witnesses, the empty
database and the named databases, and the reason is recorded ({name}`recordReason`). The
callback also gets the screen and the value that hold for the witness, for shrinking: for a
generated candidate, its value; for an explicit witness with the configured environment and
named inputs, {name}`Value.null`, which no input uses then; else none. The candidate count covers every
witness, named database and screened candidate. Compiled work stops at the time limit of the
operation. Rejected candidates restore speculative state; exhaustion and cancellation propagate.
The callback can demand a certificate plus replay, or impose another acceptance condition.
Finite search failure supplies no evidence for a universal proposition. -/
def visitCandidates (proposition : Expr) (config : SampleConfig)
    (accept : Witness → Option (Screen × Value) → TermElabM α) : TermElabM (Option α) := do
  let screen ← match config.screen with
    | some screen => pure (some screen)
    | none =>
      try some <$> speculative (compileScreen proposition config.environment config.named)
      catch error =>
        recordReason s!"the search could not compile a screen for this claim ({← error.toMessageData.toString}), so it tried only the supplied databases, the empty database and the databases that the claim names; supply a counterexample with (db := ...)"
        pure none
  let mut tried := 0
  for witness in config.witnesses do
    if tried >= config.candidates then return none
    tried := tried + 1
    let fixed := witness.environment == config.environment && witness.named == config.named
    let screened := if fixed then screen.map (·, Value.null) else none
    if let some result ← attempt (accept witness screened) then return some result
  let domain := (← attempt (domainDatabases proposition)).getD #[]
  let mut generated : Option (Database.Raw × List Value × Array Database) := none
  for value in config.values do
    if tried >= config.candidates then return none
    let initial : Witness :=
      { database := mkConst ``Database.empty, environment := config.environment, named := config.named }
    let some witness ← attempt (fillValueInputs proposition initial value) | continue
    tried := tried + 1
    if let some result ← attempt (accept witness (screen.map (·, value))) then return some result
    for database in domain do
      if tried >= config.candidates then return none
      tried := tried + 1
      if let some result ← attempt (accept { witness with database } (screen.map (·, value))) then
        return some result
    -- No inferred Value binder means later parameter values would repeat this sequence.
    let last := witness.named == config.named
    let some screen := screen | if last then return none else continue
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
    let some baseDatabase := Sampling.validated base | continue
    let baseExpression := config.schema.getD (databaseExpr base)
    let schemaText ← match config.schema with
      | some schema => schemaText? schema
      | none => pure none
    let cached := generated.bind fun (raw, known, candidates) =>
      if raw == base && known == constants then some candidates else none
    let fresh ← match cached with
      | some candidates => pure (some candidates)
      | none => attempt do
        awaitCompiled fun _ => Sampling.candidates baseDatabase constants config.maxRows
          config.randomSamples config.seed config.size config.candidates
    let some candidates := fresh | return none
    generated := some (base, constants, candidates)
    let mut position := 0
    while position < candidates.size && tried < config.candidates do
      checkSystem "SQL candidate screening"
      let count := min screenBatch (config.candidates - tried)
      let some found ← attempt do awaitCompiled fun _ => firstAccepted screen value candidates position count
        | return none
      match found with
      | none =>
        tried := tried + min count (candidates.size - position)
        position := position + count
      | some index =>
        tried := tried + (index + 1 - position)
        position := index + 1
        let some candidate := candidates[index]? | return none
        let raw := candidate.raw
        let expression := if raw == base then baseExpression else generatedExpr raw schemaText
        if let some result ← attempt (accept { witness with database := expression } (some (screen, value))) then
          return some result
    if last then return none
  return none

end Belay.Sqlite.Check
