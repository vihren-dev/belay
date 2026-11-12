import Belay.Sqlite.Tooling.Counterexamples.CheckDomain
import Belay.Sqlite.Tooling.Counterexamples.CheckData
import Belay.Sqlite.Tooling.Counterexamples.CheckScreen
import Belay.Sqlite.Tooling.Counterexamples.SampleCandidates
import Belay.Sqlite.Tooling.Counterexamples.ReplayDatabaseSql

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
  /-- Optional validated schema/base expression, for constraints or SQL without visible names.
  None uses the schema of a premise {lit}`db.HasCatalog schema` of the claim
  ({name}`domainSchemas`), else the schema that the claim's SQL suggests. -/
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

/-- Infer the shared schema, the constants and the touched tables once for each set of parameter
values. The background caller computes them with compiled code and checks them in the kernel.
With no named SQL source, use the ordinary one-table default schema so plain Lean predicates
also receive nonempty catalogs. An explicitly supplied schema always takes priority. The touched
tables are those of the scripts' statements, closed over the schema ({name}`Sampling.touchedNames`);
none, so every table, when {lit}`complete` is false because the claim can read the database
other than through these scripts, or when a statement does not name its tables. -/
def inferredData (scripts : List Script) (schema : Option Database) (complete : Bool) :
    Database.Raw × List Value × Option (List Model.Identifier) :=
  let found := scripts.foldl (fun hints script => hints.append (Sampling.scriptHints script))
    ({} : Sampling.SchemaHints)
  let inferred := if found.sources.isEmpty then Sampling.defaultSchema
    else found.schema.getD Sampling.defaultSchema
  let base := (schema.getD inferred).raw
  let named := if complete then
      scripts.foldlM (fun names script => (names ++ ·) <$> Sampling.statementsTables (script.statements.map (·.1))) []
    else none
  (base, found.expressions.values, named.bind (Sampling.touchedNames base.catalog))

/-- The generated candidates that one value of the value pool can use: an equal share of the
{lit}`left` candidates for it and the values after it, {lit}`values` in all with it, so that a
value without a counterexample, for example NULL as a key, does not use the count of the values
after it. A value that uses less leaves the rest to the values after it. The share is zero when
fewer candidates than values are left. A claim without a parameter value ({lit}`last`) gets all
of them. For example, {assert}`valueShare 100 4 false = 25` and
{assert}`valueShare 100 4 true = 100`. -/
def valueShare (left values : Nat) (last : Bool) : Nat :=
  if last then left else left / max 1 values

/-- Visit explicit witnesses, then, for each configured value, the empty database when the screen
accepts it, the databases
that the claim's equality premises name ({name}`domainDatabases`) and the generated candidates
({name}`Sampling.candidates`) that the screen accepts, in order, stopping at the first accepted
result. The generated candidates of a value are at most its share of the candidate count that
is left ({name}`valueShare`). The screen is {name}`SampleConfig.screen`, else the compiled screen of the claim
({name}`compileScreen`). A claim without a screen gets only the explicit witnesses, the empty
database and the named databases, and the reason is recorded ({name}`recordReason`). A schema without
SQL text ({name}`schemaText?`) that a replay cannot build from its catalog ({name}`Replay.databaseSql`)
records its reason too. The
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
  let suppliedSchema := config.schema.or ((← attempt (domainSchemas proposition)).bind (·[0]?))
  let schemaText ← match suppliedSchema with
    | some schema => schemaText? schema
    | none => pure none
  for (value, valueIndex) in config.values.zipIdx do
    if tried >= config.candidates then return none
    let initial : Witness :=
      { database := mkConst ``Database.empty, environment := config.environment, named := config.named }
    let some witness ← attempt (fillValueInputs proposition initial value) | continue
    tried := tried + 1
    -- The kernel certifies the empty database only when the screen accepts it.
    let some screensEmpty ← match screen with
        | some screen => attempt (awaitCompiled fun _ => screen Database.empty value)
        | none => pure (some true)
      | return none
    if screensEmpty then
      if let some result ← attempt (accept witness (screen.map (·, value))) then return some result
    for database in domain do
      if tried >= config.candidates then return none
      tried := tried + 1
      if let some result ← attempt (accept { witness with database, value := none } (screen.map (·, value))) then
        return some result
    -- No inferred Value binder means later parameter values would repeat this sequence.
    let last := witness.named == config.named
    let some screen := screen | if last then return none else continue
    let sites := (← attempt (querySites proposition witness.choose witness.database)).getD {}
    let scripts ← sites.sites.filterMapM fun site => do
      if (← attempt (scriptValue site.script)).isSome then return some site.script
      return none
    let complete := !sites.unsupported && !sites.leanCode && !sites.sites.isEmpty && scripts.size == sites.sites.size
    let scripts ← mkListLit (mkConst ``Script) scripts.toList
    let schema := match suppliedSchema with
      | some expression => mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``Database) expression
      | none => mkApp (mkConst ``Option.none [Level.zero]) (mkConst ``Database)
    let some (base, constants, touched) ← attempt <|
      dataValue (Database.Raw × List Value × Option (List Model.Identifier))
        (mkApp3 (mkConst ``inferredData) scripts schema (toExpr complete)) | continue
    let some baseDatabase := Sampling.validated base | continue
    -- Without SQL text, a replay can build only plain tables (Replay.databaseSql).
    if suppliedSchema.isSome && schemaText.isNone && (Replay.databaseSql baseDatabase).isNone then
      recordReason "the schema of the search has no SQL text, and the checker can build a schema without its \
        text only when its tables have no keys or constraints and it has no indexes, triggers or views. Write the \
        schema with db!, or as the database at the end of a run of SQL text, for example \
        (Database.empty.run (sql_file \"db/schema.sql\")).db"
    let baseExpression := suppliedSchema.getD (databaseExpr base)
    -- Generate and screen together, up to the first candidate after the position that the screen
    -- accepts; after a rejected certificate, generate again and continue after it.
    let valueEnd := tried + valueShare (config.candidates - tried) (config.values.length - valueIndex) last
    let mut position := 0
    repeat
      if tried >= valueEnd then break
      checkSystem "SQL candidate screening"
      let start := position
      let limit := start + (valueEnd - tried)
      -- The screen of the last candidate also runs in the timed task: the list can end at the
      -- limit without the stop test.
      let some (candidates, accepted) ← attempt do
          awaitCompiled fun _ =>
            let candidates := Sampling.candidates baseDatabase constants touched config.maxRows
              config.randomSamples config.seed config.size limit fun index database => start ≤ index && screen database value
            (candidates, candidates.size > start && candidates.back?.any (screen · value))
        | return none
      tried := tried + (candidates.size - start)
      let some candidate := candidates.back? | break
      unless accepted do break
      position := candidates.size
      let proposal := if candidate.raw == base then { witness with database := baseExpression, value := some candidate }
        else witness.generated candidate schemaText
      if let some result ← attempt (accept proposal (some (screen, value))) then
        return some result
    if last then return none
  return none

end Belay.Sqlite.Check
