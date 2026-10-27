import Lean.Meta.ForEachExpr
import Belay.Sqlite.CounterexampleWitness
import Belay.Sqlite.CheckProgram
import Belay.Sqlite.ExecutionObservations
import Belay.Sqlite.ExecutionViewEquivalence
import Belay.Sqlite.Queries
import Belay.Sqlite.SqlSource
import Belay.Sqlite.SampleValues
import Belay.Sqlite.SampleScriptHints

set_option doc.verso true

/-! Bounded claim inspection supplies quantified inputs, SQL relevance and original query
sites. It supplies search/display hints only; certification keeps the original proposition. -/

namespace Belay.Sqlite.Check

open Lean Meta

/-- Names whose occurrences identify SQL observations, rather than unrelated Lean facts. The check of a
program and the four equivalence relations between programs cover the claims of triples, fresh runs,
equivalences and migration patterns, which unfold to them. -/
def queryNames : Array Name :=
  #[``Holds, ``Empty, ``Fails, ``Succeeds, ``Script.outputOn, ``Database.run, ``Sql.SucceedsFrom, ``Sql.check] ++
    programRelationNames

/-- These existing helpers inspect SQL syntax or database data without executing a script.
Their arguments are still inspected; their implementation dependencies cannot add an SQL site. -/
private def dataOnlyNames : Array Name :=
  #[``Sampling.scriptHints, ``Sampling.SchemaHints.schema, ``Sampling.schema,
    ``Sampling.validated, ``Database.empty, ``Database.rows]

/-- Query predicates whose first two arguments give the script and observed database. -/
private def directQueryNames : Array Name :=
  #[``Holds, ``Empty, ``Fails]

/-- Inspect proposition arguments of these constructors without unfolding their definitions. -/
private def logicalConstructorNames : Array Name :=
  #[``Eq, ``HEq, ``And, ``Or, ``Iff, ``True, ``False]

/-- Look for a query operation or SQL source annotation, following definition bodies.
The inspection does not follow constant types, so merely using the Database type does not
trigger SQL checking. None means that the finite declaration budget ran out; it is not a
claim that the statement is unrelated to SQL. Metadata supplies relevance only, never proof.
Set includeSource to false when distinguishing execution from plain manipulation of SQL syntax. -/
def sqlMention? (expression : Expr) (fuel : Nat := 256) (includeSource : Bool := true) : MetaM (Option Bool) := do
  let mut pending := #[expression]
  let mut seen : NameSet := {}
  for _ in List.range fuel do
    if pending.isEmpty then return some false
    checkSystem "SQL relevance inspection"
    let current := pending.back!
    pending := pending.pop
    let names ← IO.mkRef ({} : NameSet)
    let found ← IO.mkRef false
    forEachExpr' current fun part => do
      checkSystem "SQL relevance expression"
      -- Database literals carry validity proofs. Their proof implementation is
      -- not another SQL observation in the statement being inspected.
      if ← isProof part then return false
      if includeSource && ((sourceText? scriptSourceKey part).isSome ||
          (sourceText? databaseSourceKey part).isSome) then found.set true
      if let .const name _ := part then
        if queryNames.contains name then found.set true
        names.modify (·.insert name)
      return true
    if ← found.get then return some true
    for name in (← names.get).toArray do
      if !seen.contains name && !dataOnlyNames.contains name then
        seen := seen.insert name
        if let some info := (← getEnv).find? name then
          if let some body := info.value? then pending := pending.push body
  return if pending.isEmpty then some false else none

open Lean Meta Elab Term

/-- One original query and the database on which its proposition observes it. -/
structure QuerySite where
  /-- The actual script expression, retaining parameters and source metadata. -/
  script : Expr
  /-- The actual database expression used by the observation. -/
  database : Expr

/-- Sites found in a finite inspection. Unsupported SQL or an exhausted inspection prevents
an SQL report, even if independent certification can refute the proposition. -/
structure QuerySites where
  /-- Query/database pairs in logical source order. -/
  sites : Array QuerySite := #[]
  /-- Some SQL cannot be replayed by this structural query/script inspection. -/
  unsupported : Bool := false
  /-- Part of a program is Lean code, which the replay cannot run: the sites are the scripts that the
  program sends first, and a report must say that the failing result is the model's run of the whole program. -/
  leanCode : Bool := false

/-- Combine inspections without dropping an unsupported branch. -/
def QuerySites.append (first second : QuerySites) : QuerySites :=
  { sites := first.sites ++ second.sites, unsupported := first.unsupported || second.unsupported,
    leanCode := first.leanCode || second.leanCode }

/-- The database of a context that is the initial context of a database and an environment, when the context
has that form after at most a few unfoldings of definitions, as a named context has. A replay starts at this
database. -/
def initialDatabase? (state : Expr) (unfoldings : Nat := 8) : MetaM (Option Expr) := do
  if state.isAppOfArity ``ExecutionContext.initial 2 then return some state.appFn!.appArg!
  match unfoldings with
  | 0 => return none
  | unfoldings + 1 =>
    let some next ← unfoldDefinition? state | return none
    initialDatabase? next unfoldings

/-- The first scripts of the programs, at the initial database of the context. A context that is no initial
context has no database to replay from, so its sites are unsupported. -/
def programSites (programs : Array Expr) (state : Expr) : MetaM QuerySites := do
  let some database ← initialDatabase? (← instantiateMVars state) | return { unsupported := true }
  let mut result : QuerySites := {}
  for program in programs do
    let shape ← programScripts defaultProgramFuel program
    result := result.append { sites := shape.scripts.map ({ script := ·, database }), leanCode := shape.leanCode }
  return result

/-- Inspect a proposition under concrete data inputs. Implication premises retain local
proof variables while their SQL is inspected; these variables are never supplied to the
certificate. Query predicates retain their exact database argument. Script success uses the
selected database; a raw continuation program is marked unsupported instead of flattened.
The finite depth is a heuristic limit. Missing inputs or unsupported structure can return
unknown in the caller, while the explicit refutation primitive remains available. -/
def querySites (proposition : Expr) (choose : Name → Expr → MetaM Expr)
    (database : Expr) (fuel : Nat := 128) : TermElabM QuerySites :=
  visit fuel proposition
where
  /-- Inspect only logical terms and named proposition definitions, leaving execution to
  the model and certification to the original-proposition checker. -/
  visit : Nat → Expr → TermElabM QuerySites
    | 0, _ => pure { unsupported := true }
    | fuel + 1, expression => do
      checkSystem "SQL claim inspection"
      let expression ← instantiateMVars expression
      match expression with
      | .mdata _ body => return ← visit fuel body
      | .letE _ _ value body _ => return ← visit fuel (body.instantiate1 value)
      | .forallE name domain body _ =>
        if ← isProp domain then
          let premise ← visit fuel domain
          let conclusion ← withLocalDeclD name domain fun input => visit fuel (body.instantiate1 input)
          return premise.append conclusion
        else
          return ← visit fuel (body.instantiate1 (← choose name domain))
      | _ => pure ()
      let head := expression.getAppFn
      let arguments := expression.getAppArgs
      if directQueryNames.any head.isConstOf && arguments.size >= 2 then
        return { sites := #[{ script := arguments[0]!, database := arguments[1]! }] }
      if head.isConstOf ``Succeeds && arguments.size == 5 then
        let program := arguments[3]!
        let script? ← if ← isDefEq arguments[0]! (mkConst ``Script) then pure (some program)
          else if program.isAppOfArity ``send 1 then pure (some program.appArg!)
          else pure none
        let some script := script? | return { unsupported := true }
        let premise ← visit fuel (mkApp arguments[4]! database)
        return premise.append { sites := #[{ script, database }] }
      if head.isConstOf ``Sql.check && arguments.size == 4 then
        return ← programSites #[arguments[1]!] arguments[3]!
      if programRelationNames.any head.isConstOf && arguments.size ≥ 4 then
        return ← programSites #[arguments[1]!, arguments[2]!] arguments.back!
      if head.isLambda then return ← visit fuel (head.beta arguments)
      if let .const name levels := head then
        -- Logical constructors are inspected by their proposition arguments below.
        unless logicalConstructorNames.contains name do
          if let some info := (← getEnv).find? name then
            if let some body := info.value? then
              if ← isProp expression then
                return ← visit fuel ((body.instantiateLevelParams info.levelParams levels).beta arguments)
      let mut result : QuerySites := {}
      for argument in arguments do
        if ← isProp argument then result := result.append (← visit fuel argument)
        else if (← sqlMention? argument (includeSource := false)) != some false then
          result := { result with unsupported := true }
      return result

end Belay.Sqlite.Check
