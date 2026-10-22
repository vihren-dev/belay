import Lean.Elab.SyntheticMVars
import Lean.Meta.Eval
import Belay.Sqlite.Database

set_option doc.verso true

/-! The value of a database term while the file elaborates, so that {lit}`sql! db r"..."` can
resolve its text against the catalog of {lit}`db`. Lean evaluates the term with its compiled
code. A term with a variable has no value at that time, and a term with an error already shows
that error. -/

namespace Belay.Sqlite

open Lean Elab Term Meta

/-- The value of a closed term of type {name}`Database`, which Lean's compiled code computes
({name}`Lean.Meta.evalExpr`). It is unsafe because Lean cannot check that the value has the
type. -/
unsafe def evaluateDatabaseExprUnsafe (value : Expr) : TermElabM Database :=
  evalExpr Database (mkConst ``Database) value

/-- The value of a closed term of type {name}`Database`, with the unsafe evaluation
({name}`evaluateDatabaseExprUnsafe`) as its implementation. -/
@[implemented_by evaluateDatabaseExprUnsafe]
opaque evaluateDatabaseExpr (value : Expr) : TermElabM Database

/-- The constants that the term uses, and, for each constant of the file that elaborates, the
constants that its value uses, each one once. A definition of an imported module compiled with no
error, so the search does not look into it. For example, for the term {lit}`wrap` with
{lit}`def wrap : Database := failed`, it gives {lit}`wrap` and {lit}`failed`, and then the
constants of {lit}`failed`. -/
def reachedConstants (value : Expr) : TermElabM (Array Name) := do
  let environment ← getEnv
  let mut pending := value.getUsedConstants.toList
  let mut seen : NameSet := {}
  let mut reached := #[]
  repeat
    match pending with
    | [] => break
    | name :: rest =>
      pending := rest
      if seen.contains name then continue
      seen := seen.insert name
      reached := reached.push name
      if (environment.getModuleIdxFor? name).isNone then
        if let some body := (environment.find? name).bind (·.value?) then
          pending := body.getUsedConstants.toList ++ pending
  return reached

/-- Whether the definition of the name has an error, which Lean showed where it is defined: its
value holds the {lit}`sorry` that Lean puts in place of a term with an error. A {lit}`sorry`
that the user writes is not such a {lit}`sorry`. -/
def failedDefinition (environment : Environment) (name : Name) : Bool :=
  ((environment.find? name).bind (·.value?)).any (·.hasSyntheticSorry)

/-- Elaborate the term as a {name}`Database` and give its value. It gives
{lean}`(none : Option Database)`, without a new error, when the term has an error or uses a
definition with an error, also through other definitions of the file ({name}`reachedConstants`,
{name}`failedDefinition`), because Lean already shows that error. It is an error at the term
when the term depends on a variable, when it is not fully known, when it uses a noncomputable
definition, or when Lean cannot evaluate it. -/
def evaluateDatabase (term : Syntax) : TermElabM (Option Database) := do
  let value ← elabTermEnsuringType term (mkConst ``Database)
  synthesizeSyntheticMVarsNoPostponing
  let value ← instantiateMVars value
  let environment ← getEnv
  let reached ← reachedConstants value
  if value.hasSyntheticSorry || reached.any (failedDefinition environment) then return none
  let value ← zetaReduce value
  if value.hasFVar then
    throwErrorAt term "sql! resolves against the value of the database, but the database term \
      depends on a variable and has no value while the file elaborates; use sql, which resolves \
      when it runs, or a database defined earlier in the file"
  if value.hasMVar then
    throwErrorAt term "sql! needs the database term to be fully known while the file elaborates; \
      use a database defined earlier in the file"
  if let some name := reached.find? (isNoncomputable environment) then
    throwErrorAt term m!"sql! cannot compute the database, because it uses the noncomputable \
      definition {name}; use sql, which resolves when it runs, or a database that Lean can compute"
  try some <$> evaluateDatabaseExpr value
  catch error =>
    throwErrorAt term m!"sql! could not evaluate the database term: {error.toMessageData}; \
      use sql, which resolves when it runs, or a database that Lean can compute"

end Belay.Sqlite
