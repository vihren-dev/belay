import Belay.Sqlite.CheckBudget
import Belay.Sqlite.CheckCompiled
import Belay.Sqlite.ReplayEvaluation
import Belay.Sqlite.SqlSource
import Belay.Sqlite.DbBang
import Belay.Sqlite.CounterexampleWitness

set_option doc.verso true

/-! Data for background SQL checks. Compiled code computes each value under the time limit of
the check, and the kernel checks it against the original expression. -/

namespace Belay.Sqlite.Check

open Lean Meta Elab Term

/-- A database exists: the empty one. Compiled evaluation needs it for its result type. -/
instance : Nonempty Database := ⟨Database.empty⟩

/-- Raw database data exists: the data of the empty database. -/
instance : Nonempty Database.Raw := ⟨Database.empty.raw⟩

/-- Reject a reified value with more than {name}`maxDataNodes` nodes or {name}`maxLiteralBytes`
literal bytes. The limit keeps the kernel check and the replay of the value small; a value that
is too large leaves the background check inconclusive, and the explicit witness primitives
remain available. -/
def checkDataSize (value : Expr) : MetaM Unit := do
  let mut pending := #[value]
  let mut literalBytes := 0
  for _ in List.range maxDataNodes do
    if pending.isEmpty then return
    let current := pending.back!
    pending := pending.pop
    match current with
    | .lit (.strVal text) => literalBytes := literalBytes + text.utf8ByteSize
    | .lit (.natVal number) => literalBytes := literalBytes + number.log2 / 8 + 1
    | .app function argument => pending := (pending.push function).push argument
    | .mdata _ body => pending := pending.push body
    | _ => pure ()
    if literalBytes > maxLiteralBytes then throwError "SQL checking reached its literal byte limit"
  unless pending.isEmpty do throwError "SQL checking reached its literal data limit"

/-- Compute data with compiled code ({name}`compiledValue`) and kernel-check equality with the
original expression. Use this for owned sampling, shrinking and model-observation computations.
A compiled implementation that differs from its definition cannot change the result: the closure
check refuses it, and the kernel compares the value with the expression. -/
def dataValue (α : Type) [ToExpr α] [Nonempty α] (expression : Expr) (excluded : Array Name := #[])
    (excludedLocals : Array FVarId := #[]) : TermElabM α := do
  auditDependencies #[expression] excluded excludedLocals
  let value ← compiledValue α (toTypeExpr α) expression
  let literal := toExpr value
  checkDataSize literal
  discard <| certify (← mkEq expression literal) (← mkEqRefl literal) excluded excludedLocals
  return value

/-- Obtain a database with compiled code ({name}`compiledValue`). Its exact raw catalog and rows
are checked against the original term in the kernel. Use the explicit witness primitive when
the background data limit is too small for a supplied database. -/
def databaseValue (expression : Expr) (excluded : Array Name := #[])
    (excludedLocals : Array FVarId := #[]) : TermElabM Database := do
  auditDependencies #[expression] excluded excludedLocals
  checkWithKernel (mkApp2 (mkConst ``id [Level.one]) (mkConst ``Database) expression)
  let value ← compiledValue Database (mkConst ``Database) expression
  let literal := toExpr value.raw
  checkDataSize literal
  let projection := mkApp (mkConst ``Database.raw) expression
  discard <| certify (← mkEq projection literal) (← mkEqRefl literal) excluded excludedLocals
  return value

/-- Obtain a script with compiled code ({name}`dataValue`), retaining
its actual bindings. Equality is checked against the supplied statement projection; source
annotations only recover the text later. -/
def scriptValue (expression : Expr) (excluded : Array Name := #[])
    (excludedLocals : Array FVarId := #[]) : TermElabM Script := do
  let statements ← dataValue (List (Model.Syntax.Statement × List Value))
    (mkApp (mkConst ``Script.statements) expression) excluded excludedLocals
  return ⟨statements⟩

/-- The SQL text of a database term's schema: the source of a {lit}`db!` constant, or the
schema text of a database that the checker generated ({name}`schemaSourceKey`). None for other
terms. -/
def schemaText? (database : Expr) : MetaM (Option String) := do
  if let some source ← sourceOf databaseSourceKey database then return some source.text
  return (← sourceOf schemaSourceKey database).map (·.text)

/-- The term of a generated database, with the SQL text of its schema when there is one, so
that its replay can build it from that text ({lit}`Replay.schemaRowsSql`). -/
def generatedExpr (raw : Database.Raw) (schema : Option String) : Expr :=
  match schema with
  | some text => withSchemaText text (databaseExpr raw)
  | none => databaseExpr raw

/-- The witness with a generated database ({name}`generatedExpr`) that carries its value
({name}`Witness.value`). -/
def Witness.generated (witness : Witness) (database : Database) (schema : Option String) : Witness :=
  { witness with database := generatedExpr database.raw schema, value := some database }

/-- The database value of a witness: the value that it carries ({name}`Witness.value`), else the
checked compiled value of its term ({name}`databaseValue`). -/
def witnessDatabase (witness : Witness) (excluded : Array Name := #[])
    (excludedLocals : Array FVarId := #[]) : TermElabM Database :=
  match witness.value with
  | some database => pure database
  | none => databaseValue witness.database excluded excludedLocals

end Belay.Sqlite.Check
