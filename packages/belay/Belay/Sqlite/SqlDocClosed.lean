import Lean.Elab.DocString
import Belay.Sqlite.EvalDatabase
import Belay.Sqlite.Env
import Belay.Sqlite.Run

set_option doc.verso true

/-! Closed Lean values in the header of a checked SQL documentation block. A block runs while
the file elaborates, so each value it names must be known at that time: a definition of the file
or of an import, not a variable of the declaration that the docstring belongs to. -/

namespace Belay.Sqlite.SqlDoc

open Lean Elab Term Meta Belay.Sqlite

/-- The value of a closed term of the type, which Lean's compiled code computes
({name}`Lean.Meta.evalExpr`). It is unsafe because Lean cannot check that the value has the
type. -/
unsafe def evaluateClosedUnsafe (α : Type) [Nonempty α] (type value : Expr) : TermElabM α :=
  evalExpr α type value

/-- The value of a closed term of the type, with the unsafe evaluation
({name}`evaluateClosedUnsafe`) as its implementation. -/
@[implemented_by evaluateClosedUnsafe]
opaque evaluateClosed (α : Type) [Nonempty α] (type value : Expr) : TermElabM α

/-- Elaborate the term at the type and give its value, as {name}`evaluateDatabase` does for a
database. It gives {lean}`(none : Option Nat)`, without a new error, when the term
has an error or uses a definition with an error, because Lean already shows that error. It is an
error at the term, which names {lit}`what` the term is for, when the term depends on a variable,
is not fully known, uses a noncomputable definition, or cannot be evaluated. -/
def closedValue (α : Type) [Nonempty α] (what : String) (type : Expr) (term : Syntax) :
    TermElabM (Option α) := do
  let value ← elabTermEnsuringType term type
  synthesizeSyntheticMVarsNoPostponing
  let value ← zetaReduce (← instantiateMVars value)
  let environment ← getEnv
  let reached ← reachedConstants value
  if value.hasSyntheticSorry || reached.any (failedDefinition environment) then return none
  if value.hasFVar then
    throwErrorAt term "the {what} depends on a variable, and has no value while the file \
      elaborates; use a definition of the file or of an import, and not a variable of the \
      declaration that this documentation belongs to"
  if value.hasMVar then
    throwErrorAt term "the {what} is not fully known while the file elaborates; use a \
      definition with its type written"
  if let some name := reached.find? (isNoncomputable environment) then
    throwErrorAt term m!"the {what} uses the noncomputable definition {name}, which has no value \
      while the file elaborates; use a definition that Lean can compute"
  try some <$> evaluateClosed α type value
  catch error =>
    throwErrorAt term m!"Lean could not evaluate the {what}: {error.toMessageData}"

/-- The name in a header argument that must be a definition, or an error at the argument. -/
def definitionName (option : String) (argument : Doc.DocArg) : TermElabM Syntax :=
  match argument with
  | .ident name => pure name
  | other => throwErrorAt other.syntax
      m!"the header option {option} takes the name of a closed definition; write ({option} := name)"

/-- The type {lit}`Value`. -/
def valueType : Expr := mkConst ``Belay.Sqlite.Model.Value

/-- The type {lit}`List Output`, the complete observation of a script. -/
def outputsType : Expr := mkApp (mkConst ``List [Level.zero]) (mkConst ``Output)

/-- The type {lit}`List (List Value)`, the values of the parameters of each statement. -/
def valueListsType : Expr :=
  mkApp (mkConst ``List [Level.zero]) (mkApp (mkConst ``List [Level.zero]) valueType)

/-- A value exists, which the evaluation of a closed {lit}`Value` needs. -/
local instance : Nonempty Belay.Sqlite.Model.Value := ⟨.null⟩

/-- The value of a header argument: a number is an INTEGER, a string is TEXT, and a name is a
closed {lit}`Value` definition, or a definition that coerces to one. It is absent when the
definition has an error that Lean already shows. -/
def valueOfArgument (argument : Doc.DocArg) : TermElabM (Option Belay.Sqlite.Model.Value) :=
  match argument with
  | .num literal => pure (some (.integer literal.getNat))
  | .str literal => pure (some (.text literal.getString.toUTF8.toList))
  | .ident name => closedValue _ "value" valueType name

end Belay.Sqlite.SqlDoc
