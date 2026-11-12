import Lean.Meta.AppBuilder
import Lean.Util.Recognizers
import Lean.Meta.Tactic.Util
import Lean.ToExpr
import Lean.Environment
import Lean.Meta.SynthInstance
import Lean.Meta.Closure

set_option doc.verso true

/-! Evaluation of a closed term of data by the kernel, for the premises of the SELECT rules that a
computation decides: the query to which a statement resolves on a fixed catalog, and the table at a
catalog position. The procedure of {lit}`sql_select` reads the value of such a term to choose the next
rule; the proof is {lit}`Eq.refl`, which the kernel checks again when it checks the declaration. No
compiled code runs. -/

namespace Belay.Sqlite.Select
open Lean Meta

/-- The value of a normalized byte: its literal {lit}`OfNat.ofNat n`, or the constructor form
{lit}`UInt8.ofBitVec (BitVec.ofFin ⟨n, _⟩)`. -/
def byteValue? (byte : Expr) : Option Nat :=
  if byte.isAppOfArity ``OfNat.ofNat 3 then byte.appFn!.appArg!.rawNatLit?
  else byte.getAppArgs.back? >>= (·.getAppArgs.back?) >>= (·.getAppArgs[1]?) >>= (·.rawNatLit?)

/-- The bytes of a normalized byte list. -/
partial def normalizedBytes? (list : Expr) : Option (List UInt8) :=
  match list.getAppFnArgs with
  | (``List.nil, _) => some []
  | (``List.cons, #[_, head, tail]) => do
    return (← byteValue? head).toUInt8 :: (← normalizedBytes? tail)
  | _ => none

/-- The literal of a normalized value of a type whose values Lean writes as literals: a string, or a
byte. The literal is definitionally equal to the value. -/
def literalOf? (type value : Expr) : Option Expr :=
  if type.isConstOf ``String then do
    let bytes ← value.getAppArgs[0]? >>= (·.getAppArgs[0]?) >>= (·.getAppArgs[1]?) >>= normalizedBytes?
    let text ← String.fromUTF8? ⟨bytes.toArray⟩
    return mkStrLit text
  else if type.isConstOf ``UInt8 then do
    return toExpr (← byteValue? value).toUInt8
  else none

/-- The normal form of a term of data: the kernel's weak head normal form, and the same for each field
of a constructor, except type parameters and proofs. A string or a byte becomes its literal. A term that
the kernel cannot reduce to a constructor stays as the kernel leaves it. -/
partial def kernelNormalize (term : Expr) : MetaM Expr := do
  if term.isLit then return term
  let environment ← getEnv
  let reduced ← match Kernel.whnf environment (← getLCtx) term with
    | .ok reduced => pure reduced
    | .error _ => throwError "sql_select: the kernel cannot evaluate{indentExpr term}"
  let .const name _ := reduced.getAppFn | return reduced
  let some (.ctorInfo info) := environment.find? name | return reduced
  let mut fields := reduced.getAppArgs
  for index in [info.numParams:fields.size] do
    let field := fields[index]!
    unless ← isProof field do
      fields := fields.set! index (← kernelNormalize field)
  let value := mkAppN reduced.getAppFn fields
  return (literalOf? (← whnfR (← inferType value)) value).getD value

/-- The value of a normalized natural number: a literal, or {lit}`Nat.succ` and {lit}`Nat.zero`. -/
partial def naturalValue? (term : Expr) : Option Nat :=
  match term.rawNatLit? <|> term.nat? with
  | some value => some value
  | none =>
    if term.isAppOfArity ``Nat.succ 1 then (naturalValue? term.appArg!).map (· + 1)
    else if term.isConstOf ``Nat.zero then some 0 else none

/-- The value of a closed natural-number term, computed by the kernel; {lean}`(none : Option Nat)` when
the term has variables or does not normalize to a number. -/
def evaluateNatural? (term : Expr) : MetaM (Option Nat) := do
  if term.hasMVar || term.hasFVar || term.hasLooseBVars then return none
  try return naturalValue? (← kernelNormalize term) catch _ => return none

/-- The proof of a closed equation that evaluation decides, as an auxiliary theorem that the kernel
checks at once: a decision of the equation, which the kernel reduces to {lean}`true`, when the type has
decidable equality, else reflexivity. The result is {lean}`(none : Option Nat)` when the kernel accepts
neither, for example when its recursion is too deep. -/
def evaluationProof? (equation : Expr) : MetaM (Option Expr) := do
  let some (_, left, _) := equation.eq? | return none
  let decision : MetaM Expr := do
    let instance_ ← synthInstance (mkApp (mkConst ``Decidable) equation)
    return mkApp3 (mkConst ``of_decide_eq_true) equation instance_ (← mkEqRefl (mkConst ``Bool.true))
  for proof in [decision, mkEqRefl left] do
    try return some (← mkAuxTheorem equation (← proof)) catch _ => pure ()
  return none

/-- Close an equation whose left side has no variable and no metavariable by evaluation: the kernel normalizes the
left side, the right side is unified with the value, which assigns its metavariables, and the proof is
{lit}`Eq.refl` of the left side. The result is {lean}`false`, with no change, when the goal is not such
an equation or the value does not unify. -/
def closeByEvaluation (goal : MVarId) : MetaM Bool := goal.withContext do
  let type ← whnfR (← instantiateMVars (← goal.getType))
  let some (_, left, right) := type.eq? | return false
  if left.hasMVar || left.hasFVar || left.hasLooseBVars then return false
  let saved ← saveState
  try
    let value ← kernelNormalize left
    if ← isDefEq right value then
      if let some proof ← evaluationProof? (← instantiateMVars type) then
        goal.assign proof
        return true
    saved.restore
    return false
  catch _ =>
    saved.restore
    return false

end Belay.Sqlite.Select
