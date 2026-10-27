import Belay.Sqlite.CounterexampleCertificate
import Belay.Sqlite.ExecutionObservations
import Belay.Sqlite.ExecutionViewEquivalence

set_option doc.verso true

/-! Refute an equivalence claim by the runs that differ. The equivalence relations between programs
are structures, and each has a field {lit}`actual` that says the actual runs agree. A false claim at a
concrete context can have actual runs that differ, and a decision procedure shows the difference. A claim
whose actual runs agree and whose branches differ is not refuted here. -/

namespace Belay.Sqlite.Check
open Lean Meta

/-- The equivalence relations between two programs at a context. Each has a field {lit}`actual` that
compares the actual runs of the programs. The two programs are the second and third explicit arguments,
and the context is the last. -/
def programRelationNames : Array Name :=
  #[``Sql.EquivAt, ``Sql.ObservationEquivAt, ``Sql.View.EquivAt, ``Sql.View.ObservationEquivAt]

/-- A proof that two values differ. The proof decides the inequality when the type has a decision
procedure. Otherwise it finds a field of a structure that differs, in the kernel, and uses
{name}`congrArg` to lift the difference of the field. Fields without a decision procedure are skipped. The
fuel bounds the depth of nested structures. A pair of values that do not differ in any decidable
field throws, because it gives no refutation. -/
def refuteDifference (excluded : Array Name) (excludedLocals : Array FVarId) :
    Nat → Expr → Expr → MetaM Expr
  | 0, _, _ => throwError "the values do not differ in a decidable field within the nesting limit"
  | depth + 1, left, right => do
    let equality ← mkEq left right
    try return ← decideCertified (mkNot equality) excluded excludedLocals catch _ => pure ()
    let type ← whnf (← inferType left)
    let some structureName := type.getAppFn.constName?
      | throwError "the values have no decision procedure and are no structure"
    unless isStructure (← getEnv) structureName do
      throwError "the values have no decision procedure and are no structure"
    for field in getStructureFields (← getEnv) structureName do
      let attempted ← try
          let different ← refuteDifference excluded excludedLocals depth
            (← mkProjection left field) (← mkProjection right field)
          let projection ← withLocalDeclD `value type fun value => do
            mkLambdaFVars #[value] (← mkProjection value field)
          some <$> withLocalDeclD `same equality fun same => do
            mkLambdaFVars #[same] (mkApp different (← mkCongrArg projection same))
        catch _ => pure none
      if let some proof := attempted then return proof
    throwError "the values do not differ in a decidable field"

/-- The depth of nested structures that the comparison of actual runs follows: a run, its connection, the
state of the connection and its database. -/
def actualRunNesting : Nat := 6

/-- A proof of {lit}`False` from a proof of an equivalence claim, when the actual runs of the claim differ at
its concrete context. The difference is decided and certified in the kernel. The result is none when the
claim is no such relation. A relation whose actual runs agree, or that no decision procedure compares,
throws, because it gives no refutation. -/
def refuteByActualRun? (claimed : Expr) (excluded : Array Name := #[]) (excludedLocals : Array FVarId := #[]) :
    MetaM (Option Expr) := do
  let proposition ← instantiateMVars (← inferType claimed)
  unless programRelationNames.any proposition.getAppFn.isConstOf do return none
  let actual ← mkProjection claimed `actual
  let some (_, left, right) := (← inferType actual).eq?
    | throwError "the field actual of this relation is no equality"
  let different ← refuteDifference excluded excludedLocals actualRunNesting left right
  return some (mkApp different actual)

end Belay.Sqlite.Check
