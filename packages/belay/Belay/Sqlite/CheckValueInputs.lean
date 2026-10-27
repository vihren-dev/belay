import Belay.Sqlite.CheckClaim

set_option doc.verso true

/-! Inputs of a claim that the search can fill from its configured values. -/

namespace Belay.Sqlite.Check

open Lean Meta

/-- Fill unassigned quantified SQL Value inputs with a selected value. Database and Env
inputs use the witness's typed selector; other types need explicit named inputs. The default
search repeats this operation over its configured values, rather than assuming NULL proves
anything. Named inputs and the arbitrary selector primitive remain available for other types.
The same value is used for every otherwise unassigned Value binder in one candidate. -/
def fillValueInputs (proposition : Expr) (witness : Witness) (value : Value)
    (fuel : Nat := 128) : MetaM Witness :=
  visit fuel proposition witness
where
  /-- Traverse the universal prefix and named proposition definitions without unfolding
  query evaluation or universal success execution. -/
  visit : Nat → Expr → Witness → MetaM Witness
    | 0, _, _ => throwError "SQL input inference exhausted its declaration budget"
    | fuel + 1, proposition, witness => do
      match proposition with
      | .mdata _ body => visit fuel body witness
      | .letE _ _ input body _ => visit fuel (body.instantiate1 input) witness
      | .forallE name domain body _ =>
        if ← isProp domain then
          withLocalDeclD name domain fun input => visit fuel (body.instantiate1 input) witness
        else
          let supplied := witness.named.any (fun (found, _) => found == name)
          let witness ← if !supplied && (← isDefEq domain (mkConst ``Value)) then
              pure { witness with named := witness.named.push (name, toExpr value) }
            else pure witness
          visit fuel (body.instantiate1 (← witness.choose name domain)) witness
      | _ =>
        let head := proposition.getAppFn
        let arguments := proposition.getAppArgs
        if queryNames.any head.isConstOf then return witness
        if head.isLambda then return ← visit fuel (head.beta arguments) witness
        let .const name levels := head | return witness
        let some info := (← getEnv).find? name | return witness
        let some body := info.value? | return witness
        visit fuel ((body.instantiateLevelParams info.levelParams levels).beta arguments) witness

end Belay.Sqlite.Check
