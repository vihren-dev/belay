import Belay.Sqlite.CheckValueInputs

set_option doc.verso true

/-! Databases that a claim names in its own domain. A claim such as "for every database equal to
{lit}`Database.empty`, the program ends well" holds vacuously at every other database, so the default
candidates cannot refute it. The candidate that its premise names can. -/

namespace Belay.Sqlite.Check

open Lean Meta

/-- The databases that an equality premise of the claim fixes: a premise {lit}`db = d` or {lit}`d = db` of a
database binder {lit}`db`, where {lit}`d` mentions no binder of the claim. The traversal is the one of
{name}`fillValueInputs`: the universal prefix and the bodies of named propositions, up to a query. The
databases are proposals only: refuting with one still decides the premise and the conclusion in the kernel,
so a wrong proposal cannot refute a claim. -/
def domainDatabases (proposition : Expr) (fuel : Nat := 128) : MetaM (Array Expr) :=
  visit fuel proposition #[] #[]
where
  /-- Walk the claim, remembering the database binders that are in scope and the databases found. -/
  visit : Nat → Expr → Array FVarId → Array Expr → MetaM (Array Expr)
    | 0, _, _, found => pure found
    | fuel + 1, proposition, binders, found => do
      match proposition with
      | .mdata _ body => visit fuel body binders found
      | .letE _ _ input body _ => visit fuel (body.instantiate1 input) binders found
      | .forallE name domain body _ =>
        let domain := (← instantiateMVars domain).headBeta
        let found ← if ← isProp domain then pure (found ++ (← fixedDatabase? domain binders).toArray) else pure found
        withLocalDeclD name domain fun input => do
          let binders ← if ← isDefEq domain (mkConst ``Database) then pure (binders.push input.fvarId!) else pure binders
          visit fuel (body.instantiate1 input) binders found
      | _ =>
        let head := proposition.getAppFn
        let arguments := proposition.getAppArgs
        if queryNames.any head.isConstOf then return found
        if head.isLambda then return ← visit fuel (head.beta arguments) binders found
        let .const name levels := head | return found
        let some info := (← getEnv).find? name | return found
        let some body := info.value? | return found
        visit fuel ((body.instantiateLevelParams info.levelParams levels).beta arguments) binders found
  /-- The database that the premise fixes, when it is an equality between a database binder and a term that
  mentions no local variable. -/
  fixedDatabase? (premise : Expr) (binders : Array FVarId) : MetaM (Option Expr) := do
    let some (type, left, right) := premise.eq? | return none
    unless ← isDefEq type (mkConst ``Database) do return none
    let closed (term : Expr) : Bool := !term.hasFVar
    return match left, right with
      | .fvar id, term => if binders.contains id && closed term then some term else none
      | term, .fvar id => if binders.contains id && closed term then some term else none
      | _, _ => none

end Belay.Sqlite.Check
