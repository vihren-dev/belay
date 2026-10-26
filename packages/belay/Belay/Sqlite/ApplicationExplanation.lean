import Belay.Sqlite.ApplicationClaims

set_option doc.verso true

namespace Belay.Sqlite

open Lean

/-- Whether a predicate is the function that is true at every context, which is the admitted predicate
of a claim without a guard. -/
def admitsEveryContext (predicate : Expr) : Bool :=
  match predicate.consumeMData with
  | .lam _ _ body _ => body.consumeMData.isConstOf ``True
  | _ => false

/-- Explain a full-state or a scoped simulation claim after elaboration. The text states the admitted
contexts, the migration domain, the observation scope, the context relation and the call conditions.
It returns none for any other proposition. The two claims differ in what they compare: the full-state
claim compares complete final contexts, and the scoped claim compares results, outputs and the
relation only. -/
def applicationExplanation (claim : Expr) : Option MessageData :=
  let arguments := claim.getAppArgs
  let isScoped := claim.getAppFn.constName? == some ``ScopedClaim
  let admitted := arguments[if isScoped then arguments.size - 3 else arguments.size - 2]?
  let domain := match admitted with
    | some predicate => if admitsEveryContext predicate then
        m!"Admitted contexts: every execution context, so the claim covers any clock, counters, settings and statement index at which the migration succeeds."
      else m!"Admitted contexts: the contexts that satisfy {predicate}. A guard is read by Holds.inContext at the real context, with its clock, counters and settings. A context that fails it adds no obligation."
    | none => m!""
  let shared := m!"Migration domain: the claim applies at an admitted context only when the migration succeeds at that original context, on its actual run and on every permitted raw or concrete branch. Where it fails, the instance is vacuous. The quiet view hides only the successful outputs of the migration; errors, stops and returned values remain. The statement index counts every migration step."
  match claim.getAppFn.constName? with
  | some ``Simulation => some
    m!"Full-state simulation claim.\n{domain}\n{shared}\nCall conditions, for every call name and argument: the old call followed by the migration commutes with the migration followed by the partner call. Both orders return the call's result, and compare the projected outputs of the actual run and of every branch and the complete final connection, clock and raw next-statement index exactly, including counters and transaction snapshots. The old call also keeps the domain: every branch that returns a value ends at an admitted context where the migration succeeds.\nConsequence: it lifts to every application over the calls (Simulation.commutes_application), also when later calls depend on earlier results. It fails for a call when the migration changes a part of the context that the call moves differently, for example a trigger that raises the change counter."
  | some ``ScopedClaim => some
    m!"Scoped simulation claim.\n{domain}\n{shared}\nContext relation: {arguments[arguments.size - 2]?.getD (mkConst ``True)}. The relation is the only place where the two sides may differ.\nEntry condition: every returning branch of the migration, from an admitted context where it succeeds, reaches a context that the relation relates to the original context.\nCall conditions, for every call name and argument and every pair of related contexts: the old call and its partner give equal results and equal outputs on the actual run, every branch of one has a matching branch of the other in both directions, and the final contexts are related again. Each side runs from its own clock, statement index and connection.\nConsequence: it lifts to every application over the calls (ScopedSimulation.application and ScopedClaim.application). It never claims that the final contexts are equal: counters, indexes and other parts that the relation ignores can differ. A call that reads such a part fails the call condition."
  | _ => none

end Belay.Sqlite
