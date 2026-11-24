import ReplacedNonQueryOutputs
import Belay

set_option doc.verso true

/-! ADR 0033 retention of the former write laws with their original premises. -/

namespace Belay.Sqlite.Model.ReplacedWriteModes
open Resolved

/-- The former {lit}`Output.ofStep_delete_ne_oneOf`. The DELETE output never offers a choice of rows. Proof sketch: apply the general non-query output law. -/
theorem Output.ofStep_delete_ne_oneOf (clock : Int) (parameters : List Value) (before : SqlState)
    (run : StatementRun) (transition : SqlTransition) (target : Nat) (filter returning subqueries rules)
    (alternatives : List (List (List Value))) :
    Output.ofStep clock parameters (.delete target filter returning subqueries rules) before run transition ≠
      .oneOf alternatives := by
  exact Output.ofStep_ne_oneOf_of_not_query _ _ _ _ _ _ (fun _ _ eq => by cases eq) _

#print axioms Output.ofStep_delete_ne_oneOf

/-- The former {lit}`runScriptStep_delete_ne_oneOf`. The DELETE step never offers a choice of rows. Proof sketch: apply the general non-query output law. -/
theorem runScriptStep_delete_ne_oneOf {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution} {target : Nat}
    {filter : Option Resolved.Expr} {returning subqueries rules} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.delete target filter returning subqueries rules, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (alternatives : List (List (List Value))) : output ≠ .oneOf alternatives := by
  exact runScriptStep_ne_oneOf_of_not_query found (fun _ _ eq => by cases eq) step _

#print axioms runScriptStep_delete_ne_oneOf

/-- The former {lit}`Output.ofStep_update_ne_oneOf`. The UPDATE output never offers a choice of rows. Proof sketch: apply the general non-query output law. -/
theorem Output.ofStep_update_ne_oneOf (clock : Int) (parameters : List Value) (before : SqlState)
    (run : StatementRun) (transition : SqlTransition) (target : Nat) (assignments filter returning subqueries rules)
    (alternatives : List (List (List Value))) :
    Output.ofStep clock parameters (.update target assignments filter returning subqueries rules) before run
      transition ≠ .oneOf alternatives := by
  exact Output.ofStep_ne_oneOf_of_not_query _ _ _ _ _ _ (fun _ _ eq => by cases eq) _

#print axioms Output.ofStep_update_ne_oneOf

/-- The former {lit}`runScriptStep_update_ne_oneOf`. The UPDATE step never offers a choice of rows. Proof sketch: apply the general non-query output law. -/
theorem runScriptStep_update_ne_oneOf {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {target : Nat} {assignments : List (Nat × Resolved.Expr)} {filter : Option Resolved.Expr}
    {returning subqueries rules} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.update target assignments filter returning subqueries rules, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (alternatives : List (List (List Value))) : output ≠ .oneOf alternatives := by
  exact runScriptStep_ne_oneOf_of_not_query found (fun _ _ eq => by cases eq) step _

#print axioms runScriptStep_update_ne_oneOf

end Belay.Sqlite.Model.ReplacedWriteModes
