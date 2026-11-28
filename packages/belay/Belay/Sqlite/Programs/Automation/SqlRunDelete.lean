import Belay.Sqlite.Programs.Automation.DeleteCoverage
import Belay.Sqlite.Programs.Automation.SqlRunKindRules
import Belay.Sqlite.Programs.StatementRunLaws.SelectCatalogExecution
import Belay.Sqlite.Schema.Dispatch.SelectCatalogExecution

set_option doc.verso true

/-! Use a catalog hint to supply the premises of the existing DELETE step and coverage rules. -/

namespace Belay.Sqlite.Run
open Model Lean Meta Elab Tactic Term
open scoped DeleteCoverage

/-- Resolution on the known catalog identifies the DELETE and its table on the actual database.
The table contains the actual rows at the resolved position. Proof sketch: transport the
resolution by {name}`Database.resolveState_of_catalog` and use {name}`Database.table_of_catalog`. -/
private theorem deleteFacts {db catalog : Database} (schema : db.HasCatalog catalog) (env : Env)
    (stmt : Model.Syntax.Statement) {pos filter subs shape}
    (resolved : resolveStatement runContext (catalog.raw.connection {}).resolveState stmt =
      .ok (.delete pos filter [] subs none, (catalog.raw.connection {}).resolveState))
    (table : catalog.raw.catalog.tableAt pos = some shape) :
    resolveStatement runContext (db.raw.connection env.counters).resolveState stmt =
      .ok (.delete pos filter [] subs none, (db.raw.connection env.counters).resolveState) ∧
    db.raw.table pos = some ⟨shape, db.raw.rows.getD pos []⟩ := by
  constructor
  · rwa [Database.resolveState_of_catalog db catalog schema env.counters]
  · exact (Database.table_of_catalog schema table).1

/-- Use a supplied catalog to resolve a plain DELETE at a fresh connection. Apply the
registered kind rule with the derived lookup and try the filter coverage proof. -/
def catalogDelete? (hints : Hints) (goal : MVarId) (script : Expr) :
    TacticM (Option (List MVarId × List MVarId)) := goal.withContext do
  let target ← whnfR (← goal.getType)
  let ctx := target.appArg!
  unless ctx.isAppOfArity ``ExecutionContext.initial 2 do return none
  let env ← exprToSyntax ctx.appArg!
  let sql ← exprToSyntax script
  for hint in hints do
    let saved ← Tactic.saveState
    try
      setGoals [goal]
      withoutRecover <| Term.withoutErrToSorry <| evalTactic (← `(tactic|
        (have names := Database.resolveState_of_catalog _ _ $hint ($env).counters
         obtain ⟨found, present⟩ := deleteFacts $hint $env (($sql).statements[0]'(by decide)).1
           (by rfl) (by rfl))))
      let prepared ← getMainGoal
      let some (pending, cases) ← applyKindRule (#[← `(found), ← `(present)] ++ hints) prepared
        | throwError "Expected the plain DELETE rule."
      let mut remaining := []
      for premise in pending do
        setGoals [premise]
        let rule := mkIdent `rule
        if (← premise.getTag).eraseMacroScopes == `modeled then
          evalTactic (← `(tactic| try (cover_delete $rule, present)))
        remaining := remaining ++ (← getGoals)
      return some (remaining, cases)
    catch _ => saved.restore
  return none

end Belay.Sqlite.Run
