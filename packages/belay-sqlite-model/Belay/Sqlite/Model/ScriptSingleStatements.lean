import Belay.Sqlite.Model.ResolveStatementSingle
import Belay.Sqlite.Model.ScriptRunSingleton

set_option doc.verso true

/-! Scripts without INSERT from a query (ADR 0019, D4, amended 2026-10-25). A script whose statements are
none of them written as INSERT from a query meets the condition of {name}`Belay.Sqlite.Model.ScriptConditionsWith` that no
statement it reaches is an INSERT from a query, on every connection. So its statements have one execution
each, and the laws that read the model's own run hold for every complete execution. -/

namespace Belay.Sqlite.Model

/-- For every context, optional clock, index, connection and statements with their values, none of which is
written as INSERT from a query ({name}`Syntax.Statement.isInsertSelect`): no statement that the run reaches
resolves to an INSERT from a query without rules. Plain words: a script that has no INSERT from a query has one
execution for each statement, on every connection. Proof sketch: induction on the statements; the head
resolves to such a statement by {name}`resolveStatement_single`, and the rest meets the condition on every
connection by the induction hypothesis. -/
theorem ScriptConditionsWith.of_not_insertSelect (context : ResolveContext) (clock : Option Clock) :
    ∀ (index : Nat) (connection : Connection) (script : List (Syntax.Statement × List Value)),
      (∀ entry ∈ script, entry.1.isInsertSelect = false) →
        ScriptConditionsWith (fun _ => True) (fun _ _ _ resolved _ => resolved.fromQuery = false) context clock index connection script
  | _, _, [], _ => trivial
  | index, connection, (statement, parameters) :: rest, notQuery => by
    refine ⟨fun _ resolved after _ found _ _ =>
      resolveStatement_single context connection.resolveState after statement resolved
        (notQuery _ (List.mem_cons_self ..)) found, ?_⟩
    cases step : runScriptStep context clock index connection statement parameters with
    | ended reason => trivial
    | continued output next others =>
      intro execution _
      exact ScriptConditionsWith.of_not_insertSelect context clock (index + 1) execution.next rest
        fun entry member => notQuery entry (List.mem_cons_of_mem _ member)

end Belay.Sqlite.Model
