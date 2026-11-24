import SelectContextCases

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! ADR 0027 case A22 reads the changes counter at the connection reached by a write. -/

namespace SelectContextCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectJoinCases (shop partial_)

/-- The A22 query, which reads the counter of {lit}`changes()`. -/
def changesScript : Script := sql r"SELECT changes()"

/-- The query {lit}`SELECT changes()`, without a source. -/
def changesQuery : Resolved.Query := Resolved.Query.simple [] none [.scalar (.counter .changes)] ["changes()"]

/-- A22: for every context whose counters give {lit}`changes()` the value {lit}`count`, the
program {name}`query` of {name}`changesScript` checks that the result is the one row
{lit}`count` and that the reached context has the connection of the start. The clock, the index
and the database of the context can be any. Proof sketch: {name}`Sql.check_query_of_step_rows` with the
readiness of {name}`Connection.SelectReady.of_phases`, whose counter premise is the premise
{lit}`known`. -/
theorem changes_at (state : ExecutionContext) (count : Nat) (known : state.connection.state.counters.changes = some count) :
    (query changesScript rfl).check
      (fun result final => result = .ok [[.integer count]] ∧ final.connection = state.connection) state := by
  have resolved := resolveStatement_selectNoFrom_columns runContext state.connection.resolveState
    (.call "changes" []) "changes()" "changes()" none (.counter .changes) none none
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (FilterResolves.of_none _ _ _ _)
  rw [show Resolved.Query.simple [] none [.scalar (.counter .changes)] ["changes()"] = changesQuery from rfl] at resolved
  have reads : (Resolved.Statement.query changesQuery []).counterReads = [.changes] := by decide +kernel
  have ready : state.connection.SelectReady 0 [] changesQuery [] _ changesQuery :=
    Connection.SelectReady.of_phases rfl (by rw [reads]; simp [Counters.firstUnknown, Counters.read, known])
      (Resolved.Query.source_none _ _ _ rfl) rfl (by simp) (Resolved.Query.bindWindow_literal _ _ rfl rfl)
      (by simp [Resolved.Query.fails, changesQuery, Resolved.Query.simple])
      (Resolved.Query.mustFail_of_faultless _ _ _ fun _ _ expression member => by
        simp [changesQuery, Resolved.Query.simple, Resolved.Query.expressions, Resolved.Query.keptExpressions,
          Resolved.Output.scalars, Resolved.Output.operands] at member
        subst member; rfl)
      (Resolved.Query.mayFail_of_faultless _ _ _ (by decide +kernel) fun _ _ expression member => by
        simp [changesQuery, Resolved.Query.simple, Resolved.Query.expressions, Resolved.Query.keptExpressions,
          Resolved.Output.scalars, Resolved.Output.operands] at member
        subst member; rfl)
      (by simp [Resolved.Query.distinctCertain, changesQuery, Resolved.Query.simple])
  refine Sql.check_query_of_step_rows rfl rfl state (property := (· ∈ changesQuery.possibleResults
    (state.connection.queryContextAt 0 [] changesQuery []) [[]])) ?_ ?_
  · simp only [runScriptStep_output, resolved]
    rw [resolvedStepOutput_select state.clock state.index _ [] (value := 0) rfl ready]
    exact (changesQuery.returnsResult_possible _ _ _).2 fun _ member => member
  intro result member final same
  have perm := Resolved.Query.perm_of_mem_possibleResults_plain rfl rfl rfl rfl rfl member
  rw [Resolved.filtered_of_filter_none _ rfl] at perm
  refine ⟨?_, same⟩
  rw [List.perm_singleton.mp perm]
  simp only [Connection.queryContextAt, reads]
  simp [Resolved.Query.rowOutput, changesQuery, Resolved.Query.simple, Counters.view, Counters.read, known,
    Resolved.Expr.eval, Resolved.Expr.evaluate]

/-- A22 contrast on {name}`shop` and {name}`partial_`, with the rows of native SQLite 3.51.0:
with the default environment, which knows no counter, {name}`changesScript` alone gives no
result; with the counters of a new connection it gives 0; after {name}`deleteScript`, which
deletes one row, it gives 1 also with the default environment, because the write sets the
counter of the reached context. -/
example : ¬ (shop.run (query changesScript rfl)).returnsResult (fun _ => True) ∧
    (shop.run (query changesScript rfl) Env.newConnection).returnsResult (· = [[.integer 0]]) ∧
    (partial_.run (do let _ ← send deleteScript; query changesScript rfl)).outputs =
      [.done 1, .rows [[.integer 1]]] := by
  decide +kernel

#print axioms changes_at

end SelectContextCases
