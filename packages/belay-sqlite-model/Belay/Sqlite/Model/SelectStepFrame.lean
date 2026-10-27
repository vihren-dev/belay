import Belay.Sqlite.Model.SelectStepKeeps
import Belay.Sqlite.Model.ReadOnlyFrame

set_option doc.verso true

/-!
A SELECT step keeps the connection, also when it fails (ADR 0017, S6). {name}`Belay.Sqlite.Model.runScriptStep_select_connection`
needs an output without an error. A step that continues always comes from a successful resolution, and a
successful resolution of a SELECT is a query or a prepare error, so no output of a SELECT step, an error
included, changes the connection.
-/

namespace Belay.Sqlite.Model

/-- For every connection and every SELECT statement: if the step continues, with any output, the next
connection is the connection and there is no other execution. In plain words, a SELECT changes nothing, also
when it gives an error. Proof sketch: the step comes from a successful resolution of the SELECT
({name}`runScriptStep_ran`), which is a query or a prepare error ({name}`resolveSelect_shape`), and
{name}`runScriptStep_readOnly_keeps` treats both. -/
theorem runScriptStep_select_keeps {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection next : Connection} {columns source joins filter groupBy orderBy limit offset subqueries having
      distinct compound parameters output} {others : List StatementExecution}
    (step : runScriptStep context clock index connection
      (.select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound)
      parameters = .continued output next others) :
    others = [] ∧ next = connection := by
  obtain ⟨resolved, after, value, original, -⟩ := runScriptStep_ran step
  have found := original
  have selected : ∃ catalog, resolveSelect context connection.resolveState.catalog
      { columns, source, joins, filter, groupBy, orderBy, limit, offset, parent := none, having, distinct,
        compound } subqueries = .ok (resolved, catalog) := by
    simp only [statement_arms, ResolveState.withCatalog] at found
    cases resolution : resolveSelect context connection.resolveState.catalog
      { columns, source, joins, filter, groupBy, orderBy, limit, offset, parent := none, having, distinct,
        compound } subqueries with
    | error failure => rw [resolution] at found; simp [Except.map] at found
    | ok result =>
      obtain ⟨statement, catalog⟩ := result
      rw [resolution] at found
      simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, -⟩ := found
      exact ⟨catalog, rfl⟩
  obtain ⟨catalog, ok⟩ := selected
  exact runScriptStep_readOnly_keeps original (resolveSelect_shape _ _ _ _ _ _ ok) step

end Belay.Sqlite.Model
