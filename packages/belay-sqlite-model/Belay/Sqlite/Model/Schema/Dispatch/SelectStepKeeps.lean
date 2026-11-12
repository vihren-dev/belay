import Belay.Sqlite.Model.Schema.Ddl.StatementArms
import Belay.Sqlite.Model.Schema.Dispatch.StatementArms
import Belay.Sqlite.Model.Schema.Writes.KeysUniqueWrites
import Belay.Sqlite.Model.Queries.Preparation.SelectStepKeeps

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every resolution of a SELECT statement: the resolved statement is a query or a prepare
error, so it is no INSERT from a query. Proof sketch: the resolution of the statement is that of its
query ({name}`resolveSelect`), whose result has one of the two shapes ({name}`resolveSelect_shape`). -/
theorem resolveStatement_select_shape {context : ResolveContext} {state : ResolveState}
    {columns source joins filter groupBy orderBy limit offset subqueries having distinct compound}
    {resolved : Resolved.Statement} {after : ResolveState}
    (found : resolveStatement context state
      (.select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound) =
      .ok (resolved, after)) :
    ∃ catalog, resolveSelect context state.catalog
      { columns, source, joins, filter, groupBy, orderBy, limit, offset, parent := none, having, distinct,
        compound } subqueries = .ok (resolved, catalog) ∧
      ((∃ query subqueries, resolved = .query query subqueries) ∨ ∃ error, resolved = .prepareError error) := by
  have selected : ∃ catalog, resolveSelect context state.catalog
      { columns, source, joins, filter, groupBy, orderBy, limit, offset, parent := none, having, distinct,
        compound } subqueries = .ok (resolved, catalog) := by
    simp only [statement_arms, ResolveState.withCatalog] at found
    cases resolution : resolveSelect context state.catalog
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
  exact ⟨catalog, ok, resolveSelect_shape _ _ _ _ _ _ ok⟩

end Belay.Sqlite.Model
