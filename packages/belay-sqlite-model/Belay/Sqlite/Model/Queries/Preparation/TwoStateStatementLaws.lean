import Belay.Sqlite.Model.Queries.Evaluation.QueryForm
import Belay.Sqlite.Model.Shared.Resolved.Resolved

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Whether a resolved statement reads the initial database: it is a query, or has a subquery, with a
source in it ({name}`Resolved.Query.readsInitial`). A statement that is not a query reads no
initial database, because the resolver gives sources of the initial origin only to queries. -/
def Resolved.Statement.readsInitial : Resolved.Statement → Bool
  | .query main inner => main.readsInitial || inner.any Resolved.Query.readsInitial
  | .createView .. | .createTable .. | .createIndex .. | .createTrigger .. | .addColumn .. | .rewrite _ | .dropColumn .. | .drop ..
  | .begin | .commit | .rollback | .insert .. | .update .. | .upsert .. | .insertSelect .. | .delete .. | .prepareError _
  | .setting .. => false

/-- For every query and subqueries, if the statement {lit}`query subqueries` reads no initial database, then
neither does the query and neither does any subquery. Proof sketch: unfold {name}`Resolved.Statement.readsInitial`;
a disjunction that is false has two false sides, and a failed {lit}`any` has a false test for each member. -/
theorem Resolved.Statement.readsInitial_query {query : Resolved.Query} {subqueries : List Resolved.Query}
    (plain : (Resolved.Statement.query query subqueries).readsInitial = false) :
    query.readsInitial = false ∧ ∀ other ∈ subqueries, other.readsInitial = false := by
  simp only [Resolved.Statement.readsInitial, Bool.or_eq_false_iff, List.any_eq_false] at plain
  exact ⟨plain.1, fun other found => by simpa using plain.2 other found⟩

end Belay.Sqlite.Model
