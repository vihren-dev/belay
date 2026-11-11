import Belay.Sqlite.Programs.Claims.SelectResultBridge

set_option doc.verso true

/-! The error bridge of a SELECT: for a script of one SELECT, the observation {lit}`returnsError` of a
run is the claim {lit}`Sql.check` that every branch returns an error with the property. It is the
error counterpart of the successful-result bridge and serves {lit}`Fails`. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- For every output that is rows, an error or a choice of at least two results, and every property
{lit}`E` of a result code: each output that may be selected from it has a {name}`queryResult` that is
an error with a code that satisfies {lit}`E`, exactly when the output is such an error
({name}`Output.returnsError`). A result, also an empty one, is no error. Proof sketch: by the three
shapes. -/
theorem OutputChoice.forall_queryError_iff {actual : Output}
    (shape : (∃ rows, actual = .rows rows) ∨ (∃ code, actual = .error code) ∨
      ∃ first second rest, actual = .oneOf (first :: second :: rest))
    (property : Nat → Prop) :
    (∀ selected, OutputChoice actual selected →
      match queryResult selected with | .ok _ => False | .error code => property code) ↔
    actual.returnsError property := by
  rcases shape with ⟨rows, rfl⟩ | ⟨code, rfl⟩ | ⟨first, second, rest, rfl⟩
  · simp only [Output.returnsError, iff_false]
    exact fun each => each _ (OutputChoice.actual _)
  · constructor
    · exact fun each => each _ (OutputChoice.actual _)
    · rintro holds selected (rfl | absurd)
      · exact holds
      · exact absurd.elim
  · simp only [Output.returnsError, iff_false]
    exact fun each => each _ (OutputChoice.actual _)

/-- For every script of one SELECT, context and property {lit}`E` of a result code: the program
{name}`query` of the script checks the post "an error with a code that satisfies {lit}`E`" at the
context exactly when the output of the step is such an error ({name}`Output.returnsError`). A step
that ends the run fails the check. Proof sketch: as {name}`check_query_returnsResult_iff`, with
{name}`OutputChoice.forall_queryError_iff`. -/
theorem check_query_returnsError_iff {script : Script} {one : script.statements.length = 1}
    (select : script.isSelect = true) (property : Nat → Prop) (state : ExecutionContext) :
    (query script one).check (fun result _ => match result with | .ok _ => False | .error code => property code) state ↔
      (runScriptStep runContext state.clock state.index state.connection (script.statements[0]'(by rw [one]; exact Nat.one_pos)).1
        (script.statements[0]'(by rw [one]; exact Nat.one_pos)).2).output.returnsError property := by
  obtain ⟨values, columns, source, joins, filter, groupBy, orderBy, limit, offset, subqueries, having, distinct, compound,
    same⟩ := Script.select_shape select
  obtain rfl : script = ⟨[(.select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound,
      values)]⟩ := by cases script; simp_all
  rw [check_query]
  simp only [List.getElem_cons_zero]
  cases step : runScriptStep runContext state.clock state.index state.connection
      (.select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound) values with
  | ended reason => simp [RunStep.output, Output.returnsError]
  | continued actual next others =>
    obtain ⟨rfl, rfl⟩ := runScriptStep_select_keeps step
    simp only [RunStep.output, RunStep.executions, List.mem_singleton, forall_eq]
    exact OutputChoice.forall_queryError_iff (runScriptStep_select_output step) property

/-- For every script of one SELECT, database, environment and property {lit}`E` of a result code: the
run of {name}`query` of the script returns an error with {lit}`E` exactly when the program checks the
post "an error with a code that satisfies {lit}`E`" from the new connection of the environment. A
successful result, also an empty one, satisfies neither side. Proof sketch:
{name}`Run.query_returnsError_iff` and {name}`check_query_returnsError_iff`. -/
theorem Run.returnsError_query_iff {script : Script} {one : script.statements.length = 1}
    (select : script.isSelect = true) (db : Database) (env : Env) (property : Nat → Prop) :
    (db.run (query script one) env).returnsError property ↔
      (query script one).check (fun result _ => match result with
        | .ok _ => False | .error code => property code) (ExecutionContext.initial db env) := by
  rw [Run.query_returnsError_iff one, check_query_returnsError_iff select]
  rfl

end Belay.Sqlite
