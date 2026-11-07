import Belay.Sqlite.RunResultSteps
import Belay.Sqlite.Queries
import Belay.Sqlite.ExecutionSpecifications
import Belay.Sqlite.Model.SelectOutputShape

set_option doc.verso true

/-! The successful-result bridge of a SELECT (ADR 0027, D2): for a script of one SELECT, the
observation {lit}`returnsResult` of a run is the claim {lit}`Sql.check` that every branch returns a
successful result with the property. Both read the same step. A SELECT step that continues the run
gives rows, an error, or a choice of at least two results
({name}`Belay.Sqlite.Model.runScriptStep_select_output`), so a universal claim over the choices is
never true without a result; a step that ends the run makes both sides false. -/

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- For every script that is one SELECT ({name}`Script.isSelect`), the statements of the script are one
SELECT statement with its values. Proof sketch: the definition of {name}`Script.isSelect` and
{name}`Model.Syntax.Statement.select_of_asQuery`. -/
theorem Script.select_shape {script : Script} (select : script.isSelect = true) :
    ∃ values columns source joins filter groupBy orderBy limit offset subqueries having distinct compound,
      script.statements = [(.select columns source joins filter groupBy orderBy limit offset subqueries having
        distinct compound, values)] := by
  unfold Script.isSelect at select
  split at select
  · rename_i statement values same
    obtain ⟨columns, source, joins, filter, groupBy, orderBy, limit, offset, subqueries, having, distinct, compound, rfl⟩ :=
      Model.Syntax.Statement.select_of_asQuery select
    exact ⟨values, columns, source, joins, filter, groupBy, orderBy, limit, offset, subqueries, having, distinct, compound, same⟩
  all_goals simp at select

/-- For every output that is rows, an error or a choice of at least two results, and every property
{lit}`Q` of a result: each output that may be selected from it ({name}`OutputChoice`) has a
{name}`queryResult` that is a successful result with {lit}`Q`, exactly when the output returns a
result with {lit}`Q` ({name}`Output.returnsResult`). The raw choice reads the first result and each
concrete choice one result of the list. Proof sketch: by the three shapes; an error is never a
successful result, and the first result of a choice is a member of it. -/
theorem OutputChoice.forall_queryResult_iff {actual : Output}
    (shape : (∃ rows, actual = .rows rows) ∨ (∃ code, actual = .error code) ∨
      ∃ first second rest, actual = .oneOf (first :: second :: rest))
    (property : List (List Value) → Prop) :
    (∀ selected, OutputChoice actual selected →
      match queryResult selected with | .ok rows => property rows | .error _ => False) ↔
    actual.returnsResult property := by
  rcases shape with ⟨rows, rfl⟩ | ⟨code, rfl⟩ | ⟨first, second, rest, rfl⟩
  · constructor
    · exact fun each => each _ (OutputChoice.actual _)
    · rintro holds selected (rfl | absurd)
      · exact holds
      · exact absurd.elim
  · simp only [Output.returnsResult, iff_false]
    exact fun each => each _ (OutputChoice.actual _)
  · constructor
    · exact fun each => ⟨List.cons_ne_nil _ _, fun rows member => each _ (OutputChoice.rows member)⟩
    · rintro ⟨-, all⟩ selected (rfl | ⟨rows, member, rfl⟩)
      · exact all first List.mem_cons_self
      · exact all rows member

/-- For every script of one SELECT and every context and property {lit}`Q` of a result: the program
{name}`query` of the script checks the post "a successful result with {lit}`Q`" at the context exactly
when the output of the step of the statement at the context returns a result with {lit}`Q`
({name}`Output.returnsResult`). A step that ends the run gives {name}`Output.unmodeled`, which returns
nothing, and fails the check. Proof sketch: {name}`check_query` reads the step; a SELECT has one
execution ({name}`runScriptStep_select_keeps`), and its output has one of the shapes of
{name}`runScriptStep_select_output`, so {name}`OutputChoice.forall_queryResult_iff` applies. -/
theorem check_query_returnsResult_iff {script : Script} {one : script.statements.length = 1}
    (select : script.isSelect = true) (property : List (List Value) → Prop) (state : ExecutionContext) :
    (query script one).check (fun result _ => match result with | .ok rows => property rows | .error _ => False) state ↔
      (runScriptStep runContext state.clock state.index state.connection (script.statements[0]'(by rw [one]; exact Nat.one_pos)).1
        (script.statements[0]'(by rw [one]; exact Nat.one_pos)).2).output.returnsResult property := by
  obtain ⟨values, columns, source, joins, filter, groupBy, orderBy, limit, offset, subqueries, having, distinct, compound,
    same⟩ := Script.select_shape select
  obtain rfl : script = ⟨[(.select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound,
      values)]⟩ := by cases script; simp_all
  rw [check_query]
  simp only [List.getElem_cons_zero]
  cases step : runScriptStep runContext state.clock state.index state.connection
      (.select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound) values with
  | ended reason => simp [RunStep.output, Output.returnsResult]
  | continued actual next others =>
    obtain ⟨rfl, rfl⟩ := runScriptStep_select_keeps step
    simp only [RunStep.output, RunStep.executions, List.mem_singleton, forall_eq]
    exact OutputChoice.forall_queryResult_iff (runScriptStep_select_output step) property

/-- For every script of one SELECT and every context and property {lit}`Q` of a result: the program
{name}`send` of the script checks the post "the one output returns a result with {lit}`Q`" at the
context exactly when the output of the step of the statement returns a result with {lit}`Q`. Each
output that may be selected returns such a result when the output of the step does, because a
choice of results returns one only when each of them has {lit}`Q`. Proof sketch:
{name}`Sql.check_stopped` and {name}`Sql.check_continued` for the step; a SELECT has one execution
({name}`runScriptStep_select_keeps`); the raw output and its concrete choices. -/
theorem check_send_returnsResult_iff {script : Script} (select : script.isSelect = true)
    (property : List (List Value) → Prop) (state : ExecutionContext) :
    (send script).check (fun outputs _ => match outputs with
      | [output] => output.returnsResult property | [] | _ :: _ :: _ => False) state ↔
      (runScriptStep runContext state.clock state.index state.connection
        (script.statements[0]'(by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, same⟩ := Script.select_shape select; simp [same])).1
        (script.statements[0]'(by obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, same⟩ := Script.select_shape select; simp [same])).2).output.returnsResult property := by
  obtain ⟨values, columns, source, joins, filter, groupBy, orderBy, limit, offset, subqueries, having, distinct, compound,
    same⟩ := Script.select_shape select
  obtain rfl : script = ⟨[(.select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound,
      values)]⟩ := by cases script; simp_all
  simp only [List.getElem_cons_zero]
  unfold send
  simp only [sendStatements]
  cases step : runScriptStep runContext state.clock state.index state.connection
      (.select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound) values with
  | ended reason => simp [Sql.check_stopped step, RunStep.output, Output.returnsResult]
  | continued actual next others =>
    obtain ⟨rfl, rfl⟩ := runScriptStep_select_keeps step
    rw [Sql.check_continued step]
    simp only [RunStep.output, RunStep.executions, List.mem_singleton, forall_eq, Sql.check_map, Sql.check_pure]
    constructor
    · exact fun each => each _ (OutputChoice.actual _)
    · rintro holds selected (rfl | choice)
      · exact holds
      · cases actual with
        | oneOf results =>
          obtain ⟨rows, member, rfl⟩ := choice
          exact holds.2 rows member
        | rows _ | done _ | error _ | unmodeled _ => exact choice.elim

/-- For every script of one SELECT, database, environment and property {lit}`Q` of a result (the
successful-result bridge of ADR 0027, D2): the run of the program {name}`query` of the script returns
a result with {lit}`Q` exactly when the program checks the post "a successful result with {lit}`Q`"
from the new connection of the environment ({name}`ExecutionContext.initial`). An error, which
{name}`query` gives as {lit}`.error code`, satisfies neither side. Proof sketch:
{name}`Run.query_returnsResult_iff` and {name}`check_query_returnsResult_iff` read the same step. -/
theorem Run.returnsResult_query_iff {script : Script} {one : script.statements.length = 1}
    (select : script.isSelect = true) (db : Database) (env : Env) (property : List (List Value) → Prop) :
    (db.run (query script one) env).returnsResult property ↔
      (query script one).check (fun result _ => match result with
        | .ok rows => property rows | .error _ => False) (ExecutionContext.initial db env) := by
  rw [Run.query_returnsResult_iff one, check_query_returnsResult_iff select]
  rfl

end Belay.Sqlite
