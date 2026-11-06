import Belay.Sqlite.Model.SelectStepKeeps
import Belay.Sqlite.Model.OutputResultsLaws
import Belay.Sqlite.Model.PrepareErrorOutput

set_option doc.verso true

/-! The shape of the output of a SELECT step (ADR 0027, D2): a SELECT step that continues gives
rows, an error, or a choice of at least two results. It never gives
{name}`Belay.Sqlite.Model.Output.done` or an empty choice, so a successful-result observation of a SELECT is never true without a result. -/

namespace Belay.Sqlite.Model

/-- For every list of results, {name}`Output.ofResults` of it is rows, a choice of at least two
results, or {name}`Output.unmodeled`. Proof sketch: {name}`Output.ofResults_listed`, by the
shape of the listed results. -/
theorem Output.ofResults_shape (rs : List (List (List Value))) :
    (∃ rows, Output.ofResults rs = .rows rows) ∨ (∃ reason, Output.ofResults rs = .unmodeled reason) ∨
      ∃ first second rest, Output.ofResults rs = .oneOf (first :: second :: rest) := by
  obtain ⟨listed, -, eq⟩ := Output.ofResults_listed rs
  rw [eq]
  match listed with
  | [] => exact .inr (.inl ⟨_, rfl⟩)
  | [result] => exact .inl ⟨_, rfl⟩
  | first :: second :: rest => exact .inr (.inr ⟨_, _, _, rfl⟩)

/-- For every clock value, values, query statement, state, run and transition, the output of the
statement ({name}`Output.ofStep`) is an error, {name}`Output.ofResults` of some results, or
{name}`Output.unmodeled`. Proof sketch: by the cases of {name}`Output.ofStep`. -/
theorem Output.ofStep_query_shape (value : Int) (parameters : List Value) (query : Resolved.Query)
    (subqueries : List Resolved.Query) (state : SqlState) (run : StatementRun) (transition : SqlTransition) :
    (∃ code, Output.ofStep value parameters (.query query subqueries) state run transition = .error code) ∨
    (∃ results, Output.ofStep value parameters (.query query subqueries) state run transition = .ofResults results) ∨
    (∃ reason, Output.ofStep value parameters (.query query subqueries) state run transition = .unmodeled reason) := by
  unfold Output.ofStep
  split
  · exact .inr (.inr ⟨_, rfl⟩)
  all_goals first | exact .inl ⟨_, rfl⟩ | skip
  dsimp only
  split
  · exact .inr (.inl ⟨_, rfl⟩)
  · exact .inr (.inr ⟨_, rfl⟩)

/-- For every state, index, values and prepare error, the transition of the prepare error halts
with it, whatever the clock value. Proof sketch: as in {name}`resolvedStepOutput_prepareError`,
unfold the run and use {name}`SqlState.haltError_failed_prepare`. -/
theorem advanceRun_prepareError_halts (state : SqlState) (index : Nat) (value : Int) (parameters : List Value)
    (error : PrepareError) :
    haltError (advanceRun index (.prepareError error) state (state.statementRun value parameters (.prepareError error))) =
      some (.prepare error) := by
  simp [advanceRun, advanceWith, SqlState.statementRun, runStatement, SqlState.publish, SqlTransition.counted, step]
  exact SqlState.haltError_failed_prepare _ _ _ _

/-- For every resolve context, clock, index, connection and SELECT statement with its values: if
the step continues with the output {lit}`output`, then {lit}`output` is one of

* {name}`Output.rows` of some rows;
* {name}`Output.error` of some code;
* {name}`Output.oneOf` of a list of at least two results.

So the output of a SELECT is never {name}`Output.done`, {name}`Output.unmodeled` or an empty or
one-element choice. Proof sketch: the step comes from a resolution to a query or a prepare error
({name}`runScriptStep_ran`, {name}`resolveStatement_select_shape`); a prepare error halts
({name}`advanceRun_prepareError_halts`); a query gives an error, unmodeled, or
{name}`Output.ofResults` ({name}`Output.ofResults_shape`), and a continued output is not
unmodeled ({name}`runScriptStep_continued`). -/
theorem runScriptStep_select_output {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection next : Connection} {columns source joins filter groupBy orderBy limit offset subqueries having
      distinct compound parameters output} {others : List StatementExecution}
    (step : runScriptStep context clock index connection
      (.select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound)
      parameters = .continued output next others) :
    (∃ rows, output = .rows rows) ∨ (∃ code, output = .error code) ∨
      ∃ first second rest, output = .oneOf (first :: second :: rest) := by
  have ends := (runScriptStep_continued step).2
  obtain ⟨resolved, after, value, found, -, -, -, rfl, -⟩ := runScriptStep_ran step
  obtain ⟨-, -, shape⟩ := resolveStatement_select_shape found
  rcases shape with ⟨query, subs, rfl⟩ | ⟨error, rfl⟩
  · rcases Output.ofStep_query_shape value parameters query subs connection.state
      (connection.state.statementRun value parameters (.query query subs))
      (advanceRun index (.query query subs) connection.state (connection.state.statementRun value parameters (.query query subs)))
      with ⟨code, same⟩ | ⟨results, same⟩ | ⟨reason, same⟩
    · exact .inr (.inl ⟨code, same⟩)
    · rw [same] at ends ⊢
      rcases Output.ofResults_shape results with ⟨rows, shape⟩ | ⟨reason, shape⟩ | ⟨first, second, rest, shape⟩
      · exact .inl ⟨rows, shape⟩
      · simp [shape, Output.endsRun] at ends
      · exact .inr (.inr ⟨first, second, rest, shape⟩)
    · simp [same, Output.endsRun] at ends
  · unfold Output.ofStep
    rw [advanceRun_prepareError_halts]
    exact .inr (.inl ⟨_, rfl⟩)

end Belay.Sqlite.Model
