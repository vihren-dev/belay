import Belay.Sqlite.Model.StatementExecution

set_option doc.verso true

/-! Laws of the executions of a statement (ADR 0019, D4, amended 2026-10-25). They are a module apart
from {lit}`StatementExecution.lean`, so that the definitions need no proof. -/

namespace Belay.Sqlite.Model

/-- For every index, values, connection, resolved statement, resolution state, clock value and run
without alternatives, the further executions ({name}`StatementExecution.ofAlternatives`) are none.
Proof sketch: the map over no alternatives is the empty list. -/
theorem StatementExecution.ofAlternatives_of_single (index : Nat) (parameters : List Value) (connection : Connection)
    (resolved : Resolved.Statement) (after : ResolveState) (value : Int) {run : StatementRun}
    (single : run.alternatives = []) :
    StatementExecution.ofAlternatives index parameters connection resolved after value run = .ok [] := by
  simp only [StatementExecution.ofAlternatives, single, List.mapM_nil]
  rfl

/-- For every function that can fail, list of arguments and list of results: if the monadic map of
the function over the arguments succeeds with the results, each result is the success of the function
for some argument. Proof sketch: induction on the arguments; the first result is the success for the
first argument, and the rest comes from the map over the other arguments. -/
theorem List.mapM_except_mem {α β : Type} (f : α → Except String β) :
    ∀ (arguments : List α) (results : List β), arguments.mapM f = .ok results →
      ∀ result ∈ results, ∃ argument ∈ arguments, f argument = .ok result
  | [], results, listed => by
    simp only [List.mapM_nil] at listed
    cases listed
    simp
  | argument :: rest, results, listed => by
    simp only [List.mapM_cons] at listed
    cases first : f argument with
    | error reason => simp [first, bind, Except.bind] at listed
    | ok head =>
      cases others : rest.mapM f with
      | error reason => simp [first, others, bind, Except.bind] at listed
      | ok tail =>
        simp only [first, others, bind, Except.bind, pure, Except.pure] at listed
        cases listed
        intro result member
        rcases List.mem_cons.1 member with rfl | member
        · exact ⟨argument, List.mem_cons_self, first⟩
        · obtain ⟨found, inRest, same⟩ := List.mapM_except_mem f rest tail others result member
          exact ⟨found, List.mem_cons_of_mem _ inRest, same⟩

/-- For every index, values, connection, resolved statement, resolution state, clock value, run and
list of further executions: if the executions of the alternatives of the run
({name}`StatementExecution.ofAlternatives`) are the list, each of them comes from an alternative of the
run: its run is the run of the alternative ({name}`StatementRun.Alternative.toRun`), its transition is the
transition of {name}`advanceRun` on the connection, and its next connection is
{name}`Connection.afterStep` of that transition with the counts of the alternative, and its output is the
output of that run and transition ({name}`Output.ofStep`). So a law about the effect of every run of a
statement is a law about every further execution. Proof sketch:
{name}`List.mapM_except_mem` finds the alternative; the execution of an alternative is built from its
run and its transition. -/
theorem StatementExecution.ofAlternatives_mem {index : Nat} {parameters : List Value} {connection : Connection}
    {resolved : Resolved.Statement} {after : ResolveState} {value : Int} {run : StatementRun}
    {further : List StatementExecution.Traced}
    (listed : StatementExecution.ofAlternatives index parameters connection resolved after value run = .ok further) :
    ∀ traced ∈ further, ∃ alternative ∈ run.alternatives,
      traced.run = alternative.toRun ∧ traced.transition = advanceRun index resolved connection.state alternative.toRun ∧
        traced.execution.next = connection.afterStep after alternative.counts traced.transition ∧
        traced.execution.output = Output.ofStep value parameters resolved connection.state alternative.toRun traced.transition := by
  intro traced member
  obtain ⟨alternative, inAlternatives, built⟩ := List.mapM_except_mem _ _ _ listed traced member
  refine ⟨alternative, inAlternatives, ?_⟩
  simp only [StatementExecution.ofRun] at built
  cases produced : Output.ofStep value parameters resolved connection.state alternative.toRun
      (advanceRun index resolved connection.state alternative.toRun) with
  | unmodeled reason => simp [produced, Except.map] at built
  | rows rows | done count | error reason | oneOf results =>
    all_goals
      simp only [produced, Except.map] at built
      injection built with same
      subst same
      exact ⟨rfl, rfl, rfl, produced.symm⟩

/-- For every index, values, connection, resolved statement, resolution state, clock value, run and
list of further executions: if the executions of the alternatives of the run
({name}`StatementExecution.ofAlternatives`) are the list, no further execution has an output that ends
the run ({name}`Output.endsRun`). Proof sketch: an alternative with the output {name}`Output.unmodeled`
gives no execution ({name}`StatementExecution.ofRun`), and every other output continues the run. -/
theorem StatementExecution.ofAlternatives_continues {index : Nat} {parameters : List Value} {connection : Connection}
    {resolved : Resolved.Statement} {after : ResolveState} {value : Int} {run : StatementRun}
    {further : List StatementExecution.Traced}
    (listed : StatementExecution.ofAlternatives index parameters connection resolved after value run = .ok further) :
    ∀ traced ∈ further, traced.execution.output.endsRun = false := by
  intro traced member
  obtain ⟨alternative, _, built⟩ := List.mapM_except_mem _ _ _ listed traced member
  simp only [StatementExecution.ofRun] at built
  cases produced : Output.ofStep value parameters resolved connection.state alternative.toRun
      (advanceRun index resolved connection.state alternative.toRun) with
  | unmodeled reason => simp [produced, Except.map] at built
  | rows rows | done count | error reason | oneOf results =>
    all_goals
      simp only [produced, Except.map] at built
      injection built with same
      subst same
      rfl

/-- For every execution, each execution that it stands for ({name}`StatementExecution.expand`) has
its next connection. Proof sketch: split on the output; a result keeps the connection. -/
theorem StatementExecution.expand_next (execution : StatementExecution) :
    ∀ other ∈ execution.expand, other.next = execution.next := by
  unfold StatementExecution.expand
  split <;> simp_all

/-- For every execution with the output {name}`Output.oneOf` of the results and every list of
rows: some execution that it stands for ({name}`StatementExecution.expand`) has the output
{name}`Output.rows` of the rows exactly when the rows are one of the results. Rows outside the
list occur in no execution that it stands for. Proof sketch: the executions are the results, one for each. -/
theorem StatementExecution.mem_expand_rows {execution : StatementExecution} {results : List (List (List Value))}
    (output : execution.output = .oneOf results) (rows : List (List Value)) :
    (∃ other ∈ execution.expand, other.output = .rows rows) ↔ rows ∈ results := by
  unfold StatementExecution.expand
  simp only [output, List.mem_map]
  constructor
  · rintro ⟨_, ⟨found, member, rfl⟩, same⟩
    cases same
    exact member
  · intro member
    exact ⟨_, ⟨rows, member, rfl⟩, rfl⟩

end Belay.Sqlite.Model
