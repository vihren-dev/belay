import Belay.Sqlite.ExecutionWP

set_option doc.verso true

namespace Belay.Sqlite
open Model

/-- Requiring a predicate for every permitted observation is exactly requiring it for the
actual raw output and every concrete rows alternative. Empty alternatives add no condition.
Proof sketch: unfold the two cases of {name}`OutputChoice`. -/
theorem OutputChoice.forall_iff (actual : Output) (predicate : Output → Prop) :
    (∀ selected, OutputChoice actual selected → predicate selected) ↔
      predicate actual ∧ match actual with
      | .oneOf alternatives => ∀ rows ∈ alternatives, predicate (.rows rows)
      | .done _ | .rows _ | .error _ | .unmodeled _ => True := by
  constructor
  · intro all
    refine ⟨all actual (.actual actual), ?_⟩
    cases actual with
    | oneOf alternatives => exact fun rows member => all (.rows rows) (.rows member)
    | done _ | rows _ | error _ | unmodeled _ => trivial
  · rintro ⟨raw, alternatives⟩ selected choice
    rcases choice with same | concrete
    · cases same; exact raw
    · cases actual with
      | oneOf rows =>
        obtain ⟨result, member, rfl⟩ := concrete
        exact alternatives result member
      | done _ | rows _ | error _ | unmodeled _ => exact concrete.elim

/-- A stopped step cannot satisfy any postcondition. The existing trace and reason do not
make the obligation vacuous. Proof sketch: its actual stopped branch has no value. -/
theorem Sql.check_stopped {α : Type} {statement values} {rest : Output → Sql α}
    {state : ExecutionContext} {reason : String} (step : runScriptStep runContext state.clock
      state.index state.connection statement values = .ended reason)
    (post : α → ExecutionContext → Prop) : ¬ (Sql.exec statement values rest).check post state := by
  intro checked
  exact checked _ (.stopped step)

/-- For a continuing step, checking its program is exactly checking, for every execution of the
statement ({name}`RunStep.executions`) and every permitted observation of that execution's output,
the continuation at the context reached by that execution: its next connection, with the chosen
output appended to the existing trace. A statement with no execution adds no condition here.
Proof sketch: invert the branch relation and move the first output into
{name}`ExecutionContext.next`. -/
theorem Sql.check_continued {α : Type} {statement values} {rest : Output → Sql α}
    {state : ExecutionContext} {actual connection others} (step : runScriptStep runContext state.clock
      state.index state.connection statement values = .continued actual connection others)
    (post : α → ExecutionContext → Prop) :
    (Sql.exec statement values rest).check post state ↔
      ∀ found ∈ (RunStep.continued actual connection others).executions, ∀ selected,
        OutputChoice found.output selected → (rest selected).check post (state.next selected found.next) := by
  constructor
  · intro checked found member selected choice result later
    have holds := checked _ (Sql.Branch.continued step member choice later)
    simpa only [ExecutionContext.finish_prepend state selected found.next result] using holds
  · intro checked result branch
    obtain ⟨found, member, selected, later, choice, nextBranch, rfl⟩ :=
      (Sql.branch_continued_executions_iff step result).mp branch
    simpa only [ExecutionContext.finish_prepend state selected found.next later] using
      checked found member selected choice later nextBranch

/-- The condition on one execution of a continuing step: the predicate holds for the raw output,
and for every concrete rows result that a raw {name}`Output.oneOf` lists (an empty list adds no such
condition). -/
def OutputChoice.Checked (predicate : Output → Prop) (actual : Output) : Prop :=
  predicate actual ∧ match actual with
  | .oneOf alternatives => ∀ rows ∈ alternatives, predicate (.rows rows)
  | .done _ | .rows _ | .error _ | .unmodeled _ => True

/-- The condition {name}`OutputChoice.Checked` is decidable when the predicate is. Use it through
{lit}`Sql.decidableCheck`. -/
instance OutputChoice.decidableChecked (predicate : Output → Prop) [DecidablePred predicate] (actual : Output) :
    Decidable (OutputChoice.Checked predicate actual) := by
  unfold OutputChoice.Checked
  cases actual <;> dsimp <;> infer_instance

/-- The exact finite proof obligations for an execution step: an unmodeled step fails;
a continued step checks, for each of its executions, the raw continuation and all listed concrete
alternatives, each with the next connection of that execution. Modeled SQL errors impose no
separate restriction. Proof sketch: combine the branch step characterization with the
permitted-output cases ({name}`OutputChoice.forall_iff`). -/
theorem Sql.check_exec {α : Type} (statement values) (rest : Output → Sql α)
    (post : α → ExecutionContext → Prop) (state : ExecutionContext) :
    (Sql.exec statement values rest).check post state ↔
      match runScriptStep runContext state.clock state.index state.connection statement values with
      | .ended _ => False
      | .continued actual connection others =>
        ∀ found ∈ (RunStep.continued actual connection others).executions,
          (rest found.output).check post (state.next found.output found.next) ∧ match found.output with
          | .oneOf alternatives => ∀ rows ∈ alternatives,
            (rest (.rows rows)).check post (state.next (.rows rows) found.next)
          | .done _ | .rows _ | .error _ | .unmodeled _ => True := by
  split
  · rename_i reason step
    exact iff_false_intro (Sql.check_stopped step post)
  · rename_i actual connection others step
    exact (Sql.check_continued step post).trans
      (forall_congr' fun found => forall_congr' fun _ => OutputChoice.forall_iff found.output _)

/-- A finite SQL program and decidable postcondition admit kernel-checked decisions of
{name}`Sql.check`. The finite step characterization supplies the algorithm; every execution and
every actual and concrete continuation remains checked. Use it for concrete proof fixtures. -/
instance Sql.decidableCheck {α : Type} (program : Sql α) (post : α → ExecutionContext → Prop)
    [∀ value state, Decidable (post value state)] (state : ExecutionContext) :
    Decidable (program.check post state) :=
  match program with
  | .pure value => decidable_of_iff (post value state) (Sql.check_pure value post state).symm
  | .exec statement values rest =>
    match step : runScriptStep runContext state.clock state.index state.connection statement values with
    | .ended reason => isFalse (Sql.check_stopped step post)
    | .continued actual connection others => by
      letI (found : StatementExecution) (output : Output) :=
        Sql.decidableCheck (rest output) post (state.next output found.next)
      have finite := (Sql.check_continued (rest := rest) step post).trans
        (forall_congr' fun found => forall_congr' fun _ => OutputChoice.forall_iff found.output _)
      apply @decidable_of_iff _ _ finite.symm ?_
      exact List.decidableBAll
        (fun found : StatementExecution =>
          OutputChoice.Checked (fun output => (rest output).check post (state.next output found.next)) found.output) _
termination_by structural program

end Belay.Sqlite
