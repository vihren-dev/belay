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

/-- For a continuing step, checking its program is exactly checking every permitted
observation's continuation at its reached context. The chosen output is appended to the
existing trace. Proof sketch: invert the branch relation and move the first output into
{name}`ExecutionContext.next`. -/
theorem Sql.check_continued {α : Type} {statement values} {rest : Output → Sql α}
    {state : ExecutionContext} {actual connection} (step : runScriptStep runContext state.clock
      state.index state.connection statement values = .continued actual connection)
    (post : α → ExecutionContext → Prop) :
    (Sql.exec statement values rest).check post state ↔
      ∀ selected, OutputChoice actual selected → (rest selected).check post (state.next selected connection) := by
  constructor
  · intro checked selected choice result later
    have holds := checked _ (Sql.Branch.continued step choice later)
    simpa only [ExecutionContext.finish_prepend state selected connection result] using holds
  · intro checked result branch
    obtain ⟨selected, later, choice, nextBranch, rfl⟩ := (Sql.branch_continued_iff step result).mp branch
    simpa only [ExecutionContext.finish_prepend state selected connection later] using checked selected choice later nextBranch

/-- The exact finite proof obligations for an execution step: an unmodeled step fails;
a continued step checks its raw continuation and all listed concrete alternatives, each
with the actual next connection. Modeled SQL errors impose no separate restriction.
Proof sketch: combine the branch step characterization with the permitted-output cases. -/
theorem Sql.check_exec {α : Type} (statement values) (rest : Output → Sql α)
    (post : α → ExecutionContext → Prop) (state : ExecutionContext) :
    (Sql.exec statement values rest).check post state ↔
      match runScriptStep runContext state.clock state.index state.connection statement values with
      | .ended _ => False
      | .continued actual connection =>
        (rest actual).check post (state.next actual connection) ∧ match actual with
        | .oneOf alternatives => ∀ rows ∈ alternatives,
          (rest (.rows rows)).check post (state.next (.rows rows) connection)
        | .done _ | .rows _ | .error _ | .unmodeled _ => True := by
  split
  · rename_i reason step
    exact iff_false_intro (Sql.check_stopped step post)
  · rename_i actual connection step
    exact (Sql.check_continued step post).trans (OutputChoice.forall_iff actual _)

/-- A finite SQL program and decidable postcondition admit kernel-checked decisions of
{name}`Sql.check`. The finite step characterization supplies the algorithm; every actual
and concrete continuation remains checked. Use it for concrete proof fixtures. -/
instance Sql.decidableCheck {α : Type} (program : Sql α) (post : α → ExecutionContext → Prop)
    [∀ value state, Decidable (post value state)] (state : ExecutionContext) :
    Decidable (program.check post state) :=
  match program with
  | .pure value => decidable_of_iff (post value state) (Sql.check_pure value post state).symm
  | .exec statement values rest =>
    match step : runScriptStep runContext state.clock state.index state.connection statement values with
    | .ended reason => isFalse (Sql.check_stopped step post)
    | .continued actual connection => by
      letI (output : Output) := Sql.decidableCheck (rest output) post (state.next output connection)
      have finite := (Sql.check_continued (rest := rest) step post).trans (OutputChoice.forall_iff actual _)
      apply @decidable_of_iff _ _ finite.symm ?_
      cases actual <;> dsimp <;> infer_instance
termination_by structural program

end Belay.Sqlite
