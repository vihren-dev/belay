import Belay.Sqlite.Model.ForeignKeyCounter
import Belay.Sqlite.Model.ForeignKeyWrites
import Belay.Sqlite.Model.RowLocalFrame

set_option doc.verso true

/-! The row-engine boundary for the global FK counter invariant. Successful and FAIL writes
publish their rows only at counter zero; the SQL run restores input or snapshot rows for other
failures. Nested bookkeeping leaves both the rows and the FK counter unchanged. -/

namespace Belay.Sqlite.Model

/-- For every input with valid selected row references and row-engine result whose success
or FAIL state has the counter bound, {name}`keyRun` satisfies the row-reference fact on every
database that SQL can retain from its effect. Other error carriers impose no requirement.
Proof sketch: published success and FAIL states have counter zero; a raw error can carry
FAIL as its reason, but its database is the input. Rollback restores a separately checked
snapshot in the SQL run rather than retaining the raw rollback carrier. -/
theorem keyRun_rowReferences {input : Database}
    (inputHolds : input.RowReferencesHold input.catalog.foreignKeyMapping) (target : Nat) (plain : Bool)
    {result : Except KeyStop KeyState}
    (bound : ResultHolds (KeyState.CounterBound input.catalog) (KeyStop.CounterBound input.catalog) result) :
    (keyRun input target plain result).effect.Satisfies
      (fun database => database.RowReferencesHold database.catalog.foreignKeyMapping) := by
  intro database kept
  cases result with
  | error stop =>
    cases stop with
    | undescribed => simp [keyRun] at kept
    | error reason state =>
      simp only [keyRun, reduceCtorEq, Except.error.injEq, Prod.mk.injEq, false_or] at kept
      exact kept.2 ▸ inputHolds
    | stopped algorithm state =>
      cases algorithm with
      | rollback => simp [keyRun] at kept
      | fail =>
        simp only [keyRun] at kept
        split at kept
        · simp at kept
        · rename_i zero
          simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at zero
          simp only [Except.error.injEq, Prod.mk.injEq, true_and, reduceCtorEq, false_or] at kept
          subst database
          exact bound.zero zero
  | ok state =>
    simp only [keyRun] at kept
    split at kept
    · simp at kept
    · rename_i zero
      simp only [Bool.not_eq_true, bne_eq_false_iff_eq] at zero
      simp only [Except.ok.injEq, reduceCtorEq, or_false] at kept
      subst database
      exact bound.zero zero

/-- For every state change that retains rows and FK counter, mapping it over a row-engine
result retains the counter bound on success and FAIL states. Other stops impose nothing.
Proof sketch: inspect the result and apply {name}`KeyState.CounterBound.of_rows_counter`. -/
theorem KeyResult.mapState_counterBound {catalog : Catalog} {change : KeyState → KeyState}
    (rows : ∀ state, (change state).rows = state.rows)
    (counter : ∀ state, (change state).counter = state.counter) {result : Except KeyStop KeyState}
    (bound : ResultHolds (KeyState.CounterBound catalog) (KeyStop.CounterBound catalog) result) :
    ResultHolds (KeyState.CounterBound catalog) (KeyStop.CounterBound catalog) (KeyResult.mapState change result) := by
  cases result with
  | ok state => exact bound.of_rows_counter (rows state) (counter state)
  | error stop =>
    cases stop with
    | error reason state => trivial
    | undescribed => trivial
    | stopped algorithm state =>
      cases algorithm with
      | fail => exact bound.of_rows_counter (rows state) (counter state)
      | rollback => trivial

/-- For a fixed catalog, input condition and nested runner, every permitted frame/work/input
with the counter bound gives a success or FAIL state with that bound. Disallowed work requires
nothing. Conditions read the input database, not bookkeeping fields. Use this as the nested
induction contract; raw work can claim an incorrect changed-column list, so it needs explicit
input conditions before FK phase laws can establish the bound. -/
def NestedRun.CounterKeeps (catalog : Catalog) (allowed : RowFrame → RowWork → Database → Prop)
    (nested : NestedRun) : Prop :=
  ∀ frame work state, allowed frame work (state.database catalog) → state.CounterBound catalog →
    ResultHolds (KeyState.CounterBound catalog) (KeyStop.CounterBound catalog) (nested frame work state)

/-- For every input condition and nested runner that keeps the counter bound under it, the
credited wrapper keeps the bound under the same condition. Proof sketch: resetting and
restoring statement counts changes neither the input database nor the immediate FK counter,
on success or on a stop. -/
theorem NestedRun.credited_counterKeeps {catalog : Catalog} {nested : NestedRun}
    {allowed : RowFrame → RowWork → Database → Prop}
    (keeps : nested.CounterKeeps catalog allowed) : (NestedRun.credited nested).CounterKeeps catalog allowed := by
  intro frame work state met bound
  have ran := keeps frame work { state with own := 0 } met (bound.of_rows_counter rfl rfl)
  unfold NestedRun.credited
  dsimp only
  cases result : nested frame work { state with own := 0 } with
  | error stop =>
    rw [result] at ran
    exact KeyResult.mapState_counterBound (change := fun reached : KeyState =>
      { reached with own := state.own, inserted := state.inserted }) (fun _ => rfl) (fun _ => rfl) ran
  | ok reached =>
    rw [result] at ran
    exact ran.of_rows_counter rfl rfl

end Belay.Sqlite.Model
