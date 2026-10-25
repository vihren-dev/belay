import AssertionContexts
import Belay.Sqlite.AssertionTerms
import Belay.Sqlite.ExecutionWPLaws

set_option doc.verso true
set_option maxRecDepth 4096

namespace AssertionExamples
open Belay.Sqlite Belay.Sqlite.Model Std.Do

/-- A write whose single output the fixtures inspect. -/
def insertThree : Sql (List Output) := send (sql r"INSERT INTO t VALUES (3, 3)")

/-- An actual rows result selects an unmodeled continuation for the second concrete row. -/
def alternateStops : Sql (List Output) := do
  match ← single (sql r"SELECT x FROM t LIMIT 1") with
  | some (.integer 1) => pure []
  | _ => send (sql r"SELECT random()")

/-- A modeled error already in the trace removes the conditional obligation, whatever the property. -/
theorem if_ok_prefix_error_is_vacuous :
    ⦃fun context : ExecutionContext => ⌜context = afterError⌝⦄
      (Sql.pure ()) ⦃ifOk (⌜False⌝ : ContextAssertion)⦄ := by
  refine (triple_ifOkWith_iff _ _ _).mpr fun context same => ?_
  cases same
  show (Sql.pure ()).ifOk (fun _ _ => False) afterError
  decide +kernel

/-- The same prefix error makes the total policy false for a program that returns normally. -/
theorem and_ok_prefix_error_fails :
    ¬ ⦃fun context : ExecutionContext => ⌜context = afterError⌝⦄
      (Sql.pure ()) ⦃andOk (⌜True⌝ : ContextAssertion)⦄ := by
  intro triple
  have : (Sql.pure ()).andOk (fun _ _ => True) afterError := (triple_andOkWith_iff _ _ _).mp triple afterError rfl
  revert this
  decide +kernel

/-- An unmodeled stop already in the trace is a non-OK output for both policies. -/
theorem prefix_stop_is_not_ok :
    ⦃fun context : ExecutionContext => ⌜context = afterStop⌝⦄
      (Sql.pure ()) ⦃ifOk (⌜False⌝ : ContextAssertion)⦄ ∧
    ¬ ⦃fun context : ExecutionContext => ⌜context = afterStop⌝⦄
      (Sql.pure ()) ⦃andOk (⌜True⌝ : ContextAssertion)⦄ := by
  constructor
  · refine (triple_ifOkWith_iff _ _ _).mpr fun context same => ?_
    cases same
    show (Sql.pure ()).ifOk (fun _ _ => False) afterStop
    decide +kernel
  · intro triple
    have : (Sql.pure ()).andOk (fun _ _ => True) afterStop := (triple_andOkWith_iff _ _ _).mp triple afterStop rfl
    revert this
    decide +kernel

/-- An error then a write: the conditional policy excuses the property and the write still runs. -/
theorem error_then_write :
    ⦃fun context : ExecutionContext => ⌜context = initial⌝⦄
      (send (sql r"SELECT absent FROM missing; INSERT INTO t VALUES (3, 3)"))
      ⦃ifOk (⌜False⌝ : ContextAssertion)⦄ := by
  refine (triple_ifOkWith_iff _ _ _).mpr fun context same => ?_
  cases same
  show (send (sql r"SELECT absent FROM missing; INSERT INTO t VALUES (3, 3)")).ifOk (fun _ _ => False) initial
  decide +kernel

/-- An error then an unmodeled step: the conditional policy never excuses the unmodeled stop. -/
theorem error_then_stop :
    ¬ ⦃fun context : ExecutionContext => ⌜context = initial⌝⦄
      (send (sql r"SELECT absent FROM missing; SELECT random()"))
      ⦃ifOk (⌜True⌝ : ContextAssertion)⦄ := by
  intro triple
  have : (send (sql r"SELECT absent FROM missing; SELECT random()")).ifOk (fun _ _ => True) initial :=
    (triple_ifOkWith_iff _ _ _).mp triple initial rfl
  revert this
  decide +kernel

/-- Each concrete choice of a rows result must stay modeled under both policies. -/
theorem every_choice_stays_modeled :
    ¬ ⦃fun context : ExecutionContext => ⌜context = initial⌝⦄ alternateStops
      ⦃ifOkWith fun _ => (⌜True⌝ : ContextAssertion)⦄ := by
  intro triple
  have : alternateStops.ifOk (fun _ _ => True) initial := (triple_ifOkWith_iff _ _ _).mp triple initial rfl
  revert this
  decide +kernel

/-- The value-aware policy inspects the returned outputs, and a default query assertion reads
the reached database in the same postcondition. -/
theorem value_and_row_after_write :
    ⦃fun context : ExecutionContext => ⌜context = initial⌝⦄ insertThree
      ⦃andOkWith fun outputs context =>
        ⌜outputs.length = 1 ∧ ((holds (sql r"SELECT 1 FROM t WHERE id = 3")) context).down⌝⦄ := by
  refine (triple_andOkWith_iff _ _ _).mpr fun context same => ?_
  cases same
  show insertThree.andOk (fun outputs final => outputs.length = 1 ∧
    Holds.reached (sql r"SELECT 1 FROM t WHERE id = 3") final) initial
  decide +kernel

/-- The real-context assertion sees the counters after the write; the default one does not. -/
theorem context_assertion_after_write :
    ⦃fun context : ExecutionContext => ⌜context = initial⌝⦄ insertThree
      ⦃andOk (holdsInContext (sql r"SELECT 1 WHERE changes() = 1") : ContextAssertion)⦄ := by
  refine (triple_andOkWith_iff _ _ _).mpr fun context same => ?_
  cases same
  show insertThree.andOk (fun _ final => Holds.inContext (sql r"SELECT 1 WHERE changes() = 1") final) initial
  decide +kernel

/-- The default assertion at a context with a later index does not hold an index claim. -/
theorem default_assertion_not_fresh_entry :
    ¬ ⦃fun context : ExecutionContext => (holds (sql r"SELECT 1 FROM t WHERE id = 2")) context⦄
      (Sql.pure ()) ⦃⇓ _ context => ⌜context.index = 0⌝⦄ := by
  intro triple
  have checked : (Sql.pure ()).check (fun _ context => context.index = 0) { initial with index := 5 } :=
    triple _ (by
      show Holds.reached (sql r"SELECT 1 FROM t WHERE id = 2") { initial with index := 5 }
      decide +kernel)
  exact absurd ((Sql.check_pure _ _ _).mp checked) (by decide)

#print axioms if_ok_prefix_error_is_vacuous
#print axioms and_ok_prefix_error_fails
#print axioms prefix_stop_is_not_ok
#print axioms error_then_write
#print axioms error_then_stop
#print axioms every_choice_stays_modeled
#print axioms value_and_row_after_write
#print axioms context_assertion_after_write
#print axioms default_assertion_not_fresh_entry
end AssertionExamples
