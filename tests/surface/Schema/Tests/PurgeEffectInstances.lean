import PurgeFrameInstances
import PurgeEffectClaims

/-! A fixture module of `tests/surface_assertion_examples_test.py`: instances of the effect claim of the purge. The
client statement `purge_clears` applies to the database `sessions`. The kernel reads the claim before and after the
actual run of the purge, so that the claim is not vacuous: it is false at the start, where an expired session of the
customer exists, and true after the purge. An aborted purge shows why the claim requires a run with no error. -/

set_option doc.verso true
set_option maxRecDepth 200000
set_option exponentiation.threshold 2000

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- The client statement of the effect claim applies to {name}`sessions`: for the customer 1 and the integer time 50,
every run of the purge with no error leaves no expired session of the customer. -/
theorem integer_time_clears : ∀ env : Env, env.Complete →
    (send (purge (.integer 1) (.integer 50))).ifOk
      (fun _ final => Holds.reached (purgeClears (.integer 1) (.integer 50)) final)
      (ExecutionContext.initial sessions env) :=
  purge_clears (.integer 1) (.integer 50) sessions rfl

/-- Before the purge the effect claim is false: the session 1 of customer 1 expired at 10. After the actual run of
the purge it is true. -/
theorem integer_time_makes_the_claim_true : ¬ Holds (purgeClears (.integer 1) (.integer 50)) sessions ∧
    (purgeFinal sessions (.integer 1) (.integer 50)).outputs.allOk = true ∧
    Holds.reached (purgeClears (.integer 1) (.integer 50)) (purgeFinal sessions (.integer 1) (.integer 50)) := by
  decide +kernel

/-- With a text time the filter is true for every session of the customer: the claim is false before the purge and
true after it. -/
theorem text_time_makes_the_claim_true : ¬ Holds (purgeClears (.integer 1) textTime) sessions ∧
    (purgeFinal sessions (.integer 1) textTime).outputs.allOk = true ∧
    Holds.reached (purgeClears (.integer 1) textTime) (purgeFinal sessions (.integer 1) textTime) := by
  decide +kernel

/-- With a NULL customer the filter is true for no row: the claim is true before and after the purge, which deletes
nothing. -/
theorem null_customer_needs_no_delete : Holds (purgeClears .null (.integer 50)) sessions ∧
    Holds.reached (purgeClears .null (.integer 50)) (purgeFinal sessions .null (.integer 50)) := by
  decide +kernel

/-- When a trigger aborts the purge, the rollback keeps the expired session 1 of customer 1, and the effect claim is
false at the end. The client statement requires nothing of this run, because the run has an error. -/
theorem an_aborted_purge_leaves_the_expired_session :
    (purgeFinal refusing (.integer 1) (.integer 50)).outputs.allOk = false ∧
    ¬ Holds.reached (purgeClears (.integer 1) (.integer 50)) (purgeFinal refusing (.integer 1) (.integer 50)) := by
  decide +kernel

#print axioms integer_time_clears
#print axioms integer_time_makes_the_claim_true
#print axioms text_time_makes_the_claim_true
#print axioms null_customer_needs_no_delete
#print axioms an_aborted_purge_leaves_the_expired_session

end AssertionExamples
