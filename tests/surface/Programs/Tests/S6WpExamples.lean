import S6WpSoundness

set_option doc.verso true
set_option maxRecDepth 4096

/-! Check SQL triples, result-dependent branches and the full execution context. -/

namespace S6.Examples
open Belay.Sqlite Std.Do

/-- A database with two permitted LIMIT results and a table for writes. -/
def sample : Database := db! r"CREATE TABLE t (x INTEGER); INSERT INTO t VALUES (1), (2)"

/-- A complete environment whose clock advances one day per statement. -/
def daily : Env :=
  { clock := some (fun index => 212602449600000 + 86400000 * index)
    counters := Counters.newConnection }

/-- The example supplies every execution input that success quantifies over. -/
theorem daily_complete : daily.Complete := ⟨rfl, rfl, rfl, rfl⟩

/-- One SQL write followed by a pure result; the returned value counts its outputs. -/
def writeOne : Sql Nat := do
  let outputs ← send (sql r"INSERT INTO t VALUES (3)")
  pure outputs.length

/-- From the exact fixture context, the write succeeds and returns one output. The checked
specification lets both proof routes reason about the same actual SQL operation. -/
@[spec] theorem writeOne_spec :
    ⦃fun state : Context => ⌜state = initial sample daily⌝⦄ writeOne ⦃⇓ value _ => ⌜value = 1⌝⦄ := by
  intro state same
  cases same
  change check true writeOne (fun value _ => value = 1) (initial sample daily)
  decide +kernel

/-- A SQL operation bound to a pure computation, for comparing the two proof routes. -/
def addThree : Sql Nat := do
  let value ← writeOne
  pure (value + 3)

/-- From the fixture context, the experimental tactic uses the SQL specification and bind
laws to prove that the program returns 4. -/
theorem tactic_triple :
    ⦃fun state : Context => ⌜state = initial sample daily⌝⦄ addThree ⦃⇓ value _ => ⌜value = 4⌝⦄ := by
  unfold addThree
  mvcgen <;> simp_all

/-- The same SQL triple follows from the checked specification and explicit pure/bind
lemmas, without the experimental tactic. -/
theorem lemma_triple :
    ⦃fun state : Context => ⌜state = initial sample daily⌝⦄ addThree ⦃⇓ value _ => ⌜value = 4⌝⦄ := by
  apply Triple.bind (m := Sql) (ps := .arg Context .pure) writeOne (fun value => pure (value + 3))
    (Q := fun (value : Nat) (_ : Context) => ⌜value = 1⌝)
  · exact writeOne_spec
  · intro value
    apply Triple.pure
    intro state same
    cases same
    rfl

/-- A result controls the returned value; every permitted row result remains covered. -/
def dependent : Sql Bool := do
  let value ← single (sql r"SELECT x FROM t LIMIT 1")
  pure (value == some 1)

/-- Both result values satisfy the postcondition, with the one statement's full context. -/
theorem dependent_check : check true dependent
    (fun _ state => state.index = 1 ∧ state.connection.state.database = sample.raw)
    (initial sample daily) := by decide +kernel

/-- The other permitted row selects a failing query, although the canonical choice succeeds. -/
def alternativeFails : Sql (List Output) := do
  match ← single (sql r"SELECT x FROM t LIMIT 1") with
  | some (.integer 1) => pure []
  | _ => send (sql r"SELECT x FROM missing")

/-- Actual success alone cannot discharge the all-branch transformer. -/
theorem alternative_refutes : (sample.run alternativeFails daily).outputs.allOk = true ∧
    ¬ check true alternativeFails (fun _ _ => True) (initial sample daily) := by decide +kernel

/-- A continuation can fail only for the actual raw output wrapper. -/
def rawFails : Sql (List Output) :=
  let (statement, values) := (sql r"SELECT x FROM t LIMIT 1").statements[0]
  .exec statement values fun output => match output with
    | .oneOf _ => send (sql r"SELECT x FROM missing")
    | .done _ | .rows _ | .error _ | .unmodeled _ => .pure []

/-- Checking only concrete row continuations would miss this actual failure. -/
theorem raw_refutes : ¬ check true rawFails (fun _ _ => True) (initial sample daily) := by decide +kernel

/-- Two reads must use consecutive clock indices. -/
def twoTimes : Sql (Option Value × Option Value) := do
  let first ← single (sql r"SELECT CURRENT_TIMESTAMP")
  let second ← single (sql r"SELECT CURRENT_TIMESTAMP")
  pure (first, second)

/-- The changing clock and next index are preserved by transformer bind. -/
theorem clock_check : check true twoTimes (fun value state =>
    value = (some (("2025-01-01 00:00:00" : String) : Value),
      some (("2025-01-02 00:00:00" : String) : Value)) ∧ state.index = 2)
    (initial sample daily) := by decide +kernel

/-- A write sets the counter that the following read observes. -/
def writeRead : Sql (Option Value) := do
  let _ ← send (sql r"INSERT INTO t VALUES (3)")
  single (sql r"SELECT changes()")

/-- The counter remains 1 in the continuation's result and full connection. -/
theorem counter_check : check true writeRead (fun value state =>
    value = some 1 ∧ state.connection.state.counters.changes = some 1)
    (initial sample daily) := by decide +kernel

/-- A transaction remains open across program bind, so rollback restores its snapshot. -/
def rolledBack : Sql (Option Value) := do
  let _ ← send (sql r"BEGIN; INSERT INTO t VALUES (3)")
  let _ ← send (sql r"ROLLBACK")
  single (sql r"SELECT count(*) FROM t")

/-- The continuation sees the restored rows, no open transaction, and unchanged clock. -/
theorem transaction_check : check true rolledBack (fun value state =>
    value = some 2 ∧ state.connection.state.database = sample.raw ∧
    state.connection.state.snapshot = none)
    (initial sample daily) := by decide +kernel

/-- A modeled SQL error may satisfy a conditional claim, but not total success. -/
theorem error_policy :
    ifOk (send (sql r"SELECT x FROM missing")) (fun _ _ => False) (initial sample daily) ∧
    ¬ check true (send (sql r"SELECT x FROM missing")) (fun _ _ => True) (initial sample daily) := by
  unfold ifOk
  decide +kernel

/-- A model restriction cannot prove a conditional claim, even with a true postcondition. -/
theorem unmodeled_policy :
    ¬ ifOk (send (sql r"SELECT random()")) (fun _ _ => True) (initial sample daily) := by
  unfold ifOk
  decide +kernel

/-- An error followed by a model restriction is still rejected: conditional claims must
check every continuation after the error. -/
theorem later_unmodeled : ¬ ifOk (send (sql r"SELECT x FROM missing; SELECT random()"))
    (fun _ _ => True) (initial sample daily) := by
  unfold ifOk
  decide +kernel

#print axioms writeOne_spec
#print axioms tactic_triple
#print axioms lemma_triple
#print axioms dependent_check
#print axioms alternative_refutes
#print axioms raw_refutes
#print axioms clock_check
#print axioms counter_check
#print axioms transaction_check
#print axioms error_policy
#print axioms unmodeled_policy
#print axioms later_unmodeled
end S6.Examples
