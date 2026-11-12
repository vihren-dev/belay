import Belay

/-! Success follows the actual output and every nondeterministic result. These fixtures
separately catch loss of concrete alternatives and loss of the actual oneOf continuation. -/

open Belay.Sqlite

/-- Two possible LIMIT 1 results. -/
def sample : Database := db! r"CREATE TABLE t (x INTEGER); INSERT INTO t VALUES (1), (2)"

/-- A complete environment with a clock and nonzero, known counters. -/
def full : Env := { clockAt "2026-10-20 12:00:00" with
  counters := { changes := some 7, totalChanges := some 12, lastInsertRowid := some (-4) } }

/-- All four environment inputs are present. -/
theorem full_complete : full.Complete := ⟨rfl, rfl, rfl, rfl⟩

/-- The selected first result succeeds; the other possible result selects a failing query. -/
def alternativeFails : Sql (List Output) := do
  match ← single (sql r"SELECT x FROM t LIMIT 1") with
  | some (.integer 1) => pure []
  | _ => send (sql r"SELECT x FROM missing")

example : (sample.run alternativeFails full).outputs.allOk = true := by decide +kernel
example : ¬ alternativeFails.SucceedsFrom full.clock 0 (sample.raw.connection full.counters) := by decide +kernel

/-- A successful actual execution does not imply universal program success. -/
theorem alternative_not_success : ¬ Succeeds alternativeFails (fun db => db = sample) := by
  have fails : ¬ alternativeFails.SucceedsFrom full.clock 0 (sample.raw.connection full.counters) := by decide +kernel
  exact Succeeds.not_of_failure rfl full_complete fails

/-- Raw continuations can distinguish the oneOf wrapper from each concrete rows output. -/
def rawRest : Output → Sql (List Output)
  | .oneOf _ => send (sql r"SELECT x FROM missing")
  | _ => .pure []

/-- The actual interpreter gives this continuation the oneOf wrapper. -/
def actualFails : Sql (List Output) :=
  let (statement, values) := (sql r"SELECT x FROM t LIMIT 1").statements[0]
  .exec statement values rawRest

example (rows : List (List Value)) :
    (rawRest (.rows rows)).SucceedsFrom full.clock 1 (sample.raw.connection full.counters) := True.intro
example : (sample.run actualFails full).outputs.allOk = false := by decide +kernel
example : ¬ actualFails.SucceedsFrom full.clock 0 (sample.raw.connection full.counters) := by decide +kernel

/-- Checking only concrete rows would miss this actual execution failure. -/
theorem actual_not_success : ¬ Succeeds actualFails (fun db => db = sample) := by
  have fails : ¬ actualFails.SucceedsFrom full.clock 0 (sample.raw.connection full.counters) := by decide +kernel
  exact Succeeds.not_of_failure rfl full_complete fails

example : ¬ (send (sql r"SELECT CURRENT_TIMESTAMP")).SucceedsFrom none 0 sample.raw.connection := by decide +kernel
example : (send (sql r"SELECT CURRENT_TIMESTAMP")).SucceedsFrom full.clock 0 sample.raw.connection := by decide +kernel
example : ¬ (send (sql r"SELECT random()")).SucceedsFrom full.clock 0 sample.raw.connection := by decide +kernel

example (predicate : Database → Prop) : Succeeds (Sql.pure 7) predicate := Succeeds.pure 7 predicate
example (script : Script) (predicate : Database → Prop) :
    Succeeds (send script) predicate ↔ Succeeds script predicate := Succeeds.send_iff script predicate
example {p : Sql Nat} {first second : Database → Prop} (success : Succeeds p first)
    (implies : ∀ db, second db → first db) : Succeeds p second := success.mono implies

#print axioms alternative_not_success
#print axioms actual_not_success
#print axioms Succeeds.allOk
#print axioms Succeeds.script_iff
