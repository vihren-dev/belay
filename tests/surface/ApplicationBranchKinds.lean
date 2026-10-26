import Belay

/-! A fixture module of `tests/surface_application_test.py`: the kinds of branches of an application
(ADR 0017, S8). A query without an order gives a raw choice between results, and the application
chooses its next call from the result, so the concrete alternatives lead to different next calls. A
modeled error is an output, and the application goes on with its next call. A clock read without a
clock stops the run, and the next call is never sent. A hidden BEGIN changes the transaction snapshot
and nothing else that the outputs show, so a relation that names the snapshot tells the programs
apart. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace ApplicationBranchKindsFixture
open Belay.Sqlite Belay.Sqlite.Calls
open Belay.Sqlite.Model hiding Database

/-- A table with two rows. -/
def sample : Belay.Sqlite.Database := db! r"CREATE TABLE t(id INTEGER PRIMARY KEY, x INTEGER);
  INSERT INTO t VALUES (1, 1), (2, 2)"

/-- An environment with a clock that gives each statement its own date. -/
def dated : Env :=
  { clock := some (fun index => 212602449600000 + 86400000 * index), counters := Counters.newConnection }

/-- An environment without a clock. -/
def undated : Env := { clock := none, counters := Counters.newConnection }

/-- The start context with the clock. -/
def start : ExecutionContext := ExecutionContext.initial sample dated

/-- The start context without a clock. -/
def startUndated : ExecutionContext := ExecutionContext.initial sample undated

/-- The names of the calls. -/
inductive Call where
  | pick | low | high | other | duplicate | stamp | follow
  deriving DecidableEq

/-- Every call takes no argument. The calls give a number. -/
@[reducible] def signature : Signature Call where
  Argument _ := Unit
  Result _ := Nat

/-- The number in the only row of the only column of an output, or zero. -/
def numberOf : List Output → Nat
  | [.rows [[.integer n]]] => n.toNat
  | _ => 0

/-- The calls. {lit}`pick` reads an ambiguous row, the next three give numbers 100, 200 and 300,
{lit}`duplicate` repeats a key, {lit}`stamp` reads the clock and {lit}`follow` gives 9. -/
def interface : Interface signature
  | .pick => { script := fun _ => sql r"SELECT x FROM t LIMIT 1", result := numberOf }
  | .low => { script := fun _ => sql r"SELECT 100", result := numberOf }
  | .high => { script := fun _ => sql r"SELECT 200", result := numberOf }
  | .other => { script := fun _ => sql r"SELECT 300", result := numberOf }
  | .duplicate => { script := fun _ => sql r"INSERT INTO t VALUES (1, 5)", result := fun _ => 0 }
  | .stamp => { script := fun _ => sql r"SELECT CURRENT_TIMESTAMP", result := fun _ => 1 }
  | .follow => { script := fun _ => sql r"SELECT 9", result := numberOf }

/-- Pick a row, and then make the call that the number selects. -/
def chooser : Application signature Nat := do
  let number ← Application.invoke (signature := signature) .pick ()
  if number = 1 then Application.invoke (signature := signature) .low ()
  else if number = 2 then Application.invoke (signature := signature) .high ()
  else Application.invoke (signature := signature) .other ()

/-- Repeat a key and then ask for a number. -/
def afterError : Application signature Nat := do
  let _ ← Application.invoke (signature := signature) .duplicate ()
  Application.invoke (signature := signature) .follow ()

/-- Read the clock and then ask for a number. -/
def afterClock : Application signature Nat := do
  let _ ← Application.invoke (signature := signature) .stamp ()
  Application.invoke (signature := signature) .follow ()

/-- The actual run of the application is the third choice: the raw output is a choice between
results, and the reader of the number maps it to zero. Proof sketch: kernel evaluation. -/
theorem chooser_actual_takes_the_default :
    ((chooser.interp interface).runFrom start.clock start.index start.connection).value = some 300 := by
  decide +kernel

/-- The concrete row 1 selects the call {lit}`low`. -/
theorem chooser_row_one_takes_low :
    ∃ result, (chooser.interp interface).Branch start.clock start.index start.connection result ∧
      result.value = some 100 ∧ result.outputs = [.rows [[1]], .rows [[100]]] := by
  refine ⟨_, Sql.Branch.continued (selected := .rows [[1]]) (by rfl)
    (OutputChoice.rows (by decide +kernel)) (Sql.Branch.actual _ _ _ _), by rfl, by rfl⟩

/-- The concrete row 2 selects the call {lit}`high`. -/
theorem chooser_row_two_takes_high :
    ∃ result, (chooser.interp interface).Branch start.clock start.index start.connection result ∧
      result.value = some 200 ∧ result.outputs = [.rows [[2]], .rows [[200]]] := by
  refine ⟨_, Sql.Branch.continued (selected := .rows [[2]]) (by rfl)
    (OutputChoice.rows (by decide +kernel)) (Sql.Branch.actual _ _ _ _), by rfl, by rfl⟩

/-- A modeled error is an output, and the application sends its next call. Proof sketch: the program
has one branch, so its actual run is the only run; kernel evaluation shows an error output, then the
rows of the next call, and the value 9. -/
theorem error_is_followed_by_the_next_call :
    (afterError.interp interface).hasOneBranch start.clock start.index start.connection = true ∧
    ((afterError.interp interface).runFrom start.clock start.index start.connection).value = some 9 ∧
    (((afterError.interp interface).runFrom start.clock start.index start.connection).outputs.map
      Output.isError) = [true, false] := by
  decide +kernel

/-- A clock read without a clock stops the run: the application has no value, one output holds the
stop, and the next call is never sent. Every branch is this run. Proof sketch: the program has one
branch, and the kernel evaluates its actual run. -/
theorem stop_ends_the_application :
    (afterClock.interp interface).hasOneBranch startUndated.clock startUndated.index
      startUndated.connection = true ∧
    ((afterClock.interp interface).runFrom startUndated.clock startUndated.index
      startUndated.connection).value = none ∧
    ((afterClock.interp interface).runFrom startUndated.clock startUndated.index
      startUndated.connection).outputs.length = 1 := by
  decide +kernel

/-- Two programs with the same output, one of which opens a transaction. -/
def opens : Sql Unit := (send (sql r"BEGIN")).map fun _ => ()

/-- A program with the same output as {name}`opens` that opens no transaction. -/
def keeps : Sql Unit := (send (sql r"DELETE FROM t WHERE 1 = 0")).map fun _ => ()

/-- A relation that names the snapshot: both contexts have an open transaction or neither has. -/
def sameSnapshot (first second : ExecutionContext) : Prop :=
  first.connection.state.snapshot.isSome = second.connection.state.snapshot.isSome

/-- A relation that ignores everything. -/
def anything (_first _second : ExecutionContext) : Prop := True

/-- The two programs agree when the relation ignores the snapshot, because the outputs and the values
are equal. Proof sketch: both programs have one branch and equal actual runs up to the connection. -/
theorem opening_agrees_when_the_snapshot_is_ignored :
    Sql.ScopedAt anything opens keeps start start := by
  apply Sql.ScopedAt.of_one_branch (by decide +kernel) (by decide +kernel)
  exact ⟨by decide +kernel, by decide +kernel, trivial⟩

/-- The two programs do not agree when the relation names the snapshot: BEGIN opens a transaction and
the other statement does not. Proof sketch: the agreement requires the relation for the reached
contexts, and the kernel evaluates their snapshots. -/
theorem opening_disagrees_when_the_snapshot_is_related :
    ¬ Sql.ScopedAt sameSnapshot opens keeps start start := by
  intro agree
  have reached := agree.actual.2.2
  revert reached
  simp only [sameSnapshot, ExecutionContext.finish]
  decide +kernel

#print axioms chooser_actual_takes_the_default
#print axioms chooser_row_one_takes_low
#print axioms chooser_row_two_takes_high
#print axioms error_is_followed_by_the_next_call
#print axioms stop_ends_the_application
#print axioms opening_agrees_when_the_snapshot_is_ignored
#print axioms opening_disagrees_when_the_snapshot_is_related

end ApplicationBranchKindsFixture
