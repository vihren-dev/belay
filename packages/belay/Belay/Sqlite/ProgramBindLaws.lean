import Belay.Sqlite.ProgramMonadLaws
import Belay.Sqlite.ProgramLaws

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- Compose a program result with the next run. A result without a value keeps its outputs
and connection and skips the next run. A result with a value passes that value and its
connection to the next run, and prefixes its outputs to the next run's outputs. Use this
operation to state composition without losing transaction state or counters. -/
def SqlRun.andThen {α β : Type} (first : SqlRun α) (next : α → Connection → SqlRun β) : SqlRun β :=
  match first.value with
  | none => { first with value := none }
  | some value =>
    let later := next value first.connection
    { later with outputs := first.outputs ++ later.outputs }

/-- For every program, continuation, clock, starting index and connection, running their
bind first runs the program. If that run has no value, execution stops there. Otherwise the
continuation runs on that value and the exact connection left by the program, at the starting
index plus the number of outputs already produced. The outputs concatenate.
Proof sketch: induction on the program. Both runs take the same first step; a continuing step
adds one output and advances the index by one, and an ending step skips the continuation. -/
theorem Sql.runFrom_bind {α β : Type} (program : Sql α) (next : α → Sql β) :
    ∀ (clock : Option Clock) (index : Nat) (connection : Connection),
      (program.bind next).runFrom clock index connection =
        (program.runFrom clock index connection).andThen fun value state =>
          (next value).runFrom clock (index + (program.runFrom clock index connection).outputs.length) state := by
  induction program with
  | pure value => intro clock index connection; simp [Sql.bind, Sql.runFrom, SqlRun.andThen]
  | exec statement values rest later =>
    intro clock index connection
    simp only [Sql.bind, Sql.runFrom]
    cases step : runScriptStep runContext clock index connection statement values with
    | ended reason => rfl
    | continued output state =>
      simp only [later, SqlRun.andThen]
      cases result : (Sql.runFrom clock (index + 1) state (rest output)).value <;>
        simp [Nat.add_assoc, Nat.add_comm]

/-- For all scripts, clocks, indices and connections, sending a concatenated script runs
the first script, then sends the second on its exact final connection at the next statement
index. A stopped first run skips the second. The returned value concatenates both scripts'
outputs, as does the run's output list. Proof sketch: {name}`send_append` and
{name}`Sql.runFrom_bind`. -/
theorem Sql.runFrom_send_append (first second : Script) (clock : Option Clock)
    (index : Nat) (connection : Connection) :
    (send (first ++ second)).runFrom clock index connection =
      ((send first).runFrom clock index connection).andThen fun before state =>
        ((send second).map (before ++ ·)).runFrom clock
          (index + ((send first).runFrom clock index connection).outputs.length) state := by
  rw [send_append]
  change ((send first).bind (fun before =>
    (send second).bind (fun after => .pure (before ++ after)))).runFrom clock index connection = _
  simp only [Sql.bind_pure_map]
  exact Sql.runFrom_bind (send first) (fun before => (send second).map (before ++ ·)) clock index connection

end Belay.Sqlite
