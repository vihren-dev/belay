import Belay.Sqlite.ExecutionViewBind
import Belay.Sqlite.SqlTerm
import Belay.Sqlite.DbBang

set_option doc.verso true
set_option maxRecDepth 4096

namespace ExecutionViewExamples
open Belay.Sqlite Belay.Sqlite.Model

/-- Two rows support writes and the alternative-query fixture. -/
def sample : Belay.Sqlite.Database := db! r"CREATE TABLE t(id INTEGER PRIMARY KEY, x INTEGER);
  INSERT INTO t VALUES (1, 1), (2, 2)"

/-- Each raw statement index has a distinct timestamp. -/
def daily : Env :=
  { clock := some (fun index => 212602449600000 + 86400000 * index)
    counters := Counters.newConnection }

/-- The shared starting context contains no earlier output. -/
def initial : ExecutionContext := ExecutionContext.initial sample daily

/-- A repeated query makes output equality insufficient to identify migration steps. -/
def repeated : Sql (List Output) := send (sql r"SELECT 1")

/-- The migration has two outputs equal to its surrounding application's outputs. -/
def migration : Sql (List Output) := send (sql r"SELECT 1; SELECT 1")

/-- Only the final application's outputs are returned, while all four steps execute. -/
def surrounded : Sql (List Output) := repeated.bind fun _ => migration.bind fun _ => repeated

/-- Only the two middle steps are quiet, even though all four outputs are equal. -/
def surroundedView : Sql.View surrounded :=
  (Sql.View.identity repeated).bind _ fun _ =>
    (Sql.View.quiet migration).bind _ fun _ => Sql.View.identity repeated

/-- Projection keeps both application outputs and the ordinary interpreter keeps all four. -/
theorem duplicate_outputs :
    let result := surrounded.runFrom daily.clock 0 initial.connection
    result.outputs = List.replicate 4 (.rows [[1]]) ∧
    surroundedView.observation result = (some [.rows [[1]]], List.replicate 2 (.rows [[1]])) ∧
    (surroundedView.finish initial result).index = 4 := by decide +kernel

/-- Quiet observation leaves a returned list of migration outputs unchanged. -/
theorem migration_value :
    (Sql.View.quiet migration).observation (migration.runFrom daily.clock 0 initial.connection) =
      (some [.rows [[1]], .rows [[1]]], []) := by decide +kernel

/-- An empty migration retains its returned value, starting trace and next index. -/
theorem empty_segment :
    let state := { initial with index := 7, outputs := [.error 1] }
    let program : Sql Nat := .pure 9
    let result := program.runFrom state.clock state.index state.connection
    (Sql.View.quiet program).observation result = (some 9, []) ∧
    (Sql.View.quiet program).finish state result = state := by exact ⟨rfl, rfl⟩

/-- A quiet failed statement remains visible and its following write still executes. -/
theorem error_then_write :
    let program := send (sql r"SELECT absent FROM missing; INSERT INTO t VALUES (3, 3)")
    let result := program.runFrom daily.clock 0 initial.connection
    (Sql.View.quiet program).observation result = (some [.error 1, .done 1], [.error 1]) ∧
    ((Sql.View.quiet program).finish initial result).connection.state.counters.totalChanges = some 1 := by
  decide +kernel

/-- An unmodeled step inside a quiet segment retains its exact reason, partial state and
raw step count; the following write does not execute. -/
theorem stopped_inside :
    let program := send (sql r"SELECT 1; SELECT random(); INSERT INTO t VALUES (3, 3)")
    let result := program.runFrom daily.clock 0 initial.connection
    result.value = none ∧ result.outputs.length = 2 ∧ (result.outputs[1]?).map Output.endsRun = some true ∧
    (Sql.View.quiet program).project result.outputs = result.outputs.drop 1 ∧
    ((Sql.View.quiet program).finish initial result).index = 2 ∧
    result.connection.state.database.rowsAt 0 = sample.raw.rowsAt 0 := by decide +kernel

/-- A stopped application prefix never enters a later quiet migration. -/
theorem stopped_outside :
    let before := send (sql r"SELECT random()")
    let program := before.bind fun _ => migration
    let view := (Sql.View.identity before).bind (fun _ => migration) (fun _ => Sql.View.quiet migration)
    let result := program.runFrom daily.clock 0 initial.connection
    result.value = none ∧ result.outputs.length = 1 ∧ view.project result.outputs = result.outputs := by
  decide +kernel

/-- A hidden transaction and write retain the snapshot, counters and advanced statement
index. Their outputs also remain in the returned value and ordinary run. -/
theorem transaction_effects :
    let program := send (sql r"BEGIN; INSERT INTO t VALUES (3, 3)")
    let result := program.runFrom daily.clock 0 initial.connection
    let reached := (Sql.View.quiet program).finish initial result
    result.outputs = [.done 0, .done 1] ∧ reached.outputs = [] ∧ reached.index = 2 ∧
    reached.connection.state.snapshot = some sample.raw ∧
    reached.connection.state.counters.totalChanges = some 1 := by decide +kernel

/-- Hiding the first clock query does not reset the second query's statement index. -/
theorem clock_advances :
    let read := send (sql r"SELECT CURRENT_TIMESTAMP")
    let program := read.bind fun _ => read
    let view := (Sql.View.quiet read).bind (fun _ => read) (fun _ => Sql.View.identity read)
    let result := program.runFrom daily.clock 0 initial.connection
    view.observation result =
      (some [.rows [[("2025-01-02 00:00:00" : String)]]],
        [.rows [[("2025-01-02 00:00:00" : String)]]]) ∧
    (view.finish initial result).index = 2 := by decide +kernel

#print axioms duplicate_outputs
#print axioms migration_value
#print axioms empty_segment
#print axioms error_then_write
#print axioms stopped_inside
#print axioms stopped_outside
#print axioms transaction_effects
#print axioms clock_advances
#print axioms Sql.View.erase_runFrom
#print axioms Sql.View.project_identity
#print axioms Sql.View.project_failures
#print axioms Sql.View.observation_value
#print axioms Sql.View.fullObservation_value
#print axioms Sql.View.finish_index
#print axioms Sql.View.finish_clock
#print axioms Sql.View.finish_connection
#print axioms Sql.View.finish_outputs
#print axioms Sql.View.finish_identity
#print axioms Sql.View.project_bind_stopped
#print axioms Sql.View.project_bind_return
#print axioms Sql.View.finish_bind_return
end ExecutionViewExamples
