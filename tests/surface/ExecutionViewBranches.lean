import ExecutionViews

set_option doc.verso true
set_option maxRecDepth 4096

namespace ExecutionViewExamples
open Belay.Sqlite Belay.Sqlite.Model

/-- Return the chosen raw wrapper or concrete rows without the query helper's conversion. -/
def observe : Sql Output :=
  let (statement, values) := (sql r"SELECT x FROM t LIMIT 1").statements[0]
  .exec statement values .pure

/-- The migration's length depends on the exact chosen output of the application query. -/
def chosenMigration (output : Output) : Sql (List Output) :=
  if output = .rows [[2]] then send (sql r"SELECT 2; SELECT 2") else send (sql r"SELECT 1")

/-- The application result chooses its migration through ordinary bind. -/
def chosen : Sql (List Output) := observe.bind chosenMigration

/-- Each chosen migration has its own witness; all application choices remain visible. -/
def chosenView : Sql.View chosen :=
  (Sql.View.identity observe).bind chosenMigration fun output => Sql.View.quiet (chosenMigration output)

/-- The raw wrapper reaches the one-step migration and remains the application observation. -/
theorem actual_choice :
    let result := chosen.runFrom daily.clock 0 initial.connection
    chosenView.observation result = (some [.rows [[1]]], [.oneOf [[[1]], [[2]]]]) ∧
    (chosenView.finish initial result).index = 2 := by decide +kernel

/-- The second listed rows result is a permitted application branch. -/
theorem second_choice : observe.Branch daily.clock 0 initial.connection
    { outputs := [.rows [[2]]], connection := initial.connection, value := some (.rows [[2]]) } := by
  unfold observe
  apply Sql.Branch.continued (rest := Sql.pure) (actual := .oneOf [[[1]], [[2]]]) (next := initial.connection)
    (selected := .rows [[2]]) (result := { outputs := [], connection := initial.connection, value := some (.rows [[2]]) })
  · rfl
  · exact OutputChoice.rows (by simp)
  · exact .pure _ _ _ _

/-- A permitted concrete choice executes its two-step migration, with its exact result. -/
theorem selected_branch : chosen.Branch daily.clock 0 initial.connection
    { outputs := [.rows [[2]], .rows [[2]], .rows [[2]]], connection := initial.connection,
      value := some [.rows [[2]], .rows [[2]]] } := by
  exact second_choice.bind_return rfl chosenMigration
    (Sql.Branch.actual (chosenMigration (.rows [[2]])) daily.clock 1 initial.connection)

/-- The chosen migration's two outputs are hidden, while its returned value and all three
raw steps remain observable. The application output is equal to the hidden outputs. -/
theorem selected_projection :
    let result : SqlRun (List Output) :=
      { outputs := [.rows [[2]], .rows [[2]], .rows [[2]]], connection := initial.connection,
        value := some [.rows [[2]], .rows [[2]]] }
    chosenView.observation result = (some [.rows [[2]], .rows [[2]]], [.rows [[2]]]) ∧
    (chosenView.finish initial result).index = 3 := by decide +kernel

/-- The generic concatenation law applies to a concrete branch and any continuation trace. -/
theorem chosen_concatenation (suffix : List Output) :
    chosenView.project ([.rows [[2]]] ++ suffix) =
      [.rows [[2]]] ++ (Sql.View.quiet (chosenMigration (.rows [[2]]))).project suffix :=
  Sql.View.project_bind_return second_choice (Sql.View.identity observe) rfl chosenMigration _ suffix

/-- The complete-context concatenation law also accepts the result-dependent witness. -/
theorem chosen_finish (last : SqlRun (List Output)) :
    chosenView.finish initial { last with outputs := [.rows [[2]]] ++ last.outputs } =
      (Sql.View.quiet (chosenMigration (.rows [[2]]))).finish
        ((Sql.View.identity observe).finish initial
          { outputs := [.rows [[2]]], connection := initial.connection, value := some (.rows [[2]]) }) last :=
  Sql.View.finish_bind_return initial second_choice (Sql.View.identity observe) rfl chosenMigration _ last

#print axioms actual_choice
#print axioms second_choice
#print axioms selected_branch
#print axioms selected_projection
#print axioms chosen_concatenation
#print axioms chosen_finish
end ExecutionViewExamples
