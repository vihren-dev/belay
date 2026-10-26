import Belay.Sqlite.ExecutionBind
import Belay.Sqlite.SqlTerm
import Belay.Sqlite.DbBang

set_option doc.verso true
set_option maxRecDepth 4096

namespace ExecutionExamples
open Belay.Sqlite Belay.Sqlite.Model

/-- Two rows expose both LIMIT choices, and the explicit rowid column supports later writes. -/
def sample : Belay.Sqlite.Database := db! r"CREATE TABLE t(id INTEGER PRIMARY KEY, x INTEGER);
  INSERT INTO t VALUES (1, 1), (2, 2)"

/-- A complete environment with a distinct timestamp for each statement index. -/
def daily : Env :=
  { clock := some (fun index => 212602449600000 + 86400000 * index)
    counters := Counters.newConnection }

/-- The exact starting context of these fixtures. -/
def initial : ExecutionContext := ExecutionContext.initial sample daily

/-- Return the raw output without the query helper's row projection. -/
def observe : Sql Output :=
  let (statement, values) := (sql r"SELECT x FROM t LIMIT 1").statements[0]
  .exec statement values .pure

/-- The actual raw wrapper is retained as both the program value and the one-step trace. -/
theorem raw_branch : observe.Branch daily.clock 0 initial.connection
    (observe.runFrom daily.clock 0 initial.connection) := Sql.Branch.actual observe _ _ _

/-- Each permitted concrete rows result also becomes the value and the trace observation. -/
theorem second_branch : observe.Branch daily.clock 0 initial.connection
    { outputs := [.rows [[2]]], connection := initial.connection, value := some (.rows [[2]]) } := by
  unfold observe
  apply Sql.Branch.continued_own (rest := Sql.pure) (actual := .oneOf [[[1]], [[2]]]) (next := initial.connection)
    (selected := .rows [[2]]) (result := { outputs := [], connection := initial.connection, value := some (.rows [[2]]) })
  · rfl
  · exact OutputChoice.rows (by simp)
  · exact .pure _ _ _ _

/-- Repeating a listed result changes no concrete rows choices; the actual wrappers remain distinct. -/
theorem repeated_choices (rows : List (List Value)) :
    OutputChoice (.oneOf [[[1]], [[1]]]) (.rows rows) ↔ OutputChoice (.oneOf [[[1]]]) (.rows rows) := by
  simp [OutputChoice]

/-- An empty alternative list retains exactly the actual raw wrapper. -/
theorem empty_choices (selected : Output) :
    OutputChoice (.oneOf []) selected ↔ selected = .oneOf [] := by simp [OutputChoice]

/-- A stopped prefix suppresses a later write; its reason and one executed step are retained. -/
theorem stopped_bind :
    ((send (sql r"SELECT random()")).bind fun _ => send (sql r"INSERT INTO t VALUES (3, 3)")).Branch
      daily.clock 0 initial.connection
      { (send (sql r"SELECT random()")).runFrom daily.clock 0 initial.connection with value := none } :=
  (Sql.Branch.actual (send (sql r"SELECT random()")) _ _ _).bind_stopped (by decide +kernel) _

/-- Advancing a stopped result counts its stopping output, while keeping the clock. -/
theorem stopped_index :
    (initial.finish ((send (sql r"SELECT random()")).runFrom daily.clock 0 initial.connection)).index = 1 := by
  decide +kernel

#print axioms raw_branch
#print axioms second_branch
#print axioms repeated_choices
#print axioms empty_choices
#print axioms stopped_bind
#print axioms stopped_index
#print axioms Sql.Branch.actual
#print axioms Sql.Branch.valid
#print axioms Sql.branch_pure_iff
#print axioms Sql.branch_stopped_iff
#print axioms Sql.branch_continued_iff
#print axioms Sql.Branch.bind_stopped
#print axioms Sql.Branch.bind_return
#print axioms Sql.branch_bind_iff
end ExecutionExamples
