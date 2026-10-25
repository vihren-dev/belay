import ViewsSupport

set_option doc.verso true
set_option maxRecDepth 8000
set_option maxHeartbeats 800000

/-! Stored-view lookup is late, nested and independent of caller CTE names.
These kernel claims check the same indexed resolver used by derived tables. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open ViewExamples
open Lean Elab Meta

namespace ViewSourceExamples

/-- Ordinary, nested, renamed and locally correlated view definitions. -/
def database : Database := ⟨withViews base [
  (name! "v", definition (sql r"SELECT x,text_value FROM t")),
  (name! "renamed", definition (sql r"SELECT x,text_value FROM v") (some [name! "number",name! "label"])),
  (name! "local", definition (sql r"SELECT x,(SELECT x+1) AS next FROM t")),
  (name! "own_cte", definition (sql r"WITH t AS (SELECT 5 AS x) SELECT * FROM t")),
  (name! "clock_counter", definition (sql r"SELECT CURRENT_DATE AS day,changes() AS count")),
  (name! "late", definition (sql r"SELECT x FROM future"))], by decide +kernel⟩

/-- Uniform sampling retains the six unresolved definitions with empty view storage. -/
example : (Sampling.uniform database [.integer 9]).map
    (fun sample => (sample.raw.catalog, sample.raw.rows.drop 2)) =
    some (database.raw.catalog, List.replicate 6 []) := by decide +kernel

/- Run the seeded generator as code, then independently check the resulting
database's validity with the kernel. Random generation is not a kernel decision. -/
run_meta do
  let .ok sample := Sampling.seeded (Sampling.database database (maxRows := 0))
    | throwError "zero-row sampling rejected the view catalog"
  unless sample.raw.catalog == database.raw.catalog && sample.raw.rows.all List.isEmpty do
    throwError "sampling changed the view catalog or stored rows for a view"
  checkWithKernel (databaseExpr sample.raw)

/- The shared incremental traversal draws only for physical tables, but checks resources
for every catalog object. Assembly must discard cells supplied for a view's storage slot. -/
run_meta do
  let draws ← IO.mkRef (0 : Nat)
  let checks ← IO.mkRef (0 : Nat)
  let cells ← Sampling.selectCells database.raw.catalog
    (do draws.modify (· + 1); pure 1) (pure (.integer 9)) (checks.modify (· + 1))
  unless (← draws.get) == 2 && (← checks.get) == 10 &&
      cells == [[[.integer 9]], [[.integer 9, .integer 9]]] ++ List.replicate 6 [] do
    throwError "shared sampling drew view rows or skipped a resource boundary"
  let raw := Sampling.withCells database.raw
    (cells.take 2 ++ List.replicate 6 [[.integer 99]])
  unless some raw == (Sampling.uniform database [.integer 9]).map (·.raw) do
    throwError "shared assembly retained supplied view cells or changed physical rows"
  checkWithKernel (databaseExpr raw)

/-- The ordinary-table replay formatter refuses a view instead of omitting its definition. -/
example : Replay.databaseSql database = none := by decide +kernel

/-- Renaming two columns keeps integer affinity and NOCASE collation. -/
example : Holds (sql r"SELECT 1 FROM renamed WHERE number='7' AND label='A'") database := by decide +kernel

/-- Stars, qualification and aliases use the view's exposed column list. -/
example : Holds (sql r"SELECT r.* FROM renamed r WHERE r.number=8") database := by decide +kernel

/-- The view has no implicit rowid, although its source table does. -/
example : prepareMessage (sql r"SELECT rowid FROM v") database = some "no such column: rowid" := by decide +kernel

/-- Removing an earlier catalog object changes positions without changing a stored name. -/
def shifted : Database := ⟨database.raw.drop [0], by decide +kernel⟩

/-- The view resolves its source at the new catalog position. -/
example : Holds (sql r"SELECT 1 FROM v WHERE x=7") shifted := by decide +kernel

/-- Removing the source table preserves the definition and makes its next use fail. -/
def missing : Database := ⟨database.raw.drop [1], by decide +kernel⟩

/-- A missing source inside a stored view is qualified with its schema once. -/
example : prepareMessage (sql r"SELECT * FROM renamed") missing = some "no such table: main.t" := by decide +kernel

/-- A definition can remain unresolved until its table is created. -/
example : prepareMessage (sql r"SELECT * FROM late") database = some "no such table: main.future" := by decide +kernel

/-- A later physical table lets the same unresolved definition resolve. -/
def completed : Database := ⟨{database.raw with
  catalog := database.catalog.createTable (name! "future") {columns := [{name := name! "x", declaredType := none}]}
  rows := database.raw.rows ++ [[{rowid := 1, values := [.integer 9]}]]}, by decide +kernel⟩

/-- The late use reads the newly created table's row. -/
example : Holds (sql r"SELECT 1 FROM late WHERE x=9") completed := by decide +kernel

/-- Caller CTEs do not shadow the physical source inside a stored definition. -/
example : Holds (sql r"WITH t AS (SELECT 100 AS x) SELECT 1 FROM v WHERE x=7") database := by decide +kernel

/-- A stored view's own WITH names remain local to that definition. -/
example : Holds (sql r"WITH t AS (SELECT 100 AS x) SELECT 1 FROM own_cte WHERE x=5") database := by decide +kernel

/-- Outer cells do not replace the view's local table cells. -/
example : Holds (sql r"SELECT 1 FROM (SELECT 100 AS x) WHERE (SELECT next FROM local WHERE x=7)=8")
    database := by decide +kernel

/-- Stored sources share the supplied clock and counters while the outer query
reads its bound parameter in the same statement context. -/
example : queryRows (sql r"SELECT day,count,?1 FROM clock_counter" (.integer 5)) database
    212640249600000 {changes := some 11} =
    some [[TimeKeyword.date.value 212640249600000,.integer 11,.integer 5]] := by decide +kernel

/-- Source failure and uncertain membership keep their existing refusal semantics. -/
def uncertain : Database := ⟨withViews base [
  (name! "limited", definition (sql r"SELECT x FROM t LIMIT 1")),
  (name! "bad_expr", definition (sql r"SELECT abs(-9223372036854775808) FROM t"))], by decide +kernel⟩

/-- A view whose LIMIT can select different rows is neither true, empty nor an error. -/
example : ¬ Holds (sql r"SELECT * FROM limited") uncertain ∧
    ¬ Empty (sql r"SELECT * FROM limited") uncertain ∧
    ¬ Fails (sql r"SELECT * FROM limited") uncertain := by decide +kernel

/-- An expression failure in a stored source is not an empty successful relation. -/
example : ¬ Holds (sql r"SELECT * FROM bad_expr") uncertain ∧
    ¬ Empty (sql r"SELECT * FROM bad_expr") uncertain ∧
    ¬ Fails (sql r"SELECT * FROM bad_expr") uncertain := by decide +kernel

end ViewSourceExamples
