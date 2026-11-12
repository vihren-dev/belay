import S6WpExamples

set_option doc.verso true
set_option maxRecDepth 4096

/-! Test which observations suffice for composition of SQL programs. -/

namespace S6.Equivalence
open Belay.Sqlite
open Examples

/-- A table with an explicit rowid alias for the counter and snapshot examples. -/
def sample : Database := db! r"CREATE TABLE t(id INTEGER PRIMARY KEY, x INTEGER);
  INSERT INTO t VALUES (1, 1), (2, 2)"

/-- The guide's visible comparison at one starting context: equal return values, outputs
and final databases. Equal databases imply equal fresh read-only observations in any fixed
environment. Connection settings, counters and snapshots are not compared here. -/
def Visible {α : Type} (first second : SqlRun α) : Prop :=
  first.value = second.value ∧ first.outputs = second.outputs ∧
    first.connection.state.database = second.connection.state.database

/-- Run a script and discard its returned output list, while retaining its actual output trace. -/
def execute (script : Script) : Sql Unit := (send script).map fun _ => ()

/-- The underlying run from the example's fixed complete environment. -/
def run (program : Sql Unit) : SqlRun Unit :=
  program.runFrom daily.clock 0 (sample.raw.connection daily.counters)

/-- Two scripts leave the same visible database and trace, but different last-insert counters. -/
def insertErase (id : Int64) : Sql Unit :=
  execute (sql r"INSERT INTO t(id, x) VALUES ($id, 9); DELETE FROM t WHERE x = 9")

/-- A later counter read distinguishes prefixes that meet the visible comparison. -/
theorem counters_distinguish : Visible (run (insertErase 10)) (run (insertErase 20)) ∧
    ((insertErase 10 >>= fun _ => single (sql r"SELECT last_insert_rowid()")).run sample daily).value ≠
    ((insertErase 20 >>= fun _ => single (sql r"SELECT last_insert_rowid()")).run sample daily).value := by
  unfold Visible
  decide +kernel

/-- Pragma assignments both return done 0 and keep the database. -/
def foreignOn : Sql Unit := execute (sql r"PRAGMA foreign_keys = ON")
/-- The other assignment leaves the same visible result but a different setting. -/
def foreignOff : Sql Unit := execute (sql r"PRAGMA foreign_keys = OFF")

/-- A continuation observes the pragma setting omitted by the visible comparison. -/
theorem pragmas_distinguish : Visible (run foreignOn) (run foreignOff) ∧
    ((foreignOn >>= fun _ => single (sql r"PRAGMA foreign_keys")).run sample daily).value ≠
    ((foreignOff >>= fun _ => single (sql r"PRAGMA foreign_keys")).run sample daily).value := by
  unfold Visible
  decide +kernel

/-- BEGIN saves the database without the temporary table. All three outputs are done 0. -/
def snapshotEarly : Sql Unit := execute (sql r"BEGIN; CREATE TABLE extra(y INTEGER); DROP TABLE extra")
/-- BEGIN instead saves the temporary table, though the final visible database is the same. -/
def snapshotLate : Sql Unit := execute (sql r"CREATE TABLE extra(y INTEGER); BEGIN; DROP TABLE extra")

/-- Rollback distinguishes equal current databases by their transaction snapshots. -/
theorem snapshots_distinguish : Visible (run snapshotEarly) (run snapshotLate) ∧
    ((snapshotEarly >>= fun _ => send (sql r"ROLLBACK")).run sample daily).db.raw ≠
    ((snapshotLate >>= fun _ => send (sql r"ROLLBACK")).run sample daily).db.raw := by
  unfold Visible
  decide +kernel

/-- error: AUTOINCREMENT is not modeled; remove it -/
#guard_msgs in
example : Database := db! r"CREATE TABLE n(id INTEGER PRIMARY KEY AUTOINCREMENT)"

/-- The same statement has different results at different supplied clock indices. -/
theorem index_distinguishes :
    ((send (sql r"SELECT CURRENT_TIMESTAMP")).runFrom daily.clock 0
      (sample.raw.connection daily.counters)).outputs ≠
    ((send (sql r"SELECT CURRENT_TIMESTAMP")).runFrom daily.clock 1
      (sample.raw.connection daily.counters)).outputs := by decide +kernel

/-- Equality adequate for the observations checked here: actual full runs agree at every
clock, index and connection; both error-policy transformers agree for every postcondition
and context. It does not claim equality of traces on alternative unmodeled branches. -/
def CheckedEq {α : Type} (first second : Sql α) : Prop :=
  (∀ clock index connection, first.runFrom clock index connection = second.runFrom clock index connection) ∧
  ∀ reject post state, check reject first post state ↔ check reject second post state

/-- For all programs related by {name}`CheckedEq`, appending the same result-dependent
continuation preserves that relation. Proof sketch: the existing actual bind law passes
identical full results; {name}`check_bind` passes the same continuation postcondition. -/
theorem bind_right {α β : Type} {first second : Sql α} (same : CheckedEq first second)
    (next : α → Sql β) : CheckedEq (first.bind next) (second.bind next) := by
  constructor
  · intro clock index connection
    rw [Sql.runFrom_bind, Sql.runFrom_bind, same.1 clock index connection]
  · intro reject post state
    rw [check_bind, check_bind]
    exact same.2 reject _ state

/-- For every prefix and pointwise-related continuations, bind preserves {name}`CheckedEq`.
Proof sketch: the actual bind law applies the related continuations to the same result;
transformer bind then replaces pointwise equivalent postconditions. -/
theorem bind_left {α β : Type} (program : Sql α) {first second : α → Sql β}
    (same : ∀ value, CheckedEq (first value) (second value)) :
    CheckedEq (program.bind first) (program.bind second) := by
  constructor
  · intro clock index connection
    rw [Sql.runFrom_bind, Sql.runFrom_bind]
    unfold SqlRun.andThen
    split
    · rfl
    · rename_i value returned
      dsimp only
      rw [(same value).1]
  · intro reject post state
    rw [check_bind, check_bind]
    have posts : (fun value state => check reject (first value) post state) =
        (fun value state => check reject (second value) post state) := by
      funext value state
      exact propext ((same value).2 reject post state)
    rw [posts]

#print axioms counters_distinguish
#print axioms pragmas_distinguish
#print axioms snapshots_distinguish
#print axioms index_distinguishes
#print axioms bind_right
#print axioms bind_left
end S6.Equivalence
