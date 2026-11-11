import S6Equivalence

set_option doc.verso true
set_option maxRecDepth 4096

/-! Refute statement-local frames for result-dependent SQL programs. -/

namespace S6.Footprints
open Belay.Sqlite

/-- A branch source and a table that its later program can change. -/
def sample : Database := db! r"CREATE TABLE a(x INTEGER); INSERT INTO a VALUES (1), (2);
  CREATE TABLE b(y INTEGER); INSERT INTO b VALUES (0)"

/-- The actual LIMIT choice does nothing, but another permitted choice writes the other table. -/
def maybeWrite : Sql Unit := do
  match ← single (sql r"SELECT x FROM a LIMIT 1") with
  | some (.integer 1) => pure ()
  | _ => let _ ← send (sql r"UPDATE b SET y = 9"); pure ()

/-- A read-only first call and an unchanged actual final database do not establish a frame
for a program: another permitted continuation changes it. -/
theorem local_footprint_refuted :
    (sample.run maybeWrite Examples.daily).db.raw = sample.raw ∧
    ¬ check true maybeWrite (fun _ state => state.connection.state.database = sample.raw)
      (initial sample Examples.daily) := by decide +kernel

/-- Two tables with rowid aliases let independent writes set distinct counter values. -/
def separate : Database := db! r"CREATE TABLE a(id INTEGER PRIMARY KEY); CREATE TABLE b(id INTEGER PRIMARY KEY)"

/-- Insert into one table, then the other. -/
def firstOrder : Sql Unit := Equivalence.execute (sql r"INSERT INTO a VALUES (1); INSERT INTO b VALUES (2)")
/-- Reverse those table-disjoint writes. -/
def secondOrder : Sql Unit := Equivalence.execute (sql r"INSERT INTO b VALUES (2); INSERT INTO a VALUES (1)")

/-- Disjoint table writes commute on the visible database and output trace, but a later
counter read distinguishes their order. This refutes a table-only SQL commutation rule. -/
theorem disjoint_tables_not_enough :
    (firstOrder.run separate Examples.daily).db.raw = (secondOrder.run separate Examples.daily).db.raw ∧
    (firstOrder.run separate Examples.daily).outputs = (secondOrder.run separate Examples.daily).outputs ∧
    ((firstOrder >>= fun _ => single (sql r"SELECT last_insert_rowid()")).run separate Examples.daily).value ≠
    ((secondOrder >>= fun _ => single (sql r"SELECT last_insert_rowid()")).run separate Examples.daily).value := by
  decide +kernel

/-- For any program, proving that every branch preserves a chosen observation requires
that observation at the end of every actual and alternative continuation. The first call's
statement-local footprint cannot replace this premise. -/
theorem all_continuations_frame {α β : Type} (program : Sql α) (next : α → Sql β)
    (observe : Context → Prop) (state : Context)
    (branches : check true program (fun value state => check true (next value)
      (fun _ final => observe final) state) state) :
    check true (program.bind next) (fun _ final => observe final) state := by
  rw [check_bind]
  exact branches

/-- A source in the schema {lit}`before` translates: {lit}`Script.observeTwoState` reads it from the fixed
initial database, and the ordinary run of the script refuses it. -/
example : Script := sql r"SELECT x FROM before.t EXCEPT SELECT x FROM t"

#print axioms local_footprint_refuted
#print axioms disjoint_tables_not_enough
#print axioms all_continuations_frame
end S6.Footprints
