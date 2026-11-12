import Belay

/-! Program algebra for S4: arbitrary programs satisfy the monad and run-composition laws.
Concrete runs preserve an open transaction, advance the clock index, and stop before a
continuation after an unmodeled statement. The Python test audits the law wrappers' axioms. -/

open Belay.Sqlite
open Belay.Sqlite.Model (Clock)

example (p : Sql Nat) : (p >>= pure) = p := by simp
example (value : Nat) (next : Nat → Sql Bool) : (pure value >>= next) = next value := by simp
example (p : Sql Nat) (f : Nat → Sql Bool) (g : Bool → Sql String) :
    ((p >>= f) >>= g) = (p >>= fun x => f x >>= g) := by simp

/-- Bind composes runs on the full connection and the next statement index. -/
theorem bind_keeps_connection {α β : Type} (p : Sql α) (next : α → Sql β)
    (clock : Option Clock) (index : Nat) (connection : Connection) :
    (p.bind next).runFrom clock index connection =
      (p.runFrom clock index connection).andThen fun value state =>
        (next value).runFrom clock (index + (p.runFrom clock index connection).outputs.length) state :=
  Sql.runFrom_bind p next clock index connection

/-- Script concatenation uses the same program bind law. -/
theorem send_keeps_connection (p q : Script) (clock : Option Clock) (index : Nat) (connection : Connection) :
    (send (p ++ q)).runFrom clock index connection =
      ((send p).runFrom clock index connection).andThen fun before state =>
        ((send q).map (before ++ ·)).runFrom clock
          (index + ((send p).runFrom clock index connection).outputs.length) state :=
  Sql.runFrom_send_append p q clock index connection

/-- A database whose table is initially empty. -/
def start : Database := db! r"CREATE TABLE t (x INTEGER)"

example : (start.run do
    let _ ← send (sql r"BEGIN; INSERT INTO t VALUES (1)")
    let value ← single (sql r"SELECT count(*) FROM t")
    let _ ← send (sql r"COMMIT")
    pure value).value = some (some 1) := by decide +kernel

/-- The clock advances one day per statement, so resetting its index would change the output. -/
def daily : Env := { clock := some (fun index => 212602449600000 + 86400000 * index) }

example : (start.run (env := daily) do
    let first ← single (sql r"SELECT CURRENT_TIMESTAMP")
    let second ← single (sql r"SELECT CURRENT_TIMESTAMP")
    pure (first, second)).value =
      some (some (("2025-01-01 00:00:00" : String) : Value),
        some (("2025-01-02 00:00:00" : String) : Value)) := by decide +kernel

example : (start.run do
    let _ ← single (sql r"SELECT random()")
    send (sql r"INSERT INTO t VALUES (1)")).db.rows "t" = some [] := by decide +kernel

#print axioms bind_keeps_connection
#print axioms send_keeps_connection
#print axioms Belay.Sqlite.instLawfulMonadSql
