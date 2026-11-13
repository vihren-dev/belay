import Belay

/-! Success notation keeps the flexible predicate primitive and checks query preconditions
at their own source position, including preconditions with bound Lean values. -/

open Belay.Sqlite

example : (Sql.pure 1 succeeds) := Succeeds.pure _ _
example : (Sql.pure 1 succeeds where sql r"SELECT 1") := Succeeds.pure _ _
example (x : Value) : (Sql.pure x succeeds where sql r"SELECT $x") := Succeeds.pure _ _

/-- The schema of the claims with {lit}`on`. -/
def shop : Database := db! "CREATE TABLE t(a)"

/-- Success on a schema covers the databases with the catalog of the schema. -/
example : (Sql.pure 1 succeeds on shop) = Succeeds (Sql.pure 1) (·.HasCatalog shop) := rfl

/-- Success on a schema with a guard needs both the catalog and the guard. -/
example : (Sql.pure 1 succeeds on shop where sql r"SELECT 1") =
    Succeeds (Sql.pure 1) (fun db => db.HasCatalog shop ∧ Holds (sql r"SELECT 1") db) := rfl

/-- The forms without a premise keep their meaning. -/
example : (Sql.pure 1 succeeds) = Succeeds (Sql.pure 1) (fun _ => True) := rfl
example : (Sql.pure 1 succeeds where sql r"SELECT 1") =
    Succeeds (Sql.pure 1) (fun db => Holds (sql r"SELECT 1") db) := rfl

/--
@ +1:37...62
error: could not synthesize default value for parameter '_query' using tactics
---
@ +1:37...62
error: the script must be one read-only statement: a SELECT, or PRAGMA foreign_keys without a value; remove the other statements, or use Database.run
-/
#guard_msgs (positions := true) in
example : (Sql.pure 1 succeeds where sql r"SELECT 1; SELECT 2") := Succeeds.pure _ _

/--
@ +1:37...62
error: could not synthesize default value for parameter '_query' using tactics
---
@ +1:37...62
error: the script must be one read-only statement: a SELECT, or PRAGMA foreign_keys without a value; remove the other statements, or use Database.run
-/
#guard_msgs (positions := true) in
example : (Sql.pure 1 succeeds where sql r"CREATE TABLE t (x)") := Succeeds.pure _ _

/--
@ +1:45...70
error: could not synthesize default value for parameter '_query' using tactics
---
@ +1:45...70
error: the script must be one read-only statement: a SELECT, or PRAGMA foreign_keys without a value; remove the other statements, or use Database.run
-/
#guard_msgs (positions := true) in
example : (Sql.pure 1 succeeds on shop where sql r"SELECT 1; SELECT 2") := Succeeds.pure _ _
