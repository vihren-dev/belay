import Belay

/-! Success notation keeps the flexible predicate primitive and checks query preconditions
at their own source position, including preconditions with bound Lean values. -/

open Belay.Sqlite

example : (Sql.pure 1 succeeds) := Succeeds.pure _ _
example : (Sql.pure 1 succeeds where sql r"SELECT 1") := Succeeds.pure _ _
example (x : Value) : (Sql.pure x succeeds where sql r"SELECT $x") := Succeeds.pure _ _

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
