import Belay

/-! CREATE INDEX success includes preparation, model restrictions and row conflicts.
The universal theorem is consumed without unfolding execution; kernel examples cover
both sides of its exact conditions and the distinct error paths. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- The script that creates the unique index i on column x of table t. -/
def uniqueIndex : Script := sql r"CREATE UNIQUE INDEX i ON t (x)"

/-- A table whose new unique index has no conflicts. -/
def distinctRows : Database := db! r"CREATE TABLE t (x INTEGER); INSERT INTO t VALUES (1), (2)"

/-- A table whose new unique index has a conflicting pair. -/
def duplicateRows : Database := db! r"CREATE TABLE t (x INTEGER); INSERT INTO t VALUES (1), (1)"

/-- The exact conditions of the unique-index statement. -/
abbrev conditions (db : Database) : Prop :=
  CreateIndexConditions runContext db.raw (name! "i") true (name! "t")
    [{ expression := .identifier (name! "x") .none, descending := false }] none

/-- For every database and environment, the index succeeds exactly under its concrete
schema, resolution and uniqueness conditions. Proof sketch: use the statement law. -/
theorem index_conditions (db : Database) (env : Env) :
    (db.run uniqueIndex env).outputs.allOk = true ↔ conditions db :=
  Script.createIndex_allOk_iff rfl db env

/-- The statement-success equivalence retains an arbitrary predicate over databases.
Proof sketch: use the public success law with the parsed statement. -/
theorem universal_index_conditions (predicate : Database → Prop) :
    Succeeds uniqueIndex predicate ↔ ∀ db, predicate db → conditions db :=
  Succeeds.iff_createIndex rfl predicate

/-- The positive condition has explicit witnesses and a kernel-checked body. -/
theorem distinct_conditions : conditions distinctRows := by
  refine ⟨0, { columns := [{ name := name! "x", declaredType := some "INTEGER" }] },
    [{ term := .column 0 }], none, ?_⟩
  decide +kernel

example : (distinctRows.run uniqueIndex).outputs.allOk = true := by decide +kernel
example : (duplicateRows.run uniqueIndex).outputs.allOk = false := by decide +kernel
example : ¬ conditions duplicateRows := by
  intro condition
  have success := (index_conditions duplicateRows Env.default).mpr condition
  exact (by decide +kernel : (duplicateRows.run uniqueIndex).outputs.allOk ≠ true) success

-- A nonunique index accepts the same duplicate rows.
example : (duplicateRows.run (sql r"CREATE INDEX i ON t (x)")).outputs.allOk = true := by decide +kernel

-- A missing table, missing column, and missing filter column are prepare failures.
example : (Database.empty.run uniqueIndex).outputs = [.error 1] := by decide +kernel
example : (distinctRows.run (sql r"CREATE INDEX i ON t (missing)")).outputs = [.error 1] := by decide +kernel
example : (distinctRows.run (sql r"CREATE INDEX i ON t (x) WHERE missing = 1")).outputs = [.error 1] := by decide +kernel

-- A reserved name and a name already used by a table or an index each fail.
example : (distinctRows.run (sql r"CREATE INDEX sqlite_i ON t (x)")).outputs = [.error 1] := by decide +kernel
example : (distinctRows.run (sql r"CREATE INDEX t ON t (x)")).outputs = [.error 1] := by decide +kernel
example : ((db! r"CREATE TABLE t (x); CREATE INDEX i ON t (x)").run uniqueIndex).outputs = [.error 1] := by decide +kernel

-- A trigger of the same name is in a separate namespace and does not block the index.
example : ((db! r"CREATE TABLE t (x); CREATE TRIGGER i AFTER INSERT ON t BEGIN SELECT 1; END;").run
    uniqueIndex).outputs.allOk = true := by decide +kernel

-- Model restrictions also fail success, although they are not errors.
example : (distinctRows.run (sql r"CREATE INDEX i ON t (abs(x))")).outputs.allOk = false := by decide +kernel

-- The filter restricts the key check to selected rows. Repeated NULLs never conflict.
example : ((db! r"CREATE TABLE t (x); INSERT INTO t VALUES (1), (2), (2)").run
    (sql r"CREATE UNIQUE INDEX i ON t (x) WHERE x = 1")).outputs.allOk = true := by decide +kernel
example : ((db! r"CREATE TABLE t (x); INSERT INTO t VALUES (NULL), (NULL)").run
    uniqueIndex).outputs.allOk = true := by decide +kernel

#print axioms index_conditions
#print axioms universal_index_conditions
