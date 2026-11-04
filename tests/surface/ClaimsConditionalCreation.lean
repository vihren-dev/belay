import Belay

set_option doc.verso true
set_option maxRecDepth 8000
set_option maxHeartbeats 800000

/-! CREATE TABLE and CREATE INDEX with {lit}`IF NOT EXISTS` through SQL and actual execution: the
no-op keeps the database and the counters, the checks before the name check keep their errors,
and with a free name the clause changes nothing. The corpus compares the same cases with native
SQLite. -/

open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

namespace ConditionalCreationExamples

/-- A table with two rows, an index, a view and a trigger exercise the two catalog namespaces. -/
def database : Database := db! r"
  CREATE TABLE MixedT(x INTEGER); INSERT INTO MixedT VALUES(7),(8);
  CREATE INDEX idx ON MixedT(x); CREATE VIEW MixedV AS SELECT x FROM MixedT;
  CREATE TRIGGER tr AFTER INSERT ON MixedT BEGIN SELECT 1; END;"

/-- Each no-op outputs done with zero changes and keeps the database, also when SQLite would
reject the rest of the statement (a duplicate column, an unknown column, an unknown name in the
filter) and when the existing index differs in its terms and uniqueness. -/
theorem no_op_keeps_database : let run := database.run (sql r"
    CREATE TABLE IF NOT EXISTS mixedt(y, y);
    CREATE TABLE IF NOT EXISTS MIXEDV(z);
    CREATE INDEX IF NOT EXISTS IDX ON MixedT(missing);
    CREATE UNIQUE INDEX IF NOT EXISTS idx ON mixedt(x) WHERE nope;
  ")
    run.outputs = [.done 0, .done 0, .done 0, .done 0] ∧ run.db.raw = database.raw := by decide +kernel

/-- A no-op keeps {lit}`changes()`, {lit}`total_changes()` and {lit}`last_insert_rowid()` of an
earlier INSERT. -/
theorem no_op_keeps_counters : (Database.empty.run (sql r"
    CREATE TABLE t(x); CREATE INDEX i ON t(x); INSERT INTO t VALUES(1);
    CREATE TABLE IF NOT EXISTS t(y); CREATE INDEX IF NOT EXISTS i ON t(y);
    SELECT changes(), total_changes(), last_insert_rowid();
  ") Env.newConnection).outputs =
    [.done 0, .done 0, .done 1, .done 0, .done 0, .rows [[.integer 1, .integer 1, .integer 1]]] := by
  decide +kernel

/-- A no-op in a transaction that rolls back leaves the database as it was. -/
theorem no_op_rollback : (database.run (sql r"
    BEGIN; CREATE TABLE IF NOT EXISTS MixedT(a); CREATE TABLE fresh(a); ROLLBACK;
  ")).db.raw = database.raw := by decide +kernel

/-- The other kind of object of the name, a missing or a view target, and a reserved name keep
their errors; a trigger of the name does not stop CREATE TABLE. -/
theorem errors_kept :
    (database.run (sql r"CREATE TABLE IF NOT EXISTS idx(a)")).outputs = [.error 1] ∧
    (database.run (sql r"CREATE INDEX IF NOT EXISTS mixedt ON MixedT(x)")).outputs = [.error 1] ∧
    (database.run (sql r"CREATE INDEX IF NOT EXISTS mixedv ON MixedT(x)")).outputs = [.error 1] ∧
    (database.run (sql r"CREATE INDEX IF NOT EXISTS idx ON missing(x)")).outputs = [.error 1] ∧
    (database.run (sql r"CREATE INDEX IF NOT EXISTS idx ON MixedV(x)")).outputs = [.error 1] ∧
    (database.run (sql r"CREATE TABLE IF NOT EXISTS sqlite_x(a)")).outputs = [.error 1] ∧
    (database.run (sql r"CREATE TABLE IF NOT EXISTS tr(a)")).outputs = [.done 0] := by
  decide +kernel

/-- A free name runs the unique check over existing rows; an existing index of the name does not. -/
theorem unique_over_duplicates : (Database.empty.run (sql r"
    CREATE TABLE d(x); INSERT INTO d VALUES(1),(1); CREATE INDEX u ON d(x);
    CREATE UNIQUE INDEX IF NOT EXISTS u ON d(x); CREATE UNIQUE INDEX IF NOT EXISTS w ON d(x);
  ")).outputs = [.done 0, .done 2, .done 0, .done 0, .error 19] := by decide +kernel

/-- For every connection where no table or view has the name, one step of CREATE TABLE with
the clause is the step without it. Proof sketch: the model step law. -/
theorem free_table {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {name : Identifier} {columns : List Syntax.ColumnDefinition}
    {constraints : List Syntax.TableConstraint} {options : Syntax.TableOptions} {parameters : List Value}
    (free : createTableKept connection.state.database.catalog name = false) :
    runScriptStep context clock index connection (.createTable name columns constraints options true) parameters =
      runScriptStep context clock index connection (.createTable name columns constraints options) parameters :=
  runScriptStep_createTable_ifNotExists_free free

/-- For every database whose catalog has no index of the name, the public run of CREATE INDEX
with the clause succeeds exactly when the index conditions hold. Proof sketch: the public
success law; its no-op case needs an index of the name. -/
theorem free_index (db : Database) (env : Env)
    (free : createIndexKept db.raw.catalog (name! "j") (name! "MixedT") = false) :
    (db.run (sql r"CREATE UNIQUE INDEX IF NOT EXISTS j ON MixedT(x)") env).outputs.allOk = true ↔
      CreateIndexConditions runContext db.raw (name! "j") true (name! "MixedT")
        [{ expression := .identifier (name! "x") .none, descending := false }] none := by
  rw [Script.createIndex_allOk_iff rfl db env]
  simp [free]

#print axioms no_op_keeps_database
#print axioms no_op_keeps_counters
#print axioms no_op_rollback
#print axioms errors_kept
#print axioms unique_over_duplicates
#print axioms free_table
#print axioms free_index

end ConditionalCreationExamples
