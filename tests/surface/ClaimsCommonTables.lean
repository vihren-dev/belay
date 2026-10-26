import Belay

set_option doc.verso true

/-! Public SQL and database quotations for ordinary CTEs. Each example checks the
model through the kernel, including per-use scope and writes whose values use a CTE. -/

open Belay.Sqlite

/-- A text column with NOCASE comparison and two distinct row values. -/
def commonTableRows : Database := db! r"
  CREATE TABLE t(x TEXT COLLATE NOCASE);
  INSERT INTO t VALUES ('a'), ('b');"

/-- Explicit CTE column names preserve their source affinity and collation. -/
example : Holds (sql r"WITH c(y) AS (SELECT x FROM t) SELECT 1 FROM c WHERE y = 'A'")
    commonTableRows := by decide +kernel

/-- Forward definitions and repeated references use the same query-source semantics. -/
example : Holds (sql r"WITH a AS (SELECT * FROM b), b(x) AS (SELECT 3)
    SELECT 1 FROM a l JOIN a r ON l.x = r.x WHERE l.x = 3") commonTableRows := by decide +kernel

/-- Nested WITH names shadow the containing WITH name. -/
example : Holds (sql r"WITH a(x) AS (SELECT 1)
    SELECT 1 WHERE (WITH a(x) AS (SELECT 2) SELECT x FROM a) = 2") commonTableRows := by decide +kernel

/-- An unused missing source and invalid column count are not prepared. -/
example : Holds (sql r"WITH unused(x,y) AS (SELECT * FROM missing) SELECT 1")
    commonTableRows := by decide +kernel

/-- A CTE copy reads the enclosing query of its use. -/
example : Holds (sql r"WITH c AS (SELECT x) SELECT 1 FROM t
    WHERE (SELECT * FROM c) = 'a'") commonTableRows := by decide +kernel

/-- A CTE source cannot read a sibling source as a lateral reference. -/
example : Fails (sql r"WITH c AS (SELECT t.x) SELECT 1 FROM t,c")
    commonTableRows := by decide +kernel

/-- An ordinary circular definition remains a SQLite preparation error. -/
example : Fails (sql r"WITH c AS (SELECT * FROM c) SELECT * FROM c")
    commonTableRows := by decide +kernel

/-- Explicit output names must match the number of produced columns when used. -/
example : Fails (sql r"WITH c(x,y) AS (SELECT 1) SELECT * FROM c")
    commonTableRows := by decide +kernel

/-- SQLite accepts empty argument parentheses on a recursive table reference; the model
refuses recursion rather than claiming that the valid query has a preparation error. -/
example : ¬ Fails (sql r"WITH c(x) AS (SELECT 1 UNION ALL
    SELECT x+1 FROM c() WHERE x<3) SELECT * FROM c") commonTableRows := by decide +kernel

/-- WITH works with each supported write family through its ordinary scalar queries. -/
def commonTableWrites : Database := db! r"
  CREATE TABLE t(x INTEGER);
  WITH c AS (SELECT 1) INSERT INTO t VALUES ((SELECT * FROM c));
  WITH c AS (SELECT 2) UPDATE t SET x = (SELECT * FROM c);
  WITH c AS (SELECT 3) DELETE FROM t WHERE x = (SELECT * FROM c);"

/-- The INSERT and UPDATE changed the row; DELETE with the other CTE value kept it. -/
example : Holds (sql r"SELECT 1 FROM t WHERE x = 2") commonTableWrites := by decide +kernel

/-- A trigger body can prepare a CTE that reads its NEW row through a scalar query. -/
def commonTableTrigger : Database := db! r"
  CREATE TABLE source(x INTEGER); CREATE TABLE target(x INTEGER);
  CREATE TRIGGER copied AFTER INSERT ON source BEGIN
    INSERT INTO target VALUES ((WITH c(x) AS (SELECT new.x) SELECT x FROM c));
  END;"

/-- The outer write that fires the trigger. -/
def commonTableTriggerInsert : Script := sql r"INSERT INTO source VALUES (7)"

/-- CTE expansion permits preparation of the trigger body and its outer INSERT. -/
example : (match Model.resolveStatement runContext commonTableTrigger.raw.connection.resolveState
    commonTableTriggerInsert.statements[0].1 with
  | .ok (.insert .., _) => true
  | .error _ | .ok (.createTable .., _) | .ok (.createView .., _) | .ok (.createIndex .., _) | .ok (.createTrigger .., _)
  | .ok (.addColumn .., _) | .ok (.drop .., _) | .ok (.begin, _) | .ok (.commit, _)
  | .ok (.rollback, _) | .ok (.update .., _) | .ok (.upsert .., _) | .ok (.delete .., _)
  | .ok (.prepareError .., _) | .ok (.query .., _) | .ok (.setting .., _) => false) = true := by decide +kernel

/-- Execution retains keyReady's existing restriction on nested writes with subqueries;
successful preparation does not turn this stop into a SQLite error or a successful write. -/
example : (match Model.runScriptStep runContext none 0 commonTableTrigger.raw.connection
    commonTableTriggerInsert.statements[0].1 [] with
  | .ended _ => true
  | .continued _ _ _ => false) = true := by decide +kernel
