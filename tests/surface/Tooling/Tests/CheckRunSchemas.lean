import Belay

open Belay.Sqlite Lean Elab

/-! Schemas that are the database at the end of a run of SQL text (issue #371): {lit}`#sql_check`
finds a replayable counterexample on such a schema ({lit}`Belay.Sqlite.Check.schemaText?`), with
{lit}`with (schema := ...)` and with the {lit}`on` form of a migration claim. A schema without SQL
text gives a replay from its catalog. Each replay must build the index on its schema. The test is {lit}`tests/surface_check_run_schemas_test.py`. -/

/-- Mark the message of one command, so the test reads each block. -/
elab "labelled_sql " label:str " in " cmd:command : command => do
  logInfo m!"SQL-COMMAND-BEGIN {label.getString}"
  Command.elabCommand cmd
  logInfo m!"SQL-COMMAND-END {label.getString}:"

set_option belay.sql.packageRoot "."

/-- The schema of a run of an SQL file on the empty database. -/
def fromFile : Database := (Database.empty.run (sql_file "sql_files/customers.sql")).db

/-- A {lit}`db!` schema, then a run of SQL text that adds an index. -/
def fromTwoRuns : Database :=
  ((db! r"CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);").run
    (sql r"CREATE INDEX customers_by_email ON customers(email);")).db

/-- A first run whose text ends with a comment and no semicolon, then a run that adds an index. The text of
the schema separates the two texts, so the last statement of the first text ends. -/
def fromUnterminated : Database :=
  ((Database.empty.run (sql r"CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL)
    -- no semicolon")).db.run (sql r"CREATE INDEX customers_by_email ON customers(email);")).db

/-- The schema of {name}`fromTwoRuns` after a run of a Lean program, which has no SQL text. -/
def withoutText : Database := (fromTwoRuns.run (Sql.pure ())).db

/-- A migration that adds a column, which changes the rows of {name}`allCustomers`. -/
def addEmailLower : Script := sql r"
ALTER TABLE customers ADD COLUMN email_lower TEXT;
UPDATE customers SET email_lower = lower(email);"

/-- Every row of the table. -/
def allCustomers : Script := sql r"SELECT * FROM customers"

labelled_sql "file-schema" in
#sql_check addEmailLower preserves allCustomers with (schema := fromFile)

labelled_sql "file-on" in
#sql_check addEmailLower preserves allCustomers on fromFile

labelled_sql "two-runs-on" in
#sql_check addEmailLower preserves allCustomers on fromTwoRuns

labelled_sql "unterminated-on" in
#sql_check addEmailLower preserves allCustomers on fromUnterminated

labelled_sql "without-text" in
#sql_check addEmailLower preserves allCustomers on withoutText


/-- A computed schema with an object name whose bytes cannot appear in SQL text. -/
def unprintable : Database :=
  let source := (db! "CREATE TABLE customers(id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL); CREATE TABLE extra(n);").raw
  ⟨{ source with catalog := source.catalog.map fun object =>
      if object.name == name! "extra" then { object with name := Model.Identifier.ofBytes [255] } else object },
    by decide +kernel⟩

labelled_sql "unprintable" in
#sql_check addEmailLower preserves allCustomers on unprintable

/-- A computed schema with each catalog entry and constraints whose formatting needs a row scope. -/
def complex : Database := db! r"
CREATE TABLE parents(id INTEGER PRIMARY KEY);
CREATE TABLE items(id INTEGER PRIMARY KEY, parent INTEGER REFERENCES parents(id),
  v INTEGER NOT NULL DEFAULT 4 CHECK(v > 0), doubled INTEGER GENERATED ALWAYS AS (v * 2) STORED,
  CONSTRAINT item_pair UNIQUE(parent,v)) STRICT;
INSERT INTO parents VALUES (1);
INSERT INTO items(id,parent,v) VALUES (2,1,3);
CREATE UNIQUE INDEX active_pair ON items(parent, v DESC) WHERE v > 1;
CREATE VIEW forward AS SELECT label FROM summary;
CREATE VIEW summary(label) AS SELECT doubled FROM items WHERE parent IN (SELECT id FROM parents);
CREATE VIEW via_cte AS WITH local AS (SELECT label FROM forward) SELECT * FROM local;
CREATE TRIGGER copy_parent AFTER INSERT ON items WHEN NEW.parent IS NOT NULL
  BEGIN INSERT INTO parents(id) VALUES (NEW.parent) ON CONFLICT(id) DO NOTHING; END;"

/- Check the same catalog equality that protects a public SQL replay after parsing the emitted text. -/
run_meta do
  let some text := Replay.databaseSql complex | throwError "no SQL for the compound catalog"
  let statements ← match ← Replay.translated text with
    | .ok statements => pure statements
    | .error reason => throwError "could not translate the printed SQL: {reason}\n{text}"
  logInfo m!"CATALOG-SQL {Json.compress (toJson text)}"
  unless Check.constructionMatches (statements.toList.map (·.statement.value)) complex.raw do
    throwError "the printed SQL did not reproduce the compound catalog: {text}"


/-- Even a quoted column rename that leaves no application-visible constraint changes later DDL diagnostics. -/
def renamedCatalog := ((db! "CREATE TABLE t(old INTEGER);").run (sql "ALTER TABLE t RENAME COLUMN old TO [new];")).db

/- Require equality including the spelling flags changed by the rename. -/
run_meta do
  let some text := Replay.databaseSql renamedCatalog | throwError "no SQL for the renamed table"
  let .ok statements ← Replay.translated text | throwError "could not translate the renamed table: {text}"
  unless Check.constructionMatches (statements.toList.map (·.statement.value)) renamedCatalog.raw do
    throwError "the printed SQL did not reproduce the rename: {text}"

/-- Only rowid 2 survives. An ordinary INSERT into the empty table would assign rowid 1. -/
def sparseRows : Database := db! r"
CREATE TABLE sparse(v INTEGER); INSERT INTO sparse VALUES (1), (2); DELETE FROM sparse WHERE v = 1;"

/- A printable schema and row value still need exact rowid reconstruction before replay. -/
run_meta do
  let some text := Replay.databaseSql sparseRows | throwError "missing candidate for ordinary rows"
  let .ok statements ← Replay.translated text | throwError "could not translate the sparse-row candidate"
  if Check.constructionMatches (statements.toList.map (·.statement.value)) sparseRows.raw then
    throwError "the construction lost a hidden rowid"
