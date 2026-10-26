import Belay
import Belay.Sqlite.SqlModule
import Belay.Sqlite.SqlFileSyntax

open Belay.Sqlite Lean Elab Command

/-! A fixture of `tests/surface_sql_file_forms_test.py`: `sql_file`, its sections and `against`
option, and `sql_module` (`Belay/Sqlite/SqlFileSyntax.lean`, `Belay/Sqlite/SqlModule.lean`) give
the scripts that `sql` gives for the same statements. The option below makes the package root
this folder, so the files of `sql_files/` are read without a Lake workspace. -/

set_option belay.sql.packageRoot "."

/-- A file with comments, a script of two statements, and the Lean arguments `a` and `b`. -/
def schema := sql_file "sql_files/schema.sql"
example (a b : Value) : schema a b =
    (sql "-- schema\nCREATE TABLE t(a INTEGER, b TEXT);\nINSERT INTO t VALUES (:a, $b);\n") a := rfl

-- A repeated parameter is one argument, and `$b` is an argument too: the file has no Lean variable `b`,
-- so the inline script needs the variable to give the same script.
/-- A repeated named parameter is one argument. -/
def repeated := sql_file "sql_files/repeated.sql"
example (a b : Value) : repeated a b = (sql "SELECT :a, :a, $b;\n") a := rfl

-- Text that looks like a marker or tool syntax inside strings and comments is ordinary SQL.
/-- A file whose strings and comments only look like tool syntax. -/
def legal := sql_file "sql_files/legal.sql"
example : legal = sql "SELECT '.mode', 'sqlc.arg(id)' -- .tables\n;\n" := rfl

-- The sections of the two migration conventions select the statements of one direction.
/-- The goose up section. -/
def gooseUp := sql_file "sql_files/goose.sql" (section := "up")
/-- The goose down section. -/
def gooseDown := sql_file "sql_files/goose.sql" (section := "down")
/-- The dbmate up section. -/
def dbmateUp := sql_file "sql_files/dbmate.sql" (section := "up")
example : gooseUp = sql "CREATE TABLE u(x);\n" := rfl
example : gooseDown = sql "DROP TABLE u;\n" := rfl
example : dbmateUp = sql "CREATE TABLE u(x);" := rfl

/-- The database of the files that are checked against it. -/
def shop : Database := db! r"CREATE TABLE users(email TEXT, name TEXT);"

-- A database that knows the tables leaves the script as it is.
/-- A file checked against a database that has its tables. -/
def checked := sql_file "sql_files/checked.sql" (against := shop)
/-- The same file without the database check. -/
def unchecked := sql_file "sql_files/checked.sql"
example : checked = unchecked := rfl
example : checked = sql "INSERT INTO users(email, name) VALUES (:email, :name);\nSELECT name FROM users WHERE email = :email;\n" := rfl

-- View statements in the sections of a migration file, checked against databases that know the table or the view.
/-- The database that already has the view, for the down section. -/
def shopWithView : Database :=
  db! r"CREATE TABLE users(email TEXT, name TEXT); CREATE VIEW active AS SELECT email FROM users;"
/-- The up section creates a view; the database check leaves the script as it is. -/
def viewUp := sql_file "sql_files/views.sql" (section := "up") (against := shop)
/-- The down section drops it. -/
def viewDown := sql_file "sql_files/views.sql" (section := "down") (against := shopWithView)
example : viewUp = sql "CREATE VIEW active AS SELECT email FROM users WHERE name IS NOT NULL;\n" := rfl
example : viewDown = sql "DROP VIEW active;\n" := rfl

-- The statements of a module are definitions named by their markers.
sql_module Queries from "sql_files/queries.sql"

example : Queries.findByEmail = fun email => (sql "SELECT * FROM users WHERE email = :email") email := rfl

-- Checking a module against the database leaves each definition as it was.
sql_module CheckedQueries from "sql_files/queries.sql" (against := shop)
example : CheckedQueries.findByEmail = Queries.findByEmail := rfl
example : CheckedQueries.insertUser = Queries.insertUser := rfl
example : CheckedQueries.last = Queries.last := rfl
example : CheckedQueries.trig = Queries.trig := rfl

-- A marker inside a trigger body, a string or a comment names nothing.
elab "check_module_names" : command => do
  let environment ← getEnv
  for name in [`Queries.findByEmail, `Queries.insertUser, `Queries.trig, `Queries.last] do
    unless environment.contains name do throwError "{name} was not defined"
  for name in [`Queries.notAMarker, `Queries.blockComment, `Queries.nope, `Queries.fake, `Queries.q, `Queries.trailing] do
    if environment.contains name then throwError "{name} came from text that is not a marker"
  let documentation ← findDocString? environment `Queries.findByEmail
  unless documentation == some "Find a user.\nSecond line.\n\nSQL source: sql_files/queries.sql:1:1" do
    throwError "unexpected documentation {documentation}"
  logInfo "module forms passed"

check_module_names
