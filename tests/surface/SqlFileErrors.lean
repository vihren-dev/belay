import Belay
import Belay.Sqlite.SqlModule
import Belay.Sqlite.SqlFileSyntax

open Belay.Sqlite

/-! A fixture of `tests/surface_sql_file_forms_test.py`: each refused `sql_file` and `sql_module`
(`Belay/Sqlite/SqlFileSyntax.lean`, `Belay/Sqlite/SqlModule.lean`, `Belay/Sqlite/SqlFileLayout.lean`)
gives exactly one error that names the SQL file, line and column. `#guard_msgs` fails the file when
a message differs or an extra message appears, for instance a second error from a database that
already has one. -/

set_option belay.sql.packageRoot "."

def shop : Database := db! r"CREATE TABLE users(email TEXT, name TEXT);"
-- A database with an error of its own, which the files that use it must not repeat.
/--
error: SQLite's grammar rejects the SQL at this offset; correct the SQL there and run the command again
-/
#guard_msgs in
def brokenShop : Database := db! r"CREATE TABLE users(email TEXT, name;"
sql_module Queries from "sql_files/queries.sql"

-- whole file of a goose migration
/--
error: sql_files/goose.sql:1:1: the file has migration direction markers; select one direction with (section := "up") or (section := "down")
-/
#guard_msgs in
def c1 := sql_file "sql_files/goose.sql"

-- a section of a file without markers
/--
error: sql_files/schema.sql: the file has no migration direction markers; remove the section, or mark the directions with -- +goose Up/Down or -- migrate:up/down
-/
#guard_msgs in
def c2 := sql_file "sql_files/schema.sql" (section := "up")

-- an unknown section
/--
error: sql_files/goose.sql: unknown section "sideways"; use "up" or "down"
-/
#guard_msgs in
def c3 := sql_file "sql_files/goose.sql" (section := "sideways")

-- two conventions
/--
error: sql_files/convention_mix.sql:3:1: the file mixes goose and dbmate direction markers; use one convention
-/
#guard_msgs in
def c5 := sql_file "sql_files/convention_mix.sql" (section := "up")

-- a direction twice
/--
error: sql_files/two_ups.sql:3:1: this migration direction occurs more than once; remove the repeated marker, or keep one marker for each of up and down
-/
#guard_msgs in
def c6 := sql_file "sql_files/two_ups.sql" (section := "up")

-- a missing direction
/--
error: sql_files/only_up.sql: the file has no marker for the requested migration direction; add the missing marker, or select the direction that the file has
-/
#guard_msgs in
def c7 := sql_file "sql_files/only_up.sql" (section := "down")

-- SQL before the first marker
/--
error: sql_files/sql_before_marker.sql:1:1: SQL before the first migration direction marker; only comments may come before it
-/
#guard_msgs in
def c8 := sql_file "sql_files/sql_before_marker.sql" (section := "up")

-- a sqlite3 dot command
/--
error: sql_files/dot.sql:2:3: SQLite's grammar rejects the SQL at this offset; correct the SQL there and run the command again; this is a sqlite3 shell dot command, not SQL; remove it from the file or run it outside the file
-/
#guard_msgs in
def c9 := sql_file "sql_files/dot.sql"

-- sqlc macro syntax
/--
error: sql_files/sqlc.sql:1:36: SQLite's grammar rejects the SQL at this offset; correct the SQL there and run the command again; sqlc.arg is sqlc macro syntax, not SQLite; convert it to a parameter such as :name or @name before use
-/
#guard_msgs in
def c10 := sql_file "sql_files/sqlc.sql"

-- a parameter named two ways
/--
error: sql_files/collision.sql:1:12: the parameters :x and $x both give the Lean name x; rename one of them
-/
#guard_msgs in
def c11 := sql_file "sql_files/collision.sql"

-- a resolution error against the database
/--
error: sql_files/bad_column.sql:1:8: no such column: nmae
-/
#guard_msgs in
def c12 := sql_file "sql_files/bad_column.sql" (against := shop)

-- a database that has an error shows no second error
#guard_msgs in
def c13 := sql_file "sql_files/bad_column.sql" (against := brokenShop)

-- a setting given twice
/--
error: the database is given twice; remove one (against := ...) option
-/
#guard_msgs in
def c14 := sql_file "sql_files/schema.sql" (against := shop) (against := shop)

-- a syntax error of the file
/--
error: sql_files/syntax_error.sql:3:6: SQLite's grammar rejects the SQL at this offset; correct the SQL there and run the command again
-/
#guard_msgs in
def c15 := sql_file "sql_files/syntax_error.sql"

-- a module entry with several statements
/--
error: sql_files/multi.sql:3:1: the entry a has more than one SQL statement; give each statement its own name
-/
#guard_msgs in
sql_module M1 from "sql_files/multi.sql"

-- SQL without a name
/--
error: sql_files/unnamed.sql:1:1: SQL without a name; put a -- name: marker before it
-/
#guard_msgs in
sql_module M2 from "sql_files/unnamed.sql"

-- an entry without SQL
/--
error: sql_files/empty.sql:1:1: the entry a has no SQL statement; add the statement after the marker, or remove the marker
-/
#guard_msgs in
sql_module M3 from "sql_files/empty.sql"

-- a duplicate name
/--
error: sql_files/dup.sql:3:1: the name a is used by more than one entry; rename one of the markers
-/
#guard_msgs in
sql_module M4 from "sql_files/dup.sql"

-- a dotted name
/--
error: sql_files/dotted.sql:1:1: the name a.b is not one Lean identifier; rename it to letters, digits and underscores that start with a letter or underscore
-/
#guard_msgs in
sql_module M5 from "sql_files/dotted.sql"

-- a malformed marker
/--
error: sql_files/malformed.sql:1:1: the name marker "name: a b c" must be -- name: identifier, with an optional :suffix; rewrite the comment in that form
-/
#guard_msgs in
sql_module M6 from "sql_files/malformed.sql"

-- direction markers in a module
/--
error: sql_files/module_with_direction.sql:4:1: a named SQL module cannot have migration direction markers; use sql_file with (section := ...)
-/
#guard_msgs in
sql_module M7 from "sql_files/module_with_direction.sql"

-- a name that is already declared; rename the SQL entry, or choose another module name
/--
error: sql_files/queries.sql:1:1: in statement `findByEmail`: the name Queries.findByEmail is already declared; rename the SQL entry, or choose another module name
-/
#guard_msgs in
sql_module Queries from "sql_files/queries.sql"

-- an entry that does not resolve
/--
error: sql_files/module_bad_column.sql:2:27: in statement `found`: no such column: nmae
-/
#guard_msgs in
sql_module M8 from "sql_files/module_bad_column.sql" (against := shop)

-- a module without entries
#guard_msgs in
sql_module M9 from "sql_files/nothing.sql"

