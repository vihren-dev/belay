import Belay

/-! A fixture of `tests/surface_guide_test.py`: `sql r"..."` (`Belay/Sqlite/SqlTerm.lean`) shows
an error at its position in the SQL text, with columns from 0: a grammar error at `FORM` (line
11, column 42); in a raw string with `#`, a grammar error at `t`, after the alias `FORM` (line
12, column 49); in a raw string with three `#`, at `FORM` (line 13, column 49); and a statement
that the translation refuses, at the statement (line 14, column 30). -/

open Belay.Sqlite

def plainError : Script := sql r"SELECT * FORM t"
def hashError : Script := sql r#"SELECT "a" FORM t"#
def threeHashError : Script := sql r###"SELECT * FORM t"###
def refused : Script := sql r"VACUUM"
