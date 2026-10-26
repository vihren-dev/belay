import Lean.Elab.Command
import Belay.Sqlite.SqlDocComments

set_option doc.verso true

namespace SqlDocComments
open Belay.Sqlite.SqlDoc

/-- Check that the final standalone comment group of the text is the expected text. -/
def expect (body expected : String) : Bool := expectedComments body == expected

-- The marker and at most one following space leave the rest of the line intact.
#guard expect "SELECT 1;\n-- 1\n" "1"
#guard expect "SELECT 1;\n--1\n" "1"
#guard expect "SELECT 1;\n--  1\n" " 1"
#guard expect "SELECT 1;\n-- 1  \n" "1  "
#guard expect "SELECT 1;\n---\n" "-"
#guard expect "SELECT 1;\n  \t-- 1\n" "1"
#guard expect "SELECT 1;\n--\n-- 2\n--\n" "\n2\n"
#guard expect "SELECT 1;\n--\n--\n" "\n"

-- Only the last contiguous group counts; blank source lines end the group and trailing ones are ignored.
#guard expect "-- first\nSELECT 1;\n-- 1\n" "1"
#guard expect "SELECT 1;\n-- a\n\n-- b\n" "b"
#guard expect "SELECT 1;\n-- a\n\n\n  \n" "a"
#guard expect "SELECT 1;\n-- a\nSELECT 2;\n" ""
#guard expect "-- a\n" "a"
#guard expect "SELECT 1;\n" ""
#guard expect "" ""
#guard expect "SELECT 1; -- on the statement line\n" ""
#guard expect "SELECT 1; -- x\n-- y\n" "y"

-- Quotes and block comments hide a marker.
#guard expect "SELECT 'a\n-- b\n" ""
#guard expect "SELECT 'it''s\n-- not expected\n" ""
#guard expect "SELECT 'it''s'\n-- expected\n" "expected"
#guard expect "SELECT \"a\n-- b\n" ""
#guard expect "SELECT `a\n-- b\n" ""
#guard expect "SELECT [a\n-- b\n" ""
#guard expect "SELECT 1 /*\n-- hidden\n*/\n" ""
#guard expect "SELECT 1 /*\n-- hidden\n*/\n-- shown\n" "shown"
#guard expect "SELECT 1 /*/\n-- hidden\n*/\n" ""
#guard expect "SELECT 1 /* open\n-- hidden\n" ""
#guard expect "SELECT '-- no';\n-- yes\n" "yes"
#guard expect "SELECT 'a--b' -- c\n-- d\n" "d"

-- A trigger body is lexically ordinary text.
#guard expect "CREATE TRIGGER g AFTER INSERT ON t BEGIN\nSELECT 1;\n-- inside\nEND;\n" ""
#guard expect "CREATE TRIGGER g AFTER INSERT ON t BEGIN\nSELECT 1;\n-- inside\nEND;\n-- outside\n" "outside"

-- Non-BMP characters and carriage returns do not change the extraction.
#guard expect "SELECT '😀';\n-- 😀 é\n" "😀 é"
#guard expect "SELECT 1;\r\n-- a\r\n-- b\r\n" "a\nb"
#guard expect "SELECT 'x\r\n-- hidden\r\n" ""

end SqlDocComments

open Lean Elab Command in
run_cmd logInfo "SQL doc comment checks passed"
