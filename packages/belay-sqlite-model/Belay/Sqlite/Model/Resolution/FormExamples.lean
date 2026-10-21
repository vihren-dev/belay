import Belay.Sqlite.Model.Resolution.Examples

set_option doc.verso true

/-! Examples of the expression forms {lit}`IN (values)`, {lit}`BETWEEN`, {lit}`CASE` and
{lit}`||` (ADR 0018, D2), checked by {lit}`#guard`: each form is resolved in a query over one table
and evaluated over its row. The values are those of native SQLite 3.51.0 over the table
{lit}`t(i INTEGER, s TEXT, n TEXT COLLATE NOCASE)` with the row {lit}`(1, '1', 'A')`. -/

namespace Belay.Sqlite.Model.Resolution.FormExamples

open Belay.Sqlite.Model Syntax Resolution.Examples

/-- A catalog with {lit}`t(i INTEGER, s TEXT, n TEXT COLLATE NOCASE)` at position 0. -/
def catalog : Catalog :=
  [{ name := (name! "t"), entry := .table { columns := [{ name := (name! "i"), declaredType := some "INTEGER" },
      { name := (name! "s"), declaredType := some "TEXT" },
      { name := (name! "n"), declaredType := some "TEXT", collation := .nocase }] } }]

/-- The row of the examples. -/
def row : List Value := [.integer 1, .text [49], .text [65]]

/-- A name as written, without quotes. -/
def col (text : String) : Expr := .identifier (Identifier.ofString text) .none

/-- A string literal of ASCII text. -/
def str (text : String) : Expr := .string text.toUTF8.toList

/-- {lit}`value COLLATE BINARY`. -/
def binary (value : Expr) : Expr := .collate value (Identifier.ofString "BINARY")

/-- The value of an expression in {lit}`SELECT expression FROM t` over the row, or none when the
query does not resolve to one scalar column. -/
def valueOf (expression : Expr) : Option Value :=
  match (statements (migration catalog [.select [.expression expression none "e"]
      (some { table := Identifier.ofString "t", alias := none }) [] none [] [] none none])).head? with
  | some (.query { columns := [.scalar resolved], .. } _) => some (resolved.eval (.plain 0) row)
  | _ => none

-- An IN list takes the affinity of its left operand only: i IN ('1', 'x') and i IN (s) are 1,
-- '1' IN (i, 'z') is 0.
#guard [valueOf (.inList (col "i") [str "1", str "x"] false), valueOf (.inList (col "i") [col "s"] false),
  valueOf (.inList (str "1") [col "i", str "z"] false)] == [some (.integer 1), some (.integer 1), some (.integer 0)]
-- It compares under the collation of its left operand: n IN ('a', 'b') is 1, 'a' IN (n, 'z') is 0,
-- n IN ('a' COLLATE BINARY, 'b') is 1.
#guard [valueOf (.inList (col "n") [str "a", str "b"] false), valueOf (.inList (str "a") [col "n", str "z"] false),
  valueOf (.inList (col "n") [binary (str "a"), str "b"] false)] == [some (.integer 1), some (.integer 0), some (.integer 1)]
-- One constant value is SQLite's x = +c: n IN ('a' COLLATE BINARY) is 0.
#guard valueOf (.inList (col "n") [binary (str "a")] false) == some (.integer 0)
-- The NULL matrix: 2 IN (1, NULL) is NULL, NULL IN () is 0, i NOT IN () is 1.
#guard [valueOf (.inList (.numeric "2") [.numeric "1", .null] false), valueOf (.inList .null [] false),
  valueOf (.inList (col "i") [] true)] == [some .null, some (.integer 0), some (.integer 1)]
-- BETWEEN applies the rules of >= and <=: i BETWEEN '0' AND '2' is 1, 1 BETWEEN NULL AND 2 is NULL,
-- 3 BETWEEN NULL AND 2 is 0, n BETWEEN 'a' AND 'a' is 1, 2 NOT BETWEEN 1 AND 3 is 0.
#guard [valueOf (.between (col "i") (str "0") (str "2") false), valueOf (.between (.numeric "1") .null (.numeric "2") false),
  valueOf (.between (.numeric "3") .null (.numeric "2") false), valueOf (.between (col "n") (str "a") (str "a") false),
  valueOf (.between (.numeric "2") (.numeric "1") (.numeric "3") true)] ==
  [some (.integer 1), some .null, some (.integer 0), some (.integer 1), some (.integer 0)]
-- CASE with a base compares as =: CASE '1' WHEN i ..., CASE 'a' WHEN n ... match; a NULL base matches nothing.
#guard [valueOf (.caseOf [str "1", col "i", str "y", str "n"] true), valueOf (.caseOf [str "a", col "n", str "y", str "n"] true),
  valueOf (.caseOf [.null, .null, str "y", str "n"] true)] == [some (.text [121]), some (.text [121]), some (.text [110])]
-- CASE without a base takes the first true WHEN; without ELSE and a true WHEN it is NULL.
#guard [valueOf (.caseOf [.numeric "0", .numeric "1", str "x", .numeric "2"] false),
  valueOf (.caseOf [.numeric "0", .numeric "1"] false)] == [some .null, some .null]
-- x || y: NULL with a NULL operand, else the text of both: 1 || 2 is '12', 1.5 || 'a' is '1.5a'.
#guard [valueOf (.concatenate (.numeric "1") (.numeric "2")), valueOf (.concatenate .null (str "a")),
  valueOf (.concatenate (.numeric "1.5") (str "a"))] == [some (.text [49, 50]), some .null, some (.text [49, 46, 53, 97])]
/-- The value of {lit}`1e300 || ''` over the row is the text {lit}`1.0e+300`, SQLite's text of the REAL. -/
theorem concat_large_real : valueOf (.concatenate (.numeric "1e300") (str "")) = some (.text "1.0e+300".toUTF8.toList) := by decide +kernel

end Belay.Sqlite.Model.Resolution.FormExamples
