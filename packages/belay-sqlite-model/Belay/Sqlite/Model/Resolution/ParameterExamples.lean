import Belay.Sqlite.Model.Resolution.Examples

set_option doc.verso true

/-! Examples of parameters (ADR 0019, D1), checked by {lit}`#guard` when the package builds:
each parameter is evaluated over the values of its statement; it has no affinity and no
collation; it is never a result column number; resolution does not compute it; and SQLite's
prepare errors where a parameter is prohibited. The values are those of native SQLite 3.51.0
over the table {lit}`t(i INTEGER, s TEXT)` with the row {lit}`(1, '1')`. -/

namespace Belay.Sqlite.Model.Resolution.ParameterExamples

open Belay.Sqlite.Model Syntax Resolution.Examples

/-- A catalog with {lit}`t(i INTEGER, s TEXT)` at position 0. -/
def catalog : Catalog := catalogOf (migration [] [.createTable (name! "t") [column (name! "i") (some "INTEGER"), column (name! "s")] []])

/-- The row of the examples. -/
def row : List Value := [.integer 1, .text [49]]

/-- A name as written, without quotes. -/
def col (text : String) : Expr := .identifier (Identifier.ofString text) .none

/-- The table {lit}`t` in {lit}`FROM`. -/
def fromT : Option TableReference := some { table := name! "t", alias := none }

/-- The resolved query of {lit}`SELECT expression FROM t` with the {lit}`GROUP BY` and
{lit}`ORDER BY` terms, or none. -/
def queryOf (expression : Expr) (groupBy : List Expr := []) (orderBy : List OrderTerm := []) : Option Resolved.Query :=
  match (statements (migration catalog [.select [.expression expression none "e"] fromT [] none groupBy orderBy none none])).head? with
  | some (.query query _) => some query
  | some (.createTable ..) | some (.createIndex ..) | some (.createTrigger ..) | some (.addColumn ..) | some (.drop ..)
  | some .begin | some .commit | some .rollback | some (.insert ..) | some (.update ..) | some (.upsert ..)
  | some (.delete ..) | some (.prepareError _) | some (.setting _) | none => none

/-- The value of an expression in {lit}`SELECT expression FROM t` over the row, with the values
bound to its parameters, or none when the query does not resolve to one scalar column. -/
def valueOf (expression : Expr) (values : List Value) : Option Value :=
  match (queryOf expression).map Resolved.Query.columns with
  | some [.scalar resolved] => some (resolved.eval { Resolved.EvalContext.plain 0 with parameters := values } row)
  | some _ | none => none

-- A parameter reads item N of the values, from 1; a number without an item is NULL.
#guard [valueOf (.parameter 2) [.integer 4, .integer 5], valueOf (.parameter 3) [.integer 4], valueOf (.parameter 1) []] ==
  [some (.integer 5), some .null, some .null]
-- No affinity: ?1 = '2' is 0 for the integer 2, as 2 = '2' is.
#guard valueOf (.compare .eq (.parameter 1) (.string [50])) [.integer 2] == some (.integer 0)
-- The column's affinity applies to the value, as to a literal: i = ?1 is 1 for the text '1',
-- and s = ?1 is 1 for the integer 1.
#guard [valueOf (.compare .eq (col "i") (.parameter 1)) [.text [49]], valueOf (.compare .eq (col "s") (.parameter 1)) [.integer 1]] ==
  [some (.integer 1), some (.integer 1)]

-- ORDER BY ?1 sorts by the value, not by a result column: ORDER BY 1 names the first column.
#guard (queryOf (col "i") [] [{ expression := .parameter 1, descending := false }]).map (·.orderBy.map (·.key)) ==
  some [.expression (.parameter 1)]
#guard (queryOf (col "i") [] [{ expression := .numeric "1", descending := false }]).map (·.orderBy.map (·.key)) ==
  some [.output 0]
-- GROUP BY ?1 groups by the value.
#guard (queryOf (.callStar "count") [.parameter 1]).map (·.groupBy.map (·.1)) == some [.parameter 1]

/-- The last resolved statement of the script over {name}`catalog`. -/
def last (script : List Syntax.Statement) : Option Resolved.Statement := (statements (migration catalog script)).getLast?

/-- The prepare error of the last statement of the script over {name}`catalog`, or none. -/
def errorOf (script : List Syntax.Statement) : Option PrepareError :=
  (last script).bind Resolved.Statement.prepareError?

-- Resolution keeps a parameter in a VALUES cell and in a SET value: it does not compute it.
#guard last [.insert (name! "t") none [[.parameter 1, .numeric "2"]] []] matches
  some (.insert _ [[.expression (.parameter 1), .value (.text [50])]] ..)
#guard last [.update (name! "t") [(name! "s", .parameter 1)] none] matches some (.update _ [(1, .parameter 1)] ..)

-- SQLite's prepare errors of a parameter in a definition. SQLite gives them in the order of
-- its name walk: a name that does not resolve before the parameter comes first, and a name
-- after it or a non-deterministic function before it comes later.
#guard errorOf [.createTable (name! "c") [constrained (.check (.compare .gt (col "nosuch") (.parameter 1)) "?")] []] ==
  some (.expression (.noSuchColumn (name! "nosuch")))
#guard [errorOf [.createTable (name! "c") [constrained (.check (.compare .gt (.parameter 1) (col "nosuch")) "?")] []],
    errorOf [.createTable (name! "c") [constrained (.check (.compare .gt (.call "random" []) (.parameter 1)) "?")] []]] ==
  [some (.expression .parameterInCheck), some (.expression .parameterInCheck)]
#guard errorOf [.createTable (name! "g") [column (name! "b"),
    constrained (.generated (.arithmetic .add (col "b") (.parameter 1)) none)] []] ==
  some (.expression .parameterInGenerated)
/-- The prepare error of {lit}`CREATE TABLE c(a CHECK (condition))`, or none. -/
def checkError (condition : Expr) : Option PrepareError :=
  errorOf [.createTable (name! "c") [constrained (.check condition "?")] []]

/-- The error of a missing name {lit}`nosuch`. -/
def missingName : Option PrepareError := some (.expression (.noSuchColumn (name! "nosuch")))

/-- The error of a parameter in a CHECK constraint. -/
def checkParameter : Option PrepareError := some (.expression .parameterInCheck)

-- The last error of SQLite's walk wins, and a function's argument list or the operand of
-- ISNULL does not stop the walk: abs(1, 2) + nosuch + ?1 and (?1 ISNULL) + nosuch give the
-- name, abs(nosuch) + ?1 the parameter. ?1 IS nosuch resolves the name first; ?1 LIKE nosuch
-- is like(nosuch, ?1); nosuch IN () has no operand.
#guard [checkError (.arithmetic .add (.arithmetic .add (.call "abs" [.numeric "1", .numeric "2"]) (col "nosuch")) (.parameter 1)),
    checkError (.arithmetic .add (.isNull (.parameter 1) false) (col "nosuch")),
    checkError (.compare .is (.parameter 1) (col "nosuch")),
    checkError (.call "like" [col "nosuch", .parameter 1])] ==
  [missingName, missingName, missingName, missingName]
#guard [checkError (.arithmetic .add (.call "abs" [col "nosuch"]) (.parameter 1)),
    checkError (.compare .is (.parameter 1) (.arithmetic .add (col "nosuch") (.numeric "1"))),
    checkError (.call "like" [.parameter 1, col "nosuch"]),
    checkError (.arithmetic .add (.inList (col "nosuch") [] false) (.parameter 1))] ==
  [checkParameter, checkParameter, checkParameter, checkParameter]

#guard errorOf [.createIndex (name! "x") false (name! "t") [{ expression := .arithmetic .add (col "i") (.parameter 1), descending := false }] none] ==
  some (.expression (.parameterInIndex false))
#guard errorOf [.createIndex (name! "x") false (name! "t") [key (name! "i")] (some (.compare .gt (col "i") (.parameter 1)))] ==
  some (.expression (.parameterInIndex true))
#guard [errorOf [.createIndex (name! "x") false (name! "t") [key (name! "i")] (some (.compare .gt (col "nosuch") (.parameter 1)))],
    errorOf [.createTable (name! "g") [column (name! "b"),
      constrained (.generated (.arithmetic .add (col "nosuch") (.parameter 1)) none)] []]] ==
  [some (.expression (.noSuchColumn (name! "nosuch"))), some (.expression (.noSuchColumn (name! "nosuch")))]
#guard errorOf [.createTable (name! "d") [{ name := (name! "a"), declaredType := none, constraints := [.default (.parameter 1) "?"] }] []] ==
  some (.expression (.defaultNotConstant (name! "a")))
#guard errorOf [.createTrigger (name! "r") false .after .insert (name! "t") none [.select [.expression (.parameter 1) none "?"]
    none [] none [] [] none none]] == some (.expression .triggerVariables)
-- A trigger that exists with IF NOT EXISTS does nothing, before the parameter is checked.
#guard (last [.createTrigger (name! "r") false .after .insert (name! "t") none [.delete (name! "t") none],
    .createTrigger (name! "r") true .after .insert (name! "t") (some (.parameter 1)) [.delete (name! "t") none]]).map
  (· matches .drop []) == some true

end Belay.Sqlite.Model.Resolution.ParameterExamples
