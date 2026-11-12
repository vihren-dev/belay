import Belay.Sqlite.Model.Schema.Dispatch.JoinExamples
import Belay.Sqlite.Model.Queries.Select.CollationExamples
import Belay.Sqlite.Model.Schema.Dispatch.SqlAdvance

set_option doc.verso true

/-! Examples of collations (ADR 0014, slice 3), checked by {lit}`#guard` when the package
builds: the comparisons of {lit}`NOCASE` and {lit}`RTRIM`; the collation that resolution
gives a comparison, an {lit}`ORDER BY` and a {lit}`GROUP BY` term, {lit}`min` and {lit}`max`,
an index term and a {lit}`USING` equality; a {lit}`NOCASE` key; and SQLite's prepare error
for an unknown name. The authored corpus of collations compares the same rules with
SQLite. -/

namespace Belay.Sqlite.Model.Resolution.CollationExamples

open Belay.Sqlite.Model Syntax Resolution.Examples Resolution.JoinExamples

/-- The schema of the examples: {name}`tableC`, {name}`tableW`, {name}`tableU` and
{lit}`v(k TEXT)`. A CREATE TABLE with a constraint, also COLLATE, that runs in a script is
a model restriction. -/
def tables : Catalog := catalogOf (schema [tableC, tableW, tableU, .createTable (name! "v") [column (name! "k")] []])

/-- The result rows of the last statement of a script that ends with a query, run from
{name}`tables` without rows; none when the script is restricted, an earlier statement
fails, or the last statement is no query. -/
def outputs (script : List Syntax.Statement) : Option (List (List Value)) :=
  match migration tables script with
  | .resolved resolved _ =>
    match resolved.getLast?, runSql (bindValues resolved.dropLast []) tables.emptyDatabase with
    | some (.query query subqueries), .success database => (query.runOn 0 {} [] database subqueries).map (·.2.rows)
    | some (.query ..), .failure .. | some (.query ..), .pending .. => none
    | some (.createTable ..), _ | some (.createView ..), _ | some (.createIndex ..), _ | some (.createTrigger ..), _ | some (.addColumn ..), _ | some (.rewrite _), _ | some (.dropColumn ..), _ | some (.drop ..), _ | some (.setting ..), _ | some .begin, _
    | some .commit, _ | some .rollback, _ | some (.insert ..), _ | some (.upsert ..), _ | some (.insertSelect ..), _ | some (.update ..), _
    | some (.delete ..), _ | some (.prepareError _), _ | none, _ => none
  | .restricted _ => none

/-- The rows of {lit}`SELECT b FROM c WHERE condition` over {name}`filledC`. -/
def whereC (condition : Expr) : Option (List (List Value)) :=
  outputs (filledC ++ [selectFrom (name! "c") [shown (ref (name! "b"))] (some condition)])

-- A comparison with a NOCASE column on the left, or on the right of a literal, folds case.
#guard whereC (.compare .eq (ref (name! "n")) (.string [97])) == some [[.text [97]], [.text [97]]]
#guard whereC (.compare .eq (.string [97]) (ref (name! "n"))) == some [[.text [97]], [.text [97]]]
-- A column on the left decides, also a BINARY one: b = n compares bytes.
#guard whereC (.compare .eq (ref (name! "b")) (ref (name! "n"))) == some [[.text [97]], [.text [66]]]
-- An explicit COLLATE decides before any column, also on the right; the left one first.
#guard whereC (.compare .eq (ref (name! "b")) (.collate (ref (name! "n")) (name! "nocase"))) ==
  some [[.text [97]], [.text [66]], [.text [97]]]
#guard whereC (.compare .eq (.collate (ref (name! "b")) (name! "nocase")) (ref (name! "n"))) ==
  some [[.text [97]], [.text [66]], [.text [97]]]
#guard whereC (.compare .eq (.collate (ref (name! "n")) (name! "binary")) (.collate (ref (name! "b")) (name! "nocase"))) ==
  some [[.text [97]], [.text [66]]]
-- COLLATE passes through unary plus: +n compares as n.
#guard whereC (.compare .eq (.positive (ref (name! "n"))) (.string [97])) == some [[.text [97]], [.text [97]]]
-- RTRIM: 'a ' = 'a'.
#guard whereC (.compare .eq (ref (name! "r")) (.string [97])) == some [[.text [97]], [.text [97]]]

-- ORDER BY a NOCASE column: 'a' and 'A' tie and keep their order, then 'B'; COLLATE BINARY orders bytes.
#guard outputs (filledC ++ [selectFrom (name! "c") [shown (ref (name! "n"))] (orderBy := [key (name! "n")])]) ==
  some [[.text [97]], [.text [65]], [.text [66]]]
#guard outputs (filledC ++ [selectFrom (name! "c") [shown (ref (name! "n"))]
    (orderBy := [{ expression := .collate (ref (name! "n")) (name! "binary"), descending := false }])]) ==
  some [[.text [65]], [.text [66]], [.text [97]]]
-- GROUP BY a NOCASE column puts 'a' and 'A' in one group.
#guard outputs (filledC ++ [selectFrom (name! "c") [shown (.callStar "count")] (groupBy := [ref (name! "n")])]) ==
  some [[.integer 2], [.integer 1]]
-- GROUP BY a column under one COLLATE groups under it, also in the kernel; under a second
-- COLLATE, the outer one decides.
example : outputs (filledC ++ [selectFrom (name! "c") [shown (.callStar "count")]
    (groupBy := [.collate (ref (name! "b")) (name! "nocase")])]) = some [[.integer 2], [.integer 1]] := by
  decide +kernel
#guard outputs (filledC ++ [selectFrom (name! "c") [shown (.callStar "count")]
    (groupBy := [.collate (.collate (ref (name! "n")) (name! "nocase")) (name! "binary")])]) ==
  some [[.integer 1], [.integer 1], [.integer 1]]
-- min and max compare under the operand's collation; a tie keeps the earlier value.
#guard outputs (filledC ++ [selectFrom (name! "c") [shown (.call "min" [ref (name! "n")]), shown (.call "max" [ref (name! "n")]),
    shown (.call "max" [ref (name! "b")])]]) ==
  some [[.text [97], .text [66], .text [97]]]

/-- The position and reason of a failure of a script from {name}`tables` without rows, or
none. -/
def failureOf (script : List Syntax.Statement) : Option (Nat × ExecutionError) :=
  match migration tables script with
  | .resolved resolved _ => match runSql (bindValues resolved []) tables.emptyDatabase with
    | .failure position reason _ => some (position, reason)
    | .success _ | .pending .. => none
  | .restricted _ => none

-- A NOCASE UNIQUE column refuses 'A' after 'a'; a unique index under COLLATE NOCASE does too.
#guard failureOf [insertText (name! "u") [[97]], insertText (name! "u") [[65]]] == some (1, .constraintViolation)
#guard failureOf [.createIndex (name! "vk") true (name! "v") [{ expression := .collate (ref (name! "k")) (name! "NOCASE"), descending := false }] none,
  insertText (name! "v") [[97]], insertText (name! "v") [[65]]] == some (2, .constraintViolation)
#guard failureOf [.createIndex (name! "vk") true (name! "v") [key (name! "k")] none,
  insertText (name! "v") [[97]], insertText (name! "v") [[65]]] == none

/-- The keys of the index of the last statement of a script, or none. -/
def indexKeys (script : List Syntax.Statement) : Option (List IndexKey) :=
  match (statements (migration tables script)).getLast? with
  | some (.createIndex _ _ index) => some index.keys
  | some (.createTable ..) | some (.createView ..) | some (.createTrigger ..) | some (.addColumn ..) | some (.rewrite _) | some (.dropColumn ..) | some (.drop ..) | some (.setting ..) | some .begin | some .commit | some .rollback | some (.insert ..)
  | some (.upsert ..) | some (.insertSelect ..) | some (.update ..) | some (.delete ..) | some (.query ..) | some (.prepareError _) | none => none

-- An index term has an explicit collation, else its column's.
#guard indexKeys [.createIndex (name! "i") false (name! "c")
    [key (name! "n"), { expression := .collate (ref (name! "n")) (name! "rtrim"), descending := false }, key (name! "b")] none] ==
  some [{ term := .column 0, collation := .nocase }, { term := .column 0, collation := .rtrim }, { term := .column 2 }]

-- USING compares under the collation of the left column: c.n is NOCASE, c.b is BINARY.
#guard outputs (filledC ++ [selectFrom (name! "c") [shown (.callStar "count")] (joins := [{ joined [] (table (name! "w")) with usingColumns := some [name! "n"] }])]) ==
  some [[.integer 2]]
#guard outputs (filledC ++ [selectFrom (name! "w") [shown (.callStar "count")] (joins := [{ joined [] (table (name! "c")) with usingColumns := some [name! "n"] }])]) ==
  some [[.integer 1]]

-- An unknown collation name is SQLite's prepare error in a column definition and in an index
-- term, after the names of the term.
#guard statements (schema [.createTable (name! "x") [collated (name! "a") (name! "foo")] []]) ==
  [.prepareError (.expression (.noSuchCollation (name! "foo")))]
#guard (statements (migration tables [.createIndex (name! "i") false (name! "c")
    [{ expression := .collate (ref (name! "n")) (name! "foo"), descending := false }] none])) ==
  [.prepareError (.expression (.noSuchCollation (name! "foo")))]
#guard (statements (migration tables [.createIndex (name! "i") false (name! "c")
    [{ expression := .collate (ref (name! "zz")) (name! "foo"), descending := false }] none])) ==
  [.prepareError (.expression (.noSuchColumn (name! "zz")))]

-- In any other expression it is a model restriction: SQLite looks it up only where it uses the
-- collation, which its query planner decides in part.
#guard reason (migration tables [selectFrom (name! "c") [shown (.collate (ref (name! "n")) (name! "foo"))]]) ==
  RestrictionKind.unknownCollation.message
-- Also on a number or an alias under COLLATE in GROUP BY.
#guard reason (migration tables [selectFrom (name! "c") [shown (ref (name! "n"))]
    (groupBy := [.collate (.numeric "1") (name! "foo")])]) == RestrictionKind.unknownCollation.message
#guard reason (migration tables [selectFrom (name! "c") [.expression (ref (name! "n")) (some (name! "k")) "n"]
    (groupBy := [.collate (ref (name! "k")) (name! "foo")])]) == RestrictionKind.unknownCollation.message

end Belay.Sqlite.Model.Resolution.CollationExamples
