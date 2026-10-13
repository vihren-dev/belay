import Belay.Sqlite.Resolution.Examples

set_option doc.verso true

/-! Examples of the resolution of a {lit}`SELECT` (ADR 0012, slice 1), checked by
{lit}`#guard`: names, result column names, the prepare errors of queries, the
affinity rules of a comparison, and the restrictions of the slice. -/

namespace Belay.Sqlite.Resolution.QueryResolutionExamples

open Belay.Sqlite Syntax Resolution.Examples

/-- A catalog with {lit}`t(Abc INTEGER, b TEXT)` at position 0. -/
def catalog : Catalog :=
  [{ name := "t", entry := .table { columns := [{ name := "Abc", declaredType := some "INTEGER" },
    { name := "b", declaredType := some "TEXT" }] } }]

/-- A {lit}`SELECT` from {lit}`t` with the given parts. -/
def select (columns : List ResultColumn) (filter : Option Expr := none) (groupBy : List Expr := [])
    (orderBy : List OrderTerm := []) (limit offset : Option Expr := none) : Syntax.Statement :=
  .select columns "t" filter groupBy orderBy limit offset

/-- A result column written as an expression without an alias. -/
def written (value : Expr) (text : String) : ResultColumn := .expression value none text

/-- The single statement of a resolution, or a prepare error for a restriction. -/
def resolvedOne (statement : Syntax.Statement) : Option Resolved.Statement :=
  (statements (migration catalog [statement])).head?

/-- The query of a resolution, if it is one. -/
def queryOf (statement : Syntax.Statement) : Option Resolved.Query :=
  match resolvedOne statement with | some (.query query) => some query | _ => none

/-- The prepare error of a resolution, if it is one. -/
def errorOf (statement : Syntax.Statement) : Option PrepareError :=
  match resolvedOne statement with | some (.prepareError error) => some error | _ => none

/-- Whether the statement is a model restriction. -/
def restrictedOne (statement : Syntax.Statement) : Bool := restricted (migration catalog [statement])

-- `*` and a bare column take the defined names; an expression keeps its text.
#guard (queryOf (select [.star])).map (·.names) == some ["Abc", "b"]
#guard (queryOf (select [written (.identifier "ABC" false) "ABC",
  written (.equals (.identifier "abc" false) (.numeric "1")) "abc = 1"])).map (·.names) == some ["Abc", "abc = 1"]
#guard (queryOf (select [.expression .countRows (some "n") "count(*)", written .countRows "count(*)"])).map
  (·.names) == some ["n", "count(*)"]
-- Names that SQLite refuses while it prepares the query.
#guard errorOf (select [written (.identifier "missing" false) "missing"]) == some (.noSuchColumn "missing")
#guard errorOf (.select [.star] "absent" none [] [] none none) == some (.noSuchTable "absent")
#guard errorOf (select [.star] (filter := some (.equals .countRows (.numeric "1")))) ==
  some (.misuseOfAggregate "count")
#guard errorOf (select [written (.aggregate .max (.aggregate .min (.identifier "b" false))) "max(min(b))"]) ==
  some (.misuseOfAggregate "min")
#guard errorOf (select [.star] (orderBy := [{ expression := .numeric "3", descending := false }])) ==
  some (.orderByOutOfRange 1 2)
#guard errorOf (select [written .countRows "count(*)"] (groupBy := [.numeric "1"])) == some .aggregateInGroupBy
-- A double-quoted name that names no column is a string literal.
#guard (queryOf (select [written (.identifier "x" true) "\"x\""])).isSome
-- Comparisons whose affinity rule would convert a value are model restrictions.
#guard restrictedOne (select [.star] (filter := some (.equals (.identifier "b" false) (.numeric "5"))))
#guard restrictedOne (select [.star] (filter := some (.equals (.identifier "Abc" false) (.string [53]))))
#guard restrictedOne (select [.star] (filter := some (.equals (.identifier "Abc" false) (.identifier "b" false))))
#guard (queryOf (select [.star] (filter := some (.equals (.identifier "Abc" false) (.numeric "5"))))).isSome
-- The restrictions of slice 1.
#guard restrictedOne (select [written (.identifier "b" false) "b", written .countRows "count(*)"])
#guard restrictedOne (select [.star] (filter := some (.identifier "Abc" false)))
#guard restrictedOne (select [.star] (offset := some (.negate (.numeric "1"))))
-- A negative LIMIT means no limit; ORDER BY an alias names the result column.
#guard (queryOf (select [.star] (limit := some (.negate (.numeric "1"))))).map (·.limit) == some none
#guard (queryOf (select [.expression (.identifier "b" false) (some "k") "b"]
  (orderBy := [{ expression := .identifier "K" false, descending := true }]))).map (·.orderBy) ==
  some [(.output 0, true)]

end Belay.Sqlite.Resolution.QueryResolutionExamples
