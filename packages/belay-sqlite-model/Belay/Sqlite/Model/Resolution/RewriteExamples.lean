import Belay.Sqlite.Model.Resolution.Examples
import Belay.Sqlite.Model.Resolution.RewriteBody
import Belay.Sqlite.Model.Resolution.TriggerPrograms
import Belay.Sqlite.Model.Resolution.TriggerTraceExamples

set_option doc.verso true

/-! Examples that the paths of the name trace lead to the names that they say, checked by {lit}`#guard`
when the package builds: for every occurrence that a rename rewrites (a table, a qualifier, a column of an
expression or of a column list), the rewrite of the object at the path of the occurrence works, and the
trace of the rewritten object has the new name at the same path. -/

namespace Belay.Sqlite.Model.Resolution.RewriteExamples

open Belay.Sqlite.Model Syntax Resolution.Examples

/-- The tables {lit}`t(a, b)` and {lit}`u(x)`. -/
def tables : Catalog := catalogOf (schema [
  .createTable (name! "t") [column (name! "a"), column (name! "b")] [],
  .createTable (name! "u") [column (name! "x")] []])

/-- The context of the examples. -/
def context : ResolveContext := { profile := defaults, mode := .execution }

/-- Whether a rename rewrites the name of the occurrence: a table or a qualifier that is a source, a
column that is found, or the target of a column list. -/
def rewritten (occurrence : NameOccurrence) : Bool :=
  occurrence.name.isSome && occurrence.exact && match occurrence.role, occurrence.result with
    | .tableReference, .source _ | .qualifier, .source _ | .columnReference, .found _ | .columnTarget, .found _ => true
    | _, _ => false

/-- The edit that writes the name {lit}`zz` at the occurrence. -/
def editOf (occurrence : NameOccurrence) : NameEdit :=
  { path := occurrence.path, old := occurrence.name.getD (name! "?"), new := name! "zz", style := .table }

/-- The paths and names of a trace. -/
def pathsOf (trace : NameTrace) : List (List Nat × Option Identifier) := trace.map fun o => (o.path, o.name)

/-- Whether every rewritten occurrence of the SELECT is found at its path, and the trace of the SELECT
rewritten there has the new name at that path. -/
def selectRoundTrips (query : Subquery) (subqueries : List Subquery := []) : Bool :=
  let trace := (resolveSelectTraced context tables query subqueries).trace
  !(trace.filter rewritten).isEmpty && (trace.filter rewritten).all fun occurrence =>
    match renameSelectAt (editOf occurrence) query subqueries with
    | some (query, subqueries) =>
      (pathsOf (resolveSelectTraced context tables query subqueries).trace).contains (occurrence.path, some (name! "zz"))
    | none => false

/-- Whether every rewritten occurrence of the SELECT is found at its path, and the rewrite changes the
SELECT. This is the check for a name whose rewrite makes the resolution fail before the name, such as the
qualifier of {lit}`zz.*`. -/
def selectRewrites (query : Subquery) (subqueries : List Subquery := []) : Bool :=
  let trace := (resolveSelectTraced context tables query subqueries).trace
  !(trace.filter rewritten).isEmpty && (trace.filter rewritten).all fun occurrence =>
    (renameSelectAt (editOf occurrence) query subqueries).any fun (renamed, _) => renamed != query

/-- Whether every rewritten occurrence of the trigger works in the same way. -/
def triggerRoundTrips (trigger : CatalogTrigger) : Bool :=
  let trace := (resolveProgramTraced context tables 2 trigger).trace
  !(trace.filter rewritten).isEmpty && (trace.filter rewritten).all fun occurrence =>
    match trigger.renameAt (editOf occurrence) occurrence.path with
    | some trigger =>
      (pathsOf (resolveProgramTraced context tables 2 trigger).trace).contains (occurrence.path, some (name! "zz"))
    | none => false

/-- {lit}`name`. -/
def ident (text : String) : Expr := .identifier (Identifier.ofString text) .none

/-- {lit}`source.name`. -/
def dotted (source name : String) : Expr := .qualified (Identifier.ofString source) (Identifier.ofString name)

/-- A SELECT of the expressions from {lit}`t` with the clauses. -/
def selectOf (values : List Expr) (filter : Option Expr := none) (orderBy : List OrderTerm := [])
    (joins : List Join := []) : Subquery :=
  { columns := values.map fun value => .expression value none "", source := some { table := name! "t", alias := none },
    joins, filter, groupBy := [], orderBy, limit := none, offset := none, parent := none }

-- The operators and the forms with several operands.
#guard selectRoundTrips (selectOf [.arithmetic .add (dotted "t" "a") (.negate (ident "b")),
  .compare .gt (ident "a") (.positive (dotted "t" "b")), .and (ident "a") (.or (ident "b") (.not (ident "a")))])
#guard selectRoundTrips (selectOf [.isNull (ident "a") true, .cast (ident "b") "TEXT", .collate (ident "a") (name! "nocase"),
  .concatenate (ident "a") (ident "b"), .between (ident "a") (ident "b") (dotted "t" "a") false])
#guard selectRoundTrips (selectOf [.call "abs" [ident "a"], .inList (ident "a") [ident "b", dotted "t" "b"] false,
  .caseOf [ident "a", ident "b", ident "a"] false])
-- The clauses: filter, order, joins with ON, and a source star.
#guard selectRoundTrips (selectOf [ident "a"] (filter := some (.compare .eq (ident "a") (dotted "t" "b")))
  (orderBy := [{ expression := ident "b", descending := false }]))
#guard selectRoundTrips (selectOf [ident "a", dotted "u" "x"]
  (joins := [{ operator := [], source := { table := name! "u", alias := none },
               condition := some (.compare .eq (dotted "t" "a") (dotted "u" "x")), usingColumns := none }]))
#guard selectRewrites { (selectOf []) with columns := [.sourceStar (name! "t")] }

-- A subquery of the statement is below the child 8; its names are in its own query.
#guard selectRoundTrips (selectOf [ident "a"] (filter := some (.inQuery (ident "a") 0 false)))
  [{ columns := [.expression (ident "x") none ""], source := some { table := name! "u", alias := none }, joins := [],
     filter := some (.compare .eq (ident "x") (dotted "t" "a")), groupBy := [], orderBy := [], limit := none,
     offset := none, parent := none }]
-- GROUP BY, HAVING and an aggregate.
/-- {lit}`SELECT a, count(b) FROM t GROUP BY a HAVING a > 0`. -/
def grouped : Subquery :=
  { selectOf [ident "a", .call "count" [ident "b"]] with
    groupBy := [ident "a"], having := some (.compare .gt (ident "a") (.numeric "0")) }

#guard selectRoundTrips grouped

-- The program of a trigger: the condition, an UPDATE, an INSERT and a SELECT in its body, and a raising SELECT.
#guard triggerRoundTrips Resolution.TriggerTraceExamples.trigger
#guard triggerRoundTrips Resolution.TriggerTraceExamples.raising

/-- The name tokens of {lit}`t.a+1`: {lit}`t` is the child 0 of the child 1 of the arithmetic, {lit}`a` the child 1. -/
def tokensOfSum : SourceText :=
  { text := "t.a+1", tokens := [
    { paths := [[1, 0]], start := 0, stop := 1, quote := .none },
    { paths := [[1, 1]], start := 2, stop := 3, quote := .none }] }

/-- The query {lit}`SELECT t.a+1 FROM t` with the tokens of its text. -/
def sumQuery : Subquery :=
  { (selectOf []) with columns := [.expression (.arithmetic .add (dotted "t" "a") (.numeric "1")) none tokensOfSum] }

/-- The text of the first column of the query after the edit, or none when the edit fails. -/
def textAfter (edit : NameEdit) : Option String :=
  (renameSelectAt edit sumQuery []).bind fun (query, _) => match query.columns with
    | [.expression _ _ text] => some text.text
    | _ => none

-- The new name of a table is always in double quotes; of a column as the statement wrote it, when the old
-- name is unquoted; the tokens behind a name move.
#guard textAfter { path := [0, 0, 0, 1, 0], old := name! "t", new := name! "u v", style := .table } == some "\"u v\".a+1"
#guard textAfter { path := [0, 0, 0, 1, 1], old := name! "a", new := name! "b", style := .column false } == some "t.b+1"
#guard textAfter { path := [0, 0, 0, 1, 1], old := name! "a", new := name! "Z z", style := .column true } == some "t.\"Z z\"+1"
-- A path that leads to another name is no edit.
#guard textAfter { path := [0, 0, 0, 1, 1], old := name! "t", new := name! "b", style := .table } == none
#guard (renameSelectAt { path := [0, 0, 0, 2], old := name! "a", new := name! "b", style := .table } sumQuery []).isNone

end Belay.Sqlite.Model.Resolution.RewriteExamples
