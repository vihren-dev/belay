import Belay.Sqlite.Model.InitialSourceExamples

set_option doc.verso true

/-! Regression examples for the guards of the initial-database source (ADR 0017, S6): a function call in
the body of an initial view looks up its name in the initial catalog (a pragma function is refused), a three-part column name picks the
source of its schema, and a stored view body never names the initial database. -/

namespace Belay.Sqlite.Model.TwoStateFixtures

open Syntax Resolution.CollationExamples

/-- A current database with {lit}`t(a)` and a view named {lit}`json_each`. SQLite finds no table-valued
function behind that name in the current database for a view of the initial database. -/
def currentJsonEachView : Database :=
  { catalog := [{ name := name! "t", entry := .table { columns := [col "a"] } },
                { name := name! "json_each", entry := .view { query := subqueryOf [cell "a"] (now "t") } }],
    rows := [[], []] }

/-- The reason of a refusal, or none when the statement resolves. -/
def refusalKind : StatementResolution → Option RestrictionKind
  | .error found => some found.kind
  | .ok _ => none

/-- The reason that resolving a query of one source in the given databases is refused, or none. -/
def selectRefusal (source : Syntax.TableReference) (initial current : Database) (column : String) : Option RestrictionKind :=
  refusalKind (resolveSelect context current.catalog (subqueryOf [cell column] source) [] (some initial.catalog))

-- The view {lit}`w` of the initial database calls {lit}`json_each('[1]')`. An initial view of that name is
-- SQLite's error that the name is no function. A current view of that name makes the later resolution of the
-- copy read the wrong catalog, so the model refuses it, and it never answers with the current view.
#guard (resolvedSources (before "w") viewsInitial "key").isSome
#guard (resolvedSources (before "w") viewsInitial "key" currentJsonEachView).isNone
#guard selectRefusal (before "w") viewsInitial currentJsonEachView "key" == some .initialDatabase
#guard (resolvedSources (before "w") { viewsInitial with
    catalog := viewsInitial.catalog ++ [{ name := name! "json_each", entry := .view { query := subqueryOf [cell "a"] (now "t") } }],
    rows := [[], [], [], []] } "key").isNone

/-- The source {lit}`pragma_table_info('t')`. -/
def pragmaTableInfoOfT : Syntax.TableReference := { now "pragma_table_info" with arguments := some [.string [116]] }

/-- The initial database of {lit}`viewsInitial` with a view {lit}`p` over {lit}`pragma_table_info('t')`. SQLite refuses a
view over a pragma function in an attached database (unsafe use of a virtual table). -/
def pragmaViewInitial : Database :=
  { viewsInitial with
    catalog := viewsInitial.catalog ++ [{ name := name! "p", entry := .view { query := subqueryOf [cell "name"] pragmaTableInfoOfT } }],
    rows := viewsInitial.rows ++ [[]] }

-- The model refuses the view instead of reading the current catalog for the pragma rows.
#guard selectRefusal (before "p") pragmaViewInitial currentT "name" == some .initialDatabase

/-- {lit}`SELECT before.t.a, c.a FROM before.t, t AS c`: the three-part name reads the initial {lit}`t`. -/
def threePartQuery : Syntax.Subquery :=
  { subqueryOf [shown (.qualified (name! "t") (name! "a") (some initialSchemaName)), cellOf "c" "a"] (before "t") with
    joins := [{ operator := [], source := now "t" "c", condition := none, usingColumns := none }] }

/-- {lit}`SELECT before.t.a FROM t, before.t`: both tables are named {lit}`t`, and the schema selects the
initial one (native SQLite 3.51.0 gives the rows 1 and 2). Without the schema filter the name is ambiguous. -/
def sameNameQuery : Syntax.Subquery :=
  { subqueryOf [shown (.qualified (name! "t") (name! "a") (some initialSchemaName))] (now "t") with
    joins := [{ operator := [], source := before "t", condition := none, usingColumns := none }] }

example : (stepOutputOf threePartQuery [] initialT).bind rows? = some (ints [[1, 3], [2, 3]]) := by decide +kernel
example : (stepOutputOf sameNameQuery [] initialT).bind rows? = some (ints [[1], [2]]) := by decide +kernel

/-- {lit}`CREATE VIEW v AS …` over a query and its subqueries, in an empty catalog. -/
def createViewRefusal (query : Syntax.Subquery) (subqueries : List Syntax.Subquery := []) : Option RestrictionKind :=
  refusalKind (resolveCreateView [] (name! "v") false { columns := none, query, subqueries })

/-- A stored view body that names {lit}`before.t`, in its source, in a joined source or in a subquery, is
refused with {name}`RestrictionKind.initialDatabase`: SQLite refuses it too. A body with no schema name is
created. -/
example : createViewRefusal (subqueryOf [cell "a"] (before "t")) = some .initialDatabase := by decide +kernel
example : createViewRefusal sameNameQuery = some .initialDatabase := by decide +kernel
example : createViewRefusal (subqueryOf [shown (.subquery 0)] (now "t"))
    [subqueryOf [cell "a"] (before "t")] = some .initialDatabase := by decide +kernel
example : createViewRefusal (subqueryOf [cell "a"] (now "t")) = none := by decide +kernel

end Belay.Sqlite.Model.TwoStateFixtures
