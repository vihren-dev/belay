import Belay.Sqlite.Model.Queries.Fixtures.InitialSourceFixtureExamples
import Belay.Sqlite.Model.Queries.Select.SelectResolution

set_option doc.verso true

namespace Belay.Sqlite.Model.TwoStateFixtures

open Resolved Syntax

/-- The resolved query of one source and no columns. -/
def readsFrom (source : Source) : Resolved.Query :=
  { sources := [{ kind := .inner, source, condition := none }], filter := none, aggregate := false, groupBy := [],
    columns := [], names := [], orderBy := [], offset := 0, limit := none }

/-- The sources of the resolved query of a {lit}`SELECT`, or none when the resolution is no query: a prepare
error or a restriction. -/
def sourcesOf : StatementResolution → Option (List Source)
  | .error _ => none
  | .ok (statement, _) => match statement with
    | .query found _ => some (found.sources.map (·.source))
    | .createView .. | .createTable .. | .createIndex .. | .createTrigger .. | .addColumn .. | .rewrite _ | .dropColumn .. | .drop .. | .begin
    | .commit | .rollback | .insert .. | .update .. | .upsert .. | .insertSelect .. | .delete .. | .prepareError _ | .setting .. => none

/-- The sources of a query that reads a column of the one given source, resolved against the current catalog and the
catalog of the given initial database. -/
def resolvedSources (source : Syntax.TableReference) (initial : Database) (column : String := "a")
    (current : Database := currentT) : Option (List Source) :=
  sourcesOf (resolveSelect context current.catalog (subqueryOf [cell column] source) [] (some initial.catalog))

/-- The source {lit}`json_each('[1]')`. -/
def jsonEachOfOne : Syntax.TableReference := { now "json_each" with arguments := some [.string [91, 93]] }

/-- The initial database has the table {lit}`t(a)` and these views: {lit}`v` is {lit}`SELECT a FROM t`, and
{lit}`w` is {lit}`SELECT key FROM json_each('[1]')`. Both bodies write no schema name. -/
def viewsInitial : Database :=
  { catalog := [{ name := name! "t", entry := .table { columns := [col "a"] } },
                { name := name! "v", entry := .view { query := subqueryOf [cell "a"] (now "t") } },
                { name := name! "w", entry := .view { query := subqueryOf [cell "key"] jsonEachOfOne } }],
    rows := [[], [], []] }

/-- A view of the initial database expands in the initial catalog, also when a function call is in the body:
the call {lit}`json_each('[1]')` is no table name, so the expansion does not read it from the initial
database. A view that the initial database lacks is no source. -/
example : (resolvedSources (before "v") viewsInitial).isSome = true := by decide +kernel
-- The kernel does not reduce the function table, so the compiled evaluator checks this one.
#guard (resolvedSources (before "w") viewsInitial "key").isSome
example : resolvedSources (before "x") viewsInitial = none := by decide +kernel

/-- The error text for a three-part column keeps the schema name. -/
example : qualifiedName (some (name! "before")) (name! "t") (name! "a") = Identifier.ofString "before.t.a" := by
  decide +kernel
example : qualifiedName none (name! "t") (name! "a") = Identifier.ofString "t.a" := by decide +kernel

end Belay.Sqlite.Model.TwoStateFixtures
