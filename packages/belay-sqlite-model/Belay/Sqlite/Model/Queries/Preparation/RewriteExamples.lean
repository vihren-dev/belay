import Belay.Sqlite.Model.Queries.Fixtures.Examples
import Belay.Sqlite.Model.Queries.Preparation.TriggerPrograms

set_option doc.verso true

namespace Belay.Sqlite.Model.Resolution.RewriteExamples

open Belay.Sqlite.Model Syntax Resolution.Examples

/-- The context of the examples. -/
def context : ResolveContext := { profile := defaults, mode := .execution }

/-- The paths and names of a trace. -/
def pathsOf (trace : NameTrace) : List (List Nat × Option Identifier) := trace.map fun o => (o.path, o.name)

/-- A SELECT of the expressions from {lit}`t` with the clauses. -/
def selectOf (values : List Expr) (filter : Option Expr := none) (orderBy : List OrderTerm := [])
    (joins : List Join := []) : Subquery :=
  { columns := values.map fun value => .expression value none "", source := some { table := name! "t", alias := none },
    joins, filter, groupBy := [], orderBy, limit := none, offset := none, parent := none }

/-- The name tokens of {lit}`t.a+1`: {lit}`t` is the child 0 of the child 1 of the arithmetic, {lit}`a` the child 1. -/
def tokensOfSum : SourceText :=
  { text := "t.a+1", tokens := [
    { paths := [[1, 0]], start := 0, stop := 1, quote := .none },
    { paths := [[1, 1]], start := 2, stop := 3, quote := .none }] }

end Belay.Sqlite.Model.Resolution.RewriteExamples
