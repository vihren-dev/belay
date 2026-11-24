import Belay

set_option doc.verso true

/-! Original observation contracts under ADR 0033. Successful resolution supplies the output evidence. -/

namespace Belay.Sqlite.ReplacedRowPredicates
open Belay.Sqlite.Model

/-- The former {lit}`Holds.iff_query` follows at its original premises. -/
theorem Holds_iff_query {script : Script} {db : Database} {isQuery : script.isQuery = true}
    {statement : Syntax.Statement} {parameters : List Value} {rest : List (Syntax.Statement × List Value)}
    {query bound : Resolved.Query} {subqueries : List Resolved.Query} {after : ResolveState}
    {source : Resolved.SourceRows}
    (head : script.statements = (statement, parameters) :: rest)
    (resolved : resolveStatement runContext db.raw.connection.resolveState statement =
      .ok (.query query subqueries, after))
    (noClock : (Resolved.Statement.query query subqueries).readsClock = false)
    (known : db.raw.connection.state.counters.firstUnknown (Resolved.Statement.query query subqueries).counterReads = none)
    (found : query.source (db.raw.connection.queryContext parameters query subqueries) db.raw = some source)
    (window : query.bindWindow parameters = some bound) :
    Holds script db isQuery ↔
      Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = true ∧ source.fault ≠ .may ∧
        (query.run (db.raw.connection.queryContext parameters query subqueries) source.rows).mismatch = false ∧
        (query.run (db.raw.connection.queryContext parameters query subqueries) source.rows).overflow = false ∧
        (query.run (db.raw.connection.queryContext parameters query subqueries) source.rows).fault = .none ∧
        bound.results (db.raw.connection.queryContext parameters query subqueries) source.rows ≠ [] := by
  exact Holds.iff_query (Script.outputOn_resolved _ _ _ _ _ _ _ head resolved) noClock known found window

/-- The former {lit}`Empty.iff_query` follows at its original premises. -/
theorem Empty_iff_query {script : Script} {db : Database} {isQuery : script.isQuery = true}
    {statement : Syntax.Statement} {parameters : List Value} {rest : List (Syntax.Statement × List Value)}
    {query bound : Resolved.Query} {subqueries : List Resolved.Query} {after : ResolveState}
    {source : Resolved.SourceRows}
    (head : script.statements = (statement, parameters) :: rest)
    (resolved : resolveStatement runContext db.raw.connection.resolveState statement =
      .ok (.query query subqueries, after))
    (noClock : (Resolved.Statement.query query subqueries).readsClock = false)
    (known : db.raw.connection.state.counters.firstUnknown (Resolved.Statement.query query subqueries).counterReads = none)
    (found : query.source (db.raw.connection.queryContext parameters query subqueries) db.raw = some source)
    (window : query.bindWindow parameters = some bound) :
    Empty script db isQuery ↔
      Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = true ∧ source.fault ≠ .may ∧
        (query.run (db.raw.connection.queryContext parameters query subqueries) source.rows).mismatch = false ∧
        (query.run (db.raw.connection.queryContext parameters query subqueries) source.rows).overflow = false ∧
        (query.run (db.raw.connection.queryContext parameters query subqueries) source.rows).fault = .none ∧
        bound.results (db.raw.connection.queryContext parameters query subqueries) source.rows = [] := by
  exact Empty.iff_query (Script.outputOn_resolved _ _ _ _ _ _ _ head resolved) noClock known found window

/-- The former {lit}`Fails.iff_query` follows at its original premises. -/
theorem Fails_iff_query {script : Script} {db : Database} {isQuery : script.isQuery = true}
    {statement : Syntax.Statement} {parameters : List Value} {rest : List (Syntax.Statement × List Value)}
    {query : Resolved.Query} {subqueries : List Resolved.Query} {after : ResolveState}
    {source : Resolved.SourceRows}
    (head : script.statements = (statement, parameters) :: rest)
    (resolved : resolveStatement runContext db.raw.connection.resolveState statement =
      .ok (.query query subqueries, after))
    (noClock : (Resolved.Statement.query query subqueries).readsClock = false)
    (known : db.raw.connection.state.counters.firstUnknown (Resolved.Statement.query query subqueries).counterReads = none)
    (found : query.source (db.raw.connection.queryContext parameters query subqueries) db.raw = some source) :
    Fails script db isQuery ↔
      Resolved.subqueriesPlain (query.nestedSubqueries subqueries) = true ∧ source.fault ≠ .may ∧
        (query.run (db.raw.connection.queryContext parameters query subqueries) source.rows).fault ≠ .may ∧
        ((query.run (db.raw.connection.queryContext parameters query subqueries) source.rows).mismatch = true ∨
        (query.run (db.raw.connection.queryContext parameters query subqueries) source.rows).overflow = true ∨
        (query.run (db.raw.connection.queryContext parameters query subqueries) source.rows).fault = .must) := by
  exact Fails.iff_query (Script.outputOn_resolved _ _ _ _ _ _ _ head resolved) noClock known found

#print axioms Holds_iff_query
#print axioms Empty_iff_query
#print axioms Fails_iff_query

end Belay.Sqlite.ReplacedRowPredicates
