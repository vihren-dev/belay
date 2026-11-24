import Belay

set_option doc.verso true

/-! Original observation contracts under ADR 0033. Successful resolution supplies the output evidence. -/

namespace Belay.Sqlite.ReplacedObservations
open Belay.Sqlite.Model

/-- The former {lit}`Script.outputOn_query` follows at its original premises. -/
theorem Script_outputOn_query (script : Script) (db : Database) (statement : Syntax.Statement)
    (parameters : List Value) (rest : List (Syntax.Statement × List Value))
    (query : Resolved.Query) (subqueries : List Resolved.Query) (after : ResolveState)
    (head : script.statements = (statement, parameters) :: rest)
    (resolved : resolveStatement runContext db.raw.connection.resolveState statement =
      .ok (.query query subqueries, after)) :
    script.outputOn db =
      some (resolvedStepOutput none 0 db.raw.connection parameters (.query query subqueries)) := by
  exact Script.outputOn_resolved script db statement parameters rest (.query query subqueries) after head resolved

/-- The former {lit}`Script.outputIn_query` follows at its original premises. -/
theorem Script_outputIn_query (script : Script) (context : ExecutionContext) (statement : Syntax.Statement)
    (parameters : List Value) (rest : List (Syntax.Statement × List Value))
    (query : Resolved.Query) (subqueries : List Resolved.Query) (after : ResolveState)
    (head : script.statements = (statement, parameters) :: rest)
    (resolved : resolveStatement runContext context.connection.resolveState statement =
      .ok (.query query subqueries, after)) :
    script.outputIn context = some (resolvedStepOutput context.clock context.index context.connection
      parameters (.query query subqueries)) := by
  exact Script.outputIn_resolved script context statement parameters rest (.query query subqueries) after head resolved

/-- The former {lit}`Script.outputIn_eq_of_independent` follows at its original premises. -/
theorem Script_outputIn_eq_of_independent (script : Script) (first second : ExecutionContext)
    (statement : Syntax.Statement) (parameters : List Value) (rest : List (Syntax.Statement × List Value))
    (query : Resolved.Query) (subqueries : List Resolved.Query) (afterFirst afterSecond : ResolveState)
    (head : script.statements = (statement, parameters) :: rest)
    (resolvedFirst : resolveStatement runContext first.connection.resolveState statement =
      .ok (.query query subqueries, afterFirst))
    (resolvedSecond : resolveStatement runContext second.connection.resolveState statement =
      .ok (.query query subqueries, afterSecond))
    (noClock : (Resolved.Statement.query query subqueries).readsClock = false)
    (noCounters : (Resolved.Statement.query query subqueries).counterReads = [])
    (sameDatabase : first.connection.state.database = second.connection.state.database) :
    script.outputIn first = script.outputIn second := by
  exact Script.outputIn_eq_of_independent script first second parameters query subqueries
    (Script.outputIn_resolved _ _ _ _ _ _ _ head resolvedFirst)
    (Script.outputIn_resolved _ _ _ _ _ _ _ head resolvedSecond) noClock noCounters sameDatabase

/-- The former {lit}`Holds.inContext_iff_reached` follows at its original premises. -/
theorem Holds_inContext_iff_reached (script : Script) (context : ExecutionContext)
    (query : script.isQuery = true) (statement : Syntax.Statement) (parameters : List Value)
    (rest : List (Syntax.Statement × List Value)) (resolvedQuery : Resolved.Query)
    (subqueries : List Resolved.Query) (afterHere afterDefault : ResolveState)
    (head : script.statements = (statement, parameters) :: rest)
    (here : resolveStatement runContext context.connection.resolveState statement =
      .ok (.query resolvedQuery subqueries, afterHere))
    (byDefault : resolveStatement runContext context.defaultObservation.connection.resolveState statement =
      .ok (.query resolvedQuery subqueries, afterDefault))
    (noClock : (Resolved.Statement.query resolvedQuery subqueries).readsClock = false)
    (noCounters : (Resolved.Statement.query resolvedQuery subqueries).counterReads = []) :
    Holds.inContext script context query ↔ Holds.reached script context query := by
  exact Holds.inContext_iff_reached script context query parameters resolvedQuery subqueries
    (Script.outputIn_resolved _ _ _ _ _ _ _ head here)
    (Script.outputIn_resolved _ _ _ _ _ _ _ head byDefault) noClock noCounters

#print axioms Script_outputOn_query
#print axioms Script_outputIn_query
#print axioms Script_outputIn_eq_of_independent
#print axioms Holds_inContext_iff_reached

end Belay.Sqlite.ReplacedObservations
