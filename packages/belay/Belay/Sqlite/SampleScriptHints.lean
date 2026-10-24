import Belay.Sqlite.SampleQueryHints
import Belay.Sqlite.Script

set_option doc.verso true

/-! SQL-guided candidates for the shared sampler. Statement names and bound values seed
the same database and value generators used by explicit-schema and Plausible callers. -/

namespace Belay.Sqlite.Sampling

open Belay.Sqlite.Model

/-- Hints for a write target and its expressions. Named write columns suggest columns even
when they do not occur in an expression, as in an INSERT column list. -/
private def writeHints (table : Identifier) (columns : List Identifier)
    (expressions : List Syntax.Expr) (returning : List Syntax.ResultColumn)
    (subqueries : List Syntax.Subquery) : SchemaHints :=
  let current : SchemaHints :=
    { sources := [{ table, alias := none }]
      expressions := ((expressionListHints expressions).append (resultHints returning)).append
        { columns := columns.map (fun column => (some table, column)) } }
  subqueries.foldl (fun hints query => hints.append (subqueryHints query)) current

/-- Hints from ON CONFLICT updates, including their target columns, assigned values and
filters. They remain candidate suggestions; the checker never assumes a conflict occurs. -/
private def conflictHints (conflicts : List Syntax.ConflictClause) : Hints :=
  conflicts.foldl (fun hints clause =>
    let target : Hints := { columns := (clause.target.getD []).map (none, ·) }
    let action : Hints := match clause.action with
      | .nothing => {}
      | .update assignments filter =>
        (expressionListHints (assignments.map (·.2) ++ filter.toList)).append
          { columns := assignments.map fun (name, _) => (none, name) }
    (hints.append target).append action) {}

/-- Infer candidate names and constants from query clauses and write targets. Table/trigger DDL,
DROP INDEX, transaction control and PRAGMAs add no guesses; explicit schema inputs cover cases whose
constraints, views or ambient state cannot be inferred from SQL alone. -/
def statementHints : Syntax.Statement → SchemaHints
  | .select columns source joins filter groupBy orderBy limit offset subqueries having _ _ =>
    subqueries.foldl (fun hints query => hints.append (subqueryHints query))
      (queryHints columns source joins filter groupBy orderBy limit offset having)
  | .insert table columns rows conflicts _ returning subqueries =>
    let hints := writeHints table (columns.getD []) rows.flatten returning subqueries
    { hints with expressions := hints.expressions.append (conflictHints conflicts) }
  | .update table assignments filter returning subqueries =>
    writeHints table (assignments.map (·.1)) (assignments.map (·.2) ++ filter.toList) returning subqueries
  | .delete table filter returning subqueries => writeHints table [] filter.toList returning subqueries
  | .createIndex _ _ table terms filter =>
    writeHints table [] (terms.map (·.expression) ++ filter.toList) [] []
  | .createTable .. | .addColumn .. | .dropTable .. | .dropIndex .. | .begin | .commit | .rollback
  | .pragma _ | .createTrigger .. | .dropTrigger .. => {}

/-- Infer names and literal/bound values from each script statement in order. Bindings are
included as actual values, so a parameterized query uses the same targeted row candidates
as its literal counterpart. Use these hints with an explicit schema to preserve constraints. -/
def scriptHints (script : Script) : SchemaHints :=
  script.statements.foldl (fun hints (statement, values) =>
    let found := statementHints statement
    hints.append { found with expressions := found.expressions.append { values } }) {}

/-- The empty database, then targeted databases under the inferred schema, in stable order.
Schema inference is a bounded heuristic: it supplies no assumption to the original claim.
Use {name}`targeted` with an explicit database or a custom sequence when SQL has insufficient
schema information. Duplicate candidates are harmless and keep source order transparent. -/
def scriptCandidates (script : Script) : List Database :=
  let hints := scriptHints script
  Database.empty :: (hints.schema.toList.flatMap fun base => targeted base hints.expressions.values)

end Belay.Sqlite.Sampling
