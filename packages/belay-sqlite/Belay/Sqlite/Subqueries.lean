import Belay.Sqlite.QueryRun
import Belay.Sqlite.QueryFunctions

set_option doc.verso true

/-! The subqueries of a statement (ADR 0018, D1): the run of one subquery for an outer row,
and the evaluation context of a statement whose expressions name its subqueries by index.
A subquery's row is the outer row followed by the subquery's own cells, so its sources are
joined after the outer row, and a correlated reference is a cell position. -/

namespace Belay.Sqlite.Resolved

/-- The source rows of a subquery for an outer row: its sources joined in written order
({name}`QuerySource.join`) from the outer row, so each row starts with the outer cells; none
when a table is missing. With no outer cells this is {name}`Query.source`. -/
def Query.sourceAfter (context : EvalContext) (outer : List Value) (query : Query) (database : Database) :
    Option SourceRows :=
  query.sources.foldlM (QuerySource.join context database) { rows := [outer], width := outer.length, fault := .none }

/-- The run of a subquery for an outer row: the rows of {name}`Query.run` over its source rows
({name}`Query.sourceAfter`), with the fault of the sources and of the run softened to
{lean}`Fault.may`, because SQLite evaluates a subquery only when it needs its value. A missing
table and an integer overflow, which the model does not describe inside a subquery, are
{lean}`Fault.may` too. -/
def Query.subqueryRun (context : EvalContext) (database : Database) (outer : List Value) (query : Query) :
    SubqueryRun :=
  match query.sourceAfter context outer database with
  | none => { rows := [], fault := .may }
  | some source =>
    let run := query.run context source.rows
    { rows := run.rows, fault := if run.overflow then .may else (source.fault.join run.fault).soften }

/-- The context of a statement's subqueries at a nesting depth: with no depth left, the plain
context; else subquery {lit}`index` runs ({name}`Query.subqueryRun`) in the context one depth
below, which serves the subqueries that its own expressions name, all later in the list. -/
def subqueryContext (clock : Int) (database : Database) (subqueries : List Query) : Nat → EvalContext
  | 0 => .plain clock
  | depth + 1 =>
    { clock, subqueries := fun index outer => match subqueries[index]? with
        | some query => query.subqueryRun (subqueryContext clock database subqueries depth) database outer
        | none => { rows := [], fault := .none } }

/-- The evaluation context of a statement at a clock value over a database: its subqueries at
the depth of their number ({name}`subqueryContext`), which bounds their nesting because each
subquery's expressions name only later ones. Without subqueries it is the plain context. -/
def statementContext (clock : Int) (database : Database) (subqueries : List Query) : EvalContext :=
  subqueryContext clock database subqueries subqueries.length

/-- For every clock value and database, the context of a statement without subqueries is the
plain context of the clock value. -/
@[simp] theorem statementContext_nil (clock : Int) (database : Database) :
    statementContext clock database [] = .plain clock := rfl

end Belay.Sqlite.Resolved
