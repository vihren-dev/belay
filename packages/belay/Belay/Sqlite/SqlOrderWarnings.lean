import Belay.Sqlite.SqlDiagnostics
import Belay.Sqlite.SqlLiteral
import Lean.Elab.Term

set_option doc.verso true

/-! Warnings about results that depend on an order which SQLite does not promise (the editor
task, part 2a). Two diagnostics exist, and each context gives one of them:

- The evidence warning, from a context that runs its statements ({lit}`db!` and {lit}`#sql`).
  The model gives {name}`Belay.Sqlite.Model.Output.oneOf` for a statement with several permitted
  results, and the warning names the number of results and, when the statement has {lit}`LIMIT` or
  {lit}`OFFSET`, that dependence. A statement with one result, or with equal results, gets none.
- The risk warning, from a context that does not run its statements ({lit}`sql` and
  {lit}`sql!`). It looks at the syntax only: a query with {lit}`LIMIT` or {lit}`OFFSET`, no
  {lit}`ORDER BY` and a source of rows. It says that the selection may depend on the order, not
  that the results differ, because nothing evaluated the query. A query that always gives one row,
  such as an aggregate, can still get it; turn the warnings off then.

A warning never changes the term, the success of the elaboration or a proof obligation. The option
{lit}`sql.orderWarnings` turns both off. -/

/-- Warn about results that depend on an order that SQLite does not promise. Set false to
silence both the warning of a run that found several permitted results and the warning of a query
that may depend on the order. Elaboration is the same with either value. -/
register_option sql.orderWarnings : Bool := {
  defValue := true
  descr := "warn about SQL results that depend on an order that SQLite does not promise" }

namespace Belay.Sqlite

open Lean Elab Term Belay.Sqlite.Model Translation

/-- Whether the statement is a query that takes rows with {lit}`LIMIT` or {lit}`OFFSET`. -/
def takesRowsByLimit : Syntax.Statement → Bool
  | .select (limit := limit) (offset := offset) .. => limit.isSome || offset.isSome
  | .createView .. | .createTable .. | .createIndex .. | .addColumn .. | .renameTable .. | .renameColumn .. | .dropTable .. | .dropView ..
  | .dropIndex .. | .begin | .commit | .rollback | .insert .. | .insertSelect .. | .update .. | .delete .. | .pragma _
  | .createTrigger .. | .dropTrigger .. => false

/-- Whether the statement is a query that takes rows with {lit}`LIMIT` or {lit}`OFFSET`, has no
{lit}`ORDER BY` and reads rows from a source or from a compound query. For example,
{lit}`SELECT a FROM t LIMIT 1` is, and {lit}`SELECT 1 LIMIT 1` is not. -/
def limitsWithoutOrder : Syntax.Statement → Bool
  | statement@(.select (source := source) (orderBy := orderBy) (compound := compound) ..) =>
    takesRowsByLimit statement && orderBy.isEmpty && (source.isSome || compound.isSome)
  | .createView .. | .createTable .. | .createIndex .. | .addColumn .. | .renameTable .. | .renameColumn .. | .dropTable .. | .dropView ..
  | .dropIndex .. | .begin | .commit | .rollback | .insert .. | .insertSelect .. | .update .. | .delete .. | .pragma _
  | .createTrigger .. | .dropTrigger .. => false

/-- The text of the risk warning. It does not say that the results differ. -/
def orderRiskMessage : String :=
  "this query takes rows with LIMIT or OFFSET and has no ORDER BY, so the rows that it selects " ++
    "may depend on an order that SQLite does not promise; add an ORDER BY with a unique order. " ++
    "This warning does not run the query, so the results may be equal"

/-- The text of the evidence warning for a statement with the given number of permitted results:
it names the dependence on {lit}`LIMIT` or {lit}`OFFSET` when the statement has one. -/
def orderEvidenceMessage (statement : Syntax.Statement) (alternatives : Nat) : String :=
  let cause := if takesRowsByLimit statement then "the rows that LIMIT or OFFSET select" else "the rows"
  s!"SQLite may give {alternatives} different results for this statement, because {cause} depend " ++
    "on an order that SQLite does not promise; add an ORDER BY with a unique order"

/-- The risk warnings of the statements, each at its statement ({name}`statementRange`). -/
def orderRiskWarnings (items : List (Located Syntax.Statement)) : List Diagnostic :=
  items.filterMap fun item =>
    if limitsWithoutOrder item.value then
      let (start, stop) := statementRange item
      some { start, stop, message := orderRiskMessage }
    else none

/-- The number of results of an output with several permitted results. -/
def permittedResults? : Output → Option Nat
  | .oneOf results => some results.length
  | .rows _ | .done _ | .error _ | .unmodeled _ => none

/-- The evidence warnings of the statements that ran, each at its statement. The outputs pair with
the statements by position; a statement that did not run has no output and gets none. -/
def orderEvidenceWarnings (items : List (Located Syntax.Statement)) (outputs : List Output) : List Diagnostic :=
  (items.zip outputs).filterMap fun (item, output) =>
    (permittedResults? output).map fun alternatives =>
      let (start, stop) := statementRange item
      { start, stop, message := orderEvidenceMessage item.value alternatives }

/-- Log the warnings at their ranges of the literal's text, unless the option
{lit}`sql.orderWarnings` is false. -/
def logOrderWarnings (literal : Syntax) (text : String) (warnings : List Diagnostic) : TermElabM Unit := do
  if sql.orderWarnings.get (← getOptions) then
    for warning in warnings do
      logWarningAt (textRange literal text warning.start warning.stop) warning.message

end Belay.Sqlite
