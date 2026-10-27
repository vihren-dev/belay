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

An {lit}`INSERT ... SELECT` is the one statement that gets the risk warning in every context: its
output is {lit}`done`, so a run gives no evidence of the order dependence, and the rows that it inserts
can depend on the order. {lit}`orderRunWarnings` adds this warning to the evidence of a run.

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

/-- Whether the statement is a query, or inserts the rows of a query, that takes rows with
{lit}`LIMIT` or {lit}`OFFSET`. -/
def takesRowsByLimit : Syntax.Statement → Bool
  | .select (limit := limit) (offset := offset) .. | .insertSelect (source := { limit, offset, .. }) .. =>
    limit.isSome || offset.isSome
  | .createView .. | .createTable .. | .createIndex .. | .addColumn .. | .renameTable .. | .renameColumn .. | .dropColumn .. | .dropTable .. | .dropView ..
  | .dropIndex .. | .begin | .commit | .rollback | .insert .. | .update .. | .delete .. | .pragma _
  | .createTrigger .. | .dropTrigger .. => false

/-- Whether a query with the given clauses reads rows from a source or from a compound query, takes
rows with {lit}`LIMIT` or {lit}`OFFSET` and has no {lit}`ORDER BY`. The clauses are those of a
{lit}`SELECT` statement and of the query of an {lit}`INSERT ... SELECT` ({name}`Syntax.SelectBody`),
which are the same fields. For example, the clauses of {lit}`SELECT a FROM t LIMIT 1` are, and those
of {lit}`SELECT 1 LIMIT 1` are not. -/
def clausesLimitWithoutOrder (limit offset : Option Syntax.Expr) (orderBy : List Syntax.OrderTerm)
    (source : Option Syntax.TableReference) (compound : Option Syntax.Compound) : Bool :=
  (limit.isSome || offset.isSome) && orderBy.isEmpty && (source.isSome || compound.isSome)

/-- Whether the statement is a query, or inserts the rows of a query, that takes rows with
{lit}`LIMIT` or {lit}`OFFSET`, has no {lit}`ORDER BY` and reads rows from a source or from a compound
query ({name}`clausesLimitWithoutOrder`). For example, {lit}`SELECT a FROM t LIMIT 1` and
{lit}`INSERT INTO s SELECT a FROM t LIMIT 1` are, and {lit}`SELECT 1 LIMIT 1` is not. -/
def limitsWithoutOrder : Syntax.Statement → Bool
  | .select (source := source) (orderBy := orderBy) (limit := limit) (offset := offset) (compound := compound) ..
  | .insertSelect (source := { source, orderBy, limit, offset, compound, .. }) .. =>
    clausesLimitWithoutOrder limit offset orderBy source compound
  | .createView .. | .createTable .. | .createIndex .. | .addColumn .. | .renameTable .. | .renameColumn .. | .dropColumn .. | .dropTable .. | .dropView ..
  | .dropIndex .. | .begin | .commit | .rollback | .insert .. | .update .. | .delete .. | .pragma _
  | .createTrigger .. | .dropTrigger .. => false

/-- Whether the statement inserts the rows of a query. -/
def insertsQueryRows : Syntax.Statement → Bool
  | .insertSelect .. => true
  | .select .. | .createView .. | .createTable .. | .createIndex .. | .addColumn .. | .renameTable .. | .renameColumn .. | .dropColumn .. | .dropTable .. | .dropView ..
  | .dropIndex .. | .begin | .commit | .rollback | .insert .. | .update .. | .delete .. | .pragma _
  | .createTrigger .. | .dropTrigger .. => false

/-- The text of the risk warning for the statement. It does not say that the results differ. An
{lit}`INSERT ... SELECT` says that the inserted rows may depend on the order. -/
def orderRiskMessage (statement : Syntax.Statement) : String :=
  let (subject, rows) := if insertsQueryRows statement
    then ("this statement inserts the rows of a query that", "the rows that it inserts")
    else ("this query", "the rows that it selects")
  s!"{subject} takes rows with LIMIT or OFFSET and has no ORDER BY, so {rows} may depend on an order " ++
    "that SQLite does not promise; add an ORDER BY with a unique order. " ++
    "This warning does not run the query, so the results may be equal"

/-- The text of the evidence warning for a statement with the given number of permitted results:
it names the dependence on {lit}`LIMIT` or {lit}`OFFSET` when the statement has one. -/
def orderEvidenceMessage (statement : Syntax.Statement) (alternatives : Nat) : String :=
  let cause := if takesRowsByLimit statement then "the rows that LIMIT or OFFSET select" else "the rows"
  s!"SQLite may give {alternatives} different results for this statement, because {cause} depend " ++
    "on an order that SQLite does not promise; add an ORDER BY with a unique order"

/-- The risk warning of a statement, at the statement ({name}`statementRange`). -/
def orderRiskDiagnostic (item : Located Syntax.Statement) : Diagnostic :=
  let (start, stop) := statementRange item
  { start, stop, message := orderRiskMessage item.value }

/-- The risk warnings of the statements, each at its statement. -/
def orderRiskWarnings (items : List (Located Syntax.Statement)) : List Diagnostic :=
  (items.filter (limitsWithoutOrder ·.value)).map orderRiskDiagnostic

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

/-- The warnings of a context that runs its statements: the evidence of the statements with several
permitted results ({name}`orderEvidenceWarnings`), and the risk of each {lit}`INSERT ... SELECT` that
takes rows by {lit}`LIMIT` without {lit}`ORDER BY`, because its output holds no alternatives
({name}`insertsQueryRows`). A statement whose output has several permitted results gets only the
evidence, so no statement warns twice. -/
def orderRunWarnings (items : List (Located Syntax.Statement)) (outputs : List Output) : List Diagnostic :=
  orderEvidenceWarnings items outputs ++
    (items.zipIdx.filter fun (item, index) =>
      insertsQueryRows item.value && limitsWithoutOrder item.value &&
        ((outputs[index]?).bind permittedResults?).isNone).map (orderRiskDiagnostic ·.1)

/-- Log the warnings at their ranges of the literal's text, unless the option
{lit}`sql.orderWarnings` is false. -/
def logOrderWarnings (literal : Syntax) (text : String) (warnings : List Diagnostic) : TermElabM Unit := do
  if sql.orderWarnings.get (← getOptions) then
    for warning in warnings do
      logWarningAt (textRange literal text warning.start warning.stop) warning.message

end Belay.Sqlite
