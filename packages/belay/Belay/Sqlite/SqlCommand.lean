import Belay.Sqlite.Run
import Belay.Sqlite.SqlTerm
import Belay.Sqlite.EvalDatabase
import Belay.Sqlite.SqlEditorInfo

set_option doc.verso true

/-! The command {lit}`#sql db r"..."`: it runs the script on the database and shows the output of
each statement in the editor, rows as a table with the names of the columns. For example,
{lit}`#sql shop r"SELECT * FROM invoices"` shows the table of the invoices. The command also runs
the script while the file elaborates, to give the table names the rows that the run reached. -/

namespace Belay.Sqlite

open Lean Elab Command Belay.Sqlite.Model

/-- The outputs of a run as {lit}`#sql` shows them: the text of each output, one after the other,
with an empty line between two outputs. -/
structure Tables where
  /-- The text that {lit}`#sql` shows. -/
  text : String

instance : Repr Tables where
  reprPrec tables _ := tables.text

/-- The outputs of the script on the database ({name}`Database.Raw.run`), each with the names of
its result columns ({name}`scriptResultNames`), as {lit}`#sql` shows them ({name}`Output.table`). -/
def Database.tables (db : Database) (script : Script) : Tables :=
  let names := scriptResultNames runContext none db.raw.connection script.statements
  { text := "\n\n".intercalate (((db.raw.run script).outputs.zip names).map fun (output, columns) => output.table columns) }

/-- {lit}`#sql db r"..."` shows the output of each statement of the script on the database
({name}`Database.tables`). The text is a script as {lit}`sql r"..."` reads it, so its errors
are at their positions in the text. -/
syntax (name := sqlCommand) "#sql " term:max str : command

/-- Run the script of the literal on the value of the database term and give the table names of
the text editor information with the rows of that run ({name}`executedContexts`). The attempt is
a trial: Lean elaborates the database term and the text again for the output, so the trial drops
its messages and information, and it keeps nothing when the database has no value yet or the text
has an error. Lean then shows each error once, at the elaboration of the output. -/
def sqlCommandInformation (databaseTerm literal : Syntax) : Term.TermElabM Unit := do
  let some text := literal.isStrLit? | return
  let saved ← Term.saveState
  let attempt ← try
      match ← evaluateDatabase databaseTerm with
      | some evaluated => pure (some (evaluated, ← literalStatements literal))
      | none => pure none
    catch _ => pure none
  saved.restore (restoreInfo := true)
  if let some (evaluated, items) := attempt then
    let statements := items.toList.map (·.statement)
    let (contexts, _) := executedContexts 0 evaluated.value.raw.connection statements
    emitSqlEditorInfo (.literal literal text) statements (.ofTerm (← getEnv) evaluated.term) contexts

/-- Elaborate {lit}`#sql db r"..."`: give the editor information of the table names
({name}`sqlCommandInformation`), then show the tables of the output of the script on the database,
as {lit}`#eval` of {name}`Database.tables` shows them. -/
@[command_elab sqlCommand]
def elabSqlCommand : CommandElab := fun stx => do
  match stx with
  | `(#sql $database $text) =>
    liftTermElabM (sqlCommandInformation database text)
    elabCommand (← `(#eval Belay.Sqlite.Database.tables $database (sql $text)))
  | _ => throwUnsupportedSyntax

end Belay.Sqlite
