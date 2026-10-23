import Lean.Elab.Command
import Belay.Sqlite.Parse
import Belay.Sqlite.SqlLiteral

set_option doc.verso true

/-! {lit}`#sql_parse "SQL"` parses the SQL text with SQLite's grammar while the file elaborates
(ADR 0017, S1, prototype 1). It shows the number of commands, or an error at the position in
the text where SQLite's grammar rejects it. -/

namespace Belay.Sqlite

open Lean Elab Command

/-- {lit}`#sql_parse "SQL"`: parse the SQL text with the grammar of SQLite 3.51.0 and show the
number of commands, or SQLite's grammar error at its position. -/
syntax (name := sqlParse) "#sql_parse " str : command

/-- The number of commands of a parse tree: its {lit}`ecmd` nodes that are more than an empty
statement's {lit}`;`, with or without {lit}`EXPLAIN` before them. -/
def commandCount (nodes : Array ParseNode) : Nat :=
  (nodes.filter fun node => node.symbol == "ecmd" && node.children.size ≥ 2).size

/-- Parse the literal's text and show the result at the command or the error's position. -/
@[command_elab sqlParse]
def elabSqlParse : CommandElab := fun command => do
  let literal := command[1]
  let some text := literal.isStrLit? | throwUnsupportedSyntax
  match ← liftIO (parseSql Release.default text.toUTF8) with
  | .parsed nodes _ => logInfo m!"SQLite's grammar accepts {commandCount nodes} commands"
  | .inputError offset =>
    logErrorAt (textRange literal text offset (offset + 1))
      m!"SQLite's grammar rejects the SQL here; correct the SQL at this position"
  | .resourceLimit _ =>
    logErrorAt literal
      m!"The SQL exceeds the parser's limits of 1 MiB of input and 200,000 syntax-tree nodes; split it"

end Belay.Sqlite
