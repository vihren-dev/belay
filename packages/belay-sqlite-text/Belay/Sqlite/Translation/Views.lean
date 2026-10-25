import Belay.Sqlite.Translation.Mappers

set_option doc.verso true

/-! CREATE VIEW uses the existing query translator and indexed subquery list.
The model retains this syntax until a statement uses the view. -/

namespace Belay.Sqlite.Translation

open Belay.Sqlite.Model

/-- Translate CREATE VIEW, including IF NOT EXISTS and optional output names.
Temporary views and schema-qualified names remain outside the single-schema model. -/
def createView (tree : SqlTree) (command : ParseNode) : TranslateM (Located Syntax.Statement) := do
  let parts ← require tree command ["createkw", "temp", "VIEW", "ifnotexists", "nm", "dbnm", "eidlist_opt",
    "AS", "select"]
  absent parts[1]! "A temporary view"
  absent parts[5]! "A schema name"
  let name ← identifierName tree parts[4]!
  let columns ← queryColumnNames tree parts[6]!
  let body := parts[8]!
  let (clauses, items) ← statementSubqueries (queryClauses tree body)
  let query := clauses.subquery (missing body.start body.stop) body.start body.stop
  let subqueries := sequence items body.start body.stop
  return composite (.createView name.value (!parts[3]!.children.isEmpty) columns.value query.value subqueries.value)
    command.start command.stop #[name.span, spanOf parts[3]!, columns.span, query.span, subqueries.span]

end Belay.Sqlite.Translation
