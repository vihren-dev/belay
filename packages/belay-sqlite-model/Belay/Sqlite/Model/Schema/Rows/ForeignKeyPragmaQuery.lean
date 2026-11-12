import Belay.Sqlite.Model.Schema.Rows.ForeignKeyCheckLaws
import Belay.Sqlite.Model.Schema.Rows.ForeignKeyPrepareLaws
import Belay.Sqlite.Model.Queries.Evaluation.SelectSubqueryRules
import Belay.Sqlite.Model.Schema.Dispatch.SelectSubqueryRules

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The foreign-key pragma reads only columns, so no expression fails or reads external state. -/
theorem keyCheckQuery_calm (table : Option Nat) : (keyCheckQuery table).Calm := by
  intro expression member
  simp [keyCheckQuery, pragmaQuery, Resolved.Statement.clockExpressions, Resolved.Query.expressions,
    Resolved.Query.keptExpressions, Resolved.QuerySource.expressions, Resolved.Output.scalars,
    Resolved.Output.operands, foreignKeyCheckNames, List.range_succ] at member
  rcases member with rfl | rfl | rfl | rfl <;> exact ⟨rfl, rfl, fun _ => rfl⟩

/-- For every context, database, table choice and rows: if the pragma supplies the rows, the source of its query gives
those rows, with four columns and no fault. Proof sketch: unfold the query, the source and the join of its one
pragma source; the join of one source is the rows of the pragma. -/
theorem keyCheckQuery_source (context : Resolved.EvalContext) (database : Database)
    (table : Option Nat) (rows : List (List Value))
    (found : (Resolved.PragmaRows.foreignKeyCheck table).rowsOn database = some rows) :
    (pragmaQuery (.foreignKeyCheck table) foreignKeyCheckNames).source context database =
      some { rows, width := 4, fault := .none } := by
  simp [pragmaQuery, Resolved.Query.source, Resolved.QuerySource.join, found, List.foldlM,
    Resolved.joinRows, Resolved.joinRow, Resolved.joinMatches, Resolved.QuerySource.matches,
    Resolved.PragmaRows.width]

end Belay.Sqlite.Model
