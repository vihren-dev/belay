import Belay.Sqlite.Model.Queries.Evaluation.SelectOneResolution
import Belay.Sqlite.Model.Queries.Preparation.SingleSourceNameLaws

set_option doc.verso true

namespace Belay.Sqlite.Model
open Resolved

/-- For every dialect setting, subquery shapes, table position, table name, columns, rowid flag, alias
flag, identifier that names a column of the table, quote kind, alias and text: a found identifier as the
only result column resolves to its column position. Its output name and affinity are whatever the
resolver gives. The result is the same whether the source has an alias or not ({lit}`aliased`), because
the flag only tells a name trace whether the table was written with an alias. Proof sketch: unfold the
result-column resolver for an expression that is a name, then apply the single-source name law. -/
theorem resolveColumns_identifier_at (dqs : Bool) (shapes : SubqueryShapes) (position : Option Nat)
    (tableName : Identifier) (columns : List CatalogColumn) (rowid aliased : Bool) {id : Identifier}
    (quote : Syntax.QuoteKind) {idPosition : Nat} (found : columnPosition columns id = some idPosition)
    (alias : Option Identifier) (text : String) :
    ∃ (name : String) (affinity : Option Affinity),
      resolveAll (resolveResultColumn dqs (Scope.singleAt position tableName columns rowid aliased) shapes)
        [.expression (.identifier id quote) alias text] = .ok [[(.scalar (.column idPosition), name, affinity)]] := by
  simp [resolveAll, resolveAllFrom, resolveResultColumn_expression, resolveOperand_identifier_singleAt found, Bind.bind,
    Except.bind, Pure.pure, Except.pure, Except.mapError]

end Belay.Sqlite.Model
