import Belay.Sqlite.Model.Resolution.ReservedNames
import Belay.Sqlite.Model.Resolution.SyntaxDefinitions

set_option doc.verso true

/-! The statistics tables of ANALYZE, which a catalog description may contain although their names are
reserved. -/

namespace Belay.Sqlite.Model

/-- The exact statistics tables that ANALYZE creates, which a catalog description may contain. -/
def statisticsTable (name : Identifier) (columns : List Syntax.ColumnDefinition)
    (constraints : List Syntax.TableConstraint) : Bool :=
  let plain := fun (names : List Identifier) => columns == names.map fun column =>
    { name := column, declaredType := none, constraints := [] }
  constraints.isEmpty && (statisticsColumns name.folded).any plain

end Belay.Sqlite.Model
