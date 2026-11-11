import Belay.Sqlite.Model.Schema.Columns.AddColumnPlainStep
import Belay.Sqlite.Model.Schema.Triggers.CreateTriggerStep
import Belay.Sqlite.Model.Queries.Preparation.ColumnPositionAppend
import Belay.Sqlite.Model.Schema.Ddl.ColumnPositionAppend

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The CREATE TRIGGER statement without IF NOT EXISTS that registers a trigger, with the values bound to it. -/
def triggerStatement (trigger : (Identifier × CatalogTrigger) × List Value) : Syntax.Statement × List Value :=
  (.createTrigger trigger.1.1 false trigger.1.2.time trigger.1.2.event trigger.1.2.table trigger.1.2.condition
    trigger.1.2.body, trigger.2)

/-- The migration script: ADD COLUMN of a column definition, the backfill
{lit}`UPDATE t SET name = value` of the added column with no filter, and one CREATE TRIGGER statement for
each trigger, with the values bound to each statement. The trigger names and definitions are arbitrary;
registration executes no trigger body. -/
def derivedColumnScript (tableName : Identifier) (definition : Syntax.ColumnDefinition) (value : Syntax.Expr)
    (addValues updateValues : List Value) (triggers : List ((Identifier × CatalogTrigger) × List Value)) :
    List (Syntax.Statement × List Value) :=
  (.addColumn tableName definition, addValues) ::
    (.update tableName [(definition.name, value)] none [] [], updateValues) :: triggers.map triggerStatement

end Belay.Sqlite.Model
