import Belay.Sqlite.Model.Frontend.Codecs.Codec
import Belay.Sqlite.Model.Queries.Preparation.ForeignKeyAction

set_option doc.verso true

open Lean

namespace Belay.Sqlite.Model.Conformance

/-- A foreign key of a table in the terms of {lit}`PRAGMA foreign_key_list`: the referenced
table, the names of its columns, the referenced columns, and the names of its actions. -/
def foreignKeyJson (columns : List CatalogColumn) (key : ForeignKey) : Json :=
  Json.mkObj [("table", toJson key.table),
    ("columns", toJson (key.columns.filterMap fun position => columns[position]?.map (·.name))),
    ("referenced", toJson key.referenced), ("onDelete", toJson key.onDelete.sqlName),
    ("onUpdate", toJson key.onUpdate.sqlName)]

end Belay.Sqlite.Model.Conformance
