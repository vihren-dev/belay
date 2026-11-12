import Belay.Sqlite.Queries.Preparation.SqlNameSites

set_option doc.verso true

namespace Belay.Sqlite

open Belay.Sqlite.Model

/-- What a source of a scope is, in a few words. -/
def sourceKindWords : SourceKind → String
  | .baseTable => "table"
  | .initialTable => "table of the initial database"
  | .storedView => "view"
  | .commonTable => "WITH definition"
  | .derivedTable => "subquery"
  | .tableFunction => "table-valued function"
  | .proposedRow => "proposed row of the upsert"
  | .triggerRow => "trigger row"

/-- The source in words: its kind and its name. A table or view that the statement renames with an
alias also shows its catalog name, which the catalog position of the source gives. -/
def sourceWords (catalog : Catalog) (source : SourceRef) : String :=
  let kind := sourceKindWords source.kind
  match source.position.bind (catalog[·]?) with
  | some object =>
    if object.name.sameName source.name then s!"{kind} `{object.name}`"
    else s!"{kind} `{object.name}` (alias `{source.name}`)"
  | none => s!"{kind} `{source.name}`"

end Belay.Sqlite
