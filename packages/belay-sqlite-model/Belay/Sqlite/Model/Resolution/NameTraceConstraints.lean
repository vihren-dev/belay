import Belay.Sqlite.Model.Resolution.NameResultSources
import Belay.Sqlite.Model.Resolution.CatalogObjects

set_option doc.verso true

/-! The constraints of the columns that a trace binds. The scopes of the resolver hold no key
and no foreign key, so the trace gets them from the catalog of the statement, once, after the
resolution: the key columns of the table at the catalog position of the source. -/

namespace Belay.Sqlite.Model

/-- The constraints of the column at {lit}`index` of the table: the table's primary key, a unique
key or a foreign key (a column constraint or a table constraint) that holds the column, and the
column's own {lit}`NOT NULL` ({lit}`notNull`, as the scope read it). -/
def CatalogTable.columnConstraints (table : CatalogTable) (index : Nat) (notNull : Bool) : ColumnConstraints :=
  { primaryKey := table.primaryKey.contains index, unique := table.uniqueKeys.any (·.contains index),
    foreignKey := table.allForeignKeys.any (·.columns.contains index), notNull }

/-- The binding whose column belongs to a table of the catalog, with the constraints of the table. A
binding of a derived column, of a source without a catalog position and of a position that is no table
stays as it is. -/
def Binding.withConstraints (catalog : Catalog) (binding : Binding) : Binding :=
  let entry : Option CatalogEntry := (binding.source.position.bind (catalog[·]?)).map (·.entry)
  match binding.column.origin, entry with
  | .declared constraints, some (.table table) =>
    { binding with column := { binding.column with
        origin := .declared (table.columnConstraints binding.column.index constraints.notNull) } }
  | .declared _, some (.view _) | .declared _, some (.index _) | .declared _, some (.trigger _)
  | .declared _, none | .inferred _, _ => binding

/-- The candidate with the constraints of its column. -/
def Candidate.withConstraints (catalog : Catalog) : Candidate → Candidate
  | .column binding => .column (binding.withConstraints catalog)
  | .resultAlias name index => .resultAlias name index
  | .source reference => .source reference
  | .catalogObject kind name position => .catalogObject kind name position

/-- The result with the constraints of every column that it binds or offers. -/
def NameResult.withConstraints (catalog : Catalog) : NameResult → NameResult
  | .found bindings => .found (bindings.map (·.withConstraints catalog))
  | .ambiguous candidates => .ambiguous (candidates.map (·.withConstraints catalog))
  | .missing use candidates => .missing use (candidates.map (·.withConstraints catalog))
  | .source reference => .source reference
  | .schema known => .schema known
  | .resultColumn index => .resultColumn index
  | .declares => .declares
  | .compared form affinity collation => .compared form affinity collation
  | .unreached why => .unreached why

/-- The trace with the constraints of the columns from the catalog of the statement. -/
def NameTrace.withConstraints (catalog : Catalog) (trace : NameTrace) : NameTrace :=
  trace.map fun occurrence => { occurrence with result := occurrence.result.withConstraints catalog }

end Belay.Sqlite.Model
