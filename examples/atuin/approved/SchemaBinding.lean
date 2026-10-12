import SchemaInputs

set_option doc.verso true

/-! The catalog comes only from the sealed resolution of schema.sql.
Handwritten column names below describe the application mapping, not a SQL schema. -/

namespace SchemaBinding

open Belay.Sqlite SqliteVerifier

/-- The complete sealed {name}`Generated.startCatalog`; use it for catalog-bound
application interpretation rather than duplicating declarations. -/
abbrev start : Catalog := Generated.startCatalog

/-- Return the history table entry of the sealed catalog, or a table without
columns when absent. The latter is not a supported table; {name}`Conforms` and
decoder validity remain separate proof obligations. -/
def history : CatalogTable :=
  ((start.findTable "history").map Prod.snd).getD { columns := [] }

/-- The eleven pre-migration application fields used by the approved decoder. -/
def fields : List String := ["id", "timestamp", "duration", "exit", "command", "cwd",
  "session", "hostname", "deleted_at", "author", "intent"]

end SchemaBinding
