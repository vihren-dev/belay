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
  ((start.findTable (name! "history")).map Prod.snd).getD { columns := [] }

/-- The eleven pre-migration application fields used by the approved decoder. -/
def fields : List Identifier := [name! "id", name! "timestamp", name! "duration", name! "exit",
  name! "command", name! "cwd", name! "session", name! "hostname", name! "deleted_at", name! "author",
  name! "intent"]

end SchemaBinding
