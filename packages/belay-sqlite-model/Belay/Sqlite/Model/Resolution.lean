import Belay.Sqlite.Model.Queries.Preparation.RestrictionRegistry
import Belay.Sqlite.Model.Schema.Writes.RowSpec
import Belay.Sqlite.Model.Schema.Dispatch.NamesSpecScript
import Belay.Sqlite.Model.Schema.Ddl.PrepareSpec
import Belay.Sqlite.Model.Schema.Triggers.UpdateSpec
import Belay.Sqlite.Model.Schema.Ddl.DefinitionSpec
import Belay.Sqlite.Model.Schema.Dispatch.TransactionSpec
import Belay.Sqlite.Model.Queries.Preparation.ErrorNames
import Belay.Sqlite.Model.Schema.Dispatch.SchemaScript

/-! Name resolution: statement syntax, the execution profile, the catalog, the resolved
statements and {lit}`resolve`, the resolution of a schema and a script, with the declarative specification of resolution and the
theorems that {lit}`resolve` meets it. Each module of {lit}`Belay/Sqlite/Model/Resolution/`
is one part; the package builds them all, and the examples run when it builds. -/
