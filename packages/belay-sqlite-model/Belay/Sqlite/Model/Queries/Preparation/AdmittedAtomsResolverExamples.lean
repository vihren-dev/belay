import Belay.Sqlite.Model.Queries.Fixtures.Examples
import Belay.Sqlite.Model.Shared.Catalog.Database
import Belay.Sqlite.Model.Shared.Resolved.Context

set_option doc.verso true

namespace Belay.Sqlite.Model.AdmittedAtomsResolverExamples

open Belay.Sqlite.Model Resolution.Examples

/-- The context of a script that runs. -/
def execution : ResolveContext := { profile := defaults, mode := .execution }

/-- Whether the resolution gives a catalog that is supported under the limits. -/
def validAfter : StatementResolution → Bool
  | .ok (_, catalog) => catalog.supported defaults.limits
  | .error _ => false

/-- The columns {lit}`a INTEGER, b TEXT`. -/
def twoColumns : List CatalogColumn :=
  [{ name := name! "a", declaredType := some "INTEGER" }, { name := name! "b", declaredType := some "TEXT" }]

end Belay.Sqlite.Model.AdmittedAtomsResolverExamples
