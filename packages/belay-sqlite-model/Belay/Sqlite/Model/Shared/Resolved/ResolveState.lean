import Belay.Sqlite.Model.Shared.Resolved.StatementCatalog
import Belay.Sqlite.Model.Shared.Execution.StatementCounterReads
import Belay.Sqlite.Model.Shared.Resolved.Context

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The catalog during resolution, the catalog that the open transaction saved, and whether
foreign keys and recursive triggers are on. Omit {lit}`saved` outside a transaction, and
{lit}`foreignKeys` and {lit}`recursiveTriggers` for a setting that is off. -/
structure ResolveState where
  /-- The current catalog. -/
  catalog : Catalog
  /-- The catalog at BEGIN, while a transaction is open. -/
  saved : Option Catalog := none
  /-- Whether foreign keys are on ({lit}`PRAGMA foreign_keys`). -/
  foreignKeys : Bool := false
  /-- Whether a trigger fires again while it runs, and the rows that REPLACE deletes fire the
  DELETE triggers ({lit}`PRAGMA recursive_triggers`). -/
  recursiveTriggers : Bool := false
  deriving Repr, DecidableEq

/-- The state with the setting at the value. -/
def ResolveState.set (state : ResolveState) (on : Bool) : Syntax.PragmaSetting → ResolveState
  | .foreignKeys => { state with foreignKeys := on }
  | .recursiveTriggers => { state with recursiveTriggers := on }

/-- The state at the start of a script, outside a transaction: the catalog, with the settings
of the profile. -/
def ResolveState.initial (profile : Profile) (catalog : Catalog) : ResolveState :=
  { catalog, foreignKeys := profile.foreignKeys, recursiveTriggers := profile.recursiveTriggers }

/-- The value of a setting in the state. -/
def ResolveState.setting (state : ResolveState) : Syntax.PragmaSetting → Bool
  | .foreignKeys => state.foreignKeys
  | .recursiveTriggers => state.recursiveTriggers

/-- The state after a statement that is not transaction control: the catalog after
the statement, and the same saved catalog and setting. -/
def ResolveState.withCatalog (state : ResolveState) (result : StatementResolution) :
    Except NodeRestriction (Resolved.Statement × ResolveState) :=
  result.map fun (statement, catalog) => (statement, { state with catalog := catalog })

end Belay.Sqlite.Model
