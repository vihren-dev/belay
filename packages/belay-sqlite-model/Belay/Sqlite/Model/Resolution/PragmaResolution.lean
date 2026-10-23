import Belay.Sqlite.Model.Resolution.ResolveState
import Belay.Sqlite.Model.Resolution.PragmaRows

set_option doc.verso true

/-! Resolution of the {lit}`PRAGMA` statements (ADR 0018, D4; ADR 0019, D2). A setting with a
value changes the setting of the state. Every other pragma is a query over the rows of the
pragma ({name}`Belay.Sqlite.Model.Resolved.Source.pragma`), with the columns of SQLite's
pragma, and leaves the state as it is. -/

namespace Belay.Sqlite.Model

/-- The query of the rows of a pragma with the names of its columns: each result column is
the cell at its position, and the query has no condition, order or window. -/
def pragmaQuery (rows : Resolved.PragmaRows) (names : List String) : Resolved.Query :=
  { sources := [{ kind := .inner, source := .pragma rows, condition := none }], filter := none,
    aggregate := false, groupBy := [], columns := (List.range names.length).map fun position => .scalar (.column position),
    names, orderBy := [], offset := 0, limit := none }

/-- The value of a setting in the state. -/
def ResolveState.setting (state : ResolveState) : Syntax.PragmaSetting → Bool
  | .foreignKeys => state.foreignKeys

/-- The query of a setting: one row with the column of its name ({name}`Syntax.PragmaSetting.sqlName`),
1 when the setting is on and 0 when it is off. -/
def settingQuery (setting : Syntax.PragmaSetting) (on : Bool) : Resolved.Statement :=
  .query (pragmaQuery (.fixed 1 [[.integer (if on then 1 else 0)]]) [setting.sqlName]) []

/-- The query of a check pragma with the limit, for the table at the catalog position or for
every table: one column with the name of the pragma ({name}`Syntax.checkName`). -/
def checkQuery (quick : Bool) (limit : Nat) (table : Option Nat) : Resolved.Statement :=
  .query (pragmaQuery (.check quick limit table) [Syntax.checkName quick]) []

/-- Resolve a pragma against the state:

* {lit}`PRAGMA foreign_keys = value` sets the setting outside a transaction and changes nothing
  inside one, as SQLite does ({name}`Resolved.Statement.setting`);
* the query of a setting is {name}`settingQuery` of its value in the state;
* {lit}`PRAGMA table_info(t)` is the query of {name}`Catalog.tableInfoRows`, and a name of SQLite's
  own tables that the catalog does not have is the restriction
  {name}`RestrictionKind.systemTable`;
* {lit}`PRAGMA foreign_key_list(t)` is the query of {name}`Catalog.foreignKeyListRows`;
* a check pragma is {name}`checkQuery` for every table, or for the named table; a name that
  the catalog does not have is SQLite's prepare error {lit}`no such table`, and a name of
  SQLite's own tables is the restriction {name}`RestrictionKind.systemTable`.

Every form except a setting with a value keeps the state. -/
def resolvePragma (state : ResolveState) : Syntax.Pragma → Except NodeRestriction (Resolved.Statement × ResolveState)
  | .setting .foreignKeys (some on) =>
    let foreignKeys := if state.saved.isSome then state.foreignKeys else on
    .ok (.setting foreignKeys, { state with foreignKeys })
  | .setting setting none => .ok (settingQuery setting (state.setting setting), state)
  | .tableInfo table => match state.catalog.tableInfoRows table with
    | some rows => .ok (.query (pragmaQuery (.fixed tableInfoNames.length rows) tableInfoNames) [], state)
    | none => .error { path := [], kind := .systemTable }
  | .foreignKeyList table =>
    .ok (.query (pragmaQuery (.fixed foreignKeyListNames.length (state.catalog.foreignKeyListRows table))
      foreignKeyListNames) [], state)
  | .check quick limit none => .ok (checkQuery quick limit none, state)
  | .check quick limit (some table) => match state.catalog.findTable table with
    | some (position, _) => .ok (checkQuery quick limit (some position), state)
    | none => if reservedName table then .error { path := [], kind := .systemTable }
      else .ok (.prepareError (.noSuchTable table), state)

/-- For every state and pragma that resolves, one of these holds:

* the result is a setting with the value {lit}`foreignKeys`, and the next state is the state
  with that setting;
* the next state is the state, the resolved statement leaves the catalog as it is
  ({name}`Resolved.Statement.applyCatalog`), and it is not control
  ({name}`Resolved.Statement.isControl`).

Proof sketch: by cases on the pragma; each branch is a definition. -/
theorem resolvePragma_cases {state next : ResolveState} {pragma : Syntax.Pragma} {resolved : Resolved.Statement}
    (ok : resolvePragma state pragma = .ok (resolved, next)) :
    (∃ foreignKeys, resolved = .setting foreignKeys ∧ next = { state with foreignKeys }) ∨
      (next = state ∧ resolved.applyCatalog state.catalog = state.catalog ∧ resolved.isControl = false) := by
  unfold resolvePragma at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact .inl ⟨_, rfl, rfl⟩)
    | (cases ok; exact .inr ⟨rfl, rfl, rfl⟩)
    | cases ok

end Belay.Sqlite.Model
