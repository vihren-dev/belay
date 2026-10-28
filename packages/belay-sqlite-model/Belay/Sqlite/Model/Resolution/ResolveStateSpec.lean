import Belay.Sqlite.Model.Resolution.ResolveState

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The resolution state after the statement: BEGIN saves the catalog unless a catalog is
already saved, COMMIT drops the saved catalog, ROLLBACK restores it, a setting pragma sets the
setting that it carries ({name}`ResolveState.set`), and every other statement applies
{name}`Resolved.Statement.applyCatalog` to the catalog and keeps the saved one. Every statement
keeps the settings, except the setting pragma. -/
def ResolveState.after (state : ResolveState) : Resolved.Statement → ResolveState
  | .begin => { state with saved := state.saved.getD state.catalog }
  | .commit => { state with saved := none }
  | .rollback => { state with catalog := state.saved.getD state.catalog, saved := none }
  | .setting setting on => state.set on setting
  | statement@(.createTable ..) | statement@(.createView ..) | statement@(.createIndex ..) | statement@(.createTrigger ..)
  | statement@(.addColumn ..) | statement@(.rewrite _) | statement@(.dropColumn ..) | statement@(.drop ..)
  | statement@(.insert ..) | statement@(.update ..) | statement@(.upsert ..) | statement@(.insertSelect ..) | statement@(.delete ..)
  | statement@(.prepareError _) | statement@(.query ..) =>
    { state with catalog := statement.applyCatalog state.catalog }

/-- For every state and statement that is not transaction control or a setting
({name}`Resolved.Statement.isControl`), {name}`ResolveState.after` applies the statement's
catalog change and keeps the saved catalog and the settings. Proof sketch: case analysis on the
statement: BEGIN, COMMIT, ROLLBACK and the setting contradict the premise, and every other
constructor is the definition. -/
theorem ResolveState.after_of_isControl (state : ResolveState) {statement : Resolved.Statement}
    (ordinary : statement.isControl = false) :
    state.after statement = { state with catalog := statement.applyCatalog state.catalog } := by
  cases statement with
  | begin | commit | rollback | setting => cases ordinary
  | createTable | createView | createIndex | createTrigger | addColumn | rewrite | dropColumn | drop | insert | update | upsert | insertSelect | delete
  | prepareError | query => rfl

/-- The resolution state is valid under the limits: the current catalog is valid
({name}`Catalog.Valid`), and so is the catalog that an open transaction saved, if there is one. -/
def ResolveState.Valid (limits : Limits) (state : ResolveState) : Prop :=
  state.catalog.Valid limits ∧ ∀ saved, state.saved = some saved → saved.Valid limits

/-! The current and saved catalog properties used by resolver proofs.
{name}`Belay.Sqlite.Model.ResolveState.after` describes transaction and setting changes;
{name}`Belay.Sqlite.Model.ResolveState.Valid` requires both catalogs to be valid. -/

end Belay.Sqlite.Model
