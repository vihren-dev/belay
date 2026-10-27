import Belay.Sqlite.Model.Resolution.ApplyCatalogSpec
import Belay.Sqlite.Model.Resolution.WriteCatalogSpec
import Belay.Sqlite.Model.Resolution.DropSpec
import Belay.Sqlite.Model.Resolution.TriggerDefinitionSpec
import Belay.Sqlite.Model.Resolution.ViewDefinitionSpec
import Belay.Sqlite.Model.Resolution.RenameSpec

set_option doc.verso true

/-! The resolution state after a resolved statement. Resolution changes the catalog with
the catalog function of each statement ({name}`Belay.Sqlite.Model.Resolved.Statement.applyCatalog`),
and BEGIN, COMMIT and ROLLBACK change the saved catalog. The theorems here state that
{lit}`resolveStatement` and {lit}`resolveFrom` give exactly that state, so the catalog that
resolution predicts is a function of the resolved statements; {lit}`CatalogAgreement`
shows that execution reaches the same catalog. -/

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
  | statement@(.addColumn ..) | statement@(.rewrite _) | statement@(.drop ..)
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
  | createTable | createView | createIndex | createTrigger | addColumn | rewrite | drop | insert | update | upsert | insertSelect | delete
  | prepareError | query => rfl

/-- For every context, state and statement that resolves, the next state is
{name}`ResolveState.after` of the resolved statement. Proof sketch: transaction control
resolves to itself and {lit}`PRAGMA setting = value` to its setting; every other statement
gives a resolved statement that is not control and the catalog of
{name}`Resolved.Statement.applyCatalog`, by the lemma of its resolver, and a write that checks
foreign keys keeps both or is a prepare error that keeps the state
({name}`ResolveState.withWrite_cases`).
-/
theorem resolveStatement_after (context : ResolveContext) (state next : ResolveState)
    (statement : Syntax.Statement) (resolved : Resolved.Statement)
    (ok : resolveStatement context state statement = .ok (resolved, next)) :
    next = state.after resolved := by
  have ordinary : ∀ after, resolved.isControl = false → after = resolved.applyCatalog state.catalog →
      ({ state with catalog := after } : ResolveState) = state.after resolved := by
    intro after control equal
    rw [state.after_of_isControl control, equal]
  have written : ∀ result, state.withWrite context result = .ok (resolved, next) →
      (∀ statement after, result = .ok (statement, after) →
        after = statement.applyCatalog state.catalog ∧ statement.isControl = false) →
      next = state.after resolved := by
    intro result ok base
    rcases ResolveState.withWrite_cases ok with ⟨error, rfl, rfl⟩ | ⟨statement, after, rfl, rfl, catalog, kind⟩
    · rfl
    · obtain ⟨equal, control⟩ := base statement after rfl
      have resolvedControl : resolved.isControl = false := by
        simp only [Resolved.Statement.isControl, kind] at control ⊢
        exact control
      rw [state.after_of_isControl resolvedControl, catalog, equal]
  cases statement with
  | begin => cases ok; rfl
  | commit => cases ok; rfl
  | rollback => cases ok; rfl
  | createTable name columns constraints options =>
    simp only [statement_arms, ResolveState.withCatalog, Except.map] at ok
    split at ok <;> cases ok
    obtain ⟨equal, control⟩ := resolveCreateTable_applyCatalog _ _ _ _ _ _ _ _ (by assumption)
    exact ordinary _ control equal
  | createView name ifNotExists columns query subqueries =>
    simp only [statement_arms, ResolveState.withCatalog, Except.map] at ok
    split at ok <;> cases ok
    obtain ⟨equal, control⟩ := resolveCreateView_applyCatalog _ _ _ _ _ _ (by assumption)
    exact ordinary _ control equal
  | createIndex name unique table terms filter =>
    simp only [statement_arms, ResolveState.withCatalog, Except.map] at ok
    split at ok <;> cases ok
    obtain ⟨equal, control⟩ := resolveCreateIndex_applyCatalog _ _ _ _ _ _ _ _ _ (by assumption)
    exact ordinary _ control equal
  | addColumn table column =>
    simp only [statement_arms, ResolveState.withCatalog, Except.map] at ok
    split at ok <;> cases ok
    obtain ⟨equal, control⟩ := resolveAddColumn_applyCatalog _ _ _ _ _ _ _ (by assumption)
    exact ordinary _ control equal
  | renameTable table newName =>
    simp only [statement_arms, ResolveState.withCatalog, Except.map] at ok
    split at ok <;> cases ok
    obtain ⟨equal, control⟩ := (resolveRenameTable_outcome _ _ _ _ _ _ (by assumption)).applyCatalog
    exact ordinary _ control equal
  | renameColumn table column newName columnToken quoted =>
    simp only [statement_arms, ResolveState.withCatalog, Except.map] at ok
    split at ok <;> cases ok
    obtain ⟨equal, control⟩ := (resolveRenameColumn_outcome _ _ _ _ _ _ _ _ _ (by assumption)).applyCatalog
    exact ordinary _ control equal
  | dropTable name ifExists =>
    simp only [statement_arms] at ok
    exact written _ ok fun _ _ found => resolveDropTable_applyCatalog _ _ _ _ _ found
  | dropView name ifExists =>
    simp only [statement_arms, ResolveState.withCatalog, Except.map] at ok
    split at ok <;> cases ok
    obtain ⟨equal, control⟩ := resolveDropView_applyCatalog _ _ _ _ _ (by assumption)
    exact ordinary _ control equal
  | dropIndex name ifExists =>
    simp only [statement_arms, ResolveState.withCatalog, Except.map] at ok
    split at ok <;> cases ok
    obtain ⟨equal, control⟩ := resolveDropIndex_applyCatalog _ _ _ _ _ (by assumption)
    exact ordinary _ control equal
  | createTrigger name ifNotExists time event table condition body =>
    simp only [statement_arms, ResolveState.withCatalog, Except.map] at ok
    split at ok <;> cases ok
    obtain ⟨equal, control⟩ := resolveCreateTrigger_applyCatalog _ _ _ _ _ _ (by assumption)
    exact ordinary _ control equal
  | dropTrigger name ifExists =>
    simp only [statement_arms, ResolveState.withCatalog, Except.map] at ok
    split at ok <;> cases ok
    obtain ⟨equal, control⟩ := resolveDropTrigger_applyCatalog _ _ _ _ _ (by assumption)
    exact ordinary _ control equal
  | insert table columns rows conflicts algorithm returning subqueries =>
    simp only [statement_arms] at ok
    exact written _ ok fun _ _ found =>
      let ⟨same, unchanged, control⟩ := resolveCommonTableWrite_same _ _ _ _ _ _ _ _ _
        (fun _ _ _ _ _ h => resolveInsert_same _ _ _ _ _ _ _ _ _ _ _ _ h) found
      ⟨same.trans unchanged.symm, control⟩
  | insertSelect table columns body conflicts algorithm returning =>
    simp only [statement_arms] at ok
    exact written _ ok fun _ _ found =>
      let ⟨same, unchanged, control⟩ := resolveInsertQuery_same _ _ _ _ _ _ _ _ _ _ found
      ⟨same.trans unchanged.symm, control⟩
  | update table assignments filter returning subqueries =>
    simp only [statement_arms] at ok
    exact written _ ok fun _ _ found =>
      let ⟨same, unchanged, control⟩ := resolveCommonTableWrite_same _ _ _ _ _ _ _ _ _
        (fun _ _ _ _ _ h => resolveUpdate_same _ _ _ _ _ _ _ _ _ _ h) found
      ⟨same.trans unchanged.symm, control⟩
  | delete table filter returning subqueries =>
    simp only [statement_arms] at ok
    exact written _ ok fun _ _ found =>
      let ⟨same, unchanged, control⟩ := resolveCommonTableWrite_same _ _ _ _ _ _ _ _ _
        (fun _ _ _ _ _ h => resolveDelete_same _ _ _ _ _ _ _ _ _ h) found
      ⟨same.trans unchanged.symm, control⟩
  | pragma pragma =>
    rcases resolveStatementPragma_cases ok with ⟨_, _, rfl, rfl⟩ | ⟨rfl, unchanged, control⟩
    · rfl
    · exact ordinary _ control unchanged.symm
  | select results source joins filter groupBy orderBy limit offset subqueries having distinct =>
    simp only [statement_arms, ResolveState.withCatalog, Except.map] at ok
    split at ok <;> cases ok
    obtain ⟨same, unchanged, control⟩ := resolveSelect_same _ _ _ _ _ _ (by assumption)
    exact ordinary _ control (same.trans unchanged.symm)

end Belay.Sqlite.Model
