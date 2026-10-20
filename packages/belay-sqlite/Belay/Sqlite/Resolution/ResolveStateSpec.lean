import Belay.Sqlite.Resolution.WriteCatalogSpec

set_option doc.verso true

/-! The resolution state after a resolved statement. Resolution changes the catalog with
the catalog function of each statement ({name}`Belay.Sqlite.Resolved.Statement.applyCatalog`),
and BEGIN, COMMIT and ROLLBACK change the saved catalog. The theorems here state that
{lit}`resolveStatement` and {lit}`resolveFrom` give exactly that state, so the catalog that
resolution predicts is a function of the resolved statements; {lit}`CatalogAgreement`
shows that execution reaches the same catalog. -/

namespace Belay.Sqlite

/-- The resolution state after the statement: BEGIN saves the catalog unless a catalog is
already saved, COMMIT drops the saved catalog, ROLLBACK restores it, and every other
statement applies {name}`Resolved.Statement.applyCatalog` to the catalog and keeps the
saved one. -/
def ResolveState.after (state : ResolveState) : Resolved.Statement → ResolveState
  | .begin => { state with saved := state.saved.getD state.catalog }
  | .commit => { state with saved := none }
  | .rollback => { catalog := state.saved.getD state.catalog, saved := none }
  | statement@(.createTable ..) | statement@(.createIndex ..) | statement@(.addColumn ..) | statement@(.drop _)
  | statement@(.insert ..) | statement@(.update ..) | statement@(.upsert ..) | statement@(.delete ..)
  | statement@(.prepareError _) | statement@(.query _) =>
    { state with catalog := statement.applyCatalog state.catalog }

/-- For every state and statement that is not transaction control
({name}`Resolved.Statement.isControl`), {name}`ResolveState.after` applies the statement's
catalog change and keeps the saved catalog. Proof sketch: case analysis on the statement:
BEGIN, COMMIT and ROLLBACK contradict the premise, and every other constructor is the
definition. -/
theorem ResolveState.after_of_isControl (state : ResolveState) {statement : Resolved.Statement}
    (ordinary : statement.isControl = false) :
    state.after statement = { state with catalog := statement.applyCatalog state.catalog } := by
  cases statement with
  | begin | commit | rollback => cases ordinary
  | createTable | createIndex | addColumn | drop | insert | update | upsert | delete | prepareError | query => rfl

/-- For every successful resolution of CREATE TABLE, the catalog after it is
{name}`Resolved.Statement.applyCatalog` of the resolved statement, which is not
transaction control. Proof sketch: every branch returns the input catalog with a prepare
error, or the CREATE TABLE at the end of the catalog with {name}`Catalog.createTable`. -/
theorem resolveCreateTable_applyCatalog (context : ResolveContext) (catalog after : Catalog) (index : Nat)
    (name : Identifier) (columns : List Syntax.ColumnDefinition) (constraints : List Syntax.TableConstraint)
    (options : Syntax.TableOptions) (statement : Resolved.Statement)
    (ok : resolveCreateTable context catalog index name columns constraints options = .ok (statement, after)) :
    after = statement.applyCatalog catalog ∧ statement.isControl = false := by
  unfold resolveCreateTable at ok
  simp only [issueResolution, prepareError, restrict] at ok
  repeat' split at ok
  all_goals first | (cases ok; exact ⟨rfl, rfl⟩) | (cases ok)

/-- For every successful resolution of CREATE INDEX, the catalog after it is
{name}`Resolved.Statement.applyCatalog` of the resolved statement, which is not
transaction control. Proof sketch: as for CREATE TABLE, with {name}`Catalog.createIndex`.
-/
theorem resolveCreateIndex_applyCatalog (context : ResolveContext) (catalog after : Catalog) (index : Nat)
    (name : Identifier) (unique : Bool) (tableName : Identifier) (terms : List Syntax.OrderTerm)
    (filter : Option Syntax.Expr)
    (statement : Resolved.Statement)
    (ok : resolveCreateIndex context catalog index name unique tableName terms filter = .ok (statement, after)) :
    after = statement.applyCatalog catalog ∧ statement.isControl = false := by
  unfold resolveCreateIndex at ok
  simp only [issueResolution, prepareError, restrict] at ok
  repeat' split at ok
  all_goals first | (cases ok; exact ⟨rfl, rfl⟩) | (cases ok)

/-- For every successful resolution of ADD COLUMN, the catalog after it is
{name}`Resolved.Statement.applyCatalog` of the resolved statement, which is not
transaction control. Proof sketch: as for CREATE TABLE, with {name}`Catalog.addColumn`. -/
theorem resolveAddColumn_applyCatalog (context : ResolveContext) (catalog after : Catalog) (index : Nat)
    (tableName : Identifier) (definition : Syntax.ColumnDefinition) (statement : Resolved.Statement)
    (ok : resolveAddColumn context catalog index tableName definition = .ok (statement, after)) :
    after = statement.applyCatalog catalog ∧ statement.isControl = false := by
  unfold resolveAddColumn at ok
  simp only [prepareError, restrict] at ok
  repeat' split at ok
  all_goals first | (cases ok; exact ⟨rfl, rfl⟩) | (cases ok)

/-- For every successful resolution of DROP TABLE, the catalog after it is
{name}`Resolved.Statement.applyCatalog` of the resolved statement, which is not
transaction control. Proof sketch: every branch returns the input catalog with a prepare
error, or a drop with {name}`Catalog.drop` of its positions. -/
theorem resolveDropTable_applyCatalog (catalog after : Catalog) (name : Identifier) (ifExists : Bool)
    (statement : Resolved.Statement) (ok : resolveDropTable catalog name ifExists = .ok (statement, after)) :
    after = statement.applyCatalog catalog ∧ statement.isControl = false := by
  unfold resolveDropTable at ok
  simp only [prepareError] at ok
  repeat' split at ok
  all_goals first | (cases ok; exact ⟨rfl, rfl⟩) | (cases ok)

/-- For every successful resolution of DROP INDEX, the catalog after it is
{name}`Resolved.Statement.applyCatalog` of the resolved statement, which is not
transaction control. Proof sketch: as for DROP TABLE. -/
theorem resolveDropIndex_applyCatalog (catalog after : Catalog) (index : Nat) (name : Identifier)
    (ifExists : Bool) (statement : Resolved.Statement)
    (ok : resolveDropIndex catalog index name ifExists = .ok (statement, after)) :
    after = statement.applyCatalog catalog ∧ statement.isControl = false := by
  unfold resolveDropIndex at ok
  simp only [prepareError, restrict] at ok
  repeat' split at ok
  all_goals first | (cases ok; exact ⟨rfl, rfl⟩) | (cases ok)

/-- For every context, state, index and statement that resolves, the next state is
{name}`ResolveState.after` of the resolved statement. Proof sketch: transaction control
resolves to itself; every other statement gives a resolved statement that is not control
and the catalog of {name}`Resolved.Statement.applyCatalog`, by the lemma of its resolver.
-/
theorem resolveStatement_after (context : ResolveContext) (state next : ResolveState) (index : Nat)
    (statement : Syntax.Statement) (resolved : Resolved.Statement)
    (ok : resolveStatement context state index statement = .ok (resolved, next)) :
    next = state.after resolved := by
  have ordinary : ∀ after, resolved.isControl = false → after = resolved.applyCatalog state.catalog →
      ({ state with catalog := after } : ResolveState) = state.after resolved := by
    intro after control equal
    rw [state.after_of_isControl control, equal]
  cases statement with
  | begin => cases ok; rfl
  | commit => cases ok; rfl
  | rollback => cases ok; rfl
  | createTable name columns constraints options =>
    simp only [resolveStatement, ResolveState.withCatalog, Except.map] at ok
    split at ok <;> cases ok
    obtain ⟨equal, control⟩ := resolveCreateTable_applyCatalog _ _ _ _ _ _ _ _ _ (by assumption)
    exact ordinary _ control equal
  | createIndex name unique table terms filter =>
    simp only [resolveStatement, ResolveState.withCatalog, Except.map] at ok
    split at ok <;> cases ok
    obtain ⟨equal, control⟩ := resolveCreateIndex_applyCatalog _ _ _ _ _ _ _ _ _ _ (by assumption)
    exact ordinary _ control equal
  | addColumn table column =>
    simp only [resolveStatement, ResolveState.withCatalog, Except.map] at ok
    split at ok <;> cases ok
    obtain ⟨equal, control⟩ := resolveAddColumn_applyCatalog _ _ _ _ _ _ _ (by assumption)
    exact ordinary _ control equal
  | dropTable name ifExists =>
    simp only [resolveStatement, ResolveState.withCatalog, Except.map] at ok
    split at ok <;> cases ok
    obtain ⟨equal, control⟩ := resolveDropTable_applyCatalog _ _ _ _ _ (by assumption)
    exact ordinary _ control equal
  | dropIndex name ifExists =>
    simp only [resolveStatement, ResolveState.withCatalog, Except.map] at ok
    split at ok <;> cases ok
    obtain ⟨equal, control⟩ := resolveDropIndex_applyCatalog _ _ _ _ _ _ (by assumption)
    exact ordinary _ control equal
  | insert table columns rows conflicts algorithm returning =>
    simp only [resolveStatement, ResolveState.withCatalog, Except.map] at ok
    split at ok <;> cases ok
    obtain ⟨same, unchanged, control⟩ := resolveInsert_same _ _ _ _ _ _ _ _ _ _ _ (by assumption)
    exact ordinary _ control (same.trans unchanged.symm)
  | update table assignments filter returning =>
    simp only [resolveStatement, ResolveState.withCatalog, Except.map] at ok
    split at ok <;> cases ok
    obtain ⟨same, unchanged, control⟩ := resolveUpdate_same _ _ _ _ _ _ _ _ _ (by assumption)
    exact ordinary _ control (same.trans unchanged.symm)
  | delete table filter returning =>
    simp only [resolveStatement, ResolveState.withCatalog, Except.map] at ok
    split at ok <;> cases ok
    obtain ⟨same, unchanged, control⟩ := resolveDelete_same _ _ _ _ _ _ _ _ (by assumption)
    exact ordinary _ control (same.trans unchanged.symm)
  | select results source joins filter groupBy orderBy limit offset =>
    simp only [resolveStatement, ResolveState.withCatalog, Except.map] at ok
    split at ok <;> cases ok
    obtain ⟨same, unchanged, control⟩ := resolveSelect_same _ _ _ _ _ _ _ _ _ _ _ _ _ (by assumption)
    exact ordinary _ control (same.trans unchanged.symm)

/-- For every context, script, index and state with a successful resolution, the final
state is the fold of {name}`ResolveState.after` over the resolved statements. Proof
sketch: induction on the script with {name}`resolveStatement_after`. -/
theorem resolveFrom_after (context : ResolveContext) :
    ∀ (script : List Syntax.Statement) (index : Nat) (state final : ResolveState)
      (resolved : List Resolved.Statement),
      resolveFrom context index state script = .ok (resolved, final) →
      final = resolved.foldl ResolveState.after state
  | [], index, state, final, resolved, ok => by
    simp only [resolveFrom] at ok
    cases ok
    rfl
  | statement :: rest, index, state, final, resolved, ok => by
    simp only [resolveFrom, bind, Except.bind] at ok
    split at ok
    · cases ok
    · rename_i first headOk
      split at ok
      · cases ok
      · rename_i later restOk
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at ok
        obtain ⟨rfl, rfl⟩ := ok
        have head := resolveStatement_after context state first.2 index statement first.1 headOk
        have tail := resolveFrom_after context rest (index + 1) first.2 later.2 later.1 restOk
        rw [List.foldl_cons, ← head]
        exact tail

/-- For every context, catalog and script with a successful resolution, the resulting
catalog is the catalog of the fold of {name}`ResolveState.after` over the resolved
statements from the catalog outside a transaction. Proof sketch: unfold {name}`resolve`; a
restriction contradicts the premise, and a resolution is the state of
{name}`resolveFrom_after` from position zero outside a transaction. -/
theorem resolve_after (context : ResolveContext) (catalog next : Catalog) (script : List Syntax.Statement)
    (resolved : List Resolved.Statement) (ok : resolve context catalog script = .resolved resolved next) :
    next = (resolved.foldl ResolveState.after { catalog }).catalog := by
  unfold resolve at ok
  split at ok
  · rename_i result found
    cases ok
    rw [resolveFrom_after context script 0 _ _ _ found]
  · cases ok

end Belay.Sqlite
