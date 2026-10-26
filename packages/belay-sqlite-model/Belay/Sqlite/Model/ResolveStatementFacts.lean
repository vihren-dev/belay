import Belay.Sqlite.Model.ResolveStatementLink
import Belay.Sqlite.Model.ResolveStatementPragmaLink

set_option doc.verso true

/-! The facts that the resolver gives for every resolved statement (ADR 0022, D3, slice 4), for a valid
resolution state in execution mode: the catalog after the statement is valid, a CREATE INDEX has an
index that is supported for the width of its table, an ADD COLUMN has a default that fits the strict type,
and a DROP meets {lit}`Catalog.DropClosed`. They discharge the conditions of the statement theorems of
{lit}`runScriptFrom`. -/

namespace Belay.Sqlite.Model

/-- For every context, state, statement and resolution: if the catalog of the state is valid, the resolved
statement meets {name}`Resolved.Statement.SchemaLink` on the catalog of the state. Proof sketch: a case for
each statement, with the lemma of its resolver ({name}`resolveAddColumn_schemaLink`,
{name}`resolveDropTable_schemaLink`, {name}`resolveDropIndex_schemaLink`,
{name}`resolveDropTrigger_schemaLink` and the lemmas of the other resolvers); a write that checks keys
keeps the link ({name}`ResolveState.withWrite_schemaLink`). -/
theorem resolveStatement_schemaLink {limits : Limits} (context : ResolveContext) (state next : ResolveState)
    (statement : Syntax.Statement) (resolved : Resolved.Statement) (valid : state.catalog.Valid limits)
    (ok : resolveStatement context state statement = .ok (resolved, next)) : resolved.SchemaLink state.catalog := by
  have plain : ∀ result, state.withCatalog result = .ok (resolved, next) →
      (∀ statement after, result = .ok (statement, after) → statement.SchemaLink state.catalog) →
      resolved.SchemaLink state.catalog := by
    intro result ok each
    rcases result with _ | ⟨statement, after⟩
    · cases ok
    · simp only [ResolveState.withCatalog, Except.map, Except.ok.injEq, Prod.mk.injEq] at ok
      obtain ⟨rfl, _⟩ := ok
      exact each _ _ rfl
  cases statement
  all_goals simp only [statement_arms] at ok
  case begin => cases ok; trivial
  case commit => cases ok; trivial
  case rollback => cases ok; trivial
  case createTable =>
    exact plain _ ok fun _ _ found => resolveCreateTable_schemaLink _ _ _ _ _ _ _ _ found
  case createView =>
    exact plain _ ok fun _ _ found => resolveCreateView_schemaLink _ _ _ _ _ _ found
  case createIndex =>
    exact plain _ ok fun _ _ found => resolveCreateIndex_schemaLink _ _ _ _ _ _ _ _ _ found
  case addColumn =>
    exact plain _ ok fun _ _ found => resolveAddColumn_schemaLink _ _ _ _ _ _ _ found
  case renameTable =>
    exact plain _ ok fun _ _ found => by
      obtain ⟨_, _, rfl⟩ := resolveRenameTable_unchanged _ _ _ _ _ found
      trivial
  case renameColumn =>
    exact plain _ ok fun _ _ found => by
      obtain ⟨_, _, rfl⟩ := resolveRenameColumn_unchanged _ _ _ _ _ _ found
      trivial
  case dropTable =>
    exact ResolveState.withWrite_schemaLink ok fun _ _ found => resolveDropTable_schemaLink _ _ _ valid found
  case dropView =>
    exact plain _ ok fun _ _ found => resolveDropView_schemaLink _ _ _ valid found
  case dropIndex =>
    exact plain _ ok fun _ _ found => resolveDropIndex_schemaLink _ _ _ valid found
  case createTrigger =>
    exact plain _ ok fun _ _ found => resolveCreateTrigger_schemaLink _ _ _ _ _ _ found
  case dropTrigger =>
    exact plain _ ok fun _ _ found => resolveDropTrigger_schemaLink _ _ _ valid found
  case insert =>
    exact ResolveState.withWrite_schemaLink ok fun _ _ found => resolveCommonTableWrite_schemaLink _ _ _ _ _ _ _ _ _
      (fun _ _ _ _ _ h => resolveInsert_schemaLink _ _ _ _ _ _ _ _ _ _ _ _ h) found
  case insertSelect =>
    exact ResolveState.withWrite_schemaLink ok fun _ _ found => by
      obtain ⟨_, ⟨_, rfl⟩ | ⟨_, _, _, _, _, _, _, rfl⟩⟩ := resolveInsertQuery_form _ _ _ _ _ _ _ _ _ _ found <;>
        trivial
  case update =>
    exact ResolveState.withWrite_schemaLink ok fun _ _ found => resolveCommonTableWrite_schemaLink _ _ _ _ _ _ _ _ _
      (fun _ _ _ _ _ h => resolveUpdate_schemaLink _ _ _ _ _ _ _ _ _ _ h) found
  case delete =>
    exact ResolveState.withWrite_schemaLink ok fun _ _ found => resolveCommonTableWrite_schemaLink _ _ _ _ _ _ _ _ _
      (fun _ _ _ _ _ h => resolveDelete_schemaLink _ _ _ _ _ _ _ _ _ h) found
  case pragma => exact resolveStatementPragma_schemaLink ok
  case select =>
    exact plain _ ok fun _ _ found => resolveSelect_schemaLink _ _ _ _ _ _ found

end Belay.Sqlite.Model
