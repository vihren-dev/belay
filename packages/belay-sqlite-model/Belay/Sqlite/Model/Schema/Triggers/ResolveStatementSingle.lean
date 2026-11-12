import Belay.Sqlite.Model.Schema.Ddl.ResolveStatementSingleOthers
import Belay.Sqlite.Model.Queries.Preparation.ResolveStatementSingle

set_option doc.verso true

/-! Which statements can have more than one possible execution (ADR 0019, D4, amended 2026-10-25). Only
the resolver of INSERT from a query gives a statement without rules that is an INSERT from a query
({name}`Belay.Sqlite.Model.Resolved.Statement.fromQuery`); every other resolver gives a statement of
another form. So a script whose statements are no INSERT from a query has one execution for each of them. -/

namespace Belay.Sqlite.Model

/-- For every statement that is no INSERT from a query without rules and every rules: the write with the rules
({name}`Resolved.Statement.withRules`) is no INSERT from a query without rules. Proof sketch: the rules
change only the rules of a write, and a write with rules is not an INSERT without rules. -/
theorem Resolved.Statement.fromQuery_withRules {statement : Resolved.Statement} (rules : Resolved.WriteRules)
    (single : statement.fromQuery = false) : (statement.withRules rules).fromQuery = false := by
  cases statement <;> first | exact single | rfl

/-- For every context, state, resolution and result of {name}`ResolveState.withWrite`: if every statement of
the resolution is no INSERT from a query without rules, neither is the resolved statement of the result. Proof
sketch: each branch gives a prepare error, the statement, or the statement with rules
({name}`Resolved.Statement.fromQuery_withRules`). -/
theorem ResolveState.withWrite_single {context : ResolveContext} {state next : ResolveState}
    {result : StatementResolution} {resolved : Resolved.Statement}
    (ok : state.withWrite context result = .ok (resolved, next))
    (each : ∀ statement catalog, result = .ok (statement, catalog) → statement.fromQuery = false) :
    resolved.fromQuery = false := by
  unfold ResolveState.withWrite ResolveState.withCatalog at ok
  rcases result with _ | ⟨statement, catalog⟩
  · cases ok
  · simp only [Except.map, bind, Except.bind, pure, Except.pure] at ok
    repeat' split at ok
    all_goals first
      | (cases ok; rfl)
      | (cases ok; exact each _ _ rfl)
      | (cases ok; exact Resolved.Statement.fromQuery_withRules _ (each _ _ rfl))
      | cases ok

/-- For every context, state, statement that is no INSERT from a query and resolution: the resolved statement is
no INSERT from a query without rules ({name}`Resolved.Statement.fromQuery`), so its run has no alternative
execution. Plain words: only a statement that is written as INSERT from a query can have more than one possible
execution. Proof sketch: a case for each statement, with the lemma of its resolver ({name}`resolveCreateTable_single`
and the lemmas of the other resolvers); a write that checks keys keeps the claim
({name}`ResolveState.withWrite_single`). -/
theorem resolveStatement_single (context : ResolveContext) (state next : ResolveState)
    (statement : Syntax.Statement) (resolved : Resolved.Statement) (notQuery : statement.isInsertSelect = false)
    (ok : resolveStatement context state statement = .ok (resolved, next)) : resolved.fromQuery = false := by
  have plain : ∀ result, state.withCatalog result = .ok (resolved, next) →
      (∀ statement after, result = .ok (statement, after) → statement.fromQuery = false) →
      resolved.fromQuery = false := by
    intro result ok each
    rcases result with _ | ⟨statement, after⟩
    · cases ok
    · simp only [ResolveState.withCatalog, Except.map, Except.ok.injEq, Prod.mk.injEq] at ok
      obtain ⟨rfl, _⟩ := ok
      exact each _ _ rfl
  cases statement
  all_goals simp only [statement_arms] at ok
  case begin => cases ok; rfl
  case commit => cases ok; rfl
  case rollback => cases ok; rfl
  case createTable =>
    exact plain _ ok fun _ _ found => by
      rcases resolveCreateTableIf_cases found with ⟨rfl, _⟩ | found
      · rfl
      · exact resolveCreateTable_single _ _ _ _ _ _ _ _ found
  case createView => exact plain _ ok fun _ _ found => resolveCreateView_single _ _ _ _ _ _ found
  case createIndex =>
    exact plain _ ok fun _ _ found => by
      rcases resolveCreateIndexIf_cases found with ⟨rfl, _⟩ | found
      · rfl
      · exact resolveCreateIndex_single _ _ _ _ _ _ _ _ _ found
  case addColumn => exact plain _ ok fun _ _ found => resolveAddColumn_single _ _ _ _ _ _ _ found
  case renameTable =>
    exact plain _ ok fun _ _ found => by
      rcases resolveRenameTable_outcome _ _ _ _ _ _ found with ⟨_, _, rfl⟩ | ⟨rfl, _⟩ <;> rfl
  case renameColumn =>
    exact plain _ ok fun _ _ found => by
      rcases resolveRenameColumn_outcome _ _ _ _ _ _ _ _ _ found with ⟨_, _, rfl⟩ | ⟨rfl, _⟩ <;> rfl
  case dropColumn =>
    exact plain _ ok fun _ _ found => by
      rcases resolveDropColumn_outcome _ _ _ _ _ _ _ found with ⟨_, _, rfl⟩ | ⟨_, _, rfl, _⟩ <;> rfl
  case dropTable => exact ResolveState.withWrite_single ok fun _ _ found => resolveDropTable_single _ _ _ found
  case dropView => exact plain _ ok fun _ _ found => resolveDropView_single _ _ _ found
  case dropIndex => exact plain _ ok fun _ _ found => resolveDropIndex_single _ _ _ found
  case createTrigger => exact plain _ ok fun _ _ found => resolveCreateTrigger_single _ _ _ _ _ _ found
  case dropTrigger => exact plain _ ok fun _ _ found => resolveDropTrigger_single _ _ _ found
  case insert =>
    exact ResolveState.withWrite_single ok fun _ _ found => resolveCommonTableWrite_single _ _ _ _ _ _ _ _ _
      (fun _ _ _ _ _ h => resolveInsert_single _ _ _ _ _ _ _ _ _ _ _ _ h) found
  case insertSelect => simp [Syntax.Statement.isInsertSelect] at notQuery
  case update =>
    exact ResolveState.withWrite_single ok fun _ _ found => resolveCommonTableWrite_single _ _ _ _ _ _ _ _ _
      (fun _ _ _ _ _ h => resolveUpdate_single _ _ _ _ _ _ _ _ _ _ h) found
  case delete =>
    exact ResolveState.withWrite_single ok fun _ _ found => resolveCommonTableWrite_single _ _ _ _ _ _ _ _ _
      (fun _ _ _ _ _ h => resolveDelete_single _ _ _ _ _ _ _ _ _ h) found
  case pragma => exact resolveStatementPragma_single ok
  case select => exact plain _ ok fun _ _ found => resolveSelect_single _ _ _ _ _ _ found

end Belay.Sqlite.Model
