import Belay.Sqlite.Model.Schema.Ddl.StatementArms
import Belay.Sqlite.Model.Schema.Dispatch.StatementArms

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every state, pragma that only reads ({name}`Syntax.Pragma.readsOnly`) and result of its resolution:
the resolved statement is a query or a prepare error. In plain words, a pragma without a value never
resolves to a statement that writes. Proof sketch: by cases on the pragma; the rows of each pragma are a
query ({name}`pragmaQuery`), and a refused one is a prepare error. -/
theorem resolvePragma_readOnly {state next : ResolveState} {pragma : Syntax.Pragma} {resolved : Resolved.Statement}
    (reads : pragma.readsOnly = true) (ok : resolvePragma state pragma = .ok (resolved, next)) :
    (∃ query subqueries, resolved = .query query subqueries) ∨ ∃ error, resolved = .prepareError error := by
  cases pragma with
  | setting setting value =>
    cases value with
    | some on => simp [Syntax.Pragma.readsOnly] at reads
    | none =>
      simp only [resolvePragma, Except.ok.injEq, Prod.mk.injEq] at ok
      obtain ⟨rfl, -⟩ := ok
      exact .inl ⟨_, _, rfl⟩
  | tableInfo table =>
    unfold resolvePragma at ok
    repeat' split at ok
    all_goals first
      | contradiction
      | (cases ok; exact .inl ⟨_, _, rfl⟩)
      | (cases ok; exact .inr ⟨_, rfl⟩)
      | cases ok
  | foreignKeyList table =>
    simp only [resolvePragma, Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨rfl, -⟩ := ok
    exact .inl ⟨_, _, rfl⟩
  | check quick limit table =>
    unfold resolvePragma at ok
    repeat' split at ok
    all_goals first
      | contradiction
      | (cases ok; exact .inl ⟨_, _, rfl⟩)
      | (cases ok; exact .inr ⟨_, rfl⟩)
      | cases ok
  | foreignKeyCheck table =>
    unfold resolvePragma at ok
    repeat' split at ok
    all_goals first
      | contradiction
      | (cases ok; exact .inl ⟨_, _, rfl⟩)
      | (cases ok; exact .inr ⟨_, rfl⟩)
      | cases ok

/-- For every context, state, pragma that only reads and result of the resolution of the pragma as a
statement: the resolved statement is a query or a prepare error. In plain words, as
{name}`resolvePragma_readOnly`, also for the metadata of a view. Proof sketch: the view branch gives a
query of the columns of the view or a prepare error, and the other branches are
{name}`resolvePragma_readOnly`. -/
theorem resolveStatementPragma_readOnly {context : ResolveContext} {state next : ResolveState}
    {pragma : Syntax.Pragma} {resolved : Resolved.Statement} (reads : pragma.readsOnly = true)
    (ok : resolveStatementPragma context state pragma = .ok (resolved, next)) :
    (∃ query subqueries, resolved = .query query subqueries) ∨ ∃ error, resolved = .prepareError error := by
  unfold resolveStatementPragma at ok
  split at ok
  · split at ok
    · unfold resolveViewTableInfo at ok
      cases read : viewColumns context state.catalog _ with
      | ok columns =>
        rw [read] at ok
        cases ok
        exact .inl ⟨_, _, rfl⟩
      | error issue =>
        rw [read] at ok
        cases issue with
        | noSuchTable name =>
          simp only [readIssueResolution, prepareError, Except.map] at ok
          cases ok
          exact .inr ⟨_, rfl⟩
        | value inner =>
          cases inner <;> simp only [readIssueResolution, issueResolution, prepareError, restrict, Except.map] at ok
          · cases ok
            exact .inr ⟨_, rfl⟩
          · cases ok
    · exact resolvePragma_readOnly reads ok
  all_goals exact resolvePragma_readOnly reads ok

end Belay.Sqlite.Model
