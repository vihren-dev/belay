import Belay.Sqlite.Model.Schema.Rows.PragmaResolution
import Belay.Sqlite.Model.Queries.Preparation.ViewTableInfo

set_option doc.verso true

/-! {lit}`PRAGMA table_info` of a view (ADR 0019, D5). SQLite reads the view's current columns
the way a query reads them, so the pragma reuses the select resolver: the rows describe the
columns of {lit}`SELECT * FROM view`. A view that SQLite cannot read gives the prepare error of
that query. -/

namespace Belay.Sqlite.Model

/-- Resolve a pragma statement: {lit}`PRAGMA table_info` of a view is {name}`resolveViewTableInfo`,
and every other pragma is {name}`resolvePragma`. -/
def resolveStatementPragma (context : ResolveContext) (state : ResolveState) :
    Syntax.Pragma → Except NodeRestriction (Resolved.Statement × ResolveState)
  | .tableInfo table =>
    if (state.catalog.findView table).isSome then resolveViewTableInfo context state table
    else resolvePragma state (.tableInfo table)
  | .setting setting value => resolvePragma state (.setting setting value)
  | .foreignKeyList table => resolvePragma state (.foreignKeyList table)
  | .check quick limit table => resolvePragma state (.check quick limit table)
  | .foreignKeyCheck table => resolvePragma state (.foreignKeyCheck table)

/-- For every context, state and table choice, the statement resolution of
{lit}`PRAGMA foreign_key_check` is {name}`resolvePragma`: a view-aware table_info does not
change it. Proof sketch: the definition has a separate case for table_info only. -/
theorem resolveStatementPragma_foreignKeyCheck (context : ResolveContext) (state : ResolveState)
    (table : Option Identifier) :
    resolveStatementPragma context state (.foreignKeyCheck table) = resolvePragma state (.foreignKeyCheck table) :=
  rfl

/-- The statement-level form of {name}`resolvePragma_cases`: for every context, state and pragma
that resolves, either a setting with a value sets the state, or the next state is the state, the
catalog is unchanged and the statement is not control. Proof sketch: a view branch yields a query
or a prepare error with the state unchanged; the other pragmas are {name}`resolvePragma_cases`. -/
theorem resolveStatementPragma_cases {context : ResolveContext} {state next : ResolveState}
    {pragma : Syntax.Pragma} {resolved : Resolved.Statement}
    (ok : resolveStatementPragma context state pragma = .ok (resolved, next)) :
    (∃ setting on, resolved = .setting setting on ∧ next = state.set on setting) ∨
      (next = state ∧ resolved.applyCatalog state.catalog = state.catalog ∧ resolved.isControl = false) := by
  unfold resolveStatementPragma at ok
  split at ok
  · split at ok
    · rename_i table found
      unfold resolveViewTableInfo at ok
      cases read : viewColumns context state.catalog table with
      | ok columns =>
        rw [read] at ok
        cases ok
        exact .inr ⟨rfl, rfl, rfl⟩
      | error issue =>
        rw [read] at ok
        cases issue with
        | noSuchTable name =>
          simp only [readIssueResolution, prepareError, Except.map] at ok
          cases ok
          exact .inr ⟨rfl, rfl, rfl⟩
        | value inner =>
          cases inner <;> simp only [readIssueResolution, issueResolution, prepareError, restrict, Except.map] at ok
          · cases ok
            exact .inr ⟨rfl, rfl, rfl⟩
          · cases ok
    · exact resolvePragma_cases ok
  all_goals exact resolvePragma_cases ok

end Belay.Sqlite.Model
