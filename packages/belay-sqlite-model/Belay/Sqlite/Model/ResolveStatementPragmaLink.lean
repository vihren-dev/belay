import Belay.Sqlite.Model.ResolveStatementForms
import Belay.Sqlite.Model.Resolution.ViewTableInfo

set_option doc.verso true

/-! The link of a resolved PRAGMA statement to its catalog (ADR 0022, D3, slice 4). A
{lit}`PRAGMA table_info` of a view reads the columns of the view
({lit}`viewColumns`), so its proof has a case for each result of that read. -/

namespace Belay.Sqlite.Model

/-- For every context, state and pragma statement that resolves ({name}`resolveStatementPragma`), the
resolved statement meets {name}`Resolved.Statement.SchemaLink` on the catalog of the state. Proof
sketch: a view branch is a query or a prepare error; every other pragma is
{name}`resolvePragma_schemaLink`. -/
theorem resolveStatementPragma_schemaLink {context : ResolveContext} {state next : ResolveState}
    {pragma : Syntax.Pragma} {resolved : Resolved.Statement}
    (ok : resolveStatementPragma context state pragma = .ok (resolved, next)) :
    resolved.SchemaLink state.catalog := by
  unfold resolveStatementPragma at ok
  split at ok
  · rename_i table
    split at ok
    · unfold resolveViewTableInfo at ok
      cases read : viewColumns context state.catalog table with
      | ok columns =>
        rw [read] at ok
        cases ok
        trivial
      | error issue =>
        rw [read] at ok
        cases issue with
        | noSuchTable name =>
          simp only [readIssueResolution, prepareError, Except.map] at ok
          cases ok
          trivial
        | value inner =>
          cases inner <;> simp only [readIssueResolution, issueResolution, prepareError, restrict, Except.map] at ok
          · cases ok
            trivial
          · cases ok
    · exact resolvePragma_schemaLink ok
  all_goals exact resolvePragma_schemaLink ok

end Belay.Sqlite.Model
