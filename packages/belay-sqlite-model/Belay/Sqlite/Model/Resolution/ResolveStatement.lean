import Belay.Sqlite.Model.Resolution.SelectResolution
import Belay.Sqlite.Model.Resolution.WriteResolution
import Belay.Sqlite.Model.Resolution.InsertQueries
import Belay.Sqlite.Model.Resolution.CommonTableWrites
import Belay.Sqlite.Model.Resolution.StatementCatalog
import Belay.Sqlite.Model.Resolution.Updates
import Belay.Sqlite.Model.Resolution.Deletes
import Belay.Sqlite.Model.Resolution.Drops
import Belay.Sqlite.Model.Resolution.Renames
import Belay.Sqlite.Model.Resolution.ViewDefinitions
import Belay.Sqlite.Model.Resolution.ResolveState
import Belay.Sqlite.Model.Resolution.TriggerDefinitions
import Belay.Sqlite.Model.Resolution.PragmaResolution
import Belay.Sqlite.Model.Resolution.ViewTableInfo
import Belay.Sqlite.Model.Resolution.StatementTraced

set_option doc.verso true

/-! Name resolution of one statement against the state of a script, with the name trace. -/

namespace Belay.Sqlite.Model

/-- Resolve one statement against the state with the name trace, as the resolver run decides it, before
the constraints of the columns are added. BEGIN in an open transaction and
COMMIT or ROLLBACK without one fail when SQLite runs them, not when it prepares
them, so they resolve and leave the error to the execution semantics: such a BEGIN
keeps the first saved catalog, and such a ROLLBACK keeps the current catalog.
A pragma resolves with {name}`resolveStatementPragma`: {lit}`PRAGMA foreign_keys = value` changes the
state's setting outside a transaction and nothing inside one, as SQLite does, and
{lit}`PRAGMA recursive_triggers = value` changes it also inside one. SELECT and supported
writes expand ordinary WITH definitions before their expressions resolve. A statement that is not
SELECT, INSERT, UPDATE or DELETE has no trace. INSERT from a query resolves with
{name}`resolveInsertQueryTraced`. -/
def resolveStatementRun (context : ResolveContext) (state : ResolveState) :
    Syntax.Statement → Traced NodeRestriction (Resolved.Statement × ResolveState)
  | .begin => pure (.begin, { state with saved := state.saved.getD state.catalog })
  | .commit => pure (.commit, { state with saved := none })
  | .rollback => pure (.rollback, { state with catalog := state.saved.getD state.catalog, saved := none })
  | .pragma pragma => Traced.lift (resolveStatementPragma context state pragma)
  | .createTable name columns constraints options =>
    Traced.lift (state.withCatalog (resolveCreateTable context state.catalog name columns constraints options))
  | .createView name ifNotExists columns query subqueries =>
    Traced.lift (state.withCatalog (resolveCreateView state.catalog name ifNotExists { columns, query, subqueries }))
  | .createIndex name unique table terms filter =>
    Traced.lift (state.withCatalog (resolveCreateIndex context state.catalog name unique table terms filter))
  | .addColumn table column =>
    Traced.lift (state.withCatalog (resolveAddColumn context state.catalog state.foreignKeys table column))
  | .renameTable table newName => Traced.lift (state.withCatalog (resolveRenameTable context state.catalog table newName))
  | .renameColumn table column newName columnToken quoted =>
    Traced.lift (state.withCatalog (resolveRenameColumn context state.catalog table column newName columnToken quoted))
  | .dropColumn table column columnToken =>
    Traced.lift (state.withCatalog (resolveDropColumn context state.catalog table column columnToken))
  | .dropTable name ifExists => Traced.lift (state.withWrite context (resolveDropTable state.catalog name ifExists))
  | .dropView name ifExists => Traced.lift (state.withCatalog (resolveDropView state.catalog name ifExists))
  | .dropIndex name ifExists => Traced.lift (state.withCatalog (resolveDropIndex state.catalog name ifExists))
  | .createTrigger name ifNotExists time event table condition body =>
    Traced.lift (state.withCatalog (resolveCreateTrigger state.catalog name ifNotExists
      { table, time, event, condition, body }))
  | .dropTrigger name ifExists => Traced.lift (state.withCatalog (resolveDropTrigger state.catalog name ifExists))
  | .insert table columns rows conflicts algorithm returning subqueries =>
    state.withWriteTraced context (resolveCommonTableWriteTraced context state.catalog 6 table (fun _ => [])
      subqueries (fun index => resolveInsertTraced context state.catalog table columns
        (rows.map (List.map (Syntax.Expr.reindex index))) conflicts algorithm returning))
  | .insertSelect table columns body conflicts algorithm returning =>
    state.withWriteTraced context
      (resolveInsertQueryTraced context state.catalog table columns body conflicts algorithm returning)
  | .update table assignments filter returning subqueries =>
    state.withWriteTraced context (resolveCommonTableWriteTraced context state.catalog 4 table (writtenScope table)
      subqueries (fun index => resolveUpdateTraced context state.catalog table
        (assignments.map fun (name, value) => (name, value.reindex index))
        (filter.map (Syntax.Expr.reindex index)) returning))
  | .select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound =>
    state.withCatalogTraced (resolveSelectTraced context state.catalog
      { columns, source, joins, filter, groupBy, orderBy, limit, offset, parent := none, having, distinct, compound }
      subqueries)
  | .delete table filter returning subqueries =>
    state.withWriteTraced context (resolveCommonTableWriteTraced context state.catalog 3 table (writtenScope table)
      subqueries (fun index => resolveDeleteTraced context state.catalog table
        (filter.map (Syntax.Expr.reindex index)) returning))

/-- Resolve one statement against the state and give the names that the resolver decided: the result
of {lit}`resolveStatement` and the trace of the run ({name}`resolveStatementRun`) with the
constraints of the columns from the catalog ({name}`NameTrace.withConstraints`). The trace is also given
when the statement fails; then it ends with the failing name and its candidates. The names of stored trigger programs, of DDL bodies and of the
other documented gaps are not in it (see the status file of the task). -/
def resolveStatementTraced (context : ResolveContext) (state : ResolveState) (statement : Syntax.Statement) :
    Except NodeRestriction (Resolved.Statement × ResolveState) × NameTrace :=
  let run := resolveStatementRun context state statement
  (run.drop, run.trace.withConstraints state.catalog)

/-- Resolve one statement against the state, with no statement index: a restriction is one
inside the statement ({name}`NodeRestriction`). It is the result of
{name}`resolveStatementTraced` without the trace, so the two cannot disagree. -/
def resolveStatement (context : ResolveContext) (state : ResolveState) (statement : Syntax.Statement) :
    Except NodeRestriction (Resolved.Statement × ResolveState) :=
  (resolveStatementTraced context state statement).1

end Belay.Sqlite.Model
