import Belay.Sqlite.Resolution.SelectResolution
import Belay.Sqlite.Resolution.WriteResolution
import Belay.Sqlite.Resolution.StatementCatalog
import Belay.Sqlite.Resolution.Updates
import Belay.Sqlite.Resolution.Deletes
import Belay.Sqlite.Resolution.Drops
import Belay.Sqlite.Resolution.ResolveState
import Belay.Sqlite.Resolution.TriggerDefinitions

set_option doc.verso true

/-! Name resolution of a script. Each statement is resolved against the catalog
that the earlier statements leave when they succeed. BEGIN saves the catalog,
ROLLBACK restores it and COMMIT drops the saved copy. Resolution also follows the
setting of {lit}`PRAGMA foreign_keys`, which no ROLLBACK undoes, and gives each write the
foreign keys that it must check (ADR 0018, D4). A statement after a prepare
error is resolved as if that statement had no effect: SQLite never runs it, and a
model restriction there still refuses the script, which is conservative. -/

namespace Belay.Sqlite

/-- The query {lit}`PRAGMA foreign_keys` as a query without {lit}`FROM`: one row with the column
{lit}`foreign_keys`, 1 with foreign keys on and 0 with them off. -/
def foreignKeysQuery (on : Bool) : Syntax.Subquery :=
  let digit := if on then "1" else "0"
  { columns := [.expression (.numeric digit) (some (name! "foreign_keys")) digit], source := none, joins := [],
    filter := none, groupBy := [], orderBy := [], limit := none, offset := none, parent := none }

/-- Resolve one statement at its zero-based index. BEGIN in an open transaction and
COMMIT or ROLLBACK without one fail when SQLite runs them, not when it prepares
them, so they resolve and leave the error to the execution semantics: such a BEGIN
keeps the first saved catalog, and such a ROLLBACK keeps the current catalog.
{lit}`PRAGMA foreign_keys` is the query {name}`foreignKeysQuery`; setting it changes the state's
setting outside a transaction and nothing inside one, as SQLite does. -/
def resolveStatement (context : ResolveContext) (state : ResolveState) (index : Nat) :
    Syntax.Statement → Except Restriction (Resolved.Statement × ResolveState)
  | .begin => .ok (.begin, { state with saved := state.saved.getD state.catalog })
  | .commit => .ok (.commit, { state with saved := none })
  | .rollback => .ok (.rollback, { state with catalog := state.saved.getD state.catalog, saved := none })
  | .pragmaForeignKeys none => state.withCatalog (resolveSelect context state.catalog index (foreignKeysQuery state.foreignKeys) [])
  | .pragmaForeignKeys (some on) =>
    let foreignKeys := if state.saved.isSome then state.foreignKeys else on
    .ok (.setting foreignKeys, { state with foreignKeys })
  | .createTable name columns constraints options =>
    state.withCatalog (resolveCreateTable context state.catalog index name columns constraints options)
  | .createIndex name unique table terms filter =>
    state.withCatalog (resolveCreateIndex context state.catalog index name unique table terms filter)
  | .addColumn table column => state.withCatalog (resolveAddColumn context state.catalog index table column)
  | .dropTable name ifExists => state.withWrite context index (resolveDropTable state.catalog name ifExists)
  | .dropIndex name ifExists => state.withCatalog (resolveDropIndex state.catalog index name ifExists)
  | .createTrigger name ifNotExists time event table condition body =>
    state.withCatalog (resolveCreateTrigger state.catalog name ifNotExists { table, time, event, condition, body })
  | .dropTrigger name ifExists => state.withCatalog (resolveDropTrigger state.catalog name ifExists)
  | .insert table columns rows conflicts algorithm returning subqueries =>
    state.withWrite context index (resolveWriteSubqueries context state.catalog index 6 table (fun _ => []) subqueries
      (resolveInsert context state.catalog index table columns rows conflicts algorithm returning))
  | .update table assignments filter returning subqueries =>
    state.withWrite context index (resolveWriteSubqueries context state.catalog index 4 table (writtenScope table) subqueries
      (resolveUpdate context state.catalog index table assignments filter returning))
  | .select columns source joins filter groupBy orderBy limit offset subqueries having distinct =>
    state.withCatalog (resolveSelect context state.catalog index
      { columns, source, joins, filter, groupBy, orderBy, limit, offset, parent := none, having, distinct } subqueries)
  | .delete table filter returning subqueries =>
    state.withWrite context index (resolveWriteSubqueries context state.catalog index 3 table (writtenScope table) subqueries
      (resolveDelete context state.catalog index table filter returning))

/-- Resolve the statements from a zero-based index and a state, in order. -/
def resolveFrom (context : ResolveContext) (index : Nat) (state : ResolveState) :
    List Syntax.Statement → Except Restriction (List Resolved.Statement × ResolveState)
  | [] => .ok ([], state)
  | statement :: rest => do
    let (resolved, next) ← resolveStatement context state index statement
    let (later, final) ← resolveFrom context (index + 1) next rest
    return (resolved :: later, final)

/-- Resolve a script against a starting catalog, from index zero outside a
transaction, with foreign keys on when the profile turns them on. The result has one
resolved statement or prepare error for each
statement, and the catalog after all of them succeed; or the first model
restriction. -/
def resolve (context : ResolveContext) (catalog : Catalog) (script : List Syntax.Statement) :
    ResolveResult :=
  match resolveFrom context 0 { catalog := catalog, foreignKeys := context.profile.foreignKeys } script with
  | .ok (statements, state) => .resolved statements state.catalog
  | .error restriction => .restricted restriction

end Belay.Sqlite
