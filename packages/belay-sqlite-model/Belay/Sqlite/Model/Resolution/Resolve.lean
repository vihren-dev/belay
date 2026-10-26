import Belay.Sqlite.Model.Resolution.StatementArms

set_option doc.verso true

/-! Name resolution of a script. Each statement is resolved against the catalog
that the earlier statements leave when they succeed. BEGIN saves the catalog,
ROLLBACK restores it and COMMIT drops the saved copy. Resolution also follows the
setting of {lit}`PRAGMA foreign_keys`, which no ROLLBACK undoes, and gives each write the
foreign keys that it must check (ADR 0018, D4). A statement after a prepare
error is resolved as if that statement had no effect: SQLite never runs it, and a
model restriction there still refuses the script, which is conservative. -/

namespace Belay.Sqlite.Model

/-- Resolve the statements from a zero-based index and a state, in order. A restriction of a
statement gets the statement's index ({name}`NodeRestriction.at`). -/
def resolveFrom (context : ResolveContext) (index : Nat) (state : ResolveState) :
    List Syntax.Statement → Except Restriction (List Resolved.Statement × ResolveState)
  | [] => .ok ([], state)
  | statement :: rest =>
    match resolveStatement context state statement with
    | .error restriction => .error (restriction.at index)
    | .ok (resolved, next) => do
      let (later, final) ← resolveFrom context (index + 1) next rest
      return (resolved :: later, final)

/-- Resolve a script against a starting catalog, from index zero outside a
transaction, with foreign keys on when the profile turns them on. The result has one
resolved statement or prepare error for each
statement, and the catalog after all of them succeed; or the first model
restriction. -/
def resolve (context : ResolveContext) (catalog : Catalog) (script : List Syntax.Statement) :
    ResolveResult :=
  match resolveFrom context 0 (ResolveState.initial context.profile catalog) script with
  | .ok (statements, state) => .resolved statements state.catalog
  | .error restriction => .restricted restriction

end Belay.Sqlite.Model
