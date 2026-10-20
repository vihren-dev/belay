import Belay.Sqlite.Resolution.Assignments
import Belay.Sqlite.Resolution.ConflictForm

set_option doc.verso true

/-! Resolution of the {lit}`ON CONFLICT` clauses of INSERT (ADR 0012, amendment 4,
slice 5c), as SQLite 3.51.0's {lit}`sqlite3UpsertAnalyzeTarget` and
{lit}`sqlite3UpsertDoUpdate` do it. A target names the columns of one key; the values
and the filter of {lit}`DO UPDATE` read the table's row by unqualified or qualified
names and the proposed row as {lit}`excluded.column`. Paths are relative to the clause
list: clause {lit}`i` is {lit}`[i]`, its target {lit}`[i, 0]`, and the assignments and
the filter of its action {lit}`[i, 1, 0]` and {lit}`[i, 1, 1]`. -/

namespace Belay.Sqlite

/-- The scope of {lit}`DO UPDATE`: the table, then {lit}`excluded` with the same
columns. Every column of {lit}`excluded` is merged ({name}`ScopeSource.merged`), so an
unqualified name reads the table's column and only {lit}`excluded.column` reads the
proposed row, as in SQLite. Both have a rowid unless the table is {lit}`WITHOUT ROWID`. -/
def upsertScope (tableName : Identifier) (columns : List CatalogColumn) (hasRowid : Bool := true) : Scope :=
  [{ name := tableName, columns, hasRowid },
   { name := (name! "excluded"), columns, offset := columns.length, merged := List.range columns.length, hasRowid }]

/-- The key that a conflict target names: the first key of columns without filter
({name}`UniqueKey.columns?`) whose columns are the target's columns, in any order. An
unknown name is {lit}`no such column: %s`; a target that is no such key, also one that
repeats a column or names only a partial or expression index, is
{name}`ExprError.conflictTargetMismatch`. -/
def targetKey (columns : List CatalogColumn) (keys : List UniqueKey) (names : List Identifier) :
    Except ValueIssue (List Nat) := do
  let positions ← resolveAll (fun _ name => match columnPosition columns name with
    | some position => .ok position
    | none => .error (.prepare (.noSuchColumn name))) names
  match (keys.filterMap UniqueKey.columns?).find? fun key =>
      key.length == positions.length && key.all positions.contains with
  | some key => .ok key
  | none => .error (.prepare .conflictTargetMismatch)

/-- Resolve the optional target of a clause at {lit}`clause` ({name}`targetKey`). -/
def resolveConflictTarget (columns : List CatalogColumn) (keys : List UniqueKey) (clause : Nat) :
    Option (List Identifier) → Except ValueIssue (Option (List Nat))
  | none => .ok none
  | some names => (some <$> targetKey columns keys names).mapError (·.under [clause, 0])

/-- Resolve the optional filter of {lit}`DO UPDATE` of a clause at {lit}`clause` as a
condition. -/
def resolveConflictFilter (dqs : Bool) (scope : Scope) (clause : Nat) :
    Option Syntax.Expr → Except ValueIssue (Option Resolved.Expr)
  | none => .ok none
  | some term => some <$> condition [clause, 1, 1] (resolveOperand dqs scope {} true term)

/-- Resolve the action of a clause at {lit}`clause`: {lit}`DO NOTHING` as it is;
{lit}`DO UPDATE` with its assignments in order, then its filter as a condition, over
the scope ({name}`upsertScope`). A column assigned twice is
{name}`RestrictionKind.updateColumnTwice`. A {lit}`DO UPDATE` without target on a table
with more than one key is {name}`RestrictionKind.conflictWithoutTarget`. -/
def resolveConflictAction (dqs : Bool) (scope : Scope) (keys : List UniqueKey) (clause : Nat)
    (targeted : Bool) : Syntax.ConflictAction → Except ValueIssue Resolved.ConflictAction
  | .nothing => .ok .nothing
  | .update assignments filter =>
    (resolveAll (resolveAssignment dqs scope [] fun _ => .restriction [] .upsertGenerated) assignments).mapError (·.under [clause, 1, 0]) >>= fun resolved =>
    resolveConflictFilter dqs scope clause filter >>= fun resolvedFilter =>
    if (resolved.map Prod.fst).eraseDups.length != resolved.length then
      .error (.restriction [clause, 1, 0] .updateColumnTwice)
    else if !targeted && keys.length > 1 then .error (.restriction [clause] .conflictWithoutTarget)
    else .ok (.update resolved resolvedFilter)

/-- Resolve one clause at {lit}`clause`: its target ({name}`resolveConflictTarget`), then
its action ({name}`resolveConflictAction`). -/
def resolveConflict (dqs : Bool) (tableName : Identifier) (table : CatalogTable) (keys : List UniqueKey)
    (clause : Nat) (written : Syntax.ConflictClause) : Except ValueIssue Resolved.ConflictClause :=
  resolveConflictTarget table.columns keys clause written.target >>= fun target =>
  resolveConflictAction dqs (upsertScope tableName table.columns !table.withoutRowid) keys clause target.isSome
    written.action
    >>= fun action => .ok { target, action }

end Belay.Sqlite
