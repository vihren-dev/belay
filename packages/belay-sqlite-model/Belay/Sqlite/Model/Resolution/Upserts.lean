import Belay.Sqlite.Model.Resolution.Assignments
import Belay.Sqlite.Model.Resolution.ConflictForm

set_option doc.verso true

/-! Resolution of the {lit}`ON CONFLICT` clauses of INSERT (ADR 0012, amendment 4,
slice 5c), as SQLite 3.51.0's {lit}`sqlite3UpsertAnalyzeTarget` and
{lit}`sqlite3UpsertDoUpdate` do it. A target names the columns of one key; the values
and the filter of {lit}`DO UPDATE` read the table's row by unqualified or qualified
names and the proposed row as {lit}`excluded.column`. Paths are relative to the clause
list: clause {lit}`i` is {lit}`[i]`, its target {lit}`[i, 0]`, and the assignments and
the filter of its action {lit}`[i, 1, 0]` and {lit}`[i, 1, 1]`. -/

namespace Belay.Sqlite.Model

/-- The scope of {lit}`DO UPDATE`: the table, read from the catalog at {lit}`position` when it is
known, then {lit}`excluded` with the same columns and the same position. Every column of {lit}`excluded` is merged
({name}`ScopeSource.merged`), so an unqualified name reads the table's column and only
{lit}`excluded.column` reads the proposed row, as in SQLite. Both have a rowid unless the table is
{lit}`WITHOUT ROWID`. -/
def upsertScope (tableName : Identifier) (columns : List CatalogColumn) (hasRowid : Bool := true)
    (position : Option Nat := none) : Scope :=
  [{ name := tableName, columns, hasRowid, catalogPosition := position },
   { name := (name! "excluded"), columns, offset := columns.length, merged := List.range columns.length, hasRowid,
     role := .proposedRow, catalogPosition := position }]

/-- The key that a conflict target names: the first key of columns without filter
({name}`UniqueKey.columns?`) whose columns are the target's columns, in any order. An
unknown name is {lit}`no such column: %s`; a target that is no such key, also one that
repeats a column or names only a partial or expression index, is
{name}`ExprError.conflictTargetMismatch`. Each name is recorded at its place in the target, as the
column of the table that it names. -/
def targetKeyTraced (columns : List CatalogColumn) (scope : Scope) (keys : List UniqueKey)
    (names : List Identifier) : Traced ValueIssue (List Nat) := do
  let positions ← resolveAllTraced (fun index name => do
    let located : Except ValueIssue Nat := match columnPosition columns name with
      | some position => .ok position
      | none => .error (.prepare (.noSuchColumn name))
    Traced.record (columnTargetOccurrence scope [index] name located.toOption .error)
    located) names
  match (keys.filterMap UniqueKey.columns?).find? fun key =>
      key.length == positions.length && key.all positions.contains with
  | some key => pure key
  | none => throw (.prepare .conflictTargetMismatch)

/-- Resolve the optional target of a clause at {lit}`clause` ({name}`targetKeyTraced`). The names of
the target are at {lit}`[clause, 0, index]`. -/
def resolveConflictTargetTraced (columns : List CatalogColumn) (scope : Scope) (keys : List UniqueKey) (clause : Nat) :
    Option (List Identifier) → Traced ValueIssue (Option (List Nat))
  | none => pure none
  | some names => (Traced.map some (targetKeyTraced columns scope keys names)).under [clause, 0]

/-- Resolve the optional filter of {lit}`DO UPDATE` of a clause at {lit}`clause` as a
condition. -/
def resolveConflictFilterTraced (dqs : Bool) (scope : Scope) (clause : Nat) :
    Option Syntax.Expr → Traced ValueIssue (Option Resolved.Expr)
  | none => pure none
  | some term => Traced.map some (Traced.condition [clause, 1, 1] (resolveOperandTraced dqs scope {} true term))

/-- Resolve the action of a clause at {lit}`clause`: {lit}`DO NOTHING` as it is;
{lit}`DO UPDATE` with its assignments in order, then its filter as a condition, over
the scope ({name}`upsertScope`). A column assigned twice is
{name}`RestrictionKind.updateColumnTwice`. A {lit}`DO UPDATE` without target on a table
with more than one key is {name}`RestrictionKind.conflictWithoutTarget`. The assignments are at
{lit}`[clause, 1, 0]` and the filter at {lit}`[clause, 1, 1]`. -/
def resolveConflictActionTraced (dqs : Bool) (scope : Scope) (keys : List UniqueKey) (clause : Nat)
    (targeted : Bool) (rowid : Option (Option Nat)) :
    Syntax.ConflictAction → Traced ValueIssue Resolved.ConflictAction
  | .nothing => pure .nothing
  | .update assignments filter => do
    let resolved ← (resolveAllTraced (resolveAssignmentTraced dqs scope {} [] (fun _ => .restriction [] .upsertGenerated)
      rowid) assignments).under [clause, 1, 0]
    let resolvedFilter ← resolveConflictFilterTraced dqs scope clause filter
    if (resolved.map Prod.fst).eraseDups.length != resolved.length then
      throw (.restriction [clause, 1, 0] .updateColumnTwice)
    else if !targeted && keys.length > 1 then throw (.restriction [clause] .conflictWithoutTarget)
    else pure (.update resolved resolvedFilter)

/-- Resolve one clause at {lit}`clause`: its target ({name}`resolveConflictTargetTraced`), then
its action ({name}`resolveConflictActionTraced`). The table was read from the catalog at
{lit}`position`. -/
def resolveConflictTraced (dqs : Bool) (tableName : Identifier) (position : Nat) (table : CatalogTable)
    (keys : List UniqueKey) (clause : Nat) (written : Syntax.ConflictClause) :
    Traced ValueIssue Resolved.ConflictClause := do
  let scope := upsertScope tableName table.columns (!table.withoutRowid) (some position)
  let target ← resolveConflictTargetTraced table.columns scope keys clause written.target
  let action ← resolveConflictActionTraced dqs scope keys clause target.isSome
    (if table.withoutRowid then none else some table.rowidAlias) written.action
  pure { target, action }

end Belay.Sqlite.Model
