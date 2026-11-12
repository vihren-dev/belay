import Belay.Sqlite.Model.Queries.Preparation.ColumnPositionAppend
import Belay.Sqlite.Model.Schema.Ddl.ColumnPositionAppend
import Belay.Sqlite.Model.Queries.Select.ExprResolutionLaws
import Belay.Sqlite.Model.Schema.Ddl.CatalogValidSet
import Belay.Sqlite.Model.Schema.Dispatch.Updates

set_option doc.verso true

/-! The resolution of the backfill of an appended column (ADR 0017, S6): {lit}`UPDATE t SET c = e` on
a table whose catalog entry already holds the appended column {lit}`c`. The premise on the catalog
concerns the table after ADD COLUMN, because the model resolves the UPDATE against that catalog. -/

namespace Belay.Sqlite.Model

/-- The scope in which the backfill {lit}`UPDATE t SET c = e` resolves the value {lit}`e`: the one table
at its catalog position, with the columns of the table before the appended column {lit}`c` and then
{lit}`c`. It has the table's name and no alias, and sees the rowid of a table that has one. -/
abbrev backfillScope (position : Nat) (tableName : Identifier) (table : CatalogTable) (column : CatalogColumn) : Scope :=
  Scope.singleAt (some position) tableName (table.columns ++ [column]) (!table.withoutRowid) false

/-- For every catalog that finds the table with the appended column, every written value that resolves in the
scope of that table, and every successful resolution of {lit}`UPDATE t SET name = value` with no filter:
the resolution is the plain UPDATE at the position of the table that assigns the appended column the
resolved value ({name}`assignedExpression`), and it leaves the catalog unchanged. The name must resolve to
the appended column, and that column must have no generated expression. A restriction outcome does not
satisfy the resolution premise. The value can be any expression that resolves: a function of one column,
a concatenation, a sum, a constant. Proof sketch: identify the target position and the resolved operand;
the remaining checks either refuse resolution or leave this assignment unchanged. -/
theorem backfillUpdate_resolution {context : ResolveContext} {catalog : Catalog}
    {tableName name : Identifier} {value : Syntax.Expr} {position : Nat} {table : CatalogTable}
    {column : CatalogColumn} {derived : Resolved.Expr} {affinity : Option Affinity}
    {resolved : Resolved.Statement} {next : Catalog}
    (found : catalog.findTable tableName = some (position, { table with columns := table.columns ++ [column] }))
    (added : columnPosition (table.columns ++ [column]) name = some table.columns.length)
    (newPlain : column.generated = none)
    (operand : resolveOperand context.profile.dqsDml
      (backfillScope position tableName table column) {} true value =
        .ok (derived, affinity))
    (ok : resolveUpdate context catalog tableName [(name, value)] none [] [] {} = .ok (resolved, next)) :
    resolved = .update position [(table.columns.length, assignedExpression
      (backfillScope position tableName table column)
      table.columns.length value derived)] none [] [] none ∧ next = catalog := by
  have generated : ((table.columns ++ [column])[table.columns.length]?.bind (·.generated)).isSome = false := by
    rw [List.getElem?_append_right (Nat.le_refl table.columns.length), Nat.sub_self]
    simp [newPlain]
  have assignment (keys : List Nat) (failure : Identifier → ValueIssue) (rowid : Option (Option Nat))
      (item : Nat) : (resolveAssignmentTraced context.profile.dqsDml
        (backfillScope position tableName table column)
        {} keys failure rowid item [] (name, value)).drop =
      if mentionsColumn (backfillScope position tableName table column)
          value && keys.contains table.columns.length then .error (.restriction [item, 1] .rowDependentKey)
      else if !mentionsColumn (Scope.singleAt (some position) tableName (table.columns ++ [column])
          (!table.withoutRowid) false) value && !derived.readsClock && !derived.readsRunValue &&
          derived.mayFailOn (.plain 0) [] then .error (.restriction [item, 1] .constantFunctionError)
      else .ok (table.columns.length, assignedExpression
        (backfillScope position tableName table column)
        table.columns.length value derived) := by
    simp only [resolveAssignmentTraced, traced_drop, resolveOperandTraced_drop, assignedPosition, List.append_nil,
      operand, Except.mapError, bind, Scope.columns_singleAt, added, generated, Bool.false_eq_true,
      ↓reduceIte]
  by_cases mentions : mentionsColumn (Scope.singleAt (some position) tableName (table.columns ++ [column])
      (!table.withoutRowid) false) value = true <;>
  by_cases fails : (!derived.readsClock && !derived.readsRunValue &&
      Resolved.Expr.mayFailOn (Resolved.EvalContext.plain 0) [] derived) = true <;>
  cases keyed : ((catalog.uniqueKeys position
      { table with columns := table.columns ++ [column] }).flatMap
        (·.reads (table.columns ++ [column]).length)).contains table.columns.length <;>
    simp only [resolveUpdate, resolveUpdateTraced, traced_drop, found, Option.map_none, Option.getD_none, resolveAll,
      resolveAllFrom, assignment, mentions, fails, keyed, Bool.and_true, Bool.and_false, Bool.false_and, Bool.true_and,
      Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte,
      bind, Except.bind, pure, Except.pure, resolveReturningTraced, resolveWriteFilterTraced, Except.map, List.any_nil,
      issueResolution, restrict] at ok <;>
  (repeat' split at ok) <;>
  first
    | (cases ok; exact ⟨rfl, rfl⟩)
    | cases ok

end Belay.Sqlite.Model
