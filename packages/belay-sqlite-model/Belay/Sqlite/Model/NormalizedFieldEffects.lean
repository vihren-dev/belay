import Belay.Sqlite.Model.NormalizedFieldScan
import Belay.Sqlite.Model.DatabaseLaws
import Belay.Sqlite.Model.StatementStep

set_option doc.verso true

/-! Exact stored rows after a successful plain UPDATE. The success premise
comes from the existing statement effect; the resulting row map is derived
from its assignment evaluator. Foreign-key and trigger plans are excluded by
the resolved statement's absent rules, independently of these row laws. -/

namespace Belay.Sqlite.Model
open Resolved

/-- For every present table, assignment list, filter, returning list and
subquery list, a successful UPDATE without a foreign-key or trigger plan
stores exactly the rows computed by {name}`LiteralData.updated`. This states
the effect only; it does not assert that the statement passes its support
check or succeeds on every database. Proof sketch: success excludes the
alias-mismatch and constraint-failure branches, leaving the stored row list. -/
theorem runStatement_update_ok (clock : Int) (counters : Counters) (parameters : List Value)
    {database after : Database} {target : Nat} {table : Table}
    (assignments : List (Nat × Expr)) (filter : Option Expr)
    (returning : List (Expr × String)) (subqueries : List Query)
    (present : database.table target = some table)
    (success : (runStatement clock counters parameters
      (.update target assignments filter returning subqueries none) database).effect = .ok after) :
    after = database.setRows target
      (LiteralData.updated (statementContext clock counters parameters database subqueries)
        table assignments filter).rows := by
  simp only [runStatement, present, Option.map_none, StatementRun.withKeys] at success
  split at success
  · cases success
  · unfold checkedWrite at success
    split at success
    · cases success; rfl
    · cases success

/-- Under the successful plain UPDATE assumptions of {name}`runStatement_update_ok`,
if the target has a storage slot, its resulting table is exactly the computed
updated table, including its unchanged schema. Proof sketch: the exact effect
stores those rows, and {name}`Database.table_setRows` identifies the table. -/
theorem table_after_update_ok (clock : Int) (counters : Counters) (parameters : List Value)
    {database after : Database} {target : Nat} {table : Table}
    (assignments : List (Nat × Expr)) (filter : Option Expr)
    (returning : List (Expr × String)) (subqueries : List Query)
    (present : database.table target = some table) (aligned : target < database.rows.length)
    (success : (runStatement clock counters parameters
      (.update target assignments filter returning subqueries none) database).effect = .ok after) :
    after.table target = some
      (LiteralData.updated (statementContext clock counters parameters database subqueries)
        table assignments filter) := by
  rw [runStatement_update_ok clock counters parameters assignments filter returning subqueries present success]
  exact Database.table_setRows _ present aligned

namespace NormalizedField

/-- For every table extended by a plain TEXT column containing NULL, a successful
plain UPDATE that assigns the new column to lowercase of an original column
stores each original row with that lowercase cell appended. The target must
have storage; original rows must be wide and aliased, the source must be in
range, and original columns must have no generated expressions. The conclusion
is conditional on the supplied successful effect. Proof sketch: the successful-effect
law identifies the computed table, and {name}`updated_lower_append` derives its
rows while the UPDATE leaves its schema unchanged. -/
theorem table_after_lower_update (clock : Int) (counters : Counters) (parameters : List Value)
    {database after : Database} {target : Nat} (table : Table) (column : CatalogColumn) (source : Nat)
    (present : database.table target = some (table.appendColumns [(column, .null)]))
    (aligned : target < database.rows.length)
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (inside : source < table.shape.columns.length)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none)
    (newPlain : column.generated = none) (text : column.affinity = .text)
    (success : (runStatement clock counters parameters
      (.update target [(table.shape.columns.length, .scalar .lower (.cons (.column source) .nil))]
        none [] [] none) database).effect = .ok after) :
    after.table target = some
      { shape := { table.shape with columns := table.shape.columns ++ [column] },
        rows := table.rows.map fun row => row.appendValues [mapText lowerByte (row.values.getD source .null)] } := by
  rw [table_after_update_ok clock counters parameters _ none [] [] present aligned success]
  exact congrArg (fun rows : List Row => some
    ({ shape := { table.shape with columns := table.shape.columns ++ [column] }, rows } : Table))
    (updated_lower_append (statementContext clock counters parameters database [])
      table column source wide aliased inside plain newPlain text)

/-- Under the same successful appended-column UPDATE and row premises, with
original primary-key positions in range, reading the resulting target's full
scan gives the original scan with lowercase cells appended. Rowid and
WITHOUT ROWID ordering, including direction and collation, are preserved.
The starting row list can have any order. Proof sketch: the effect identifies
the actual stored table, then {name}`sourceRows_updated_lower` transports its scan. -/
theorem sourceRows_after_lower_update (clock : Int) (counters : Counters) (parameters : List Value)
    {database after : Database} {target : Nat} (table : Table) (column : CatalogColumn) (source : Nat)
    (present : database.table target = some (table.appendColumns [(column, .null)]))
    (aligned : target < database.rows.length)
    (wide : table.RowsWide) (aliased : table.RowsAliased)
    (inside : source < table.shape.columns.length)
    (keysInside : ∀ position ∈ table.shape.primaryKey, position < table.shape.columns.length)
    (plain : ∀ old ∈ table.shape.columns, old.generated = none)
    (newPlain : column.generated = none) (text : column.affinity = .text)
    (success : (runStatement clock counters parameters
      (.update target [(table.shape.columns.length, .scalar .lower (.cons (.column source) .nil))]
        none [] [] none) database).effect = .ok after) :
    (after.table target).map sourceRows = some
      ((sourceRows table).map fun row => row ++ [mapText lowerByte (row.getD source .null)]) := by
  rw [table_after_update_ok clock counters parameters _ none [] [] present aligned success]
  simp only [Option.map_some]
  rw [sourceRows_updated_lower _ table column source wide aliased inside keysInside plain newPlain text]

end NormalizedField
end Belay.Sqlite.Model
