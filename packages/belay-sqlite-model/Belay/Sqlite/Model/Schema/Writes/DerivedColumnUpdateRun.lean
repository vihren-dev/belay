import Belay.Sqlite.Model.Schema.Writes.DerivedColumnConstraints
import Belay.Sqlite.Model.Schema.Dispatch.DerivedColumnBackfill
import Belay.Sqlite.Model.Schema.Writes.JsonReady
import Belay.Sqlite.Model.Schema.Dispatch.StatementStep
import Belay.Sqlite.Model.Queries.Evaluation.QueryPlainLaws

set_option doc.verso true

/-! The run of the backfill UPDATE of a derived-column migration (ADR 0017, S6), as the model describes
it: on a table that ADD COLUMN extended with NULL cells, {lit}`UPDATE t SET c = e` of the new column, with an
expression of the old columns that has no fallible call, is ready, has no alternative execution and
succeeds. It writes the old rows with the stored value of the expression appended. -/

namespace Belay.Sqlite.Model
open Resolved

/-- For every clock value, counters, parameters, database, position, old table, new column and
expression: if the database holds at the position the old table with the column appended with NULL cells,
and these hold:

* the old table is admitted and satisfies {name}`Table.NotNull`, {name}`Table.TypesFit`,
  {name}`Table.ChecksHold` and {name}`Table.KeysUnique` for the keys of the position
  ({name}`Database.keys`);
* each CHECK constraint and each key reads only columns below the old width;
* the new column has no NOT NULL, no STRICT type, no CHECK and no generated expression, and no old column
  is generated;
* the old shape passes {name}`LiteralData.aliasReady`, and its rowid alias, if it has one, is an old
  column;
* the expression reads only old columns and has no fallible call ({name}`Resolved.Expr.isFallibleCall`),

then the run of the UPDATE of the new column to the expression, without filter, RETURNING, subqueries or
rules, is ready, has no alternative execution, and succeeds with the database whose table at the position
has the old rows with the stored value of the expression appended ({name}`Table.appendCells`). In plain
words, the backfill of a derived column cannot fail. The model has no limit on the size of a record, so
the length of a row is no condition. Proof sketch: the UPDATE gives the old rows with a cell appended
({name}`updated_derived_append`); {name}`Table.appendCells_checked` gives the write check of that table and
the ready check of the table before it; the alias is not assigned, so no rowid moves; the expression has
no fault ({name}`Resolved.Expr.fault_of_plain_at`). -/
theorem runStatement_backfill_ok (clock : Int) (counters : Counters) (parameters : List Value)
    {database : Database} {position : Nat} {table : Table} {column : CatalogColumn} {derived : Resolved.Expr}
    (present : database.table position = some (table.appendColumns [(column, .null)]))
    (admitted : table.Admitted) (notNull : table.NotNull) (fits : table.TypesFit) (holds : table.ChecksHold)
    (unique : table.KeysUnique (database.keys position (table.appendColumns [(column, .null)])))
    (checksBelow : ∀ check ∈ table.shape.allChecks, check.condition.readsBelow table.shape.columns.length = true)
    (keysBelow : ∀ key ∈ database.keys position (table.appendColumns [(column, .null)]),
      key.readsBelow table.shape.columns.length = true)
    (nullable : column.notNull = false) (loose : column.strictType = none) (unchecked : column.checks = [])
    (newPlain : column.generated = none) (plain : ∀ old ∈ table.shape.columns, old.generated = none)
    (alias : LiteralData.aliasReady table.shape = true)
    (aliasBelow : table.shape.rowidAlias.all (· < table.shape.columns.length) = true)
    (below : derived.readsBelow table.shape.columns.length = true)
    (safe : derived.any Resolved.Expr.isFallibleCall = false) :
    let run := runStatement clock counters parameters
      (.update position [(table.shape.columns.length, derived)] none [] [] none) database
    run.ready = true ∧ run.alternatives = [] ∧
      run.effect = .ok (database.setRows position (table.appendCells column fun row =>
        Value.store column.affinity
          (derived.eval (statementContext clock counters parameters database []) row.values)).rows) := by
  intro run
  have rows := updated_derived_append (statementContext clock counters parameters database [])
    (statementContext_nil_rowFree clock counters parameters database) table
    column derived admitted.rowsWide admitted.rowsAliased below plain newPlain
  have result : LiteralData.updated (statementContext clock counters parameters database [])
      (table.appendColumns [(column, .null)])
      [(table.shape.columns.length, derived)] none = table.appendCells column fun row =>
        Value.store column.affinity
          (derived.eval (statementContext clock counters parameters database []) row.values) := by
    simp only [LiteralData.updated] at rows ⊢
    rw [rows]
    rfl
  have nullCells : table.appendColumns [(column, .null)] =
      table.appendCells column fun _ => Value.store column.affinity .null := rfl
  have checked := Table.appendCells_checked (cell := fun row =>
      Value.store column.affinity (derived.eval (statementContext clock counters parameters database []) row.values))
    admitted.rowsWide notNull fits holds unique
    admitted.rowidsDistinct checksBelow keysBelow nullable loose unchecked
  have ready := Table.appendCells_checked (cell := fun _ => Value.store column.affinity .null) admitted.rowsWide notNull
    fits holds unique admitted.rowidsDistinct checksBelow keysBelow nullable loose unchecked
  have noMismatch : LiteralData.updateMismatch (statementContext clock counters parameters database [])
      (table.appendColumns [(column, .null)])
      [(table.shape.columns.length, derived)] none = false := by
    unfold LiteralData.updateMismatch
    cases aliasAt : table.shape.rowidAlias with
    | none => simp [Table.appendColumns, aliasAt]
    | some place =>
      simp only [aliasAt, Option.all_some, decide_eq_true_eq] at aliasBelow
      simp [Table.appendColumns, aliasAt, Nat.ne_of_gt aliasBelow]
  have quiet : (statementContext clock counters parameters database []).Quiet := fun _ _ => ⟨rfl, rfl, rfl⟩
  have noFault : ∀ row, derived.mayFailOn (statementContext clock counters parameters database []) row = false :=
    fun row => by
      unfold Resolved.Expr.mayFailOn
      rw [Resolved.Expr.fault_of_plain_at _ row (quiet.at row) derived safe]
      rfl
  simp only [run, runStatement, present, StatementRun.withKeys, Option.map_none, noMismatch, Bool.false_eq_true,
    ite_false,
    checkedWrite]
  rw [result]
  simp only [checked.1, checked.2, Bool.and_self, ite_true]
  refine ⟨?_, trivial, ?_⟩
  rotate_left
  · trivial
  simp only [LiteralData.updateReady, LiteralData.tableReady, Bool.and_eq_true]
  refine ⟨⟨⟨⟨⟨by rw [nullCells]; exact ready.1, ?_⟩, ?_⟩, ?_⟩, rfl⟩, ?_⟩
  · unfold LiteralData.aliasReady at alias ⊢
    cases aliasAt : table.shape.rowidAlias with
    | none => simp [Table.appendColumns, aliasAt]
    | some place =>
      simp only [aliasAt, Option.all_some, decide_eq_true_eq] at aliasBelow alias
      simpa [Table.appendColumns, aliasAt, List.getElem?_append_left aliasBelow] using alias
  · simp [Table.appendColumns]
  · simp only [Table.appendCells, List.all_map, List.all_eq_true, Function.comp_apply, Row.appendValues,
      LiteralData.boundedInteger, decide_eq_true_eq]
    exact fun row member => admitted.rowidsInRange row member
  · have never : ∀ rows, Resolved.anyMayFail (statementContext clock counters parameters database []) rows
        [derived] = false := by
      intro rows
      unfold Resolved.anyMayFail
      simp only [List.any_cons, List.any_nil, noFault, Bool.or_false]
      exact List.any_eq_false.mpr fun _ _ => Bool.false_ne_true
    unfold updateJsonReady
    simp only [List.map_cons, List.map_nil, never]
    simp [Resolved.anyMayFail, returningExpressions]

end Belay.Sqlite.Model
