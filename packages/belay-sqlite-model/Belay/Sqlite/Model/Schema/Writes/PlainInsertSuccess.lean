import Belay.Sqlite.Model.Schema.Writes.InsertSelectSuccess

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For a plain INSERT with no RETURNING or write rules, a found table, plain subqueries,
ready cell expressions and values that satisfy {name}`InsertFits`, the model describes the run (it is ready).
The run has one successful effect and no alternative executions. It stores the table with
the new rows and uses the counts of that insertion.
The change count is the number of inserted rows. Proof sketch: the final table satisfies
its constraints, so its prefix does too. No row fails the alias check. These two facts
select the successful branches of {name}`insertOutcome` and {name}`checkedWrite`. -/
theorem runStatement_insert_ok (clock : Int) (counters : Counters) (parameters : List Value)
    (database : Database) (target : Nat) (table : Table) (rows : List (List Resolved.Cell))
    (subqueries : List Resolved.Query) (found : database.table target = some table)
    (plain : Resolved.subqueriesPlain subqueries = true)
    (cells : Resolved.cellsReady (Resolved.statementContext clock counters parameters database subqueries) rows = true)
    (fits : InsertFits (database.keys target table) table
      (Resolved.rowsAt (Resolved.statementContext clock counters parameters database subqueries) table.shape.columns rows)) :
    let values := Resolved.rowsAt (Resolved.statementContext clock counters parameters database subqueries)
      table.shape.columns rows
    let effect := Except.ok (database.setRows target (LiteralData.inserted table values).rows)
    let run := runStatement clock counters parameters (.insert target rows [] subqueries none) database
    run = { effect, ready := true, counts := LiteralData.insertCounts effect (database.keys target table) table values } ∧
      run.counts.changes = some rows.length := by
  let values := Resolved.rowsAt (Resolved.statementContext clock counters parameters database subqueries)
    table.shape.columns rows
  change InsertFits _ _ values at fits
  have passes : LiteralData.constraints (database.keys target table) (LiteralData.inserted table values) = true := by
    simp [LiteralData.constraints, fits.notNull, fits.typed, fits.checked, fits.keysDistinct]
  obtain ⟨added, appended⟩ := LiteralData.inserted_rows_prefix table values
  have before := LiteralData.constraints_of_appended (LiteralData.shape_inserted table values) appended passes
  have aliases : values.findIdx? (LiteralData.aliasMismatch table.shape) = none := by
    simpa [List.findIdx?_eq_none_iff] using fits.aliasFree
  have effect : insertOutcome database target (database.keys target table) table values
      (LiteralData.inserted table values) = .ok (database.setRows target (LiteralData.inserted table values).rows) := by
    simp [insertOutcome, aliases, checkedWrite, passes, fits.rowidsDistinct]
  have ready : LiteralData.insertReady (database.keys target table) table values (LiteralData.inserted table values) = true := by
    simp [LiteralData.insertReady, LiteralData.tableReady, before, fits.aliasInteger, fits.stored, fits.rowidsBounded]
  let written := database.setRows target (LiteralData.inserted table values).rows
  have certified : runStatement clock counters parameters (.insert target rows [] subqueries none) database =
      { effect := .ok written, ready := true,
        counts := LiteralData.insertCounts (.ok written) (database.keys target table) table values } := by
    simp only [runStatement, found, Option.map_none]
    change StatementRun.withKeys (insertOutcome database target _ table values _)
      (LiteralData.insertReady _ table values _ && Resolved.subqueriesPlain subqueries && _ && _)
      (LiteralData.insertCounts _ _ table values) none = _
    rw [effect, ready, plain, cells]
    rfl
  refine ⟨certified, ?_⟩
  rw [certified]
  simp [LiteralData.insertCounts, values, Resolved.rowsAt]

end Belay.Sqlite.Model
