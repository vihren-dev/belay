import Belay.Sqlite.Model.UpsertInsertedReady
import Belay.Sqlite.Model.InsertSelectLaws

set_option doc.verso true

/-! The success of INSERT from a query (ADR 0017, S6). {lit}`runStatement_insertSelect_none_effects` says
what a run can do: fail and keep the database, or write like an upsert. This module gives the other
direction for a statement without rules (no trigger, no foreign-key check): when the query has one certain
production without a fault, and the rows it hands over meet every constraint of the target, then no
execution of the statement fails, the statement is described by the model, and its result is the target
with those rows appended. -/

namespace Belay.Sqlite.Model

/-- The facts that the rows of an INSERT must have for the statement to succeed, for a list of keys, the
target table and the full rows to write. In plain words, the table after appending the rows one after the
other (not the rows alone) meets these conditions:
* no row has a rowid alias cell that is neither NULL nor an integer
  ({name}`LiteralData.aliasMismatch`);
* the rowid alias, if any, is an integer column ({name}`LiteralData.aliasReady`);
* every row has one cell for each column and every cell is in stored form ({name}`LiteralData.storedForm`);
* the rows meet NOT NULL ({name}`LiteralData.notNullRows`), the types of a STRICT table
  ({name}`LiteralData.typedRows`), every CHECK constraint ({name}`LiteralData.checkedRows`) and every unique
  key ({name}`LiteralData.keysUnique`), also against the rows that the table has;
* the rowids are distinct ({name}`LiteralData.rowidsDistinct`) and signed 64-bit integers
  ({name}`LiteralData.boundedInteger`). -/
structure InsertFits (keys : List UniqueKey) (table : Table) (values : List (List Value)) : Prop where
  /-- No row has an alias cell that SQLite refuses. -/
  aliasFree : ∀ row ∈ values, LiteralData.aliasMismatch table.shape row = false
  /-- The rowid alias is an integer column, if the table has one. -/
  aliasInteger : LiteralData.aliasReady table.shape = true
  /-- Every row has one stored cell for each column. -/
  stored : values.all (fun row => row.length == table.shape.columns.length &&
    (table.shape.columns.zip row).all fun (column, value) => LiteralData.storedForm column.affinity value) = true
  /-- The table with the rows has no NULL in a NOT NULL column. -/
  notNull : LiteralData.notNullRows (LiteralData.inserted table values) = true
  /-- The table with the rows has only cells that fit the STRICT types. -/
  typed : LiteralData.typedRows (LiteralData.inserted table values) = true
  /-- The table with the rows meets every CHECK constraint. -/
  checked : LiteralData.checkedRows (LiteralData.inserted table values) = true
  /-- The table with the rows has no two rows that conflict on a key. -/
  keysDistinct : LiteralData.keysUnique keys (LiteralData.inserted table values) = true
  /-- The table with the rows has distinct rowids. -/
  rowidsDistinct : LiteralData.rowidsDistinct (LiteralData.inserted table values) = true
  /-- The rowids of the table with the rows are signed 64-bit integers. -/
  rowidsBounded : (LiteralData.inserted table values).rows.all (fun row => LiteralData.boundedInteger row.rowid) = true

/-- For every table and reached rows of an upsert whose summary succeeds, the rows written by the steps
({name}`LiteralData.upsertWritten`) are the written rows of the summary. Proof sketch: induction on the
steps; a successful summary has a successful result at every step. -/
theorem LiteralData.upsertWritten_of_summary (table : Table) :
    ∀ (steps : List LiteralData.UpsertStep) {final : Table} {written : List Row},
      LiteralData.upsertSummary table steps = .ok (final, written) → LiteralData.upsertWritten steps = written
  | [], _, _, summary => by
    simp only [LiteralData.upsertSummary, Except.ok.injEq, Prod.mk.injEq] at summary
    simp [LiteralData.upsertWritten, summary.2]
  | step :: rest, _, _, summary => by
    unfold LiteralData.upsertSummary at summary
    cases result : step.result with
    | error reason => simp [result] at summary
    | ok pair =>
      obtain ⟨next, wrote⟩ := pair
      cases later : LiteralData.upsertSummary next rest with
      | error failure => obtain ⟨reason, reached, more⟩ := failure; simp [result, later] at summary
      | ok done =>
        obtain ⟨last, more⟩ := done
        simp only [result, later, Except.ok.injEq, Prod.mk.injEq] at summary
        have tail := LiteralData.upsertWritten_of_summary next rest later
        simp [LiteralData.upsertWritten, result, ← summary.2, ← tail]

/-- For every clock value, counters, parameters, target, cells, query, clauses, {lit}`RETURNING` list,
algorithm and subqueries of INSERT from a query without rules, database, target table and production rows:
if the query has one certain production, which hands over the rows and has no failure, the full rows of
the INSERT meet every constraint of the target ({name}`InsertFits`), and the statement is in the part that
the model describes (the premises on clauses, subqueries, fixed cells, {lit}`RETURNING` and SQLite's
transfer), then:
* the run has no failing execution: its effect succeeds with the target rows of the table with the
  full rows appended, one after the other ({name}`LiteralData.inserted`), and no other table changes;
* the run is ready, so a step of the statement continues;
* the run has no alternative execution.

In plain words, an INSERT from a query whose rows fit the target writes exactly those rows. The premises
are:
* {lit}`found`: the target position holds the table;
* {lit}`certain`: the productions of the query, in the order of reading that the statement allows
  ({name}`Resolved.Query.productions`), are exactly one, with these rows and no failure;
* {lit}`fits`: the rows meet the constraints, also with respect to the rows that the table has;
* {lit}`clauseColumns`, {lit}`plainSubqueries`, {lit}`fixedCells`, {lit}`json`: the clauses assign existing
  columns and the statement has no cell, clause or subquery that can fail
  ({name}`LiteralData.upsertReady`, {name}`insertSelectRun`);
* {lit}`transfer`: when SQLite may copy the rows under their source rowids
  ({name}`insertSelectTransferRowids`), the rows written get those rowids.

The theorem says nothing about the counts of the run or the rows that it reports. Proof sketch: with one
production the run is the outcome of that production ({name}`insertSelectOutcome`); the upsert of the
rows succeeds ({name}`LiteralData.upsertSummary_inserted`), and every part of the support check follows from
the premises ({name}`LiteralData.upsertBounded_inserted`, {name}`LiteralData.constraints_of_appended`). -/
theorem runStatement_insertSelect_none_ok (clock : Int) (counters : Counters) (parameters : List Value)
    (target : Nat) (cells : List Resolved.SourceCell) (query : Resolved.Query)
    (clauses : List Resolved.ConflictClause) (returning : List (Resolved.Expr × String))
    (algorithm : Option ConflictAlgorithm) (subqueries : List Resolved.Query) (database : Database)
    (table : Table) (rows : List (List Value)) (found : database.table target = some table)
    (certain : query.productions (Resolved.statementContext clock counters parameters database subqueries) database
      (!Resolved.Statement.collectsSource target query subqueries returning none) =
        some [{ rows, failure := none }])
    (fits : InsertFits (database.keys target table) table
      (insertSelectRows (Resolved.statementContext clock counters parameters database subqueries)
        table.shape.columns cells rows))
    (clauseColumns : clauses.all (fun clause => match clause.action with
      | .nothing => true
      | .update assignments _ => assignments.all fun (position, _) => (table.shape.columns[position]?).isSome) = true)
    (transfer : ∀ source, insertSelectTransferRowids target cells query table database none = some source →
      ((LiteralData.inserted table (insertSelectRows (Resolved.statementContext clock counters parameters database
        subqueries) table.shape.columns cells rows)).rows.drop table.rows.length).map (·.rowid) = source)
    (plainSubqueries : Resolved.subqueriesPlain subqueries = true)
    (fixedCells : Resolved.cellsReady (Resolved.statementContext clock counters parameters database subqueries)
      [cells.filterMap fun | .cell fixed => some fixed | .source _ => none] = true)
    (json : upsertJsonReady clauses returning = true) :
    (runStatement clock counters parameters (.insertSelect target cells query clauses returning algorithm subqueries none)
      database).effect = .ok (database.setRows target (LiteralData.inserted table (insertSelectRows
        (Resolved.statementContext clock counters parameters database subqueries) table.shape.columns cells rows)).rows) ∧
    (runStatement clock counters parameters (.insertSelect target cells query clauses returning algorithm subqueries none)
      database).ready = true ∧
    (runStatement clock counters parameters (.insertSelect target cells query clauses returning algorithm subqueries none)
      database).alternatives = [] := by
  rw [show runStatement clock counters parameters (.insertSelect target cells query clauses returning algorithm subqueries none)
    database = insertSelectRun clock counters parameters target cells query clauses returning algorithm subqueries none database
    from rfl]
  unfold insertSelectRun
  simp only [found, certain]
  have passes : LiteralData.constraints (database.keys target table) (LiteralData.inserted table (insertSelectRows
      (Resolved.statementContext clock counters parameters database subqueries) table.shape.columns cells rows)) = true := by
    simp [LiteralData.constraints, fits.notNull, fits.typed, fits.checked, fits.keysDistinct]
  have summary := LiteralData.upsertSummary_inserted (Resolved.statementContext clock counters parameters database subqueries)
    (database.keys target table) (database.catalog.writePolicy target table.shape algorithm) clauses table _ fits.aliasFree
    passes fits.rowidsDistinct
  obtain ⟨added, appended⟩ := LiteralData.inserted_rows_prefix table (insertSelectRows
    (Resolved.statementContext clock counters parameters database subqueries) table.shape.columns cells rows)
  have tableOk : LiteralData.tableReady (database.keys target table) table = true :=
    LiteralData.constraints_of_appended (LiteralData.shape_inserted _ _) appended passes
  have readyRun : LiteralData.upsertReady (database.keys target table) table clauses
      (insertSelectRows (Resolved.statementContext clock counters parameters database subqueries)
        table.shape.columns cells rows)
      (LiteralData.upsertSteps (Resolved.statementContext clock counters parameters database subqueries)
        (database.keys target table) (database.catalog.writePolicy target table.shape algorithm) clauses table
        (insertSelectRows (Resolved.statementContext clock counters parameters database subqueries)
          table.shape.columns cells rows)) = true := by
    have bounded := LiteralData.upsertBounded_inserted
      (Resolved.statementContext clock counters parameters database subqueries) (database.keys target table)
      (database.catalog.writePolicy target table.shape algorithm) clauses table _ fits.aliasFree passes
      fits.rowidsDistinct fits.rowidsBounded
    simp only [LiteralData.upsertReady, Bool.and_eq_true]
    exact ⟨⟨⟨⟨tableOk, fits.aliasInteger⟩, by simpa using fits.stored⟩, clauseColumns⟩, bounded⟩
  have written := LiteralData.upsertWritten_of_summary table _ summary
  simp only [insertSelectOutcome, summary, Option.map_none, StatementRun.withKeys, readyRun]
  refine ⟨trivial, ?_, by simp⟩
  simp only [Bool.and_eq_true, Option.isNone_none, Bool.true_or, Bool.and_true, plainSubqueries, json, true_and]
  refine ⟨⟨by simp, ?_⟩, fixedCells⟩
  cases rowids : insertSelectTransferRowids target cells query table database none with
  | none => simp [insertSelectTransferReady]
  | some source =>
    have same := transfer source rowids
    simpa [insertSelectTransferReady, written] using same

end Belay.Sqlite.Model
