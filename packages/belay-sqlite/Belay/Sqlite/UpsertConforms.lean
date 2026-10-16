import Belay.Sqlite.UpsertPreservation

set_option doc.verso true

/-! {lit}`Conforms` after INSERT with {lit}`ON CONFLICT` clauses (ADR 0012, amendment 4,
slice 5c): by induction on the rows, each successful row of {lit}`LiteralData.upsertRun`
keeps the table's shape and {lit}`Table.Valid`, so the final table conforms. -/

namespace Belay.Sqlite

/-- For every valid table and one row of an UPSERT: assume
{name}`LiteralData.aliasReady`, one value per column in stored form, a bounded
{name}`LiteralData.newRowid`, and bounded rowids in the table after the row. If
{name}`LiteralData.upsertRow` succeeds, its table has the same shape and is
{name}`Table.Valid`. Proof sketch: a skipped row keeps the table; an inserted row is
{name}`Table.RowsValid.insertRow` with the distinct rowids of the check; an updated row
is {name}`LiteralData.updateExisting_valid` of the conflicting row, a row of the table
({name}`LiteralData.handlingClause_mem`). -/
theorem LiteralData.upsertRow_valid {keys : List (List Nat)} {clauses : List Resolved.ConflictClause}
    {table next : Table} {values : List Value} {written : Option Row} (valid : table.Valid)
    (ready : aliasReady table.shape = true) (width : values.length = table.shape.columns.length)
    (stored : Row.Stored table.shape.columns { rowid := 0, values })
    (boundedNew : boundedInteger (newRowid table values) = true)
    (bounded : next.rows.all (fun row => boundedInteger row.rowid) = true)
    (step : upsertRow keys clauses table values = .ok (next, written)) :
    next.shape = table.shape ∧ next.Valid := by
  unfold upsertRow at step
  dsimp only at step
  split at step
  · cases step
  split at step
  · cases step
  split at step
  · unfold checkedRow at step
    split at step
    · rename_i passed
      cases step
      have distinct := of_decide_eq_true ((Bool.and_eq_true _ _).mp passed).2
      exact ⟨rfl, distinct, valid.2.insertRow ready (by simpa [boundedInteger, validRowid] using boundedNew)
        width stored⟩
    · cases step
  · rename_i clause existing found
    have member := handlingClause_mem found
    split at step
    · cases step; exact ⟨rfl, valid⟩
    · exact updateExisting_valid valid member bounded step

/-- For every valid table and value rows of an UPSERT: assume
{name}`LiteralData.aliasReady`, one value per column in stored form in every row, and
{name}`LiteralData.upsertBounded`. If {name}`LiteralData.upsertRun` succeeds, its final
table has the same shape and is {name}`Table.Valid`. Proof sketch: induction on the
rows with {name}`LiteralData.upsertRow_valid`; each row keeps the shape, so the
premises about the shape hold for the next row. -/
theorem LiteralData.upsertRun_valid {keys : List (List Nat)} {clauses : List Resolved.ConflictClause} :
    ∀ {rows : List (List Value)} {table final : Table} {written : List Row}, table.Valid →
    aliasReady table.shape = true →
    (∀ values ∈ rows, values.length = table.shape.columns.length ∧
      (table.shape.columns.zip values).all (fun (column, value) => storedForm column.affinity value) = true) →
    upsertBounded keys clauses table rows = true →
    upsertRun keys clauses table rows = .ok (final, written) → final.shape = table.shape ∧ final.Valid
  | [], _, _, _, valid, _, _, _, run => by cases run; exact ⟨rfl, valid⟩
  | values :: rest, table, final, written, valid, ready, each, bounded, run => by
    simp only [upsertBounded, Bool.and_eq_true] at bounded
    obtain ⟨boundedNew, boundedRest⟩ := bounded
    unfold upsertRun at run
    split at run
    · cases run
    rename_i next written' step
    rw [step] at boundedRest
    simp only [Bool.and_eq_true] at boundedRest
    obtain ⟨width, storedForm⟩ := each values (by simp)
    obtain ⟨shape, nextValid⟩ := upsertRow_valid valid ready width (Row.Stored.of_storedForm storedForm)
      boundedNew boundedRest.1 step
    split at run
    · cases run
    rename_i final' later rest_run
    cases run
    obtain ⟨finalShape, finalValid⟩ := upsertRun_valid nextValid (shape ▸ ready)
      (fun row member => shape ▸ each row (List.mem_cons_of_mem _ member)) boundedRest.2 rest_run
    exact ⟨finalShape.trans shape, finalValid⟩

/-- For every profile, catalog and database, and every UPSERT that
{name}`statementReady` admits: if the database {name}`Conforms` to the catalog, so does
the database of its step, at every statement position. Proof sketch: without a table or
after an error the step keeps the database; otherwise
{name}`LiteralData.upsertRun_valid` gives the shape and validity of the final table, and
{name}`Conforms.replaceRows` stores it. -/
theorem literalStep_upsert_conforms (conforms : Conforms profile catalog database)
    (ready : statementReady (.upsert at_ rows clauses keys returning) database = true) (position : Nat) :
    Conforms profile catalog (literalStep (.upsert at_ rows clauses keys returning) database position).database := by
  cases present : database at_ with
  | none => simp only [literalStep, present]; exact conforms
  | some table =>
    simp only [literalStep, present]
    simp only [statementReady, present, Option.all_some, LiteralData.upsertReady, Bool.and_eq_true] at ready
    obtain ⟨⟨⟨⟨_, aliasOk⟩, each⟩, _⟩, bounded⟩ := ready
    split
    · rename_i result _ run
      obtain ⟨shape, valid⟩ := LiteralData.upsertRun_valid ((conforms.2 at_).2 table present) aliasOk
        (fun values member => by
          have check := List.all_eq_true.mp each values member
          simp only [Bool.and_eq_true, beq_iff_eq] at check
          exact ⟨check.1, check.2⟩) bounded run
      exact conforms.replaceRows present shape valid
    · exact conforms

end Belay.Sqlite
