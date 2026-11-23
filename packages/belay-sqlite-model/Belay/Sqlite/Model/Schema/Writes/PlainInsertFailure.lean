import Belay.Sqlite.Model.Schema.Writes.PlainCounts

set_option doc.verso true

/-! Data facts of a plain INSERT that fails: the counts that it reports, and the outcome of rows that SQLite refuses
because of a constraint or a repeated rowid. The facts are about functions on tables, rows and databases; none of
them is about the step of a statement. The kind rule {lit}`runScriptStep_plainInsert_eq` selects its failure case
by the outcome of the insertion: a caller can prove that the outcome is an error with
{lit}`insertOutcome_constraintViolation`, and read the counters after the step with
{lit}`LiteralData.insertCounts_error_changes` and {lit}`LiteralData.insertCounts_error_total`. -/

namespace Belay.Sqlite.Model

/-- For every failure, keys, table and rows: the counts of a failed plain INSERT ({name}`LiteralData.insertCounts`)
report 0 changed rows. In plain words, {lit}`changes()` is 0 after an INSERT that fails, for each reason of the
failure. Proof: the error case of the definition. -/
theorem LiteralData.insertCounts_error_changes {failure : ExecutionError × Database} {keys : List UniqueKey}
    {table : Table} {rows : List (List Value)} :
    (LiteralData.insertCounts (.error failure) keys table rows).changes = some 0 := rfl

/-- For every failure, keys, table and rows: the counts of a failed plain INSERT add no row to
{lit}`total_changes()`. Proof: the error case of the definition. -/
theorem LiteralData.insertCounts_error_total {failure : ExecutionError × Database} {keys : List UniqueKey}
    {table : Table} {rows : List (List Value)} :
    (LiteralData.insertCounts (.error failure) keys table rows).total = 0 := rfl

/-- For every table whose rows are two lists one after the other, and a row of each list with the same rowid: the
rowids of the table are not distinct ({name}`LiteralData.rowidsDistinct`). In plain words, a new row whose rowid a
stored row has makes the table fail the check of distinct rowids. Each pair of rows at two positions is such a split
of the rows, so the theorem covers every repeated rowid. Proof sketch: the rowids of the two lists are not disjoint,
so the list of all rowids has a duplicate. -/
theorem LiteralData.rowidsDistinct_eq_false_of_repeated {table : Table} {before after : List Row} {old new : Row}
    (split : table.rows = before ++ after) (stored : old ∈ before) (added : new ∈ after)
    (same : old.rowid = new.rowid) : LiteralData.rowidsDistinct table = false := by
  unfold LiteralData.rowidsDistinct
  rw [split, List.map_append, decide_eq_false_iff_not, List.nodup_append]
  rintro ⟨-, -, disjoint⟩
  exact disjoint old.rowid (List.mem_map_of_mem stored) new.rowid (List.mem_map_of_mem added) same

/-- For every database, target, keys, table, rows and result table: if no row has an alias cell that SQLite refuses
({name}`LiteralData.aliasMismatch`), and the result violates a constraint of the keys or has a repeated rowid, the
outcome of the INSERT ({name}`insertOutcome`) is a constraint violation with the database before. In plain words,
when no supplied row has an alias cell that SQLite refuses, and the given result table breaks a NOT NULL, type,
CHECK or unique constraint or has a repeated rowid, the INSERT fails with code 19 and keeps the database. The theorem
does not relate the result table to the supplied rows; in the step of an INSERT it is
{name}`LiteralData.inserted` of the table and the rows. Proof sketch: with no alias mismatch,
{name}`insertOutcome` is {name}`checkedWrite` of the result, and its check fails. -/
theorem insertOutcome_constraintViolation {database : Database} {target : Nat} {keys : List UniqueKey}
    {table : Table} {values : List (List Value)} {result : Table}
    (aliasFree : ∀ row ∈ values, LiteralData.aliasMismatch table.shape row = false)
    (violates : LiteralData.constraints keys result = false ∨ LiteralData.rowidsDistinct result = false) :
    insertOutcome database target keys table values result = .error (.constraintViolation, database) := by
  have aliases : values.findIdx? (LiteralData.aliasMismatch table.shape) = none := by
    simpa [List.findIdx?_eq_none_iff] using aliasFree
  have failing : (LiteralData.constraints keys result && LiteralData.rowidsDistinct result) = false := by
    rcases violates with violated | violated <;> simp [violated]
  rw [insertOutcome, aliases]
  simp only [checkedWrite, failing, Bool.false_eq_true, ite_false]

end Belay.Sqlite.Model
