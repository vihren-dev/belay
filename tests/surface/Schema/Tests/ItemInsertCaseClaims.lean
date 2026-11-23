import ItemInsertCaseChecks

set_option doc.verso true

/-! A fixture module of {lit}`tests/surface_schema_script_test.py` (statement rule pilot, "Case type of plain
INSERT"): the two INSERT claims of {lit}`ItemInsertClaims`, proved with the checks of {lit}`ItemInsertCaseChecks`
that use the case type of plain INSERT, and a claim for each input with two proofs. One proof uses the cover of the
case type; the other splits on whether the key is taken and uses the case laws. -/

namespace ItemInsertCaseClaims
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database
open ItemInsertSite (insertItem itemsCatalog itemRow insert_new_check insert_taken_check)

/-- The claim {name}`ItemInsertSite.new_key_inserts` with the same statement, proved with the case type: for every
id and name, every database whose catalog is {name}`itemsCatalog` and whose table {lit}`items` has no row with the id
as its rowid, and every complete environment, the fresh run of {name}`insertItem` ends with
{lean}`[Output.done 1]`, the old rows and {name}`itemRow`, {lit}`changes()` 1 and {lit}`last_insert_rowid()` the id. -/
theorem new_key_inserts (id : Int64) (name : String) :
    FreshTriple (send (insertItem id name))
      (fun db => db.raw.catalog = itemsCatalog ∧ ∀ row ∈ db.raw.rows.getD 0 [], row.rowid ≠ id.toInt)
      (fun db _ _ final => final.outputs = [.done 1] ∧
        final.connection.state.database = db.raw.setRows 0 (db.raw.rows.getD 0 [] ++ [itemRow id name]) ∧
        final.connection.state.counters.changes = some 1 ∧
        final.connection.state.counters.lastInsertRowid = some id.toInt) := by
  rintro ⟨⟨catalog, rows⟩, valid⟩ ⟨same, fresh⟩ env _complete
  dsimp only at same fresh
  subst same
  exact insert_new_case (ExecutionContext.initial_holds_valid ⟨_, valid⟩ env) fresh
    (by simp [ExecutionContext.next, Connection.afterWrite, Counters.apply])

/-- The claim {name}`ItemInsertSite.taken_key_fails` with the same statement, proved with the case type: for every
id and name, every database whose catalog is {name}`itemsCatalog` and whose table {lit}`items` has a row with the id
as its rowid, and every complete environment, the fresh run of {name}`insertItem` ends with
{lean}`[Output.error 19]`, the database before the run and {lit}`changes()` 0. -/
theorem taken_key_fails (id : Int64) (name : String) :
    FreshTriple (send (insertItem id name))
      (fun db => db.raw.catalog = itemsCatalog ∧ ∃ row ∈ db.raw.rows.getD 0 [], row.rowid = id.toInt)
      (fun db _ _ final => final.outputs = [.error 19] ∧ final.connection.state.database = db.raw ∧
        final.connection.state.counters.changes = some 0) := by
  rintro ⟨⟨catalog, rows⟩, valid⟩ ⟨same, taken⟩ env _complete
  dsimp only at same taken
  subst same
  exact insert_taken_case (ExecutionContext.initial_holds_valid ⟨_, valid⟩ env) taken fun counts changes => by
    simp [ExecutionContext.next, Connection.afterWrite, Counters.apply, changes]

/-- Client claim "each insert of an item succeeds or keeps the database", proved with the case type. For every id
and name, every database whose catalog is {name}`itemsCatalog`, and every complete environment, the fresh run of
{name}`insertItem` ends in one of these:
* the outputs {lean}`[Output.done 1]` and the database with the old rows of {lit}`items` and {name}`itemRow` after
  them;
* the outputs with one error output, of some code, and the database before the run.
The claim has no premise about the id. Proof: {name}`insert_any_case`. -/
theorem insert_done_or_error (id : Int64) (name : String) :
    FreshTriple (send (insertItem id name)) (fun db => db.raw.catalog = itemsCatalog)
      (fun db _ _ final => (final.outputs = [.done 1] ∧
          final.connection.state.database = db.raw.setRows 0 (db.raw.rows.getD 0 [] ++ [itemRow id name])) ∨
        (∃ code, final.outputs = [.error code] ∧ final.connection.state.database = db.raw)) := by
  rintro ⟨⟨catalog, rows⟩, valid⟩ same env _complete
  dsimp only at same
  subst same
  exact insert_any_case (ExecutionContext.initial_holds_valid ⟨_, valid⟩ env)
    (.inl (by simp [ExecutionContext.next, Connection.afterWrite]))
    fun code _ => .inr ⟨code, by simp [ExecutionContext.next, Connection.afterWrite]⟩

/-- The statement of {name}`insert_done_or_error`, proved without the case type: for every id and name, every
database whose catalog is {name}`itemsCatalog`, and every complete environment, the fresh run of {name}`insertItem`
ends with {lean}`[Output.done 1]` and the database with {name}`itemRow` after the old rows, or with one error output
and the database before the run. Proof sketch: split on whether a stored item has the id as its rowid; the claims
{name}`insert_taken_check` and {name}`insert_new_check`, which use the case laws, give each side. -/
theorem insert_done_or_error_by_laws (id : Int64) (name : String) :
    FreshTriple (send (insertItem id name)) (fun db => db.raw.catalog = itemsCatalog)
      (fun db _ _ final => (final.outputs = [.done 1] ∧
          final.connection.state.database = db.raw.setRows 0 (db.raw.rows.getD 0 [] ++ [itemRow id name])) ∨
        (∃ code, final.outputs = [.error code] ∧ final.connection.state.database = db.raw)) := by
  rintro ⟨⟨catalog, rows⟩, valid⟩ same env _complete
  dsimp only at same
  subst same
  by_cases taken : ∃ row ∈ rows.getD 0 [], row.rowid = id.toInt
  · exact insert_taken_check (ExecutionContext.initial_holds_valid ⟨_, valid⟩ env) taken
      fun _ _ => .inr ⟨19, by simp [ExecutionContext.next, Connection.afterWrite]⟩
  · exact insert_new_check (ExecutionContext.initial_holds_valid ⟨_, valid⟩ env)
      (fun row member same => taken ⟨row, member, same⟩)
      (.inl (by simp [ExecutionContext.next, Connection.afterWrite]))

#print axioms new_key_inserts
#print axioms taken_key_fails
#print axioms insert_done_or_error
#print axioms insert_done_or_error_by_laws

end ItemInsertCaseClaims
