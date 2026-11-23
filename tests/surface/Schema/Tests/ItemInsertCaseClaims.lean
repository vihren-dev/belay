import ItemInsertClaims

set_option doc.verso true

/-! A fixture module of {lit}`tests/surface_schema_script_test.py` (statement rule pilot, "Case type of plain
INSERT"): the two INSERT claims of {lit}`ItemInsertClaims`, proved with the case type of plain INSERT
({name}`Belay.Sqlite.Model.PlainInsertCase`), and a claim for each input with two proofs. One proof splits the cover
of the case type; the other splits on whether the key is taken and uses the case laws. The proofs with the case type
name no kind rule and no case law. -/

namespace ItemInsertCaseClaims
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database
open ItemInsertSite (insertItem itemsCatalog itemRow itemCells items_clock items_reads items_table items_values
  items_ready items_fits items_taken_outcome items_cellsReady items_counts_ok items_inserted insert_new_check
  insert_taken_check)

/-- The statement of {name}`ItemInsertSite.insert_new_check`, proved with the case type. For every clock, index,
counters, outputs, row lists, id, name and post, from a context whose connection has the database with
{name}`itemsCatalog` and the rows: if that connection is valid, no stored item has the id as its rowid, and the post
holds for the output {lean}`Output.done 1` in the context after the connection that stores {name}`itemRow` and
counts one change with the id as the last rowid, then the insert checks the post. Proof sketch: the bridge with the
step equation {name}`runScriptStep_plainInsert_of_case` of the case {lit}`checked` with {lit}`success`; the site
facts give the premises of the case, and {name}`insertOutcome_of_fits` with {name}`items_fits` gives the outcome. -/
theorem insert_new_case {clock : Option Clock} {index : Nat} {counters : Counters} {outputs : List Output}
    {rows : List (List Row)} {id : Int64} {name : String} {post : List Output → ExecutionContext → Prop}
    (valid : (Database.Raw.connection { catalog := itemsCatalog, rows } counters).state.Holds
      (Model.Database.Valid Profile.pinned))
    (fresh : ∀ row ∈ rows.getD 0 [], row.rowid ≠ id.toInt)
    (holds : post [.done 1] (ExecutionContext.next ⟨clock, index, Database.Raw.connection { catalog := itemsCatalog, rows }
      counters, outputs⟩ (.done 1) ((Database.Raw.connection { catalog := itemsCatalog, rows } counters).afterWrite
        (({ catalog := itemsCatalog, rows } : Model.Database).setRows 0 (rows.getD 0 [] ++ [itemRow id name]))
        { changes := some 1, total := 1, lastRowid := some id.toInt }))) :
    (send (insertItem id name)).check post ⟨clock, index, Database.Raw.connection { catalog := itemsCatalog, rows } counters,
      outputs⟩ := by
  unfold insertItem
  refine Sql.check_send_of_rule (runScriptStep_plainInsert_of_case (target := 0) (rows := itemCells) (subqueries := [])
    (by rfl) (.checked (items_clock _ _) (by rw [items_reads]; rfl) (.success (items_table rows) (items_values _ _ _ id name)
      (items_ready rows valid.1 id name) rfl (items_cellsReady _)
      (insertOutcome_of_fits (items_fits rows valid.1 id name fresh))))) valid rfl ?_
  refine Sql.sendReached_single (fun _ same => by cases same) fun _ => ?_
  dsimp only [Database.Raw.connection, List.headD] at holds ⊢
  simp only [items_counts_ok, items_inserted]
  exact holds

/-- The statement of {name}`ItemInsertSite.insert_taken_check`, proved with the case type. For every clock, index,
counters, outputs, row lists, id, name and post, from a context whose connection has the database with
{name}`itemsCatalog` and the rows: if that connection is valid, a stored item has the id as its rowid, and for all
counts with no change the post holds for the output {lean}`Output.error 19` in the context after the connection with
the same database and those counts, then the insert checks the post. Proof sketch: the bridge with the step equation
of the case {lit}`checked` with {lit}`failure`; {name}`items_taken_outcome` gives the failed outcome. -/
theorem insert_taken_case {clock : Option Clock} {index : Nat} {counters : Counters} {outputs : List Output}
    {rows : List (List Row)} {id : Int64} {name : String} {post : List Output → ExecutionContext → Prop}
    (valid : (Database.Raw.connection { catalog := itemsCatalog, rows } counters).state.Holds
      (Model.Database.Valid Profile.pinned))
    (taken : ∃ row ∈ rows.getD 0 [], row.rowid = id.toInt)
    (holds : ∀ counts : Counts, counts.changes = some 0 → post [.error 19] (ExecutionContext.next ⟨clock, index,
      Database.Raw.connection { catalog := itemsCatalog, rows } counters, outputs⟩ (.error 19)
      ((Database.Raw.connection { catalog := itemsCatalog, rows } counters).afterWrite { catalog := itemsCatalog, rows }
        counts))) :
    (send (insertItem id name)).check post ⟨clock, index, Database.Raw.connection { catalog := itemsCatalog, rows } counters,
      outputs⟩ := by
  unfold insertItem
  refine Sql.check_send_of_rule (runScriptStep_plainInsert_of_case (target := 0) (rows := itemCells) (subqueries := [])
    (by rfl) (.checked (items_clock _ _) (by rw [items_reads]; rfl) (.failure (reason := .constraintViolation)
      (items_table rows) (items_values _ _ _ id name) (items_ready rows valid.1 id name) rfl (items_cellsReady _)
      (items_taken_outcome rows id name taken _ _)))) valid rfl ?_
  exact Sql.sendReached_single (fun _ same => by cases same) fun _ => holds _ LiteralData.insertCounts_error_changes

/-- For every clock, index, counters, outputs, row lists, id, name and post, from a context whose connection has the
database with {name}`itemsCatalog` and the rows: take these premises:
* the connection is valid;
* the post holds for the output {lean}`Output.done 1` in the context after the connection that stores the old rows
  and {name}`itemRow` after them, and counts one change with the id as the last rowid;
* for each code and counts, the post holds for the error output of the code in the context after the connection
  with the same database and the counts.
Then the insert checks the post. The theorem has no premise about the id. Proof sketch: the cover
{name}`runScriptStep_plainInsert_cover` relates the step to a case; the site facts exclude the cases in which the run
ends; in the case {lit}`success`, {name}`insertOutcome_ok` gives the database; the bridge gives the post. -/
theorem insert_any_case {clock : Option Clock} {index : Nat} {counters : Counters} {outputs : List Output}
    {rows : List (List Row)} {id : Int64} {name : String} {post : List Output → ExecutionContext → Prop}
    (valid : (Database.Raw.connection { catalog := itemsCatalog, rows } counters).state.Holds
      (Model.Database.Valid Profile.pinned))
    (done : post [.done 1] (ExecutionContext.next ⟨clock, index, Database.Raw.connection { catalog := itemsCatalog, rows }
      counters, outputs⟩ (.done 1) ((Database.Raw.connection { catalog := itemsCatalog, rows } counters).afterWrite
        (({ catalog := itemsCatalog, rows } : Model.Database).setRows 0 (rows.getD 0 [] ++ [itemRow id name]))
        { changes := some 1, total := 1, lastRowid := some id.toInt })))
    (failed : ∀ code counts, post [.error code] (ExecutionContext.next ⟨clock, index,
      Database.Raw.connection { catalog := itemsCatalog, rows } counters, outputs⟩ (.error code)
      ((Database.Raw.connection { catalog := itemsCatalog, rows } counters).afterWrite { catalog := itemsCatalog, rows }
        counts))) :
    (send (insertItem id name)).check post ⟨clock, index, Database.Raw.connection { catalog := itemsCatalog, rows } counters,
      outputs⟩ := by
  unfold insertItem
  generalize named : Syntax.Statement.insert _ _ _ _ = statement
  have cover := runScriptStep_plainInsert_cover (context := runContext) (clock := clock) (index := index)
    (connection := Database.Raw.connection { catalog := itemsCatalog, rows } counters) (statement := statement)
    (target := 0) (rows := itemCells) (subqueries := []) (parameters := [.integer id.toInt, .text name.toUTF8.toList])
    (by rw [← named]; rfl)
  generalize step : runScriptStep _ _ _ _ _ _ = result at cover
  cases cover with
  | noClock timed => simp [items_clock] at timed
  | unknownCounter timed unknown => simp [items_reads, Counters.firstUnknown] at unknown
  | checked timed known case =>
    dsimp only [Database.Raw.connection] at case
    cases case with
    | noTable located => simp [items_table] at located
    | unready located evaluated unready =>
      obtain rfl := Option.some.inj ((items_table rows).symm.trans located)
      obtain rfl := (items_values _ _ _ id name).symm.trans evaluated
      simp [items_ready rows valid.1, items_cellsReady, Resolved.subqueriesPlain] at unready
    | success located evaluated ready plain cells outcome =>
      obtain rfl := Option.some.inj ((items_table rows).symm.trans located)
      obtain rfl := (items_values _ _ _ id name).symm.trans evaluated
      obtain rfl := insertOutcome_ok outcome
      refine Sql.check_send_of_rule step valid rfl (Sql.sendReached_single (fun _ same => by cases same) fun _ => ?_)
      simp only [items_counts_ok, items_inserted]
      exact done
    | failure located evaluated ready plain cells outcome =>
      exact Sql.check_send_of_rule step valid rfl (Sql.sendReached_single (fun _ same => by cases same)
        fun _ => failed _ _)

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
* the outputs of one error and the database before the run.
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
ends with {lean}`[Output.done 1]` and the database with {name}`itemRow` after the old rows, or with one error and
the database before the run. Proof sketch: split on whether a stored item has the id as its rowid; the claims
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
