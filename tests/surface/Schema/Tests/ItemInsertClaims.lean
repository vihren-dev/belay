import ItemInsertOutcomes

set_option doc.verso true

/-! A fixture module of {lit}`tests/surface_schema_script_test.py` (statement rule pilot, "Client claims"): claims
that a client can state and prove about programs on databases with the catalog {name}`ItemInsertSite.itemsCatalog`
and arbitrary valid rows. They check the kind rules {name}`Belay.Sqlite.Model.runScriptStep_plainInsert_eq` and
{name}`Belay.Sqlite.Model.runScriptStep_createTable_eq` through the bridge
{name}`Belay.Sqlite.Sql.check_send_of_rule`, and the path of
{lit}`sql_run` through the kind rules. The proofs use the kind rules, the bridge and the data facts of
{lit}`ItemInsertSite` and {lit}`ItemInsertOutcomes`; they do not name the step function, its implementation, the
resolver or the statement run. The claim for each input is in {lit}`ItemInsertAnyClaims`. -/

namespace ItemInsertSite
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- For every clock, index, counters, outputs, row lists, id, name and post, from a context whose connection has the
database with {name}`itemsCatalog` and the rows: if that connection is valid, no stored item has the id as its rowid,
and the post holds for the output {lean}`Output.done 1` in the context after the connection that stores
{name}`itemRow` and counts one change with the id as the last rowid, then the insert checks the post. Proof sketch:
the bridge with the kind rule of plain INSERT; the site facts and {name}`insertOutcome_of_fits` with
{name}`items_fits` select the success case of the rule. -/
theorem insert_new_check {clock : Option Clock} {index : Nat} {counters : Counters} {outputs : List Output}
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
  refine Sql.check_send_of_rule (runScriptStep_plainInsert_eq (target := 0) (rows := itemCells) (subqueries := [])
    (by rfl)) valid ?_ ?_
  all_goals dsimp only [Database.Raw.connection, List.headD]
  all_goals simp only [items_clock, items_reads, items_table, items_values, Counters.firstUnknown, List.find?_nil,
    items_ready rows valid.1, Resolved.subqueriesPlain, List.all_nil, items_cellsReady, Bool.and_self, ↓reduceIte,
    insertOutcome_of_fits (items_fits rows valid.1 id name fresh)]
  · rfl
  refine Sql.sendReached_single (fun _ same => by cases same) fun _ => ?_
  simp only [items_counts_ok, items_inserted]
  exact holds

/-- Client claim "an insert of a new key succeeds". For every id and name, every database whose catalog is
{name}`itemsCatalog` and whose table {lit}`items` has no row with the id as its rowid, and every complete
environment: the fresh run of {name}`insertItem` ends with the outputs {lean}`[Output.done 1]`, the database with
the old rows of {lit}`items` and {name}`itemRow` after them, {lit}`changes()` 1 and {lit}`last_insert_rowid()` the
id. -/
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
  exact insert_new_check (ExecutionContext.initial_holds_valid ⟨_, valid⟩ env) fresh
    (by simp [ExecutionContext.next, Connection.afterWrite, Counters.apply])

/-- For every clock, index, counters, outputs, row lists, id, name and post, from a context whose connection has the
database with {name}`itemsCatalog` and the rows: if that connection is valid, a stored item has the id as its rowid,
and for all counts with no change the post holds for the output {lean}`Output.error 19` in the context after the
connection with the same database and those counts, then the insert checks the post. Proof sketch: the bridge with
the kind rule of plain INSERT; the site facts and {name}`items_taken_outcome` select the failure case of the rule.
-/
theorem insert_taken_check {clock : Option Clock} {index : Nat} {counters : Counters} {outputs : List Output}
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
  refine Sql.check_send_of_rule (runScriptStep_plainInsert_eq (target := 0) (rows := itemCells) (subqueries := [])
    (by rfl)) valid ?_ ?_
  all_goals dsimp only [Database.Raw.connection, List.headD]
  all_goals simp only [items_clock, items_reads, items_table, items_values, Counters.firstUnknown, List.find?_nil,
    items_ready rows valid.1, Resolved.subqueriesPlain, List.all_nil, items_cellsReady, Bool.and_self, ↓reduceIte,
    items_taken_outcome rows id name taken]
  · rfl
  exact Sql.sendReached_single (fun _ same => by cases same) fun _ => holds _ rfl

/-- Client claim "an insert of a key that the table holds fails". For every id and name, every database whose
catalog is {name}`itemsCatalog` and whose table {lit}`items` has a row with the id as its rowid, and every complete
environment: the fresh run of {name}`insertItem` ends with the outputs {lean}`[Output.error 19]`, the database
before the run and {lit}`changes()` 0. -/
theorem taken_key_fails (id : Int64) (name : String) :
    FreshTriple (send (insertItem id name))
      (fun db => db.raw.catalog = itemsCatalog ∧ ∃ row ∈ db.raw.rows.getD 0 [], row.rowid = id.toInt)
      (fun db _ _ final => final.outputs = [.error 19] ∧ final.connection.state.database = db.raw ∧
        final.connection.state.counters.changes = some 0) := by
  rintro ⟨⟨catalog, rows⟩, valid⟩ ⟨same, taken⟩ env _complete
  dsimp only at same taken
  subst same
  exact insert_taken_check (ExecutionContext.initial_holds_valid ⟨_, valid⟩ env) taken fun counts changes => by
    simp [ExecutionContext.next, Connection.afterWrite, Counters.apply, changes]

/-- The program text that creates the table {lit}`items`. -/
def createItems : Script := sql r"CREATE TABLE items(id INTEGER PRIMARY KEY, name TEXT)"

/-- The program that creates the table {lit}`items` and then inserts one item. -/
def createAndInsert (id : Int64) (name : String) : Sql (List Output) := do
  let _ ← send createItems
  send (insertItem id name)

/-- Client claim "a program that creates a table and inserts a row into it succeeds". For every id and name, every
database with an empty catalog, and every complete environment: the fresh run of {name}`createAndInsert` ends with
the outputs {lean}`[Output.done 0, Output.done 1]`, and the table at position 0 is {name}`itemsShape` with exactly
the row {name}`itemRow`. Proof sketch: the bridge with the kind rule of CREATE TABLE, whose guard holds on the
valid empty database; after it, the database has {name}`itemsCatalog` and one empty row list, so
{name}`insert_new_check` applies. -/
theorem create_then_insert (id : Int64) (name : String) :
    FreshTriple (createAndInsert id name) (fun db => db.raw.catalog = [])
      (fun _ _ _ final => final.outputs = [.done 0, .done 1] ∧
        final.connection.state.database.table 0 = some ⟨itemsShape, [itemRow id name]⟩) := by
  rintro ⟨⟨catalog, rows⟩, valid⟩ same env _complete
  dsimp only at same
  subst same
  obtain rfl : rows = [] := List.eq_nil_of_length_eq_zero valid.admitted.rowsShaped.1
  have created : Catalog.createTable [] (name! "items") itemsShape = itemsCatalog := by
    rw [items_catalog]
    rfl
  unfold createAndInsert createItems
  refine (Sql.check_bind _ _ _ _).2 ?_
  refine Sql.check_send_of_rule (runScriptStep_createTable_eq (target := 0) (name := name! "items")
    (table := itemsShape) (by with_unfolding_all rfl)) (ExecutionContext.initial_holds_valid ⟨_, valid⟩ env) rfl ?_
  refine Sql.sendReached_single (fun _ same => by cases same) fun createdValid => ?_
  simp only [ExecutionContext.next, ExecutionContext.initial, Connection.withDatabase, Database.createTable,
    Database.Raw.connection, created, List.nil_append] at createdValid ⊢
  refine insert_new_check (rows := [[]]) createdValid (by simp) ?_
  simp [ExecutionContext.next, Connection.afterWrite, Database.setRows, items_table]

/-- For the given database: no row of the first row list has NULL, or no cell, at position 1 (the column
{lit}`name` of {lit}`items`). A database without rows there satisfies it. -/
def NamesPresent (database : Model.Database) : Prop :=
  ∀ row ∈ database.rows.getD 0 [], row.values.getD 1 .null ≠ .null

/-- Client claim "the program preserves a condition on the database", proved with {lit}`sql_run`. For every id and
name, every database whose catalog is {name}`itemsCatalog` and which satisfies {name}`NamesPresent`, and every
complete environment: the final database of the fresh run of {name}`insertItem` satisfies {name}`NamesPresent`,
whether the insert succeeds or fails. Proof sketch: {lit}`sql_run` applies the kind rule of plain INSERT and leaves
three goals. In {lit}`modeled`, the hypothesis {lit}`rule` rewrites the step, and the data facts reduce it to a step
that continues in both outcomes. In {lit}`success`, the new row has a text name and the old rows keep theirs. In
{lit}`failure`, the database does not change. -/
theorem insert_keeps_names (id : Int64) (name : String) :
    FreshTriple (send (insertItem id name)) (fun db => db.raw.catalog = itemsCatalog ∧ NamesPresent db.raw)
      (fun _ _ _ final => NamesPresent final.connection.state.database) := by
  rintro ⟨⟨catalog, rows⟩, valid⟩ ⟨same, before⟩ env _complete
  dsimp only at same
  subst same
  unfold insertItem
  sql_run [rfl, items_table rows]
  case modeled =>
    rw [rule]
    simp only [ExecutionContext.initial, Database.Raw.connection, List.headD, List.map_nil, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some, Resolved.Cell.stored, Nat.zero_add]
    simp only [items_clock, items_reads, items_table, items_values, Counters.firstUnknown, List.find?_nil,
      items_ready rows valid, Resolved.subqueriesPlain, List.all_nil, items_cellsReady, Bool.and_self, ↓reduceIte]
    split <;> rfl
  case success =>
    simp only [ExecutionContext.next, ExecutionContext.initial, Connection.afterWrite, Database.Raw.connection,
      List.headD, List.map_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
      Resolved.Cell.stored, Nat.zero_add]
    erw [items_values, items_inserted]
    intro row member
    cases rows with
    | nil => simp [Database.setRows] at member
    | cons first rest =>
      simp only [Database.setRows, List.set_cons_zero, List.getD_cons_zero, List.mem_append, List.mem_singleton]
        at member
      rcases member with old | rfl
      · exact before row (by simpa using old)
      · simp [itemRow, itemValues]
  case failure =>
    simp only [ExecutionContext.next, ExecutionContext.initial, Connection.afterWrite, Database.Raw.connection]
    exact before

#print axioms new_key_inserts
#print axioms taken_key_fails
#print axioms create_then_insert
#print axioms insert_keeps_names

end ItemInsertSite
