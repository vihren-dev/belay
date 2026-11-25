import ItemInsertOutcomes

set_option doc.verso true

/-! A fixture module of {lit}`tests/surface_schema_script_test.py` (statement rule pilot, "Client claims"): the
claim for each input of the insert of one item into {lit}`items`. The claim has no premise about whether the key is
taken: the insert succeeds with the new row, or it fails with an error output and keeps the database. The proof
uses the kind rule {name}`Belay.Sqlite.Model.runScriptStep_plainInsert_eq` through the bridge
{name}`Belay.Sqlite.Sql.check_send_of_rule` and the data facts of {lit}`ItemInsertSite` and
{lit}`ItemInsertOutcomes`; it does not name the step function, its implementation, the resolver or the statement
run. -/

namespace ItemInsertSite
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- For every clock, index, counters, outputs, row lists, id, name and post, from a context whose connection has the
database with {name}`itemsCatalog` and the rows: if that connection is valid, then the insert checks the post when
these two conditions hold:
* the post holds for the output {lean}`Output.done 1` in the context after the connection that stores
  {name}`itemRow` and counts one change with the id as the last rowid;
* for each code and counts, the post holds for the error output ({name}`Output.error`) of the code in the context
  after the connection with the same database and those counts.
The id can be new or taken. Proof sketch: the bridge with the kind rule of plain INSERT; the site facts reduce the
checks of the clock, the counters, the table and the readiness, and a split on the outcome gives the success case,
with {name}`insertOutcome_ok`, or the failure case. -/
theorem insert_any_rule {clock : Option Clock} {index : Nat} {counters : Counters} {outputs : List Output}
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
  refine Sql.check_send_of_rule (runScriptStep_plainInsert_eq (target := 0) (rows := itemCells) (subqueries := [])
    (by rfl)) valid ?_ ?_
  all_goals
    dsimp only [Database.Raw.connection, List.headD]
    simp only [items_clock, items_reads, Counters.firstUnknown, items_table, items_values, items_ready rows valid.1,
      items_cellsReady, Resolved.subqueriesPlain, List.find?_nil, List.all_nil, Bool.and_self, ↓reduceIte]
  · split <;> rfl
  · split
    · rename_i written outcome
      rw [outcome, insertOutcome_ok outcome]
      refine Sql.sendReached_single (fun _ same => by cases same) fun _ => ?_
      simp only [items_counts_ok, items_inserted]
      exact done
    · exact Sql.sendReached_single (fun _ same => by cases same) fun _ => failed _ _

/-- Client claim "each insert of an item succeeds or keeps the database". For every id and name, every database
whose catalog is {name}`itemsCatalog`, and every complete environment, the fresh run of {name}`insertItem` ends in
one of these:
* the outputs {lean}`[Output.done 1]` and the database with the old rows of {lit}`items` and {name}`itemRow` after
  them;
* the outputs with one error output, of some code, and the database before the run.
The claim has no premise about the id. Proof: {name}`insert_any_rule`. -/
theorem insert_done_or_error (id : Int64) (name : String) :
    FreshTriple (send (insertItem id name)) (fun db => db.raw.catalog = itemsCatalog)
      (fun db _ _ final => (final.outputs = [.done 1] ∧
          final.connection.state.database = db.raw.setRows 0 (db.raw.rows.getD 0 [] ++ [itemRow id name])) ∨
        (∃ code, final.outputs = [.error code] ∧ final.connection.state.database = db.raw)) := by
  rintro ⟨⟨catalog, rows⟩, valid⟩ same env _complete
  dsimp only at same
  subst same
  exact insert_any_rule (ExecutionContext.initial_holds_valid ⟨_, valid⟩ env)
    (.inl (by simp [ExecutionContext.next, Connection.afterWrite]))
    fun code _ => .inr ⟨code, by simp [ExecutionContext.next, Connection.afterWrite]⟩

#print axioms insert_done_or_error

end ItemInsertSite
