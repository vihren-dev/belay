import ItemInsertClaims

set_option doc.verso true

/-! A fixture module of {lit}`tests/surface_schema_script_test.py` (statement rule pilot, "Case type of plain
INSERT"): the checks of the insert of one item into {lit}`items`, proved with the case type of plain INSERT
({name}`Belay.Sqlite.Model.PlainInsertCase`). Two checks build one case and use the step equation
{name}`Belay.Sqlite.Model.runScriptStep_plainInsert_of_case`; the check for each input splits the cover
{name}`Belay.Sqlite.Model.runScriptStep_plainInsert_cover`. The proofs name no kind rule and no case law. -/

namespace ItemInsertCaseClaims
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database
open ItemInsertSite (insertItem itemsCatalog itemRow itemCells items_clock items_reads items_table items_values
  items_ready items_fits items_taken_outcome items_cellsReady items_counts_ok items_inserted)

/-- The statement of {name}`ItemInsertSite.insert_new_check`, proved with the case type. Take a clock, an index,
counters, outputs, row lists, an id, a name and a post. The starting context has the clock, the index, the outputs and
the connection ({name}`Database.Raw.connection`) of the database with {name}`itemsCatalog` and the rows, with the
counters. Take these premises:
* the connection is valid;
* no stored item has the id as its rowid;
* the post holds for the output {lean}`Output.done 1` in the context after the connection that stores
  {name}`itemRow` after the old rows and counts one change with the id as the last rowid.
Then the insert checks the post. Proof sketch: the bridge with the step equation
{name}`runScriptStep_plainInsert_of_case` of the case {lit}`checked` with {lit}`success`; the site facts give the
premises of the case, and {name}`insertOutcome_of_fits` with {name}`items_fits` gives the outcome. -/
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

/-- The statement of {name}`ItemInsertSite.insert_taken_check`, proved with the case type. Take a clock, an index,
counters, outputs, row lists, an id, a name and a post. The starting context has the clock, the index, the outputs and
the connection ({name}`Database.Raw.connection`) of the database with {name}`itemsCatalog` and the rows, with the
counters. Take these premises:
* the connection is valid;
* a stored item has the id as its rowid;
* for all counts whose {lit}`changes` is {lit}`some 0`, with any total and last rowid, the post holds for the
  output {lean}`Output.error 19` in the context after the connection with the same database and those counts.
Then the insert checks the post. Proof sketch: the bridge with the step equation of the case {lit}`checked` with
{lit}`failure`; {name}`items_taken_outcome` gives the failed outcome. -/
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

/-- The check of the insert for each input, proved with the case type. Take a clock, an index, counters, outputs, row
lists, an id, a name and a post. The starting context has the clock, the index, the outputs and the connection
({name}`Database.Raw.connection`) of the database with {name}`itemsCatalog` and the rows, with the counters. Take these
premises:
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
  obtain ⟨result, step, cover⟩ : ∃ result, _ = result ∧ StepCase _ _ _ _ _ result := ⟨_, rfl, cover⟩
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

end ItemInsertCaseClaims
