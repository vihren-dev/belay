import Belay

set_option doc.verso true

/-! ADR 0033 retention of the former write laws with their original premises. -/

namespace Belay.Sqlite.Model.ReplacedWriteModes
open Resolved

/-- The former {lit}`runScriptStep_insertSelect_ok`. A ready single successful production at a known time and counters continues with the updated database and counts. Proof sketch: apply the ordinary single-write projection; a successful production has an output for every RETURNING list. -/
theorem runScriptStep_insertSelect_ok {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value}
    {target : Nat} {cells : List Resolved.SourceCell} {query : Resolved.Query} {clauses : List Resolved.ConflictClause}
    {returning : List (Resolved.Expr × String)} {algorithm : Option ConflictAlgorithm} {subqueries : List Resolved.Query}
    {after : ResolveState} {value : Int} {database : Database}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.insertSelect target cells query clauses returning algorithm subqueries none, after))
    (timed : statementClock clock index (.insertSelect target cells query clauses returning algorithm subqueries none) =
      some value)
    (known : connection.state.counters.firstUnknown
      (Resolved.Statement.insertSelect target cells query clauses returning algorithm subqueries none).counterReads = none)
    (ready : (connection.state.statementRun value parameters
      (.insertSelect target cells query clauses returning algorithm subqueries none)).ready = true)
    (effect : (connection.state.statementRun value parameters
      (.insertSelect target cells query clauses returning algorithm subqueries none)).effect = .ok database)
    (single : (connection.state.statementRun value parameters
      (.insertSelect target cells query clauses returning algorithm subqueries none)).alternatives = []) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] ∧
      output.isError = false ∧
      next = { connection with state := { connection.state with
        database := database
        counters := connection.state.counters.apply (connection.state.statementRun value parameters
          (.insertSelect target cells query clauses returning algorithm subqueries none)).counts } } := by
  exact runScriptStep_ordinary_ok found rfl (fun _ _ eq => by cases eq) timed ready single effect rfl

#print axioms runScriptStep_insertSelect_ok

/-- The former {lit}`runScriptStep_insertSelect_success`. A single complete source production whose rows fit gives a successful INSERT and the appended rows. Proof sketch: obtain the run data for the fitted rows and apply the first retained implication. -/
theorem runScriptStep_insertSelect_success {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value}
    {target : Nat} {cells : List Resolved.SourceCell} {query : Resolved.Query} {clauses : List Resolved.ConflictClause}
    {returning : List (Resolved.Expr × String)} {algorithm : Option ConflictAlgorithm} {subqueries : List Resolved.Query}
    {after : ResolveState} {value : Int} {table : Table} {rows : List (List Value)}
    (found : resolveStatement context connection.resolveState statement =
      .ok (.insertSelect target cells query clauses returning algorithm subqueries none, after))
    (timed : statementClock clock index (.insertSelect target cells query clauses returning algorithm subqueries none) =
      some value)
    (known : connection.state.counters.firstUnknown
      (Resolved.Statement.insertSelect target cells query clauses returning algorithm subqueries none).counterReads = none)
    (present : connection.state.database.table target = some table)
    (certain : query.productions (Resolved.statementContext value (connection.state.counters.view
      (Resolved.Statement.insertSelect target cells query clauses returning algorithm subqueries none).counterReads)
      parameters connection.state.database subqueries) connection.state.database
      (!Resolved.Statement.collectsSource target query subqueries returning none) = some [{ rows, failure := none }])
    (fits : InsertFits (connection.state.database.keys target table) table
      (insertSelectRows (Resolved.statementContext value (connection.state.counters.view
        (Resolved.Statement.insertSelect target cells query clauses returning algorithm subqueries none).counterReads)
        parameters connection.state.database subqueries) table.shape.columns cells rows))
    (clauseColumns : clauses.all (fun clause => match clause.action with
      | .nothing => true
      | .update assignments _ => assignments.all fun (position, _) => (table.shape.columns[position]?).isSome) = true)
    (transfer : ∀ source, insertSelectTransferRowids target cells query table connection.state.database none = some source →
      ((LiteralData.inserted table (insertSelectRows (Resolved.statementContext value (connection.state.counters.view
        (Resolved.Statement.insertSelect target cells query clauses returning algorithm subqueries none).counterReads)
        parameters connection.state.database subqueries) table.shape.columns cells rows)).rows.drop
          table.rows.length).map (·.rowid) = source)
    (plainSubqueries : Resolved.subqueriesPlain subqueries = true)
    (fixedCells : Resolved.cellsReady (Resolved.statementContext value (connection.state.counters.view
      (Resolved.Statement.insertSelect target cells query clauses returning algorithm subqueries none).counterReads)
      parameters connection.state.database subqueries)
      [cells.filterMap fun | .cell fixed => some fixed | .source _ => none] = true)
    (json : upsertJsonReady clauses returning = true) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] ∧
      output.isError = false ∧
      next.state.database = connection.state.database.setRows target (LiteralData.inserted table (insertSelectRows
        (Resolved.statementContext value (connection.state.counters.view
          (Resolved.Statement.insertSelect target cells query clauses returning algorithm subqueries none).counterReads)
          parameters connection.state.database subqueries) table.shape.columns cells rows)).rows := by
  obtain ⟨effect, ready, single⟩ := runStatement_insertSelect_none_ok value _ parameters target cells query clauses returning
    algorithm subqueries connection.state.database table rows present certain fits clauseColumns transfer plainSubqueries
    fixedCells json
  obtain ⟨output, next, step, noError, nextEq⟩ := runScriptStep_insertSelect_ok (parameters := parameters) found timed known
    (by unfold SqlState.statementRun; simp [ready, known]) (by unfold SqlState.statementRun; exact effect)
    (by unfold SqlState.statementRun; exact single)
  refine ⟨output, next, step, noError, ?_⟩
  rw [nextEq]

#print axioms runScriptStep_insertSelect_success

end Belay.Sqlite.Model.ReplacedWriteModes
