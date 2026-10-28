import Belay.Sqlite.Model.InsertSelectSuccess
import Belay.Sqlite.Model.OrdinaryStepEffects

set_option doc.verso true

/-! The step law of INSERT from a query (ADR 0017, S6): the success direction at the level of
{lit}`runScriptStep`. A run that the model describes, has no alternative execution and succeeds makes the
step continue, without an error output and without further executions, with the database that the
effect gives. {lit}`runStatement_insertSelect_none_ok` gives such a run for rows that fit the target. -/

namespace Belay.Sqlite.Model

/-- For every context, clock, index, connection, statement and values that resolve to an INSERT from a
query without rules, where the statement has a clock value and no unknown counter, and the run of the
statement is ready, has no alternative execution and succeeds with a database: the step of the statement
continues with an output that is no error, without further executions, and the next connection is the
connection with that database and the counters after the counts of the run. In plain words, a successful
INSERT from a query gives a step that continues and writes what the run writes. Proof sketch: with a
modeled clock and counters the step reaches the transition of the run; a successful transition has a
modeled output for this statement ({name}`statementOutput`); without alternatives the step has no further
executions; {name}`runScriptStep_effect` then reads the next connection. -/
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
  have ordinary : (Resolved.Statement.insertSelect target cells query clauses returning algorithm subqueries none).isControl
    = false := rfl
  have continues : ∃ output next, runScriptStep context clock index connection statement parameters =
      .continued output next [] := by
    simp only [runScriptStep, runScriptStepWith, found, timed, known, ready, Bool.not_true, Bool.false_eq_true, ite_false,
      ranScriptStep]
    rw [advanceRun_ordinary index _ connection.state _ ordinary, effect]
    simp only [SqlState.publish, SqlTransition.counted, haltError, Output.ofStep, statementOutput]
    simp only [↓reduceIte, StatementExecution.ofAlternatives, single, List.mapM_nil, Except.map, pure, Except.pure]
    split
    · rename_i reason shape
      split at shape <;> simp_all
    all_goals exact ⟨_, _, rfl⟩
  obtain ⟨output, next, step⟩ := continues
  have noError : output.isError = false := by
    obtain ⟨resolved', after', value', same, timed', -, -, ofStep, -⟩ := runScriptStep_continued_spec step
    rw [found] at same
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same)
    rw [timed] at timed'
    obtain rfl := Option.some.inj timed'
    rw [← ofStep, advanceRun_ordinary index _ connection.state _ ordinary, effect]
    exact Output.ofStep_isError_of_noHalt _ _ _ _ _ _ _ (fun _ _ => nofun) (by
      simp [SqlTransition.counted, SqlState.publish, haltError])
  obtain ⟨value', database', timed', effect', nextEq⟩ := runScriptStep_effect found ordinary step noError
  rw [timed] at timed'
  obtain rfl := Option.some.inj timed'
  rw [effect] at effect'
  obtain rfl := Except.ok.inj effect'
  exact ⟨output, next, step, noError, nextEq⟩

/-- For every step that resolves to an INSERT from a query without rules, with a clock value and no unknown counter,
over a table at the target position, where the query has one certain production without failure, the rows it
hands over fit the target ({name}`InsertFits`), and the statement is in the part that the model describes (the
premises of {name}`runStatement_insertSelect_none_ok`): the step continues, with an output that is no error and no
further executions, and the next database is the database with the target rows of the table with the rows
appended, one after the other ({name}`LiteralData.inserted`). The rows that are appended are the full target rows
that {name}`insertSelectRows` makes of the rows of the production: the cells that the statement selects from the
source row, the fixed cells, and the affinity of each target column applied to each. In plain words, this is the
success law of INSERT from a query: it never fails, whatever the clauses say, and it writes those full rows as an
upsert of them does when no row meets a conflict. The premises are those of {name}`runStatement_insertSelect_none_ok`, with the context of the
statement at the clock value and the counters that the connection knows. Proof sketch:
{name}`runStatement_insertSelect_none_ok` gives the run, and {name}`runScriptStep_insertSelect_ok` the step. -/
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

end Belay.Sqlite.Model
