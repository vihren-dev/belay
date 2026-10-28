import Belay.Sqlite.Model.SuccessfulScriptEffects
import Belay.Sqlite.Model.ScriptRunContinued
import Belay.Sqlite.Model.InsertSelectLaws

set_option doc.verso true

/-! What every execution of an ordinary statement leaves (ADR 0017, S6). A step can have several executions
({lit}`RunStep.executions`): the model's own and one for each alternative run. The laws of
{lit}`SuccessfulScriptEffects` read the own execution only. This module reads all of them: an execution
without an error is the success of some run of the statement. For INSERT from a query without rules it follows
that every such execution writes the rows of the target table and nothing else. -/

namespace Belay.Sqlite.Model

/-- For every step that continues, statement that resolves to an ordinary statement (none of BEGIN, COMMIT,
ROLLBACK or a setting: {name}`Resolved.Statement.isControl` is false) and every execution of the step: if the
output of the execution is no error, then the effect of some run of the statement is a success with a database,
and the next connection of the execution is the connection with that database and the counters after the counts
of that run. The formula says only that the effect of the run is listed among the effects of the statement
({name}`StatementRun.effects`), which are the effects of the own run and of the alternative runs; it does not say
which run of the step it is, or which execution of the step the run belongs to. In plain words, an execution
that does not fail has the effect of one successful run of the statement; the snapshot, the clock and the settings
stay. Proof sketch: {name}`runScriptStep_continued_spec` gives the own execution and the executions of the
alternatives; {name}`StatementExecution.ofAlternatives_mem` gives the run, transition and output of an
alternative. In both cases {name}`successful_output_effect` turns an output that is no error and does not end
the run into a successful effect and a transition that continues. -/
theorem runScriptStep_execution_effects {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {output : Output}
    {next : Connection} {others : List StatementExecution} {resolved : Resolved.Statement} {after : ResolveState}
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (found : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    (ordinary : resolved.isControl = false) :
    ∃ value, ∀ execution ∈ (RunStep.continued output next others).executions, execution.output.isError = false →
      ∃ (run : StatementRun) (database : Database),
        run.effect ∈ (connection.state.statementRun value parameters resolved).effects ∧
        run.effect = .ok database ∧
        execution.next = { connection with state := { connection.state with
          database, counters := connection.state.counters.apply run.counts } } := by
  obtain ⟨resolved', after', value, same, -, -, -, ofStep, noStop, nextEq, further, listed, rfl⟩ :=
    runScriptStep_continued_spec step
  rw [found] at same
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same)
  have afterEq := (resolveStatement_certificate context _ _ _ _ found).after
  rw [ResolveState.after_of_isControl _ ordinary] at afterEq
  refine ⟨value, fun execution member noError => ?_⟩
  simp only [RunStep.executions, List.mem_cons, List.mem_map] at member
  rcases member with rfl | ⟨traced, inFurther, rfl⟩
  · obtain ⟨database, effect, transition⟩ := successful_output_effect value parameters index resolved connection.state _
      ordinary (by rw [ofStep]; exact noError) (by rw [ofStep]; exact noStop)
    refine ⟨_, database, StatementRun.effect_mem_effects _, effect, ?_⟩
    rw [nextEq, transition, afterEq]
    rfl
  · obtain ⟨alternative, inAlternatives, -, transitionEq, nextEq', outputEq⟩ :=
      StatementExecution.ofAlternatives_mem listed traced inFurther
    have stops := StatementExecution.ofAlternatives_continues listed traced inFurther
    obtain ⟨database, effect, transition⟩ := successful_output_effect value parameters index resolved connection.state
      alternative.toRun ordinary (by rw [← transitionEq, ← outputEq]; exact noError)
      (by rw [← transitionEq, ← outputEq]; exact stops)
    refine ⟨alternative.toRun, database, List.mem_cons_of_mem _ (List.mem_map_of_mem inAlternatives), effect, ?_⟩
    rw [nextEq', transitionEq, transition, afterEq]
    rfl

/-- For every upsert of rows into a target, with the values of its clauses, and every database: if the upsert has
no rules (no trigger and no foreign-key action: the last argument is {lit}`none`) and the effect of the run
succeeds with a database, that database is the input database with the rows of the target replaced. Proof sketch: unfold the run; a missing table is an error, and the effect of the summary of the
steps writes the rows of the target. -/
theorem runStatement_upsert_ok_setRows (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat)
    (literals : List (List Resolved.Cell)) (clauses : List Resolved.ConflictClause)
    (returning : List (Resolved.Expr × String)) (algorithm : Option ConflictAlgorithm)
    (subqueries : List Resolved.Query) (database after : Database)
    (ok : (runStatement clock counters parameters
      (.upsert target literals clauses returning algorithm subqueries none) database).effect = .ok after) :
    ∃ rows, after = database.setRows target rows := by
  simp only [runStatement] at ok
  cases present : database.table target with
  | none => simp [present] at ok
  | some table =>
    simp only [present, StatementRun.withKeys, Option.map_none] at ok
    split at ok
    · cases ok; exact ⟨_, rfl⟩
    · cases ok

/-- For every step that continues and resolves to INSERT from a query without rules (no trigger and no
foreign-key action), and every execution of the step whose output is no error: the next connection of the
execution is the connection with the rows of the target table replaced, and the counters after some counts.
In plain words, a successful INSERT from a query, whichever production of the query it takes, changes the rows
of its target table and the counters, and nothing else: not the catalog, not another table, not the snapshot
and not a setting. Proof sketch: {name}`runScriptStep_execution_effects` gives a successful run;
{name}`runStatement_insertSelect_none_effects` shows that its effect is an error, which is no success, or the
effect of an upsert, and {name}`runStatement_upsert_ok_setRows` reads that. -/
theorem runScriptStep_insertSelect_frame {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {output : Output}
    {next : Connection} {others : List StatementExecution} {target : Nat} {cells : List Resolved.SourceCell}
    {query : Resolved.Query} {clauses : List Resolved.ConflictClause} {returning : List (Resolved.Expr × String)}
    {algorithm : Option ConflictAlgorithm} {subqueries : List Resolved.Query} {after : ResolveState}
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (found : resolveStatement context connection.resolveState statement =
      .ok (.insertSelect target cells query clauses returning algorithm subqueries none, after)) :
    ∀ execution ∈ (RunStep.continued output next others).executions, execution.output.isError = false →
      ∃ (rows : List Row) (counters : Counters), execution.next = { connection with state := { connection.state with
        database := connection.state.database.setRows target rows, counters } } := by
  obtain ⟨value, effects⟩ := runScriptStep_execution_effects step found rfl
  intro execution member noError
  obtain ⟨run, database, inEffects, effect, nextEq⟩ := effects execution member noError
  have cases := runStatement_insertSelect_none_effects value (connection.state.counters.view
    (Resolved.Statement.insertSelect target cells query clauses returning algorithm subqueries none).counterReads)
    parameters target cells query clauses returning algorithm subqueries connection.state.database run.effect inEffects
  rcases cases with ⟨reason, error⟩ | ⟨literals, same⟩
  · rw [effect] at error
    cases error
  · obtain ⟨rows, rfl⟩ := runStatement_upsert_ok_setRows value _ parameters target literals clauses returning algorithm
      subqueries connection.state.database database (by rw [← same.1, effect])
    exact ⟨rows, _, nextEq⟩

end Belay.Sqlite.Model
