import Belay.Sqlite.Model.Programs.Scripts.StepContinuesOk

set_option doc.verso true

/-! The success direction of one step for every ordinary statement (ADR 0017, S6). A statement that
resolves, has a clock value, reads only known counters, has a ready run without alternatives that succeeds
with a database, and has an output for that run, makes the step continue without an error and with that
database. -/

namespace Belay.Sqlite.Model

/-- For every context, clock, index, connection, statement and values that resolve to a statement that
is neither a control statement nor a query, with a clock value and no unknown counter, whose run is ready,
has no alternative execution and succeeds with a database, and which has an output for that run
({name}`statementOutput` is some): the step continues with an output that is no error and with no further
execution, and the next connection is the connection with that database and the counters after the counts
of the run. Clock, snapshot and settings stay. Proof sketch: the output is not a stop of the model, so
{name}`runScriptStep_continues` gives the step; the transition does not halt, so the output is no error
({name}`Output.ofStep_isError_of_noHalt`); {name}`runScriptStep_effect` reads the next connection. -/
theorem runScriptStep_ordinary_ok {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value}
    {resolved : Resolved.Statement} {after : ResolveState} {value : Int} {database : Database}
    (found : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    (ordinary : resolved.isControl = false) (notQuery : ∀ query subqueries, resolved ≠ .query query subqueries)
    (timed : statementClock clock index resolved = some value)
    (known : connection.state.counters.firstUnknown resolved.counterReads = none)
    (ready : (connection.state.statementRun value parameters resolved).ready = true)
    (single : (connection.state.statementRun value parameters resolved).alternatives = [])
    (effect : (connection.state.statementRun value parameters resolved).effect = .ok database)
    (described : (statementOutput value parameters resolved connection.state
      (connection.state.statementRun value parameters resolved)
      ((connection.state.publish index (.ok database)).counted
        (connection.state.statementRun value parameters resolved).counts)).isSome = true) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] ∧
      output.isError = false ∧
      next = { connection with state := { connection.state with
        database := database
        counters := connection.state.counters.apply
          (connection.state.statementRun value parameters resolved).counts } } := by
  have calm : haltError ((connection.state.publish index (.ok database)).counted
      (connection.state.statementRun value parameters resolved).counts) = none := by
    simp [SqlTransition.counted, SqlState.publish, haltError]
  obtain ⟨output, next, step⟩ := runScriptStep_continues found timed known ready single fun reason => by
    rw [advanceRun_ordinary index _ connection.state _ ordinary, effect]
    exact Output.ofStep_ne_unmodeled _ _ _ _ _ _ _ notQuery (by rw [calm]; nofun) described reason
  have noError : output.isError = false := by
    obtain ⟨resolved', after', value', same, timed', -, -, ofStep, -⟩ := runScriptStep_continued_spec step
    rw [found] at same
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same)
    rw [timed] at timed'
    obtain rfl := Option.some.inj timed'
    rw [← ofStep, advanceRun_ordinary index _ connection.state _ ordinary, effect]
    exact Output.ofStep_isError_of_noHalt _ _ _ _ _ _ _ notQuery calm
  obtain ⟨value', database', timed', effect', nextEq⟩ := runScriptStep_effect found ordinary step noError
  rw [timed] at timed'
  obtain rfl := Option.some.inj timed'
  rw [effect] at effect'
  obtain rfl := Except.ok.inj effect'
  exact ⟨output, next, step, noError, nextEq⟩

end Belay.Sqlite.Model
