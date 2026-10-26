import ContextSurface

set_option doc.verso true

/-! Boundary laws for the contextual experiment: conditions stop at the actual
transition, invariant certificates compose, and the state support check retains
its extra obligation about known counters. -/

namespace Belay.Sqlite.Model.ContextExperiment

/-- For every pair of database properties and execution conditions, preservation
of each property under its own condition implies preservation of their
conjunction under both conditions. Proof sketch: apply each effect certificate
to the same database retained by the effect. -/
theorem keeps_and {first second : Database → Prop} {firstCondition secondCondition : Condition}
    (left : Keeps first firstCondition) (right : Keeps second secondCondition) :
    Keeps (fun database => first database ∧ second database)
      (fun clock counters parameters statement database =>
        firstCondition clock counters parameters statement database ∧
          secondCondition clock counters parameters statement database) :=
  fun clock counters parameters statement database holds met database' retained =>
    ⟨left clock counters parameters statement database holds.1 met.1 database' retained,
      right clock counters parameters statement database holds.2 met.2 database' retained⟩

/-- For every contextual condition and raw script whose first transition halts,
the complete script condition is exactly the first statement's condition. Its
suffix requires nothing. Proof sketch: reduce the definition at the halt. -/
theorem conditions_halt {condition : Condition} {position : Nat}
    {statement : Resolved.Statement} {parameters : List Value} {state : SqlState}
    {outcome : Outcome} (halted : advance position statement parameters state = .halt outcome)
    (rest : List (Resolved.Statement × List Value)) :
    Conditions condition position ((statement, parameters) :: rest) state ↔
      condition (state.clock position) (state.counters.view statement.counterReads)
        parameters statement state.database := by
  simp [Conditions, halted]

/-- For every surface script whose first step ends, its complete obligations are
exactly the first guarded step obligation. The suffix requires nothing.
Proof sketch: reduce the definition at the ended step. -/
theorem obligations_ended {property : Database → Prop} {condition : Condition}
    {context : ResolveContext} {clock : Option Clock} {index : Nat} {connection : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {reason : String}
    (ended : runScriptStep context clock index connection statement parameters = .ended reason)
    (rest : List (Syntax.Statement × List Value)) :
    ScriptObligations property condition context clock index connection
      ((statement, parameters) :: rest) ↔
        (connection.state.Holds property →
          StepCondition condition context clock index connection statement parameters) := by
  simp [ScriptObligations, ended]

/-- For every state run, readiness implies readiness of the raw statement run
with exactly the visible counters. Proof sketch: select the first conjunct of
the state support check. -/
theorem state_ready_implies_raw {state : SqlState} {clock : Int}
    {parameters : List Value} {statement : Resolved.Statement}
    (ready : (SqlState.statementRun state clock parameters statement).ready = true) :
    (runStatement clock (state.counters.view statement.counterReads)
      parameters statement state.database).ready = true :=
  (Bool.and_eq_true_iff.mp ready).1

/-- For every state and statement with an unknown counter read, the state run
fails its support check, whatever the raw statement's support result is.
Proof sketch: the state check conjoins the known-counter test. -/
theorem unknown_counter_blocks_state {state : SqlState} {clock : Int}
    {parameters : List Value} {statement : Resolved.Statement} {kind : CounterKind}
    (unknown : state.counters.firstUnknown statement.counterReads = some kind) :
    (SqlState.statementRun state clock parameters statement).ready = false := by
  simp [SqlState.statementRun, unknown]

#print axioms keeps_and
#print axioms conditions_halt
#print axioms obligations_ended
#print axioms state_ready_implies_raw
#print axioms unknown_counter_blocks_state

end Belay.Sqlite.Model.ContextExperiment
