import VerifierConformance.Trace
import VerifierConformance.PossibleOutputs
import Belay.Sqlite.Model.ScriptRun

set_option doc.verso true

/-! The classification passes of the run that continues after an error (ADR 0017, D3, amended
2026-10-22), for the records of a recorder that runs on after an SQL error. A statement can have
several possible executions (ADR 0019, D4, amended 2026-10-25), so there is one pass for each
complete execution of the statements ({lit}`runScriptAllWith`): each pass takes
one execution of each statement, and a later statement runs from the connection of the execution
that reached it. Each statement takes the model's step ({name}`Belay.Sqlite.Model.runScriptStepWith`
and {name}`Belay.Sqlite.Model.ranScriptStep`, of which {name}`Belay.Sqlite.Model.runScriptStep` is
made), so the passes and {lit}`runScriptAllFrom` are the same runs
({lit}`VerifierConformance.RunPassLaws` proves it). A pass keeps what the comparison needs and the
run's output does not hold: the observation after each statement, with the error and its phase, and
the columns, rows and changes of each statement. -/

namespace Belay.Sqlite.Model.Conformance

/-- What the pass of the run that continues gives. For example, the pass of no statements has
no observations and no outputs, and is supported. -/
structure RunPass where
  /-- One observation after each statement that ran, with the error of a statement that
  stopped with one. -/
  observations : List Observation
  /-- Writer counters after each statement, aligned with its observation. -/
  counters : List Counters
  /-- The output of each statement that ran ({name}`statementOutput`). -/
  outputs : List (Option StatementOutput)
  /-- The results that SQLite may give for each statement that ran ({name}`possibleOutput`). -/
  possible : List (Option (List (List ResultRow)))
  /-- The output of each statement in the run ({name}`Output`): one for each statement that
  ran, and {name}`Output.unmodeled` last when the run ended early. -/
  results : List Output
  /-- Whether the run reached the end of the statements: false when a statement ended it. -/
  supported : Bool

/-- The pass of a run that ends at a statement, with the reason: no more observations or
outputs, the result {name}`Output.unmodeled` of the reason, and not supported. -/
def RunPass.ended (reason : String) : RunPass :=
  { observations := [], counters := [], outputs := [], possible := [], results := [.unmodeled reason], supported := false }

/-- The observation after a statement at a zero-based index: the visible and committed
databases and the transaction status of the connection after it, and the error with which its
transition stops ({name}`haltError`), at the index. -/
def observeStep (index : Nat) (next : Connection) (transition : SqlTransition) : Observation :=
  { observeState next.state with error := (haltError transition).map ((index, ·)) }

/-- One possible execution of a statement, as the pass keeps it: the connection after the statement,
the observation, counters, output and possible results after it, and the output of the run
({name}`Output`). -/
structure ExecutionPass where
  /-- The connection after the statement in this execution. -/
  next : Connection
  /-- The observation after the statement ({name}`observeStep`). -/
  observation : Observation
  /-- The writer counters after the statement. -/
  counters : Counters
  /-- The output of the statement ({name}`statementOutput`). -/
  output : Option StatementOutput
  /-- The results that SQLite may give for the statement ({name}`possibleOutput`). -/
  possible : Option (List (List ResultRow))
  /-- The output of the statement in the run ({name}`Output`). -/
  result : Output

/-- What the pass takes from one statement: the reason why the run ends at it, or its possible
executions, the model's own execution first. -/
inductive RunPassStep where
  /-- The model does not describe the statement; the run ends. -/
  | ended (reason : String)
  /-- The statement ran, with one pass entry for each possible execution. -/
  | continued (executions : List ExecutionPass)

/-- The entry of one execution of a statement at a zero-based index on the connection, from the
values bound to its parameters, the resolved statement, its clock value, the execution and the run
and transition that gave it. -/
def ExecutionPass.ofExecution (index : Nat) (parameters : List Value) (connection : Connection)
    (resolved : Resolved.Statement) (value : Int) (execution : StatementExecution) (run : StatementRun)
    (transition : SqlTransition) : ExecutionPass :=
  { next := execution.next, observation := observeStep index execution.next transition,
    counters := execution.next.state.counters,
    output := statementOutput value parameters resolved connection.state run transition,
    possible := possibleOutput value parameters resolved connection.state transition,
    result := execution.output }

/-- The step of the pass for a statement that ran, from the values bound to its parameters, the
connection before it, the resolved statement, the resolution state {lit}`after` it, its clock value, its
run and its transition. It takes the model's step ({name}`ranScriptStep`); a step that ends the run ends
the pass. A step that continues gives the entry of its own execution and the entry of each further
execution ({name}`StatementExecution.ofAlternatives`), each with the run and transition that gave it. -/
def ranPassStep (index : Nat) (parameters : List Value) (connection : Connection) (resolved : Resolved.Statement)
    (after : ResolveState) (value : Int) (run : StatementRun) (transition : SqlTransition) : RunPassStep :=
  match ranScriptStep index parameters connection resolved after value run transition with
  | .ended reason => .ended reason
  | .continued output next _ =>
    match StatementExecution.ofAlternatives index parameters connection resolved after value run with
    | .error reason => .ended reason
    | .ok further =>
      .continued (ExecutionPass.ofExecution index parameters connection resolved value { output, next } run transition ::
        further.map fun traced =>
          ExecutionPass.ofExecution index parameters connection resolved value traced.execution traced.run
            traced.transition)

/-- The step of the pass for one statement: the model's steps ({name}`runScriptStepWith`), then
{name}`ranPassStep` for a statement that runs. -/
def runPassStep (context : ResolveContext) (clock : Option Clock) (index : Nat) (connection : Connection)
    (statement : Syntax.Statement) (parameters : List Value) : RunPassStep :=
  runScriptStepWith RunPassStep.ended (ranPassStep index parameters connection) context clock index connection
    statement parameters

/-- The passes over the complete executions of statements, each with the values bound to its
parameters, from a zero-based index on a connection, for a function that gives the step of each
statement ({name}`RunPassStep`). A step that ends the run ends the pass ({name}`RunPass.ended`). A
step that continues gives, for each of its executions, the passes of the rest from the connection of
that execution, each with the entry of that execution first, also after an error. The function
argument lets a caller run the executions of a statement that it describes itself. -/
def runPassAllWith (step : Nat → Connection → Syntax.Statement × List Value → RunPassStep) :
    Nat → Connection → List (Syntax.Statement × List Value) → List RunPass
  | _, _, [] => [{ observations := [], counters := [], outputs := [], possible := [], results := [], supported := true }]
  | index, connection, entry :: rest =>
    match step index connection entry with
    | .ended reason => [RunPass.ended reason]
    | .continued executions =>
      executions.flatMap fun execution =>
        (runPassAllWith step (index + 1) execution.next rest).map fun later =>
          { observations := execution.observation :: later.observations,
            counters := execution.counters :: later.counters,
            outputs := execution.output :: later.outputs,
            possible := execution.possible :: later.possible,
            results := execution.result :: later.results, supported := later.supported }

/-- The passes over the complete executions of statements with their values, from a zero-based
index on the connection, with an optional clock: {name}`runPassAllWith` with the step
{name}`runPassStep`. -/
def runPassAllFrom (context : ResolveContext) (clock : Option Clock) (index : Nat) (connection : Connection)
    (script : List (Syntax.Statement × List Value)) : List RunPass :=
  runPassAllWith (fun index connection (statement, parameters) =>
    runPassStep context clock index connection statement parameters) index connection script

/-- The pass of the model's own execution of the statements: the first of the passes over the complete
executions ({name}`runPassAllFrom`), which takes the model's own execution of each statement. The
prediction of a case comes from this pass, because a prediction is one answer. A script always has a
pass, so the reason of {name}`RunPass.ended` only stands for a run that has none. -/
def runPassFrom (context : ResolveContext) (clock : Option Clock) (index : Nat) (connection : Connection)
    (script : List (Syntax.Statement × List Value)) : RunPass :=
  (runPassAllFrom context clock index connection script).headD (RunPass.ended "the model gives no execution")

end Belay.Sqlite.Model.Conformance
