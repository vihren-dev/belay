import VerifierConformance.Trace
import VerifierConformance.Outputs

/-! One classification pass over a script (ADR 0013, D2): each reached statement runs
once, and the pass keeps the observation before it, its output and whether the model
describes it. The theorems relate the pass to {lit}`runSqlFrom`, whose final outcome the
last observation shows, and to {lit}`supportedSqlFrom`, the support check of the
verification target. -/

namespace Belay.Sqlite.Conformance

/-- What one pass over a script gives: the observation before each executed statement and
of the final outcome, the output of each executed statement, and whether every reached
statement passes {lit}`statementReady`. -/
structure Pass where
  /-- The initial snapshot and one observation after each executed statement; a halt ends
  them. -/
  observations : List Observation
  /-- The output of each executed statement, up to and including a halting one. -/
  outputs : List (Option StatementOutput)
  /-- Whether every reached statement passes {lit}`statementReady`. -/
  supported : Bool

/-- Run the script from a position and connection state once. Each statement runs once
({lit}`runStatement`), which gives its support check and its effect; it is advanced with
that effect ({lit}`advanceWith`) and observed; a halt ends the pass with the observation of
its outcome. -/
def passFrom (position : Nat) (script : List Resolved.Statement) (state : SqlState) : Pass :=
  match script with
  | [] => { observations := [observeState state], outputs := [], supported := true }
  | statement :: rest =>
    let clock := state.clock position
    let run := runStatement clock statement state.database
    let ready := run.ready
    let transition := advanceWith position statement state run.effect
    let output := statementOutput clock statement state transition
    match transition with
    | .next next =>
      let later := passFrom (position + 1) rest next
      { observations := observeState state :: later.observations, outputs := output :: later.outputs,
        supported := ready && later.supported }
    | .halt outcome =>
      { observations := [observeState state, observeOutcome outcome], outputs := [output], supported := ready }

/-- The observations of a complete case, which begins outside a transaction as
{lit}`runSql` does. -/
def trace (script : List Resolved.Statement) (initial : Database) : List Observation :=
  (passFrom 0 script { database := initial }).observations

/-- For every position, script and state, the last observation of the pass is the
observation of {lit}`runSqlFrom`'s outcome. Proof sketch: induction on the script; a halt
ends both with the same outcome, and a continuing step moves both to the next state. -/
theorem passFrom_final (position : Nat) (script : List Resolved.Statement) (state : SqlState) :
    (passFrom position script state).observations.getLast? =
      some (observeOutcome (runSqlFrom position script state)) := by
  induction script generalizing position state with
  | nil => simp [passFrom, runSqlFrom, observeState]
  | cons statement rest ih =>
    cases h : advanceWith position statement state
        (runStatement (state.clock position) statement state.database).effect with
    | next next =>
      have later := ih (position + 1) next
      simp only [passFrom, runSqlFrom, advance, literalStep, h] at later ⊢
      rw [List.getLast?_cons, later]
      rfl
    | halt outcome => simp [passFrom, runSqlFrom, advance, literalStep, h]

/-- For every script and starting database, the last observation of {name}`trace` is the
observation of {lit}`runSql`'s outcome: conformance traces and verifier proofs refer to
the same execution. -/
theorem trace_final (script : List Resolved.Statement) (initial : Database) :
    (trace script initial).getLast? = some (observeOutcome (runSql script initial)) :=
  passFrom_final 0 script { database := initial }

/-- For every position, script and state, the support verdict of the pass is
{lit}`supportedSqlFrom`. Proof sketch: induction on the script; both check the statement,
then stop at a halt or continue with the same next state. -/
theorem passFrom_supported (position : Nat) (script : List Resolved.Statement) (state : SqlState) :
    (passFrom position script state).supported = supportedSqlFrom position script state := by
  induction script generalizing position state with
  | nil => rfl
  | cons statement rest ih =>
    cases h : advanceWith position statement state
        (runStatement (state.clock position) statement state.database).effect with
    | next next => simp [passFrom, supportedSqlFrom, h, ih]
    | halt outcome => simp [passFrom, supportedSqlFrom, h]

end Belay.Sqlite.Conformance
