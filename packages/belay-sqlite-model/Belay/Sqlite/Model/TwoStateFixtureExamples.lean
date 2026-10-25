import Belay.Sqlite.Model.TwoStateQuery
import Belay.Sqlite.Model.InitialSourceExamples

set_option doc.verso true

/-! Fixtures for the observation of a query over two databases (ADR 0017, S6): {lit}`observe` runs a
statement that is a query, and the helpers below read its output. The examples in
{lit}`TwoStateExamples.lean` and {lit}`TwoStateViewExamples.lean` check each result with the kernel. -/

namespace Belay.Sqlite.Model.TwoStateFixtures

open Syntax

/-- The output of a statement that is a query, over the initial database and the current database,
with values, a clock and counters. A statement that is not a query is not modeled. -/
def observe (initial current : Database) (statement : Syntax.Statement) (parameters : List Value := [])
    (clock : Option Clock := none) (counters : Counters := {}) : Output :=
  match statement.asQuery? with
  | some (query, subqueries) =>
    observeTwoState context clock 0 initial (connectionOf current counters) parameters query subqueries
  | none => .unmodeled "not a query"

/-- The error code of an output, or none for every other output. -/
def code? : Output → Option Nat
  | .error code => some code
  | .rows _ | .done _ | .oneOf _ | .unmodeled _ => none

/-- Whether an output is a refusal of the model. -/
def refused : Output → Bool
  | .unmodeled _ => true
  | .rows _ | .done _ | .error _ | .oneOf _ => false

end Belay.Sqlite.Model.TwoStateFixtures
