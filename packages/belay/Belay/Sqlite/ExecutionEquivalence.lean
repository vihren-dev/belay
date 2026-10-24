import Belay.Sqlite.ExecutionSuccess

set_option doc.verso true

namespace Belay.Sqlite

/-- Two programs have the same actual run and exactly the same complete branch outcomes
at this context. Outcomes include return values, errors, stopping reasons, partial traces,
and every connection field. The context's existing trace is shared by both programs.
Use this primitive for a single starting state; it has no unrestricted bind rule. -/
structure Sql.EquivAt {α : Type} (first second : Sql α) (state : ExecutionContext) : Prop where
  /-- The actual interpreter returns the same complete result for both programs. -/
  actual : first.runFrom state.clock state.index state.connection =
    second.runFrom state.clock state.index state.connection
  /-- Every result is a branch of the first program exactly when it is a branch of the
  second. Failed and unmodeled branches remain observations. -/
  branches : ∀ result, first.Branch state.clock state.index state.connection result ↔
    second.Branch state.clock state.index state.connection result

/-- Complete execution equivalence at every context satisfying the supplied predicate.
Contexts outside that domain impose nothing; an empty domain makes this true.
Use it when a schema or connection precondition restricts a comparison. Composition
also needs that each returning prefix reaches the continuation's domain. -/
def Sql.EquivOn {α : Type} (pre : ExecutionContext → Prop) (first second : Sql α) : Prop :=
  ∀ state, pre state → first.EquivAt second state

/-- Complete execution equivalence at every shared clock, statement index and connection.
It retains actual execution and all branch outcomes, including failed alternatives.
Use this unrestricted relation for ordinary compositional equivalence. -/
def Sql.Equiv {α : Type} (first second : Sql α) : Prop :=
  ∀ state, first.EquivAt second state

/-- Every returning branch from a context satisfying the precondition reaches a context
satisfying the postcondition for its returned value. Stopped branches require nothing.
Unlike a total-correctness check, this premise permits unmodeled stops. Use it to state
the domain needed by a continuation in restricted equivalence. -/
def Sql.ReturnsIn {α : Type} (program : Sql α) (pre : ExecutionContext → Prop)
    (post : α → ExecutionContext → Prop) : Prop :=
  ∀ state, pre state → ∀ result, program.Branch state.clock state.index state.connection result →
    ∀ value, result.value = some value → post value (state.finish result)

end Belay.Sqlite
