import Belay.Sqlite.Model.Programs.StatementRunLaws.SelectCalmRule
import Belay.Sqlite.Model.Tooling.Counterexamples.SelectExecutionRule
import Belay.Sqlite.Model.Schema.Dispatch.TableSourceLaws

set_option doc.verso true

/-! The output of a calm query over the rows scanned from one table. -/

namespace Belay.Sqlite.Model

/-- At any clock, index and connection with a table at the given position, the output of a calm
one-table query returns rows with a property exactly when every possible result of its scan has
that property. The source is the first table, the query is simple, the window binds without
parameters, and the scan rules out overflow and uncertain DISTINCT. Proof sketch:
{name}`Connection.SelectReady.of_faultless` supplies readiness and {name}`resolvedStepOutput_select`
evaluates the output in the context of the bound parameter values. -/
theorem resolvedStepOutput_calm_scan (clock : Option Clock) (index : Nat) (connection : Connection)
    (parameters : List Value) {query : Resolved.Query} {position : Nat} {table : Table}
    (sources : query.sources = [.first position]) (present : connection.state.database.table position = some table)
    (calm : (Resolved.Statement.query query []).Calm) (single : query.compound = none)
    (limitParameter : query.limitParameter = none) (offsetParameter : query.offsetParameter = none)
    (noOverflow : query.fails (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table) = false)
    (distinct : query.distinctCertain (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table) = true)
    (property : List (List Value) → Prop) :
    (resolvedStepOutput clock index connection parameters (.query query [])).returnsResult property ↔
      ∀ rows ∈ query.possibleResults (Resolved.EvalContext.bound parameters) (Resolved.sourceRows table),
        property rows := by
  have faultless := calm.faultless_nil connection parameters (rows := Resolved.sourceRows table)
  rw [Connection.queryContext_calm _ parameters query [] calm] at faultless
  have ready := Connection.SelectReady.of_faultless connection parameters calm single
    (Resolved.Query.bindWindow_literal parameters query limitParameter offsetParameter)
    (Resolved.Query.source_first _ query connection.state.database position _ sources present) (by simp)
    faultless noOverflow distinct
  rw [resolvedStepOutput_select clock index connection parameters (by simp [statementClock, calm.readsClock]) ready,
    show connection.queryContextAt 0 parameters query [] = Resolved.EvalContext.bound parameters
      from Connection.queryContext_of_quiet _ _ _ calm.quiet]
  exact query.returnsResult_possible _ _ property

end Belay.Sqlite.Model
