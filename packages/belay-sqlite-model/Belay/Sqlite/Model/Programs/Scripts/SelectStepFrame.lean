import Belay.Sqlite.Model.Programs.Scripts.SuccessfulScriptEffects
import Belay.Sqlite.Model.Programs.Scripts.KeysUniqueWrites
import Belay.Sqlite.Model.Schema.Dispatch.SelectStepKeeps
import Belay.Sqlite.Model.Programs.Scripts.ReadOnlyFrame

set_option doc.verso true

/-! A continuing SELECT preserves its connection and has no further execution,
including when its output is a modeled error. -/

namespace Belay.Sqlite.Model

/-- For every connection and every SELECT statement: if the step continues, with any output, the next
connection is the connection and there is no other execution. In plain words, a SELECT changes nothing, also
when it gives an error. Proof sketch: the step comes from a successful resolution of the SELECT
({name}`runScriptStep_ran`), which is a query or a prepare error ({name}`resolveStatement_select_shape`), and
{name}`runScriptStep_readOnly_keeps` treats both. -/
theorem runScriptStep_select_keeps {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection next : Connection} {columns source joins filter groupBy orderBy limit offset subqueries having
      distinct compound parameters output} {others : List StatementExecution}
    (step : runScriptStep context clock index connection
      (.select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound)
      parameters = .continued output next others) :
    others = [] ∧ next = connection := by
  obtain ⟨resolved, after, value, original, -⟩ := runScriptStep_ran step
  obtain ⟨_, _, shape⟩ := resolveStatement_select_shape original
  exact runScriptStep_readOnly_keeps original shape step

end Belay.Sqlite.Model
