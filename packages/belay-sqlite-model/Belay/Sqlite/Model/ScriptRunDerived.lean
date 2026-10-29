import Belay.Sqlite.Model.ScriptRunHolds

set_option doc.verso true

/-! Resolver- and invariant-derived obligations use the same preservation induction as
explicit obligations. Canonical runs follow by membership in all complete executions. -/

namespace Belay.Sqlite.Model

variable {property : Database → Prop} {condition : StatementCondition}

/-- For every preservation rule, context and optional clock: if every step on an invariant state
meets its actual-input condition, every complete execution from an invariant state preserves the
property on the database and snapshot. Failed gates and ended suffixes impose no condition.
Proof sketch: construct guarded obligations with {name}`ScriptConditionsWith.of_invariant`, then
apply the common all-execution theorem. -/
theorem runScriptAllFrom_holds_derived (keeps : StatementKeeps property condition) (context : ResolveContext)
    (clock : Option Clock)
    (derive : ∀ index connection statement parameters, connection.state.Holds property →
      ScriptStepCondition condition context clock index connection statement parameters)
    (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds property) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds property :=
  runScriptAllFrom_holds keeps context clock index script holds
    (ScriptConditionsWith.of_invariant context clock derive index connection script)

/-- Under the same invariant-derived step obligations, the canonical run preserves the property
on its database and snapshot. Proof sketch: use membership in all complete executions. -/
theorem runScriptFrom_holds_derived (keeps : StatementKeeps property condition) (context : ResolveContext)
    (clock : Option Clock)
    (derive : ∀ index connection statement parameters, connection.state.Holds property →
      ScriptStepCondition condition context clock index connection statement parameters)
    (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds property) :
    (runScriptFrom context clock index connection script).connection.state.Holds property :=
  runScriptAllFrom_holds_derived keeps context clock derive index script holds _
    (runScriptFrom_mem_runScriptAllFrom context clock index connection script)

end Belay.Sqlite.Model
