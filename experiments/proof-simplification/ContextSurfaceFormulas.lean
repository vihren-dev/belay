import ContextSurface

set_option doc.verso true

/-! Old surface formulas derived through the contextual experiment. The adapter
proofs are evidence that the proposed API retains those formulas. Production
code would remove the old condition APIs and these compatibility traversals. -/

namespace Belay.Sqlite.Model.ContextExperiment

/-- For every old explicit script condition, its obligations imply the guarded
contextual obligations with the same statement and database predicate.
Proof sketch: induction follows the surface transitions; the property guard,
clock and readiness hypotheses can be ignored for an explicit old condition. -/
theorem script_obligations_plain {property : Database → Prop}
    {condition : Resolved.Statement → Database → Prop}
    (context : ResolveContext) (clock : Option Clock) :
    ∀ index connection script,
      ScriptConditionsWith condition context clock index connection script →
        ScriptObligations property (fun _ _ _ => condition) context clock index connection script
  | _, _, [], _ => trivial
  | index, connection, (statement, parameters) :: rest, conditions => by
    refine ⟨fun _ resolved after _ found _ _ => conditions.1 resolved after found, ?_⟩
    have later := conditions.2
    revert later
    cases runScriptStep context clock index connection statement parameters with
    | ended _ => exact fun _ => trivial
    | continued _ next => exact script_obligations_plain context clock (index + 1) next rest

/-- For every condition derived from a state's invariant and successful
resolution, the guarded script obligations hold for that condition paired with
raw readiness. The state support gate supplies raw readiness at each evaluated
step. Proof sketch: construct each guarded condition and follow the transitions;
this proof does not establish or assume preservation of the script. -/
theorem script_obligations_derived {property : Database → Prop}
    {condition : Resolved.Statement → Database → Prop}
    (context : ResolveContext) (clock : Option Clock)
    (derive : ∀ (connection : Connection) (statement : Syntax.Statement) resolved after,
      connection.state.Holds property →
      resolveStatement context connection.resolveState statement = .ok (resolved, after) →
        condition resolved connection.state.database) :
    ∀ index connection script,
      ScriptObligations property
        (fun value counters parameters statement database => condition statement database ∧
          (runStatement value counters parameters statement database).ready = true)
        context clock index connection script
  | _, _, [] => trivial
  | index, connection, (statement, parameters) :: rest => by
    refine ⟨?_, ?_⟩
    · intro holds resolved after value found _ ready
      exact ⟨derive connection statement resolved after holds found,
        (Bool.and_eq_true_iff.mp ready).1⟩
    · cases runScriptStep context clock index connection statement parameters with
      | ended _ => trivial
      | continued _ next => exact script_obligations_derived context clock derive (index + 1) next rest

/-- The old surface theorem with explicit conditions follows with precisely its
original assumptions. Proof sketch: convert its explicit obligations and apply
the single contextual surface run theorem. -/
theorem old_surface_plain_formula {property : Database → Prop}
    {condition : Resolved.Statement → Database → Prop}
    (keeps : StatementKeeps property condition) (context : ResolveContext)
    (clock : Option Clock) (index : Nat) {connection : Connection}
    (script : List (Syntax.Statement × List Value)) (holds : connection.state.Holds property)
    (conditions : ScriptConditionsWith condition context clock index connection script) :
    (runScriptFrom context clock index connection script).connection.state.Holds property :=
  surface_run_keeps keeps context clock index script holds
    (script_obligations_plain context clock index connection script conditions)

/-- The old surface theorem with invariant-derived conditions and support-based
preservation follows with precisely its original assumptions. Proof sketch:
pair the condition with readiness, construct its guarded obligations and apply
the same contextual surface run theorem as the explicit-condition formula. -/
theorem old_surface_derived_formula {property : Database → Prop}
    {condition : Resolved.Statement → Database → Prop}
    (keeps : StatementKeepsReady property condition) (context : ResolveContext)
    (clock : Option Clock)
    (derive : ∀ (connection : Connection) (statement : Syntax.Statement) resolved after,
      connection.state.Holds property →
      resolveStatement context connection.resolveState statement = .ok (resolved, after) →
        condition resolved connection.state.database)
    (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds property) :
    (runScriptFrom context clock index connection script).connection.state.Holds property :=
  surface_run_keeps (fun value counters parameters statement database holds met =>
    keeps value counters parameters statement database holds met.1 met.2)
    context clock index script holds
      (script_obligations_derived context clock derive index connection script)

#print axioms old_surface_plain_formula
#print axioms old_surface_derived_formula

end Belay.Sqlite.Model.ContextExperiment
