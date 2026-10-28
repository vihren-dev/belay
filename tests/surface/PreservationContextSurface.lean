import PreservationContextRaw

/-! Temporary generic surface witnesses freeze the old all-execution and canonical formulas.
The old condition's resolution obligation remains unchanged, including every continuing branch. -/

namespace PreservationMigration
open Belay.Sqlite.Model

/-- The frozen surface predicate asks for the old condition after resolution, even when a later gate ends the step. -/
def SurfaceConditions (condition : Resolved.Statement → Database → Prop) (context : ResolveContext)
    (clock : Option Clock) (index : Nat) (connection : Connection) : List (Syntax.Statement × List Value) → Prop
  | [] => True
  | (statement, parameters) :: rest =>
    (∀ resolved after, resolveStatement context connection.resolveState statement = .ok (resolved, after) →
      condition resolved connection.state.database) ∧
      match runScriptStep context clock index connection statement parameters with
      | .ended _ => True
      | stepped@(.continued ..) =>
        ∀ execution ∈ stepped.executions, SurfaceConditions condition context clock (index + 1) execution.next rest

/-- Frozen explicit obligations supply the guarded obligations for every branch, without extra assumptions. -/
theorem surface_conditions {property : Database → Prop} {condition : Resolved.Statement → Database → Prop}
    (context : ResolveContext) (clock : Option Clock) :
    ∀ index connection script, SurfaceConditions condition context clock index connection script →
      ScriptConditionsWith property (fun _ _ _ => condition) context clock index connection script
  | _, _, [], _ => trivial
  | index, connection, (statement, parameters) :: rest, met => by
    refine ⟨fun _ resolved after _ found _ _ => met.1 resolved after found, ?_⟩
    have later := met.2
    revert later
    cases runScriptStep context clock index connection statement parameters with
    | ended _ => exact fun _ => trivial
    | continued output next others =>
      exact fun later execution member => surface_conditions context clock (index + 1) execution.next rest
        (later execution member)

/-- The full old explicit all-execution formula follows without readiness or resolver-mode premises. -/
theorem surface {property : Database → Prop} {condition : Resolved.Statement → Database → Prop}
    (keeps : PlainKeeps property condition) (context : ResolveContext) (clock : Option Clock) (index : Nat)
    {connection : Connection} (script : List (Syntax.Statement × List Value)) (holds : connection.state.Holds property)
    (conditions : SurfaceConditions condition context clock index connection script) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds property :=
  runScriptAllFrom_holds keeps context clock index script holds
    (surface_conditions context clock index connection script conditions)

/-- The full old explicit canonical formula follows by membership in all executions. -/
theorem surface_one {property : Database → Prop} {condition : Resolved.Statement → Database → Prop}
    (keeps : PlainKeeps property condition) (context : ResolveContext) (clock : Option Clock) (index : Nat)
    {connection : Connection} (script : List (Syntax.Statement × List Value)) (holds : connection.state.Holds property)
    (conditions : SurfaceConditions condition context clock index connection script) :
    (runScriptFrom context clock index connection script).connection.state.Holds property :=
  surface keeps context clock index script holds conditions _
    (runScriptFrom_mem_runScriptAllFrom context clock index connection script)

/-- The full old derived all-execution formula uses the old readiness evidence and resolver obligation. -/
theorem surface_derived {property : Database → Prop} {condition : Resolved.Statement → Database → Prop}
    (keeps : ReadyKeeps property condition) (context : ResolveContext) (clock : Option Clock)
    (derive : ∀ (connection : Connection) (statement : Syntax.Statement) resolved after,
      connection.state.Holds property → resolveStatement context connection.resolveState statement = .ok (resolved, after) →
        condition resolved connection.state.database)
    (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds property) :
    ∀ run ∈ runScriptAllFrom context clock index connection script, run.connection.state.Holds property :=
  runScriptAllFrom_holds_derived
    (condition := fun clock counters parameters statement database => condition statement database ∧
      (runStatement clock counters parameters statement database).ready = true)
    (fun clock counters parameters statement database holds met =>
      keeps clock counters parameters statement database holds met.1 met.2) context clock
    (fun _ connection statement _ holds resolved after _ found _ ready =>
      ⟨derive connection statement resolved after holds found, (Bool.and_eq_true_iff.mp ready).1⟩)
    index script holds

/-- The full old derived canonical formula follows by membership in all executions. -/
theorem surface_derived_one {property : Database → Prop} {condition : Resolved.Statement → Database → Prop}
    (keeps : ReadyKeeps property condition) (context : ResolveContext) (clock : Option Clock)
    (derive : ∀ (connection : Connection) (statement : Syntax.Statement) resolved after,
      connection.state.Holds property → resolveStatement context connection.resolveState statement = .ok (resolved, after) →
        condition resolved connection.state.database)
    (index : Nat) {connection : Connection} (script : List (Syntax.Statement × List Value))
    (holds : connection.state.Holds property) :
    (runScriptFrom context clock index connection script).connection.state.Holds property :=
  surface_derived keeps context clock derive index script holds _
    (runScriptFrom_mem_runScriptAllFrom context clock index connection script)

end PreservationMigration
