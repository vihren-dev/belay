import Belay.Sqlite.Model.Resolution.TriggerStatements

set_option doc.verso true

/-! The program of one trigger (ADR 0018, D5): its {lit}`WHEN` condition and the statements of its
body, resolved over the rows that the trigger's event has. The trace of the resolution holds the
names of the condition and of the body at their places in the trigger as written. -/

namespace Belay.Sqlite.Model

/-- The resolved event of a trigger of a table with the columns ({name}`Resolved.TriggerEvent`). -/
def triggerEvent (columns : List CatalogColumn) : Syntax.TriggerEvent → Resolved.TriggerEvent
  | .insert => .insert
  | .delete => .delete
  | .update [] => .update none
  | .update names => .update (some (names.filterMap (columnPosition columns)))

/-- A computation that may fail, run so that its failure is a value: the outcome is the
computation's {lit}`Except` and the trace stays, also after a failure. -/
def Traced.attempt {ε ε' α : Type} (computation : Traced ε α) : Traced ε' (Except ε α) :=
  ⟨.ok computation.drop, computation.trace⟩

/-- Resolve the program of the trigger at the position over the catalog, for a write: its
condition over the trigger's rows, which may not name a subquery, call a function that can fail or call a connection counter ({name}`RestrictionKind.triggerForm`), and its body statements in order
({name}`resolveBodyStatementTraced`); the first prepare error stops. The trace places the names of the
condition below the child 5 of a trigger statement and those of the statement {lit}`k` of the body below
the path {lit}`[6, k]`: a trigger has the fields name, {lit}`IF NOT EXISTS`, time, event, table,
condition and body, in this order, as {lit}`Statement.createTrigger` has them. -/
def resolveProgramTraced (context : ResolveContext) (catalog : Catalog) (position : Nat) (trigger : CatalogTrigger) :
    Traced NodeRestriction (Except PrepareError Resolved.Program) := do
  let some (table, shape) := catalog.findTable trigger.table | pure (.error (.noSuchTable trigger.table))
  let row : TriggerRow := { columns := shape.columns, new := !(trigger.event matches .delete),
                            old := !(trigger.event matches .insert) }
  let condition : Except PrepareError (Option Resolved.Expr) ← match trigger.condition with
    | none => pure (.ok none)
    | some term =>
      let outcome ← Traced.attempt
        ((Traced.condition [] (resolveOperandTraced context.profile.dqsDml (row.scope 0) {} true term)).underTrace [5])
      match outcome with
      | .error (.prepare error) =>
        if error == .raiseOutsideTrigger then throw (triggerRestriction .raiseForm) else pure (.error (.expression error))
      | .error (.restriction path kind) => throw { path, kind }
      | .ok resolved =>
        if resolved.any Resolved.Expr.isFallibleCall || resolved.any Resolved.Expr.namesSubquery ||
            resolved.any Resolved.Expr.isCounter then
          throw (triggerRestriction .triggerForm)
        else pure (.ok (some resolved))
  match condition with
  | .error error => pure (.error error)
  | .ok condition =>
    let body ← trigger.body.zipIdx.foldlM (fun (steps : Except PrepareError (List Resolved.Step)) (statement, index) =>
      match steps with
      | .error error => pure (.error error)
      | .ok steps => (·.map (steps ++ [·])) <$>
        (resolveBodyStatementTraced context catalog row statement).underTrace [6, index]) (.ok [])
    pure (body.map fun body => { trigger := position, table, time := trigger.time,
                                  event := triggerEvent shape.columns trigger.event, width := shape.columns.length,
                                  condition, body })

/-- The program of a trigger: {name}`resolveProgramTraced` without its trace. -/
def resolveProgram (context : ResolveContext) (catalog : Catalog) (position : Nat) (trigger : CatalogTrigger) :
    Except NodeRestriction (Except PrepareError Resolved.Program) :=
  (resolveProgramTraced context catalog position trigger).drop

end Belay.Sqlite.Model
