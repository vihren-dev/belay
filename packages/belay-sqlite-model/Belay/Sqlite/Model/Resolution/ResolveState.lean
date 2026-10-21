import Belay.Sqlite.Model.Resolution.TriggerRules
import Belay.Sqlite.Model.Resolution.StatementCatalog

set_option doc.verso true

/-! The state of name resolution between statements: the catalog, the catalog that an open
transaction saved, and the setting of {lit}`PRAGMA foreign_keys` (ADR 0018, D4), with the
step of a statement that is not transaction control and the step of a write, which checks its
foreign keys when they are on. -/

namespace Belay.Sqlite.Model

/-- The catalog during resolution, the catalog that the open transaction saved, and whether
foreign keys are on. Omit {lit}`saved` outside a transaction and {lit}`foreignKeys` with
foreign keys off. -/
structure ResolveState where
  /-- The current catalog. -/
  catalog : Catalog
  /-- The catalog at BEGIN, while a transaction is open. -/
  saved : Option Catalog := none
  /-- Whether foreign keys are on ({lit}`PRAGMA foreign_keys`). -/
  foreignKeys : Bool := false
  deriving Repr, DecidableEq

/-- The state after a statement that is not transaction control: the catalog after
the statement, and the same saved catalog and setting. -/
def ResolveState.withCatalog (state : ResolveState) (result : StatementResolution) :
    Except Restriction (Resolved.Statement × ResolveState) :=
  result.map fun (statement, catalog) => (statement, { state with catalog := catalog })

/-- The state after a write at the zero-based index ({name}`ResolveState.withCatalog`): with
foreign keys on, the write checks its keys ({name}`foreignKeyCheck`); it gets the programs of the
triggers that it may fire ({name}`triggerPrograms`), whose writes check their keys with foreign
keys on; and with a key to check or a program, the rules that it runs row by row
({name}`Resolved.Statement.withRules`), with the profile's trigger depth limit and the setting. A prepare error of its keys or of a program leaves the state as it was. -/
def ResolveState.withWrite (context : ResolveContext) (state : ResolveState) (index : Nat)
    (result : StatementResolution) : Except Restriction (Resolved.Statement × ResolveState) := do
  let (statement, next) ← state.withCatalog result
  let keys ← if state.foreignKeys then foreignKeyCheck state.catalog index statement else pure (.ok false)
  match keys with
  | .error error => return (.prepareError error, state)
  | .ok keys =>
    match ← triggerPrograms context state.catalog index state.foreignKeys statement with
    | .error error => return (.prepareError error, state)
    | .ok programs =>
      if keys || !programs.isEmpty then
        return (statement.withRules { depth := context.profile.limits.triggerDepth, keys := state.foreignKeys, programs },
          next)
      else return (statement, next)

/-- For every resolved statement and rules, the write with the rules
({name}`Resolved.Statement.withRules`) changes the catalog as the statement does and has its
form. Proof sketch: each constructor keeps every field that the two functions read. -/
theorem Resolved.Statement.withRules_same (statement : Resolved.Statement) (rules : Resolved.WriteRules) :
    (statement.withRules rules).applyCatalog = statement.applyCatalog ∧
      (statement.withRules rules).kind = statement.kind := by
  cases statement <;> exact ⟨rfl, rfl⟩

/-- For every context, state, index, resolution and result of {name}`ResolveState.withWrite`:
the result is a prepare error with the state unchanged, or comes from a statement of the
resolution with its catalog, with the same catalog change and form, and keeps the saved catalog
and the setting. Proof sketch: unfold the definition; each branch gives a prepare error with the
state, the statement, or the statement with rules, which keeps the catalog change and form
({name}`Resolved.Statement.withRules_same`). -/
theorem ResolveState.withWrite_cases {context : ResolveContext} {state next : ResolveState} {index : Nat}
    {result : StatementResolution} {resolved : Resolved.Statement}
    (ok : state.withWrite context index result = .ok (resolved, next)) :
    (∃ error, resolved = .prepareError error ∧ next = state) ∨
      ∃ statement catalog, result = .ok (statement, catalog) ∧ next = { state with catalog } ∧
        resolved.applyCatalog = statement.applyCatalog ∧ resolved.kind = statement.kind := by
  unfold ResolveState.withWrite ResolveState.withCatalog at ok
  rcases result with _ | ⟨statement, catalog⟩
  · cases ok
  · simp only [Except.map, bind, Except.bind, pure, Except.pure] at ok
    repeat' split at ok
    all_goals first
      | (cases ok; exact .inl ⟨_, rfl, rfl⟩)
      | (cases ok; exact .inr ⟨_, _, rfl, rfl, (Resolved.Statement.withRules_same _ _).1,
          (Resolved.Statement.withRules_same _ _).2⟩)
      | (cases ok; exact .inr ⟨_, _, rfl, rfl, rfl, rfl⟩)
      | cases ok

end Belay.Sqlite.Model
