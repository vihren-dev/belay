import Belay.Sqlite.Resolution.ForeignKeyResolution
import Belay.Sqlite.Resolution.StatementCatalog

set_option doc.verso true

/-! The state of name resolution between statements: the catalog, the catalog that an open
transaction saved, and the setting of {lit}`PRAGMA foreign_keys` (ADR 0018, D4), with the
step of a statement that is not transaction control and the step of a write, which checks its
foreign keys when they are on. -/

namespace Belay.Sqlite

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

/-- The state after a write at the zero-based index ({name}`ResolveState.withCatalog`); with
foreign keys on, the write checks its keys ({name}`enforceForeignKeys`), and a prepare error of
its keys leaves the state as it was. -/
def ResolveState.withWrite (context : ResolveContext) (state : ResolveState) (index : Nat)
    (result : StatementResolution) : Except Restriction (Resolved.Statement × ResolveState) := do
  let (statement, next) ← state.withCatalog result
  if !state.foreignKeys then return (statement, next)
  match ← enforceForeignKeys context state.catalog index statement with
  | .prepareError error => return (.prepareError error, state)
  | checked@(.createTable ..) | checked@(.createIndex ..) | checked@(.addColumn ..) | checked@(.drop ..)
  | checked@.begin | checked@.commit | checked@.rollback | checked@(.insert ..) | checked@(.upsert ..)
  | checked@(.update ..) | checked@(.delete ..) | checked@(.query ..) | checked@(.setting _) =>
    return (checked, next)

/-- For every resolved statement and trigger depth limit, the write with the limit
({name}`Resolved.Statement.withForeignKeys`) changes the catalog as the statement does and has
its form. Proof sketch: each constructor keeps every field that the two functions read. -/
theorem Resolved.Statement.withForeignKeys_same (statement : Resolved.Statement) (depth : Nat) :
    (statement.withForeignKeys depth).applyCatalog = statement.applyCatalog ∧
      (statement.withForeignKeys depth).kind = statement.kind := by
  cases statement <;> exact ⟨rfl, rfl⟩

/-- For every context, catalog, index, statement and result: if {name}`enforceForeignKeys`
gives the result, the result is the statement, a prepare error, or the statement with a trigger
depth limit. Proof sketch: each branch of the definition gives one of them. -/
theorem enforceForeignKeys_cases {context : ResolveContext} {catalog : Catalog} {index : Nat}
    {statement result : Resolved.Statement} (ok : enforceForeignKeys context catalog index statement = .ok result) :
    result = statement ∨ (∃ error, result = .prepareError error) ∨ ∃ depth, result = statement.withForeignKeys depth := by
  unfold enforceForeignKeys at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact .inl rfl)
    | (cases ok; exact .inr (.inl ⟨_, rfl⟩))
    | (cases ok; exact .inr (.inr ⟨_, rfl⟩))
    | cases ok

/-- For every context, state, index, resolution and result of {name}`ResolveState.withWrite`:
the result is a prepare error with the state unchanged, or comes from a statement of the
resolution with its catalog, with the same catalog change and form, and keeps the saved catalog
and the setting. Proof sketch: unfold the definition; {name}`enforceForeignKeys_cases` gives the
statement, a prepare error or the statement with a limit, and
{name}`Resolved.Statement.withForeignKeys_same` keeps the catalog change and form. -/
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
    split at ok
    · cases ok
      exact .inr ⟨_, _, rfl, rfl, rfl, rfl⟩
    · split at ok
      · cases ok
      · rename_i checked enforced
        split at ok
        · cases ok
          exact .inl ⟨_, rfl, rfl⟩
        all_goals
          cases ok
          rcases enforceForeignKeys_cases enforced with same | ⟨_, same⟩ | ⟨depth, same⟩
          · exact .inr ⟨_, _, rfl, rfl, by rw [same], by rw [same]⟩
          · cases same
          · exact .inr ⟨_, _, rfl, rfl, by rw [same]; exact (Resolved.Statement.withForeignKeys_same _ depth).1,
              by rw [same]; exact (Resolved.Statement.withForeignKeys_same _ depth).2⟩

end Belay.Sqlite
