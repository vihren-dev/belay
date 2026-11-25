import Belay.Sqlite.Model.Programs.Scripts.TablePath
import Belay.Sqlite.Model.Programs.Scripts.CreateTableRule
import Belay.Sqlite.Model.Schema.Ddl.SchemaExtensionLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Locate the empty table created at statement {lit}`origin` after a prefix of length {lit}`count`.
The result contains its position and shape. It is absent before creation, for a no-op, and once a
statement could change that table. For example the empty prefix gives {lean}`(none : Option (Nat × CatalogTable))`. -/
def ResolveState.createdTable (initial : ResolveState) (path : List Resolved.Statement)
    (origin : Nat) : (count : Nat) → Option (Nat × CatalogTable)
  | 0 => none
  | n + 1 => do
    let stmt ← path[n]?
    if n = origin then
      match stmt with
      | .createTable pos _ shape => some (pos, shape)
      | _ => none
    else
      let (old, shape) ← initial.createdTable path origin n
      let pos ← stmt.keeps (initial.atPrefix path n).catalog old
      return (pos, shape)

/-- At every origin for which {name}`ResolveState.createdTable` reports a position and a shape,
the database at this prefix holds that shape and no rows at that position. An absent result imposes no condition. -/
def ResolveState.CreatedTablesAt (initial : ResolveState) (path : List Resolved.Statement)
    (n : Nat) (database : Database) : Prop :=
  ∀ origin pos shape, initial.createdTable path origin n = some (pos, shape) →
    database.table pos = some ⟨shape, []⟩

/-- Suppose the statement resolves to the entry at position {lit}`n` of the path, the connection's
resolution state equals the prefix state there, and its database satisfies {name}`ResolveState.CreatedTablesAt`
for that prefix. If the step continues, the next database of every error-free execution satisfies
{name}`ResolveState.CreatedTablesAt` at {lit}`n + 1`. Proof sketch: for a fresh creation, the kind rule
{name}`runScriptStep_createTable_eq` gives the next database and {name}`Database.table_createTable_end` the empty
table at the end. For a previous creation,
{name}`runScriptStep_keepsTable` supplies the new lookup whenever the frame check succeeds. -/
theorem runScriptStep_createdTables {context : ResolveContext} {clock : Option Clock} {index n : Nat}
    {initial : ResolveState} {path : List Resolved.Statement} {resolved : Resolved.Statement} {after : ResolveState}
    {c next : Connection} {statement : Syntax.Statement} {parameters : List Value}
    {out : Output} {others : List StatementExecution} {ex : StatementExecution}
    (atStmt : path[n]? = some resolved) (same : c.resolveState = initial.atPrefix path n)
    (resolution : resolveStatement context c.resolveState statement = .ok (resolved, after))
    (before : initial.CreatedTablesAt path n c.state.database)
    (step : runScriptStep context clock index c statement parameters = .continued out next others)
    (member : ex ∈ (RunStep.continued out next others).executions) (ok : ex.output.isError = false) :
    initial.CreatedTablesAt path (n + 1) ex.next.state.database := by
  intro origin pos shape found
  simp only [ResolveState.createdTable, atStmt, bind, Option.bind_some] at found
  split at found
  · cases resolved <;> try contradiction
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj found)
    rw [runScriptStep_createTable_eq resolution] at step
    split at step
    · rename_i guard
      cases step
      simp only [RunStep.executions, List.mem_singleton] at member
      subst ex
      obtain ⟨rfl, aligned⟩ := guard
      exact Database.table_createTable_end _ _ aligned
    · cases step
  · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨⟨old, priorShape⟩, previous, moved, kept, rfl, rfl⟩ := found
    rw [← same] at kept
    exact runScriptStep_keepsTable resolution kept (before origin old priorShape previous) step member ok

end Belay.Sqlite.Model
