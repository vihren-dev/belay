import Belay.Sqlite.Model.Programs.Scripts.TablePath
import Belay.Sqlite.Model.Programs.Scripts.CreateTableStepLaws
import Belay.Sqlite.Model.Schema.Ddl.SchemaExtensionLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Whenever a resolved CREATE TABLE step continues, the new position holds the resolved table shape
with no rows. Proof sketch: {name}`runScriptStep_createTable` gives the appended table and the aligned
row stores. Looking up the append position selects the new table and the last, empty store. -/
theorem runScriptStep_createTable_empty {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {c next : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {pos : Nat} {name : Identifier} {shape : CatalogTable} {out : Output} {others : List StatementExecution}
    (resolved : resolveStatement context c.resolveState statement = .ok (.createTable pos name shape, after))
    (step : runScriptStep context clock index c statement parameters = .continued out next others) :
    next.state.database.table pos = some ⟨shape, []⟩ := by
  obtain ⟨_, _, rfl, aligned, rfl⟩ := runScriptStep_createTable resolved step
  simp [Database.table, Catalog.tableAt_createTable_end, List.getD_eq_getElem?_getD, aligned]

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

/-- Each successful execution of a resolved step carries the created tables of the prefix to the next
prefix. A fresh creation uses {name}`runScriptStep_createTable_empty`. For a previous creation,
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
    obtain ⟨_, rfl, _⟩ := runScriptStep_createTable resolution step
    simp only [RunStep.executions, List.mem_singleton] at member
    subst ex
    exact runScriptStep_createTable_empty resolution step
  · simp only [Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at found
    obtain ⟨⟨old, priorShape⟩, previous, moved, kept, rfl, rfl⟩ := found
    rw [← same] at kept
    exact runScriptStep_keepsTable resolution kept (before origin old priorShape previous) step member ok

end Belay.Sqlite.Model
