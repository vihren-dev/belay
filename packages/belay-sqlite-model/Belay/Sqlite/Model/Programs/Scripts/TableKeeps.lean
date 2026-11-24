import Belay.Sqlite.Model.Programs.Scripts.ControlRules
import Belay.Sqlite.Model.Programs.Scripts.CreateTableRule
import Belay.Sqlite.Model.Programs.Scripts.DropTableStepLaws
import Belay.Sqlite.Model.Programs.Scripts.ExecutionEffects
import Belay.Sqlite.Model.Programs.Scripts.ReadOnlyFrame
import Belay.Sqlite.Model.Programs.Scripts.CatalogChangeRules

set_option doc.verso true

/-! A one-statement frame check for callers that follow a single table across a migration. -/

namespace Belay.Sqlite.Model

/-- The position of a table after a statement whose effects preserve its definition and rows.
Give the catalog before the statement so a catalog rewrite can compare table definitions.
For a plain DROP the result counts the surviving objects below the table. A result of
{lean}`(none : Option Nat)` means the check gives no guarantee. -/
def Resolved.Statement.keeps (statement : Resolved.Statement) (catalog : Catalog) (position : Nat) : Option Nat :=
  match statement with
  | .begin | .commit | .setting .. | .query .. | .createTable .. => some position
  | .insertSelect target _ _ _ _ _ _ none => if position = target then none else some position
  | .drop positions none => if positions.contains position then none else some (keptBelow positions position)
  | .rewrite renamed => if renamed.tableAt position == catalog.tableAt position then some position else none
  | .insert .. | .update .. | .delete .. =>
    statement.plainWriteTarget.bind fun target => if position = target then none else some position
  | .insertSelect _ _ _ _ _ _ _ (some _) | .drop _ (some _) | .rollback | .createView .. | .createIndex ..
  | .createTrigger .. | .addColumn .. | .dropColumn .. | .prepareError _ | .upsert .. => none

/-- With no alternative executions, every member of the step reaches the given next connection. -/
private theorem singleConnection {output : Output} {next : Connection} {execution : StatementExecution}
    (mem : execution ∈ (RunStep.continued output next []).executions) : execution.next = next := by
  simp only [RunStep.executions, List.mem_singleton] at mem
  rw [mem]

/-- For every statement that resolves and continues, if {name}`Resolved.Statement.keeps` gives a
destination for a table in the input database, each successful execution holds the same table
at the destination. It preserves the definition and rows and makes no claim about other tables
or counters. Proof sketch: control statements and reads preserve the database. The frame law
of each write gives its target rows, the position after a drop or the catalog after a rewrite.
The INSERT from a query law applies to each of its possible executions. -/
theorem runScriptStep_keepsTable {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {c next : Connection} {statement : Syntax.Statement} {parameters : List Value} {output : Output}
    {others : List StatementExecution} {resolved : Resolved.Statement} {after : ResolveState}
    {position destination : Nat} {table : Table}
    (resolution : resolveStatement context c.resolveState statement = .ok (resolved, after))
    (kept : resolved.keeps c.state.database.catalog position = some destination)
    (present : c.state.database.table position = some table)
    (step : runScriptStep context clock index c statement parameters = .continued output next others)
    {found : StatementExecution} (member : found ∈ (RunStep.continued output next others).executions)
    (ok : found.output.isError = false) : found.next.state.database.table destination = some table := by
  unfold Resolved.Statement.keeps at kept
  split at kept
  · cases kept
    rw [runScriptStep_begin_eq resolution] at step
    split at step <;> cases step <;> rw [singleConnection member] <;> exact present
  · cases kept
    rw [runScriptStep_commit_eq resolution] at step
    split at step <;> cases step <;> rw [singleConnection member] <;> exact present
  · cases kept
    rw [runScriptStep_setting_eq resolution] at step
    cases step
    rw [singleConnection member]
    rename_i setting on
    cases setting <;> exact present
  · cases kept
    obtain ⟨rfl, rfl⟩ := runScriptStep_readOnly_keeps resolution (Or.inl ⟨_, _, rfl⟩) step
    rw [singleConnection member]
    exact present
  · cases kept
    rw [runScriptStep_createTable_eq resolution] at step
    split at step
    · cases step
      rw [singleConnection member]
      exact Database.table_createTable _ _ present
    · cases step
  · split at kept <;> try contradiction
    rename_i distinct
    cases kept
    obtain ⟨rows, _, nextEq⟩ := runScriptStep_insertSelect_frame step resolution found member ok
    rw [nextEq]
    exact (Database.table_setRows_other _ rows distinct).trans present
  · split at kept <;> try contradiction
    rename_i survives
    cases kept
    rw [runScriptStep_dropPlain_eq resolution] at step
    cases step
    rw [singleConnection member]
    exact (Database.table_drop_kept _ _ (by simpa using survives)).trans present
  · split at kept <;> try contradiction
    rename_i equal
    cases kept
    rw [runScriptStep_rewrite_eq resolution] at step
    dsimp only at step
    split at step <;> cases step
    rw [singleConnection member]
    simpa only [Connection.withDatabase, Database.table, eq_of_beq equal] using present
  all_goals try contradiction
  all_goals
    obtain ⟨target, plain, destinationEq⟩ := Option.bind_eq_some_iff.mp kept
    split at destinationEq <;> try contradiction
    rename_i distinct
    cases destinationEq
    obtain ⟨rfl, _, _, _, write⟩ := runScriptStep_plainWrite_frame resolution plain step
    rw [singleConnection member]
    rcases write with same | ⟨rows, updated⟩
    · simpa only [same] using present
    · rw [updated, Database.table_setRows_other _ rows distinct]
      exact present

end Belay.Sqlite.Model
