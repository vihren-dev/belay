import Belay

set_option doc.verso true

/-! The former schema statements of ADR 0033, derived with their original premises. -/

namespace Belay.Sqlite.Model.ReplacedSchema

/-- The deleted law {lit}`runScriptStep_drop_plain`. For every connection and statement that resolves to a drop without rules, and every step that
continues: the step has no error output and no further execution, and the next connection is the
connection with the database after {name}`Database.drop` of the positions and nothing else changed. In
plain words, a plain DROP TABLE never fails (the failure law is empty), and the database after is the
database before without the dropped objects and their row lists (the success law). Proof sketch: the applicable branch of {name}`runScriptStep_dropPlain_eq` gives the result. -/
theorem runScriptStep_drop_plain {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {positions : List Nat}
    (found : resolveStatement context connection.resolveState statement = .ok (.drop positions none, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    output.isError = false ∧ others = [] ∧
      next = { connection with state := { connection.state with
        database := connection.state.database.drop positions } } := by
  rw [runScriptStep_dropPlain_eq found] at step
  cases step; exact ⟨rfl, rfl, rfl⟩

/-- The deleted law {lit}`runScriptStep_drop_frame`. For every connection, statement that resolves to a drop without rules, and step that continues, and
every table that a name finds in the database of the connection at a position that the drop keeps: the
name finds the same table, with the same rows, in the database of the next connection, at the
transported position ({name}`keptBelow`). In plain words, a plain drop keeps every table that it does
not drop, found by name. Proof sketch: the applicable branch of {name}`runScriptStep_dropPlain_eq` gives the result. -/
theorem runScriptStep_drop_frame {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {positions : List Nat}
    (found : resolveStatement context connection.resolveState statement = .ok (.drop positions none, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    {name : Identifier} {position : Nat} {table : Table}
    (present : connection.state.database.tableNamed name = some (position, table))
    (kept : !positions.contains position) :
    next.state.database.tableNamed name = some (keptBelow positions position, table) := by
  rw [runScriptStep_dropPlain_eq found] at step
  cases step; exact Database.tableNamed_drop_kept present kept

/-- The deleted law {lit}`runScriptStep_dropTable_frame`. For every connection with foreign keys off, DROP TABLE of a name that resolves to a drop of some positions
(the premise {lit}`found`; a drop that SQLite refuses resolves to a prepare error and is not covered), and step that
continues: a table that another name finds in the database of the connection, at a position, is found by that name
in the database of the next connection with the same rows, at the transported position
({name}`keptBelow` of the dropped positions). In plain words, with foreign keys off DROP TABLE of one table leaves
every table of another name as it was, and the premise {lit}`off` is what excludes a cascade. The theorem says
nothing about the table that the drop removes. Proof sketch: the applicable branch of {name}`runScriptStep_dropPlain_eq` gives the result. -/
theorem runScriptStep_dropTable_frame {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {positions : List Nat} {rules : Option Resolved.WriteRules}
    {dropped : Identifier} {ifExists : Bool}
    (off : connection.foreignKeys = false)
    (found : resolveStatement context connection.resolveState (.dropTable dropped ifExists) =
      .ok (.drop positions rules, after))
    (step : runScriptStep context clock index connection (.dropTable dropped ifExists) parameters =
      .continued output next others)
    {other : Identifier} {position : Nat} {table : Table}
    (differs : other.folded ≠ dropped.folded)
    (present : connection.state.database.tableNamed other = some (position, table)) :
    next.state.database.tableNamed other = some (keptBelow positions position, table) := by
  obtain ⟨rfl, positionsEq⟩ := resolveStatement_dropTable_off context connection.resolveState after dropped ifExists off found
  refine runScriptStep_drop_frame found step present ?_
  rcases positionsEq with rfl | ⟨droppedAt, droppedTable, droppedFound, rfl⟩
  · rfl
  · obtain ⟨otherFound, -⟩ := Database.tableNamed_some present
    simpa using Catalog.tableObjects_not_contains droppedFound otherFound differs

#print axioms runScriptStep_drop_plain
#print axioms runScriptStep_drop_frame
#print axioms runScriptStep_dropTable_frame

end Belay.Sqlite.Model.ReplacedSchema
