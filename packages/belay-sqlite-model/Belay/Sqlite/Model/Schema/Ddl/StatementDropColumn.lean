import Belay.Sqlite.Model.Schema.Ddl.StatementRewrite
import Belay.Sqlite.Model.Schema.Ddl.DropColumnDatabaseLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- The contract of a DROP COLUMN that the model runs: the run succeeds and the result is the database without the
cells of the column and with the stored catalog. Proof sketch: the guard of {name}`step` holds. -/
theorem step_dropColumn_of_runs (clock : Int) (counters : Counters) (parameters : List Value)
    {database : Database} {position index : Nat} {stored : Catalog}
    (runs : database.runsDropColumn position index stored = true) :
    step clock counters parameters (.dropColumn position index stored) database =
      .ok (database.dropColumn position index stored) := by
  simp [step, runs]

/-- For every clock value, counters, parameters, position, index, catalog, property and database: if the database has
the property, and the database after the drop has it whenever the model runs the drop, the effect of
{name}`runStatement` for the DROP COLUMN satisfies the property ({name}`Effect.Satisfies`). Proof sketch: the run is
{name}`step`, which stores the dropped database when {name}`Database.runsDropColumn` and else fails with the input
database. Success and {lit}`constraintFail` need the property. Every other error, including the rejection as
{lit}`ExecutionError.unmodeled`, puts no obligation on the database. -/
theorem runStatement_dropColumn_satisfies (clock : Int) (counters : Counters) (parameters : List Value)
    (position index : Nat) (stored : Catalog) {database : Database} {property : Database → Prop}
    (kept : property database)
    (after : database.runsDropColumn position index stored = true → property (database.dropColumn position index stored)) :
    (runStatement clock counters parameters (.dropColumn position index stored) database).effect.Satisfies property := by
  simp only [runStatement, step]
  split
  · rename_i runs
    exact Effect.satisfies_of_effectDatabase (after runs)
  · exact Effect.satisfies_of_database kept rfl

/-- For every property of a table that a drop keeps, and every database whose tables have it: the effect of a DROP
COLUMN satisfies "every table has the property". The property must hold again for the table without the column
when the table can lose it, and for a table with the same rows and a shape that differs only in names, which the
stored catalog gives. Proof sketch: {name}`runStatement_dropColumn_satisfies`; the database with the catalog after
the drop has the property in the table without the column ({name}`Database.EveryTable.dropColumn`), and the stored
catalog has its outline ({name}`Database.EveryTable.of_outline`). -/
theorem runStatement_dropColumn_eachTable {atom : Table → Prop}
    (dropped : ∀ table index, atom table → table.shape.DropsCleanly index → atom (table.dropColumn index))
    (renamed : ∀ table other, atom table → other.rows = table.rows →
      table.shape.blankNames = other.shape.blankNames → atom other)
    (clock : Int) (counters : Counters) (parameters : List Value) (position index : Nat) (stored : Catalog)
    {database : Database} (every : database.EachTable atom) :
    (runStatement clock counters parameters (.dropColumn position index stored) database).effect.Satisfies
      fun after => after.EachTable atom :=
  runStatement_dropColumn_satisfies clock counters parameters position index stored every fun runs => by
    obtain ⟨⟨shape, shapeFound, clean, _⟩, outline, _⟩ := Database.runsDropColumn_spec runs
    have droppedEvery := Database.EveryTable.dropColumn (index := index) shapeFound every (fun _ _ _ holds => holds)
      fun table present holds => by
        have same : table.shape = shape := by
          simp only [Database.table, shapeFound, Option.map_some, Option.some.injEq] at present
          rw [← present]
        exact dropped table index holds (same ▸ clean)
    exact Database.EveryTable.of_outline (fun _ first second rows shapes holds => renamed first second holds rows shapes)
      droppedEvery (renamed := stored) outline

end Belay.Sqlite.Model
