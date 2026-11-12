import Belay.Sqlite.Model.Programs.Scripts.StatementStep
import Belay.Sqlite.Model.Schema.Ddl.KeysUniqueDrop

set_option doc.verso true

/-! The theorem of the atom "keys unique" (ADR 0022, D3, slice 2) for DROP TABLE and DROP INDEX
without the row engine. A drop keeps the other objects with their rows and renumbers them
({lit}`keptBelow`). A kept table keeps its keys when no unique index that the drop keeps is on a
table that it drops: otherwise the index would name the next kept position, as the task file's
counterexample shows. -/

namespace Belay.Sqlite.Model

/-- For every clock value, counters, parameter list, DROP without foreign key rules and trigger programs
({lean}`(none : Option Resolved.WriteRules)`) and database: if the database satisfies
{name}`Database.KeysUnique` and its catalog meets the condition of DROP at the positions
({name}`Catalog.DropCondition`), the effect of {name}`runStatement` satisfies
{name}`Effect.Satisfies` for {name}`Database.KeysUnique`. Proof sketch: the effect is the database after
{name}`Database.drop` ({name}`Database.KeysUnique.drop`). -/
theorem runStatement_drop_keysUnique (clock : Int) (counters : Counters) (parameters : List Value) (positions : List Nat)
    {database : Database} (unique : database.KeysUnique) (condition : database.catalog.DropCondition positions) :
    (runStatement clock counters parameters (.drop positions none) database).effect.Satisfies Database.KeysUnique := by
  simp only [runStatement, Option.map_none, StatementRun.withKeys, step]
  exact Effect.satisfies_of_effectDatabase (unique.drop condition)

end Belay.Sqlite.Model
