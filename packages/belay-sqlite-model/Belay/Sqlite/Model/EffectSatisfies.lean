import Belay.Sqlite.Model.Execution

set_option doc.verso true

/-! Properties of every database retained by a statement effect, including constraint FAIL. -/

namespace Belay.Sqlite.Model

/-- For the given property of a database: it holds for every database that a run can keep from
the effect. These are two cases:
* the effect succeeds with the database;
* the effect fails with {name}`ExecutionError.constraintFail` and carries the database, which
  keeps the rows that a FAIL write stored before the failed row.

An error with any other reason requires nothing: the run keeps the input database, or the
snapshot of a ROLLBACK, for it ({lit}`SqlState.publish`). -/
def Effect.Satisfies (property : Database → Prop) (effect : Effect) : Prop :=
  ∀ database, effect = .ok database ∨ effect = .error (.constraintFail, database) → property database

/-- For every property and effect: if the database of the effect ({name}`effectDatabase`) has
the property, the effect satisfies it ({name}`Effect.Satisfies`). Proof sketch: both databases of
{name}`Effect.Satisfies` are the database of the effect. -/
theorem Effect.satisfies_of_effectDatabase {property : Database → Prop} {effect : Effect}
    (holds : property (effectDatabase effect)) : effect.Satisfies property := by
  intro database kept
  rcases kept with same | same <;> subst same <;> exact holds

/-- For every property, effect and database: if the database has the property and the database of
the effect is the database, the effect satisfies the property. This is the case of each statement
that writes no row, and of each error that keeps the input database. Proof sketch:
{name}`Effect.satisfies_of_effectDatabase` after rewriting the database of the effect. -/
theorem Effect.satisfies_of_database {property : Database → Prop} {effect : Effect} {database : Database}
    (holds : property database) (kept : effectDatabase effect = database) : effect.Satisfies property :=
  Effect.satisfies_of_effectDatabase (kept ▸ holds)

/-- For every four properties of an effect: if the effect satisfies each of them
({name}`Effect.Satisfies`), it satisfies their conjunction. Proof sketch: a database that a run keeps
from the effect has each property. -/
theorem Effect.satisfies_and {first second third fourth : Database → Prop} {effect : Effect}
    (one : effect.Satisfies first) (two : effect.Satisfies second) (three : effect.Satisfies third)
    (four : effect.Satisfies fourth) : effect.Satisfies fun database => first database ∧ second database ∧
      third database ∧ fourth database :=
  fun database kept => ⟨one database kept, two database kept, three database kept, four database kept⟩

end Belay.Sqlite.Model
