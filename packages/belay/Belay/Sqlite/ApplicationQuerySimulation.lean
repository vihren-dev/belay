import Belay.Sqlite.ApplicationSimulation
import Belay.Sqlite.MigrationQueryFrames

set_option doc.verso true

/-! A full-state simulation from query calls (ADR 0017, S8). A pairing whose calls are queries that keep
the connection is a full-state simulation when each call translates weakly and meets the frame facts of
{name}`Belay.Sqlite.Migration.QueryFrames`. The weak translation alone is not enough, as the fixture
{lit}`ApplicationWeakBridges` shows. -/

namespace Belay.Sqlite

open Belay.Sqlite.Calls Belay.Sqlite.Migration

/-- For every pairing, migration and predicate: if each call translates weakly, meets the frame facts of
{name}`QueryFrames`, the clock gives one date at every index at the contexts of the predicate, and the
migration reaches one connection with one count of outputs on all its branches, then the pairing is a
full-state simulation ({name}`Simulation`). Plain words: both parts of a full-state simulation hold. At
every context where the predicate holds and the migration succeeds, each call commutes with the migration
in the full context. After every returning branch of a call from such a context, the predicate holds and
the migration succeeds again. At other contexts the conclusion requires nothing. Proof sketch: {name}`TranslatesOn.commutes_of_query` gives the commutation. The call keeps the
connection and the predicate, and a constant clock lets the migration succeed at the later index
({name}`Sql.succeedsFrom_index`). -/
theorem Simulation.ofQueries {Name : Type} {signature : Signature Name} {μ : Type} {migration : Sql μ}
    {admitted : ExecutionContext → Prop} {pairing : Pairing signature}
    (translation : ∀ name argument,
      TranslatesOn migration admitted (pairing.old.run name argument) (pairing.new.run name argument))
    (frames : ∀ name argument,
      QueryFrames migration admitted (pairing.old.run name argument) (pairing.new.run name argument))
    (constant : ∀ state, admitted state → ∀ assignment ∈ state.clock, ∀ one other, assignment one = assignment other)
    (uniform : ∀ state, Domain migration admitted state → ∀ one other,
      migration.Branch state.clock state.index state.connection one →
      migration.Branch state.clock state.index state.connection other →
        one.connection = other.connection ∧ one.outputs.length = other.outputs.length) :
    Simulation migration admitted pairing :=
  ⟨fun name argument => TranslatesOn.commutes_of_query (translation name argument) (frames name argument)
      constant uniform,
   fun name argument state domain first branch _ returned => by
    obtain ⟨keeps, -⟩ := (frames name argument).queryKeeps state domain first branch
    refine ⟨(frames name argument).admittedKept state domain first branch, ?_⟩
    show migration.SucceedsFrom state.clock (state.index + first.outputs.length) first.connection
    rw [keeps]
    exact (Sql.succeedsFrom_index migration state.clock (constant state domain.1) state.index _ state.connection).1 domain.2⟩

end Belay.Sqlite
