import Belay.Sqlite.MigrationPatternSuccess
import Belay.Sqlite.MigrationPattern
import Belay.Sqlite.ProgramBindLaws
import Belay.Sqlite.ProgramQueries
import Belay.Sqlite.ExecutionViewBind

set_option doc.verso true

/-! The observations of an application that runs after a successful quiet migration (ADR 0017, S6).
The observations of the application after the migration are the observations of the application alone, run
at the connection that a branch of the migration reaches and at the raw index shifted by the outputs of that
branch. Different branches can reach different connections: the actual observation uses the actual run, and
the set of branch observations is the union over the branches of the migration. -/

namespace Belay.Sqlite.Migration
open Model

/-- For a returning prefix branch with an error-free trace, the annotated observation of the migration
followed by any application branch is the observation of that application branch alone. The quiet
migration segment contributes no output. Proof sketch: split the projection at the prefix
({name}`Sql.View.project_bind_return`), then use {name}`Sql.View.project_quiet_of_allOk` and the
identity projection. -/
theorem afterView_observation_of_branch {μ α : Type} (migration : Sql μ) (replacement : Sql α)
    {clock : Option Clock} {index : Nat} {connection : Connection} {first : SqlRun μ} {value : μ}
    (before : migration.Branch clock index connection first) (returned : first.value = some value)
    (ok : List.allOk first.outputs = true) (last : SqlRun α) :
    (afterView migration replacement).observation { last with outputs := first.outputs ++ last.outputs } =
      last.observation := by
  have projected : (afterView migration replacement).project (first.outputs ++ last.outputs) = last.outputs := by
    have split := Sql.View.project_bind_return before (Sql.View.quiet migration) returned (fun _ => replacement)
      (fun _ => Sql.View.identity replacement) last.outputs
    have quiet := Sql.View.project_quiet_of_allOk before ok
    simp only [quiet, Sql.View.project_identity, List.nil_append] at split
    exact split
  change (last.value, (afterView migration replacement).project (first.outputs ++ last.outputs)) =
    (last.value, last.outputs)
  rw [projected]

/-- If the migration succeeds, then the actual observation of the migration followed by the replacement
equals the actual observation of the replacement alone, run at the connection that the actual run of the
migration reaches and at the raw index shifted by the outputs of that run. Proof sketch: the actual migration
run is a branch ({name}`Sql.Branch.actual`); {name}`Sql.runFrom_bind` splits the run, and
{name}`afterView_observation_of_branch` removes the quiet prefix. -/
theorem afterView_observation_actual {μ α : Type} (migration : Sql μ) (replacement : Sql α)
    (state : ExecutionContext) (success : migration.SucceedsFrom state.clock state.index state.connection) :
    (afterView migration replacement).observation
        ((after migration replacement).runFrom state.clock state.index state.connection) =
      (replacement.runFrom state.clock
        (state.index + (migration.runFrom state.clock state.index state.connection).outputs.length)
        (migration.runFrom state.clock state.index state.connection).connection).observation := by
  have actualBranch := Sql.Branch.actual migration state.clock state.index state.connection
  obtain ⟨returned, ok⟩ := (Sql.succeedsFrom_iff_branches migration _ _ _).mp success _ actualBranch
  obtain ⟨value, hasValue⟩ := Option.isSome_iff_exists.mp returned
  have run := Sql.runFrom_bind migration (fun _ => replacement) state.clock state.index state.connection
  change (afterView migration replacement).observation
    ((migration.bind fun _ => replacement).runFrom state.clock state.index state.connection) = _
  rw [run]
  unfold SqlRun.andThen
  simp only [hasValue]
  exact afterView_observation_of_branch migration replacement actualBranch hasValue ok _

/-- If the migration succeeds, then the set of observations of branches of the migration followed by the
replacement equals the union, over the branches of the migration, of the sets of observations of branches of
the replacement alone, run at the connection that the migration branch reaches and at the raw index shifted
by its outputs. This includes every raw and concrete branch of the migration, and the branches can reach
different connections. Proof sketch: split each bind branch with {name}`Sql.branch_bind_iff`; the success
premise gives the returned value and the quiet outputs of each migration branch, and
{name}`afterView_observation_of_branch` equates the observations. -/
theorem afterView_observation_branches {μ α : Type} (migration : Sql μ) (replacement : Sql α)
    (state : ExecutionContext) (success : migration.SucceedsFrom state.clock state.index state.connection)
    (observation : Option α × List Output) :
    (∃ result, (after migration replacement).Branch state.clock state.index state.connection result ∧
        (afterView migration replacement).observation result = observation) ↔
      ∃ first, migration.Branch state.clock state.index state.connection first ∧
        ∃ result, replacement.Branch state.clock (state.index + first.outputs.length) first.connection result ∧
          result.observation = observation := by
  constructor
  · rintro ⟨result, branch, seen⟩
    have bound : (migration.bind fun _ => replacement).Branch state.clock state.index state.connection result := branch
    obtain ⟨first, before, continuation⟩ := (Sql.branch_bind_iff migration _ _ _ _ result).mp bound
    obtain ⟨returned, ok⟩ := (Sql.succeedsFrom_iff_branches migration _ _ _).mp success first before
    obtain ⟨value, hasValue⟩ := Option.isSome_iff_exists.mp returned
    simp only [hasValue] at continuation
    obtain ⟨last, lastBranch, rfl⟩ := continuation
    exact ⟨first, before, last, lastBranch,
      (afterView_observation_of_branch migration replacement before hasValue ok last).symm.trans seen⟩
  · rintro ⟨first, before, last, lastBranch, seen⟩
    obtain ⟨returned, ok⟩ := (Sql.succeedsFrom_iff_branches migration _ _ _).mp success first before
    obtain ⟨value, hasValue⟩ := Option.isSome_iff_exists.mp returned
    exact ⟨_, Sql.Branch.bind_return before hasValue (fun _ => replacement) (last := last) lastBranch,
      (afterView_observation_of_branch migration replacement before hasValue ok last).trans seen⟩

/-- If the migration succeeds at the original context, then an original application translates into a
replacement after the migration whenever two facts hold. First, the actual observation of the original
application equals the actual observation of the replacement, run at the connection and shifted raw index
that the actual run of the migration reaches. Second, the original application has an observation exactly
when some branch of the migration is followed by a replacement branch, at the connection and shifted raw index
of that migration branch, with the same observation. The branches of the migration can reach different
connections. Proof sketch: identity projection leaves the original observations unchanged, and
{name}`afterView_observation_actual` and {name}`afterView_observation_branches` do the same for the
replacement after the migration. -/
theorem translatesAt_of_observations {μ α : Type} (migration : Sql μ) (original replacement : Sql α)
    (state : ExecutionContext) (success : migration.SucceedsFrom state.clock state.index state.connection)
    (actual : (original.runFrom state.clock state.index state.connection).observation =
      (replacement.runFrom state.clock
        (state.index + (migration.runFrom state.clock state.index state.connection).outputs.length)
        (migration.runFrom state.clock state.index state.connection).connection).observation)
    (branches : ∀ observation,
      (∃ result, original.Branch state.clock state.index state.connection result ∧
        result.observation = observation) ↔
      ∃ first, migration.Branch state.clock state.index state.connection first ∧
        ∃ result, replacement.Branch state.clock (state.index + first.outputs.length) first.connection result ∧
          result.observation = observation) :
    (Sql.View.identity original).ObservationEquivAt (afterView migration replacement) state := by
  apply observationProfile_eq_iff.mpr
  constructor
  · rw [afterView_observation_actual migration replacement state success, ← actual]
    simp [Sql.View.observation, Sql.View.project_identity, SqlRun.observation]
  · intro observation
    rw [afterView_observation_branches migration replacement state success, ← branches]
    simp [Sql.View.observation, Sql.View.project_identity, SqlRun.observation]

end Belay.Sqlite.Migration
