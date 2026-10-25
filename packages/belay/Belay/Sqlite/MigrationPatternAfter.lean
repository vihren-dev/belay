import Belay.Sqlite.MigrationPatternSuccess
import Belay.Sqlite.MigrationPattern
import Belay.Sqlite.ProgramBindLaws
import Belay.Sqlite.ProgramQueries
import Belay.Sqlite.ExecutionViewBind

set_option doc.verso true

/-! The observations of an application that runs after a successful quiet migration (ADR 0017, S6).
When every branch of the migration reaches one connection with one number of outputs, the observations of
the application after the migration are exactly the observations of the application alone, run at that
reached connection and that shifted raw index. -/

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

/-- If the migration succeeds and all its branches reach one connection with one output count, then
the actual observation of the migration followed by the replacement equals the actual observation of
the replacement alone, run at that connection and shifted raw index. Proof sketch: the actual migration run
is a branch ({name}`Sql.Branch.actual`); {name}`Sql.runFrom_bind` splits the run, and
{name}`afterView_observation_of_branch` removes the quiet prefix. -/
theorem afterView_observation_actual {μ α : Type} (migration : Sql μ) (replacement : Sql α)
    (state : ExecutionContext) (count : Nat) (reached : Connection)
    (success : migration.SucceedsFrom state.clock state.index state.connection)
    (uniform : ∀ branch, migration.Branch state.clock state.index state.connection branch →
      branch.connection = reached ∧ branch.outputs.length = count) :
    (afterView migration replacement).observation
        ((after migration replacement).runFrom state.clock state.index state.connection) =
      (replacement.runFrom state.clock (state.index + count) reached).observation := by
  have actualBranch := Sql.Branch.actual migration state.clock state.index state.connection
  obtain ⟨sameConnection, sameCount⟩ := uniform _ actualBranch
  obtain ⟨returned, ok⟩ := (Sql.succeedsFrom_iff_branches migration _ _ _).mp success _ actualBranch
  obtain ⟨value, hasValue⟩ := Option.isSome_iff_exists.mp returned
  have run := Sql.runFrom_bind migration (fun _ => replacement) state.clock state.index state.connection
  change (afterView migration replacement).observation
    ((migration.bind fun _ => replacement).runFrom state.clock state.index state.connection) = _
  rw [run]
  unfold SqlRun.andThen
  simp only [hasValue, sameConnection, sameCount]
  exact afterView_observation_of_branch migration replacement actualBranch hasValue ok _

/-- Under the premises of {name}`afterView_observation_actual`, the set of observations of branches of the
migration followed by the replacement equals the set of observations of branches of the replacement alone,
run at the reached connection and shifted raw index. This includes every raw and concrete branch of
the migration. Proof sketch: split each bind branch with {name}`Sql.branch_bind_iff`; the uniform premise
fixes the continuation inputs, and {name}`afterView_observation_of_branch` equates the observations. -/
theorem afterView_observation_branches {μ α : Type} (migration : Sql μ) (replacement : Sql α)
    (state : ExecutionContext) (count : Nat) (reached : Connection)
    (success : migration.SucceedsFrom state.clock state.index state.connection)
    (uniform : ∀ branch, migration.Branch state.clock state.index state.connection branch →
      branch.connection = reached ∧ branch.outputs.length = count) (observation : Option α × List Output) :
    (∃ result, (after migration replacement).Branch state.clock state.index state.connection result ∧
        (afterView migration replacement).observation result = observation) ↔
      ∃ result, replacement.Branch state.clock (state.index + count) reached result ∧
        result.observation = observation := by
  have actualBranch := Sql.Branch.actual migration state.clock state.index state.connection
  constructor
  · rintro ⟨result, branch, seen⟩
    have bound : (migration.bind fun _ => replacement).Branch state.clock state.index state.connection result := branch
    obtain ⟨first, before, continuation⟩ := (Sql.branch_bind_iff migration _ _ _ _ result).mp bound
    obtain ⟨sameConnection, sameCount⟩ := uniform first before
    obtain ⟨returned, ok⟩ := (Sql.succeedsFrom_iff_branches migration _ _ _).mp success first before
    obtain ⟨value, hasValue⟩ := Option.isSome_iff_exists.mp returned
    simp only [hasValue] at continuation
    obtain ⟨last, lastBranch, rfl⟩ := continuation
    rw [sameConnection, sameCount] at lastBranch
    exact ⟨last, lastBranch, (afterView_observation_of_branch migration replacement before hasValue ok last).symm.trans seen⟩
  · rintro ⟨last, lastBranch, seen⟩
    obtain ⟨sameConnection, sameCount⟩ := uniform _ actualBranch
    obtain ⟨returned, ok⟩ := (Sql.succeedsFrom_iff_branches migration _ _ _).mp success _ actualBranch
    obtain ⟨value, hasValue⟩ := Option.isSome_iff_exists.mp returned
    refine ⟨_, Sql.Branch.bind_return actualBranch hasValue (fun _ => replacement) (last := last) ?_, ?_⟩
    · rw [sameConnection, sameCount]; exact lastBranch
    · exact (afterView_observation_of_branch migration replacement actualBranch hasValue ok last).trans seen

/-- If the migration succeeds at the original context and all its branches reach one connection with one
output count, then an original application translates into a replacement after the migration whenever the
original application and the replacement, the latter at that reached connection and shifted raw index,
have equal actual observations and equal sets of branch observations. Proof sketch: identity projection
leaves the original observations unchanged, and {name}`afterView_observation_actual` and
{name}`afterView_observation_branches` do the same for the replacement after the migration. -/
theorem translatesAt_of_observations {μ α : Type} (migration : Sql μ) (original replacement : Sql α)
    (state : ExecutionContext) (count : Nat) (reached : Connection)
    (success : migration.SucceedsFrom state.clock state.index state.connection)
    (uniform : ∀ branch, migration.Branch state.clock state.index state.connection branch →
      branch.connection = reached ∧ branch.outputs.length = count)
    (actual : (original.runFrom state.clock state.index state.connection).observation =
      (replacement.runFrom state.clock (state.index + count) reached).observation)
    (branches : ∀ observation,
      (∃ result, original.Branch state.clock state.index state.connection result ∧
        result.observation = observation) ↔
      ∃ result, replacement.Branch state.clock (state.index + count) reached result ∧
        result.observation = observation) :
    (Sql.View.identity original).ObservationEquivAt (afterView migration replacement) state := by
  constructor
  · rw [afterView_observation_actual migration replacement state count reached success uniform, ← actual]
    simp [Sql.View.observation, Sql.View.project_identity, SqlRun.observation]
  · intro observation
    rw [afterView_observation_branches migration replacement state count reached success uniform, ← branches]
    simp [Sql.View.observation, Sql.View.project_identity, SqlRun.observation]

end Belay.Sqlite.Migration
