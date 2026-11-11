import Belay
import ApplicationRestrictedDomain

/-! A fixture module of `tests/surface_application_test.py`: the bridge from weak query translation to
simulation (ADR 0017, S8). Under a clock that gives one date at every statement index, the constant read
translates weakly at every admitted context, meets the frame facts of
{name}`Belay.Sqlite.Migration.QueryFrames`, and the bridge {name}`Belay.Sqlite.Simulation.ofQueries`
gives a full-state simulation over the migration that stores the clock. The application with two reads
then commutes with the migration at every admitted context, which it does not under a changing clock. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

namespace ApplicationConstantClockFixture
open Belay.Sqlite Belay.Sqlite.Calls ApplicationRestrictedDomainFixture
open Belay.Sqlite.Model hiding Database

/-- A clock with one date at every statement index. -/
def still : Env :=
  { clock := some (fun _ => 212602449600000), counters := Counters.newConnection }

/-- The start of a run under the clock with one date. -/
def startStill : ExecutionContext := ExecutionContext.initial sample still

/-- The admitted contexts: the clock and the connection of the start, at any statement index and with
any earlier outputs. -/
def admittedStill (state : ExecutionContext) : Prop :=
  state.clock = startStill.clock ∧ state.connection = startStill.connection

/-- The clock of the start gives one date at every statement index. Proof sketch: the clock of the start
is the constant function. -/
theorem still_clock_constant :
    ∀ assignment ∈ startStill.clock, ∀ one other, assignment one = assignment other := by
  intro assignment member one other
  have same : (fun _ => (212602449600000 : Int)) = assignment := by
    simpa [startStill, ExecutionContext.initial, still] using member
  subst same
  rfl

/-- At an admitted context, a program runs as it runs at the start. Proof sketch: the admitted context
has the clock and the connection of the start, and the clock is constant
({name}`Sql.runFrom_index`). -/
theorem admitted_run {α : Type} (program : Sql α) {state : ExecutionContext} (admitted : admittedStill state) :
    program.runFrom state.clock state.index state.connection =
      program.runFrom startStill.clock 0 startStill.connection := by
  rw [admitted.1, admitted.2]
  exact Sql.runFrom_index program _ still_clock_constant _ _ _

/-- At an admitted context, a program has one branch when it has one branch at the start. Proof sketch:
as {name}`admitted_run`, with {name}`Sql.hasOneBranch_index`. -/
theorem admitted_one_branch {α : Type} (program : Sql α) {state : ExecutionContext}
    (admitted : admittedStill state) (one : program.hasOneBranch startStill.clock 0 startStill.connection = true) :
    program.hasOneBranch state.clock state.index state.connection = true := by
  rw [admitted.1, admitted.2, Sql.hasOneBranch_index _ _ still_clock_constant state.index 0]
  exact one

/-- The read translates weakly at every admitted context under the clock with one date. Proof sketch:
at an admitted context, both programs have one branch and run as at the start, where the kernel
evaluates them. -/
theorem still_translates :
    Migration.TranslatesOn clockWrite admittedStill (readPairing.old.run () ()) (readPairing.new.run () ()) := by
  intro state domain
  apply Sql.View.ObservationEquivAt.of_one_branch
  · exact admitted_one_branch _ domain.1 (by decide +kernel)
  · exact admitted_one_branch _ domain.1 (by decide +kernel)
  · show _ = _
    rw [admitted_run _ domain.1, admitted_run _ domain.1]
    rfl

/-- The read of the pairing. -/
def readQuery : Sql Nat := readPairing.old.run () ()

/-- A program with one branch from the start has only its actual run as a branch from any index, under
the clock with one date. Proof sketch: {name}`Sql.hasOneBranch_index`, {name}`Sql.branch_iff_actual` and
{name}`Sql.runFrom_index`. -/
theorem still_branch {α : Type} (program : Sql α) (connection : Connection) (index : Nat)
    (one : program.hasOneBranch startStill.clock 0 connection = true) (result : SqlRun α) :
    program.Branch startStill.clock index connection result ↔
      result = program.runFrom startStill.clock 0 connection := by
  rw [Sql.branch_iff_actual _ _ _ _ _
      ((Sql.hasOneBranch_index _ _ still_clock_constant index 0 connection).trans one),
    Sql.runFrom_index _ _ still_clock_constant index 0 connection]

/-- The read meets the frame facts of {name}`Migration.QueryFrames` at every admitted context: it keeps
the connection, it has one output, it leaves the admitted contexts, and the same holds for the read
after the migration. Proof sketch: the branches of the read and of the migration are their actual runs
({name}`still_branch`), and the kernel evaluates the facts about those runs. -/
theorem still_frames : Migration.QueryFrames clockWrite admittedStill readQuery readQuery := by
  have migrationOne : clockWrite.hasOneBranch startStill.clock 0 startStill.connection = true := by
    decide +kernel
  have queryOne : readQuery.hasOneBranch startStill.clock 0 startStill.connection = true := by
    decide +kernel
  have queryKeeps :
      (readQuery.runFrom startStill.clock 0 startStill.connection).connection = startStill.connection ∧
      (readQuery.runFrom startStill.clock 0 startStill.connection).value.isSome = true :=
    ⟨by rfl, by decide +kernel⟩
  have afterOne : readQuery.hasOneBranch startStill.clock 0
      (clockWrite.runFrom startStill.clock 0 startStill.connection).connection = true := by decide +kernel
  have afterKeeps :
      (readQuery.runFrom startStill.clock 0
        (clockWrite.runFrom startStill.clock 0 startStill.connection).connection).connection =
        (clockWrite.runFrom startStill.clock 0 startStill.connection).connection ∧
      (readQuery.runFrom startStill.clock 0
        (clockWrite.runFrom startStill.clock 0 startStill.connection).connection).value.isSome = true :=
    ⟨by rfl, by decide +kernel⟩
  have counts : (readQuery.runFrom startStill.clock 0 startStill.connection).outputs.length =
      (readQuery.runFrom startStill.clock 0
        (clockWrite.runFrom startStill.clock 0 startStill.connection).connection).outputs.length := by
    decide +kernel
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro state domain first branch
    obtain ⟨hc, hk⟩ := domain.1
    rw [hc, hk, still_branch _ _ _ queryOne] at branch
    rw [hk, branch]
    exact queryKeeps
  · intro state domain ran ranBranch last lastBranch
    obtain ⟨hc, hk⟩ := domain.1
    rw [hc, hk, still_branch _ _ _ migrationOne] at ranBranch
    subst ranBranch
    rw [hc, still_branch _ _ _ afterOne] at lastBranch
    subst lastBranch
    exact afterKeeps
  · intro state domain first ran last firstBranch ranBranch lastBranch
    obtain ⟨hc, hk⟩ := domain.1
    rw [hc, hk, still_branch _ _ _ queryOne] at firstBranch
    rw [hc, hk, still_branch _ _ _ migrationOne] at ranBranch
    subst firstBranch ranBranch
    rw [hc, still_branch _ _ _ afterOne] at lastBranch
    subst lastBranch
    exact counts
  · intro state domain first branch
    obtain ⟨hc, hk⟩ := domain.1
    rw [hc, hk, still_branch _ _ _ queryOne] at branch
    subst branch
    exact ⟨hc, queryKeeps.1⟩

/-- Under the clock with one date, the read pairing is a full-state simulation over the admitted
contexts. Proof sketch: {name}`Simulation.ofQueries` with the weak translation
({name}`still_translates`), the frame facts ({name}`still_frames`), the constant clock, and the one
branch of the migration, whose branches therefore end at one connection with one count of outputs. -/
theorem still_simulation : Simulation clockWrite admittedStill readPairing := by
  have migrationOne : clockWrite.hasOneBranch startStill.clock 0 startStill.connection = true := by
    decide +kernel
  refine Simulation.ofQueries (fun _ _ => still_translates) (fun _ _ => still_frames)
    (fun state admitted => ?_) (fun state domain one other oneBranch otherBranch => ?_)
  · rw [admitted.1]; exact still_clock_constant
  · obtain ⟨hc, hk⟩ := domain.1
    rw [hc, hk, still_branch _ _ _ migrationOne] at oneBranch otherBranch
    subst oneBranch otherBranch
    exact ⟨rfl, rfl⟩

/-- The application with two reads commutes with the migration at every admitted context, which it does
not under the changing clock ({name}`ApplicationRestrictedDomainFixture.two_reads_do_not_commute`). Proof
sketch: {name}`Simulation.commutes_application` with {name}`still_simulation`. -/
theorem two_reads_commute_under_the_constant_clock :
    Migration.CommutesAsOn clockWrite admittedStill (twoReads.interp readPairing.old)
      (twoReads.interp readPairing.new) :=
  Simulation.commutes_application still_simulation twoReads

#print axioms still_translates
#print axioms still_frames
#print axioms still_simulation
#print axioms two_reads_commute_under_the_constant_clock

end ApplicationConstantClockFixture
