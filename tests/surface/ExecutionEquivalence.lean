import ExecutionBranches
import Belay.Sqlite.ExecutionEquivalenceBind
import Belay.Sqlite.ExecutionObservations

set_option doc.verso true
set_option maxRecDepth 4096

namespace ExecutionExamples
open Belay.Sqlite Belay.Sqlite.Model

/-- Only a selected concrete second row executes this suffix; the actual raw wrapper returns. -/
def alternateSuffix (suffix : Script) : Sql Unit := observe.bind fun output =>
  if output == .rows [[2]] then (send suffix).map fun _ => () else .pure ()

/-- One alternative stops at random, while the actual branch returns unit. -/
def failsRandom : Sql Unit := alternateSuffix (sql r"SELECT random()")
/-- The same alternative stops for a distinct unsupported OFFSET. -/
def failsOffset : Sql Unit := alternateSuffix (sql r"SELECT 1 LIMIT 1 OFFSET -1")

/-- The actual raw branch cannot distinguish these programs. -/
theorem same_actual : failsRandom.runFrom daily.clock 0 initial.connection =
    failsOffset.runFrom daily.clock 0 initial.connection := rfl

/-- Both successful-transformer checks reject every postcondition, so they compare equally. -/
theorem same_failed_checks (post : Unit → ExecutionContext → Prop) :
    failsRandom.check post initial ↔ failsOffset.check post initial := by
  have one : ¬ failsRandom.check (fun _ _ => True) initial := by decide +kernel
  have two : ¬ failsOffset.check (fun _ _ => True) initial := by decide +kernel
  exact iff_of_false (fun checked => one (Sql.check_mono checked (fun _ _ _ => True.intro)))
    (fun checked => two (Sql.check_mono checked (fun _ _ _ => True.intro)))

/-- The random alternative's stopped outcome includes its concrete prefix observation. -/
def randomOutcome : SqlRun Unit :=
  let suffix := ((send (sql r"SELECT random()")).map fun _ => ()).runFrom
    daily.clock 1 initial.connection
  { suffix with outputs := .rows [[2]] :: suffix.outputs }

/-- The raw-step relation includes the alternative stopped trace. -/
theorem random_branch : failsRandom.Branch daily.clock 0 initial.connection randomOutcome := by
  exact second_branch.bind_return rfl _ (Sql.Branch.actual _ _ _ _)

/-- The same full outcome is not a branch of the other program: its failure reason differs.
Proof sketch: invert bind and the three LIMIT observations. Only the second concrete row
runs a suffix; its unique stopped outcome has the OFFSET reason rather than the random reason. -/
theorem other_branch_absent : ¬ failsOffset.Branch daily.clock 0 initial.connection randomOutcome := by
  intro branch
  unfold failsOffset alternateSuffix at branch
  obtain ⟨before, first, after⟩ := (Sql.branch_bind_iff _ _ _ _ _ _).mp branch
  unfold observe at first
  cases first with
  | stopped step => contradiction
  | continued step member choice later =>
    have actual : runScriptStep runContext daily.clock 0 initial.connection
        (sql r"SELECT x FROM t LIMIT 1").statements[0].1 [] =
        .continued (.oneOf [[[1]], [[2]]]) initial.connection [] := rfl
    have equal := actual.symm.trans step
    cases equal
    cases Sql.Branch.found_eq step member
    cases later
    simp only [OutputChoice, List.mem_cons, List.not_mem_nil, or_false] at choice
    rcases choice with rfl | ⟨rows, (rfl | rfl), rfl⟩
    all_goals simp [Sql.branch_pure_iff, randomOutcome,
      show (1 : Value) ≠ 2 from by decide, show (2 : Value) ≠ 1 from by decide] at after
    obtain ⟨last, branch, same⟩ := after
    simp only [send, sendStatements, Sql.map] at branch
    have stopped := (Sql.branch_stopped_iff (reason :=
      "a negative literal OFFSET is not modeled; write OFFSET 0 or more, or bind the value to a parameter")
      (by rfl) last).mp branch
    cases stopped
    have different : (((send (sql r"SELECT random()")).map fun _ => ()).runFrom
      daily.clock 1 initial.connection).outputs ≠ [.unmodeled
        "a negative literal OFFSET is not modeled; write OFFSET 0 or more, or bind the value to a parameter"] := by
      decide +kernel
    exact different same.1.1

/-- Actual equality and equal successful transformers still do not imply complete equivalence. -/
theorem failed_traces_distinguish : ¬ failsRandom.EquivAt failsOffset initial := by
  intro same
  apply other_branch_absent
  apply ((observationProfile_id_eq_iff.mp same).2 randomOutcome).mp
  exact random_branch

/-- A deterministic done step followed by pure has one complete branch. -/
private theorem unit_step_branch {statement values clock index connection next}
    (step : runScriptStep runContext clock index connection statement values = .continued (.done 0) next [])
    (result : SqlRun Unit) :
    (Sql.exec statement values (fun _ => .pure ())).Branch clock index connection result ↔
      result = { outputs := [.done 0], connection := next, value := some () } := by
  rw [Sql.branch_continued_iff step _ rfl]
  simp [OutputChoice, Sql.branch_pure_iff]

/-- Set the connection's enforcement flag and return unit, retaining the done output. -/
def foreignOn : Sql Unit :=
  let (statement, values) := (sql r"PRAGMA foreign_keys = ON").statements[0]
  .exec statement values fun _ => .pure ()
/-- Clear the same connection flag; its output and returned value agree with the setting step. -/
def foreignOff : Sql Unit :=
  let (statement, values) := (sql r"PRAGMA foreign_keys = OFF").statements[0]
  .exec statement values fun _ => .pure ()

/-- The named observation comparison discards the differing settings on every branch. -/
theorem same_observations : foreignOn.ObservationEquivAt foreignOff initial := by
  have on (result) : foreignOn.Branch daily.clock 0 initial.connection result ↔
      result = foreignOn.runFrom daily.clock 0 initial.connection := unit_step_branch (by rfl) result
  have off (result) : foreignOff.Branch daily.clock 0 initial.connection result ↔
      result = foreignOff.runFrom daily.clock 0 initial.connection := unit_step_branch (by rfl) result
  apply observationProfile_eq_iff.mpr
  constructor
  · rfl
  · intro observation
    change (∃ result, foreignOn.Branch daily.clock 0 initial.connection result ∧ _) ↔
      (∃ result, foreignOff.Branch daily.clock 0 initial.connection result ∧ _)
    simp only [on, off, exists_eq_left]
    rfl

/-- Full equivalence retains the pragma setting even though all weaker observations agree. -/
theorem settings_distinguish : ¬ foreignOn.EquivAt foreignOff initial := by
  intro same
  have setting := congrArg (fun result : SqlRun Unit => result.connection.foreignKeys) (observationProfile_actual same)
  contradiction

/-- A shared continuation reads the omitted setting, refuting unrestricted weaker bind congruence. -/
theorem observations_do_not_compose :
    ¬ (foreignOn.bind fun _ => single (sql r"PRAGMA foreign_keys")).ObservationEquivAt
      (foreignOff.bind fun _ => single (sql r"PRAGMA foreign_keys")) initial := by
  intro same
  have value := congrArg Prod.fst (observationProfile_actual same)
  have different : ((foreignOn.bind fun _ => single (sql r"PRAGMA foreign_keys")).runFrom
      daily.clock 0 initial.connection).value ≠
      ((foreignOff.bind fun _ => single (sql r"PRAGMA foreign_keys")).runFrom
        daily.clock 0 initial.connection).value := by decide +kernel
  exact different value

#print axioms same_actual
#print axioms same_failed_checks
#print axioms random_branch
#print axioms other_branch_absent
#print axioms failed_traces_distinguish
#print axioms same_observations
#print axioms settings_distinguish
#print axioms observations_do_not_compose
#print axioms Sql.EquivAt.check_iff
#print axioms Sql.Equiv.transformer
#print axioms Sql.EquivAt.andOk_iff
#print axioms Sql.EquivAt.ifOk_iff
#print axioms Sql.Equiv.fresh_iff
#print axioms Sql.Equiv.succeeds_iff
#print axioms Sql.EquivAt.observation
end ExecutionExamples
