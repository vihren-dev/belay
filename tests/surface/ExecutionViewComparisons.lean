import Belay.Sqlite.ExecutionViewIdentity
import Belay.Sqlite.SqlTerm
import Belay.Sqlite.DbBang

set_option doc.verso true
set_option maxRecDepth 4096

namespace ExecutionViewComparisonExamples
open Belay.Sqlite Belay.Sqlite.Model

/-- The comparison examples start with two rows and known connection counters. -/
def sample : Belay.Sqlite.Database := db! r"CREATE TABLE t(id INTEGER PRIMARY KEY, x INTEGER);
  INSERT INTO t VALUES (1, 1), (2, 2)"

/-- The shared environment gives each actual statement index a different date. -/
def daily : Env :=
  { clock := some (fun index => 212602449600000 + 86400000 * index)
    counters := Counters.newConnection }

/-- An arbitrary earlier error is retained in the comparison's shared prefix. -/
def initial : ExecutionContext :=
  { ExecutionContext.initial sample daily with outputs := [.error 1] }

/-- A single successful query returns an application value independent of its output. -/
def one : Sql Nat :=
  let (statement, values) := (sql r"SELECT 1").statements[0]
  .exec statement values fun _ => .pure 7

/-- The concrete one-step query produces one modeled output and leaves the connection.
Proof sketch: reduce the installed statement interpreter on this valid fixture. -/
theorem one_step :
    let (statement, values) := (sql r"SELECT 1").statements[0]
    runScriptStep runContext initial.clock initial.index initial.connection statement values =
      .continued (.rows [[1]]) initial.connection [] := by rfl

/-- Every branch of the quiet query returns 7 with no projected outputs.
Proof sketch: its single non-alternative step has only the actual output choice. -/
theorem one_observation {result : SqlRun Nat}
    (branch : one.Branch initial.clock initial.index initial.connection result) :
    (Sql.View.quiet one).observation result = (some 7, []) := by
  obtain ⟨selected, later, choice, tail, rfl⟩ := (Sql.branch_continued_iff one_step result).mp branch
  have selected_eq : selected = .rows [[1]] := by simpa [OutputChoice] using choice
  subst selected
  have later_eq := (Sql.branch_pure_iff 7 _ _ _ later).mp tail
  subst later
  rfl

/-- Hiding one successful query makes its weak observations equal to a pure return,
even with a prior error trace. Proof sketch: all branches have the same value and empty
new observation; actual branch membership supplies the converse witness. -/
theorem weak_extra_step :
    (Sql.View.identity (.pure 7 : Sql Nat)).ObservationEquivAt (Sql.View.quiet one) initial := by
  constructor
  · rfl
  · intro observation
    constructor
    · rintro ⟨result, branch, seen⟩
      have eq := (Sql.branch_pure_iff 7 _ _ _ result).mp branch
      subst result
      exact ⟨_, Sql.Branch.actual one _ _ _, (one_observation (Sql.Branch.actual one _ _ _)).trans seen⟩
    · rintro ⟨result, branch, seen⟩
      exact ⟨_, Sql.Branch.pure 7 _ _ _, (one_observation branch).symm.trans seen⟩

/-- The same weak comparison is not full: the hidden query still advances the index.
Proof sketch: equal full actual observations would imply the computed unequal indices. -/
theorem not_full_extra_step :
    ¬ (Sql.View.identity (.pure 7 : Sql Nat)).EquivAt (Sql.View.quiet one) initial := by
  intro same
  have index := congrArg (fun observed => observed.2.index) same.actual
  have impossible : (0 : Nat) = 1 := index
  cases impossible

/-- Ordinary strong equivalence also distinguishes the step whose output was hidden.
Proof sketch: equality of complete actual runs would equate their unequal traces. -/
theorem not_ordinary_extra_step : ¬ (.pure 7 : Sql Nat).EquivAt one initial := by
  intro same
  have outputs := congrArg (fun result => result.outputs.length) same.actual
  have impossible : (0 : Nat) = 1 := outputs
  cases impossible

/-- Identity-view bridges work for arbitrary programs and supplied contexts, retaining
all raw and concrete alternatives. Proof sketch: use both exact public bridges. -/
theorem identity_bridges {α : Type} (first second : Sql α) (state : ExecutionContext) :
    ((Sql.View.identity first).ObservationEquivAt (Sql.View.identity second) state ↔
      first.ObservationEquivAt second state) ∧
    ((Sql.View.identity first).EquivAt (Sql.View.identity second) state ↔ first.EquivAt second state) :=
  ⟨Sql.View.identity_observation_iff first second state, Sql.View.identity_equiv_iff first second state⟩

#print axioms one_step
#print axioms one_observation
#print axioms weak_extra_step
#print axioms not_full_extra_step
#print axioms not_ordinary_extra_step
#print axioms identity_bridges
#print axioms Sql.View.ObservationEquivAt.refl
#print axioms Sql.View.ObservationEquivAt.symm
#print axioms Sql.View.ObservationEquivAt.trans
#print axioms Sql.View.EquivAt.refl
#print axioms Sql.View.EquivAt.symm
#print axioms Sql.View.EquivAt.trans
#print axioms Sql.View.observation_eq_of_full
#print axioms Sql.View.EquivAt.observation
#print axioms Sql.View.identity_full_eq_iff
end ExecutionViewComparisonExamples
