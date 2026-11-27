import Belay.Sqlite.Programs.Reasoning.ExecutionObservations
import Belay.Sqlite.Programs.Reasoning.ExecutionWPLaws

set_option doc.verso true

/-! Compare the last outputs of two SQL scripts through their execution branches. -/

namespace Belay.Sqlite

/-- The last output of the actual execution of {name}`send` and the predicate of last
outputs permitted by its execution branches. An empty script produces {lean}`(none : Option Output)`.
Only outputs produced by the script contribute to the profile. -/
def Script.lastOutputProfile (s : Script) (start : ExecutionContext) :
    Option Output × (Option Output → Prop) :=
  observationProfile ((send s).runFrom start.clock start.index start.connection)
    ((send s).Branch start.clock start.index start.connection)
    (fun run => run.outputs.getLast?)

/-- For every database with the given catalog and every complete environment,
the two scripts have equal actual last outputs and permit the same last outputs
from the same fresh connection. Equality compares the entire final output, including
row order, error codes and stopping reasons. Earlier errors can precede another output.
Use {name}`Script.lastOutputProfile` to compare scripts at a supplied context. -/
def Script.SameLastOn (a b : Script) (catalog : Database) : Prop :=
  ∀ db : Database, db.HasCatalog catalog → ∀ env : Env, env.Complete →
    a.lastOutputProfile (ExecutionContext.initial db env) = b.lastOutputProfile (ExecutionContext.initial db env)

namespace LastOutput

/-- Compare the last outputs of two sequences of scripts on all databases with one catalog.
For example, {lit}`deleteScript; bigScript ~ referenceScript on shop` runs the DELETE before
the query. Use {name}`Script.SameLastOn` directly for already composed scripts. -/
scoped syntax:20 (name := sameLastSyntax) term:21 (";" term:21)* " ~ " term:21 (";" term:21)* " on " term:21 : term
macro_rules
  | `($a:term $[; $left:term]* ~ $b:term $[; $right:term]* on $schema:term) => do
    let l ← left.foldlM (fun x y => `($x ++ $y)) a
    let r ← right.foldlM (fun x y => `($x ++ $y)) b
    `(Script.SameLastOn $l $r $schema)

end LastOutput

/-- A last-output plan maps a starting database and environment to an actual last output
and a predicate describing all permitted last outputs. Use {lean}`(none : Option Output)` for
an execution that produces no output. -/
abbrev LastOutputPlan := Database → Env → Option Output × (Option Output → Prop)

/-- For every database with the given catalog and every complete environment, the plan
gives exactly the actual and permitted last outputs of the script at the fresh connection. -/
def LastOutputPlan.Correct (plan : LastOutputPlan) (script : Script) (catalog : Database) : Prop :=
  ∀ db : Database, db.HasCatalog catalog → ∀ env : Env, env.Complete →
    script.lastOutputProfile (.initial db env) = plan db env

/-- Given correct plans for both scripts on one catalog, the scripts have the same last
outputs exactly when their plans agree on every admitted start. Proof sketch: substitute
the two certificates at the same database and environment in each direction. -/
theorem LastOutputPlan.sameLastOn_iff {p q : LastOutputPlan} {a b : Script} {catalog : Database}
    (left : p.Correct a catalog) (right : q.Correct b catalog) :
    a.SameLastOn b catalog ↔ ∀ db : Database, db.HasCatalog catalog → ∀ env : Env, env.Complete →
      p db env = q db env := by
  unfold Script.SameLastOn
  constructor <;> intro same db schema env complete
  · rw [← left db schema env complete, ← right db schema env complete]
    exact same db schema env complete
  · rw [left db schema env complete, right db schema env complete]
    exact same db schema env complete

/-- If every branch of a send from a fresh connection ends with the given output, its
profile has that actual output and permits precisely that output. Proof sketch: the actual
run is one branch. Every witness of a permitted output therefore gives the same value. -/
theorem Script.lastOutputProfile_of_check (p : Script) (db : Database) (env : Env) (out : Output)
    (h : (send p).check (fun _ final => final.outputs.getLast? = some out) (.initial db env)) :
    p.lastOutputProfile (.initial db env) = (some out, fun o => some out = o) := by
  let s := ExecutionContext.initial db env
  have every (run : SqlRun (List Output)) (branch : (send p).Branch s.clock s.index s.connection run) :
      run.outputs.getLast? = some out := by
    have h' := h _ branch
    cases val : run.value <;> simp [val, ExecutionContext.finish, ExecutionContext.initial] at h' <;> exact h'
  have actual := Sql.Branch.actual (send p) s.clock s.index s.connection
  exact Prod.ext (every _ actual) (funext fun o => propext
    ⟨fun ⟨run, branch, eq⟩ => (every run branch).symm.trans eq,
     fun eq => ⟨_, actual, (every _ actual).trans eq⟩⟩)

/-- At a fresh connection, if both sends establish the same final output on every
branch, their last-output profiles agree. Proof sketch: each actual run is a branch,
so both profiles contain exactly the supplied output. -/
theorem Script.lastOutputProfile_eq_of_check (a b : Script) (db : Database) (env : Env) (out : Output)
    (left : (send a).check (fun _ final => final.outputs.getLast? = some out) (ExecutionContext.initial db env))
    (right : (send b).check (fun _ final => final.outputs.getLast? = some out) (ExecutionContext.initial db env)) :
    a.lastOutputProfile (ExecutionContext.initial db env) = b.lastOutputProfile (ExecutionContext.initial db env) := by
  exact (a.lastOutputProfile_of_check db env out left).trans (b.lastOutputProfile_of_check db env out right).symm

end Belay.Sqlite
