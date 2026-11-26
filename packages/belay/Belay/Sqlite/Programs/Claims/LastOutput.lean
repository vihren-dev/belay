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

/-- At a fresh connection, if both sends establish the same final output on every
branch, their last-output profiles agree. Proof sketch: each actual run is a branch,
so both profiles contain exactly the supplied output. -/
theorem Script.lastOutputProfile_eq_of_check (a b : Script) (db : Database) (env : Env) (out : Output)
    (left : (send a).check (fun _ final => final.outputs.getLast? = some out) (ExecutionContext.initial db env))
    (right : (send b).check (fun _ final => final.outputs.getLast? = some out) (ExecutionContext.initial db env)) :
    a.lastOutputProfile (ExecutionContext.initial db env) = b.lastOutputProfile (ExecutionContext.initial db env) := by
  let s := ExecutionContext.initial db env
  have every (p : Script) (h : (send p).check (fun _ final => final.outputs.getLast? = some out) s)
      (run : SqlRun (List Output)) (branch : (send p).Branch s.clock s.index s.connection run) :
      run.outputs.getLast? = some out := by
    have h' := h _ branch
    cases val : run.value <;> simp [val, s, ExecutionContext.finish, ExecutionContext.initial] at h' <;> exact h'
  have actual (p : Script) := Sql.Branch.actual (send p) s.clock s.index s.connection
  apply observationProfile_eq_iff.mpr
  refine ⟨(every a left _ (actual a)).trans (every b right _ (actual b)).symm, ?_⟩
  intro o
  constructor
  · rintro ⟨run, branch, rfl⟩
    exact ⟨_, actual b, (every b right _ (actual b)).trans (every a left run branch).symm⟩
  · rintro ⟨run, branch, rfl⟩
    exact ⟨_, actual a, (every a left _ (actual a)).trans (every b right run branch).symm⟩

end Belay.Sqlite
