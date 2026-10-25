import Belay.Sqlite.MigrationPattern
import Belay.Sqlite.Queries

set_option doc.verso true

namespace Belay.Sqlite.Migration

/-- Query translation on every valid bundled database satisfying the predicate and
every complete fresh environment, whenever the migration succeeds at that original
context. Both scripts must be single read-only statements. Application output lists
are also their returned values; only the migration's trace segment is quiet.
Failure of the original migration makes that instance vacuous. Use {name}`TranslatesAt`
for arbitrary supplied contexts, programs or a different returned application value. -/
def QueryTranslates {μ : Type} (migration : Sql μ) (original replacement : Script)
    (pre : Database → Prop) (_original : original.isQuery = true := by check_query)
    (_replacement : replacement.isQuery = true := by check_query) : Prop :=
  ∀ db, pre db → ∀ env : Env, env.Complete →
    TranslatesAt migration (fun _ => True) (send original) (send replacement) (ExecutionContext.initial db env)

/-- Preserve this single read-only query on every admitted database and complete
fresh environment where the original migration succeeds. It is the same-query case
of {name}`QueryTranslates`, with the same explicit vacuity outside the success domain. -/
def QueryPreserves {μ : Type} (migration : Sql μ) (query : Script) (pre : Database → Prop)
    (readOnly : query.isQuery = true := by check_query) : Prop :=
  QueryTranslates migration query query pre readOnly readOnly

/-- Full commutation with a replacement on every valid bundled database satisfying
the predicate and every complete fresh environment where the original migration
succeeds. Application return types are arbitrary; both execution orders retain that
value. The supplied-context primitive is {name}`CommutesAsAt`. -/
def CommutesAs {μ α : Type} (migration : Sql μ) (application replacement : Sql α)
    (pre : Database → Prop) : Prop :=
  ∀ db, pre db → ∀ env : Env, env.Complete →
    CommutesAsAt migration (fun _ => True) application replacement (ExecutionContext.initial db env)

/-- Full fresh-context commutation with the same application, for every valid database
in the predicate and complete environment where the migration originally succeeds.
Use {name}`CommutesOn` when intermediate contexts must also be covered. -/
def Commutes {μ α : Type} (migration : Sql μ) (application : Sql α) (pre : Database → Prop) : Prop :=
  CommutesAs migration application application pre

end Belay.Sqlite.Migration
