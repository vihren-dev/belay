import Belay

/-! Recover the original schema-checker claims using the identity comparison. -/

namespace Belay.Sqlite.DerivedColumnMigration
open Belay.Sqlite.Model

/-- The original checker for one read follows by comparing the statement with itself. -/
theorem original_preserves_of_check {schema : Database} {migration query : Script}
    (checked : preservesCheck schema migration (query.statements.map Prod.fst) = true) :
    Migration.QueryPreserves (Runnable.toSql migration) query (fun db => db.HasCatalog schema)
      (isQuery_of_preservesCheck checked) :=
  preserves_of_check id (by simpa using checked) (isQuery_of_preservesCheck checked)

/-- The original checker for a family follows by using each statement as its own reference. -/
theorem original_preserves_of_check_forall {α : Type} {schema : Database} {migration : Script} (query : α → Script)
    (sample : α)
    (sameStatements : ∀ index, (query index).statements.map Prod.fst = (query sample).statements.map Prod.fst)
    (checked : preservesCheck schema migration ((query sample).statements.map Prod.fst) = true) :
    ∀ index, Migration.QueryPreserves (Runnable.toSql migration) (query index)
      (fun db => db.HasCatalog schema) (isQuery_of_preservesCheck (by rw [sameStatements index]; exact checked)) :=
  preserves_of_check_forall query sample id sameStatements (by simpa using checked)
    (fun index => isQuery_of_preservesCheck (by rw [sameStatements index]; exact checked))

#print axioms original_preserves_of_check
#print axioms original_preserves_of_check_forall

end Belay.Sqlite.DerivedColumnMigration
