import Belay.Sqlite.Model.Schema.Ddl.StatementArms
import Belay.Sqlite.Model.Schema.Dispatch.StatementArms
import Belay.Sqlite.Model.Schema.Ddl.ScriptLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every catalog, trigger name and trigger: a resolution of CREATE TRIGGER without IF NOT EXISTS
gives a prepare error with the catalog unchanged, or the creation of exactly the written trigger at the
end of the catalog with the catalog that holds it. No body executes in either case. Proof sketch: split
the preparation checks of the resolver. -/
theorem createTrigger_resolution_cases {catalog next : Catalog} {name : Identifier}
    {trigger : CatalogTrigger} {resolved : Resolved.Statement}
    (ok : resolveCreateTrigger catalog name false trigger = .ok (resolved, next)) :
    (∃ error, resolved = .prepareError error ∧ next = catalog) ∨
      (resolved = .createTrigger catalog.length name trigger ∧ next = catalog.createTrigger name trigger) := by
  unfold resolveCreateTrigger at ok
  simp only [prepareError, Bool.false_eq_true, ↓reduceIte] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact .inl ⟨_, rfl, rfl⟩)
    | (cases ok; exact .inr ⟨rfl, rfl⟩)
    | cases ok

end Belay.Sqlite.Model
