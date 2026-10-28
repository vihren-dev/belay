import Belay.Sqlite.Model.Resolution.ResolveStateSpec
import Belay.Sqlite.Model.ResolveStatementLink

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Facts about a successful {name}`resolveStatement` resolution. The state equation is unconditional.
The schema link requires a valid current catalog, at any limits. Validity of
the next state requires execution mode and validity of both starting catalogs.
For example, {lean}`Resolved.Statement.rollback` restores the saved catalog.
Use the individual fields when only one guarantee is needed. -/
structure ResolverCertificate (context : ResolveContext) (state : ResolveState)
    (resolved : Resolved.Statement) (next : ResolveState) : Prop where
  /-- {name}`ResolveState.after` determines the full next resolver state. -/
  after : next = state.after resolved
  /-- For any limits, {name}`Catalog.Valid` of the current catalog supplies {name}`Resolved.Statement.SchemaLink`. -/
  link : ∀ limits, state.catalog.Valid limits → resolved.SchemaLink state.catalog
  /-- Execution mode and {name}`ResolveState.Valid` of the input imply validity of the next state. -/
  valid : context.mode = .execution → state.Valid context.profile.limits →
    next.Valid context.profile.limits

/-- Facts supplied by an ordinary catalog resolver. It returns a non-control
statement and its catalog change. For a statement already attached to a state,
use {name}`ResolverCertificate`.
The link and validity facts retain their
different premises; validity alone requires execution mode. -/
structure CatalogCertificate (context : ResolveContext) (catalog : Catalog)
    (resolved : Resolved.Statement) (next : Catalog) : Prop where
  /-- The returned catalog equals {name}`Resolved.Statement.applyCatalog` on the input. -/
  after : next = resolved.applyCatalog catalog
  /-- {name}`Resolved.Statement.isControl` is false for this statement. -/
  ordinary : resolved.isControl = false
  /-- For any limits, {name}`Catalog.Valid` of the input supplies {name}`Resolved.Statement.SchemaLink`. -/
  link : ∀ limits, catalog.Valid limits → resolved.SchemaLink catalog
  /-- Execution mode and {name}`Catalog.Valid` at the context limits imply validity of the next catalog. -/
  valid : context.mode = .execution → catalog.Valid context.profile.limits →
    next.Valid context.profile.limits

/-- For each successful {name}`ResolveState.withCatalog` result, certificates for
its underlying catalog result give a {name}`ResolverCertificate` and keep the saved catalog. Proof sketch: a successful map has one underlying catalog result;
its non-control equation identifies the complete next state. -/
theorem certificate_withCatalog {context : ResolveContext} {state next : ResolveState}
    {resolved : Resolved.Statement} {result : StatementResolution}
    (ok : state.withCatalog result = .ok (resolved, next))
    (each : ∀ statement after, result = .ok (statement, after) →
      CatalogCertificate context state.catalog statement after) :
    ResolverCertificate context state resolved next := by
  rcases result with _ | ⟨statement, after⟩
  · cases ok
  · simp only [ResolveState.withCatalog, Except.map, Except.ok.injEq, Prod.mk.injEq] at ok
    obtain ⟨rfl, rfl⟩ := ok
    have facts := each _ _ rfl
    refine ⟨?_, facts.link, fun execution valid => ⟨facts.valid execution valid.1, valid.2⟩⟩
    rw [state.after_of_isControl facts.ordinary, facts.after]

/-- For each successful {name}`ResolveState.withWrite` result, certificates for
its underlying catalog result give a {name}`ResolverCertificate`, including rule wrapping
and prepare errors. Proof sketch: its existing case law exposes an unchanged error
state or an attached catalog. Rule wrapping keeps the catalog action and kind;
the schema-link transport accounts for the rules separately. -/
theorem certificate_withWrite {context : ResolveContext} {state next : ResolveState}
    {resolved : Resolved.Statement} {result : StatementResolution}
    (ok : state.withWrite context result = .ok (resolved, next))
    (each : ∀ statement after, result = .ok (statement, after) →
      CatalogCertificate context state.catalog statement after) :
    ResolverCertificate context state resolved next := by
  have link : ∀ limits, state.catalog.Valid limits → resolved.SchemaLink state.catalog :=
    fun limits valid => ResolveState.withWrite_schemaLink ok
      (fun statement after found => (each statement after found).link limits valid)
  rcases ResolveState.withWrite_cases ok with
    ⟨error, rfl, rfl⟩ | ⟨statement, after, found, rfl, catalog, kind⟩
  · exact ⟨rfl, link, fun _ valid => valid⟩
  · have facts := each statement after found
    have ordinary : resolved.isControl = false := by
      simpa only [Resolved.Statement.isControl, kind] using facts.ordinary
    refine ⟨?_, link, fun execution valid => ⟨facts.valid execution valid.1, valid.2⟩⟩
    rw [state.after_of_isControl ordinary, catalog, facts.after]

end Belay.Sqlite.Model
