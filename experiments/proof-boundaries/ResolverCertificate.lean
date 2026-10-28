import Belay.Sqlite.Model.ResolveStatementFacts
import Belay.Sqlite.Model.ResolveStatementValid
import Belay.Sqlite.Model.Resolution.ResolveStateSpec

set_option doc.verso true

namespace ProofBoundaries
open Belay.Sqlite.Model

/-- Facts about a successful resolution. The state equation is unconditional.
The schema link requires a valid current catalog, at any limits. Validity of
the next state requires execution mode and validity of both starting catalogs. -/
structure ResolverCertificate (context : ResolveContext) (state : ResolveState)
    (resolved : Resolved.Statement) (next : ResolveState) : Prop where
  /-- The resolved statement determines the full next resolver state. -/
  after : next = state.after resolved
  /-- A valid current catalog supplies the resolved statement's schema link. -/
  link : ∀ limits, state.catalog.Valid limits → resolved.SchemaLink state.catalog
  /-- Execution resolution preserves current and saved catalog validity. -/
  valid : context.mode = .execution → state.Valid context.profile.limits →
    next.Valid context.profile.limits

/-- Facts supplied by an ordinary catalog resolver. It returns a non-control
statement and its catalog change. The link and validity facts retain their
different premises; validity alone requires execution mode. -/
structure CatalogCertificate (context : ResolveContext) (catalog : Catalog)
    (resolved : Resolved.Statement) (next : Catalog) : Prop where
  /-- The returned catalog is the resolved catalog change. -/
  after : next = resolved.applyCatalog catalog
  /-- Catalog resolvers return no transaction or setting control. -/
  ordinary : resolved.isControl = false
  /-- A valid starting catalog supplies the schema link. -/
  link : ∀ limits, catalog.Valid limits → resolved.SchemaLink catalog
  /-- In execution mode a valid starting catalog yields a valid next catalog. -/
  valid : context.mode = .execution → catalog.Valid context.profile.limits →
    next.Valid context.profile.limits

/-- Catalog attachment transports all certificate fields and keeps the saved
catalog. Proof sketch: a successful map has one underlying catalog result;
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

/-- Write attachment transports the certificate through rule wrapping and
prepare errors. Proof sketch: its existing case law exposes an unchanged error
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

end ProofBoundaries

#print axioms ProofBoundaries.certificate_withCatalog
#print axioms ProofBoundaries.certificate_withWrite
