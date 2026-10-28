import ResolverCertificate

set_option doc.verso true

namespace ProofBoundaries
open Belay.Sqlite.Model

/-- Successful resolution gives all three facts in one syntax dispatch. The
state equation needs no validity premise, the schema link accepts any valid
catalog limits, and state validity requires execution mode. Proof sketch:
transaction cases copy the appropriate catalogs; ordinary and wrapped writes
use their leaf resolver facts through the two certificate transport laws. -/
theorem resolve_certificate (context : ResolveContext) (state next : ResolveState)
    (statement : Syntax.Statement) (resolved : Resolved.Statement)
    (ok : resolveStatement context state statement = .ok (resolved, next)) :
    ResolverCertificate context state resolved next := by
  cases statement with
  | begin =>
    cases ok
    refine ⟨rfl, fun _ _ => trivial, fun _ valid => ⟨valid.1, ?_⟩⟩
    intro copy h
    cases hsaved : state.saved <;> simp [hsaved] at h <;> subst h
    · exact valid.1
    · exact valid.2 _ hsaved
  | commit => cases ok; exact ⟨rfl, fun _ _ => trivial, fun _ valid => ⟨valid.1, by simp⟩⟩
  | rollback =>
    cases ok
    refine ⟨rfl, fun _ _ => trivial, fun _ valid => ⟨?_, by simp⟩⟩
    cases hsaved : state.saved
    · simpa [hsaved] using valid.1
    · simpa [hsaved] using valid.2 _ hsaved
  | createTable name columns constraints options =>
    apply certificate_withCatalog ok
    intro statement after found
    obtain ⟨equal, control⟩ := resolveCreateTable_applyCatalog _ _ _ _ _ _ _ _ found
    exact ⟨equal, control, fun _ _ => resolveCreateTable_schemaLink _ _ _ _ _ _ _ _ found,
      fun execution valid => resolveCreateTable_valid _ _ _ _ _ _ _ _ valid execution found⟩
  | createView name ifNotExists columns query subqueries =>
    apply certificate_withCatalog ok
    intro statement after found
    obtain ⟨equal, control⟩ := resolveCreateView_applyCatalog _ _ _ _ _ _ found
    exact ⟨equal, control, fun _ _ => resolveCreateView_schemaLink _ _ _ _ _ _ found,
      fun _ valid => resolveCreateView_valid _ _ _ _ _ _ _ valid found⟩
  | createIndex name unique table terms filter =>
    apply certificate_withCatalog ok
    intro statement after found
    obtain ⟨equal, control⟩ := resolveCreateIndex_applyCatalog _ _ _ _ _ _ _ _ _ found
    exact ⟨equal, control, fun _ _ => resolveCreateIndex_schemaLink _ _ _ _ _ _ _ _ _ found,
      fun _ valid => resolveCreateIndex_valid _ _ _ _ _ _ _ _ _ valid found⟩
  | addColumn table column =>
    apply certificate_withCatalog ok
    intro statement after found
    obtain ⟨equal, control⟩ := resolveAddColumn_applyCatalog _ _ _ _ _ _ _ found
    exact ⟨equal, control, fun _ _ => resolveAddColumn_schemaLink _ _ _ _ _ _ _ found,
      fun _ valid => resolveAddColumn_valid _ _ _ _ _ _ _ valid found⟩
  | dropTable name ifExists =>
    apply certificate_withWrite ok
    intro statement after found
    obtain ⟨equal, control⟩ := resolveDropTable_applyCatalog _ _ _ _ _ found
    exact ⟨equal, control, fun _ valid => resolveDropTable_schemaLink _ _ _ valid found,
      fun _ valid => resolveDropTable_valid _ _ _ _ _ _ valid found⟩
  | dropView name ifExists =>
    apply certificate_withCatalog ok
    intro statement after found
    obtain ⟨equal, control⟩ := resolveDropView_applyCatalog _ _ _ _ _ found
    exact ⟨equal, control, fun _ valid => resolveDropView_schemaLink _ _ _ valid found,
      fun _ valid => resolveDropView_valid _ _ _ _ _ _ valid found⟩
  | dropIndex name ifExists =>
    apply certificate_withCatalog ok
    intro statement after found
    obtain ⟨equal, control⟩ := resolveDropIndex_applyCatalog _ _ _ _ _ found
    exact ⟨equal, control, fun _ valid => resolveDropIndex_schemaLink _ _ _ valid found,
      fun _ valid => resolveDropIndex_valid _ _ _ _ _ _ valid found⟩
  | createTrigger name ifNotExists time event table condition body =>
    apply certificate_withCatalog ok
    intro statement after found
    obtain ⟨equal, control⟩ := resolveCreateTrigger_applyCatalog _ _ _ _ _ _ found
    exact ⟨equal, control, fun _ _ => resolveCreateTrigger_schemaLink _ _ _ _ _ _ found,
      fun _ valid => resolveCreateTrigger_valid _ _ _ _ _ _ _ valid found⟩
  | dropTrigger name ifExists =>
    apply certificate_withCatalog ok
    intro statement after found
    obtain ⟨equal, control⟩ := resolveDropTrigger_applyCatalog _ _ _ _ _ found
    exact ⟨equal, control, fun _ valid => resolveDropTrigger_schemaLink _ _ _ valid found,
      fun _ valid => resolveDropTrigger_valid _ _ _ _ _ _ valid found⟩
  | insert table columns rows conflicts algorithm returning subqueries =>
    apply certificate_withWrite ok
    intro statement after found
    obtain ⟨same, unchanged, control⟩ := resolveCommonTableWrite_same _ _ _ _ _ _ _ _ _
      (fun _ _ _ _ _ h => resolveInsert_same _ _ _ _ _ _ _ _ _ _ _ _ h) found
    refine ⟨same.trans unchanged.symm, control, ?_, fun _ valid => same ▸ valid⟩
    intro limits valid
    exact resolveCommonTableWrite_schemaLink _ _ _ _ _ _ _ _ _
      (fun _ _ _ _ _ h => resolveInsert_schemaLink _ _ _ _ _ _ _ _ _ _ _ _ h) found
  | update table assignments filter returning subqueries =>
    apply certificate_withWrite ok
    intro statement after found
    obtain ⟨same, unchanged, control⟩ := resolveCommonTableWrite_same _ _ _ _ _ _ _ _ _
      (fun _ _ _ _ _ h => resolveUpdate_same _ _ _ _ _ _ _ _ _ _ h) found
    refine ⟨same.trans unchanged.symm, control, ?_, fun _ valid => same ▸ valid⟩
    intro limits valid
    exact resolveCommonTableWrite_schemaLink _ _ _ _ _ _ _ _ _
      (fun _ _ _ _ _ h => resolveUpdate_schemaLink _ _ _ _ _ _ _ _ _ _ h) found
  | delete table filter returning subqueries =>
    apply certificate_withWrite ok
    intro statement after found
    obtain ⟨same, unchanged, control⟩ := resolveCommonTableWrite_same _ _ _ _ _ _ _ _ _
      (fun _ _ _ _ _ h => resolveDelete_same _ _ _ _ _ _ _ _ _ h) found
    refine ⟨same.trans unchanged.symm, control, ?_, fun _ valid => same ▸ valid⟩
    intro limits valid
    exact resolveCommonTableWrite_schemaLink _ _ _ _ _ _ _ _ _
      (fun _ _ _ _ _ h => resolveDelete_schemaLink _ _ _ _ _ _ _ _ _ h) found
  | pragma pragma =>
    have link := resolveStatementPragma_schemaLink ok
    rcases resolveStatementPragma_cases ok with ⟨setting, on, rfl, rfl⟩ | ⟨rfl, unchanged, control⟩
    · exact ⟨rfl, fun _ _ => link, fun _ valid => by cases setting <;> exact valid⟩
    · refine ⟨?_, fun _ _ => link, fun _ valid => valid⟩
      rw [ResolveState.after_of_isControl _ control, unchanged]
  | select results source joins filter groupBy orderBy limit offset subqueries having distinct compound =>
    apply certificate_withCatalog ok
    intro statement after found
    obtain ⟨same, unchanged, control⟩ := resolveSelect_same _ _ _ _ _ _ found
    exact ⟨same.trans unchanged.symm, control, fun _ _ => resolveSelect_schemaLink _ _ _ _ _ _ found,
      fun _ valid => same ▸ valid⟩

end ProofBoundaries

#print axioms ProofBoundaries.resolve_certificate
