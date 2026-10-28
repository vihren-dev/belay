import Belay.Sqlite.Model.ResolverCertificate
import Belay.Sqlite.Model.Resolution.StatementArms
import Belay.Sqlite.Model.Resolution.ApplyCatalogSpec
import Belay.Sqlite.Model.ResolveStatementPragmaLink
import Belay.Sqlite.Model.ResolveCreateViewCatalog

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- Every successful {name}`resolveStatement` gives a {name}`ResolverCertificate`. Its state
equation needs no validity or mode premise; its schema link accepts any valid
current-catalog limits; its next-state validity requires execution mode and
valid current and saved input catalogs at the context profile limits.
For example, the state equation also applies in resolution-only mode. Use the
certificate fields separately when only one guarantee is needed. Proof sketch:
transaction cases copy the appropriate catalogs; ordinary and wrapped writes
use their leaf resolver facts through the two certificate transport laws. -/
theorem resolveStatement_certificate (context : ResolveContext) (state next : ResolveState)
    (statement : Syntax.Statement) (resolved : Resolved.Statement)
    (ok : resolveStatement context state statement = .ok (resolved, next)) :
    ResolverCertificate context state resolved next := by
  cases statement
  all_goals simp only [statement_arms] at ok
  case begin =>
    cases ok
    refine ⟨rfl, fun _ _ => trivial, fun _ valid => ⟨valid.1, ?_⟩⟩
    intro copy h
    cases hsaved : state.saved <;> simp [hsaved] at h <;> subst h
    · exact valid.1
    · exact valid.2 _ hsaved
  case commit => cases ok; exact ⟨rfl, fun _ _ => trivial, fun _ valid => ⟨valid.1, by simp⟩⟩
  case rollback =>
    cases ok
    refine ⟨rfl, fun _ _ => trivial, fun _ valid => ⟨?_, by simp⟩⟩
    cases hsaved : state.saved
    · simpa [hsaved] using valid.1
    · simpa [hsaved] using valid.2 _ hsaved
  case createTable name columns constraints options =>
    apply certificate_withCatalog ok
    intro statement after found
    obtain ⟨equal, control⟩ := resolveCreateTable_applyCatalog _ _ _ _ _ _ _ _ found
    exact ⟨equal, control, fun _ _ => resolveCreateTable_schemaLink _ _ _ _ _ _ _ _ found,
      fun execution valid => resolveCreateTable_valid _ _ _ _ _ _ _ _ valid execution found⟩
  case createView name ifNotExists columns query subqueries =>
    apply certificate_withCatalog ok
    intro statement after found
    obtain ⟨equal, control⟩ := resolveCreateView_applyCatalog _ _ _ _ _ _ found
    exact ⟨equal, control, fun _ _ => resolveCreateView_schemaLink _ _ _ _ _ _ found,
      fun _ valid => resolveCreateView_valid _ _ _ _ _ _ _ valid found⟩
  case createIndex name unique table terms filter =>
    apply certificate_withCatalog ok
    intro statement after found
    obtain ⟨equal, control⟩ := resolveCreateIndex_applyCatalog _ _ _ _ _ _ _ _ _ found
    exact ⟨equal, control, fun _ _ => resolveCreateIndex_schemaLink _ _ _ _ _ _ _ _ _ found,
      fun _ valid => resolveCreateIndex_valid _ _ _ _ _ _ _ _ _ valid found⟩
  case addColumn table column =>
    apply certificate_withCatalog ok
    intro statement after found
    obtain ⟨equal, control⟩ := resolveAddColumn_applyCatalog _ _ _ _ _ _ _ found
    exact ⟨equal, control, fun _ _ => resolveAddColumn_schemaLink _ _ _ _ _ _ _ found,
      fun _ valid => resolveAddColumn_valid _ _ _ _ _ _ _ valid found⟩
  case renameTable table newName =>
    apply certificate_withCatalog ok
    intro statement after found
    have outcome := resolveRenameTable_outcome _ _ _ _ _ _ found
    refine ⟨outcome.applyCatalog.1, outcome.applyCatalog.2, ?_, fun _ valid => outcome.valid valid⟩
    intro limits valid
    rcases outcome with ⟨_, _, rfl⟩ | ⟨rfl, _⟩ <;> trivial
  case renameColumn table column newName columnToken quoted =>
    apply certificate_withCatalog ok
    intro statement after found
    have outcome := resolveRenameColumn_outcome _ _ _ _ _ _ _ _ _ found
    refine ⟨outcome.applyCatalog.1, outcome.applyCatalog.2, ?_, fun _ valid => outcome.valid valid⟩
    intro limits valid
    rcases outcome with ⟨_, _, rfl⟩ | ⟨rfl, _⟩ <;> trivial
  case dropColumn table column columnToken =>
    apply certificate_withCatalog ok
    intro statement after found
    have outcome := resolveDropColumn_outcome _ _ _ _ _ _ _ found
    refine ⟨outcome.applyCatalog.1, outcome.applyCatalog.2, ?_, fun _ valid => outcome.valid valid⟩
    intro limits valid
    rcases outcome with ⟨_, _, rfl⟩ | ⟨_, _, rfl, _⟩ <;> trivial
  case dropTable name ifExists =>
    apply certificate_withWrite ok
    intro statement after found
    obtain ⟨equal, control⟩ := resolveDropTable_applyCatalog _ _ _ _ _ found
    exact ⟨equal, control, fun _ valid => resolveDropTable_schemaLink _ _ _ valid found,
      fun _ valid => resolveDropTable_valid _ _ _ _ _ _ valid found⟩
  case dropView name ifExists =>
    apply certificate_withCatalog ok
    intro statement after found
    obtain ⟨equal, control⟩ := resolveDropView_applyCatalog _ _ _ _ _ found
    exact ⟨equal, control, fun _ valid => resolveDropView_schemaLink _ _ _ valid found,
      fun _ valid => resolveDropView_valid _ _ _ _ _ _ valid found⟩
  case dropIndex name ifExists =>
    apply certificate_withCatalog ok
    intro statement after found
    obtain ⟨equal, control⟩ := resolveDropIndex_applyCatalog _ _ _ _ _ found
    exact ⟨equal, control, fun _ valid => resolveDropIndex_schemaLink _ _ _ valid found,
      fun _ valid => resolveDropIndex_valid _ _ _ _ _ _ valid found⟩
  case createTrigger name ifNotExists time event table condition body =>
    apply certificate_withCatalog ok
    intro statement after found
    obtain ⟨equal, control⟩ := resolveCreateTrigger_applyCatalog _ _ _ _ _ _ found
    exact ⟨equal, control, fun _ _ => resolveCreateTrigger_schemaLink _ _ _ _ _ _ found,
      fun _ valid => resolveCreateTrigger_valid _ _ _ _ _ _ _ valid found⟩
  case dropTrigger name ifExists =>
    apply certificate_withCatalog ok
    intro statement after found
    obtain ⟨equal, control⟩ := resolveDropTrigger_applyCatalog _ _ _ _ _ found
    exact ⟨equal, control, fun _ valid => resolveDropTrigger_schemaLink _ _ _ valid found,
      fun _ valid => resolveDropTrigger_valid _ _ _ _ _ _ valid found⟩
  case insert table columns rows conflicts algorithm returning subqueries =>
    apply certificate_withWrite ok
    intro statement after found
    obtain ⟨same, unchanged, control⟩ := resolveCommonTableWrite_same _ _ _ _ _ _ _ _ _
      (fun _ _ _ _ _ h => resolveInsert_same _ _ _ _ _ _ _ _ _ _ _ _ h) found
    refine ⟨same.trans unchanged.symm, control, ?_, fun _ valid => same ▸ valid⟩
    intro limits valid
    exact resolveCommonTableWrite_schemaLink _ _ _ _ _ _ _ _ _
      (fun _ _ _ _ _ h => resolveInsert_schemaLink _ _ _ _ _ _ _ _ _ _ _ _ h) found
  case insertSelect table columns body conflicts algorithm returning =>
    apply certificate_withWrite ok
    intro statement after found
    obtain ⟨same, unchanged, control⟩ := resolveInsertQuery_same _ _ _ _ _ _ _ _ _ _ found
    refine ⟨same.trans unchanged.symm, control, ?_, fun _ valid => same ▸ valid⟩
    intro limits valid
    obtain ⟨_, ⟨_, rfl⟩ | ⟨_, _, _, _, _, _, _, rfl⟩⟩ := resolveInsertQuery_form _ _ _ _ _ _ _ _ _ _ found <;>
      trivial
  case update table assignments filter returning subqueries =>
    apply certificate_withWrite ok
    intro statement after found
    obtain ⟨same, unchanged, control⟩ := resolveCommonTableWrite_same _ _ _ _ _ _ _ _ _
      (fun _ _ _ _ _ h => resolveUpdate_same _ _ _ _ _ _ _ _ _ _ h) found
    refine ⟨same.trans unchanged.symm, control, ?_, fun _ valid => same ▸ valid⟩
    intro limits valid
    exact resolveCommonTableWrite_schemaLink _ _ _ _ _ _ _ _ _
      (fun _ _ _ _ _ h => resolveUpdate_schemaLink _ _ _ _ _ _ _ _ _ _ h) found
  case delete table filter returning subqueries =>
    apply certificate_withWrite ok
    intro statement after found
    obtain ⟨same, unchanged, control⟩ := resolveCommonTableWrite_same _ _ _ _ _ _ _ _ _
      (fun _ _ _ _ _ h => resolveDelete_same _ _ _ _ _ _ _ _ _ h) found
    refine ⟨same.trans unchanged.symm, control, ?_, fun _ valid => same ▸ valid⟩
    intro limits valid
    exact resolveCommonTableWrite_schemaLink _ _ _ _ _ _ _ _ _
      (fun _ _ _ _ _ h => resolveDelete_schemaLink _ _ _ _ _ _ _ _ _ h) found
  case pragma pragma =>
    have link := resolveStatementPragma_schemaLink ok
    rcases resolveStatementPragma_cases ok with ⟨setting, on, rfl, rfl⟩ | ⟨rfl, unchanged, control⟩
    · exact ⟨rfl, fun _ _ => link, fun _ valid => by cases setting <;> exact valid⟩
    · refine ⟨?_, fun _ _ => link, fun _ valid => valid⟩
      rw [ResolveState.after_of_isControl _ control, unchanged]
  case select results source joins filter groupBy orderBy limit offset subqueries having distinct =>
    apply certificate_withCatalog ok
    intro statement after found
    obtain ⟨same, unchanged, control⟩ := resolveSelect_same _ _ _ _ _ _ found
    exact ⟨same.trans unchanged.symm, control, fun _ _ => resolveSelect_schemaLink _ _ _ _ _ _ found,
      fun _ valid => same ▸ valid⟩

end Belay.Sqlite.Model
