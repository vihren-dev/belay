import Belay

set_option doc.verso true

/-! Observable checks of individual schema sends on variable catalogs and row stores. -/

namespace SchemaSendClaims
open Belay.Sqlite Model

/-- On any valid connection with the given resolution, the view is present at the end of the catalog and the step reports zero changes.
Proof sketch: the resolution selects the kind rule and its data checks determine the outcome. -/
theorem createView_send (ctx : ExecutionContext) (stmt : Syntax.Statement) (after : ResolveState)
    (pos : Nat) (name : Identifier) (view : CatalogView)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.createView pos name view, after)) :
    (send ⟨[(stmt, [])]⟩).check (fun outputs final => outputs = [.done 0] ∧
      final.connection.state.database = ctx.connection.state.database.appendView name view) ctx := by
  sql_run [found]
  all_goals exact ⟨trivial, rfl⟩

#print axioms createView_send

/-- On any valid connection with the given resolution, the catalog gains the trigger and the step reports zero changes.
Proof sketch: the resolution selects the kind rule and its data checks determine the outcome. -/
theorem createTrigger_send (ctx : ExecutionContext) (stmt : Syntax.Statement) (after : ResolveState)
    (pos : Nat) (name : Identifier) (trigger : CatalogTrigger)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.createTrigger pos name trigger, after)) :
    (send ⟨[(stmt, [])]⟩).check (fun outputs final => outputs = [.done 0] ∧
      final.connection.state.database = ctx.connection.state.database.appendTrigger name trigger) ctx := by
  sql_run [found]
  all_goals exact ⟨trivial, rfl⟩

#print axioms createTrigger_send

/-- On any valid connection with the given resolution, the step removes exactly the resolved positions and reports zero changes.
Proof sketch: the resolution selects the kind rule and its data checks determine the outcome. -/
theorem dropPlain_send (ctx : ExecutionContext) (stmt : Syntax.Statement) (after : ResolveState)
    (positions : List Nat)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.drop positions none, after)) :
    (send ⟨[(stmt, [])]⟩).check (fun outputs final => outputs = [.done 0] ∧
      final.connection.state.database = ctx.connection.state.database.drop positions) ctx := by
  sql_run [found]
  all_goals exact ⟨trivial, rfl⟩

#print axioms dropPlain_send

/-- On any valid connection with the given resolution, the renamed catalog has the original row stores.
Proof sketch: the resolution selects the kind rule and its data checks determine the outcome. -/
theorem rewrite_send (ctx : ExecutionContext) (stmt : Syntax.Statement) (after : ResolveState)
    (renamed : Catalog)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.rewrite renamed, after)) :
    (send ⟨[(stmt, [])]⟩).check (fun outputs final => outputs = [.done 0] ∧
      final.connection.state.database = { ctx.connection.state.database with catalog := renamed }) ctx := by
  sql_run [found]
  all_goals exact ⟨trivial, rfl⟩

#print axioms rewrite_send

/-- On any valid connection with the given resolution, the catalog and rows have the column removed and the step reports zero changes.
Proof sketch: the resolution selects the kind rule and its data checks determine the outcome. -/
theorem dropColumn_send (ctx : ExecutionContext) (stmt : Syntax.Statement) (after : ResolveState)
    (pos col : Nat) (stored : Catalog)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.dropColumn pos col stored, after)) :
    (send ⟨[(stmt, [])]⟩).check (fun outputs final => outputs = [.done 0] ∧
      final.connection.state.database = ctx.connection.state.database.dropColumn pos col stored) ctx := by
  sql_run [found]
  all_goals exact ⟨trivial, rfl⟩

#print axioms dropColumn_send

/-- On any valid connection with the given resolution, a refused preparation reports its error code and keeps the whole connection.
Proof sketch: the resolution selects the kind rule and its data checks determine the outcome. -/
theorem prepareError_send (ctx : ExecutionContext) (stmt : Syntax.Statement) (after : ResolveState)
    (reason : PrepareError)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.prepareError reason, after)) :
    (send ⟨[(stmt, [])]⟩).check (fun outputs final => outputs = [.error (ExecutionError.prepare reason).primaryCode] ∧
      final.connection = ctx.connection) ctx := by
  sql_run [found]
  all_goals exact ⟨trivial, rfl⟩

#print axioms prepareError_send

/-- On any valid connection with the given resolution, a unique index over duplicate keys reports a constraint violation and keeps the connection.
Proof sketch: the resolution selects the kind rule and its data checks determine the outcome. -/
theorem createIndex_send (ctx : ExecutionContext) (stmt : Syntax.Statement) (after : ResolveState)
    (pos : Nat) (name : Identifier) (idx : CatalogIndex) (table : Table)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.createIndex pos name idx, after))
    (present : ctx.connection.state.database.table idx.table = some table)
    (unique : idx.unique = true) (duplicates : LiteralData.uniqueRows idx.uniqueKey table.rows = false) :
    (send ⟨[(stmt, [])]⟩).check (fun outputs final => outputs = [.error 19] ∧
      final.connection = ctx.connection) ctx := by
  obtain ⟨atEnd, aligned, _⟩ := step_guards_hold found rfl valid.1
  refine Sql.check_send_of_rule (runScriptStep_createIndex_eq found) valid ?_ ?_
  · simp [atEnd, aligned, present, unique, duplicates, RunStep.continues]
  · simp only [atEnd, aligned, present, unique, duplicates, Bool.not_false, Bool.and_self, ite_true, and_self]
    exact Sql.sendReached_single (by intro _ same; cases same) (fun _ => ⟨rfl, rfl⟩)

#print axioms createIndex_send

/-- On any valid connection with the given resolution, a restricted reference default on a populated table reports an error and keeps the connection.
Proof sketch: the resolution selects the kind rule and its data checks determine the outcome. -/
theorem addColumn_send (ctx : ExecutionContext) (stmt : Syntax.Statement) (after : ResolveState)
    (pos : Nat) (column : CatalogColumn) (table : Table)
    (valid : ctx.connection.state.Holds (Model.Database.Valid Profile.pinned))
    (found : resolveStatement runContext ctx.connection.resolveState stmt = .ok (.addColumn pos column true, after))
    (present : ctx.connection.state.database.table pos = some table)
    (timed : column.clockDefault = true) (populated : table.rows.isEmpty = false) :
    (send ⟨[(stmt, [])]⟩).check (fun outputs final => outputs = [.error ExecutionError.referenceColumnDefault.primaryCode] ∧
      final.connection = ctx.connection) ctx := by
  refine Sql.check_send_of_rule (runScriptStep_addColumn_eq found) valid ?_ ?_
  · simp [timed, present, populated, RunStep.continues]
  · simp only [timed, present, populated, Bool.true_or, Bool.not_false, Bool.and_self, ite_true]
    exact Sql.sendReached_single (by intro _ same; cases same) (fun _ => ⟨rfl, rfl⟩)

#print axioms addColumn_send

end SchemaSendClaims
