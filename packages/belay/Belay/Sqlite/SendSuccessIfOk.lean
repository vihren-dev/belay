import Belay.Sqlite.DerivedColumnMigration

set_option doc.verso true

/-! Fresh-run claims about sent scripts that succeed (ADR 0017, S6). When a script succeeds from the start
of a fresh run, every raw or concrete branch of the sent program reaches the connection of the model run, so
a claim about the final database needs only the database of that run. A migration that adds a derived column has an
exact reached database. -/

namespace Belay.Sqlite
open Belay.Sqlite Model

/-- For every database, environment, list of statements and post: if sending the statements succeeds from
the start of a fresh run, and the post holds in every final context that sees the connection of the model
run and a valid database, then the fresh run keeps the post whenever the trace has no error. The statements
are none of them written as INSERT from a query, so each has one execution. Proof sketch:
success gives a value and an error-free trace to every branch ({name}`Sql.succeedsFrom_iff_branches`);
{name}`sendStatements_branch_shape` gives the connection of the branch; the database of the run is valid
({name}`Script.run_database_valid`). -/
theorem Sql.ifOk_send_of_success (db : Database) (env : Env) (statements : List (Syntax.Statement × List Value))
    (single : ∀ entry ∈ statements, entry.1.isInsertSelect = false)
    (success : (sendStatements statements).SucceedsFrom env.clock 0 (db.raw.connection env.counters))
    {post : List Output → ExecutionContext → Prop}
    (reached : ∀ (outputs : List Output) (final : ExecutionContext),
      final.connection = (runScriptFrom runContext env.clock 0 (db.raw.connection env.counters) statements).connection →
      final.connection.state.database.Valid Profile.pinned → post outputs final) :
    (send ⟨statements⟩).ifOk post (ExecutionContext.initial db env) := by
  intro branch isBranch
  obtain ⟨returned, _⟩ := (Sql.succeedsFrom_iff_branches _ _ _ _).1 success branch isBranch
  cases value : branch.value with
  | none => simp [value] at returned
  | some outputs =>
    intro _allOk
    obtain ⟨sameConnection, -⟩ := sendStatements_branch_shape statements _ _ _ branch
      (ScriptConditionsWith.of_not_insertSelect runContext _ _ _ _ single) isBranch
    have valid := Script.run_database_valid ⟨statements⟩ db env
    refine reached outputs _ sameConnection ?_
    rw [show ((ExecutionContext.initial db env).finish branch).connection = branch.connection from rfl, sameConnection]
    exact valid

end Belay.Sqlite

namespace Belay.Sqlite.DerivedColumnMigration
open Belay.Sqlite.Model

/-- For every database with a {name}`Site`, environment, migration that succeeds from the start of a fresh
run, and post: the post holds whenever the trace has no error, if it holds in every final context that
sees the database {name}`Site.reached` and a valid one. The failures of ADD COLUMN, the backfill and the
trigger names are excluded by the success premise. Proof sketch: {name}`Sql.ifOk_send_of_success`, with the
connection of the run read from {name}`Model.derivedColumn_state`. -/
theorem ifOk_send_derivedColumn (tableName : Identifier) (definition : Syntax.ColumnDefinition)
    (value : Syntax.Expr) (addValues updateValues : List Value)
    (triggers : List ((Identifier × CatalogTrigger) × List Value))
    (db : Database) (env : Env) (site : Site db.raw tableName definition value)
    (success : (send (migration tableName definition value addValues updateValues triggers)).SucceedsFrom
      env.clock 0 (db.raw.connection env.counters))
    {post : List Output → ExecutionContext → Prop}
    (reached : ∀ (outputs : List Output) (final : ExecutionContext),
      final.connection.state.database = site.reached (triggers.map (·.1)) →
      final.connection.state.database.Valid Profile.pinned → post outputs final) :
    (send (migration tableName definition value addValues updateValues triggers)).ifOk post
      (ExecutionContext.initial db env) := by
  have wide : site.table.RowsWide := db.valid.admitted.rowsWide site.position site.table site.present
  have aliased : site.table.RowsAliased := db.valid.admitted.rowsAliased site.position site.table site.present
  have ok := Sql.allOk_of_succeedsFrom_send _ _ _ _ success
  obtain ⟨counters, hconn, -⟩ := derivedColumn_state (context := runContext) (clock := env.clock) (index := 0)
    (connection := db.raw.connection env.counters) (tableName := tableName) (definition := definition)
    (value := value) site.table addValues updateValues triggers site.found site.present site.constraintFree
    site.admitted site.fresh site.operand site.below site.contextFree wide aliased site.plain rfl rfl
    site.noneFiring ok
  refine Sql.ifOk_send_of_success db env _
    (migration_noInsertSelect _ _ _ _ _ _) success fun outputs final sameConnection valid => ?_
  refine reached outputs final ?_ valid
  rw [sameConnection]
  exact congrArg (fun connection : Connection => connection.state.database) hconn

end Belay.Sqlite.DerivedColumnMigration
