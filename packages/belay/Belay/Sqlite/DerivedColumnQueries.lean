import Belay.Sqlite.DerivedColumnReads

set_option doc.verso true

/-! Reads across a migration that adds a column, backfills it from an expression and registers triggers
(ADR 0017, S6), as migration-pattern claims. The theorems give the claims for every valid database that has
a site: a read that {lit}`Site.LookupMove` moves keeps its result, and a read that {lit}`Site.ReadPreserved` keeps
is preserved. -/

namespace Belay.Sqlite.DerivedColumnMigration
open Belay.Sqlite.Model

/-- For a database with a {name}`Site`, a migration that succeeds, and two statements whose steps have equal
outputs on the original connection and on any connection with the migrated database, the first statement
translates into the second after the migration, when neither statement is written as INSERT from a query
(such a statement has one execution, and so has each statement of the migration). The equal-outputs premise
must hold for every clock index after the migration and gets the table's row facts. The result covers the
actual run and every raw or concrete branch. Proof sketch: success of the sent script gives the model run;
{name}`derivedColumn_state` gives its reached connection; every branch reaches the same connection
({name}`sendStatements_branch_shape`); and equal step outputs give equal observations
({name}`sendStatements_single_observations`, {name}`Migration.translatesAt_of_observations`). -/
theorem translatesAt_of_outputs (tableName : Identifier) (definition : Syntax.ColumnDefinition)
    (value : Syntax.Expr) (addValues updateValues : List Value)
    (triggers : List ((Identifier × CatalogTrigger) × List Value))
    (db : Database) (env : Env) (site : Site db.raw tableName definition value)
    (original replacement : Syntax.Statement) (originalParameters replacementParameters : List Value)
    (originalSingle : original.isInsertSelect = false) (replacementSingle : replacement.isInsertSelect = false)
    (outputs : site.table.RowsWide → site.table.RowsAliased → site.position < db.raw.rows.length →
      ∀ (migrated : Connection) (after : Nat),
        migrated.state.database = site.reached (triggers.map (·.1)) →
        (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) original originalParameters).output =
          (runScriptStep runContext env.clock after migrated replacement replacementParameters).output) :
    Migration.TranslatesAt
      (send (migration tableName definition value addValues updateValues triggers))
      (fun _ => True) (send ⟨[(original, originalParameters)]⟩) (send ⟨[(replacement, replacementParameters)]⟩)
      (ExecutionContext.initial db env) := by
  rintro ⟨_, success⟩
  have wide : site.table.RowsWide := db.valid.admitted.rowsWide site.position site.table site.present
  have aliased : site.table.RowsAliased := db.valid.admitted.rowsAliased site.position site.table site.present
  have aligned : site.position < db.raw.rows.length := by
    rw [db.valid.admitted.rowsShaped.1]; exact Database.table_lt site.present
  have reachedSuccess : (sendStatements (migration tableName definition value addValues updateValues triggers).statements).SucceedsFrom
      env.clock 0 (db.raw.connection env.counters) := success
  have ok : List.allOk (runScriptFrom runContext env.clock 0 (db.raw.connection env.counters)
      (derivedColumnScript tableName definition value addValues updateValues triggers)).outputs = true :=
    Sql.allOk_of_succeedsFrom_send _ _ _ _ reachedSuccess
  obtain ⟨run, hrun⟩ : ∃ run, run = runScriptFrom runContext env.clock 0 (db.raw.connection env.counters)
      (derivedColumnScript tableName definition value addValues updateValues triggers) := ⟨_, rfl⟩
  obtain ⟨counters, hconn, hlength⟩ := site.run_state addValues updateValues triggers
    (connection := db.raw.connection env.counters) (clock := env.clock) (index := 0) rfl wide aliased rfl rfl ok
  rw [← hrun] at hconn
  have uniform : ∀ branch, (send (migration tableName definition value addValues updateValues triggers)).Branch
      env.clock 0 (db.raw.connection env.counters) branch →
      branch.connection = run.connection ∧ branch.outputs.length = run.outputs.length := by
    intro branch reached
    rw [hrun]
    exact sendStatements_branch_shape _ _ _ _ branch
      (ScriptConditionsWith.of_not_insertSelect runContext _ _ _ _
        (migration_noInsertSelect _ _ _ _ _ _)) reached
  have database : run.connection.state.database = site.reached (triggers.map (·.1)) := by
    rw [hconn]
  obtain ⟨actual, branches⟩ := sendStatements_single_observations original replacement originalParameters
    replacementParameters env.clock env.clock 0 (0 + run.outputs.length) (db.raw.connection env.counters)
    run.connection
    (fun _ after found => resolveStatement_single _ _ after original _ originalSingle found)
    (fun _ after found => resolveStatement_single _ _ after replacement _ replacementSingle found)
    (outputs wide aliased aligned run.connection (0 + run.outputs.length) database)
  have actualBranch := Sql.Branch.actual (send (migration tableName definition value addValues updateValues triggers))
    env.clock 0 (db.raw.connection env.counters)
  obtain ⟨sameConnection, sameCount⟩ := uniform _ actualBranch
  refine Migration.translatesAt_of_observations _ _ _ (ExecutionContext.initial db env) success
    (by dsimp only [ExecutionContext.initial]; rw [sameConnection, sameCount]; exact actual)
    fun observation => (branches observation).trans ⟨?_, ?_⟩
  · intro ⟨result, branch, seen⟩
    exact ⟨_, actualBranch, result, by dsimp only [ExecutionContext.initial]; rw [sameConnection, sameCount]; exact branch, seen⟩
  · rintro ⟨first, ran, result, branch, seen⟩
    obtain ⟨oneConnection, oneCount⟩ := uniform _ ran
    exact ⟨result, by dsimp only [ExecutionContext.initial] at branch; rw [oneConnection, oneCount] at branch; exact branch, seen⟩

/-- For every class of valid databases that each give a {name}`Site`, complete environment and read that is
moved by {name}`Site.LookupMove` for the site of the database, if the migration succeeds, then the original statement and the replacement
statement have equal actual values and traces and the same set of branch observations. The statements are
read-only. The class of databases and its site for each database are arguments, so a caller can use a
narrower description of a site than the general one, such as one that names the id and the source column.
Plain words: for every such database and environment, if the
migration succeeds, the read before it gives the same result as the moved read after it. The table, the
column definition, the written expression, the triggers and the values bound to the statements are
arbitrary within the premises of the site. Proof sketch: {name}`translatesAt_of_outputs` with
{name}`Model.derivedColumn_lookup_outputs` for the supplied queries. -/
theorem queryTranslates (tableName : Identifier) (definition : Syntax.ColumnDefinition) (value : Syntax.Expr)
    (addValues updateValues : List Value) (triggers : List ((Identifier × CatalogTrigger) × List Value))
    (original replacement : Syntax.Statement) (parameters : List Value)
    (originalReads : original.readsOnly = true) (replacementReads : replacement.readsOnly = true)
    (originalSingle : original.isInsertSelect = false) (replacementSingle : replacement.isInsertSelect = false)
    (domain : Database → Prop) (siteOf : ∀ db, domain db → Site db.raw tableName definition value)
    (move : ∀ (db : Database) (inside : domain db),
      (siteOf db inside).LookupMove (triggers.map (·.1)) original replacement parameters) :
    Migration.QueryTranslates
      (send (migration tableName definition value addValues updateValues triggers))
      ⟨[(original, parameters)]⟩ ⟨[(replacement, parameters)]⟩ domain
      (by simp [Script.isQuery, originalReads]) (by simp [Script.isQuery, replacementReads]) := by
  intro db inside env _
  have lookup := move db inside
  generalize siteOf db inside = site at lookup
  refine translatesAt_of_outputs tableName definition value addValues updateValues triggers db env site original
    replacement parameters parameters originalSingle replacementSingle fun wide aliased aligned migrated after reached => ?_
  exact lookup.outputs env.clock 0 after rfl aligned reached wide aliased

/-- For every class of valid databases that each give a {name}`Site`, complete environment and read that
{name}`Site.ReadPreserved` keeps for the site of the database, if the migration succeeds, then the read gives the same actual
value and trace and the same set of branch observations after the migration as before it. Proof sketch:
{name}`translatesAt_of_outputs` with {name}`Model.derivedColumn_preserved_outputs`. -/
theorem queryPreserves (tableName : Identifier) (definition : Syntax.ColumnDefinition) (value : Syntax.Expr)
    (addValues updateValues : List Value) (triggers : List ((Identifier × CatalogTrigger) × List Value))
    (statement : Syntax.Statement) (parameters : List Value) (reads : statement.readsOnly = true)
    (single : statement.isInsertSelect = false)
    (domain : Database → Prop) (siteOf : ∀ db, domain db → Site db.raw tableName definition value)
    (kept : ∀ (db : Database) (inside : domain db), (siteOf db inside).ReadPreserved (triggers.map (·.1)) statement) :
    Migration.QueryPreserves
      (send (migration tableName definition value addValues updateValues triggers))
      ⟨[(statement, parameters)]⟩ domain (by simp [Script.isQuery, reads]) := by
  intro db inside env _
  have read := kept db inside
  generalize siteOf db inside = site at read
  refine translatesAt_of_outputs tableName definition value addValues updateValues triggers db env site statement
    statement parameters parameters single single fun wide aliased aligned migrated after reached => ?_
  exact read.outputs parameters env.clock 0 after rfl aligned reached wide aliased

end Belay.Sqlite.DerivedColumnMigration
