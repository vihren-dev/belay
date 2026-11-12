import Belay.Sqlite.Programs.StatementRunLaws.DerivedColumnSchema
import Belay.Sqlite.Programs.Scripts.ScriptSuccess
import Belay.Sqlite.Model.Programs.StatementRunLaws.DerivedColumnSuccess

set_option doc.verso true

/-! The success of the derived-column migration on the databases of one schema, from a computed check.
The check runs on the catalog of the schema, and the kernel evaluates it, for example with
{lit}`decide +kernel`. The law gives {lit}`Succeeds M (·.HasCatalog schema)`. -/

namespace Belay.Sqlite.DerivedColumnMigration
open Belay.Sqlite.Model

/-- The facts beyond the site that the success law needs, for the site parts of {name}`siteParts`, with
{lit}`column` the new column and {lit}`width` the number of old columns. It is true when all of these hold:

* ADD COLUMN resolves on the catalog to the addition of {lit}`column` at the position;
* {lit}`column` has no {lit}`STRICT` type: a typed column of a {lit}`STRICT` table fails the check, because
  a value of another type makes the UPDATE fail;
* with {lit}`column` added, the UPDATE resolves, and the unique keys of the table do not change;
* every unique key and every check of the table reads only old columns, and the rowid alias is ready
  and is an old column;
* the assigned expression reads only old columns and has no fallible call
  ({name}`Resolved.Expr.isFallibleCall`), and the resolved UPDATE reads neither the clock nor a counter. -/
def successFacts (catalog : Catalog) (tableName : Identifier) (definition : Syntax.ColumnDefinition)
    (value : Syntax.Expr) : Nat × CatalogTable × Resolved.Expr × Option Affinity → Bool
  | (position, shape, derived, _) =>
    let column := definedColumn shape.strict definition
    let width := shape.columns.length
    let assigned := assignedExpression (backfillScope position tableName shape column) width value derived
    let update := Resolved.Statement.update position [(width, assigned)] none [] [] none
    (match resolveStatement runContext { catalog } (.addColumn tableName definition) with
      | .ok (resolved, _) => decide (resolved = .addColumn position column false)
      | .error _ => false) &&
    (match resolveStatement runContext { catalog := catalog.addColumn position column }
        (.update tableName [(definition.name, value)] none [] []) with
      | .ok _ => true
      | .error _ => false) &&
    column.strictType.isNone &&
    decide ((catalog.addColumn position column).uniqueKeys position
      { shape with columns := shape.columns ++ [column] } = catalog.uniqueKeys position shape) &&
    (catalog.uniqueKeys position shape).all (·.readsBelow width) &&
    shape.allChecks.all (·.condition.readsBelow width) &&
    LiteralData.aliasReady shape && shape.rowidAlias.all (· < width) &&
    assigned.readsBelow width && !assigned.any Resolved.Expr.isFallibleCall &&
    !update.readsClock && update.counterReads.isEmpty

/-- Whether the derived-column migration succeeds on every database with the catalog of the schema, by a
check that the kernel can evaluate. It is true when {name}`migrationParts` gives the parts of the migration,
{name}`siteParts` gives the site parts on the catalog of the schema, and both {name}`siteFacts` and
{name}`successFacts` hold for them. It is a sufficient condition: when it is false, the migration can
still succeed. -/
def succeedsCheck (schema : Database) (migration : Script) : Bool :=
  match migrationParts migration with
  | some (tableName, definition, value, _, _) =>
    match siteParts schema.raw.catalog tableName definition value with
    | some parts => siteFacts schema.raw.catalog tableName definition value parts &&
        successFacts schema.raw.catalog tableName definition value parts
    | none => false
  | none => false

/-- For every schema and migration that pass {name}`succeedsCheck`, the migration succeeds on every
database with the catalog of the schema: for each such database and complete environment, its run has no
output that is an error or that ends the run. For example, with the schema {lit}`shop` and the migration
{lit}`addEmailLower` of the page for agents, the proof is {lit}`succeeds_of_check (by decide +kernel)`.
Proof sketch: the check gives the parts of the migration and the site of each database
({name}`Site.ofCheck`); the validity of the database gives the facts of the rows of the table, and the
computed facts give the rest of the premises of {name}`derivedColumn_script_ok`. -/
theorem succeeds_of_check {schema : Database} {migration : Script}
    (checked : succeedsCheck schema migration = true) :
    Succeeds migration (fun db => db.HasCatalog schema) := by
  unfold succeedsCheck at checked
  split at checked
  · rename_i tableName definition value addValues updateValues parts
    obtain rfl := migrationParts_some parts
    split at checked
    · rename_i sp foundParts
      obtain ⟨position, shape, derived, affinity⟩ := sp
      rw [Succeeds.script_iff _ _ (migration_noInsertSelect _ _ _ _ _ _)]
      intro db inside env _
      have same : db.raw.catalog = schema.raw.catalog := inside
      rw [← same] at foundParts checked
      obtain ⟨found, operand⟩ := siteParts_some foundParts
      simp only [siteFacts, successFacts, Bool.and_eq_true, Bool.not_eq_true', Option.isNone_iff_eq_none,
        List.isEmpty_iff, decide_eq_true_eq, List.all_eq_true] at checked
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, fresh⟩, -⟩, -⟩, -⟩, plain⟩, noneFiring⟩, ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨addMatch, updateMatch⟩, loose⟩,
        keysSame⟩, keysBelow⟩, checksBelow⟩, alias⟩, aliasBelow⟩, assignedBelow⟩, safe⟩, free⟩, noCounters⟩⟩ := checked
      have present := db.raw.table_of_findTable tableName position shape found
      have addResolves : ∃ after, resolveStatement runContext (db.raw.connection env.counters).resolveState
          (.addColumn tableName definition) = .ok (.addColumn position (definedColumn shape.strict definition) false,
            after) := by
        change ∃ after, resolveStatement runContext { catalog := db.raw.catalog } _ = _
        split at addMatch
        · rename_i resolved after resolvedEq
          rw [decide_eq_true_eq] at addMatch
          exact ⟨after, by rw [resolvedEq, addMatch]⟩
        · cases addMatch
      have updateResolves : ∃ resolution, resolveStatement runContext
          { (db.raw.connection env.counters).resolveState with
            catalog := db.raw.catalog.addColumn position (definedColumn shape.strict definition) }
          (.update tableName [(definition.name, value)] none [] []) = .ok resolution := by
        split at updateMatch
        · rename_i resolution resolvedEq
          exact ⟨resolution, resolvedEq⟩
        · cases updateMatch
      have unique := db.valid.unique position _ present
      rw [Script.run_outputs]
      exact derivedColumn_script_ok { shape, rows := db.raw.rows.getD position [] } addValues updateValues found present addResolves loose fresh operand
        updateResolves noneFiring rfl rfl (Database.Admitted.table db.valid.admitted present)
        (db.valid.notNull _ _ present) (db.valid.typesFit _ _ present) (db.valid.check _ _ present)
        (by rw [Database.keys]; exact keysSame ▸ unique) checksBelow
        (by rw [Database.keys]; exact keysSame ▸ keysBelow)
        plain alias aliasBelow assignedBelow safe free noCounters
    · cases checked
  · cases checked

end Belay.Sqlite.DerivedColumnMigration
