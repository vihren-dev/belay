import Belay.Sqlite.Programs.StatementRunLaws.DerivedColumnQueries
import Belay.Sqlite.Schema.Columns.DerivedColumnReadCheck

set_option doc.verso true

/-! Reads across the derived-column migration on the databases of one schema, from a computed check.
The migration and the reads are scripts as {lit}`sql` text gives them; the check takes their statements,
and the kernel evaluates it on the catalog of the schema, for example with {lit}`decide +kernel`. The
laws give {lit}`M preserves Q on schema` from the check. They build the {lit}`Site` with
{lit}`Site.ofCheck` and the {lit}`Site.ReadPreserved` with {lit}`Site.ReadPreserved.ofCheck`, which are
also public, and apply {lit}`queryPreserves`. -/

namespace Belay.Sqlite.DerivedColumnMigration
open Belay.Sqlite.Model

/-- The parts of a derived-column migration without triggers, from its statements: the table name, the
column definition, the written value and the values bound to the two statements. The script must have
exactly two statements, {lit}`ALTER TABLE t ADD COLUMN c …` and {lit}`UPDATE t SET c = value`, with no
filter, RETURNING clause or subquery. None for any other script. -/
def migrationParts (script : Script) :
    Option (Identifier × Syntax.ColumnDefinition × Syntax.Expr × List Value × List Value) :=
  match script.statements with
  | [(.addColumn tableName definition, addValues), (.update updated [(name, value)] none [] [], updateValues)] =>
    if updated = tableName ∧ name = definition.name then some (tableName, definition, value, addValues, updateValues)
    else none
  | _ => none

/-- For every script whose parts {name}`migrationParts` gives, the script is the {name}`migration` of the
parts without triggers. Proof sketch: unfold the match; the two statements are the statements of the
migration. -/
theorem migrationParts_some {script : Script} {tableName : Identifier} {definition : Syntax.ColumnDefinition}
    {value : Syntax.Expr} {addValues updateValues : List Value}
    (parts : migrationParts script = some (tableName, definition, value, addValues, updateValues)) :
    script = migration tableName definition value addValues updateValues [] := by
  obtain ⟨statements⟩ := script
  unfold migrationParts at parts
  split at parts
  · rename_i same
    split at parts
    · rename_i names
      obtain ⟨rfl, rfl⟩ := names
      cases parts
      simp only at same
      simp [same, migration, derivedColumnScript]
    · cases parts
  · cases parts

/-- Whether the derived-column migration keeps the read on every database with the catalog of the
schema, by a check that the kernel can evaluate. It is true when all of these hold:

* {name}`migrationParts` gives the parts of the migration;
* the read has one statement, which reads only and is no INSERT from a query;
* the catalog of the schema passes {name}`siteFacts` for the parts ({name}`siteCheck`);
* the statement passes {name}`readCheck` at the table of the site.

The check reads the statements of the read only, not the values bound to them. It is a sufficient
condition: when it is false, the read can still be preserved, and a proof with a hand-built
{name}`Site` and {name}`Site.ReadPreserved` and {name}`queryPreserves` stays possible. -/
def preservesCheck (schema : Database) (migration : Script) (statements : List Syntax.Statement) : Bool :=
  match migrationParts migration, statements with
  | some (tableName, definition, value, _, _), [statement] =>
    statement.readsOnly && !statement.isInsertSelect &&
      match siteParts schema.raw.catalog tableName definition value with
      | some (position, shape, derived, affinity) =>
        siteFacts schema.raw.catalog tableName definition value (position, shape, derived, affinity) &&
          readCheck schema.raw.catalog position shape.columns.length (definedColumn shape.strict definition) statement
      | none => false
  | _, _ => false

/-- For every schema, migration and read that pass {name}`preservesCheck`, the read is a query: it has one
statement, which reads only. Proof sketch: the check requires both. -/
theorem isQuery_of_preservesCheck {schema : Database} {migration query : Script}
    (checked : preservesCheck schema migration (query.statements.map Prod.fst) = true) : query.isQuery = true := by
  obtain ⟨statements⟩ := query
  unfold preservesCheck at checked
  split at checked
  · rename_i statement _ listed
    rcases statements with _ | ⟨⟨statement', parameters⟩, _ | ⟨_, _⟩⟩ <;>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, reduceCtorEq, and_false] at listed
    subst statement'
    simp only [Bool.and_eq_true] at checked
    exact checked.1.1
  · cases checked

/-- For every schema, migration and read, if {name}`preservesCheck` holds for the statements of the
read, the migration preserves the read on every database with the catalog of the schema
({lit}`M preserves Q on schema`): on each such database and complete environment where the migration
succeeds, the read gives the same actual value and trace and the same set of branch observations after the
migration as before it. For example, with the schema {lit}`shop`, the migration {lit}`addEmailLower` and
the read {lit}`namedCustomers` of the page for agents, the proof is
{lit}`preserves_of_check (by decide +kernel)`. Use {lit}`preserves_of_check_forall` for a read with a
value of a Lean variable. Proof sketch: the check gives the parts of the migration and the statement of the
read; {name}`Site.ofCheck` and {name}`Site.ReadPreserved.ofCheck` give the facts for each database of the
schema, whose catalog is the catalog of the schema; {name}`queryPreserves` gives the claim. -/
theorem preserves_of_check {schema : Database} {migration query : Script}
    (checked : preservesCheck schema migration (query.statements.map Prod.fst) = true) :
    Migration.QueryPreserves (Runnable.toSql migration) query (fun db => db.HasCatalog schema)
      (isQuery_of_preservesCheck checked) := by
  obtain ⟨statements⟩ := query
  unfold preservesCheck at checked
  split at checked
  · rename_i tableName definition value addValues updateValues statement parts listed
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at checked
    obtain ⟨⟨reads, single⟩, rest⟩ := checked
    obtain rfl := migrationParts_some parts
    rcases statements with _ | ⟨⟨statement', parameters⟩, _ | ⟨_, _⟩⟩ <;>
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true, reduceCtorEq, and_false] at listed
    subst statement'
    split at rest
    · rename_i position shape derived affinity found
      simp only [Bool.and_eq_true] at rest
      have siteChecked : siteCheck schema.raw.catalog tableName definition value = true := by
        simp [siteCheck, found, rest.1]
      refine queryPreserves tableName definition value addValues updateValues [] statement parameters reads single
        (fun db => db.HasCatalog schema) (fun db inside => Site.ofCheck inside siteChecked)
        (fun db inside => Site.ReadPreserved.ofCheck _ ?_)
      have same := Site.ofCheck_parts (database := db.raw) inside siteChecked
      rw [found] at same
      simp only [Option.some.injEq, Prod.mk.injEq] at same
      obtain ⟨atPosition, atShape, -, -⟩ := same
      show readCheck db.raw.catalog _ _ (definedColumn (Site.ofCheck inside siteChecked).table.shape.strict definition)
        statement = true
      rw [← atPosition, ← atShape, show db.raw.catalog = schema.raw.catalog from inside]
      exact rest.2
    · cases rest
  · cases checked

/-- For every schema, migration, family of reads with the same statements at every index, and sample
index: if {name}`preservesCheck` holds for the statements of the read at the sample index, then at every
index the migration preserves the read on every database with the catalog of the schema. The values bound
to the read can depend on the index, for example a lookup for every email:
{lit}`preserves_of_check_forall customerIdByEmail .null (fun _ => rfl) (by decide +kernel)`. The kernel
evaluates the check at the sample, so the goal of {lit}`decide` has no free variable. Proof sketch:
{name}`preserves_of_check` at each index, with the statements of the sample. -/
theorem preserves_of_check_forall {α : Type} {schema : Database} {migration : Script} (query : α → Script)
    (sample : α) (sameStatements : ∀ index, (query index).statements.map Prod.fst = (query sample).statements.map Prod.fst)
    (checked : preservesCheck schema migration ((query sample).statements.map Prod.fst) = true) :
    ∀ index, Migration.QueryPreserves (Runnable.toSql migration) (query index)
      (fun db => db.HasCatalog schema) (isQuery_of_preservesCheck (by rw [sameStatements index]; exact checked)) :=
  fun index => preserves_of_check (by rw [sameStatements index]; exact checked)

end Belay.Sqlite.DerivedColumnMigration
