import Belay.Sqlite.Model.Schema.Columns.SqlLaws
import Belay.Sqlite.Model.Schema.Rows.DatabaseWriteLaws
import Belay.Sqlite.Model.Schema.Dispatch.Execution

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- There exists a list of trailing column/value pairs whose affinity-applied extension of the before
table equals the after table. This includes equality through an empty extension.
Use it to preserve old cells and physical row identities. -/
def TableExtends (before after : Table) : Prop :=
  ∃ columns, after = before.appendColumns columns

/-- For every catalog position and table present before execution, there exists a
table present after execution that satisfies {name}`TableExtends`. An empty before
database imposes no requirement. New tables are allowed. -/
def DatabaseExtends (before after : Database) : Prop :=
  ∀ position table, before.table position = some table →
    ∃ result, after.table position = some result ∧ TableExtends table result

/-- Every table extends itself, witnessed by an empty list of appended columns. -/
theorem TableExtends.refl (table : Table) : TableExtends table table :=
  ⟨[], table.appendColumns_nil.symm⟩

/-- Whenever a before table extends to a middle table and that middle table
extends to an after table, the before table extends to the after table. The proof
concatenates the extension lists; it assumes nothing about application contracts. -/
theorem TableExtends.trans (first : TableExtends before middle)
    (second : TableExtends middle after) : TableExtends before after := by
  obtain ⟨a, rfl⟩ := first
  obtain ⟨b, rfl⟩ := second
  exact ⟨a ++ b, before.appendColumns_append a b⟩

/-- Every database extends itself: each present table is retained unchanged.
This includes an empty database, where the table premise is always false. -/
theorem DatabaseExtends.refl (database : Database) : DatabaseExtends database database :=
  fun _ table present => ⟨table, present, TableExtends.refl table⟩

/-- If a before database extends to a middle database and the middle extends to
an after database, the before extends to the after. The proof retrieves each
present intermediate table and composes its table extension witnesses. -/
theorem DatabaseExtends.trans (first : DatabaseExtends before middle)
    (second : DatabaseExtends middle after) : DatabaseExtends before after := by
  intro position table present
  obtain ⟨intermediate, present', growth⟩ := first position table present
  obtain ⟨result, present'', growth'⟩ := second position intermediate present'
  exact ⟨result, present'', growth.trans growth'⟩

/-- For every database, name and catalog table, CREATE TABLE ({name}`Catalog.createTable`
with an empty row list appended) extends the database: every table present before is
present and unchanged. No condition is imposed on the new table. -/
theorem DatabaseExtends.create (database : Database) (name : Identifier) (table : CatalogTable) :
    DatabaseExtends database
      { catalog := database.catalog.createTable name table, rows := database.rows ++ [[]] } :=
  fun _ old present => ⟨old, Database.table_createTable name table present, TableExtends.refl old⟩

/-- For every database and object, appending the object to the catalog and an empty row list
extends the database, as CREATE INDEX and CREATE TRIGGER do: every table keeps its position and
is unchanged. Proof sketch: {name}`Database.table_append` keeps each present table at its
position, and {name}`TableExtends.refl` extends it by no columns. -/
theorem DatabaseExtends.append (database : Database) (object : CatalogObject) :
    DatabaseExtends database { catalog := database.catalog ++ [object], rows := database.rows ++ [[]] } :=
  fun _ old present => ⟨old, Database.table_append object present, TableExtends.refl old⟩

/-- For every present table, column and value, {name}`Database.addColumn` at its position
extends the database. Other tables are unchanged. The proof separates the selected
position from the others. -/
theorem DatabaseExtends.add (database : Database) (position : Nat) (table : Table) (column : CatalogColumn)
    (value : Value) (present : database.table position = some table) :
    DatabaseExtends database (database.addColumn position column value) := by
  intro other old oldPresent
  by_cases same : other = position
  · subst other
    have equal : old = table := Option.some.inj (oldPresent.symm.trans present)
    subst old
    exact ⟨table.appendColumns [(column, value)], Database.table_addColumn column value present, ⟨_, rfl⟩⟩
  · exact ⟨old, (Database.table_addColumn_other database column value same).trans oldPresent,
      TableExtends.refl old⟩

/-- For every clock value, counters, list of values, database and statement that is not DROP (its
{name}`Resolved.Statement.kind` is not {name}`Resolved.Statement.Kind.drop`), the database of
the primitive {name}`step` effect ({name}`effectDatabase`) extends the input database. A DROP
removes tables, and a RENAME or a DROP COLUMN changes the names or the shape of tables (its kind is
{name}`Resolved.Statement.Kind.rewrite`), so the theorem says nothing about them. CREATE/ADD extend existing tables or retain
errors; other constructors return an unchanged error. This is a primitive schema
fact, not a preservation law for literal SQL writes. The proof follows the
primitive branches and table-update witnesses. -/
theorem step_extends (clock : Int) (counters : Counters) (parameters : List Value) (statement : Resolved.Statement) (database : Database)
    (kept : statement.kind ≠ .drop) (unrenamed : statement.kind ≠ .rewrite) :
    DatabaseExtends database (effectDatabase (step clock counters parameters statement database)) := by
  cases statement with
  | drop _ _ => exact absurd rfl kept
  | rewrite _ => exact absurd rfl unrenamed
  | dropColumn _ _ _ => exact absurd rfl unrenamed
  | createTable target name table =>
    simp only [step]
    split
    · exact DatabaseExtends.create database name table
    · exact DatabaseExtends.refl database
  | addColumn target column _ =>
    simp only [step]
    cases h : database.table target with
    | none => exact DatabaseExtends.refl database
    | some table =>
      simp only []
      split
      · exact DatabaseExtends.refl database
      split
      · split
        · exact DatabaseExtends.add database target table column .null h
        · exact DatabaseExtends.refl database
      · cases readDefaultValue column with
        | error _ => exact DatabaseExtends.refl database
        | ok value =>
          simp only []
          split
          · exact DatabaseExtends.refl database
          · split
            · exact DatabaseExtends.refl database
            · exact DatabaseExtends.add database target table column value h
  | createIndex target name index =>
    simp only [step]
    split
    · split
      · exact DatabaseExtends.refl database
      · split
        · exact DatabaseExtends.refl database
        · exact DatabaseExtends.append database _
    · exact DatabaseExtends.refl database
  | createView target name view =>
    simp only [step]
    split
    · exact DatabaseExtends.append database _
    · exact DatabaseExtends.refl database
  | createTrigger target name trigger =>
    simp only [step]
    split
    · exact DatabaseExtends.append database _
    · exact DatabaseExtends.refl database
  | query query subqueries =>
    have same : effectDatabase (step clock counters parameters (.query query subqueries) database) = database := by
      simp only [step, queryEffect]
      repeat' split
      all_goals rfl
    rw [same]
    exact DatabaseExtends.refl database
  | begin => exact DatabaseExtends.refl database
  | commit => exact DatabaseExtends.refl database
  | rollback => exact DatabaseExtends.refl database
  | insert => exact DatabaseExtends.refl database
  | upsert => exact DatabaseExtends.refl database
  | insertSelect => exact DatabaseExtends.refl database
  | update => exact DatabaseExtends.refl database
  | delete => exact DatabaseExtends.refl database
  | prepareError _ => exact DatabaseExtends.refl database
  | setting _ => exact DatabaseExtends.refl database

end Belay.Sqlite.Model
