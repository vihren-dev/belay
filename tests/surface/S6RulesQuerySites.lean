import S6RulesQueryPattern
import S6ColumnLookups

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048

/-! A fixture module of {lit}`tests/surface_s6_rules_test.py`: the guide's migration query claim for every database of
a site (ADR 0017, S6). {lit}`S6RulesQueryPattern` proves that the lookup {lit}`SELECT id FROM items WHERE name = ?1`
is preserved by the lowercase-field migration for one database. This module proves the claim for every valid
database that has the table {lit}`items` with an id column, a name column and no column {lit}`name_lower`, for
every value bound to the parameter, and in every complete environment where the migration succeeds. The proof
applies the general derived-column laws ({lit}`DerivedColumnMigration.queryPreserves`) to the site of
{lit}`LowercaseSite`; the claim of {lit}`S6RulesQueryPattern` is an instance. -/

namespace S6RulesQuerySites
open Belay.Sqlite Belay.Sqlite.Model Belay.Sqlite.Model.Resolved LowercaseFixture

/-- The guide's lookup statement is the lookup of {name}`columnLookup` over the table {lit}`items`. Proof sketch:
both sides are the same syntax. -/
theorem lookupStatement_is_column_lookup :
    S6RulesQueryPattern.lookupStatement =
      columnLookup (tableReference (name! "items") none) (name! "id") (name! "name") "id" 1 := by
  rfl

/-- The guide's lookup script sends that statement with the bound value. -/
theorem lookup_is_column_lookup (name : Value) :
    S6RulesQueryPattern.lookup name = ⟨[(columnLookup (tableReference (name! "items") none) (name! "id")
      (name! "name") "id" 1, [name])]⟩ := by
  have statements := S6RulesQueryPattern.lookup_statements name
  rw [lookupStatement_is_column_lookup] at statements
  cases same : S6RulesQueryPattern.lookup name
  rw [same] at statements
  simp only at statements
  rw [statements]

/-- The guide's migration is the general derived-column migration of the table {lit}`items`: a TEXT field
{lit}`name_lower` filled with the lowercase of {lit}`name`, without triggers and without bound values. -/
theorem expansion_is_migration :
    S6RulesQueryPattern.expansion =
      DerivedColumnMigration.migration (name! "items") (textDefinition (name! "name_lower"))
        (lowerCall (name! "name")) [] [] [] := by
  rfl

/-- The databases of the claim: valid databases with a table {lit}`items` that has an id column, a name
column and no column {lit}`name_lower`, with plain columns, key positions inside the columns, and no trigger that
fires for an UPDATE of the new column. Other tables, indexes, triggers and rows are unrestricted. -/
abbrev ItemsSite (db : Belay.Sqlite.Database) : Prop :=
  Nonempty (LowercaseSite db.raw (name! "items") (name! "id") (name! "name") (name! "name_lower"))

/-- For every bound value, every valid database that has the site {name}`ItemsSite` and every complete
environment: if the guide's migration succeeds on the database, then the lookup of the ids of the items with a
given name gives the same actual value and trace and the same set of branch observations after the migration
as before it. Plain words: adding the lowercase field and filling it never changes what the name lookup
returns, whatever the other columns, rows and objects of the database are and whatever type and collation the
name column has. Proof sketch: the general {name}`DerivedColumnMigration.queryPreserves` with the site
{name}`LowercaseSite.toSite` and the read {name}`columnPreserved`; the guide's script and lookup are the
general ones ({name}`expansion_is_migration`, {name}`lookup_is_column_lookup`). -/
theorem lookup_preserved_at_every_site (name : Value) :
    Migration.QueryPreserves (send S6RulesQueryPattern.expansion) (S6RulesQueryPattern.lookup name) ItemsSite
      (by simp [Script.isQuery, lookup_is_column_lookup, columnLookup, Syntax.Statement.readsOnly]) := by
  have general := DerivedColumnMigration.queryPreserves (name! "items") (textDefinition (name! "name_lower"))
    (lowerCall (name! "name")) [] [] []
    (columnLookup (tableReference (name! "items") none) (name! "id") (name! "name") "id" 1) [name]
    (by simp [columnLookup, Syntax.Statement.readsOnly]) (by simp [columnLookup, Syntax.Statement.isInsertSelect])
    ItemsSite (fun _ inside => (Classical.choice inside).toSite)
    (fun _ inside => columnPreserved (Classical.choice inside) none "id" 1 _)
  have transport : ∀ (query other : Script) (same : query = other) (queryReads : query.isQuery = true)
      (otherReads : other.isQuery = true),
      Migration.QueryPreserves (send (DerivedColumnMigration.migration (name! "items")
        (textDefinition (name! "name_lower")) (lowerCall (name! "name")) [] [] [])) query ItemsSite queryReads →
      Migration.QueryPreserves (send (DerivedColumnMigration.migration (name! "items")
        (textDefinition (name! "name_lower")) (lowerCall (name! "name")) [] [] [])) other ItemsSite otherReads := by
    intro query other same _ _ preserved
    subst same
    exact preserved
  rw [expansion_is_migration]
  exact transport _ _ (lookup_is_column_lookup name).symm _ _ general

/-- The one-item database of {lit}`S6RulesQueryPattern` has the site: its table is found by name at position 0,
the id is column 0, the name is column 1, no column is named {lit}`name_lower`, and no trigger exists. Proof
sketch: each field is a closed fact about the parsed database, checked by kernel evaluation. -/
theorem sample_has_site : ItemsSite S6RulesQueryPattern.sample :=
  ⟨{ position := 0, table := (S6RulesQueryPattern.sample.raw.table 0).get (by decide +kernel), id := 0, source := 1
     found := by decide +kernel
     present := (Option.some_get _).symm
     fresh := by decide +kernel
     idFound := by decide +kernel
     sourceFound := by decide +kernel
     keysInside := by decide +kernel
     plain := by decide +kernel
     noneFiring := by decide +kernel }⟩

/-- The claim of {lit}`S6RulesQueryPattern` for the one-item database is the instance of
{name}`lookup_preserved_at_every_site` at its site and its environment. Proof sketch: the environment is
complete (every field holds a value), and the preserved claim at the initial context is the claim for the
database in that environment. -/
theorem lookup_preserved_is_instance (name : Value) :
    Migration.PreservesAt (send S6RulesQueryPattern.expansion) (fun _ => True) (send (S6RulesQueryPattern.lookup name))
      S6RulesQueryPattern.initial :=
  lookup_preserved_at_every_site name S6RulesQueryPattern.sample sample_has_site S6RulesQueryPattern.environment
    ⟨rfl, rfl, rfl, rfl⟩

#print axioms resolve_column_filter_at
#print axioms resolve_column_lookup
#print axioms columnPreserved
#print axioms lookup_preserved_at_every_site
#print axioms sample_has_site
#print axioms lookup_preserved_is_instance

end S6RulesQuerySites
