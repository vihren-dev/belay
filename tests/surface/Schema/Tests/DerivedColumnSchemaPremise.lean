import Belay

set_option doc.verso true

/-! A fixture module of {lit}`tests/surface_derived_column_test.py`: the derived-column law with a schema as the
premise of the claim. The migration adds the column {lit}`email_lower` to {lit}`customers` and fills it with
{lit}`lower(email)`. The claims are about every database with the catalog of the schema {lit}`shop`, which is the
premise that a project with a schema file states. The module shows the three answers of the check as theorems:
the read with {lit}`SELECT *` changes ({lit}`star_read_changes`), and the read with named columns and the lookup
by email keep their results ({lit}`named_read_preserved`, {lit}`lookup_read_preserved`). The last two come from
{lit}`DerivedColumnMigration.queryPreserves`. The law needs the migration and the reads as syntax, a site of the
migration for each database of the premise ({lit}`siteOf`) and a description of each read ({lit}`namedKept`,
{lit}`lookupKept`). The proofs of the facts move from the catalog of the database to the catalog of {lit}`shop`
with the premise, and the kernel decides the rest on that closed catalog. -/

namespace DerivedColumnSchemaPremise
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- The schema of the premise: customers and their sessions. -/
def shop : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  CREATE TABLE sessions (id INTEGER PRIMARY KEY,
    customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
    expires_at INTEGER NOT NULL);"

/-- The migration: add the column {lit}`email_lower` to {lit}`customers` and fill it with {lit}`lower(email)`. -/
def addEmailLower : Script := sql r"
  ALTER TABLE customers ADD COLUMN email_lower TEXT;
  UPDATE customers SET email_lower = lower(email);"

/-- The read of all customers with {lit}`SELECT *`. -/
def allCustomers : Script := sql r"SELECT * FROM customers"

/-- The read of all customers with named columns. -/
def namedCustomers : Script := sql r"SELECT id, name, email FROM customers"

/-- The lookup of a customer id by email, with the email as its parameter. -/
def customerIdByEmail (email : Value) : Script :=
  sql r"SELECT id FROM customers WHERE email = ?1" email

/-- The database of the counterexample of {lit}`#sql_check`: one customer with an empty email. -/
def found : Database := db! r"
CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
INSERT INTO customers (id, name, email) VALUES (1, NULL, '');
CREATE TABLE sessions (id INTEGER PRIMARY KEY,
  customer_id INTEGER NOT NULL REFERENCES customers(id) ON DELETE CASCADE,
  expires_at INTEGER NOT NULL);"

/-- The migration changes the result of {lit}`SELECT * FROM customers`: each row gets one cell more. -/
theorem star_read_changes :
    ¬ Migration.QueryPreserves (send addEmailLower) allCustomers (·.HasCatalog shop) := by
  sql_refute (db := found)

/-- On the database of the counterexample, the read with named columns gives the same rows before and
after the migration. -/
theorem named_read_kept_on_found :
    (found.run namedCustomers).outputs = ((found.run addEmailLower).db.run namedCustomers).outputs := by
  decide +kernel

/-- The column definition {lit}`email_lower TEXT` of the migration, as syntax. -/
def emailLowerDefinition : Syntax.ColumnDefinition := ⟨name! "email_lower", some "TEXT", []⟩
/-- The written value {lit}`lower(email)` of the backfill, as syntax. -/
def lowerEmail : Syntax.Expr := .call "lower" [.identifier (name! "email") .none]
/-- The table {lit}`customers` in {lit}`FROM`, without an alias. -/
def customersReference : Syntax.TableReference := { table := name! "customers", alias := none }
/-- The result columns {lit}`id, name, email` of {lit}`namedCustomers`. -/
def namedColumns : List Syntax.ResultColumn :=
  [.expression (.identifier (name! "id") .none) none "id",
    .expression (.identifier (name! "name") .none) none "name",
    .expression (.identifier (name! "email") .none) none "email"]
/-- The result column {lit}`id` of {lit}`customerIdByEmail`. -/
def idColumns : List Syntax.ResultColumn := [.expression (.identifier (name! "id") .none) none "id"]
/-- The filter {lit}`email = ?1` of {lit}`customerIdByEmail`. -/
def emailFilter : Syntax.Expr := .compare .eq (.identifier (name! "email") .none) (.parameter 1)

/-- The SQL file is the derived-column migration of the library law. -/
theorem addEmailLower_is_migration : addEmailLower =
    DerivedColumnMigration.migration (name! "customers") emailLowerDefinition lowerEmail [] [] [] := rfl

/-- The table {lit}`customers` of the schema {lit}`shop`, at catalog position 0. -/
def customersShape : CatalogTable := (shop.raw.catalog.tableAt 0).get (by decide +kernel)
/-- The table {lit}`customers` with the column {lit}`email_lower` appended. -/
def customersWide : CatalogTable :=
  { customersShape with
    columns := customersShape.columns ++ [definedColumn customersShape.strict emailLowerDefinition] }
/-- The catalog of {lit}`shop` after the migration. -/
def wideCatalog : Catalog := shop.raw.catalog.addColumn 0 (definedColumn customersShape.strict emailLowerDefinition)


/-- Each database with the catalog of {lit}`shop` has the site of the law: {lit}`customers` is at position 0, has no
column {lit}`email_lower`, no generated column and no trigger, and {lit}`lower(email)` reads the column at
position 2. -/
def siteOf (db : Database) (schema : db.HasCatalog shop) :
    DerivedColumnMigration.Site db.raw (name! "customers") emailLowerDefinition lowerEmail :=
  { position := 0, table := { shape := customersShape, rows := db.raw.rows.getD 0 [] }
    derived := .scalar .lower (.cons (.column 2) .nil), affinity := none
    found := by rw [show db.raw.catalog = shop.raw.catalog from schema]; dsimp only; decide +kernel
    present := (Database.table_of_catalog schema (by decide +kernel)).1
    constraintFree := rfl
    admitted := by dsimp only; decide +kernel
    fresh := by dsimp only; decide +kernel
    operand := by dsimp only; decide +kernel
    below := by dsimp only; decide +kernel
    contextFree := by intro first second cells; rfl
    keysInside := by dsimp only; decide +kernel
    plain := by dsimp only; decide +kernel
    noneFiring := by rw [show db.raw.catalog = shop.raw.catalog from schema]; dsimp only; decide +kernel }

/-- The catalog that the migration reaches from a database of {lit}`shop` is {lit}`wideCatalog`. -/
theorem reached_catalog (db : Database) (schema : db.HasCatalog shop) :
    ((siteOf db schema).reached []).catalog = wideCatalog := by
  show db.raw.catalog.addColumn 0 _ = _
  rw [show db.raw.catalog = shop.raw.catalog from schema]
  rfl

/-- {lit}`resolveStatement_select_table` of the library for a state whose catalog is a given catalog, and the
table {lit}`customers` at position 0. -/
theorem select_resolves (state : ResolveState) (catalog : Catalog) (same : state.catalog = catalog)
    (shape : CatalogTable) (filter : Option Syntax.Expr) (condition : Option Resolved.Expr)
    (columns : List Syntax.ResultColumn) (resolved : List (List (Resolved.Output × String × Option Affinity)))
    (found : catalog.findTable customersReference.table = some (0, shape))
    (noAggregate : (columns.all fun
      | .expression value _ _ => value.aggregateCalls.isEmpty
      | .star | .sourceStar _ => true) = true)
    (noStar : starIssue (tableScope catalog customersReference 0 shape) columns = none)
    (columnsOk : resolveAll (resolveResultColumn runContext.profile.dqsDml
      (tableScope catalog customersReference 0 shape) { later := [] }) columns = .ok resolved)
    (resolves : FilterResolves runContext.profile.dqsDml (tableScope catalog customersReference 0 shape)
      ((resultAliases (tableScope catalog customersReference 0 shape) columns).filterMap id) filter condition)
    (noFeed : (resolved.flatten.filterMap fun (output, _) => match output with
      | .scalar expression => some expression
      | .aggregate _ => none).any (fun expression =>
        expression.any fun node => node.isFallibleCall && node.any (· matches .aggregateValue _)) = false) :
    resolveStatement runContext state
        (.select columns (some customersReference) [] filter [] [] none none [] none false none) =
      .ok (.query (Resolved.Query.simple [Resolved.QuerySource.first 0] condition
        (resolved.flatten.map (·.1)) (resolved.flatten.map (·.2.1))) [], state) := by
  subst same
  exact resolveStatement_select_table runContext state customersReference filter 0 shape condition columns resolved
    rfl rfl rfl found noAggregate noStar columnsOk resolves noFeed

/-- The statement of {lit}`namedCustomers`, as syntax. -/
def namedStatement : Syntax.Statement :=
  .select namedColumns (some customersReference) [] none [] [] none none [] none false none
/-- The statement of {lit}`customerIdByEmail`, as syntax. -/
def lookupStatement : Syntax.Statement :=
  .select idColumns (some customersReference) [] (some emailFilter) [] [] none none [] none false none
/-- The resolved result columns of {lit}`namedCustomers`. -/
def namedResolved : List (List (Resolved.Output × String × Option Affinity)) :=
  [[(.scalar (.column 0), "id", some .integer)], [(.scalar (.column 1), "name", some .text)],
    [(.scalar (.column 2), "email", some .text)]]
/-- The resolved result column of {lit}`customerIdByEmail`. -/
def idResolved : List (List (Resolved.Output × String × Option Affinity)) :=
  [[(.scalar (.column 0), "id", some .integer)]]
/-- The resolved filter {lit}`email = ?1`: the comparison has the TEXT affinity of the column. -/
def emailCondition : Resolved.Expr := .compare .eq (some .text) (.column 2) (.parameter 1)

/-- The read {lit}`namedCustomers` resolves to the same query of old columns before and after the migration. -/
def namedKept (db : Database) (schema : db.HasCatalog shop) :
    (siteOf db schema).ReadPreserved [] namedStatement :=
  { filter := none
    columns := [.scalar (.column 0), .scalar (.column 1), .scalar (.column 2)]
    filterBelow := by intro condition member; cases member
    columnsBelow := by dsimp only [siteOf]; decide +kernel
    resolvesBefore := fun state same => ⟨_, state,
      select_resolves state shop.raw.catalog (same.trans schema) customersShape none none namedColumns namedResolved
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (FilterResolves.of_none _ _ _ _) (by decide +kernel)⟩
    resolvesAfter := fun state same => ⟨_, state,
      select_resolves state wideCatalog (same.trans (reached_catalog db schema)) customersWide none none namedColumns
        namedResolved (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (FilterResolves.of_none _ _ _ _) (by decide +kernel)⟩
    calm := fun names => Resolved.Statement.simpleTable_calm 0 none _ names
      (by
        intro expression member
        simp [Resolved.Output.scalars] at member
        rcases member with rfl | rfl | rfl <;> exact Resolved.Expr.calm_column _)
      (by
        intro column member
        simp at member
        rcases member with rfl | rfl | rfl <;> rfl) }

/-- The read {lit}`customerIdByEmail` resolves to the same query of old columns before and after the migration. -/
def lookupKept (db : Database) (schema : db.HasCatalog shop) :
    (siteOf db schema).ReadPreserved [] lookupStatement :=
  { filter := some emailCondition
    columns := [.scalar (.column 0)]
    filterBelow := by dsimp only [siteOf]; decide +kernel
    columnsBelow := by dsimp only [siteOf]; decide +kernel
    resolvesBefore := fun state same => ⟨_, state,
      select_resolves state shop.raw.catalog (same.trans schema) customersShape (some emailFilter) (some emailCondition)
        idColumns idResolved (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (FilterResolves.of_term (result := (emailCondition, none)) (by decide +kernel) (by decide +kernel))
        (by decide +kernel)⟩
    resolvesAfter := fun state same => ⟨_, state,
      select_resolves state wideCatalog (same.trans (reached_catalog db schema)) customersWide (some emailFilter)
        (some emailCondition) idColumns idResolved (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel)
        (FilterResolves.of_term (result := (emailCondition, none)) (by decide +kernel) (by decide +kernel))
        (by decide +kernel)⟩
    calm := fun names => Resolved.Statement.simpleColumn_calm 0 _ 0 names (by
      intro expression member
      simp at member
      subst member
      simp [emailCondition, Resolved.Expr.Calm, Resolved.Expr.any, Resolved.Expr.isFallibleCall,
        Resolved.Expr.readsClockHere, Resolved.Expr.readsCounterHere]) }

/-- On every database with the catalog of {lit}`shop` where the migration succeeds, the read of all customers
with named columns gives the same result after the migration as before it. -/
theorem named_read_preserved :
    Migration.QueryPreserves (send addEmailLower) namedCustomers (·.HasCatalog shop) :=
  DerivedColumnMigration.queryPreserves (name! "customers") emailLowerDefinition lowerEmail [] [] []
    namedStatement [] rfl rfl (·.HasCatalog shop) siteOf namedKept

/-- For every email, on every database with the catalog of {lit}`shop` where the migration succeeds, the
lookup of a customer id by email gives the same result after the migration as before it. -/
theorem lookup_read_preserved : ∀ email : Value,
    Migration.QueryPreserves (send addEmailLower) (customerIdByEmail email) (·.HasCatalog shop) :=
  fun email => DerivedColumnMigration.queryPreserves (name! "customers") emailLowerDefinition lowerEmail [] [] []
    lookupStatement [email] rfl rfl (·.HasCatalog shop) siteOf lookupKept

#print axioms star_read_changes
#print axioms named_read_kept_on_found
#print axioms named_read_preserved
#print axioms lookup_read_preserved

end DerivedColumnSchemaPremise
