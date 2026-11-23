import Belay

/-! A fixture module of `tests/surface_assertion_examples_test.py`: the site of the guide's insert and lookup
claim (ADR 0017, S6). The statement `INSERT INTO customers VALUES ($id, $name)` adds one row with the two values
when the schema, the resolution and the affinities are as the fields of `CustomerInsertSite` say. This module
shows the rows that the statement stores and reduces a fresh-run claim about the statement to a claim about the
database with the new row. The final property of the claim is not a field of the site. -/

set_option doc.verso true

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- The statement of the guide's insert claim, for an id and a name. -/
def insertCustomer (id : Int64) (name : String) : Script := sql r"INSERT INTO customers VALUES ($id, $name)"

/-- The conditions under which the statement {name}`insertCustomer` adds the row of its two values to the table
{lit}`customers` of the database, and nothing else. The table has exactly the columns {lit}`id` and {lit}`name`,
the first with INTEGER affinity and the second with TEXT affinity, none of them generated, and its rowid alias,
if any, is the first column. The statement resolves from the idle connection to a plain insert, which has no
rule of a trigger or a foreign key. The model runs it for every clock and every counter. -/
structure CustomerInsertSite (db : Database) (id : Int64) (name : String) where
  /-- The syntax tree of the statement. -/
  statement : Syntax.Statement
  /-- The script is this statement with the two bound values. -/
  script : insertCustomer id name = ⟨[(statement, [.integer id.toInt, .text name.toUTF8.toList])]⟩
  /-- The catalog position of {lit}`customers`. -/
  position : Nat
  /-- The catalog entry of {lit}`customers`. -/
  table : CatalogTable
  /-- The column {lit}`id`. -/
  idCell : CatalogColumn
  /-- The column {lit}`name`. -/
  nameCell : CatalogColumn
  /-- The resolution state after the statement. -/
  after : ResolveState
  /-- The database has the table. -/
  found : db.raw.catalog.findTable (name! "customers") = some (position, table)
  /-- The table has these two columns. -/
  columns : table.columns = [idCell, nameCell]
  /-- The first column is named {lit}`id`. -/
  idAt : columnPosition table.columns (name! "id") = some 0
  /-- The second column is named {lit}`name`. -/
  nameAt : columnPosition table.columns (name! "name") = some 1
  /-- The id has INTEGER affinity, so the stored id is the integer. -/
  idInteger : idCell.affinity = .integer
  /-- The name has TEXT affinity, so the stored name is the text. -/
  nameText : nameCell.affinity = .text
  /-- Neither column is generated. -/
  plainColumns : idCell.generated = none ∧ nameCell.generated = none
  /-- The table has no rowid alias, or the id is the alias. -/
  alias : table.rowidAlias = none ∨ table.rowidAlias = some 0
  /-- The statement resolves to a plain insert. -/
  resolves : resolveStatement runContext (db.raw.connection {}).resolveState statement =
    .ok (.insert position [[.expression (.parameter 1), .expression (.parameter 2)]] [] [] none, after)
  /-- The model runs the statement, whatever the clock and the counters. -/
  modeled : ∀ env : Env, (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) statement
    [.integer id.toInt, .text name.toUTF8.toList]).continues = true

/-- For every database with the site of the insert: the rows of the table after the statement are the
old rows and one row with the id and the name. Proof sketch: the two bound values are stored as they
are, and a plain table keeps the cells of a new row. -/
theorem inserted_rows {db : Database} {id : Int64} {name : String} (site : CustomerInsertSite db id name)
    (counters : Counters) (value : Int) :
    (LiteralData.inserted ⟨site.table, db.raw.rows.getD site.position []⟩
      (Resolved.rowsAt (Resolved.statementContext value counters [.integer id.toInt, .text name.toUTF8.toList] db.raw [])
        site.table.columns [[.expression (.parameter 1), .expression (.parameter 2)]])).rows =
    db.raw.rows.getD site.position [] ++ [⟨LiteralData.newRowid ⟨site.table, db.raw.rows.getD site.position []⟩
      [.integer id.toInt, .text name.toUTF8.toList], [.integer id.toInt, .text name.toUTF8.toList]⟩] := by
  rw [site.columns, rowsAt_two_parameters]
  simp only [Value.store, boundValue, site.idInteger, site.nameText, numericStore]
  exact LiteralData.inserted_plain ⟨site.table, db.raw.rows.getD site.position []⟩ id.toInt _
    (by simp [site.columns, site.plainColumns.1, site.plainColumns.2]) site.alias

/-- The first claim: exactly one customer has the id. -/
def exactlyOneCustomerHasTheId (id : Int64) : Script :=
  sql r"SELECT 1 WHERE (SELECT count(*) FROM customers WHERE id = $id) = 1"

/-- The second claim: a customer has the id and the name. -/
def aCustomerHasTheIdAndName (id : Int64) (name : String) : Script :=
  sql r"SELECT 1 FROM customers WHERE id = $id AND name = $name"

/-- The guard of the claim: no customer has the id. -/
def noCustomerHasTheId (id : Int64) : Script := sql r"SELECT 1 WHERE NOT EXISTS (SELECT 1 FROM customers WHERE id = $id)"

/-- For every script that holds on the database with the new row appended to the table, the fresh run of
the statement, from a database with the site and without a customer of the id, checks the script in every
final state without an error. The new row has the cells of the bound values; its rowid is not named.
Proof sketch: {name}`Sql.check_send_of_rule` with the kind rule {name}`runScriptStep_plainInsert_eq`, split on
its cases after the table of the site selects one; a failure gives an error and requires nothing, and after a
success the final context sees the database with the rows of {name}`inserted_rows`, and it is valid. -/
theorem insert_then_holds (id : Int64) (name : String) (query : Script) (isQuery : query.isQuery = true)
    (afterwards : ∀ (db : Database) (site : CustomerInsertSite db id name), Holds (noCustomerHasTheId id) db →
      ∀ (row : Row), row.values = [.integer id.toInt, .text name.toUTF8.toList] →
      ∀ valid : (db.raw.setRows site.position (db.raw.rows.getD site.position [] ++ [row])).Valid Profile.pinned,
        Holds query ⟨db.raw.setRows site.position (db.raw.rows.getD site.position [] ++ [row]), valid⟩ isQuery) :
    FreshEnsures (send (insertCustomer id name))
      (fun db => Holds (noCustomerHasTheId id) db ∧ Nonempty (CustomerInsertSite db id name))
      (ifOk (holds query isQuery)) := by
  refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_
  rintro db ⟨guard, ⟨site⟩⟩ env _complete
  rw [site.script]
  have rule := runScriptStep_plainInsert_eq (connection := db.raw.connection env.counters) (clock := env.clock)
    (index := 0) (parameters := [.integer id.toInt, .text name.toUTF8.toList]) site.resolves
  refine Sql.check_send_of_rule rule (ExecutionContext.initial_holds_valid _ _)
    (RunStep.continues_of_rule rule (site.modeled env)) ?_
  dsimp only
  erw [Database.table_of_findTable db.raw _ site.position site.table site.found]
  dsimp only
  repeat' split
  all_goals first
    | exact trivial
    | refine Sql.sendReached_single (fun _ same => by cases same) fun valid allOk => ?_
  · refine (Holds.reached_iff_holds_of_valid query _ isQuery valid.1).2 ?_
    revert valid
    erw [inserted_rows site]
    exact fun valid => afterwards db site guard _ rfl valid.1
  · simp [ExecutionContext.next, List.allOk, Output.isError] at allOk

#print axioms inserted_rows
#print axioms insert_then_holds

end AssertionExamples
