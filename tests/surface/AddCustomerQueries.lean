import Belay

/-! A fixture module of `tests/surface_assertion_examples_test.py`: the program of the guide that uses a result,
and the site of its claim (ADR 0017, S6). The program {lit}`addCustomer` reads the next free id with one SELECT and
inserts the customer with that id. A universal claim about the program cannot compute the id: the id depends on
the aggregate over the rows and on the rowid bound of the insert. The claim holds for every id the SELECT
returns, so the site lists the conditions that the model runs both statements, and nothing about the value of the
id. The final property of the claim is not a field of the site. -/

set_option doc.verso true

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- The query of the guide that reads the next free id. -/
def selectNext : Script := sql r"SELECT coalesce(max(id), 0) + 1 FROM customers"

/-- The insert of the guide, for the id that the query returned. -/
def insertCustomerAt (next : Value) (name email : String) : Script :=
  sql r"INSERT INTO customers (id, name, email) VALUES ($next, $name, $email)"

/-- The program of the guide: add a customer with the next free id. The value tells whether the insert
succeeded; it is {lean}`false` when the query returns no single value. -/
def addCustomer (name email : String) : Sql Bool := do
  let some next ← single selectNext
    | pure false
  let outputs ← send (insertCustomerAt next name email)
  pure outputs.allOk

/-- The claim of the guide: a customer with the name exists. -/
def customerNamed (name : String) : Script := sql r"SELECT 1 FROM customers WHERE name = $name"

/-- The syntax tree of the query {name}`selectNext`. -/
def selectStatement : Syntax.Statement := (selectNext.statements.headD (.begin, [])).1

/-- The syntax tree of the insert, which does not depend on the id and the text values. -/
def insertStatement : Syntax.Statement := ((insertCustomerAt .null "" "").statements.headD (.begin, [])).1

/-- The script {name}`selectNext` is its one statement without bound values. -/
theorem selectNext_script : selectNext = ⟨[(selectStatement, [])]⟩ := rfl

/-- For every id and texts: the script of the insert is {name}`insertStatement` with the three bound values. -/
theorem insertCustomerAt_script (next : Value) (name email : String) :
    insertCustomerAt next name email =
      ⟨[(insertStatement, [next, .text name.toUTF8.toList, .text email.toUTF8.toList])]⟩ := rfl

/-- The statement {name}`selectStatement` is a SELECT. -/
theorem selectStatement_is_select : ∃ columns source joins filter groupBy orderBy limit offset subqueries having
    distinct compound, selectStatement =
      .select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound :=
  ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

/-- The conditions under which the program {name}`addCustomer` inserts one customer with the name, whatever
id the query returns. The table {lit}`customers` has exactly the columns {lit}`id`, {lit}`name` and
{lit}`email`, none of them generated, the name with TEXT affinity, and its rowid alias, if any, is the first
column. The insert resolves from the idle connection to a plain insert, which has no rule of a trigger or a
foreign key. The model runs the query for every clock and every counter, and runs the insert for every clock and
every counter with every value that the query can return. -/
structure AddCustomerSite (db : Database) (name email : String) where
  /-- The catalog position of {lit}`customers`. -/
  position : Nat
  /-- The catalog entry of {lit}`customers`. -/
  table : CatalogTable
  /-- The column {lit}`id`. -/
  idCell : CatalogColumn
  /-- The column {lit}`name`. -/
  nameCell : CatalogColumn
  /-- The column {lit}`email`. -/
  emailCell : CatalogColumn
  /-- The resolution state after the insert. -/
  after : ResolveState
  /-- The database has the table. -/
  found : db.raw.catalog.findTable (name! "customers") = some (position, table)
  /-- The table has these three columns. -/
  columns : table.columns = [idCell, nameCell, emailCell]
  /-- The second column is named {lit}`name`. -/
  nameAt : columnPosition table.columns (name! "name") = some 1
  /-- The name has TEXT affinity, so the stored name is the text. -/
  nameText : nameCell.affinity = .text
  /-- No column is generated. -/
  plainColumns : ∀ column ∈ table.columns, column.generated = none
  /-- The table has no rowid alias, or the id is the alias. -/
  alias : table.rowidAlias = none ∨ table.rowidAlias = some 0
  /-- The insert resolves to a plain insert. -/
  insertResolves : resolveStatement runContext (db.raw.connection {}).resolveState insertStatement =
    .ok (.insert position [[.expression (.parameter 1), .expression (.parameter 2), .expression (.parameter 3)]]
      [] [] none, after)
  /-- The model runs the query, whatever the clock and the counters. -/
  selectModeled : ∀ env : Env,
    (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) selectStatement []).continues = true
  /-- The model runs the insert, whatever the clock and the counters, with each value that the query can
  return. -/
  insertModeled : ∀ env : Env,
    (selectedValues (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) selectStatement []).output).all
      (fun next => (runScriptStep runContext env.clock 1 (db.raw.connection env.counters) insertStatement
        [next, .text name.toUTF8.toList, .text email.toUTF8.toList]).continues) = true

/-- For every database with a table {lit}`customers` whose second column is {lit}`name`: a customer with the
name exists exactly when one row of the table has the cell equal to the name. Proof sketch: apply
{name}`Holds.iff_selectOne` to the resolved condition. -/
theorem a_customer_named_iff (db : Database) (name : String) (position : Nat) (table : CatalogTable)
    (nameCell : CatalogColumn)
    (found : db.raw.catalog.findTable (name! "customers") = some (position, table))
    (nameAt : columnPosition table.columns (name! "name") = some 1) (nameCellAt : table.columns[1]? = some nameCell) :
    Holds (customerNamed name) db ↔
      ∃ row ∈ Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] },
        Resolved.truthy ((equalsParameter nameCell 1 1).eval (Resolved.EvalContext.bound [.text name.toUTF8.toList])
          row) = true := by
  have resolves := FilterResolves.of_term (dqs := runContext.profile.dqsDml)
    (scope := tableScope db.raw.catalog { table := name! "customers", alias := none } position table) (aliases := [])
    (shapes := { later := [] })
    (term := .compare .eq (.identifier (name! "name") .none) (.parameter 1)) (by simp [namesAlias])
    (result := (equalsParameter nameCell 1 1, none))
    (by simp [sql_simp, nameAt, nameCellAt, equalsParameter]; rfl)
  refine Iff.trans (Holds.iff_selectOne (namedSource := rfl) (current := rfl) (head := rfl) (arguments := rfl) found resolves ?_) ?_
  · simp [sql_simp, equalsParameter]
  · simp [sql_simp]

end AssertionExamples
