import CustomerInsertQueries

/-! A fixture of `tests/surface_assertion_examples_test.py`: the guide's insert and lookup claim as fresh-run
triples over every admitted database (ADR 0017, S6). The claim reads: if no customer has the id and the
`INSERT` runs without an error, then exactly one customer has the id, and a customer has the id and the name.
It holds for every database with a site of the insert; the instances check that the site and the guard are
satisfiable, and the other databases show what the conditions of the site exclude. -/

set_option doc.verso true

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- Over every admitted database with the site of the insert, every id and every name: if no customer has the id
and the {lit}`INSERT` runs without an error, exactly one customer has the id afterwards. -/
theorem inserted_customer_is_unique (id : Int64) (name : String) :
    FreshEnsures (send (insertCustomer id name))
      (fun db => Holds (noCustomerHasTheId id) db ∧ Nonempty (CustomerInsertSite db id name))
      (ifOk (holds (exactlyOneCustomerHasTheId id))) :=
  insert_then_holds id name _ _ fun db site guard row hrow valid => by
    have idCellAt : site.table.columns[0]? = some site.idCell := by simp [site.columns]
    have none := (no_customer_has_the_id_iff db id site.position 0 site.table site.idCell site.found site.idAt
      idCellAt).1 guard
    refine (one_customer_has_the_id_iff ⟨_, valid⟩ id site.position 0 site.table site.idCell
      (found_after_insert site _) site.idAt idCellAt).2 ?_
    show Resolved.countMatching _ _ ⟨site.table, (db.raw.setRows _ _).rows.getD site.position []⟩ = 1
    rw [rows_after_insert site row]
    refine countMatching_appended _ _ ⟨site.table, db.raw.rows.getD site.position []⟩ row ?_ ?_
    · intro values mem
      simpa using none values mem
    · rw [hrow]
      simpa using equalsParameter_true site.idCell 0 1 [.integer id.toInt] [.integer id.toInt,
        .text name.toUTF8.toList] (.integer id.toInt) rfl rfl rfl (comparisonOperands_integer _ _ site.idInteger)

/-- Over every admitted database with the site of the insert, every id and every name: if no customer has the id
and the {lit}`INSERT` runs without an error, a customer has the id and the name afterwards. -/
theorem inserted_customer_has_the_name (id : Int64) (name : String) :
    FreshEnsures (send (insertCustomer id name))
      (fun db => Holds (noCustomerHasTheId id) db ∧ Nonempty (CustomerInsertSite db id name))
      (ifOk (holds (aCustomerHasTheIdAndName id name))) :=
  insert_then_holds id name _ _ fun db site guard row hrow valid => by
    have idCellAt : site.table.columns[0]? = some site.idCell := by simp [site.columns]
    have nameCellAt : site.table.columns[1]? = some site.nameCell := by simp [site.columns]
    refine (a_customer_has_the_id_and_name_iff ⟨_, valid⟩ id name site.position site.table site.idCell site.nameCell
      (found_after_insert site _) site.idAt idCellAt site.nameAt nameCellAt).2 ?_
    show ∃ stored ∈ Resolved.sourceRows ⟨site.table, (db.raw.setRows _ _).rows.getD site.position []⟩, _
    rw [rows_after_insert site row]
    refine ⟨row.values, (mem_sourceRows_iff _ _).2 ⟨row, by simp, rfl⟩, ?_, ?_⟩
    · rw [hrow]
      exact equalsParameter_true site.idCell 0 1 _ _ (.integer id.toInt) rfl rfl rfl
        (comparisonOperands_integer _ _ site.idInteger)
    · rw [hrow]
      exact equalsParameter_true site.nameCell 1 2 _ _ (.text name.toUTF8.toList) rfl rfl rfl
        (comparisonOperands_text _ _ site.nameText)

/-- A database with the site: the guide's table of customers, with one customer. -/
def shop : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT NOT NULL);
  INSERT INTO customers VALUES (1, 'mary');"

/-- The catalog position and entry of {lit}`customers` in {name}`shop`. -/
def shopCustomers : Nat × CatalogTable := (shop.raw.catalog.findTable (name! "customers")).get (by decide +kernel)

set_option maxRecDepth 200000 in
set_option exponentiation.threshold 2000 in
/-- The site of the insert of the id 3 and the name {lit}`'ann'` into {name}`shop`. -/
def shopSite : CustomerInsertSite shop 3 "ann" where
  statement := .insert (name! "customers") none [[.parameter 1, .parameter 2]] []
  script := rfl
  position := shopCustomers.1
  table := shopCustomers.2
  idCell := (shopCustomers.2.columns[0]?).get (by decide +kernel)
  nameCell := (shopCustomers.2.columns[1]?).get (by decide +kernel)
  after := (shop.raw.connection {}).resolveState
  found := by decide +kernel
  columns := by decide +kernel
  idAt := by decide +kernel
  nameAt := by decide +kernel
  idInteger := by decide +kernel
  nameText := by decide +kernel
  plainColumns := by decide +kernel
  alias := by decide +kernel
  resolves := by decide +kernel
  modeled := fun env => by with_unfolding_all rfl

/-- The final context of the run of the insert from the fresh start of a database, with no clock and the
counters of a new connection. -/
def afterInsert (db : Database) (id : Int64) (name : String) : ExecutionContext :=
  let start := ExecutionContext.initial db { counters := Counters.newConnection }
  start.finish ((send (insertCustomer id name)).runFrom none 0 start.connection)

-- The instance on `shop`: no customer has the id 3, the insert runs without an error, and afterwards exactly one
-- customer has the id and a customer has the id and the name, as the two theorems say for every such database.
example : Holds (noCustomerHasTheId 3) shop := by decide +kernel
example : (afterInsert shop 3 "ann").outputs.allOk = true ∧
    Holds.reached (exactlyOneCustomerHasTheId 3) (afterInsert shop 3 "ann") ∧
    Holds.reached (aCustomerHasTheIdAndName 3 "ann") (afterInsert shop 3 "ann") := by decide +kernel

/-- A successful trigger may remove the inserted row. The statement is a plain insert only when no trigger
fires, which the site requires, so this database has no site. -/
def removingTrigger : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT NOT NULL);
  CREATE TRIGGER forget AFTER INSERT ON customers BEGIN DELETE FROM customers WHERE id = NEW.id; END;"

/-- In {name}`removingTrigger` no customer has the id 3 before, the insert succeeds, and afterwards neither
the count claim nor the row claim holds: the successful insert is not enough for the claims. -/
theorem a_trigger_removes_the_inserted_customer :
    Holds (noCustomerHasTheId 3) removingTrigger ∧ (afterInsert removingTrigger 3 "ann").outputs.allOk = true ∧
    ¬ Holds.reached (exactlyOneCustomerHasTheId 3) (afterInsert removingTrigger 3 "ann") ∧
    ¬ Holds.reached (aCustomerHasTheIdAndName 3 "ann") (afterInsert removingTrigger 3 "ann") := by decide +kernel

/-- Without the guard the claim fails: with no key on the id, and a customer 1 present, the insert of the id 1 runs
and two customers have the id. -/
def keyless : Database := db! r"
  CREATE TABLE customers (id INTEGER, name TEXT NOT NULL);
  INSERT INTO customers VALUES (1, 'mary');"

/-- In {name}`keyless` customer 1 is present, the insert of the id 1 succeeds, and afterwards the count of the
customers with the id is not exactly one. -/
theorem without_the_guard_two_customers_have_the_id :
    ¬ Holds (noCustomerHasTheId 1) keyless ∧ (afterInsert keyless 1 "john").outputs.allOk = true ∧
    ¬ Holds.reached (exactlyOneCustomerHasTheId 1) (afterInsert keyless 1 "john") := by decide +kernel

/-- A {lit}`UNIQUE` name makes the insert fail when the name exists: the trace has an error, and the conditional
postcondition requires nothing. -/
def uniqueName : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT NOT NULL UNIQUE);
  INSERT INTO customers VALUES (7, 'john');"

/-- In {name}`uniqueName` no customer has the id 3 before, and the insert of the name {lit}`'john'` fails, so
the run does not succeed and a claim guarded by {lit}`ifOk` asks nothing. -/
theorem a_duplicate_name_fails_the_insert :
    Holds (noCustomerHasTheId 3) uniqueName ∧ (afterInsert uniqueName 3 "john").outputs.allOk = false := by
  decide +kernel

#print axioms inserted_customer_is_unique
#print axioms inserted_customer_has_the_name
#print axioms shopSite

end AssertionExamples
