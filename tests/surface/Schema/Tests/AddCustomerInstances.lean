import AddCustomerClaims

/-! A fixture module of `tests/surface_assertion_examples_test.py`: an instance and a counterexample of the claim
about the program that uses a result (ADR 0017, S6). The instance shows that the site of
{name}`AddCustomerSite` holds on a database, including the kernel check that the model runs the insert for
every environment and every value that the query returns, and that the program adds the customer. The
counterexample is a database with a trigger that removes the new customer: the program returns {lean}`true` and
no customer has the name, so the site must exclude the trigger. -/

set_option doc.verso true
set_option maxRecDepth 200000
set_option exponentiation.threshold 2000

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- A database with the site: the guide's table of customers, with one customer. -/
def shop : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT NOT NULL, email TEXT NOT NULL);
  INSERT INTO customers VALUES (1, 'mary', 'm@x');"

/-- The catalog position and entry of {lit}`customers` in {name}`shop`. -/
def shopCustomers : Nat × CatalogTable := (shop.raw.catalog.findTable (name! "customers")).get (by decide +kernel)

set_option maxHeartbeats 4000000 in
/-- The site of the program {name}`addCustomer` for the name {lit}`'eve'` in {name}`shop`. The kernel checks
that the model runs the query and the insert for every environment by evaluation; the check of the insert is
the slowest step of the fixture. -/
def shopSite : AddCustomerSite shop "eve" "e@x" where
  position := shopCustomers.1
  table := shopCustomers.2
  idCell := (shopCustomers.2.columns[0]?).get (by decide +kernel)
  nameCell := (shopCustomers.2.columns[1]?).get (by decide +kernel)
  emailCell := (shopCustomers.2.columns[2]?).get (by decide +kernel)
  after := (shop.raw.connection {}).resolveState
  found := by decide +kernel
  columns := by decide +kernel
  nameAt := by decide +kernel
  nameText := by decide +kernel
  plainColumns := by decide +kernel
  alias := by decide +kernel
  insertResolves := by decide +kernel
  selectModeled := fun env => by with_unfolding_all rfl
  insertModeled := fun env => by with_unfolding_all rfl

/-- The run of {name}`addCustomer` from the fresh start of a database, with no clock and the counters of a new
connection. -/
def addRun (db : Database) (name email : String) : SqlRun Bool :=
  (addCustomer name email).runFrom none 0 (ExecutionContext.initial db { counters := Counters.newConnection }).connection

/-- The final context of {name}`addRun`. -/
def afterAdd (db : Database) (name email : String) : ExecutionContext :=
  (ExecutionContext.initial db { counters := Counters.newConnection }).finish (addRun db name email)

-- The instance on `shop`: the program reports success with the id 2, and afterwards a customer named eve exists.
example : (addRun shop "eve" "e@x").value = some true ∧ Holds.reached (customerNamed "eve") (afterAdd shop "eve" "e@x") := by
  decide +kernel

/-- A successful trigger may remove the new customer. The insert is a plain insert only when no trigger fires,
which the site requires, so this database has no site. -/
def removingTrigger : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT NOT NULL, email TEXT NOT NULL);
  CREATE TRIGGER forget AFTER INSERT ON customers BEGIN DELETE FROM customers WHERE id = NEW.id; END;"

/-- In {name}`removingTrigger` the program reports success and afterwards no customer has the name: the
reported success is not enough for the claim without the conditions of the site. -/
theorem a_trigger_removes_the_added_customer :
    (addRun removingTrigger "eve" "e@x").value = some true ∧
    ¬ Holds.reached (customerNamed "eve") (afterAdd removingTrigger "eve" "e@x") := by decide +kernel

#print axioms shopSite
#print axioms a_trigger_removes_the_added_customer

end AssertionExamples
