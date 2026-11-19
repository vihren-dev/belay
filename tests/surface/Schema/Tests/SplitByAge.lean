import Belay

set_option doc.verso true

/-! A migration whose data loss depends on a value in a row, not on the schema. The migration splits
the table {lit}`customers` into {lit}`minors` and {lit}`adults` by age and keeps the old name as a view
over the two tables. A customer whose age is NULL goes to neither table: {lit}`age < 18` and
{lit}`age >= 18` are both NULL for it. The check finds such a customer. The fixed migration copies the
NULL ages into {lit}`adults`. The test is {lit}`tests/surface_split_by_age_test.py`. -/

namespace SplitByAge
open Belay.Sqlite

/-- The schema, without rows. -/
def shop : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT NOT NULL, age INTEGER);"

/-- The migration with the mistake: a customer whose age is NULL is in neither copy, and the drop of
{lit}`customers` deletes it. -/
def splitByAge : Script := sql r"
  BEGIN;
  CREATE TABLE minors (id INTEGER PRIMARY KEY, name TEXT NOT NULL, age INTEGER);
  CREATE TABLE adults (id INTEGER PRIMARY KEY, name TEXT NOT NULL, age INTEGER);
  INSERT INTO minors SELECT id, name, age FROM customers WHERE age < 18;
  INSERT INTO adults SELECT id, name, age FROM customers WHERE age >= 18;
  DROP TABLE customers;
  CREATE VIEW customers AS
    SELECT id, name, age FROM minors UNION ALL SELECT id, name, age FROM adults;
  COMMIT;"

/-- The fixed migration: the customers whose age is NULL go to {lit}`adults`. Every value that is not
NULL makes exactly one of {lit}`age < 18` and {lit}`age >= 18` true, so each customer is in exactly one
copy. -/
def splitByAgeFixed : Script := sql r"
  BEGIN;
  CREATE TABLE minors (id INTEGER PRIMARY KEY, name TEXT NOT NULL, age INTEGER);
  CREATE TABLE adults (id INTEGER PRIMARY KEY, name TEXT NOT NULL, age INTEGER);
  INSERT INTO minors SELECT id, name, age FROM customers WHERE age < 18;
  INSERT INTO adults SELECT id, name, age FROM customers WHERE age >= 18 OR age IS NULL;
  DROP TABLE customers;
  CREATE VIEW customers AS
    SELECT id, name, age FROM minors UNION ALL SELECT id, name, age FROM adults;
  COMMIT;"

/-- The read that a correct migration keeps: every customer. It has no {lit}`ORDER BY`: the model
compares its rows in their normal form, so the claim is about the rows and not about their order. -/
def allCustomers : Script := sql r"SELECT id, name, age FROM customers"

-- The default time limit is 10 s of wall-clock time. On an idle machine this file elaborates about 8 s
-- longer with the check than without it, which is near the limit, and a loaded machine makes the check
-- slower (issue #426). So the fixture gives the check 60 s.
set_option sql.checkTimeLimit 60000 in
#sql_check splitByAge preserves allCustomers on shop

/-- The counterexample that the check found: one customer whose age is NULL. -/
def found : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT NOT NULL, age INTEGER);
  INSERT INTO customers VALUES (1, '', NULL);"

/-- On {name}`found`, every statement of {name}`splitByAge` succeeds, and the read gives no row. -/
example : (found.run splitByAge).outputs.allOk = true ∧
    ((found.run splitByAge).db.run allCustomers).outputs.getLast? = some (.rows []) := by
  decide +kernel

/-- On {name}`found`, every statement of {name}`splitByAgeFixed` succeeds, and the read gives the
customer. -/
example : (found.run splitByAgeFixed).outputs.allOk = true ∧
    ((found.run splitByAgeFixed).db.run allCustomers).outputs.getLast? = some (.rows [[1, "", .null]]) := by
  decide +kernel

/-- The migration with the mistake does not preserve the read on {name}`shop`: {name}`found` is a
database with the schema on which the read changes. -/
theorem split_loses_null_age : ¬ (splitByAge preserves allCustomers on shop) := by
  sql_refute (db := found)

#print axioms split_loses_null_age

end SplitByAge
