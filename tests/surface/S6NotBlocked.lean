import S6CheckLabels

/-! A fixture module of `tests/surface_s6_check_programs_test.py`: the guide's query equivalence of
{lit}`NOT IN` and {lit}`NOT EXISTS` (ADR 0017, S6). The two queries select the customers that no row of
{lit}`blocked` names. They are not equivalent in general. Three databases show it, and the checker refutes the
equivalence on each of them with a replay in SQLite:

- a NULL {lit}`blocked.customer_id` makes {lit}`NOT IN` drop every row;
- a NULL {lit}`customers.id` with a non-NULL blocked id makes {lit}`NOT IN` drop that row, and {lit}`NOT EXISTS`
  keeps it;
- a text key of {lit}`customers.id` with the collation BINARY and a blocked id with the collation NOCASE:
  {lit}`IN` takes the collation of its left operand and {lit}`=` of its left operand, which is the other column.

A fourth database meets the sufficient premises: the customers table has a rowid alias, which is never NULL and
always an integer, and no blocked id is NULL. The two queries give the same outputs there. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048
set_option sql.check false

namespace S6NotBlocked
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- The customers that no row of {lit}`blocked` names, by {lit}`NOT IN`. -/
def notBlockedIn : Script := sql r"SELECT id FROM customers WHERE id NOT IN (SELECT customer_id FROM blocked)"

/-- The customers that no row of {lit}`blocked` names, by {lit}`NOT EXISTS`. -/
def notBlockedExists : Script :=
  sql r"SELECT id FROM customers c WHERE NOT EXISTS (SELECT 1 FROM blocked b WHERE b.customer_id = c.id)"

/-- A blocked id is NULL. -/
def nullBlocked : Database := db! r"
  CREATE TABLE customers(id INTEGER PRIMARY KEY, name TEXT, email TEXT);
  CREATE TABLE blocked(customer_id INTEGER);
  INSERT INTO customers VALUES(1, 'ann', 'a@x');
  INSERT INTO blocked VALUES(NULL);"

/-- A customer id is NULL, and the blocked id is not. -/
def nullCustomer : Database := db! r"
  CREATE TABLE customers(id INTEGER, name TEXT, email TEXT);
  CREATE TABLE blocked(customer_id INTEGER);
  INSERT INTO customers VALUES(NULL, 'ann', 'a@x');
  INSERT INTO blocked VALUES(5);"

/-- The key columns are text with different collations: BINARY for the customer, NOCASE for the blocked id. -/
def collations : Database := db! r"
  CREATE TABLE customers(id TEXT COLLATE BINARY, name TEXT, email TEXT);
  CREATE TABLE blocked(customer_id TEXT COLLATE NOCASE);
  INSERT INTO customers VALUES('a', 'ann', 'a@x');
  INSERT INTO blocked VALUES('A');"

/-- The premises hold: the customers table has a rowid alias, and no blocked id is NULL. -/
def premisesHold : Database := db! r"
  CREATE TABLE customers(id INTEGER PRIMARY KEY, name TEXT, email TEXT);
  CREATE TABLE blocked(customer_id INTEGER);
  INSERT INTO customers VALUES(1, 'ann', 'a@x'), (2, 'bob', 'b@x');
  INSERT INTO blocked VALUES(2);"

/-- A complete environment: a constant clock and the counters after the setup. -/
def environment : Env :=
  { clock := some (fun _ => 0)
    counters := { changes := some 1, totalChanges := some 1, lastInsertRowid := some 1 } }

/-- The outputs of a script on a database, from the initial context of the database and the environment. -/
def outputsOn (script : Script) (db : Database) : List Output :=
  let start := ExecutionContext.initial db environment
  ((send script).runFrom start.clock start.index start.connection).outputs

/-- On the database that meets the premises, the two queries give the same outputs. This is one instance: it
is no proof that the premises suffice for every database. Proof sketch: kernel evaluation of both runs. -/
theorem premises_give_equal_outputs : outputsOn notBlockedIn premisesHold = outputsOn notBlockedExists premisesHold := by
  decide +kernel

set_option sql.checkBudget 400000 in
labelled_sql "null-blocked" in
#sql_check ∀ env : Env, env.Complete →
  Sql.EquivAt (send notBlockedIn) (send notBlockedExists) (ExecutionContext.initial nullBlocked env)

set_option sql.checkBudget 400000 in
labelled_sql "null-customer" in
#sql_check ∀ env : Env, env.Complete →
  Sql.EquivAt (send notBlockedIn) (send notBlockedExists) (ExecutionContext.initial nullCustomer env)

set_option sql.checkBudget 400000 in
labelled_sql "collations" in
#sql_check ∀ env : Env, env.Complete →
  Sql.EquivAt (send notBlockedIn) (send notBlockedExists) (ExecutionContext.initial collations env)

#print axioms premises_give_equal_outputs

end S6NotBlocked
