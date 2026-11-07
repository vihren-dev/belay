import SelectJoinSupport

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance cases A05 and A06 of ADR 0027, through the join rules
({lit}`Resolved.joinRows_inner`, {lit}`Resolved.joinRows_left`, {lit}`Resolved.joinRows_right`,
{lit}`Resolved.joinRows_full`) over every database with the catalog of {lit}`shop`: an inner join
gives each order with each customer that matches it, and as many rows as orders when each order has
exactly one match; a left join keeps each order, with a NULL name when no customer matches it; a
right join adds each customer that no order matches, with a NULL id; a full join does both. -/

namespace SelectJoinCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases (cell)

/-- For every order row of three cells and customer row, the cells 0 and 4 of the joined row are
the order's id and the customer's name. -/
theorem cells_append {order customer : List Value} (wide : order.length = 3) :
    cell 0 (order ++ customer) = cell 0 order ∧ cell 4 (order ++ customer) = cell 1 customer := by
  simp [Resolved.Expr.eval_column, List.getElem?_append_left (by omega : 0 < order.length),
    List.getElem?_append_right (by omega : order.length ≤ 4), wide]

/-- The result rows of the orders joined with their matching customers: for each order in scan
order, its id with the name of each customer that matches it ({name}`Matches`), in scan order. -/
def matchedPairs (db : Database) : List (List Value) :=
  (orderRows db).flatMap fun order =>
    ((customerRows db).filter (Matches order)).map fun customer => [cell 0 order, cell 1 customer]

/-- For every join kind, joined row and customer, the join condition of {name}`customerJoin` does not
depend on the kind: it is {name}`Matches`. -/
theorem matches_kind (kind : Resolved.JoinKind) (order customer : List Value) :
    (customerJoin kind).matches (Resolved.EvalContext.bound []) (order ++ customer) = Matches order customer := rfl

/-- For every join kind and order of three cells, the result rows of the order's matches
({name}`Resolved.matchedRows`) are its id with the name of each matching customer. Proof sketch:
{name}`cells_append`. -/
theorem matchedRows_map (kind : Resolved.JoinKind) (customers : List (List Value)) {order : List Value}
    (wide : order.length = 3) :
    (Resolved.matchedRows (Resolved.EvalContext.bound []) (customerJoin kind) customers order).map
      (fun row => [cell 0 row, cell 4 row]) =
      (customers.filter (Matches order)).map fun customer => [cell 0 order, cell 1 customer] := by
  simp only [Resolved.matchedRows, List.map_map, matches_kind]
  refine List.map_congr_left fun customer _ => ?_
  obtain ⟨id, name⟩ := cells_append (customer := customer) wide
  simp only [Function.comp_apply, id, name]

/-- The result rows of the matched part of a join: {name}`matchedPairs`. Proof sketch: each joined
row is an order of three cells followed by a customer ({name}`matchedRows_map`). -/
theorem matched_map (kind : Resolved.JoinKind) (db : Database) (schema : db.HasCatalog shop) :
    ((orderRows db).flatMap (Resolved.matchedRows (Resolved.EvalContext.bound []) (customerJoin kind) (customerRows db))).map
      (fun row => [cell 0 row, cell 4 row]) = matchedPairs db := by
  rw [List.map_flatMap, matchedPairs]
  exact flatMap_congr_mem fun order member => matchedRows_map kind _ ((rows_width db schema).1 order member)

/-- The inner join query of A05. -/
def innerScript : Script := sql r"SELECT o.id, c.name FROM orders o JOIN customers c ON c.id = o.customer_id"

/-- The inner join query has one statement. -/
theorem innerScript_one : innerScript.statements.length = 1 := rfl

/-- A05: for every database with the catalog of {name}`shop` and every environment, the inner join
returns a result that is a permutation of {name}`matchedPairs`: each order once for each customer
that matches it, and no order without a match. Proof sketch: {name}`Run.query_returnsResult_calm`
through {name}`joined_returns`, then {name}`Resolved.joinRows_inner` and
{name}`matched_map`. -/
theorem inner_join (db : Database) (env : Env) (schema : db.HasCatalog shop) :
    (db.run (query innerScript innerScript_one) env).returnsResult fun result => result.Perm (matchedPairs db) :=
  joined_returns .inner innerScript innerScript_one _ rfl (by decide +kernel) db env schema _ fun result perm => by
    rwa [Resolved.joinRows_inner _ rfl, matched_map .inner db schema] at perm

/-- A05 cardinality: for every database with the catalog of {name}`shop` and every environment, when
exactly one customer matches each order, the inner join returns a result with as many rows as
orders. Proof sketch: {name}`inner_join` gives a permutation of the join, whose length
{name}`Resolved.joinRows_inner_length_of_unique` gives. -/
theorem inner_join_unique (db : Database) (env : Env) (schema : db.HasCatalog shop)
    (unique : ∀ order ∈ orderRows db, (customerRows db).countP (Matches order) = 1) :
    (db.run (query innerScript innerScript_one) env).returnsResult fun result => result.length = (orderRows db).length := by
  refine (inner_join db env schema).mono fun result perm => ?_
  rw [perm.length_eq, ← matched_map .inner db schema, List.length_map, ← Resolved.joinRows_inner _ rfl 3 _ 2 _ [],
    Resolved.joinRows_inner_length_of_unique _ rfl 3 2 [] unique]

/-- An order whose customer exists, one whose customer is missing, one without a customer, and a
customer without an order. -/
def partial_ : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT NOT NULL);
  CREATE TABLE orders (id INTEGER PRIMARY KEY, customer_id INTEGER, amount INTEGER NOT NULL);
  INSERT INTO customers VALUES (1, 'acme'), (2, 'zeta');
  INSERT INTO orders VALUES (1, 1, 10), (2, 9, 5), (3, NULL, 7);"

/-- The join of each order with every customer whose id is at most the order's customer. -/
def atMostScript : Script := sql r"SELECT o.id, c.name FROM orders o JOIN customers c ON c.id <= o.customer_id"

/-- A05 contrast: a missing match removes rows, and multiple matches multiply them. On
{name}`partial_` the inner join returns only order 1 of three orders; the join on
{lit}`c.id <= o.customer_id` returns order 2 twice, once for each customer. Native SQLite 3.51.0
gives the same rows. -/
example : (partial_.run (query innerScript innerScript_one)).returnsResult (· = [[.integer 1, .text "acme".toUTF8.toList]]) ∧
    (partial_.run (query atMostScript rfl)).returnsResult (· = [[.integer 1, .text "acme".toUTF8.toList],
      [.integer 2, .text "acme".toUTF8.toList], [.integer 2, .text "zeta".toUTF8.toList]]) := by
  decide +kernel

#print axioms matched_map
#print axioms inner_join
#print axioms inner_join_unique

end SelectJoinCases
