import SelectJoinCases

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance case A06 of ADR 0027, through the left, right and full join rules over every
database with the catalog of {lit}`shop`: the matched rows of an outer join are those of the inner
join; a left join adds each order without a match with a NULL name, a right join each customer
without a matching order with a NULL id, and a full join both. Contrast: the NOT NULL constraint
of {lit}`customers.name` does not make the names of a left join non-NULL. -/

namespace SelectJoinCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases (cell)

/-- The result rows of the orders of a left join: for each order in scan order, its
{name}`matchedPairs` part, or, when no customer matches it ({name}`Matches`), its id with a NULL
name. -/
def paddedPairs (db : Database) : List (List Value) :=
  (orderRows db).flatMap fun order =>
    if (customerRows db).any (Matches order) then
      ((customerRows db).filter (Matches order)).map fun customer => [cell 0 order, cell 1 customer]
    else [[cell 0 order, .null]]

/-- The result rows that a right join adds: a NULL id with the name of each customer that no order
matches, in scan order. -/
def unmatchedCustomers (db : Database) : List (List Value) :=
  ((customerRows db).filter fun customer => !(orderRows db).any fun order => Matches order customer).map
    fun customer => [.null, cell 1 customer]

/-- The result rows of the padded part of a left or full join: {name}`paddedPairs`. Proof sketch:
an order without a match is followed by two NULL cells; one with a match gives its
{name}`Resolved.matchedRows`, as in {name}`matched_map`. -/
theorem padded_map (kind : Resolved.JoinKind) (db : Database) (schema : db.HasCatalog shop) :
    ((orderRows db).flatMap (Resolved.paddedRows (Resolved.EvalContext.bound []) (customerJoin kind) 2 (customerRows db))).map
      (fun row => [cell 0 row, cell 4 row]) = paddedPairs db := by
  rw [List.map_flatMap, paddedPairs]
  refine flatMap_congr_mem fun order member => ?_
  have wide := (rows_width db schema).1 order member
  have same : (Resolved.matchedRows (Resolved.EvalContext.bound []) (customerJoin kind) (customerRows db) order).isEmpty =
      !(customerRows db).any (Matches order) := by
    cases any : (customerRows db).any (Matches order) <;>
      simp_all [Resolved.matchedRows, matches_kind, List.filter_eq_nil_iff, List.any_eq_false, List.any_eq_true]
  unfold Resolved.paddedRows
  rw [same]
  cases (customerRows db).any (Matches order)
  · simp [Resolved.Expr.eval_column, wide]
  · simpa using matchedRows_map kind (customerRows db) wide

/-- The result rows of the unmatched part of a right or full join: {name}`unmatchedCustomers`.
Proof sketch: an added row is three NULL cells followed by the customer. -/
theorem unmatched_map (kind : Resolved.JoinKind) (db : Database) :
    (Resolved.unmatchedRows (Resolved.EvalContext.bound []) (customerJoin kind) 3 (orderRows db) (customerRows db) []).map
      (fun row => [cell 0 row, cell 4 row]) = unmatchedCustomers db := by
  simp only [Resolved.unmatchedRows, Resolved.unmatchedRight, unmatchedCustomers, List.map_map]
  refine List.map_congr_left fun customer _ => ?_
  simp [Resolved.Expr.eval_column]

/-- The left join query of A06. -/
def leftScript : Script := sql r"SELECT o.id, c.name FROM orders o LEFT JOIN customers c ON c.id = o.customer_id"

/-- The right join query of A06. -/
def rightScript : Script := sql r"SELECT o.id, c.name FROM orders o RIGHT JOIN customers c ON c.id = o.customer_id"

/-- The full join query of A06. -/
def fullScript : Script := sql r"SELECT o.id, c.name FROM orders o FULL JOIN customers c ON c.id = o.customer_id"

/-- A06 for a left join: for every database with the catalog of {name}`shop` and every environment,
the left join returns a permutation of {name}`paddedPairs`: each order with each matching customer,
and each order without a match once, with a NULL name. Proof sketch: {name}`joined_returns`,
{name}`Resolved.joinRows_left` and {name}`padded_map`. -/
theorem left_join (db : Database) (env : Env) (schema : db.HasCatalog shop) :
    (db.run (query leftScript rfl) env).returnsResult fun result => result.Perm (paddedPairs db) :=
  joined_returns .left leftScript rfl _ rfl (by decide +kernel) db env schema _ fun result perm => by
    rwa [Resolved.joinRows_left _ rfl, padded_map .left db schema] at perm

/-- A06 for a right join: for every database with the catalog of {name}`shop` and every environment,
the right join returns a permutation of {name}`matchedPairs` followed by {name}`unmatchedCustomers`:
each order with each matching customer, then each customer that no order matches once, with a NULL
id. Proof sketch: {name}`joined_returns`, {name}`Resolved.joinRows_right`, {name}`matched_map` and
{name}`unmatched_map`. -/
theorem right_join (db : Database) (env : Env) (schema : db.HasCatalog shop) :
    (db.run (query rightScript rfl) env).returnsResult fun result =>
      result.Perm (matchedPairs db ++ unmatchedCustomers db) :=
  joined_returns .right rightScript rfl _ rfl (by decide +kernel) db env schema _ fun result perm => by
    rwa [Resolved.joinRows_right _ rfl, List.map_append, matched_map .right db schema, unmatched_map] at perm

/-- A06 for a full join: for every database with the catalog of {name}`shop` and every environment,
the full join returns a permutation of {name}`paddedPairs` followed by {name}`unmatchedCustomers`.
Proof sketch: as {name}`right_join`, with {name}`Resolved.joinRows_full` and {name}`padded_map`. -/
theorem full_join (db : Database) (env : Env) (schema : db.HasCatalog shop) :
    (db.run (query fullScript rfl) env).returnsResult fun result =>
      result.Perm (paddedPairs db ++ unmatchedCustomers db) :=
  joined_returns .full fullScript rfl _ rfl (by decide +kernel) db env schema _ fun result perm => by
    rwa [Resolved.joinRows_full _ rfl, List.map_append, padded_map .full db schema, unmatched_map] at perm

/-- A06 instances and contrast: on {name}`partial_` the left join keeps orders 2 and 3 with a NULL
name, the right join adds {lit}`zeta` with a NULL id, and the full join does both. The column
{lit}`customers.name` is NOT NULL, but the left join does not return a result whose names are all
non-NULL. The run returns each result as a multiset in the order of the output normal form, NULL
first. Native SQLite 3.51.0 gives the same rows, in its own order. -/
example : (partial_.run (query leftScript rfl)).returnsResult (· = [[.integer 1, .text "acme".toUTF8.toList],
    [.integer 2, .null], [.integer 3, .null]]) := by
  decide +kernel

example : (partial_.run (query rightScript rfl)).returnsResult (· = [[.null, .text "zeta".toUTF8.toList],
    [.integer 1, .text "acme".toUTF8.toList]]) := by
  decide +kernel

example : (partial_.run (query fullScript rfl)).returnsResult (· = [[.null, .text "zeta".toUTF8.toList],
    [.integer 1, .text "acme".toUTF8.toList], [.integer 2, .null], [.integer 3, .null]]) := by
  decide +kernel

example : ¬ (partial_.run (query leftScript rfl)).returnsResult (fun result => ∀ row ∈ result, row[1]? ≠ some .null) := by
  decide +kernel

#print axioms padded_map
#print axioms unmatched_map
#print axioms left_join
#print axioms right_join
#print axioms full_join

end SelectJoinCases
