import SelectGroupSupport

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance case A10 of the {lit}`HAVING` rule of ADR 0027: {lit}`HAVING count(*) > 1` keeps exactly
the groups of more than one row, over every database with the catalog of {lit}`orders`, with a
witness, the contrast of a NULL condition, and a condition on the row of a group, which is a model
claim (issue #309). -/

namespace SelectHavingCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases

/-- The query of a grouping column with a count condition: the rows of the table at catalog position 0
grouped by the column at the index under the collation, the column's cell and {lit}`count(*)` of each group whose
count is more than the threshold. -/
def havingQuery (index : Nat) (collation : Collation) (names : List String) (threshold : Int) :
    Resolved.Query :=
  { sources := [.first 0], filter := none, aggregate := true, groupBy := [(.column index, collation)],
    columns := [.scalar (.column index), .aggregate .countRows], names, orderBy := [], offset := 0, limit := none,
    aggregates := [.countRows], having := some (.compare .gt none (.aggregateValue 0) (.literal (.integer threshold))) }

/-- The A10 result of a grouping by a key that keeps the groups of more than {lit}`threshold` rows,
over the rows {lit}`rows`: there are groups {lit}`all`, a partition of the rows by the key
({name}`KeyPartition`), and some choice {lit}`pick` of one row of each group, such that the result
is a permutation of the key of the picked row and the number of rows of each group of {lit}`all`
that has more than {lit}`threshold` rows, in the order of {lit}`all`. A group of at most
{lit}`threshold` rows gives no row. -/
def KeptCounts (key : List Value → Value) (collation : Collation) (threshold : Int) (rows result : List (List Value)) :
    Prop :=
  ∃ all : List (List (List Value)), KeyPartition key collation rows all ∧
    ∃ pick : List (List Value) → List Value, (∀ group ∈ all, pick group ∈ group) ∧
      result.Perm ((all.filter fun group => decide (threshold < group.length)).map fun group =>
        [key (pick group), .integer group.length])

/-- For every context of a group whose first aggregate value is the integer {lit}`count`, every row and
threshold, the condition {lit}`count(*) > threshold` of {name}`havingQuery` is true exactly when
{lit}`count` is more than the threshold. Proof sketch: the comparison of two integers without affinity
is the order of the integers ({name}`Collation.compare_integer`). -/
theorem countCondition_truthy (context : Resolved.EvalContext) (row : List Value) (count threshold : Int)
    (first : context.aggregates.getD 0 .null = .integer count) :
    Resolved.truthy ((Resolved.Expr.compare .gt none (.aggregateValue 0) (.literal (.integer threshold))).eval context row) =
      decide (threshold < count) := by
  have value : (Resolved.Expr.aggregateValue 0).eval context row = .integer count := first
  rw [Resolved.Expr.eval_compare, value, Resolved.Expr.eval_literal]
  simp only [Resolved.comparisonOperands, Comparison.apply, Collation.compare_integer, Comparison.holds, Resolved.truthy]
  by_cases above : threshold < count <;> simp [above, Value.isNull, truth, Int.compare_eq_gt]

/-- Having rule of A10 for every column: for every index of a grouping column, collation, names, threshold, rows and
result that the model permits for {name}`havingQuery` in the context without parameters, the result
is {name}`KeptCounts` of the column's cell. Proof sketch:
{name}`Resolved.Query.perm_of_mem_possibleResults` gives a permutation of the records, the records of
the groups that {lit}`HAVING` keeps ({name}`uniqueRecords_grouped`); the condition of a group reads
its count ({name}`countCondition_truthy`), and {name}`keyPartition_groups` and
{name}`Resolved.Query.groupRow_mem` give the partition and the row of each group. -/
theorem keptCounts_of_mem (index : Nat) (collation : Collation) (names : List String) (threshold : Int)
    {rows result : List (List Value)}
    (member : result ∈ (havingQuery index collation names threshold).possibleResults (Resolved.EvalContext.bound []) rows) :
    KeptCounts (·.getD index .null) collation threshold rows result := by
  have perm := Resolved.Query.perm_of_mem_possibleResults rfl rfl member
  rw [uniqueRecords_grouped rfl rfl rfl rfl rfl] at perm
  have partition := keyPartition_groups (.column index) collation rows
  refine ⟨_, partition, (havingQuery index collation names threshold).groupRow (Resolved.EvalContext.bound []),
    fun group member => Resolved.Query.groupRow_mem _ _ (partition.ne_nil member), perm.trans ?_⟩
  rw [List.map_map]
  have keeps : ∀ group, (havingQuery index collation names threshold).keepsGroup (Resolved.EvalContext.bound []) group =
      decide (threshold < group.length) := fun group => by
    simp only [Resolved.Query.keepsGroup, havingQuery, Option.all_some]
    exact countCondition_truthy _ _ group.length threshold (by simp [Resolved.Query.groupContext, Resolved.countRows_eval])
  rw [List.filter_congr fun group _ => keeps group]
  exact List.Perm.of_eq (List.map_congr_left fun group _ => rfl)

/-- The A10 query: the customers with more than one order and their numbers of orders. -/
def repeatCustomers : Script := sql r"SELECT customer, count(*) FROM orders GROUP BY customer HAVING count(*) > 1"

/-- The A10 query has one statement. -/
theorem repeatCustomers_one : repeatCustomers.statements.length = 1 := rfl

/-- A10 with the catalog fact: for every database with the catalog of {name}`orders` and every
environment, {name}`repeatCustomers` returns a result, and the result is {name}`KeptCounts` of the
customer cell under {lit}`NOCASE` with the threshold 1 over the stored rows of {lit}`orders`
({name}`ordersRows`): exactly the groups of more than one order give a row. Proof sketch: for the
catalog the statement resolves to {name}`havingQuery` of the customer column, which is calm and has
no failing aggregate; {name}`Run.query_returnsResult_calmTable` and {name}`keptCounts_of_mem`. -/
theorem repeat_customers (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (db.run (query repeatCustomers repeatCustomers_one) env).returnsResult
      (KeptCounts (·.getD 1 .null) .nocase 1 (ordersRows db)) := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState
      (match repeatCustomers.statements with | (statement, _) :: _ => statement | [] => .begin) =
      .ok (.query (havingQuery 1 .nocase ["customer", "count(*)"] 1) [],
        (db.raw.connection env.counters).resolveState) := by
    rw [orders_state db env schema]
    decide +kernel
  rw [Run.query_returnsResult_calmTable (script := repeatCustomers) rfl repeatCustomers_one db env resolved rfl
    (Database.table_of_findTable db.raw _ _ _ (orders_found db schema)) (by unfold Resolved.Statement.Calm; decide)
    rfl rfl rfl (by simp [Resolved.Query.fails, havingQuery, Resolved.Aggregate.fails_countRows]) rfl]
  exact fun result member => keptCounts_of_mem _ _ _ _ member

/-- A10 witness: on {name}`mixed`, {name}`repeatCustomers` returns only the customer {lit}`acme`, whose
two orders are written {lit}`'acme'` and {lit}`'ACME'`, with the count 2. -/
theorem repeat_witness :
    (mixed.run (query repeatCustomers repeatCustomers_one)).returnsResult
      (· = [[.text [97, 99, 109, 101], .integer 2]]) := by
  decide +kernel

/-- A {lit}`HAVING` condition that is NULL. -/
def nullHaving : Script := sql r"SELECT customer FROM orders GROUP BY customer HAVING NULL"

/-- The NULL-condition query has one statement. -/
theorem nullHaving_one : nullHaving.statements.length = 1 := rfl

/-- A10 contrast: a NULL condition does not keep a group. {name}`mixed` has two groups, and
{name}`nullHaving` returns no row there. -/
theorem null_having_contrast : (mixed.run (query nullHaving nullHaving_one)).returnsResult (· = []) := by
  decide +kernel

/-- A {lit}`HAVING` condition on the row of a group: the customer cell compared without the collation
of the column. -/
def exactHaving : Script := sql r"SELECT count(*) FROM orders GROUP BY customer HAVING customer = 'ACME' COLLATE BINARY"

/-- The row-condition query has one statement. -/
theorem exactHaving_one : exactHaving.statements.length = 1 := rfl

/-- A10 model claim: a condition on the row of a group reads the model's row
({name}`Resolved.Query.groupRow`). On {name}`mixed` the model reads the first order of {lit}`acme`,
written {lit}`'acme'`, so the condition is false for every group and the result is empty. In native
SQLite the plan decides the row (issue #309): over a full scan of the table it keeps the group of
{lit}`acme`, and over an index on {lit}`customer` it keeps no group, as the model does. The claim
holds of the model and of some plans, not of every plan. -/
theorem group_row_claim : (mixed.run (query exactHaving exactHaving_one)).returnsResult (· = []) := by
  decide +kernel

#print axioms countCondition_truthy
#print axioms keptCounts_of_mem
#print axioms repeat_customers
#print axioms repeat_witness
#print axioms null_having_contrast
#print axioms group_row_claim

end SelectHavingCases
