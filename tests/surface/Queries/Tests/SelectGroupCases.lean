import SelectGroupSupport

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance cases of the group rules of ADR 0027: A07, {lit}`GROUP BY` with a column term and with an
expression term over every database with the catalog of {lit}`orders`, with a witness and the contrasts
of collated keys and of a grouping key that can fail. -/

namespace SelectGroupCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- The count query of a grouping term: the rows of the table at catalog position 0 grouped by the
term under the collation, with the term's value and {lit}`count(*)` of each group, sorted by the
count, descending. -/
def countQuery (term : Resolved.Expr) (collation : Collation) (names : List String) : Resolved.Query :=
  { sources := [.first 0], filter := none, aggregate := true, groupBy := [(term, collation)],
    columns := [.scalar term, .aggregate .countRows], names,
    orderBy := [{ key := .output 1, descending := true }], offset := 0, limit := none }

/-- The A07 result of a grouping by a key with the count of each group, most rows first, over the
rows {lit}`rows`: there are groups {lit}`found`, in the order of the result, such that
- they are a partition of the rows by the key ({name}`KeyPartition`);
- some choice {lit}`pick` of one row of each group gives the result: for each group, the key of its
  row and the number of its rows;
- no group has fewer rows than a later group.

The row of a group that {lit}`pick` chooses is the model's choice ({name}`Resolved.Query.groupRow`).
Under a collation the keys of the rows of a group can differ as values; native SQLite can read
another row where its plan decides (issue #309). -/
def KeyCounts (key : List Value → Value) (collation : Collation) (rows result : List (List Value)) : Prop :=
  ∃ found : List (List (List Value)), KeyPartition key collation rows found ∧
    (∃ pick : List (List Value) → List Value, (∀ group ∈ found, pick group ∈ group) ∧
      result = found.map fun group => [key (pick group), .integer group.length]) ∧
    found.Pairwise fun earlier later => later.length ≤ earlier.length

/-- Group rule of A07 for every term: for every grouping term, collation, names, rows and result that
the model permits for the count query of the term ({name}`countQuery`) in the context without
parameters, the result is {name}`KeyCounts` of the term's value. Proof sketch:
{name}`Resolved.Query.exists_sorted_perm_of_mem_possibleResults` gives the sorted records, a
permutation of the records of the groups ({name}`uniqueRecords_grouped`);
{name}`Resolved.exists_perm_map_eq` moves the groups into the order of the result;
{name}`keyPartition_groups` and {name}`Resolved.Query.groupRow_mem` give the partition and the row of
each group, and the sort values are the counts. -/
theorem keyCounts_of_mem (term : Resolved.Expr) (collation : Collation) (names : List String)
    {rows result : List (List Value)}
    (member : result ∈ (countQuery term collation names).possibleResults (Resolved.EvalContext.bound []) rows) :
    KeyCounts (term.eval (Resolved.EvalContext.bound [])) collation rows result := by
  obtain ⟨ordered, perm, sorted, rfl⟩ := Resolved.Query.exists_sorted_perm_of_mem_possibleResults rfl rfl member
  rw [uniqueRecords_grouped rfl rfl rfl rfl rfl,
    (List.filter_eq_self (p := (countQuery term collation names).keepsGroup _)).mpr (fun _ _ => rfl)] at perm
  obtain ⟨moved, movedPerm, rfl⟩ := Resolved.exists_perm_map_eq _ perm
  have partition := (keyPartition_groups term collation rows).perm movedPerm
  refine ⟨moved, partition, ⟨(countQuery term collation names).groupRow (Resolved.EvalContext.bound []),
    fun group member => Resolved.Query.groupRow_mem _ _ (partition.ne_nil member), ?_⟩, ?_⟩
  · simp only [List.map_map]
    refine List.map_congr_left fun group _ => ?_
    rfl
  · rw [List.pairwise_map] at sorted
    refine sorted.imp fun {earlier later} le => ?_
    have isLE : (compare (later.length : Int) earlier.length).isLE = true := by
      simpa [Resolved.Query.groupRecord, countQuery, Resolved.compareSort, Resolved.compareTerm,
        Collation.compare_integer, Resolved.countRows_eval] using le
    exact Int.ofNat_le.mp (Int.isLE_compare.mp isLE)

/-- For every term, collation, names and rows, the count query has no failing aggregate
({name}`Resolved.Query.fails`): {lit}`count(*)` cannot fail. Proof sketch: the only aggregate is
{lit}`count(*)`, whose failure is false ({name}`Resolved.Aggregate.fails_countRows`). -/
theorem countQuery_fails (term : Resolved.Expr) (collation : Collation) (names : List String)
    (rows : List (List Value)) :
    (countQuery term collation names).fails (Resolved.EvalContext.bound []) rows = false := by
  simp [Resolved.Query.fails, countQuery, Resolved.Aggregate.fails_countRows]

/-- The A07 query with a column term: the number of orders of each customer, most orders first. -/
def byCustomer : Script := sql r"SELECT customer, count(*) FROM orders GROUP BY customer ORDER BY 2 DESC"

/-- The A07 query with a column term has one statement. -/
theorem byCustomer_one : byCustomer.statements.length = 1 := rfl

/-- A07 with a column term: for every database with the catalog of {name}`orders` and every
environment, {name}`byCustomer` returns a result, and the result is {name}`KeyCounts` of the
customer cell under {lit}`NOCASE` over the stored rows of {lit}`orders` ({name}`ordersRows`). The
table can have any rows, also none: then there is no group and the result is empty. Proof sketch:
for the catalog the statement resolves to {name}`countQuery` of the column, which is calm;
{name}`Run.query_returnsResult_calmTable` reduces the claim to the possible results over the scan,
and {name}`keyCounts_of_mem` gives it. -/
theorem customer_counts (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (db.run (query byCustomer byCustomer_one) env).returnsResult
      (KeyCounts (·.getD 1 .null) .nocase (ordersRows db)) := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState
      (match byCustomer.statements with | (statement, _) :: _ => statement | [] => .begin) =
      .ok (.query (countQuery (.column 1) .nocase ["customer", "count(*)"]) [],
        (db.raw.connection env.counters).resolveState) := by
    rw [orders_state db env schema]
    decide +kernel
  rw [Run.query_returnsResult_calmTable (script := byCustomer) rfl byCustomer_one db env resolved rfl
    (Database.table_of_findTable db.raw _ _ _ (orders_found db schema)) (by unfold Resolved.Statement.Calm; decide)
    rfl rfl rfl (countQuery_fails _ _ _ _) rfl]
  exact fun result member => keyCounts_of_mem _ _ _ member

/-- The A07 query with an expression term: the number of orders above 5 and of the others, the larger
number first. -/
def byLarge : Script := sql r"SELECT amount > 5, count(*) FROM orders GROUP BY amount > 5 ORDER BY 2 DESC"

/-- The A07 query with an expression term has one statement. -/
theorem byLarge_one : byLarge.statements.length = 1 := rfl

/-- The term {lit}`amount > 5` of {name}`byLarge`, with the integer affinity of the column. -/
def largeTerm : Resolved.Expr := .compare .gt (some .integer) (.column 2) (.literal (.integer 5))

/-- A07 with an expression term: for every database with the catalog of {name}`orders` and every
environment, {name}`byLarge` returns a result, and the result is {name}`KeyCounts` of the value of
{lit}`amount > 5` ({name}`largeTerm`) over the stored rows. Proof sketch: as
{name}`customer_counts`, with the count query of the expression. -/
theorem large_counts (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (db.run (query byLarge byLarge_one) env).returnsResult
      (KeyCounts (largeTerm.eval (Resolved.EvalContext.bound [])) .binary (ordersRows db)) := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState
      (match byLarge.statements with | (statement, _) :: _ => statement | [] => .begin) =
      .ok (.query (countQuery largeTerm .binary ["amount > 5", "count(*)"]) [],
        (db.raw.connection env.counters).resolveState) := by
    rw [orders_state db env schema]
    decide +kernel
  rw [Run.query_returnsResult_calmTable (script := byLarge) rfl byLarge_one db env resolved rfl
    (Database.table_of_findTable db.raw _ _ _ (orders_found db schema)) (by unfold Resolved.Statement.Calm; decide)
    rfl rfl rfl (countQuery_fails _ _ _ _) rfl]
  exact fun result member => keyCounts_of_mem _ _ _ member

/-- A07 witness: {name}`mixed` has the catalog of {name}`orders`; {name}`byCustomer` returns the two
customers with 2 and 1 orders, and {name}`byLarge` returns the two values of {lit}`amount > 5` with
2 and 1 orders. The customer of the group of {lit}`acme` is the cell of its first row in the model. -/
theorem counts_witness :
    mixed.HasCatalog orders ∧
      (mixed.run (query byCustomer byCustomer_one)).returnsResult
        (· = [[.text [97, 99, 109, 101], .integer 2], [.text [122, 101, 116, 97], .integer 1]]) ∧
      (mixed.run (query byLarge byLarge_one)).returnsResult (· = [[.integer 1, .integer 2], [.integer 0, .integer 1]]) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- A07 contrast: collated key equality does not make equal values. The first two stored rows of
{name}`mixed` have the same customer under {lit}`NOCASE`, so they are in one group, but their
customer cells differ. -/
theorem collated_contrast :
    SameKey (·.getD 1 .null) .nocase ((ordersRows mixed).getD 0 []) ((ordersRows mixed).getD 1 []) ∧
      ((ordersRows mixed).getD 0 []).getD 1 .null ≠ ((ordersRows mixed).getD 1 []).getD 1 .null := by
  unfold SameKey
  decide +kernel

/-- A query whose grouping term can fail: {lit}`abs` of the least 64-bit integer has no 64-bit
integer. -/
def byAbsolute : Script := sql r"SELECT count(*) FROM orders GROUP BY abs(amount)"

/-- The fallible-key query has one statement. -/
theorem byAbsolute_one : byAbsolute.statements.length = 1 := rfl

/-- An order whose amount is the least 64-bit integer. -/
def extreme : Database := db! r"
  CREATE TABLE orders (id INTEGER PRIMARY KEY, customer TEXT NOT NULL COLLATE NOCASE, amount INTEGER NOT NULL);
  INSERT INTO orders VALUES (1, 'acme', -9223372036854775808);"

/-- A07 contrast: a grouping key that can fail is a fault obligation. The run of {name}`byAbsolute`
over {name}`extreme` returns neither a result nor an error: the model does not describe the step, so
no claim about its groups holds there. -/
theorem fallible_key_contrast :
    extreme.HasCatalog orders ∧ ¬ (extreme.run (query byAbsolute byAbsolute_one)).returnsResult (fun _ => True) ∧
      ¬ (extreme.run (query byAbsolute byAbsolute_one)).returnsError (fun _ => True) :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

#print axioms keyCounts_of_mem
#print axioms customer_counts
#print axioms large_counts
#print axioms counts_witness
#print axioms collated_contrast
#print axioms fallible_key_contrast

end SelectGroupCases
