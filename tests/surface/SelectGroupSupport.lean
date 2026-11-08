import Belay

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Support of the A07 to A10 acceptance cases of ADR 0027: the table {lit}`orders`, the partition of
rows by a key ({lit}`KeyPartition`), the record rule of a query with one grouping term, the truth of a
count condition and the result rule of an ungrouped aggregate query. -/

namespace SelectGroupCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- A table {lit}`orders` whose customer names compare without case ({lit}`NOCASE`), with no rows. -/
def orders : Database := db! r"
  CREATE TABLE orders (id INTEGER PRIMARY KEY, customer TEXT NOT NULL COLLATE NOCASE, amount INTEGER NOT NULL);"

/-- The table of {lit}`orders` in {name}`orders`. -/
def ordersShape : CatalogTable := ((orders.raw.catalog.findTable (name! "orders")).get (by decide +kernel)).2

/-- The rows of {lit}`orders` in a database, in the order of a full scan, as lists of values. -/
def ordersRows (db : Database) : List (List Value) :=
  Resolved.sourceRows { shape := ordersShape, rows := db.raw.rows.getD 0 [] }

/-- The value of a column of a source row, as a resolved column reference reads it. -/
abbrev cell (index : Nat) (row : List Value) : Value :=
  (Resolved.Expr.column index).eval (Resolved.EvalContext.bound []) row

/-- Three orders: two of the customer {lit}`acme`, written {lit}`'acme'` and {lit}`'ACME'`, and one of
{lit}`zeta`. -/
def mixed : Database := db! r"
  CREATE TABLE orders (id INTEGER PRIMARY KEY, customer TEXT NOT NULL COLLATE NOCASE, amount INTEGER NOT NULL);
  INSERT INTO orders VALUES (1, 'acme', 10), (2, 'ACME', 5), (3, 'zeta', 7);"

/-- Two rows have the same key: the values of the key function compare equal under the collation. -/
def SameKey (key : List Value → Value) (collation : Collation) (first second : List Value) : Prop :=
  collation.compare (key first) (key second) = .eq

/-- For every key function, collation and two rows, {name}`SameKey` holds in both directions or in none.
Proof sketch: a collation comparison is oriented. -/
theorem SameKey.symm {key : List Value → Value} {collation : Collation} {first second : List Value}
    (same : SameKey key collation first second) : SameKey key collation second first :=
  Std.OrientedCmp.eq_comm.mp same

/-- The groups {lit}`found` are a partition of the rows {lit}`rows` by a key under a collation:
- the groups one after the other are a permutation of the rows: each row is in exactly one group, as
  often as in the rows;
- each group has a first row, and each later row of the group has the same key as it
  ({name}`SameKey`);
- the first rows of two groups do not have the same key. -/
def KeyPartition (key : List Value → Value) (collation : Collation) (rows : List (List Value))
    (found : List (List (List Value))) : Prop :=
  found.flatten.Perm rows ∧
    (∀ group ∈ found, ∃ first rest, group = first :: rest ∧ ∀ later ∈ rest, SameKey key collation later first) ∧
    (found.map List.head?).Pairwise (fun earlier later => ∀ e ∈ earlier, ∀ l ∈ later, ¬ SameKey key collation l e)

/-- Partition rule for one term: for every grouping term, collation and rows, the groups of the rows
by the term ({name}`Resolved.groups`) in the context without parameters are a {name}`KeyPartition`
by the term's value. Proof sketch: {name}`Resolved.groups_partition`, whose test
{name}`Resolved.sameGroup` of one term is {name}`SameKey`. -/
theorem keyPartition_groups (term : Resolved.Expr) (collation : Collation) (rows : List (List Value)) :
    KeyPartition (term.eval (Resolved.EvalContext.bound [])) collation rows
      (Resolved.groups (Resolved.EvalContext.bound []) [(term, collation)] rows) := by
  obtain ⟨flat, formed, apart⟩ := Resolved.groups_partition (Resolved.EvalContext.bound []) [(term, collation)] rows
  have same : ∀ first second, Resolved.sameGroup (Resolved.EvalContext.bound []) [(term, collation)] first second = true ↔
      SameKey (term.eval (Resolved.EvalContext.bound [])) collation first second := fun first second => by
    simp [Resolved.sameGroup, SameKey]
  refine ⟨flat, fun group member => ?_, apart.imp fun {earlier later} sameFalse e inE l inL sameKey => ?_⟩
  · obtain ⟨first, rest, shape, later⟩ := formed group member
    exact ⟨first, rest, shape, fun item inRest => (same _ _).mp (later item inRest)⟩
  · have := sameFalse e inE l inL
    rw [← Bool.not_eq_true, same] at this
    exact this sameKey

/-- For every partition and permutation of its groups, the permuted groups are a partition of the
same rows by the same key. Proof sketch: each condition keeps under a permutation; the condition on
first rows is symmetric ({name}`SameKey.symm`). -/
theorem KeyPartition.perm {key : List Value → Value} {collation : Collation} {rows : List (List Value)}
    {found moved : List (List (List Value))} (partition : KeyPartition key collation rows found)
    (perm : moved.Perm found) : KeyPartition key collation rows moved := by
  obtain ⟨flat, formed, apart⟩ := partition
  refine ⟨perm.flatten.trans flat, fun group member => formed group (perm.subset member), ?_⟩
  refine (perm.map List.head?).symm.pairwise apart ?_
  intro earlier later apartEL l inL e inE sameKey
  exact apartEL e inE l inL sameKey.symm

/-- For every partition, each of its groups has a row. Proof sketch: each group has a first row. -/
theorem KeyPartition.ne_nil {key : List Value → Value} {collation : Collation} {rows : List (List Value)}
    {found : List (List (List Value))} (partition : KeyPartition key collation rows found) {group : List (List Value)}
    (member : group ∈ found) : group ≠ [] := by
  obtain ⟨first, rest, rfl, -⟩ := partition.2.1 group member
  exact List.cons_ne_nil _ _

/-- Record rule of a grouped query: for every aggregate query of the table at position 0 with one
grouping term, no {lit}`WHERE`, no {lit}`DISTINCT` and no compound, and every rows, the records of
the query ({name}`Resolved.Query.uniqueRecords`) are the records
({name}`Resolved.Query.groupRecord`) of the groups by the term that {lit}`HAVING` keeps. Proof
sketch: {name}`Resolved.filtered_of_filter_none`, {name}`Resolved.records_aggregate` and
{name}`Resolved.queryGroups_grouped`. -/
theorem uniqueRecords_grouped {query : Resolved.Query} {term : Resolved.Expr} {collation : Collation}
    (aggregate : query.aggregate = true) (grouped : query.groupBy = [(term, collation)]) (noFilter : query.filter = none)
    (noDistinct : query.distinct = none) (single : query.compound = none) (rows : List (List Value)) :
    query.uniqueRecords (Resolved.EvalContext.bound []) rows =
      ((Resolved.groups (Resolved.EvalContext.bound []) [(term, collation)] rows).filter
        (query.keepsGroup (Resolved.EvalContext.bound []))).map (query.groupRecord (Resolved.EvalContext.bound [])) := by
  rw [Resolved.Query.uniqueRecords, single]
  dsimp only
  rw [noDistinct, Resolved.filtered_of_filter_none _ noFilter, Resolved.records_aggregate _ aggregate,
    Resolved.queryGroups_grouped _ (by simp [grouped]), grouped]

/-- For every context of a group whose first aggregate value is the integer {lit}`count`, every row and
threshold, the condition {lit}`count(*) > threshold` is true exactly when
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

/-- Result rule of an ungrouped aggregate query: for every aggregate query without {lit}`GROUP BY`,
{lit}`HAVING`, {lit}`WHERE`, {lit}`DISTINCT`, compound, {lit}`OFFSET` and {lit}`LIMIT`, every list of rows and
every result that the model permits in the context without parameters, the result is the one row of
the group of all the rows ({name}`Resolved.Query.groupRecord`), also when there is no row. Proof
sketch: the result is a permutation of the records ({name}`Resolved.Query.perm_of_mem_possibleResults`),
which are the one record of all the rows ({name}`Resolved.records_ungrouped`). -/
theorem result_ungrouped {query : Resolved.Query} (aggregate : query.aggregate = true) (ungrouped : query.groupBy = [])
    (noHaving : query.having = none) (noFilter : query.filter = none) (noDistinct : query.distinct = none)
    (single : query.compound = none) (offset : query.offset = 0) (limit : query.limit = none)
    {rows result : List (List Value)} (member : result ∈ query.possibleResults (Resolved.EvalContext.bound []) rows) :
    result = [(query.groupRecord (Resolved.EvalContext.bound []) rows).1] := by
  have perm := Resolved.Query.perm_of_mem_possibleResults offset limit member
  rw [Resolved.Query.uniqueRecords, single] at perm
  dsimp only at perm
  rw [noDistinct, Resolved.filtered_of_filter_none _ noFilter,
    Resolved.records_ungrouped _ aggregate ungrouped noHaving] at perm
  exact List.perm_singleton.mp (by simpa using perm)

/-- For every database with the catalog of {name}`orders`, the catalog has {lit}`orders` at position 0
with the table {name}`ordersShape`. Proof sketch: the premise fixes the catalog. -/
theorem orders_found (db : Database) (schema : db.HasCatalog orders) :
    db.raw.catalog.findTable (name! "orders") = some (0, ordersShape) := by
  rw [show db.raw.catalog = orders.raw.catalog from schema]
  decide +kernel

/-- For every database with the catalog of {name}`orders` and every environment, the resolution state
of the connection is that of {name}`orders`. Proof sketch: the state reads only the catalog. -/
theorem orders_state (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (db.raw.connection env.counters).resolveState = (orders.raw.connection {}).resolveState := by
  simp only [Connection.resolveState, Database.Raw.connection]
  rw [show db.raw.catalog = orders.raw.catalog from schema]

end SelectGroupCases
