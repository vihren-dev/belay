import SelectGroupSupport

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance cases A13 and A14 of ADR 0027, through the order rules
({lit}`Query.exists_sorted_perm_of_mem_possibleResults`, {lit}`Query.exists_sorted_of_mem_possibleResults`)
and the window rule ({lit}`Query.length_of_mem_possibleResults`): over every database with the
catalog of {lit}`orders`, a sort by {lit}`amount`, which is not a result column, gives the ids of all
the rows with the amounts in order, and {lit}`LIMIT 2 OFFSET 1` gives as many rows as the window
takes, from a sublist of the rows in order. -/

namespace SelectOrderCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases

/-- The query of the ids of the rows of {lit}`orders` with {lit}`ORDER BY` {lit}`amount`, in the given
direction, {lit}`OFFSET` and {lit}`LIMIT`. -/
def idsByAmount (descending : Bool) (offset : Nat) (limit : Option Nat) : Resolved.Query :=
  { sources := [.first 0], filter := none, aggregate := false, groupBy := [], columns := [.scalar (.column 0)],
    names := ["id"], orderBy := [{ key := .expression (.column 2), descending, collation := .binary }], offset, limit }

/-- Records rule of {name}`idsByAmount`: for every context, direction, offset, limit and rows, the records of
the query are, for each row in order, its id as the result row and its amount as the sort value.
Proof sketch: the query has no {lit}`WHERE`, {lit}`DISTINCT`, compound or aggregate. -/
theorem idsByAmount_records (context : Resolved.EvalContext) (descending : Bool) (offset : Nat) (limit : Option Nat)
    (rows : List (List Value)) :
    (idsByAmount descending offset limit).uniqueRecords context rows =
      rows.map fun row => ([cell 0 row], [cell 2 row]) := by
  have kept : rows.filter (fun _ => true) = rows := List.filter_eq_self.mpr fun _ _ => rfl
  simp [Resolved.Query.uniqueRecords, idsByAmount, Resolved.records, Resolved.filtered, kept, Resolved.Expr.eval_column]

/-- Order rule of {name}`idsByAmount`: for every direction, offset, limit, rows and result that the
model permits, the result is the ids of some rows that are a permutation of a sublist of the rows,
and the amounts of each two of those rows are in order: under {lit}`BINARY`, the earlier amount is
at most the later one, or at least it when {lit}`descending` is true. Proof sketch:
{name}`Resolved.Query.exists_sorted_of_mem_possibleResults` with {name}`idsByAmount_records`; a
sublist of the mapped rows is the map of a sublist, and a permutation of it the map of a
permutation ({name}`Resolved.exists_perm_map_eq`). -/
theorem idsByAmount_sorted {context : Resolved.EvalContext} {descending : Bool} {offset : Nat} {limit : Option Nat}
    {rows result : List (List Value)}
    (member : result ∈ (idsByAmount descending offset limit).possibleResults context rows) :
    ∃ picked : List (List Value), (∃ chosen, chosen.Sublist rows ∧ picked.Perm chosen) ∧
      picked.Pairwise (fun a b => (Resolved.compareTerm descending .binary (cell 2 a) (cell 2 b)).isLE) ∧
      result = picked.map fun row => [cell 0 row] := by
  obtain ⟨ordered, ⟨records, sublist, perm⟩, sorted, rfl⟩ := Resolved.Query.exists_sorted_of_mem_possibleResults member
  rw [idsByAmount_records] at sublist
  obtain ⟨chosen, chosenSublist, rfl⟩ := List.sublist_map_iff.mp sublist
  obtain ⟨picked, pickedPerm, rfl⟩ := Resolved.exists_perm_map_eq _ perm
  refine ⟨picked, ⟨chosen, chosenSublist, pickedPerm⟩, ?_, by simp⟩
  simpa [List.pairwise_map, idsByAmount, Resolved.compareSort] using sorted

/-- The A13 query: the ids of the orders, the largest amount first. -/
def idsDescending : Script := sql r"SELECT id FROM orders ORDER BY amount DESC"

/-- The A13 query has one statement. -/
theorem idsDescending_one : idsDescending.statements.length = 1 := rfl

/-- A13: for every database with the catalog of {name}`orders` and every environment,
{name}`idsDescending` returns the ids of an order of all the stored rows ({name}`ordersRows`): a
permutation of the rows, each as often as in the scan, in which the amount of each row is at least the amount of
every later row under {lit}`BINARY`. The sort key {lit}`amount` is no result column. Proof sketch:
{name}`idsByAmount_sorted`; without a window the result has a row for each record
({name}`Resolved.Query.perm_of_mem_possibleResults`), so the sublist is all the rows. -/
theorem ids_descending (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (db.run (query idsDescending idsDescending_one) env).returnsResult fun result =>
      ∃ ordered : List (List Value), ordered.Perm (ordersRows db) ∧
        ordered.Pairwise (fun a b => (Collation.binary.compare (cell 2 b) (cell 2 a)).isLE) ∧
        result = ordered.map fun row => [cell 0 row] := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState
      (match idsDescending.statements with | (statement, _) :: _ => statement | [] => .begin) =
      .ok (.query (idsByAmount true 0 none) [], (db.raw.connection env.counters).resolveState) := by
    rw [orders_state db env schema]
    decide +kernel
  rw [Run.query_returnsResult_calmTable (script := idsDescending) rfl idsDescending_one db env resolved rfl
    (Database.table_of_findTable db.raw _ _ _ (orders_found db schema)) (by unfold Resolved.Statement.Calm; decide)
    rfl rfl rfl rfl rfl]
  intro result member
  change result ∈ (idsByAmount true 0 none).possibleResults _ (ordersRows db) at member
  have length := (Resolved.Query.perm_of_mem_possibleResults (query := idsByAmount true 0 none) rfl rfl member).length_eq
  obtain ⟨picked, ⟨chosen, sublist, perm⟩, sorted, rfl⟩ := idsByAmount_sorted member
  rw [idsByAmount_records] at length
  simp only [List.length_map] at length
  rw [sublist.eq_of_length (by rw [← perm.length_eq, length])] at perm
  exact ⟨picked, perm, by simpa [Resolved.compareTerm] using sorted, rfl⟩

/-- The A14 query: the ids of the orders by amount, without the first, at most two. -/
def idsWindow : Script := sql r"SELECT id FROM orders ORDER BY amount LIMIT 2 OFFSET 1"

/-- The A14 query has one statement. -/
theorem idsWindow_one : idsWindow.statements.length = 1 := rfl

/-- A14: for every database with the catalog of {name}`orders` and every environment,
{name}`idsWindow` returns a result such that:

* it has the smaller of 2 and the number of stored rows less one rows: none for no row or one row
  (the offset is past the end), one for two rows, two for more rows;
* it is the ids of some rows that are a permutation of a sublist of the stored rows, in which the
  amount of each row is at most the amount of every later row under {lit}`BINARY`.

It does not say which rows of equal amounts the window takes. Proof sketch:
{name}`Resolved.Query.length_of_mem_possibleResults` and {name}`idsByAmount_sorted`. -/
theorem ids_window (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (db.run (query idsWindow idsWindow_one) env).returnsResult fun result =>
      result.length = min 2 ((ordersRows db).length - 1) ∧
      ∃ picked : List (List Value), (∃ chosen, chosen.Sublist (ordersRows db) ∧ picked.Perm chosen) ∧
        picked.Pairwise (fun a b => (Collation.binary.compare (cell 2 a) (cell 2 b)).isLE) ∧
        result = picked.map fun row => [cell 0 row] := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState
      (match idsWindow.statements with | (statement, _) :: _ => statement | [] => .begin) =
      .ok (.query (idsByAmount false 1 (some 2)) [], (db.raw.connection env.counters).resolveState) := by
    rw [orders_state db env schema]
    decide +kernel
  rw [Run.query_returnsResult_calmTable (script := idsWindow) rfl idsWindow_one db env resolved rfl
    (Database.table_of_findTable db.raw _ _ _ (orders_found db schema)) (by unfold Resolved.Statement.Calm; decide)
    rfl rfl rfl rfl rfl]
  intro result member
  change result ∈ (idsByAmount false 1 (some 2)).possibleResults _ (ordersRows db) at member
  have length := (Resolved.Query.length_of_mem_possibleResults member).2 2 rfl
  rw [idsByAmount_records, List.length_map] at length
  simpa [Resolved.compareTerm, idsByAmount] using And.intro length (idsByAmount_sorted member)

/-- Orders whose two smallest amounts are equal. -/
def tied : Database := db! r"
  CREATE TABLE orders (id INTEGER PRIMARY KEY, customer TEXT NOT NULL COLLATE NOCASE, amount INTEGER NOT NULL);
  INSERT INTO orders VALUES (1, 'a', 5), (2, 'b', 5), (3, 'c', 9);"

/-- The query of the id of one order of the smallest amount. -/
def idSmallest : Script := sql r"SELECT id FROM orders ORDER BY amount LIMIT 1"

/-- A14 instances and contrast on {name}`mixed` and {name}`tied`:

* {name}`idsDescending` gives the ids 1, 3, 2 and {name}`idsWindow` the ids 3, 1 on {name}`mixed`;
* {lit}`LIMIT 0` gives no row, {lit}`LIMIT 1` one row and an offset past the end no row;
* on {name}`tied`, {name}`idSmallest` gives the id 1 or the id 2: the model permits each tied
  winner, and claims neither alone. Native SQLite gives 1 with a full scan and 2 with an index on
  {lit}`(amount, id DESC)`. -/
example : (mixed.run (query idsDescending idsDescending_one)).returnsResult (· = [[.integer 1], [.integer 3], [.integer 2]]) ∧
    (mixed.run (query idsWindow idsWindow_one)).returnsResult (· = [[.integer 3], [.integer 1]]) ∧
    (mixed.run (query (sql r"SELECT id FROM orders ORDER BY amount LIMIT 0") rfl)).returnsResult (· = []) ∧
    (mixed.run (query idSmallest rfl)).returnsResult (· = [[.integer 2]]) ∧
    (mixed.run (query (sql r"SELECT id FROM orders ORDER BY amount LIMIT 2 OFFSET 5") rfl)).returnsResult (· = []) ∧
    (tied.run (query idSmallest rfl)).returnsResult (fun result => result = [[.integer 1]] ∨ result = [[.integer 2]]) ∧
    ¬ (tied.run (query idSmallest rfl)).returnsResult (· = [[.integer 1]]) ∧
    ¬ (tied.run (query idSmallest rfl)).returnsResult (· = [[.integer 2]]) := by
  decide +kernel

#print axioms idsByAmount_records
#print axioms idsByAmount_sorted
#print axioms ids_descending
#print axioms ids_window

end SelectOrderCases
