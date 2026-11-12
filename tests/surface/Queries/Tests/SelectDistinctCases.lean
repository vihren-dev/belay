import SelectGroupSupport

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance case A12 of ADR 0027, through the distinct rules ({lit}`distinctRecords_rules`,
{lit}`Query.uniqueRecords_distinct`, {lit}`pairwise_sameOutput_perm`): over every database with the
catalog of {lit}`orders` whose customers that compare equal under {lit}`NOCASE` are the same
values, {lit}`SELECT DISTINCT customer` gives each customer once; when two such customers differ,
as {lit}`'acme'` and {lit}`'ACME'`, the model fixes no representative and describes no result. -/

namespace SelectDistinctCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases

/-- The A12 query: each customer once. -/
def distinctCustomers : Script := sql r"SELECT DISTINCT customer FROM orders"

/-- The A12 query has one statement. -/
theorem distinctCustomers_one : distinctCustomers.statements.length = 1 := rfl

/-- The query to which {name}`distinctCustomers` resolves: the customer column, distinct under
{lit}`NOCASE`, the collation of the column. -/
def distinctQuery : Resolved.Query :=
  { sources := [.first 0], filter := none, aggregate := false, groupBy := [], columns := [.scalar (.column 1)],
    names := ["customer"], orderBy := [], offset := 0, limit := none, distinct := some [.nocase] }

/-- For every rows, the rows of the records of {name}`distinctQuery` before {lit}`DISTINCT` are the
customers of the rows, in order. Proof sketch: {name}`Resolved.records_outputs_plain`. -/
theorem distinctQuery_outputs (rows : List (List Value)) :
    (Resolved.records (Resolved.EvalContext.bound []) distinctQuery rows).map Prod.fst = rows.map fun row => [cell 1 row] := by
  rw [Resolved.records_outputs_plain _ rfl]
  rfl

/-- Distinct rule of {name}`distinctQuery`: for every rows whose customers that compare equal under
{lit}`NOCASE` are the same values, and every result that the model permits:

* no two rows of the result compare equal under {lit}`NOCASE` ({name}`Resolved.sameOutput`);
* each row of the result is the customer of a row;
* the customer of each row is a row of the result.

Proof sketch: the result is a permutation of the distinct records
({name}`Resolved.Query.uniqueRecords_distinct`, {name}`Resolved.distinctRecords_rules`); a row that
the distinct records do not keep compares equal to a kept row, so the premise makes it that row. -/
theorem distinct_rule {rows result : List (List Value)}
    (identical : ∀ a ∈ rows, ∀ b ∈ rows, Collation.nocase.compare (cell 1 a) (cell 1 b) = .eq → cell 1 a = cell 1 b)
    (member : result ∈ distinctQuery.possibleResults (Resolved.EvalContext.bound []) rows) :
    result.Pairwise (fun a b => Resolved.sameOutput [.nocase] a b = false) ∧
      (∀ row ∈ result, ∃ stored ∈ rows, row = [cell 1 stored]) ∧
      ∀ stored ∈ rows, [cell 1 stored] ∈ result := by
  have perm := Resolved.Query.perm_of_mem_possibleResults (query := distinctQuery) rfl rfl member
  rw [Resolved.Query.uniqueRecords_distinct _ rfl rfl, Resolved.filtered_of_filter_none _ rfl] at perm
  obtain ⟨sublist, covers, apart⟩ := Resolved.distinctRecords_rules [.nocase]
    (Resolved.records (Resolved.EvalContext.bound []) distinctQuery rows)
  have outputs := distinctQuery_outputs rows
  have customer : ∀ record ∈ Resolved.records (Resolved.EvalContext.bound []) distinctQuery rows,
      ∃ stored ∈ rows, record.1 = [cell 1 stored] := fun record inRecords => by
    obtain ⟨stored, inRows, same⟩ := List.mem_map.mp (outputs ▸ List.mem_map_of_mem (f := Prod.fst) inRecords)
    exact ⟨stored, inRows, same.symm⟩
  refine ⟨Resolved.pairwise_sameOutput_perm _ (List.pairwise_map.mpr apart) perm, fun row inResult => ?_,
    fun stored inRows => ?_⟩
  · obtain ⟨kept, inKept, rfl⟩ := List.mem_map.mp (perm.subset inResult)
    exact customer kept (sublist.subset inKept)
  · obtain ⟨record, inRecords, same⟩ := List.mem_map.mp (outputs.symm ▸ List.mem_map_of_mem (f := fun row => [cell 1 row]) inRows)
    obtain ⟨kept, inKept, equal⟩ := covers record inRecords
    obtain ⟨other, inOther, keptIs⟩ := customer kept (sublist.subset inKept)
    have row : kept.1 = [cell 1 stored] := by
      rcases equal with rfl | equal
      · exact same
      · rw [keptIs, same] at equal
        rw [keptIs, identical other inOther stored inRows (by simpa [Resolved.sameOutput] using equal)]
    exact perm.symm.subset (List.mem_map.mpr ⟨kept, inKept, row⟩)

/-- A12: for every database with the catalog of {name}`orders` whose customers that compare equal
under {lit}`NOCASE` are the same values, and every environment, {name}`distinctCustomers` returns a
result in which no two rows compare equal under {lit}`NOCASE`, each row is the customer of a stored
row ({name}`ordersRows`), and the customer of each stored row is a row. Proof sketch: the premise
makes the {lit}`DISTINCT` certain ({name}`Resolved.Query.distinctCertain`), so
{name}`Run.query_returnsResult_calmTable` applies; then {name}`distinct_rule`. -/
theorem distinct_customers (db : Database) (env : Env) (schema : db.HasCatalog orders)
    (identical : ∀ a ∈ ordersRows db, ∀ b ∈ ordersRows db,
      Collation.nocase.compare (cell 1 a) (cell 1 b) = .eq → cell 1 a = cell 1 b) :
    (db.run (query distinctCustomers distinctCustomers_one) env).returnsResult fun result =>
      result.Pairwise (fun a b => Resolved.sameOutput [.nocase] a b = false) ∧
        (∀ row ∈ result, ∃ stored ∈ ordersRows db, row = [cell 1 stored]) ∧
        ∀ stored ∈ ordersRows db, [cell 1 stored] ∈ result := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState
      (match distinctCustomers.statements with | (statement, _) :: _ => statement | [] => .begin) =
      .ok (.query distinctQuery [], (db.raw.connection env.counters).resolveState) := by
    rw [orders_state db env schema]
    decide +kernel
  have certain : distinctQuery.distinctCertain (Resolved.EvalContext.bound []) (ordersRows db) = true := by
    change Resolved.equalRowsIdentical [.nocase] ((Resolved.records (Resolved.EvalContext.bound []) distinctQuery
      (Resolved.filtered (Resolved.EvalContext.bound []) distinctQuery (ordersRows db))).map Prod.fst) = true
    rw [Resolved.filtered_of_filter_none _ (query := distinctQuery) rfl, distinctQuery_outputs]
    simp only [Resolved.equalRowsIdentical, List.all_map, List.all_eq_true]
    intro a inA
    simp only [List.all_map, List.all_eq_true, Function.comp_apply]
    intro b inB
    by_cases equal : Collation.nocase.compare (cell 1 a) (cell 1 b) = .eq
    · simp [identical a inA b inB equal]
    · simp [Resolved.sameOutput, equal]
  rw [Run.query_returnsResult_calmTable (script := distinctCustomers) rfl distinctCustomers_one db env resolved rfl
    (Database.table_of_findTable db.raw _ _ _ (orders_found db schema)) (by unfold Resolved.Statement.Calm; decide)
    rfl rfl rfl rfl certain]
  exact fun result member => distinct_rule identical member

/-- {name}`mixed` with the two spellings of {lit}`acme` in the other order. -/
def swapped : Database := db! r"
  CREATE TABLE orders (id INTEGER PRIMARY KEY, customer TEXT NOT NULL COLLATE NOCASE, amount INTEGER NOT NULL);
  INSERT INTO orders VALUES (1, 'ACME', 10), (2, 'acme', 5), (3, 'zeta', 7);"

/-- Orders whose customers differ under {lit}`NOCASE`. -/
def plain : Database := db! r"
  CREATE TABLE orders (id INTEGER PRIMARY KEY, customer TEXT NOT NULL COLLATE NOCASE, amount INTEGER NOT NULL);
  INSERT INTO orders VALUES (1, 'acme', 10), (2, 'zeta', 5), (3, 'acme', 7);"

/-- A12 instance and contrast:

* on {name}`plain`, {name}`distinctCustomers` returns {lit}`acme` and {lit}`zeta`, each once;
* on {name}`mixed` and on {name}`swapped`, {lit}`'acme'` and {lit}`'ACME'` compare equal under
  {lit}`NOCASE` but are different values: the model describes no result, because the kept
  spelling depends on the order in which SQLite reads the rows. Native SQLite 3.51.0 gives
  {lit}`acme` on {name}`mixed` and {lit}`ACME` on {name}`swapped`. -/
example : (plain.run (query distinctCustomers distinctCustomers_one)).returnsResult
      (· = [[.text "acme".toUTF8.toList], [.text "zeta".toUTF8.toList]]) ∧
    ¬ (mixed.run (query distinctCustomers distinctCustomers_one)).returnsResult (fun _ => True) ∧
    ¬ (swapped.run (query distinctCustomers distinctCustomers_one)).returnsResult (fun _ => True) := by
  decide +kernel

#print axioms distinctQuery_outputs
#print axioms distinct_rule
#print axioms distinct_customers

end SelectDistinctCases
