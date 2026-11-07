import SelectOrderCases

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance case A15 of ADR 0027, through the faultless execution rule with a bound window
({lit}`Run.query_returnsResult_faultless`) and the mismatch rule ({lit}`Run.query_mismatch`): over
every database with the catalog of {lit}`orders`, {lit}`LIMIT ? OFFSET ?` with values that SQLite
reads as integers gives the window of the rows in order, as {lit}`LIMIT` and {lit}`OFFSET` literals
do (A14), and a {lit}`LIMIT` value that is not an integer gives the error {lit}`datatype mismatch`,
not an empty result. With {lit}`LIMIT 0`, SQLite does not read the {lit}`OFFSET` value; with a
negative {lit}`LIMIT` it does, also when no row passes the filter. -/

namespace SelectOrderCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases

/-- The query {lit}`SELECT id FROM orders ORDER BY amount LIMIT ?1 OFFSET ?2`. -/
def parameterWindow : Resolved.Query :=
  { idsByAmount false 0 none with limitParameter := some 1, offsetParameter := some 2 }

/-- The A15 script with the values of its {lit}`LIMIT` and its {lit}`OFFSET`. -/
def windowScript (limit offset : Value) : Script := sql r"SELECT id FROM orders ORDER BY amount LIMIT ? OFFSET ?" limit offset

/-- For every two values, the A15 script has one statement, which resolves to
{name}`parameterWindow` on the catalog of {name}`orders`, with the values. -/
theorem windowScript_statement (limit offset : Value) : ∃ statement,
    (windowScript limit offset).statements = [(statement, [limit, offset])] ∧
      resolveStatement runContext (orders.raw.connection {}).resolveState statement =
        .ok (.query parameterWindow [], (orders.raw.connection {}).resolveState) :=
  ⟨_, rfl, by decide +kernel⟩

/-- For every two values that SQLite reads as the integers {lit}`limit` and {lit}`offset` that are
not negative ({name}`windowInteger` of {name}`boundValue`), the window of {name}`parameterWindow`
binds to {name}`idsByAmount` with {lit}`LIMIT limit`, and {lit}`OFFSET offset`, or {lit}`OFFSET 0`
for {lit}`LIMIT 0`, which does not read the offset. -/
theorem parameterWindow_bind {limitValue offsetValue : Value} {limit offset : Nat}
    (limitInteger : windowInteger (boundValue limitValue) = some limit)
    (offsetInteger : windowInteger (boundValue offsetValue) = some offset) :
    parameterWindow.bindWindow [limitValue, offsetValue] =
      some (idsByAmount false (if limit = 0 then 0 else offset) (some limit)) := by
  by_cases zero : limit = 0
  · subst zero
    simp [Resolved.Query.bindWindow, Resolved.Query.boundLimit, Resolved.Query.boundOffset, parameterWindow,
      idsByAmount, parameterValue, limitInteger]
  · simp [Resolved.Query.bindWindow, Resolved.Query.boundLimit, Resolved.Query.boundOffset, parameterWindow,
      idsByAmount, parameterValue, limitInteger, offsetInteger, zero]

/-- A15 with valid values: for every two values that SQLite reads as the integers {lit}`limit` and
{lit}`offset` that are not negative, database with the catalog of {name}`orders` and environment,
{name}`windowScript` returns a result such that:

* it has the smaller of {lit}`limit` and the number of stored rows after the first {lit}`offset`;
* it is the ids of some rows that are a permutation of a sublist of the stored rows, in which the
  amount of each row is at most the amount of every later row under {lit}`BINARY`.

Proof sketch: {name}`parameterWindow_bind` gives the bound query of
{name}`Run.query_returnsResult_faultless`; then the rules of A14
({name}`Resolved.Query.length_of_mem_possibleResults`, {name}`idsByAmount_sorted`). -/
theorem ids_parameter_window {limitValue offsetValue : Value} {limit offset : Nat}
    (limitInteger : windowInteger (boundValue limitValue) = some limit)
    (offsetInteger : windowInteger (boundValue offsetValue) = some offset)
    (db : Database) (env : Env) (schema : db.HasCatalog orders) :
    (db.run (query (windowScript limitValue offsetValue) rfl) env).returnsResult fun result =>
      result.length = min limit ((ordersRows db).length - offset) ∧
      ∃ picked : List (List Value), (∃ chosen, chosen.Sublist (ordersRows db) ∧ picked.Perm chosen) ∧
        picked.Pairwise (fun a b => (Collation.binary.compare (cell 2 a) (cell 2 b)).isLE) ∧
        result = picked.map fun row => [cell 0 row] := by
  obtain ⟨statement, head, resolves⟩ := windowScript_statement limitValue offsetValue
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query parameterWindow [], (db.raw.connection env.counters).resolveState) := by
    rw [orders_state db env schema]
    exact resolves
  rw [Run.query_returnsResult_faultless head rfl db env resolved
    (Resolved.Query.source_first _ parameterWindow db.raw 0 _ rfl
      (Database.table_of_findTable db.raw _ _ _ (orders_found db schema)))
    (by simp) (by unfold Resolved.Statement.Calm; decide +kernel) rfl (parameterWindow_bind limitInteger offsetInteger)
    (fun row _ expression member => by
      simp [parameterWindow, idsByAmount, Resolved.Query.expressions, Resolved.Query.keptExpressions,
        Resolved.QuerySource.expressions, Resolved.QuerySource.first, Resolved.Output.scalars, Resolved.Output.operands,
        Resolved.SortKey.expressions] at member
      rcases member with rfl | rfl <;> rfl)
    (by simp [Resolved.Query.fails, idsByAmount]) (by simp [Resolved.Query.distinctCertain, idsByAmount])]
  intro result member
  have length := (Resolved.Query.length_of_mem_possibleResults member).2 limit rfl
  rw [idsByAmount_records, List.length_map] at length
  refine ⟨?_, by simpa [Resolved.compareTerm, ordersRows] using idsByAmount_sorted member⟩
  rw [length]
  by_cases zero : limit = 0 <;> simp [zero, idsByAmount, ordersRows]

/-- A15 with a value that is no integer: for every {lit}`LIMIT` value that SQLite cannot read as an
integer ({name}`windowInteger` of {name}`boundValue` is none), {lit}`OFFSET` value, database with
the catalog of {name}`orders`, environment, property {lit}`Q` of a result and property {lit}`E` of a
result code, {name}`windowScript` returns no result with {lit}`Q`, also not the empty result, and
returns an error with {lit}`E` exactly when {lit}`E` holds of the code of {lit}`datatype mismatch`.
Proof sketch: the window does not bind ({name}`Resolved.Query.bindWindow`), and
{name}`Run.query_mismatch` gives the error. -/
theorem limit_mismatch {limitValue : Value} (offsetValue : Value)
    (notInteger : windowInteger (boundValue limitValue) = none)
    (db : Database) (env : Env) (schema : db.HasCatalog orders)
    (property : List (List Value) → Prop) (code : Nat → Prop) :
    ¬ (db.run (query (windowScript limitValue offsetValue) rfl) env).returnsResult property ∧
      ((db.run (query (windowScript limitValue offsetValue) rfl) env).returnsError code ↔
        code ExecutionError.datatypeMismatch.primaryCode) := by
  obtain ⟨statement, head, resolves⟩ := windowScript_statement limitValue offsetValue
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query parameterWindow [], (db.raw.connection env.counters).resolveState) := by
    rw [orders_state db env schema]
    exact resolves
  exact Run.query_mismatch head rfl db env resolved (by unfold Resolved.Statement.Calm; decide +kernel) rfl
    (Resolved.Query.source_first _ parameterWindow db.raw 0 _ rfl
      (Database.table_of_findTable db.raw _ _ _ (orders_found db schema)))
    (by simp)
    (by simp [Resolved.Query.bindWindow, Resolved.Query.boundLimit, parameterWindow, parameterValue, notInteger])
    property code

/-- A15 instances and contrast on {name}`mixed`, with the rows of native SQLite 3.51.0:

* {lit}`LIMIT 2 OFFSET 1` gives the ids 3 and 1, also with the text values {lit}`'+2'` and {lit}`' 1 '`;
* {lit}`LIMIT 'abc'` fails with {lit}`datatype mismatch` and gives no empty result, and an
  {lit}`OFFSET 'abc'` after {lit}`LIMIT 2` fails too;
* {lit}`LIMIT 0` gives no row and does not read the {lit}`OFFSET`: NULL there gives no error. -/
example : (mixed.run (query (windowScript (.integer 2) (.integer 1)) rfl)).returnsResult
      (· = [[.integer 3], [.integer 1]]) ∧
    (mixed.run (query (windowScript (.text "+2".toUTF8.toList) (.text " 1 ".toUTF8.toList)) rfl)).returnsResult
      (· = [[.integer 3], [.integer 1]]) ∧
    ¬ (mixed.run (query (windowScript (.text "abc".toUTF8.toList) (.integer 0)) rfl)).returnsResult (· = []) ∧
    (mixed.run (query (windowScript (.text "abc".toUTF8.toList) (.integer 0)) rfl)).returnsError
      (· = ExecutionError.datatypeMismatch.primaryCode) ∧
    (mixed.run (query (windowScript (.integer 2) (.text "abc".toUTF8.toList)) rfl)).returnsError
      (· = ExecutionError.datatypeMismatch.primaryCode) ∧
    (mixed.run (query (windowScript (.integer 0) .null) rfl)).returnsResult (· = []) := by
  decide +kernel

/-- The A15 script with the value of its {lit}`LIMIT` only: the script gives no value for the
{lit}`OFFSET` parameter, which is then NULL. -/
def limitOnlyScript (limit : Value) : Script :=
  { statements := (windowScript limit .null).statements.map fun (statement, _) => (statement, [limit]) }

/-- A15 contrasts of the read of the window on {name}`mixed`, with the rows of native SQLite 3.51.0:

* a negative {lit}`LIMIT` has no limit, and a negative {lit}`OFFSET` skips no row;
* with {lit}`LIMIT -1` SQLite reads the {lit}`OFFSET`, so NULL there fails with
  {lit}`datatype mismatch`, and so does an {lit}`OFFSET` value that is not given, which is NULL;
* SQLite reads the window before the first row: {lit}`WHERE 0` with {lit}`OFFSET NULL` fails, and
  with {lit}`OFFSET 1` it gives no row. -/
example : (mixed.run (query (windowScript (.integer (-1)) (.integer 1)) rfl)).returnsResult
      (· = [[.integer 3], [.integer 1]]) ∧
    (mixed.run (query (windowScript (.integer 1) (.integer (-5))) rfl)).returnsResult (· = [[.integer 2]]) ∧
    (mixed.run (query (windowScript (.integer (-1)) .null) rfl)).returnsError
      (· = ExecutionError.datatypeMismatch.primaryCode) ∧
    (mixed.run (query (limitOnlyScript (.integer (-1))) rfl)).returnsError
      (· = ExecutionError.datatypeMismatch.primaryCode) ∧
    (mixed.run (query (sql r"SELECT id FROM orders WHERE 0 ORDER BY amount LIMIT 2 OFFSET ?" .null) rfl)).returnsError
      (· = ExecutionError.datatypeMismatch.primaryCode) ∧
    (mixed.run (query (sql r"SELECT id FROM orders WHERE 0 ORDER BY amount LIMIT 2 OFFSET ?" (.integer 1)) rfl)).returnsResult
      (· = []) := by
  decide +kernel

#print axioms windowScript_statement
#print axioms parameterWindow_bind
#print axioms ids_parameter_window
#print axioms limit_mismatch

end SelectOrderCases
