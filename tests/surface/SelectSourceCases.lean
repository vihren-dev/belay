import SelectDerivedSupport

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Acceptance case A20 of ADR 0027, through the source rules of a query without a table: a
{lit}`SELECT` without {lit}`FROM` reads the one row with no cells ({lit}`Resolved.Query.source_none`)
over every database, a pragma source gives its rows ({lit}`Resolved.Query.source_pragma`), and a
{lit}`json_each` source gives the rows of its argument ({lit}`Resolved.Query.source_each`), each
over every database with the catalog of {lit}`shop`. A {lit}`json_each` call that fails keeps its
fault ({lit}`Resolved.Query.source_each_fault`): the model describes no result, also not the empty
result. -/

namespace SelectSourceCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases SelectJoinCases SelectDerivedCases

/-- The query {lit}`SELECT 1 + 2`, without a source. -/
def sumQuery : Resolved.Query :=
  { sources := [], filter := none, aggregate := false, groupBy := [],
    columns := [.scalar (.arithmetic .add (.literal (.integer 1)) (.literal (.integer 2)))], names := ["1 + 2"],
    orderBy := [], offset := 0, limit := none }

/-- A20, no {lit}`FROM`: for every database and environment, {lit}`SELECT 1 + 2` returns the one
row 3. Proof sketch: resolution gives {name}`sumQuery` for every state
({name}`resolveStatement_selectNoFrom`), whose source is the one row with no cells
({name}`Resolved.Query.source_none`). -/
theorem sum_returns (db : Database) (env : Env) :
    (db.run (query (sql r"SELECT 1 + 2") rfl) env).returnsResult (· = [[.integer 3]]) := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState
      (sql r"SELECT 1 + 2").statements[0].1 =
      .ok (.query sumQuery [], (db.raw.connection env.counters).resolveState) :=
    resolveStatement_selectNoFrom runContext _ _ _ none _ none none rfl rfl (by decide +kernel) (by decide +kernel)
      (FilterResolves.of_none _ _ _ _)
  rw [Run.query_returnsResult_faultless (script := sql r"SELECT 1 + 2") rfl rfl db env resolved (Resolved.Query.source_none _ _ _ rfl) (by simp)
    (by unfold Resolved.Statement.Calm; decide +kernel) rfl (Resolved.Query.bindWindow_literal _ _ rfl rfl)
    (fun row _ expression member => by
      simp [sumQuery, Resolved.Query.expressions, Resolved.Query.keptExpressions,
        Resolved.Output.scalars, Resolved.Output.operands] at member
      subst member
      rfl)
    (by simp [Resolved.Query.fails, sumQuery]) (by simp [Resolved.Query.distinctCertain, sumQuery])]
  intro result member
  have perm := Resolved.Query.perm_of_mem_possibleResults_plain rfl rfl rfl rfl rfl member
  rw [Resolved.filtered_of_filter_none _ rfl] at perm
  exact List.perm_singleton.mp perm

/-- A20 contrast with native SQLite 3.51.0 on {name}`shop`: {lit}`SELECT count(*)` without
{lit}`FROM` counts the one row with no cells and gives 1, where {lit}`count(*)` over the empty
table {lit}`orders` gives 0; {lit}`SELECT 1 WHERE 0` gives no row. -/
example : (shop.run (query (sql r"SELECT count(*)") rfl)).returnsResult (· = [[.integer 1]]) ∧
    (shop.run (query (sql r"SELECT count(*) FROM orders") rfl)).returnsResult (· = [[.integer 0]]) ∧
    (shop.run (query (sql r"SELECT 1 WHERE 0") rfl)).returnsResult (· = []) := by
  decide +kernel

/-- The text value of a string. -/
def text (string : String) : Value := .text string.toUTF8.toList

/-- The rows of {lit}`pragma_table_info('customers')` on the catalog of {name}`shop`, with the
hidden argument and schema cells. -/
def customersInfo : List (List Value) :=
  [[.integer 0, text "id", text "INTEGER", .integer 0, .null, .integer 1, text "customers", .null],
   [.integer 1, text "name", text "TEXT", .integer 1, .null, .integer 0, text "customers", .null]]

/-- The query {lit}`SELECT name FROM pragma_table_info('customers')` on the catalog of
{name}`shop`. -/
def namesQuery : Resolved.Query :=
  { sources := [{ kind := .inner, source := .pragma (.fixed 8 customersInfo), condition := none }], filter := none,
    aggregate := false, groupBy := [], columns := [.scalar (.column 1)], names := ["name"], orderBy := [],
    offset := 0, limit := none }

/-- A20, pragma: for every database with the catalog of {name}`shop` and environment,
{lit}`SELECT name FROM pragma_table_info('customers')` returns the rows {lit}`id` and {lit}`name` in
some order. Proof sketch: resolution computes the rows from the catalog, and
{name}`Resolved.Query.source_pragma` gives them as the source rows. -/
theorem names_returns (db : Database) (env : Env) (schema : db.HasCatalog shop) :
    (db.run (query (sql r"SELECT name FROM pragma_table_info('customers')") rfl) env).returnsResult
      (·.Perm [[text "id"], [text "name"]]) := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState
      (sql r"SELECT name FROM pragma_table_info('customers')").statements[0].1 =
      .ok (.query namesQuery [], (db.raw.connection env.counters).resolveState) := by
    rw [catalog_state shop db env schema]
    decide +kernel
  rw [Run.query_returnsResult_faultless (script := sql r"SELECT name FROM pragma_table_info('customers')") rfl rfl
    db env resolved (Resolved.Query.source_pragma _ db.raw none namesQuery _ customersInfo rfl rfl) (by simp)
    (by unfold Resolved.Statement.Calm; decide +kernel) rfl (Resolved.Query.bindWindow_literal _ _ rfl rfl)
    (fun row _ expression member => by
      simp [namesQuery, Resolved.Query.expressions, Resolved.Query.keptExpressions,
        Resolved.QuerySource.expressions, Resolved.Output.scalars, Resolved.Output.operands] at member
      subst member
      rfl)
    (by simp [Resolved.Query.fails, namesQuery]) (by simp [Resolved.Query.distinctCertain, namesQuery])]
  intro result member
  have perm := Resolved.Query.perm_of_mem_possibleResults_plain rfl rfl rfl rfl rfl member
  rwa [Resolved.filtered_of_filter_none _ rfl] at perm

/-- The query {lit}`SELECT value FROM json_each(?)`. -/
def valuesQuery : Resolved.Query :=
  { sources := [{ kind := .inner, source := .each (.parameter 1) none, condition := none }], filter := none,
    aggregate := false, groupBy := [], columns := [.scalar (.column 1)], names := ["value"], orderBy := [],
    offset := 0, limit := none }

/-- A20, {lit}`json_each`: for every value whose JSON rows ({name}`Json.eachRows` of the bound
value) are {lit}`rows`, every database with the catalog of {name}`shop` and environment,
{lit}`SELECT value FROM json_each(?)` with the value returns the value cell of each row of
{lit}`rows`, in some order. Proof sketch: {name}`Resolved.Query.source_each` gives the rows of the
bound value as the source rows. -/
theorem values_returns (value : Value) (rows : List (List Value))
    (parsed : Json.eachRows (boundValue value) none = .ok rows) (db : Database) (env : Env)
    (schema : db.HasCatalog shop) :
    (db.run (query (sql r"SELECT value FROM json_each(?)" value) rfl) env).returnsResult
      (·.Perm (rows.map fun row => [cell 1 row])) := by
  obtain ⟨statement, head, resolves⟩ : ∃ statement,
      (sql r"SELECT value FROM json_each(?)" value).statements = [(statement, [value])] ∧
        resolveStatement runContext (shop.raw.connection {}).resolveState statement =
          .ok (.query valuesQuery [], (shop.raw.connection {}).resolveState) :=
    ⟨_, rfl, by decide +kernel⟩
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query valuesQuery [], (db.raw.connection env.counters).resolveState) := by
    rw [catalog_state shop db env schema]
    exact resolves
  rw [Run.query_returnsResult_faultless head rfl db env resolved (Resolved.Query.source_each _ db.raw none valuesQuery _ _ rows rfl parsed) (by simp)
    (by unfold Resolved.Statement.Calm; decide +kernel) rfl (Resolved.Query.bindWindow_literal _ _ rfl rfl)
    (fun row _ expression member => by
      simp [valuesQuery, Resolved.Query.expressions, Resolved.Query.keptExpressions,
        Resolved.QuerySource.expressions, Resolved.Output.scalars, Resolved.Output.operands] at member
      rcases member with rfl | rfl <;> rfl)
    (by simp [Resolved.Query.fails, valuesQuery]) (by simp [Resolved.Query.distinctCertain, valuesQuery])]
  intro result member
  have perm := Resolved.Query.perm_of_mem_possibleResults_plain rfl rfl rfl rfl rfl member
  have output : valuesQuery.rowOutput (Resolved.EvalContext.statement [value] db.raw []) = fun row => [cell 1 row] := by
    funext row
    simp [Resolved.Query.rowOutput, valuesQuery, Resolved.Expr.eval_column]
  rwa [Resolved.filtered_of_filter_none _ rfl, output] at perm

/-- A20 instances on {name}`shop`, with the rows of native SQLite 3.51.0: {lit}`json_each(?)` with
the value {lit}`'[10,20]'` gives the values 10 and 20, and {lit}`PRAGMA table_info(customers)` gives
the rows of {name}`customersInfo` without the two hidden cells. -/
example : (shop.run (query (sql r"SELECT value FROM json_each(?)" (text "[10,20]")) rfl)).returnsResult
      (· = [[.integer 10], [.integer 20]]) ∧
    (shop.run (query (sql r"PRAGMA table_info(customers)") rfl)).returnsResult (· = customersInfo.map (·.take 6)) := by
  decide +kernel

/-- The query {lit}`SELECT key FROM json_each('[1')`, whose JSON argument is malformed. -/
def keysQuery : Resolved.Query :=
  { sources := [{ kind := .inner, source := .each (.literal (text "[1")) none, condition := none }], filter := none,
    aggregate := false, groupBy := [], columns := [.scalar (.column 0)], names := ["key"], orderBy := [],
    offset := 0, limit := none }

/-- The JSON text {lit}`[1` is malformed: {name}`Json.eachRows` of it gives the error. -/
theorem malformed_rows : Json.eachRows (text "[1") none = .error .malformed := by decide +kernel

/-- A20 contrast, a fault that stays: for every database with the catalog of {name}`shop`,
environment, property {lit}`Q` of a result and property {lit}`E` of a result code,
{lit}`SELECT key FROM json_each('[1')` returns no result with {lit}`Q`, also not the empty result,
and no error with {lit}`E`: the call fails, so the source has the fault {name}`Resolved.Fault.may`
({name}`Resolved.Query.source_each_fault`), and the model describes no result. Native SQLite 3.51.0
gives the error {lit}`malformed JSON`. -/
theorem malformed_unmodeled (db : Database) (env : Env) (schema : db.HasCatalog shop)
    (property : List (List Value) → Prop) (code : Nat → Prop) :
    ¬ (db.run (sql r"SELECT key FROM json_each('[1')") env).returnsResult property ∧
      ¬ (db.run (sql r"SELECT key FROM json_each('[1')") env).returnsError code := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState
      (sql r"SELECT key FROM json_each('[1')").statements[0].1 =
      .ok (.query keysQuery [], (db.raw.connection env.counters).resolveState) := by
    rw [catalog_state shop db env schema]
    decide +kernel
  have calm : (Resolved.Statement.query keysQuery []).Calm := by
    unfold Resolved.Statement.Calm
    decide +kernel
  have context : (db.raw.connection env.counters).queryContextAt 0 [] keysQuery [] = _ :=
    Connection.queryContext_calm (db.raw.connection env.counters) [] keysQuery [] calm
  have found := Resolved.Query.source_each_fault (Resolved.EvalContext.statement [] db.raw []) db.raw none keysQuery
    _ _ .malformed rfl (by rw [Resolved.Expr.eval_literal]; exact malformed_rows)
  exact Run.send_unready (script := sql r"SELECT key FROM json_each('[1')") rfl db env resolved (value := 0)
    (by simp [statementClock, calm.readsClock]) (calm.firstUnknown _)
    (by rw [context]; exact found)
    (Or.inr (Or.inl rfl)) property code

#print axioms sum_returns
#print axioms names_returns
#print axioms values_returns
#print axioms malformed_unmodeled

end SelectSourceCases
