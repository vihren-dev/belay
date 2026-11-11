import SelectGroupSupport

set_option doc.verso true
set_option sql.check false
set_option maxRecDepth 8192

/-! Support of the join cases A05 and A06 of ADR 0027: the catalog of {lit}`customers` and
{lit}`orders`, the scans of both tables, the query of each join kind and the result rule of a join
query through the two-table source rule ({lit}`Resolved.Query.source_two_tables`) and the calm
execution rule ({lit}`Run.query_returnsResult_calm`). -/

namespace SelectJoinCases
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database
open SelectGroupCases (cell)

/-- A shop without rows: {lit}`customers` with a NOT NULL name, and {lit}`orders` whose
{lit}`customer_id` can be NULL and has no foreign key. -/
def shop : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT NOT NULL);
  CREATE TABLE orders (id INTEGER PRIMARY KEY, customer_id INTEGER, amount INTEGER NOT NULL);"

/-- The table of {lit}`customers` in {name}`shop`. -/
def customersShape : CatalogTable := ((shop.raw.catalog.findTable (name! "customers")).get (by decide +kernel)).2

/-- The table of {lit}`orders` in {name}`shop`. -/
def ordersShape : CatalogTable := ((shop.raw.catalog.findTable (name! "orders")).get (by decide +kernel)).2

/-- The rows of {lit}`customers` in a database, in the order of a full scan. -/
def customerRows (db : Database) : List (List Value) :=
  Resolved.sourceRows { shape := customersShape, rows := db.raw.rows.getD 0 [] }

/-- The rows of {lit}`orders` in a database, in the order of a full scan. -/
def orderRows (db : Database) : List (List Value) :=
  Resolved.sourceRows { shape := ordersShape, rows := db.raw.rows.getD 1 [] }

/-- The join of {lit}`customers c` with the condition {lit}`c.id = o.customer_id`, as resolution
gives it after {lit}`orders o`: cell 3 of a joined row is {lit}`c.id`, cell 1 is {lit}`o.customer_id`. -/
def customerJoin (kind : Resolved.JoinKind) : Resolved.QuerySource :=
  { kind, source := .table 0,
    condition := some (.compare .eq (some .numeric) (.column 3) (.column 1) .binary) }

/-- The query {lit}`SELECT o.id, c.name FROM orders o KIND JOIN customers c ON c.id = o.customer_id`
for a join kind. -/
def joined (kind : Resolved.JoinKind) : Resolved.Query :=
  { sources := [.first 1, customerJoin kind], filter := none, aggregate := false, groupBy := [],
    columns := [.scalar (.column 0), .scalar (.column 4)], names := ["id", "name"], orderBy := [], offset := 0,
    limit := none }

/-- Whether a customer matches an order: the join condition is true for the order followed by the
customer, so the customer's id equals the order's {lit}`customer_id` under numeric affinity. A NULL
{lit}`customer_id` matches no customer. -/
def Matches (order customer : List Value) : Bool :=
  (customerJoin .inner).matches (Resolved.EvalContext.bound []) (order ++ customer)

/-- For every list and two functions that agree on its elements, the two lists of the elements'
results one after the other are equal. -/
theorem flatMap_congr_mem {α β : Type} {list : List α} {first second : α → List β}
    (agree : ∀ item ∈ list, first item = second item) : list.flatMap first = list.flatMap second := by
  induction list with
  | nil => rfl
  | cons item rest later =>
    simp only [List.flatMap_cons, agree item List.mem_cons_self,
      later fun other member => agree other (List.mem_cons_of_mem _ member)]

/-- For every database with the catalog of {name}`shop`, the catalog has {lit}`customers` at position
0 and {lit}`orders` at position 1. Proof sketch: the premise fixes the catalog. -/
theorem shop_found (db : Database) (schema : db.HasCatalog shop) :
    db.raw.catalog.findTable (name! "customers") = some (0, customersShape) ∧
      db.raw.catalog.findTable (name! "orders") = some (1, ordersShape) := by
  rw [show db.raw.catalog = shop.raw.catalog from schema]
  exact ⟨by decide +kernel, by decide +kernel⟩

/-- For every database with the catalog of {name}`shop` and every environment, the resolution state
of the connection is that of {name}`shop`. Proof sketch: the state reads only the catalog. -/
theorem shop_state (db : Database) (env : Env) (schema : db.HasCatalog shop) :
    (db.raw.connection env.counters).resolveState = (shop.raw.connection {}).resolveState := by
  simp only [Connection.resolveState, Database.Raw.connection]
  rw [show db.raw.catalog = shop.raw.catalog from schema]

/-- For every database with the catalog of {name}`shop`, every order row has three cells and every
customer row two. Proof sketch: the rows of a valid database have one cell per column
({name}`Resolved.sourceRows_width`). -/
theorem rows_width (db : Database) (schema : db.HasCatalog shop) :
    (∀ order ∈ orderRows db, order.length = 3) ∧ ∀ customer ∈ customerRows db, customer.length = 2 := by
  obtain ⟨customers, orders⟩ := shop_found db schema
  have orderWidth : ordersShape.columns.length = 3 := by decide +kernel
  have customerWidth : customersShape.columns.length = 2 := by decide +kernel
  exact ⟨fun order member => orderWidth ▸ Resolved.sourceRows_width
      (db.valid.admitted.rowsWide 1 _ (Database.table_of_findTable db.raw _ _ _ orders)) order member,
    fun customer member => customerWidth ▸ Resolved.sourceRows_width
      (db.valid.admitted.rowsWide 0 _ (Database.table_of_findTable db.raw _ _ _ customers)) customer member⟩

/-- Source rule of {name}`joined`: for every join kind and database with the catalog of
{name}`shop`, the source rows of the join query are the join ({name}`Resolved.joinRows`) of the
order scan, three cells wide, with the customer scan, two cells wide, without a fault. Proof sketch:
{name}`Resolved.Query.source_two_tables`. -/
theorem joined_source (kind : Resolved.JoinKind) (db : Database) (schema : db.HasCatalog shop) :
    (joined kind).source (Resolved.EvalContext.bound []) db.raw = some
      { rows := Resolved.joinRows (Resolved.EvalContext.bound []) 3 (orderRows db) (customerJoin kind) 2
          (customerRows db) [], width := 5, fault := .none } := by
  obtain ⟨customers, orders⟩ := shop_found db schema
  have orderWidth : ordersShape.columns.length = 3 := by decide +kernel
  have customerWidth : customersShape.columns.length = 2 := by decide +kernel
  rw [Resolved.Query.source_two_tables _ _ _ rfl rfl (Database.table_of_findTable db.raw _ _ _ orders)
    (Database.table_of_findTable db.raw _ _ _ customers)]
  simp only [orderWidth, customerWidth]
  rfl

/-- Result rule of {name}`joined`: for every join kind and rows, every result that the model permits
over the rows is a permutation of the result rows {lit}`[cell 0, cell 4]` of the rows. Proof
sketch: {name}`Resolved.Query.perm_of_mem_possibleResults_plain`; the query has no {lit}`WHERE`. -/
theorem joined_perm {kind : Resolved.JoinKind} {rows result : List (List Value)}
    (member : result ∈ (joined kind).possibleResults (Resolved.EvalContext.bound []) rows) :
    result.Perm (rows.map fun row => [cell 0 row, cell 4 row]) := by
  have perm := Resolved.Query.perm_of_mem_possibleResults_plain rfl rfl rfl rfl rfl member
  rw [Resolved.filtered_of_filter_none _ rfl] at perm
  exact perm

/-- For every join kind, script of the join query of that kind, database with the catalog of
{name}`shop`, environment and property {lit}`Q` of a result: when every permutation of the result
rows of the join ({name}`Resolved.joinRows`) has {lit}`Q`, the script returns a result with {lit}`Q`.
Proof sketch: {name}`Run.query_returnsResult_calm` with {name}`joined_source` and
{name}`joined_perm`. -/
theorem joined_returns (kind : Resolved.JoinKind) (script : Script) (one : script.statements.length = 1)
    (statement : Syntax.Statement) (head : script.statements = [(statement, [])])
    (resolves : resolveStatement runContext (shop.raw.connection {}).resolveState statement =
      .ok (.query (joined kind) [], (shop.raw.connection {}).resolveState))
    (db : Database) (env : Env) (schema : db.HasCatalog shop) (property : List (List Value) → Prop)
    (holds : ∀ result, result.Perm ((Resolved.joinRows (Resolved.EvalContext.bound []) 3 (orderRows db) (customerJoin kind) 2
      (customerRows db) []).map fun row => [cell 0 row, cell 4 row]) → property result) :
    (db.run (query script one) env).returnsResult property := by
  have resolved : resolveStatement runContext (db.raw.connection env.counters).resolveState statement =
      .ok (.query (joined kind) [], (db.raw.connection env.counters).resolveState) := by
    rw [shop_state db env schema]
    exact resolves
  rw [Run.query_returnsResult_calm head one db env resolved (joined_source kind db schema) (by simp)
    (by unfold Resolved.Statement.Calm; cases kind <;> decide +kernel) rfl rfl rfl
    (by simp [Resolved.Query.fails, joined]) (by simp [Resolved.Query.distinctCertain, joined])]
  exact fun result member => holds result (joined_perm member)

end SelectJoinCases
