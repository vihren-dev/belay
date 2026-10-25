import ExpansionCountQueries

/-! A fixture of `tests/surface_assertion_examples_test.py`: the guide's preserved-count claim as a fresh-run triple
over every admitted database (ADR 0017, S6). The claim reads: if the table of customers has `n` rows, and the
four-statement lowercase-field expansion runs without an error, then the table has `n` rows afterwards. It holds
for every database with a site of the expansion, for every trigger definitions and bound values. The instance
checks that the site and the success are satisfiable, and a database with an old trigger on UPDATE shows what
the site excludes: the backfill fires that trigger, which removes the rows. -/

set_option doc.verso true
set_option maxRecDepth 200000
set_option exponentiation.threshold 2048

namespace AssertionExamples
open Belay.Sqlite Std.Do Belay.Sqlite.NormalizedFieldExpansion Belay.Sqlite.Model.NormalizedField
open Belay.Sqlite.Model hiding Database

/-- The table, its id column, the column that the field lowers and the new field of the guide's expansion. -/
abbrev CustomersSite (db : Database) := Site db.raw (name! "customers") (name! "id") (name! "email")
  (name! "email_lower")

/-- The expansion of the guide's customers for chosen triggers and bound values: add the field, fill it, create
the two triggers. -/
def customersExpansion (first second : Identifier × CatalogTrigger) (firstValues secondValues thirdValues
    fourthValues : List Value) : Script :=
  expansion (name! "customers") (name! "email_lower") (name! "email") first second firstValues secondValues
    thirdValues fourthValues

/-- Over every admitted database with a site of the expansion, every number, every pair of triggers and every
bound values: if the table has {lit}`n` rows and the expansion runs without an error on the database, the table
has {lit}`n` rows afterwards. The success is a condition of the claim because the expansion fails, for example,
when a trigger of that name exists; the claim then says nothing. Proof sketch:
{name}`ifOk_send_expansion` gives the database {lit}`expandedDatabase`; its table keeps the number of rows of
the old one, because the backfill replaces each row by the row with one more cell. -/
theorem expansion_keeps_the_customer_count (n : Int64) (first second : Identifier × CatalogTrigger)
    (firstValues secondValues thirdValues fourthValues : List Value) :
    FreshEnsures (send (customersExpansion first second firstValues secondValues thirdValues fourthValues))
      (fun db => Holds (customerCountIs n) db ∧ Nonempty (CustomersSite db) ∧
        (db.run (customersExpansion first second firstValues secondValues thirdValues fourthValues)).outputs.allOk =
          true)
      (ifOk (holds (customerCountIs n))) := by
  refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_
  rintro db ⟨count, ⟨site⟩, success⟩ env _complete
  have ok := Script.allOk_env success env
  rw [Database.run_script] at ok
  have ranOk : (send (customersExpansion first second firstValues secondValues thirdValues fourthValues)).SucceedsFrom
      env.clock 0 (db.raw.connection env.counters) := (Sql.succeedsFrom_sendStatements _ _ _ _).2 ok
  refine ifOk_send_expansion (name! "customers") (name! "id") (name! "email") (name! "email_lower") first second
    firstValues secondValues thirdValues fourthValues db env site ranOk ?_
  intro outputs final reached valid
  show Holds.reached (customerCountIs n) final (by check_query)
  rw [Holds.reached_iff_holds_of_valid (customerCountIs n) final (by check_query) valid]
  generalize hv : final.connection.state.database = reachedDatabase at reached valid ⊢
  subst reached
  have oldRows : site.table.rows = db.raw.rows.getD site.position [] := by
    have := Database.table_of_findTable db.raw _ site.position site.table.shape site.found
    rw [site.present] at this
    exact congrArg Table.rows (Option.some.inj this)
  have newTable := Database.table_of_findTable
    (expandedDatabase db.raw site.position site.source site.table (name! "email_lower") first second) _ site.position
    (expandedTable site.table (name! "email_lower") site.source).shape
    (expandedDatabase_findTable _ first second site.found)
  rw [expandedDatabase_table (name! "email_lower") first second site.present
    (Database.position_lt_rows db.valid.admitted.rowsShaped site.found)] at newTable
  have newRows : (expandedDatabase db.raw site.position site.source site.table (name! "email_lower") first
      second).rows.getD site.position [] = (expandedTable site.table (name! "email_lower") site.source).rows :=
    (congrArg Table.rows (Option.some.inj newTable)).symm
  rw [customer_count_is_iff _ n site.position _ (expandedDatabase_findTable _ first second site.found)]
  dsimp only
  rw [newRows]
  rw [customer_count_is_iff db n site.position site.table.shape site.found] at count
  simpa [expandedTable, loweredRows, oldRows] using count

/-- The body of both maintenance triggers: copy the lowercase of the new email into the stored field of the
changed row. -/
def maintenanceBody : List Syntax.BodyStatement :=
  [.update (name! "customers")
    [(name! "email_lower", .call "lower" [.qualified (name! "NEW") (name! "email")])]
    (some (.compare .eq (.identifier (name! "id") .none) (.qualified (name! "NEW") (name! "id"))))]

/-- The trigger that runs after every INSERT into {lit}`customers`. -/
def insertTrigger : Identifier × CatalogTrigger :=
  (name! "customers_email_ins",
    { table := name! "customers", time := .after, event := .insert, body := maintenanceBody })

/-- The trigger that runs after an UPDATE of {lit}`email` in {lit}`customers`. -/
def updateTrigger : Identifier × CatalogTrigger :=
  (name! "customers_email_upd",
    { table := name! "customers", time := .after, event := .update [name! "email"], body := maintenanceBody })

/-- The expansion of the guide with the two maintenance triggers and no bound values. -/
def expand : Script := customersExpansion insertTrigger updateTrigger [] [] [] []

/-- The guide's preserved-count claim for the expansion {name}`expand`: the instance of
{name}`expansion_keeps_the_customer_count`. -/
theorem count_kept (n : Int64) :
    FreshEnsures (send expand)
      (fun db => Holds (customerCountIs n) db ∧ Nonempty (CustomersSite db) ∧
        (db.run expand).outputs.allOk = true)
      (ifOk (holds (customerCountIs n))) :=
  expansion_keeps_the_customer_count n insertTrigger updateTrigger [] [] [] []

/-- A database with a site of {name}`expand`: two customers and no trigger. -/
def shop : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  INSERT INTO customers VALUES (1, 'Ada', 'Alpha@X');
  INSERT INTO customers VALUES (2, 'Bob', 'Beta@X');"

/-- The table of {name}`shop`. -/
def shopTable : Table := (shop.raw.table 0).get (by decide +kernel)

/-- The site of the expansion in {name}`shop`: each field is a closed fact about the parsed database. -/
def shopSite : CustomersSite shop :=
  { position := 0, table := shopTable, id := 0, source := 2
    found := by decide +kernel
    present := (Option.some_get _).symm
    fresh := by decide +kernel
    idFound := by decide +kernel
    sourceFound := by decide +kernel
    keysInside := by decide +kernel
    plain := by decide +kernel
    noneFiring := by decide +kernel }

/-- The final context of the expansion from the fresh start of a database with no clock and the counters of a
new connection. -/
def afterExpansion (db : Database) : ExecutionContext :=
  let start := ExecutionContext.initial db { counters := Counters.newConnection }
  start.finish ((send expand).runFrom none 0 start.connection)

-- The instance on `shop`: it has two customers, the expansion runs without an error (the premise of the claim),
-- and two customers remain.
example : Holds (customerCountIs 2) shop := by decide +kernel
example : (shop.run expand).outputs.allOk = true := by decide +kernel
example : (afterExpansion shop).outputs.allOk = true ∧ Holds.reached (customerCountIs 2) (afterExpansion shop) := by
  decide +kernel

/-- A trigger that exists before the expansion may fire during the backfill and remove rows: a deleting trigger
on every UPDATE removes each customer when the field is filled. The database has no site, because the catalog
selects a trigger for the UPDATE of the new field. -/
def purging : Database := db! r"
  CREATE TABLE customers (id INTEGER PRIMARY KEY, name TEXT, email TEXT NOT NULL);
  INSERT INTO customers VALUES (1, 'Ada', 'Alpha@X');
  CREATE TRIGGER purge AFTER UPDATE ON customers BEGIN DELETE FROM customers WHERE id = OLD.id; END;"

theorem an_old_trigger_removes_the_customers :
    Holds (customerCountIs 1) purging ∧ (afterExpansion purging).outputs.allOk = true ∧
    ¬ Holds.reached (customerCountIs 1) (afterExpansion purging) := by
  decide +kernel

#print axioms expansion_keeps_the_customer_count
#print axioms count_kept
#print axioms shopSite

end AssertionExamples
