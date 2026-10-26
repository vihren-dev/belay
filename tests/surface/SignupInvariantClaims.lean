import AccountSignupQueries

/-! A fixture of `tests/surface_assertion_examples_test.py`: the guide's invariant example as a fresh-run triple
over every admitted database (ADR 0017, S6). The invariant reads: at most one live account has an email. With the
partial unique index on `accounts (email) WHERE deleted_at IS NULL` it holds before and after the signup, because
every database that SQLite writes keeps the index. The ordinary `UNIQUE (email, deleted_at)` does not give it,
because two NULL deletion times are distinct for `UNIQUE`: the instance database shows the counterexample. -/

set_option doc.verso true
set_option maxRecDepth 200000
set_option exponentiation.threshold 2000

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- The conditions under which {name}`signupAccount` is a plain insert of a live account and the database
enforces the partial unique index of live emails: the table {lit}`accounts` has the columns {lit}`email` and
{lit}`deleted_at`; the catalog has a unique index on that table with the one key {lit}`email`, under the
collation of the column, and the filter {lit}`deleted_at IS NULL`; the statement resolves from the idle
connection to a plain insert, which has no rule of a trigger or a foreign key; and the model runs it for every
clock and every counter. -/
structure AccountSignupSite (db : Database) (e : String) where
  /-- The syntax tree of the statement. -/
  statement : Syntax.Statement
  /-- The script is this statement with the one bound value. -/
  script : signupAccount e = ⟨[(statement, [.text e.toUTF8.toList])]⟩
  /-- The catalog position of {lit}`accounts`. -/
  position : Nat
  /-- The catalog entry of {lit}`accounts`. -/
  table : CatalogTable
  /-- The positions of the columns {lit}`email` and {lit}`deleted_at`. -/
  emailIx : Nat
  deletedIx : Nat
  /-- The two columns. -/
  emailCell : CatalogColumn
  deletedCell : CatalogColumn
  /-- The cells of the resolved insert, and the resolution state after the statement. -/
  cells : List (List Resolved.Cell)
  after : ResolveState
  /-- The database has the table. -/
  found : db.raw.catalog.findTable (name! "accounts") = some (position, table)
  /-- The columns are at the positions. -/
  emailColumn : columnPosition table.columns (name! "email") = some emailIx
  emailAt : table.columns[emailIx]? = some emailCell
  deletedColumn : columnPosition table.columns (name! "deleted_at") = some deletedIx
  deletedAt : table.columns[deletedIx]? = some deletedCell
  /-- The partial unique index of live emails. -/
  indexName : Identifier
  index : CatalogIndex
  indexed : ({ name := indexName, entry := .index index } : CatalogObject) ∈ db.raw.catalog
  indexTable : index.table = position
  indexUnique : index.unique = true
  indexKeys : index.keys = [{ term := .column emailIx, descending := false, collation := emailCell.collation }]
  indexFilter : index.filter = some (liveCondition deletedCell deletedIx)
  /-- The statement resolves to a plain insert. -/
  resolves : resolveStatement runContext (db.raw.connection {}).resolveState statement =
    .ok (.insert position cells [] [] none, after)
  /-- The model runs the statement, whatever the clock and the counters. -/
  modeled : ∀ env : Env, (runScriptStep runContext env.clock 0 (db.raw.connection env.counters) statement
    [.text e.toUTF8.toList]).continues = true

/-- Over every admitted database with a site of the signup, every email and every email value {lit}`f`: if at most
one live account has the email {lit}`f` and the signup runs without an error, at most one live account has it
afterwards. Plain words: the invariant of the guide, for each email value. The final database is valid, so it
keeps its unique indexes, and the signup does not change the catalog. Proof sketch:
{name}`Sql.ifOk_send_plainInsert` gives the final database as the old one with other rows; the key of the index
is a unique key of the table ({name}`Catalog.uniqueKeys`); and
{name}`Table.KeysUnique.countMatching_partial_le_one` bounds the count of the live accounts of the email. -/
theorem signup_keeps (e : String) (f : Value) :
    FreshEnsures (send (signupAccount e))
      (fun db => Holds (atMostOneLiveAccountWithEmail f) db ∧ Nonempty (AccountSignupSite db e))
      (ifOk (holds (atMostOneLiveAccountWithEmail f))) := by
  refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_
  rintro db ⟨_, ⟨site⟩⟩ env _complete
  rw [site.script]
  refine Sql.ifOk_send_plainInsert (table := ⟨site.table, db.raw.rows.getD site.position []⟩)
    site.resolves (Database.table_of_findTable db.raw _ site.position site.table site.found)
    (RunStep.continues_iff.1 (site.modeled env)) ?_
  intro value outputs final reached valid _allOk
  show Holds.reached (atMostOneLiveAccountWithEmail f) final (by check_query)
  rw [Holds.reached_iff_holds_of_valid _ final _ valid]
  generalize hv : final.connection.state.database = reachedDatabase at reached valid ⊢
  obtain ⟨rows, rfl⟩ : ∃ rows, reachedDatabase = db.raw.setRows site.position rows := ⟨_, reached⟩
  have foundAfter : (db.raw.setRows site.position rows).catalog.findTable (name! "accounts") =
      some (site.position, site.table) := site.found
  rw [at_most_one_live_account_iff ⟨db.raw.setRows site.position rows, valid⟩ f site.position site.emailIx site.deletedIx site.table site.emailCell
    site.deletedCell foundAfter site.emailColumn site.emailAt site.deletedColumn site.deletedAt]
  have present := Database.table_of_findTable (db.raw.setRows site.position rows) _ site.position site.table foundAfter
  have member : site.index.uniqueKey ∈ (db.raw.setRows site.position rows).catalog.uniqueKeys site.position site.table :=
    List.mem_append_right _ (List.mem_filterMap.2 ⟨_, site.indexed, by simp [site.indexTable, site.indexUnique]⟩)
  refine Table.KeysUnique.countMatching_partial_le_one (valid.unique _ _ present)
    (valid.admitted.rowsStored _ _ present) member site.emailAt (filter := liveCondition site.deletedCell site.deletedIx)
    site.indexFilter site.indexKeys _ _ (.parameter 1) (boundValue f) ?_ fun row => ?_
  · intro row guard
    simpa [liveCondition, sql_simp] using guard
  · simp [sql_simp]

/-- A database with a site of the signup: one live account for {lit}`a@x`, one deleted account for {lit}`b@x`, and the
partial unique index of live emails. -/
def accounts : Database := db! r"
  CREATE TABLE accounts (id INTEGER PRIMARY KEY, email TEXT NOT NULL, deleted_at TEXT);
  CREATE UNIQUE INDEX accounts_live ON accounts (email) WHERE deleted_at IS NULL;
  INSERT INTO accounts (email) VALUES ('a@x');
  INSERT INTO accounts (email, deleted_at) VALUES ('b@x', '2026-10-01');"

/-- The catalog position and entry of {lit}`accounts` in {name}`accounts`. -/
def accountsTable : Nat × CatalogTable := (accounts.raw.catalog.findTable (name! "accounts")).get (by decide +kernel)

/-- The partial unique index of live emails of {name}`accounts`, as the catalog stores it. -/
def accountsLiveIndex : CatalogIndex :=
  { table := 0, keys := [{ term := .column 1 }], unique := true,
    filter := some (liveCondition ((accountsTable.2.columns[2]?).get (by decide +kernel)) 2) }

/-- The site of the signup of {lit}`c@x` in {name}`accounts`: each field is a closed fact about the parsed database. -/
def accountsSite : AccountSignupSite accounts "c@x" where
  statement := .insert (name! "accounts") (some [name! "email"]) [[.parameter 1]] []
  script := rfl
  position := accountsTable.1
  table := accountsTable.2
  emailIx := 1
  deletedIx := 2
  emailCell := (accountsTable.2.columns[1]?).get (by decide +kernel)
  deletedCell := (accountsTable.2.columns[2]?).get (by decide +kernel)
  cells := [[.value .null, .expression (.parameter 1), .value .null]]
  after := (accounts.raw.connection {}).resolveState
  found := by decide +kernel
  emailColumn := by decide +kernel
  emailAt := by decide +kernel
  deletedColumn := by decide +kernel
  deletedAt := by decide +kernel
  indexName := name! "accounts_live"
  index := accountsLiveIndex
  indexed := by decide +kernel
  indexTable := by decide +kernel
  indexUnique := rfl
  indexKeys := by decide +kernel
  indexFilter := by decide +kernel
  resolves := by decide +kernel
  modeled := fun env => by with_unfolding_all rfl

/-- The final context of the signup from the fresh start of a database, with no clock and the counters of a new
connection. -/
def afterSignup (db : Database) (email : String) : ExecutionContext :=
  let start := ExecutionContext.initial db { counters := Counters.newConnection }
  start.finish ((send (signupAccount email)).runFrom none 0 start.connection)

/-- The email {lit}`a@x` as a value. -/
def emailA : Value := .text "a@x".toUTF8.toList

-- The instance on `accounts`: the invariant holds, a signup of a new email runs and keeps it, a signup of the live
-- email fails (the trace has an error, so the conditional postcondition requires nothing), and a signup of the
-- email of the deleted account runs and keeps it.
example : Holds (atMostOneLiveAccountWithEmail emailA) accounts := by decide +kernel
example : (afterSignup accounts "c@x").outputs.allOk = true ∧
    Holds.reached (atMostOneLiveAccountWithEmail emailA) (afterSignup accounts "c@x") := by decide +kernel
example : (afterSignup accounts "a@x").outputs.allOk = false := by decide +kernel
-- The failed statement is rolled back by the actual run: the live account remains alone and the invariant holds.
example : (afterSignup accounts "a@x").outputs.allOk = false ∧
    Holds.reached (atMostOneLiveAccountWithEmail emailA) (afterSignup accounts "a@x") := by decide +kernel
example : (afterSignup accounts "b@x").outputs.allOk = true ∧
    Holds.reached (atMostOneLiveAccountWithEmail (.text "b@x".toUTF8.toList)) (afterSignup accounts "b@x") := by
  decide +kernel

/-- The ordinary {lit}`UNIQUE` constraint does not give the invariant: two NULL deletion times are distinct for
{lit}`UNIQUE`, so the signup of the email of a live account runs, and two live accounts have the email. -/
def nullableUnique : Database := db! r"
  CREATE TABLE accounts (id INTEGER PRIMARY KEY, email TEXT NOT NULL, deleted_at TEXT, UNIQUE (email, deleted_at));
  INSERT INTO accounts (email) VALUES ('a@x');"

/-- In {name}`nullableUnique` at most one live account has the email {lit}`a@x` before the signup of that email,
the signup succeeds, and afterwards two live accounts have it: an ordinary {lit}`UNIQUE` over a column
that can be NULL does not keep the invariant, which needs the partial unique index. -/
theorem unique_with_null_does_not_keep_the_invariant :
    Holds (atMostOneLiveAccountWithEmail emailA) nullableUnique ∧
    (afterSignup nullableUnique "a@x").outputs.allOk = true ∧
    ¬ Holds.reached (atMostOneLiveAccountWithEmail emailA) (afterSignup nullableUnique "a@x") := by
  decide +kernel

#print axioms signup_keeps
#print axioms accountsSite

end AssertionExamples
