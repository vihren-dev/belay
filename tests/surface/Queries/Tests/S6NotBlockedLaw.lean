import S6NotBlocked

/-! A fixture module of `tests/surface_s6_not_blocked_test.py`: the guide's query equivalence of {lit}`NOT IN` and
{lit}`NOT EXISTS` (ADR 0017, S6), proved for every database with the stated site. The site says that the customers
table has a rowid alias {lit}`id` with INTEGER affinity as its first column, that the two statements resolve to the
queries of the general laws (the key column against the first column of {lit}`blocked`), and that the database has
both tables. The premise on rows is that no blocked id is NULL. A schema with {lit}`NOT NULL` on the blocked id gives
the premise with {lit}`Database.NotNull`. The three counterexamples of {lit}`S6NotBlocked` show that no premise can be
dropped: the rowid alias excludes the NULL customer id and the collation difference, and the row premise excludes the
NULL blocked id. -/

set_option doc.verso true
set_option maxRecDepth 8192
set_option exponentiation.threshold 2048
set_option sql.check false

namespace S6NotBlocked
open Belay.Sqlite
open Belay.Sqlite.Model hiding Database

/-- The conditions under which the two guide statements resolve to the queries of the general laws, on the database.
The database has the tables {lit}`customers` and {lit}`blocked` at catalog positions. The first column of
{lit}`customers` is the rowid alias {lit}`id` and has INTEGER affinity. The first column of {lit}`blocked` is
{lit}`customer_id`. Each script is one select statement with no values, and it resolves from the idle connection to
the one-table query of the general laws: the comparison affinity is the one of the two columns, and the collations are
free. -/
structure NotBlockedSite (db : Database) where
  /-- The syntax tree of {name}`notBlockedIn`. -/
  inStatement : Syntax.Statement
  /-- The syntax tree of {name}`notBlockedExists`. -/
  existsStatement : Syntax.Statement
  /-- The first script is the statement without values. -/
  inScript : notBlockedIn.statements = [(inStatement, [])]
  /-- The second script is the statement without values. -/
  existsScript : notBlockedExists.statements = [(existsStatement, [])]
  /-- The first statement is a select statement. -/
  inSelect : IsSelectStatement inStatement
  /-- The second statement is a select statement. -/
  existsSelect : IsSelectStatement existsStatement
  /-- The catalog position of {lit}`customers`. -/
  customersPosition : Nat
  /-- The catalog position of {lit}`blocked`. -/
  blockedPosition : Nat
  /-- The catalog entry of {lit}`customers`. -/
  customers : CatalogTable
  /-- The catalog entry of {lit}`blocked`. -/
  blocked : CatalogTable
  /-- The column {lit}`customers.id`. -/
  idCell : CatalogColumn
  /-- The column {lit}`blocked.customer_id`. -/
  customerIdCell : CatalogColumn
  /-- The database has the table {lit}`customers`. -/
  foundCustomers : db.raw.catalog.findTable (name! "customers") = some (customersPosition, customers)
  /-- The database has the table {lit}`blocked`. -/
  foundBlocked : db.raw.catalog.findTable (name! "blocked") = some (blockedPosition, blocked)
  /-- The first column of {lit}`customers` is {lit}`id`. -/
  idFirst : customers.columns[0]? = some idCell
  /-- The first column of {lit}`blocked` is {lit}`customer_id`. -/
  customerIdFirst : blocked.columns[0]? = some customerIdCell
  /-- The column {lit}`id` is the rowid alias of {lit}`customers`. -/
  idAlias : customers.rowidAlias = some 0
  /-- The column {lit}`id` has INTEGER affinity. -/
  idInteger : idCell.affinity = .integer
  /-- The comparison affinity of the two columns. -/
  affinity : Option Affinity
  /-- The comparison affinity is the one that the resolver gives the two columns. -/
  affinityIs : affinity = comparisonAffinity (some idCell.affinity) (some customerIdCell.affinity)
  /-- The collation of the {lit}`IN` test. -/
  inCollation : Collation
  /-- The collation of the comparison {lit}`=`. -/
  equalsCollation : Collation
  /-- The resolution state after the first statement. -/
  afterIn : ResolveState
  /-- The resolution state after the second statement. -/
  afterExists : ResolveState
  /-- The first statement resolves to {lit}`NOT IN` of the key against the first column of {lit}`blocked`. -/
  resolvesIn : resolveStatement runContext (db.raw.connection {}).resolveState inStatement =
    .ok (.query (Resolved.Query.oneTable customersPosition 0
        (some (.inQuery (.column 0) 0 affinity inCollation true)) [.column 0] ["id"])
      [Resolved.Query.oneTable blockedPosition customers.columns.length none
        [.column (customers.columns.length + 0)] ["customer_id"]], afterIn)
  /-- The second statement resolves to {lit}`NOT EXISTS` of the correlated comparison. -/
  resolvesExists : resolveStatement runContext (db.raw.connection {}).resolveState existsStatement =
    .ok (.query (Resolved.Query.oneTable customersPosition 0 (some (.not (.exists 0))) [.column 0] ["id"])
      [Resolved.Query.oneTable blockedPosition customers.columns.length
        (some (.compare .eq affinity (.column (customers.columns.length + 0)) (.column 0) equalsCollation))
        [.literal (.integer 1)] ["1"]], afterExists)

/-- No row of {lit}`blocked` has a NULL {lit}`customer_id`: the cell at position 0 of every row is not NULL. -/
def NoNullBlockedId {db : Database} (site : NotBlockedSite db) : Prop :=
  ∀ row ∈ db.raw.rows.getD site.blockedPosition [], (row.values.getD 0 .null).isNull = false

/-- For every database with the site, every environment, and no NULL blocked id: the two guide scripts are
equivalent ({name}`Sql.EquivAt`) at the initial context of the database. The premises are the rowid alias of
{lit}`customers.id` (in the site) and the row premise {name}`NoNullBlockedId`. Proof sketch: the general law
{name}`Sql.EquivAt.notIn_notExists_of_rowidAlias` with the two resolutions of the site; the alias cells of an admitted
database are the rowids, the comparison affinity is not TEXT because {lit}`id` has INTEGER affinity, and the cells of
the scan of {lit}`blocked` are the cells of its rows. -/
theorem notBlocked_equivalent {db : Database} (site : NotBlockedSite db) (noNull : NoNullBlockedId site) (env : Env) :
    Sql.EquivAt (send notBlockedIn) (send notBlockedExists) (ExecutionContext.initial db env) := by
  have presentCustomers := Database.table_of_findTable db.raw _ _ _ site.foundCustomers
  have presentBlocked := Database.table_of_findTable db.raw _ _ _ site.foundBlocked
  refine Sql.EquivAt.notIn_notExists_of_rowidAlias (parameters := []) site.inSelect site.existsSelect
    site.customersPosition site.blockedPosition site.customers.columns.length 0 0 _ _ [0] ["id"] ["customer_id"]
    ["1"] site.affinity site.inCollation site.equalsCollation ?_ presentCustomers presentBlocked site.idAlias
    (db.valid.admitted.rowsAliased _ _ presentCustomers) ?_ ?_ site.inScript site.existsScript
    site.resolvesIn site.resolvesExists
  · exact (List.getElem?_eq_some_iff.1 site.idFirst).1
  · rw [site.affinityIs, site.idInteger]
    exact comparisonAffinity_integer_ne_text _
  · intro cells member
    obtain ⟨row, inRows, rfl⟩ := (mem_sourceRows_iff _ cells).1 member
    exact noNull row inRows

/-- For every database with the site whose blocked id is declared {lit}`NOT NULL`: no blocked id is NULL, so the two
guide scripts are equivalent at the initial context of the database. Plain words: with {lit}`NOT NULL` in the schema
of {lit}`blocked` and a valid database, the row premise {name}`NoNullBlockedId` needs no assumption. Proof sketch: a
row of a valid database has one cell for each column ({name}`Database.Admitted.rowsWide`), and the cell of a
{lit}`NOT NULL` column is not NULL ({name}`Database.NotNull`); apply {name}`notBlocked_equivalent`. -/
theorem notBlocked_equivalent_of_notNull {db : Database} (site : NotBlockedSite db)
    (declared : site.customerIdCell.notNull = true) (env : Env) :
    Sql.EquivAt (send notBlockedIn) (send notBlockedExists) (ExecutionContext.initial db env) := by
  have presentBlocked := Database.table_of_findTable db.raw _ _ _ site.foundBlocked
  refine notBlocked_equivalent site ?_ env
  intro row inRows
  have wide := db.valid.admitted.rowsWide _ _ presentBlocked row inRows
  have inside : 0 < row.values.length := by
    rw [show row.values.length = site.blocked.columns.length from wide]
    exact (List.getElem?_eq_some_iff.1 site.customerIdFirst).1
  have cell : row.values[0]? = some row.values[0] := List.getElem?_eq_getElem inside
  have known := db.valid.notNull _ _ presentBlocked row inRows 0 site.customerIdCell _ site.customerIdFirst cell declared
  rw [List.getD_eq_getElem?_getD, cell]
  cases value : row.values[0] <;> simp_all [Value.isNull]

/-- The catalog entry of {lit}`customers` and its position in {name}`premisesHold`. -/
def customersEntry : Nat × CatalogTable :=
  (premisesHold.raw.catalog.findTable (name! "customers")).get (by decide +kernel)

/-- The catalog entry of {lit}`blocked` and its position in {name}`premisesHold`. -/
def blockedEntry : Nat × CatalogTable :=
  (premisesHold.raw.catalog.findTable (name! "blocked")).get (by decide +kernel)

/-- The database {name}`premisesHold` has the site: the site is satisfiable, and the tables of the site are the ones
of the schema of the fixture. -/
def premisesHoldSite : NotBlockedSite premisesHold where
  inStatement := (notBlockedIn.statements[0]'(by decide +kernel)).1
  existsStatement := (notBlockedExists.statements[0]'(by decide +kernel)).1
  inScript := by rfl
  existsScript := by rfl
  inSelect := ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  existsSelect := ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩
  customersPosition := customersEntry.1
  blockedPosition := blockedEntry.1
  customers := customersEntry.2
  blocked := blockedEntry.2
  idCell := customersEntry.2.columns[0]'(by decide +kernel)
  customerIdCell := blockedEntry.2.columns[0]'(by decide +kernel)
  foundCustomers := by decide +kernel
  foundBlocked := by decide +kernel
  idFirst := by decide +kernel
  customerIdFirst := by decide +kernel
  idAlias := by decide +kernel
  idInteger := by decide +kernel
  affinity := comparisonAffinity (some (customersEntry.2.columns[0]'(by decide +kernel)).affinity)
    (some (blockedEntry.2.columns[0]'(by decide +kernel)).affinity)
  affinityIs := rfl
  inCollation := .binary
  equalsCollation := .binary
  afterIn := (premisesHold.raw.connection {}).resolveState
  afterExists := (premisesHold.raw.connection {}).resolveState
  resolvesIn := by rfl
  resolvesExists := by rfl

/-- On the database {name}`premisesHold` no blocked id is NULL. -/
theorem premisesHold_noNullBlocked : NoNullBlockedId premisesHoldSite := by
  unfold NoNullBlockedId
  decide +kernel

/-- The general theorem applies to {name}`premisesHold`: the two scripts are equivalent there, for every
environment. This is the instance of {name}`notBlocked_equivalent` that shows the premises are satisfiable. -/
theorem premisesHold_equivalent (env : Env) :
    Sql.EquivAt (send notBlockedIn) (send notBlockedExists) (ExecutionContext.initial premisesHold env) :=
  notBlocked_equivalent premisesHoldSite premisesHold_noNullBlocked env

/-- On the database {name}`premisesHold` both scripts give the customer 1, which no blocked id names. The native
SQLite check of `tests/surface_s6_not_blocked_test.py` gives the same rows. Proof sketch: kernel evaluation of the run
of the first script; the second script has the same outputs by {name}`premises_give_equal_outputs`. -/
theorem premisesHold_rows : outputsOn notBlockedIn premisesHold = [.rows [[.integer 1]]] := by
  decide +kernel

#print axioms notBlocked_equivalent
#print axioms premisesHold_rows
#print axioms notBlocked_equivalent_of_notNull
#print axioms premisesHold_equivalent

end S6NotBlocked
