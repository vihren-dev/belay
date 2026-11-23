import SignupInvariantClaims
import SelectDuplicateKeySupport

/-! A fixture module of `tests/surface_assertion_examples_test.py`: the global form of the signup invariant of the
guide (ADR 0017, S6). The query `SELECT 1 WHERE NOT EXISTS (SELECT email FROM accounts WHERE deleted_at IS NULL GROUP BY
email HAVING count(*) > 1)` holds exactly when no two live accounts have emails that compare equal. For every admitted
database with a site of the signup and NOT NULL on the email, if it holds and the signup succeeds, it holds afterwards.
The partial unique index of live emails gives it; the ordinary `UNIQUE (email, deleted_at)` does not. -/

set_option doc.verso true
set_option maxRecDepth 200000
set_option exponentiation.threshold 2000

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- The global invariant of the guide: no email has two live accounts. -/
def oneLive : Script :=
  sql r"SELECT 1 WHERE NOT EXISTS (SELECT email FROM accounts WHERE deleted_at IS NULL GROUP BY email HAVING count(*) > 1)"

/-- The sufficient conditions of the global invariant: the site of {name}`signupAccount` as for {name}`signup_keeps`,
and the column {lit}`email` is declared NOT NULL, so that the index on it applies to every live account. -/
structure GlobalSignupSite (db : Database) (e : String) extends AccountSignupSite db e where
  /-- The email column is declared NOT NULL. -/
  emailNotNull : emailCell.notNull = true

/-- Over every database with a table {lit}`accounts` that has the columns {lit}`email` and {lit}`deleted_at`:
{name}`oneLive` holds exactly when no two live accounts have emails that compare equal under the collation of the
email column. Plain words: among the rows of the table in scan order for which {lit}`deleted_at IS NULL` is true, no
row has an email equal to the email of a row before it. Proof sketch: {name}`noDuplicateKeys_claims` and
{name}`keyGroupsShort_iff_pairwise` with the resolution of the column {lit}`email` as result column and grouping
term, and of the filter by {name}`resolveOperand_column_is_null`. -/
theorem one_live_iff (db : Database) (position emailIx deletedIx : Nat)
    (table : CatalogTable) (emailCell deletedCell : CatalogColumn)
    (found : db.raw.catalog.findTable (name! "accounts") = some (position, table))
    (emailColumn : columnPosition table.columns (name! "email") = some emailIx)
    (emailAt : table.columns[emailIx]? = some emailCell)
    (deletedColumn : columnPosition table.columns (name! "deleted_at") = some deletedIx)
    (deletedAt : table.columns[deletedIx]? = some deletedCell) :
    Holds oneLive db ↔
      (Resolved.keptRows (Resolved.EvalContext.bound []) (some (liveCondition deletedCell deletedIx))
        (Resolved.sourceRows { shape := table, rows := db.raw.rows.getD position [] })).Pairwise
        fun earlier later => emailCell.collation.compare (later.getD emailIx .null) (earlier.getD emailIx .null) ≠ .eq := by
  obtain ⟨columnName, affinity, columns⟩ := resolveColumns_identifier_at runContext.profile.dqsDml
    { current := some 0, aggregates := [.callStar "count"] } (some position) _ table.columns _ _ (quote := .none) emailColumn
    none "email"
  have filterResolves := FilterResolves.of_term (dqs := runContext.profile.dqsDml)
    (scope := tableScope db.raw.catalog { table := name! "accounts", alias := none } position table) (aliases := [])
    (shapes := { current := some 0, aggregates := [.callStar "count"] })
    (term := .compare .is (.identifier (name! "deleted_at") .none) .null) (by simp [namesAlias])
    (result := (liveCondition deletedCell deletedIx, none))
    (resolveOperand_column_is_null _ _ _ _ _ _ _ deletedColumn deletedAt)
  have whereCalm : ∀ condition ∈ (some (liveCondition deletedCell deletedIx)).toList, condition.Calm := by
    intro condition member
    obtain rfl : condition = liveCondition deletedCell deletedIx := by simpa using member
    simp [liveCondition, Resolved.Expr.Calm, Resolved.Expr.any, Resolved.Expr.isFallibleCall,
      Resolved.Expr.readsClockHere, Resolved.Expr.readsCounterHere]
  refine Iff.trans (noDuplicateKeys_claims (script := oneLive) (isQuery := by check_query)
    (head := rfl) (count := rfl) (namedSource := rfl) (current := rfl) (arguments := rfl) (found := found)
    (notCall := rfl) (noCalls := rfl) (columnResolves := columns) (columnGrouped := by simp [Resolved.Expr.grouped])
    (columnFeeds := by simp [Resolved.Expr.any, Resolved.Expr.isFallibleCall]) (filterResolves := filterResolves)
    (groupResolves := GroupTermResolvesIn.identifier_table (quote := .none) emailColumn) (whereCalm := whereCalm)
    (columnCalm := Resolved.Expr.calm_column _) (keyCalm := Resolved.Expr.calm_column _)).1 ?_
  rw [keyGroupsShort_iff_pairwise]
  simp [keptTableRows, emailAt, Resolved.Expr.eval_column]

/-- Over every site of the signup with NOT NULL on the email and every valid database with the catalog of the
site: no email has two live accounts. Plain words: the global invariant of the guide holds in every valid database
with the catalog of the site. Proof sketch: as for {name}`AccountSignupSite.keeps_of_valid`, with
{name}`Database.Valid.keptRows_pairwise` for the live rows, whose emails are never NULL, and {name}`one_live_iff`
for the query. -/
theorem GlobalSignupSite.keeps_of_valid {db : Database} {e : String} (site : GlobalSignupSite db e)
    {reached : Model.Database} (valid : reached.Valid Profile.pinned) (sameCatalog : reached.catalog = db.raw.catalog) :
    Holds oneLive ⟨reached, valid⟩ := by
  have foundAfter : reached.catalog.findTable (name! "accounts") = some (site.position, site.table) := by
    rw [sameCatalog]; exact site.found
  rw [one_live_iff ⟨reached, valid⟩ site.position site.emailIx site.deletedIx site.table
    site.emailCell site.deletedCell foundAfter site.emailColumn site.emailAt site.deletedColumn site.deletedAt]
  have member : site.index.uniqueKey ∈ reached.catalog.uniqueKeys site.position site.table :=
    CatalogIndex.uniqueKey_mem_uniqueKeys (sameCatalog ▸ site.indexed) _ _ site.indexTable site.indexUnique
  refine valid.keptRows_pairwise (Database.table_of_findTable reached _ site.position site.table foundAfter)
    member site.indexKeys site.emailAt site.emailNotNull _ _ fun row guard => ?_
  simpa [liveCondition, sql_simp, CatalogIndex.uniqueKey, site.indexFilter] using guard

/-- Over every admitted database with a site of the signup and NOT NULL on the email, and every email: if no email has two
live accounts and the signup runs without an error, no email has two live accounts afterwards. Plain words: the global
invariant of the guide is kept by the signup. The premise on the database is the site, which names the partial unique
index of live emails and the NOT NULL of the email; it does not state the invariant of the final database. Proof sketch:
as for {name}`signup_keeps`, with {name}`GlobalSignupSite.keeps_of_valid` for the final database. -/
theorem signup_keeps_global (e : String) :
    FreshEnsures (send (signupAccount e))
      (fun db => Holds oneLive db ∧ Nonempty (GlobalSignupSite db e))
      (ifOk (holds oneLive)) := by
  refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_
  rintro db ⟨_, ⟨site⟩⟩ env _complete
  rw [site.script]
  refine Sql.check_send_of_rule (runScriptStep_plainInsert_eq site.resolves) (ExecutionContext.initial_holds_valid _ _)
    (RunStep.continues_of_rule (runScriptStep_plainInsert_eq site.resolves) (site.modeled env)) ?_
  dsimp only
  repeat' split
  all_goals first
    | exact trivial
    | refine Sql.sendReached_single (fun _ same => by cases same) fun valid allOk => ?_
  · exact (Holds.reached_iff_holds_of_valid _ _ _ valid.1).2 (site.keeps_of_valid valid.1 rfl)
  · simp [ExecutionContext.next, List.allOk, Output.isError] at allOk

/-- In {name}`nullableUnique` no email has two live accounts before the signup of {lit}`a@x`, the signup succeeds, and
afterwards two live accounts have the email: an ordinary {lit}`UNIQUE` over a column that can be NULL does not keep the
global invariant either. -/
theorem unique_with_null_does_not_keep_one_live :
    Holds oneLive nullableUnique ∧ (afterSignup nullableUnique "a@x").outputs.allOk = true ∧
    ¬ Holds.reached oneLive (afterSignup nullableUnique "a@x") := by
  decide +kernel

#print axioms one_live_iff
#print axioms signup_keeps_global
#print axioms unique_with_null_does_not_keep_one_live

end AssertionExamples
