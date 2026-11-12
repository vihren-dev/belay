import GlobalSignupInvariant

/-! A fixture module of `tests/surface_s6_automation_test.py`: the partial-index invariant of the guide, proved
with the tactic {lit}`sql_run` (ADR 0017, S6). The claims are those of {lit}`SignupInvariantClaims` and
{lit}`GlobalSignupInvariant`, which have explicit proofs with {name}`Sql.ifOk_send_plainInsert`. Here the tactic
reduces the program to the rule of a plain insert. The statement is a field of the site, so the tactic reads
its kind from the hint that closes its resolution. The goal that remains is the final property of the reached
database, which is valid; the unique index of the database gives it by the laws of valid databases. -/

set_option doc.verso true
set_option maxRecDepth 200000
set_option exponentiation.threshold 2000

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- Over every site of the signup, email value {lit}`f` and valid database with the catalog of the site: at most
one live account has the email {lit}`f`. Plain words: the partial unique index of live emails holds in every valid
database that has the catalog of the site, whatever rows it has. Proof sketch: the database has the table and the
index of the site; the key of the index is a unique key of the table ({name}`CatalogIndex.uniqueKey_mem_uniqueKeys`);
{name}`Database.Valid.countMatching_partial_le_one` bounds the count of the live accounts of the email, which is
the right side of {name}`at_most_one_live_account_iff`. -/
theorem AccountSignupSite.keeps_of_valid {db : Database} {e : String} (site : AccountSignupSite db e) (f : Value)
    {reached : Model.Database} (valid : reached.Valid Profile.pinned) (sameCatalog : reached.catalog = db.raw.catalog) :
    Holds (atMostOneLiveAccountWithEmail f) ⟨reached, valid⟩ := by
  have foundAfter : reached.catalog.findTable (name! "accounts") = some (site.position, site.table) := by
    rw [sameCatalog]; exact site.found
  rw [at_most_one_live_account_iff ⟨reached, valid⟩ f site.position site.emailIx site.deletedIx site.table site.emailCell
    site.deletedCell foundAfter site.emailColumn site.emailAt site.deletedColumn site.deletedAt]
  have member : site.index.uniqueKey ∈ reached.catalog.uniqueKeys site.position site.table :=
    CatalogIndex.uniqueKey_mem_uniqueKeys (sameCatalog ▸ site.indexed) _ _ site.indexTable site.indexUnique
  refine valid.countMatching_partial_le_one (Database.table_of_findTable reached _ site.position site.table foundAfter)
    member site.emailAt (filter := liveCondition site.deletedCell site.deletedIx)
    site.indexFilter site.indexKeys _ _ (.parameter 1) (boundValue f) ?_ fun row => ?_
  · intro row guard
    simpa [liveCondition, sql_simp] using guard
  · simp [sql_simp]

/-- The claim of {name}`signup_keeps`, proved with {lit}`sql_run`. The hints close the resolution of the insert,
the table and the model's coverage, and the tactic reads the kind of the statement from the first hint. The
goal that remains is the final property for the reached database, which {name}`AccountSignupSite.keeps_of_valid`
proves. -/
theorem signup_keeps_by_sql_run (e : String) (f : Value) :
    FreshEnsures (send (signupAccount e))
      (fun db => Holds (atMostOneLiveAccountWithEmail f) db ∧ Nonempty (AccountSignupSite db e))
      (ifOk (holds (atMostOneLiveAccountWithEmail f))) := by
  refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_
  rintro db ⟨_, ⟨site⟩⟩ env _complete
  rw [site.script]
  sql_run [site.resolves, Database.table_of_findTable db.raw _ site.position site.table site.found,
    RunStep.continues_iff.1 (site.modeled env)]
  case success =>
    intro _allOk
    exact (Holds.reached_iff_holds_of_valid _ _ _ valid.1).2 (site.keeps_of_valid f valid.1 rfl)

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

/-- The claim of {name}`signup_keeps_global`, proved with {lit}`sql_run` and
{name}`GlobalSignupSite.keeps_of_valid`. -/
theorem signup_keeps_global_by_sql_run (e : String) :
    FreshEnsures (send (signupAccount e))
      (fun db => Holds oneLive db ∧ Nonempty (GlobalSignupSite db e))
      (ifOk (holds oneLive)) := by
  refine (FreshEnsures.ifOkWith_iff _ _ _).2 ?_
  rintro db ⟨_, ⟨site⟩⟩ env _complete
  rw [site.script]
  sql_run [site.resolves, Database.table_of_findTable db.raw _ site.position site.table site.found,
    RunStep.continues_iff.1 (site.modeled env)]
  case success =>
    intro _allOk
    exact (Holds.reached_iff_holds_of_valid _ _ _ valid.1).2 (site.keeps_of_valid valid.1 rfl)

#print axioms signup_keeps_by_sql_run
#print axioms signup_keeps_global_by_sql_run

end AssertionExamples
