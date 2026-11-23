import AddCustomerQueries

/-! A fixture module of `tests/surface_s6_automation_test.py`: the guide's insertion claim about the program that
uses a result, proved with the tactic {lit}`sql_run` and, for the same proposition, with the public step rules
alone (ADR 0017, S6). The program, the site and the claim are those of {lit}`AddCustomerQueries`. The tactic
reduces the query to the premises of its rule and the insert to the cases of the kind rule of plain INSERT; the
hints close the resolution of the insert and select the case of the table, and the premise about the model's
coverage of the insert and the final property stay as goals. -/

set_option doc.verso true
set_option maxRecDepth 200000
set_option exponentiation.threshold 2000

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- The claim of {lit}`addCustomer_adds` in {lit}`AddCustomerClaims`, proved with {lit}`sql_run`: the tactic applies the rule for the
query and the kind rule of plain INSERT and leaves three goals, which the proof closes by name. The goal
{lit}`modeled` is that the step of the insert for the id that the query returned continues, which the site gives
for every id in the result of the query. The goal {lit}`success` is the final property in the context after the
stored row ({name}`customer_named_after_insert`); the tactic closes the case of a failed insert. The goal
{lit}`h_2` is the branch of a query without one value, where the program returns {lean}`false`. -/
theorem addCustomer_adds_by_sql_run (name email : String) :
    FreshEnsures (addCustomer name email) (fun db => Nonempty (AddCustomerSite db name email))
      (⇓ ok final => ⌜ok = true → Holds.reached (customerNamed name) final⌝) := by
  rintro db ⟨site⟩ env _complete
  sql_run [site.insertResolves, Database.table_of_findTable db.raw _ site.position site.table site.found,
    RunStep.continues_iff.1 (site.selectModeled env)]
  case modeled =>
    rename_i next found
    have mem : next ∈ selectedValues (runScriptStep runContext env.clock 0 (db.raw.connection env.counters)
        selectStatement []).output := mem_selectedValues choice found
    exact List.all_eq_true.1 (site.insertModeled env) next mem
  case success => exact fun _allOk => customer_named_after_insert site _ _ valid rfl
  case h_2 =>
    intro impossible
    cases impossible

/-- The same claim as {name}`addCustomer_adds_by_sql_run`, proved with the public rules and without the
tactic: {name}`Sql.check_single_select` for the query, and for the insert {name}`Sql.check_send_of_rule` with the
kind rule {name}`runScriptStep_plainInsert_eq`, split on its cases after the table of the site selects one. -/
theorem addCustomer_adds_by_rules (name email : String) :
    FreshEnsures (addCustomer name email) (fun db => Nonempty (AddCustomerSite db name email))
      (⇓ ok final => ⌜ok = true → Holds.reached (customerNamed name) final⌝) := by
  rintro db ⟨site⟩ env _complete
  unfold addCustomer
  refine (Sql.check_bind _ _ _ _).2 ?_
  refine Sql.check_single_select (statement := selectStatement) (values := []) rfl rfl ?_ ?_
  · exact RunStep.continues_iff.1 (site.selectModeled env)
  intro selected choice
  cases found : singleValue (queryResult selected) with
  | none =>
    refine (Sql.check_pure _ _ _).2 ?_
    intro impossible
    cases impossible
  | some next =>
    simp only []
    refine (Sql.check_bind _ _ _ _).2 ?_
    rw [insertCustomerAt_script]
    have mem : next ∈ selectedValues (runScriptStep runContext env.clock 0 (db.raw.connection env.counters)
        selectStatement []).output := mem_selectedValues choice found
    have rule := runScriptStep_plainInsert_eq (connection := db.raw.connection env.counters) (clock := env.clock)
      (index := 1) (parameters := [next, .text name.toUTF8.toList, .text email.toUTF8.toList]) site.insertResolves
    refine Sql.check_send_of_rule rule (ExecutionContext.initial_holds_valid db env)
      (RunStep.continues_of_rule rule (List.all_eq_true.1 (site.insertModeled env) next mem)) ?_
    dsimp only
    erw [Database.table_of_findTable db.raw _ site.position site.table site.found]
    dsimp only
    repeat' split
    all_goals first
      | exact trivial
      | refine Sql.sendReached_single (fun _ same => by cases same) fun valid => (Sql.check_pure _ _ _).2 ?_
    · exact fun _allOk => customer_named_after_insert site next _ valid rfl
    · intro allOk
      simp [List.allOk, Output.isError] at allOk

/-- The insertion claim as a standard triple for the initial context of a database with a site, proved with
{lit}`sql_run` after {lit}`mvcgen` has unfolded {name}`addCustomer`. The generated condition is a check of the
program, which the tactic reduces to the same three goals as for the fresh-run claim. -/
theorem addCustomer_adds_triple (name email : String) (db : Database) (env : Env)
    (site : AddCustomerSite db name email) :
    ⦃fun state : ExecutionContext => ⌜state = ExecutionContext.initial db env⌝⦄
      addCustomer name email
    ⦃⇓ ok final => ⌜ok = true → Holds.reached (customerNamed name) final⌝⦄ := by
  mvcgen [addCustomer]
  sql_run [site.insertResolves, Database.table_of_findTable db.raw _ site.position site.table site.found,
    RunStep.continues_iff.1 (site.selectModeled env)]
  case modeled =>
    rename_i next found
    have mem : next ∈ selectedValues (runScriptStep runContext env.clock 0 (db.raw.connection env.counters)
        selectStatement []).output := mem_selectedValues choice found
    exact List.all_eq_true.1 (site.insertModeled env) next mem
  case success => exact fun _allOk => customer_named_after_insert site _ _ valid rfl
  case h_2 =>
    intro impossible
    cases impossible

#print axioms addCustomer_adds_triple
#print axioms addCustomer_adds_by_sql_run
#print axioms addCustomer_adds_by_rules

end AssertionExamples
