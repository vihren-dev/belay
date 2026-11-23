import AddCustomerQueries

/-! A fixture module of `tests/surface_assertion_examples_test.py`: the guide's claim about the program that uses a
result, as a fresh-run triple over every admitted database (ADR 0017, S6). When {name}`addCustomer` reports
success, a customer with the name exists. The claim depends on the result of the first query only through the
conditions of {name}`AddCustomerSite`; it holds for every id the query returns, also an id that makes the insert
fail, because a failed insert gives the value {lean}`false`. -/

set_option doc.verso true
set_option maxRecDepth 200000
set_option exponentiation.threshold 2000

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- For every name and email, every admitted database with an {name}`AddCustomerSite`, every environment and
every run of the program {name}`addCustomer` from the fresh start: if the program returns {lean}`true`, a
customer with the name exists in the final database. When the query returns no single value, the program returns
{lean}`false` and the claim requires nothing. A trigger that removes the new customer is outside the site, and
the next module keeps it as a counterexample. Proof sketch: the check of the query is the check of its one step;
a SELECT keeps the connection ({name}`Belay.Sqlite.Model.runScriptStep_select_connection`); for the value of the
query, the kind rule of plain INSERT ({name}`runScriptStep_plainInsert_eq`) with {name}`Sql.check_send_of_rule`
splits the insert on its cases: a failure gives {lean}`false`, and a success stores the one row
({name}`customer_named_after_insert`). -/
theorem addCustomer_adds (name email : String) :
    FreshEnsures (addCustomer name email) (fun db => Nonempty (AddCustomerSite db name email))
      (⇓ ok final => ⌜ok = true → Holds.reached (customerNamed name) final⌝) := by
  rintro db ⟨site⟩ env _complete
  unfold addCustomer
  refine (Sql.check_bind _ _ _ _).2 ?_
  refine (check_single_of_statement selectNext _ (by rw [selectNext_script]) _ _).2 ?_
  have modeled : (runScriptStep runContext (ExecutionContext.initial db env).clock (ExecutionContext.initial db env).index
      (ExecutionContext.initial db env).connection selectStatement []).continues = true := site.selectModeled env
  cases step : runScriptStep runContext (ExecutionContext.initial db env).clock (ExecutionContext.initial db env).index
      (ExecutionContext.initial db env).connection selectStatement [] with
  | ended reason => rw [step] at modeled; cases modeled
  | continued output connection others =>
    obtain ⟨columns, source, joins, filter, groupBy, orderBy, limit, offset, subqueries, having, distinct, compound, isSelect⟩ :=
      selectStatement_is_select
    obtain rfl := runScriptStep_select_others isSelect step
    intro found member selected choice
    obtain rfl := Sql.Branch.found_eq step member
    cases found : singleValue (queryResult selected) with
    | none =>
      refine (Sql.check_pure _ _ _).2 ?_
      intro impossible
      cases impossible
    | some next =>
      simp only []
      have noError := not_error_of_single choice found
      have kept : connection = db.raw.connection env.counters := by
        rw [isSelect] at step
        exact runScriptStep_select_connection step noError
      subst kept
      have stepEq : runScriptStep runContext env.clock 0 (db.raw.connection env.counters) selectStatement [] =
          .continued output (db.raw.connection env.counters) [] := step
      have mem : next ∈ selectedValues (runScriptStep runContext env.clock 0 (db.raw.connection env.counters)
          selectStatement []).output := by
        rw [stepEq]
        exact mem_selectedValues choice found
      have continues := List.all_eq_true.1 (site.insertModeled env) next mem
      have resolves : resolveStatement runContext (db.raw.connection env.counters).resolveState insertStatement =
          .ok (.insert site.position [[.expression (.parameter 1), .expression (.parameter 2),
            .expression (.parameter 3)]] [] [] none, site.after) := by
        rw [connection_resolveState db.raw env.counters {}]
        exact site.insertResolves
      refine (Sql.check_bind _ _ _ _).2 ?_
      rw [insertCustomerAt_script]
      have present : (db.raw.connection env.counters).state.database.table site.position =
          some ⟨site.table, db.raw.rows.getD site.position []⟩ :=
        Database.table_of_findTable db.raw _ site.position site.table site.found
      have start : (db.raw.connection env.counters).state.Holds (Database.Valid Profile.pinned) :=
        ⟨db.valid, fun _ same => by simp [Database.Raw.connection] at same⟩
      refine Sql.check_send_of_rule (runScriptStep_plainInsert_eq resolves) start
        (RunStep.continues_of_rule (runScriptStep_plainInsert_eq resolves) continues) ?_
      dsimp only
      erw [present]
      dsimp only
      repeat' split
      all_goals first
        | exact trivial
        | refine Sql.sendReached_single (fun _ same => by cases same) fun valid => (Sql.check_pure _ _ _).2 ?_
      · exact fun _ => customer_named_after_insert site next _ valid rfl
      · intro allOk
        simp [List.allOk, Output.isError] at allOk

#print axioms addCustomer_adds

end AssertionExamples
