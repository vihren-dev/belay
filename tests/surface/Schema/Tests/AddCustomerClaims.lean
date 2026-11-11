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
query, the modeled insert stores the one row ({name}`Belay.Sqlite.Model.plainInsert_database`), whose name cell
is the text, so the lookup finds it. -/
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
      obtain ⟨output2, connection2, others2, step2⟩ := RunStep.continues_iff.1 continues
      have resolves : resolveStatement runContext (db.raw.connection env.counters).resolveState insertStatement =
          .ok (.insert site.position [[.expression (.parameter 1), .expression (.parameter 2),
            .expression (.parameter 3)]] [] [] none, site.after) := by
        rw [connection_resolveState db.raw env.counters {}]
        exact site.insertResolves
      refine (Sql.check_bind _ _ _ _).2 ?_
      rw [insertCustomerAt_script]
      refine (check_send_single_of_step (state := (ExecutionContext.initial db env).next selected
        (db.raw.connection env.counters)) step2
        (fun _ _ resolved => by
          obtain rfl := (Prod.mk.inj (Except.ok.inj (resolved.symm.trans resolves))).1
          rfl)
        (runScriptStep_insert_ne_oneOf resolves step2)).2 ?_
      refine (Sql.check_pure _ _ _).2 ?_
      intro allOk
      have noError2 : output2.isError = false := by
        simp [List.allOk] at allOk
        exact allOk.1
      have present : (db.raw.connection env.counters).state.database.table site.position =
          some ⟨site.table, db.raw.rows.getD site.position []⟩ :=
        Database.table_of_findTable db.raw _ site.position site.table site.found
      obtain ⟨value, -, effect⟩ := plainInsert_database resolves present step2 noError2
      rw [show (db.raw.connection env.counters).state.database = db.raw from rfl] at effect
      have start : (db.raw.connection env.counters).state.Holds (Database.Valid Profile.pinned) :=
        ⟨db.valid, fun _ same => by simp [Database.Raw.connection] at same⟩
      have valid : connection2.state.Holds (Database.Valid Profile.pinned) :=
        runScriptStep_valid (profile := Profile.pinned) runContext env.clock 1 insertStatement
        [next, .text name.toUTF8.toList, .text email.toUTF8.toList] rfl rfl start
        { output := output2, next := connection2 } (by rw [step2]; simp [RunStep.executions])
      refine (Holds.reached_iff_holds_of_valid _ _ _ valid.1).2 ?_
      refine (a_customer_named_iff ⟨connection2.state.database, valid.1⟩ name site.position site.table site.nameCell
        (by show (connection2.state.database).catalog.findTable _ = _; rw [effect]; exact site.found)
        site.nameAt (by simp [site.columns])).2 ?_
      show ∃ row ∈ Resolved.sourceRows { shape := site.table, rows := connection2.state.database.rows.getD site.position [] }, _
      rw [effect, Model.Database.rows_getD_setRows _
        (Model.Database.position_lt_rows db.valid.admitted.rowsShaped site.found)]
      rw [site.columns, rowsAt_three_parameters, LiteralData.inserted_single_rows]
      refine ⟨_, (mem_sourceRows_iff _ _).2 ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩, ?_⟩
      refine equalsParameter_true site.nameCell 1 1 [.text name.toUTF8.toList] _ (.text name.toUTF8.toList) ?_ rfl rfl
        (comparisonOperands_text _ _ site.nameText)
      have different : 1 ≠ 0 := by decide
      have alias : (⟨site.table, db.raw.rows.getD site.position []⟩ : Table).shape.rowidAlias = none ∨
          (⟨site.table, db.raw.rows.getD site.position []⟩ : Table).shape.rowidAlias = some 0 := site.alias
      rw [LiteralData.newCells_getElem?_of_plain _ _ _ site.plainColumns alias different]
      simp [Value.store, boundValue, site.nameText]


#print axioms addCustomer_adds

end AssertionExamples
