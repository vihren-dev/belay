import AddCustomerQueries

/-! A fixture module of `tests/surface_s6_automation_test.py`: the guide's insertion claim about the program that
uses a result, proved with the tactic {lit}`sql_run` and, for the same proposition, with the public step rules
alone (ADR 0017, S6). The program, the site and the claim are those of {lit}`AddCustomerQueries`. The tactic
reduces the program to the premises of the rules; the hints close the premises about the resolution of the
insert and the table, and the premises about the model's coverage and the final property stay as goals. -/

set_option doc.verso true
set_option maxRecDepth 200000
set_option exponentiation.threshold 2000

namespace AssertionExamples
open Belay.Sqlite Std.Do
open Belay.Sqlite.Model hiding Database

/-- For every database with an {name}`AddCustomerSite`, every id the query returned, and every connection
whose database is the database of the start with the one row that the insert stores: a customer with the name
exists in the context that has this connection. Proof sketch: the lookup of the name finds the stored row,
whose name cell is the text because the column has TEXT affinity ({name}`a_customer_named_iff`). -/
theorem customer_named_after_insert {db : Database} {name email : String} (site : AddCustomerSite db name email)
    (next : Value) (value : Int) {view} {final : ExecutionContext}
    (valid : final.connection.state.Holds (Database.Valid Profile.pinned))
    (stored : final.connection.state.database = db.raw.setRows site.position
      (LiteralData.inserted ⟨site.table, db.raw.rows.getD site.position []⟩
        (Resolved.rowsAt (Resolved.statementContext value view
          [next, .text name.toUTF8.toList, .text email.toUTF8.toList] db.raw [])
          site.table.columns [[.expression (.parameter 1), .expression (.parameter 2),
            .expression (.parameter 3)]])).rows) :
    Holds.reached (customerNamed name) final := by
  refine (Holds.reached_iff_holds_of_valid _ _ _ valid.1).2 ?_
  refine (a_customer_named_iff ⟨_, valid.1⟩ name site.position site.table site.nameCell
    (by show (final.connection.state.database).catalog.findTable _ = _; rw [stored]; exact site.found)
    site.nameAt (by simp [site.columns])).2 ?_
  show ∃ row ∈ Resolved.sourceRows { shape := site.table, rows := final.connection.state.database.rows.getD site.position [] }, _
  rw [stored, Model.Database.rows_getD_setRows _ (Model.Database.position_lt_rows db.valid.admitted.rowsShaped site.found)]
  rw [site.columns, rowsAt_three_parameters, LiteralData.inserted_single_rows]
  refine ⟨_, (mem_sourceRows_iff _ _).2 ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩, ?_⟩
  refine equalsParameter_true site.nameCell 1 1 [.text name.toUTF8.toList] _ (.text name.toUTF8.toList) ?_ rfl rfl
    (comparisonOperands_text _ _ site.nameText)
  have different : 1 ≠ 0 := by decide
  have alias : (⟨site.table, db.raw.rows.getD site.position []⟩ : Table).shape.rowidAlias = none ∨
      (⟨site.table, db.raw.rows.getD site.position []⟩ : Table).shape.rowidAlias = some 0 := site.alias
  rw [LiteralData.newCells_getElem?_of_plain _ _ _ site.plainColumns alias different]
  simp [Value.store, boundValue, site.nameText]

/-- The claim of {lit}`addCustomer_adds` in {lit}`AddCustomerClaims`, proved with {lit}`sql_run`: the tactic applies the rules for the
query and the insert and leaves three goals, which the proof closes by name. The goal {lit}`modeled` is that the
model runs the insert for the id that the query returned, which the site gives for every id in the result of
the query. The goal {lit}`success` is the final property in the context after the stored row. The goal
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
    exact RunStep.continues_iff.1 (List.all_eq_true.1 (site.insertModeled env) next mem)
  case success =>
    rename_i next found
    intro allOk
    exact customer_named_after_insert site next value valid rfl
  case h_2 =>
    intro impossible
    cases impossible

/-- The same claim as {name}`addCustomer_adds_by_sql_run`, proved with the public rules and without the
tactic: {name}`Sql.check_single_select` for the query, {name}`Sql.check_send_plainInsert` for the insert. -/
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
    refine Sql.check_send_plainInsert (target := site.position) (after := site.after)
      (table := ⟨site.table, db.raw.rows.getD site.position []⟩)
      (ExecutionContext.initial_holds_valid db env) site.insertResolves
      (Database.table_of_findTable db.raw _ site.position site.table site.found)
      (RunStep.continues_iff.1 (List.all_eq_true.1 (site.insertModeled env) next mem)) ?_ ?_
    · intro output value connection noError ongoing timed same valid
      refine (Sql.check_pure _ _ _).2 ?_
      intro allOk
      subst same
      exact customer_named_after_insert site next value valid rfl
    · intro output value connection failed ongoing same valid
      refine (Sql.check_pure _ _ _).2 ?_
      intro allOk
      simp [List.allOk, failed] at allOk

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
    exact RunStep.continues_iff.1 (List.all_eq_true.1 (site.insertModeled env) next mem)
  case success =>
    rename_i next found
    intro allOk
    exact customer_named_after_insert site next value valid rfl
  case h_2 =>
    intro impossible
    cases impossible

#print axioms addCustomer_adds_triple
#print axioms addCustomer_adds_by_sql_run
#print axioms addCustomer_adds_by_rules

end AssertionExamples
