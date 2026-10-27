import Belay.Sqlite.Model.StatementStep
import Belay.Sqlite.Model.RowLocalFrame

set_option doc.verso true

/-! The effect of one production of INSERT from a query (ADR 0019, D4; ADR 0022): the helper laws
that {lit}`InsertSelectLaws` uses to reduce the run of the statement to runs that the laws already
know. A failure of the query ends the statement with an error that keeps the database, and the
other cells are known values, so the outcome of a production is an upsert of known rows or such an
error. The laws of a statement with rules ({lit}`runStatement_insertSelect_some`) are here too: their
outcome is a write of the row engine or such an error. -/

namespace Belay.Sqlite.Model

/-- For every rules, clock value, target, work, database, flag, algorithm and failure, the effect of
{name}`rowsKeys` with a failure is the effect without it, or an error that keeps the database: the
failure of the query ends the statement with the input database after rows that all succeed, and
changes nothing else. Proof sketch: unfold {name}`rowsKeys`; only the case of a failure after a
successful run differs, and {name}`keyRun` of that case has the input database. -/
theorem rowsKeys_effect_failure (rules : Resolved.WriteRules) (clock : Int) (target : Nat) (work : RowWork)
    (database : Database) (plain : Bool) (algorithm : Option ConflictAlgorithm) (failure : Option ExecutionError) :
    (rowsKeys rules clock target work database plain algorithm failure).effect =
        (rowsKeys rules clock target work database plain algorithm).effect ∨
      ∃ reason, (rowsKeys rules clock target work database plain algorithm failure).effect = .error (reason, database) := by
  unfold rowsKeys
  cases failure with
  | none => exact .inl rfl
  | some reason =>
    cases runRows database.catalog (rules.links database.catalog) (rules.depth + 1) (rules.frame clock algorithm) work
        { rows := database.rows } with
    | error _ => exact .inl rfl
    | ok state => exact .inr ⟨reason, rfl⟩


/-- For every context and rows of known values ({name}`Resolved.Cell.value`), the rows are ready
({name}`Resolved.cellsReady`): a known value is no expression that may fail. -/
theorem cellsReady_values (context : Resolved.EvalContext) (rows : List (List Value)) :
    Resolved.cellsReady context (rows.map (·.map Resolved.Cell.value)) = true := by
  have none : (rows.map (·.map Resolved.Cell.value)).flatten.filterMap Resolved.Cell.expression? = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro cell member
    simp only [List.mem_flatten, List.mem_map] at member
    obtain ⟨_, ⟨row, _, rfl⟩, found⟩ := member
    obtain ⟨value, _, rfl⟩ := List.mem_map.1 found
    rfl
  simp [Resolved.cellsReady, none, Resolved.anyMayFail]

/-- For every clock value, counters, parameters, target, clauses, {lit}`RETURNING` list, algorithm,
subqueries, database, table at the target and rows of values, the effect of an upsert of the rows
as known values ({name}`Resolved.Cell.value`) is the effect of the summary of its steps, and the upsert is
ready when the steps are ready, the subqueries are plain and the clauses and the {lit}`RETURNING` list
need no JSON check. Proof sketch: unfold the run; the rows in the context are the values
({name}`Resolved.rowsAt_values`) and known values are ready ({name}`cellsReady_values`). -/
theorem runStatement_upsert_values (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat)
    (clauses : List Resolved.ConflictClause) (returning : List (Resolved.Expr × String))
    (algorithm : Option ConflictAlgorithm) (subqueries : List Resolved.Query) (database : Database) (table : Table)
    (found : database.table target = some table) (values : List (List Value)) :
    let context := Resolved.statementContext clock counters parameters database subqueries
    let steps := LiteralData.upsertSteps context (database.keys target table)
      (database.catalog.writePolicy target table.shape algorithm) clauses table values
    (runStatement clock counters parameters
        (.upsert target (values.map (·.map Resolved.Cell.value)) clauses returning algorithm subqueries none) database).effect =
      (match LiteralData.upsertSummary table steps with
        | .ok (result, _) => .ok (database.setRows target result.rows)
        | .error (reason, reached, _) => .error (reason, database.setRows target reached.rows)) ∧
    (runStatement clock counters parameters
        (.upsert target (values.map (·.map Resolved.Cell.value)) clauses returning algorithm subqueries none) database).ready =
      (LiteralData.upsertReady (database.keys target table) table clauses values steps && Resolved.subqueriesPlain subqueries &&
        upsertJsonReady clauses returning) := by
  refine ⟨?_, ?_⟩ <;> simp only [runStatement, found, Resolved.rowsAt_values, StatementRun.withKeys, Option.map_none,
    cellsReady_values, Bool.and_true] <;> first | done | rfl

/-- For every clock value, counters, parameters, target, cells, clauses, {lit}`RETURNING` list,
algorithm, subqueries, database, table at the target, flag and production, the outcome of one
production ({name}`insertSelectOutcome`) without rules has an effect that is an error that keeps the
database, or the effect of an upsert of known rows ({name}`Resolved.Cell.value`) into the target with
the same clauses, algorithm and subqueries. In the second case, the upsert is ready when the outcome
is, its subqueries are plain and its {lit}`RETURNING` list and clauses need no JSON check. The rows are
the rows of the production, stored for the columns. Proof sketch: the rows give the same steps and
summary as the upsert ({name}`runStatement_upsert_values`), and the effect differs only by the failure of
the production after rows that all succeed, which keeps the database. -/
theorem insertSelectOutcome_cases (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat)
    (cells : List Resolved.SourceCell) (clauses : List Resolved.ConflictClause)
    (returning : List (Resolved.Expr × String)) (algorithm : Option ConflictAlgorithm)
    (subqueries : List Resolved.Query) (database : Database) (table : Table) (found : database.table target = some table)
    (plain : Bool) (production : SourceProduction) :
    (∃ reason, (insertSelectOutcome clock (Resolved.statementContext clock counters parameters database subqueries) database
        target table cells clauses algorithm none plain production).effect = .error (reason, database)) ∨
    ∃ literals : List (List Resolved.Cell),
      (insertSelectOutcome clock (Resolved.statementContext clock counters parameters database subqueries) database target
        table cells clauses algorithm none plain production).effect =
      (runStatement clock counters parameters (.upsert target literals clauses returning algorithm subqueries none)
        database).effect ∧
      ((insertSelectOutcome clock (Resolved.statementContext clock counters parameters database subqueries) database target
          table cells clauses algorithm none plain production).ready = true → Resolved.subqueriesPlain subqueries = true →
        upsertJsonReady clauses returning = true →
        (runStatement clock counters parameters (.upsert target literals clauses returning algorithm subqueries none)
          database).ready = true) := by
  have values := runStatement_upsert_values clock counters parameters target clauses returning algorithm subqueries database
    table found (insertSelectRows (Resolved.statementContext clock counters parameters database subqueries)
      table.shape.columns cells production.rows)
  have ready : (insertSelectOutcome clock (Resolved.statementContext clock counters parameters database subqueries) database
      target table cells clauses algorithm none plain production).ready = true → Resolved.subqueriesPlain subqueries = true →
      upsertJsonReady clauses returning = true →
      (runStatement clock counters parameters (.upsert target ((insertSelectRows
        (Resolved.statementContext clock counters parameters database subqueries) table.shape.columns cells
        production.rows).map (·.map Resolved.Cell.value)) clauses returning algorithm subqueries none) database).ready = true := by
    intro outcome plainSubqueries json
    rw [values.2, plainSubqueries, json, Bool.and_true, Bool.and_true]
    simpa only [insertSelectOutcome, StatementRun.withKeys, Option.map_none] using outcome
  have effect := values.1
  simp only [insertSelectOutcome, StatementRun.withKeys, Option.map_none] at ready ⊢
  cases summary : LiteralData.upsertSummary table (LiteralData.upsertSteps
      (Resolved.statementContext clock counters parameters database subqueries) (database.keys target table)
      (database.catalog.writePolicy target table.shape algorithm) clauses table
      (insertSelectRows (Resolved.statementContext clock counters parameters database subqueries) table.shape.columns cells
        production.rows)) with
  | error pair => simp only [summary] at effect ⊢; exact .inr ⟨_, effect.symm, ready⟩
  | ok pair =>
    simp only [summary] at effect ready ⊢
    cases failure : production.failure with
    | none => simp only [failure, Option.map_none]; exact .inr ⟨_, effect.symm, ready⟩
    | some reason => simp only [failure, Option.map_some]; exact .inl ⟨reason.toError, rfl⟩

/-- For every clock value, counters, parameters, target, cells, query, clauses, {lit}`RETURNING` list,
algorithm, subqueries, rules and database, the effect of INSERT from a query with rules is an error that
keeps the database, or the effect of a write of the row engine ({name}`rowsKeys`) of an INSERT work
({name}`RowWork.insert`) of some rows, policy and flags, with the clauses of the INSERT. It states nothing
about the alternative executions. Proof sketch: unfold the run; a missing table or production is an error
that keeps the database; otherwise the effect is that of {name}`insertKeys` with the failure of the
production, and {name}`rowsKeys_effect_failure` removes the failure. -/
theorem runStatement_insertSelect_some (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat)
    (cells : List Resolved.SourceCell) (query : Resolved.Query) (clauses : List Resolved.ConflictClause)
    (returning : List (Resolved.Expr × String)) (algorithm : Option ConflictAlgorithm)
    (subqueries : List Resolved.Query) (rules : Resolved.WriteRules) (database : Database) :
    (∃ reason, (runStatement clock counters parameters
        (.insertSelect target cells query clauses returning algorithm subqueries (some rules)) database).effect =
      .error (reason, database)) ∨
    ∃ (values : List (List Value)) (policy : Resolved.ConflictPolicy) (multi plain : Bool)
      (conflict : Option ConflictAlgorithm),
      (runStatement clock counters parameters (.insertSelect target cells query clauses returning algorithm subqueries (some rules))
          database).effect =
        (rowsKeys rules clock target (.insert target values policy clauses multi true) database plain conflict).effect := by
  rw [show runStatement clock counters parameters (.insertSelect target cells query clauses returning algorithm subqueries
    (some rules)) database = insertSelectRun clock counters parameters target cells query clauses returning algorithm subqueries
    (some rules) database from rfl]
  unfold insertSelectRun
  cases found : database.table target with
  | none => exact .inl ⟨.unmodeled, rfl⟩
  | some table =>
    dsimp only
    cases productions : query.productions (Resolved.statementContext clock counters parameters database subqueries) database
        (!Resolved.Statement.collectsSource target query subqueries returning (some rules)) with
    | none => exact .inl ⟨.unmodeled, rfl⟩
    | some list =>
      cases list with
      | nil => exact .inl ⟨.unmodeled, rfl⟩
      | cons first others =>
        dsimp only
        simp only [insertSelectOutcome, StatementRun.withKeys, Option.map_some]
        rcases rowsKeys_effect_failure rules clock target _ database subqueries.isEmpty algorithm (first.failure.map SourceFailure.toError) with same | ⟨reason, kept⟩
        · exact .inr ⟨_, _, _, _, _, same⟩
        · exact .inl ⟨reason, kept⟩

/-- For every property and parameters of INSERT from a query with rules and database: if the database has
the property, and every write of the row engine ({name}`rowsKeys`) of the rules for an INSERT work into the target has an
effect that satisfies it ({name}`Effect.Satisfies`), then the effect of the INSERT satisfies it.
Proof sketch: {name}`runStatement_insertSelect_some`. -/
theorem runStatement_insertSelect_some_satisfies {property : Database → Prop} (clock : Int) (counters : Counters)
    (parameters : List Value) (target : Nat) (cells : List Resolved.SourceCell) (query : Resolved.Query)
    (clauses : List Resolved.ConflictClause) (returning : List (Resolved.Expr × String)) (algorithm : Option ConflictAlgorithm)
    (subqueries : List Resolved.Query) (rules : Resolved.WriteRules) {database : Database} (holds : property database)
    (writes : ∀ (values : List (List Value)) (policy : Resolved.ConflictPolicy) (multi plain : Bool)
      (conflict : Option ConflictAlgorithm),
      (rowsKeys rules clock target (.insert target values policy clauses multi true) database plain conflict).effect.Satisfies
        property) :
    (runStatement clock counters parameters (.insertSelect target cells query clauses returning algorithm subqueries (some rules))
      database).effect.Satisfies property := by
  rcases runStatement_insertSelect_some clock counters parameters target cells query clauses returning algorithm subqueries
    rules database with ⟨_, kept⟩ | ⟨values, policy, multi, plain, conflict, same⟩
  · rw [kept]; exact Effect.satisfies_of_database holds rfl
  · rw [same]; exact writes values policy multi plain conflict

end Belay.Sqlite.Model
