import Belay.Sqlite.Model.InsertSelectOutcomeLaws

set_option doc.verso true

/-! The run of INSERT from a query, reduced to runs that the laws already know (ADR 0019, D4; ADR 0022).
Without rules, the effect of the run is that of an upsert of the rows of the query written as known values
({lit}`runStatement_insertSelect_none`), or an error that keeps the database. With rules, it is that of a write
of the row engine, or an error that keeps the database ({lit}`runStatement_insertSelect_some`). So each law that
holds for the effect of an upsert, and for an error that keeps the database, holds for INSERT from a query. -/

namespace Belay.Sqlite.Model

/-- For every clock value, counters, parameters, target, cells, query, clauses, {lit}`RETURNING`
list, algorithm, subqueries and database, each admitted execution of INSERT from a query without
rules ({name}`StatementRun.effects`) has an effect that is an error that keeps the database, or the
effect of an upsert of known rows ({name}`Resolved.Cell.value`) into the same target with the same
clauses, algorithm and subqueries, and then the upsert is ready when the INSERT is. The rows are
the rows of one production of the query, stored for the columns. Proof sketch: unfold the run; a
missing table or production is an error that keeps the database; otherwise each execution is the
outcome of one production, and {name}`insertSelectOutcome_cases` gives its effect, with the readiness
of the outcome taken from the readiness of the INSERT. -/
theorem runStatement_insertSelect_none_effects (clock : Int) (counters : Counters) (parameters : List Value)
    (target : Nat) (cells : List Resolved.SourceCell) (query : Resolved.Query) (clauses : List Resolved.ConflictClause)
    (returning : List (Resolved.Expr × String)) (algorithm : Option ConflictAlgorithm)
    (subqueries : List Resolved.Query) (database : Database) :
    ∀ effect ∈ (runStatement clock counters parameters
        (.insertSelect target cells query clauses returning algorithm subqueries none) database).effects,
      (∃ reason, effect = .error (reason, database)) ∨
      ∃ literals : List (List Resolved.Cell),
        effect = (runStatement clock counters parameters (.upsert target literals clauses returning algorithm subqueries none)
          database).effect ∧
        ((runStatement clock counters parameters (.insertSelect target cells query clauses returning algorithm subqueries none)
          database).ready = true →
        (runStatement clock counters parameters (.upsert target literals clauses returning algorithm subqueries none)
          database).ready = true) := by
  rw [show runStatement clock counters parameters (.insertSelect target cells query clauses returning algorithm subqueries none)
    database = insertSelectRun clock counters parameters target cells query clauses returning algorithm subqueries none database
    from rfl]
  unfold insertSelectRun
  cases found : database.table target with
  | none =>
    intro effect member
    simp only [StatementRun.effects, List.map_nil, List.mem_singleton] at member
    exact .inl ⟨.unmodeled, member⟩
  | some table =>
    dsimp only
    cases productions : query.productions (Resolved.statementContext clock counters parameters database subqueries) database
        (!Resolved.Statement.collectsSource target query subqueries returning none) with
    | none =>
      intro effect member
      simp only [StatementRun.effects, List.map_nil, List.mem_singleton] at member
      exact .inl ⟨.unmodeled, member⟩
    | some list =>
      cases list with
      | nil =>
        intro effect member
        simp only [StatementRun.effects, List.map_nil, List.mem_singleton] at member
        exact .inl ⟨.unmodeled, member⟩
      | cons first others =>
        dsimp only
        intro effect member
        simp only [StatementRun.effects, Option.isNone_none, ite_true, List.map_map, List.mem_cons, List.mem_map,
          Function.comp] at member
        rcases member with rfl | ⟨p, mem, rfl⟩
        · rcases insertSelectOutcome_cases clock counters parameters target cells clauses returning algorithm subqueries
            database table found subqueries.isEmpty first with kept | ⟨literals, same, imp⟩
          · exact .inl kept
          · refine .inr ⟨literals, same, fun ready => ?_⟩
            simp only [Bool.and_eq_true] at ready
            obtain ⟨⟨⟨⟨⟨⟨mainReady, _⟩, _⟩, _⟩, plainSub⟩, _⟩, json⟩ := ready
            exact imp mainReady plainSub json
        · rcases insertSelectOutcome_cases clock counters parameters target cells clauses returning algorithm subqueries
            database table found subqueries.isEmpty p with kept | ⟨literals, same, imp⟩
          · exact .inl kept
          · refine .inr ⟨literals, same, fun ready => ?_⟩
            simp only [Bool.and_eq_true] at ready
            obtain ⟨⟨⟨⟨⟨⟨_, restReady⟩, _⟩, _⟩, plainSub⟩, _⟩, json⟩ := ready
            exact imp (Bool.and_eq_true_iff.1 (List.all_eq_true.1 restReady _ (List.mem_map_of_mem mem))).1 plainSub json

/-- For every clock value, counters, parameters, target, cells, query, clauses, {lit}`RETURNING`
list, algorithm, subqueries and database, the effect of INSERT from a query without rules is an error
that keeps the database, or the effect of an upsert of known rows ({name}`Resolved.Cell.value`) into
the same target with the same clauses, algorithm and subqueries, and then the upsert is ready when
the INSERT is. It is {name}`runStatement_insertSelect_none_effects` for the model's own execution. -/
theorem runStatement_insertSelect_none (clock : Int) (counters : Counters) (parameters : List Value) (target : Nat)
    (cells : List Resolved.SourceCell) (query : Resolved.Query) (clauses : List Resolved.ConflictClause)
    (returning : List (Resolved.Expr × String)) (algorithm : Option ConflictAlgorithm)
    (subqueries : List Resolved.Query) (database : Database) :
    (∃ reason, (runStatement clock counters parameters
        (.insertSelect target cells query clauses returning algorithm subqueries none) database).effect =
      .error (reason, database)) ∨
    ∃ literals : List (List Resolved.Cell),
      (runStatement clock counters parameters (.insertSelect target cells query clauses returning algorithm subqueries none)
          database).effect =
        (runStatement clock counters parameters (.upsert target literals clauses returning algorithm subqueries none)
          database).effect ∧
      ((runStatement clock counters parameters (.insertSelect target cells query clauses returning algorithm subqueries none)
          database).ready = true →
        (runStatement clock counters parameters (.upsert target literals clauses returning algorithm subqueries none)
          database).ready = true) :=
  runStatement_insertSelect_none_effects clock counters parameters target cells query clauses returning algorithm subqueries
    database _ (StatementRun.effect_mem_effects _)

/-- For every property, parameters of INSERT from a query without rules and database: if the database has the
property, and the effect of an upsert of every list of known rows ({name}`Resolved.Cell.value`) with the same
target, clauses, algorithm and subqueries satisfies it ({name}`Effect.Satisfies`), then the effect of the INSERT
satisfies it. Proof sketch: {name}`runStatement_insertSelect_none`; an error that keeps the database satisfies
the property when the database has it. -/
theorem runStatement_insertSelect_none_satisfies {property : Database → Prop} (clock : Int) (counters : Counters)
    (parameters : List Value) (target : Nat) (cells : List Resolved.SourceCell) (query : Resolved.Query)
    (clauses : List Resolved.ConflictClause) (returning : List (Resolved.Expr × String)) (algorithm : Option ConflictAlgorithm)
    (subqueries : List Resolved.Query) {database : Database} (holds : property database)
    (upserts : ∀ literals : List (List Resolved.Cell), (runStatement clock counters parameters
      (.upsert target literals clauses returning algorithm subqueries none) database).effect.Satisfies property) :
    (runStatement clock counters parameters (.insertSelect target cells query clauses returning algorithm subqueries none)
      database).effect.Satisfies property := by
  rcases runStatement_insertSelect_none clock counters parameters target cells query clauses returning algorithm subqueries
    database with ⟨_, kept⟩ | ⟨literals, same, _⟩
  · rw [kept]; exact Effect.satisfies_of_database holds rfl
  · rw [same]; exact upserts literals

/-- The same as {name}`runStatement_insertSelect_none_satisfies` for a law that needs the run to be
ready: the effect of the upsert is only required to satisfy the property when the upsert is ready, and
the INSERT is ready only when the upsert is. -/
theorem runStatement_insertSelect_none_satisfies_ready {property : Database → Prop} (clock : Int) (counters : Counters)
    (parameters : List Value) (target : Nat) (cells : List Resolved.SourceCell) (query : Resolved.Query)
    (clauses : List Resolved.ConflictClause) (returning : List (Resolved.Expr × String)) (algorithm : Option ConflictAlgorithm)
    (subqueries : List Resolved.Query) {database : Database} (holds : property database)
    (ready : (runStatement clock counters parameters (.insertSelect target cells query clauses returning algorithm subqueries
      none) database).ready = true)
    (upserts : ∀ literals : List (List Resolved.Cell), (runStatement clock counters parameters
      (.upsert target literals clauses returning algorithm subqueries none) database).ready = true →
      (runStatement clock counters parameters
        (.upsert target literals clauses returning algorithm subqueries none) database).effect.Satisfies property) :
    (runStatement clock counters parameters (.insertSelect target cells query clauses returning algorithm subqueries none)
      database).effect.Satisfies property := by
  rcases runStatement_insertSelect_none clock counters parameters target cells query clauses returning algorithm subqueries
    database with ⟨_, kept⟩ | ⟨literals, same, readyUpsert⟩
  · rw [kept]; exact Effect.satisfies_of_database holds rfl
  · rw [same]; exact upserts literals (readyUpsert ready)

end Belay.Sqlite.Model
