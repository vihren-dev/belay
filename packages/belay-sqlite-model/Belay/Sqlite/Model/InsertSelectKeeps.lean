import Belay.Sqlite.Model.InsertSelectLaws
import Belay.Sqlite.Model.StatementSingleton
import Belay.Sqlite.Model.RunHoldsReady

set_option doc.verso true

/-! The statement theorem for every admitted execution of a statement (ADR 0019, D4, amended
2026-10-25; ADR 0022, D3). The proof of an atom reads the model's own run of each statement. Every
statement except INSERT from a query without rules has no other execution
({lit}`runStatement_alternatives`), and each execution of INSERT from a query without rules is an
error that keeps the database, or the effect of an upsert of known rows
({lit}`runStatement_insertSelect_none_effects`). So the own-run theorem of an atom gives the theorem
for every execution, when the condition of the INSERT gives the condition of that upsert. -/

namespace Belay.Sqlite.Model

/-- For every statement that is an INSERT from a query without rules
({name}`Resolved.Statement.fromQuery`), the statement has the form of INSERT from a query with no rules.
Proof sketch: a case split on the statement; only that form is true. -/
theorem Resolved.Statement.fromQuery_form {statement : Resolved.Statement} (query : statement.fromQuery = true) :
    ∃ (target : Nat) (cells : List Resolved.SourceCell) (source : Resolved.Query) (clauses : List Resolved.ConflictClause)
      (returning : List (Resolved.Expr × String)) (algorithm : Option ConflictAlgorithm)
      (subqueries : List Resolved.Query),
      statement = .insertSelect target cells source clauses returning algorithm subqueries none := by
  cases statement with
  | insertSelect target cells source clauses returning algorithm subqueries rules =>
    cases rules with
    | none => exact ⟨target, cells, source, clauses, returning, algorithm, subqueries, rfl⟩
    | some _ => simp [Resolved.Statement.fromQuery] at query
  | _ => simp [Resolved.Statement.fromQuery] at query

variable {property : Database → Prop} {condition : Resolved.Statement → Database → Prop}

/-- For every property and condition of statements: if the own run of every statement satisfies the
property, and the condition of an INSERT from a query without rules gives the condition of each upsert
of known rows with the same target, clauses, algorithm and subqueries, the statement theorem holds for
every admitted execution ({name}`StatementKeeps`). Proof sketch: a statement with one execution is its
own run ({lit}`runStatement_alternatives`). Otherwise each execution is an error that keeps the
database, which satisfies the property because the database has it, or the effect of such an upsert
({lit}`runStatement_insertSelect_none_effects`), which the own-run theorem covers. -/
theorem StatementKeeps.ofOwnRun
    (own : ∀ (clock : Int) (counters : Counters) (parameters : List Value) (statement : Resolved.Statement)
      (database : Database), property database → condition statement database →
        (runStatement clock counters parameters statement database).effect.Satisfies property)
    (compatible : ∀ (target : Nat) (cells : List Resolved.SourceCell) (source : Resolved.Query)
      (clauses : List Resolved.ConflictClause) (returning : List (Resolved.Expr × String))
      (algorithm : Option ConflictAlgorithm) (subqueries : List Resolved.Query)
      (literals : List (List Resolved.Cell)) (database : Database),
      condition (.insertSelect target cells source clauses returning algorithm subqueries none) database →
        condition (.upsert target literals clauses returning algorithm subqueries none) database) :
    StatementKeeps property condition := by
  intro clock counters parameters statement database holds met effect member
  by_cases single : statement.fromQuery = false
  · simp only [StatementRun.effects, runStatement_alternatives clock counters parameters statement database none single,
      List.map_nil, List.mem_singleton] at member
    exact member ▸ own clock counters parameters statement database holds met
  · obtain ⟨target, cells, source, clauses, returning, algorithm, subqueries, rfl⟩ :=
      Resolved.Statement.fromQuery_form (by simpa using single)
    rcases runStatement_insertSelect_none_effects clock counters parameters target cells source clauses returning algorithm
      subqueries database effect member with ⟨_, rfl⟩ | ⟨literals, rfl, _⟩
    · exact Effect.satisfies_of_database holds rfl
    · exact own clock counters parameters _ database holds (compatible target cells source clauses returning algorithm
        subqueries literals database met)

/-- The same as {name}`StatementKeeps.ofOwnRun` for the statement theorem with the support check
({name}`StatementKeepsReady`): the own-run theorem may use the support check, and the support check of
the INSERT gives that of the upsert of known rows. -/
theorem StatementKeepsReady.ofOwnRun
    (own : ∀ (clock : Int) (counters : Counters) (parameters : List Value) (statement : Resolved.Statement)
      (database : Database), property database → condition statement database →
        (runStatement clock counters parameters statement database).ready = true →
        (runStatement clock counters parameters statement database).effect.Satisfies property)
    (compatible : ∀ (target : Nat) (cells : List Resolved.SourceCell) (source : Resolved.Query)
      (clauses : List Resolved.ConflictClause) (returning : List (Resolved.Expr × String))
      (algorithm : Option ConflictAlgorithm) (subqueries : List Resolved.Query)
      (literals : List (List Resolved.Cell)) (database : Database),
      condition (.insertSelect target cells source clauses returning algorithm subqueries none) database →
        condition (.upsert target literals clauses returning algorithm subqueries none) database) :
    StatementKeepsReady property condition := by
  intro clock counters parameters statement database holds met ready effect member
  by_cases single : statement.fromQuery = false
  · simp only [StatementRun.effects, runStatement_alternatives clock counters parameters statement database none single,
      List.map_nil, List.mem_singleton] at member
    exact member ▸ own clock counters parameters statement database holds met ready
  · obtain ⟨target, cells, source, clauses, returning, algorithm, subqueries, rfl⟩ :=
      Resolved.Statement.fromQuery_form (by simpa using single)
    rcases runStatement_insertSelect_none_effects clock counters parameters target cells source clauses returning algorithm
      subqueries database effect member with ⟨_, rfl⟩ | ⟨literals, rfl, readyUpsert⟩
    · exact Effect.satisfies_of_database holds rfl
    · exact own clock counters parameters _ database holds (compatible target cells source clauses returning algorithm
        subqueries literals database met) (readyUpsert ready)

end Belay.Sqlite.Model
