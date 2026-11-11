import Belay.Sqlite.Model.Queries.Preparation.StatementSingleton

set_option doc.verso true

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

end Belay.Sqlite.Model
