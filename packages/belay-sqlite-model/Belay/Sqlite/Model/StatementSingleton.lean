import Belay.Sqlite.Model.StatementStep

set_option doc.verso true

/-! Every statement that the model describes, except INSERT from a query, has one next state (ADR 0019, D4, amended
2026-10-25): its run lists no further execution ({name}`Belay.Sqlite.Model.StatementRun.alternatives`). A query can
still have several permitted results on that one state ({lit}`Output.oneOf`). A statement whose
result depends on the plan of SQLite gives alternatives in its run, and then this theorem no longer
covers it. -/

namespace Belay.Sqlite.Model

/-- For every run that {name}`StatementRun.withKeys` builds, the run has no alternative. Proof sketch:
the cases of the optional run of the keys build a run with the default alternatives. -/
theorem StatementRun.withKeys_alternatives (effect : Effect) (ready : Bool) (counts : Counts) (keys : Option KeyRun) :
    (StatementRun.withKeys effect ready counts keys).alternatives = [] := by
  cases keys <;> rfl

/-- Whether the statement is an INSERT from a query without rules, the one statement whose run can
have alternative executions ({name}`Resolved.Statement.insertSelect`). With rules (a trigger or an
enforced foreign key) the model describes the statement only for one production of the query. -/
def Resolved.Statement.fromQuery : Resolved.Statement → Bool
  | .insertSelect _ _ _ _ _ _ _ none => true
  | _ => false

/-- For every clock, counters, values, statement that is no INSERT from a query without rules
({name}`Resolved.Statement.fromQuery`), database and initial database, the run of the
statement ({name}`runStatement`) has no alternative execution: such a statement
has one next state, the database, counters and connection of its own run. The
output is the output of that run; a query keeps its permitted results in {lit}`Output.oneOf`. Proof sketch: a
case split on the statement and on the table that it writes; each run is a record with the default
alternatives, or a run built by {name}`StatementRun.withKeys`, and an INSERT from a query with rules
lists none. -/
theorem runStatement_alternatives (clock : Int) (counters : Counters) (parameters : List Value)
    (statement : Resolved.Statement) (database : Database) (initial : Option Database)
    (single : statement.fromQuery = false) :
    (runStatement clock counters parameters statement database initial).alternatives = [] := by
  cases statement with
  | insertSelect target cells query clauses returning algorithm subqueries rules =>
    cases rules with
    | none => simp [Resolved.Statement.fromQuery] at single
    | some rules =>
      simp only [runStatement, insertSelectRun]
      repeat' split
      all_goals first | rfl | (rename_i isNone; simp at isNone) | simp
  | _ =>
    simp only [runStatement]
    repeat' split
    all_goals first | rfl | exact StatementRun.withKeys_alternatives _ _ _ _

/-- For every state, clock, values and statement that is no INSERT from a query without rules, the run of the
statement on a connection state ({name}`SqlState.statementRun`) has no alternative execution. Proof sketch:
{name}`runStatement_alternatives`; the support check changes only {lit}`ready`. -/
theorem SqlState.statementRun_alternatives (state : SqlState) (clock : Int) (parameters : List Value)
    (statement : Resolved.Statement) (initial : Option Database) (single : statement.fromQuery = false) :
    (state.statementRun clock parameters statement initial).alternatives = [] :=
  runStatement_alternatives clock (state.counters.view statement.counterReads) parameters statement state.database initial single

end Belay.Sqlite.Model
