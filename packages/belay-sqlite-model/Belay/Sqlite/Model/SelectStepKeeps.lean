import Belay.Sqlite.Model.SuccessfulScriptEffects
import Belay.Sqlite.Model.KeysUniqueWrites
import Belay.Sqlite.Model.Counters
import Belay.Sqlite.Model.Resolution.SelectResolution

set_option doc.verso true

/-!
A SELECT step keeps the connection (ADR 0017, S6). A SELECT writes no row and leaves the
counters, so a step of it that continues without an error ends at the connection where it began.
A program that reads with a SELECT and then writes continues from the same connection, which lets a
claim about the write use the facts about the start.
-/

namespace Belay.Sqlite.Model

/-- For every successful resolution of a SELECT: the resolved statement is a query or a prepare
error. Proof sketch: every successful branch of the resolver returns one of the two
({name}`resolveSelect_same` reads the same branches). -/
theorem resolveSelect_shape (context : ResolveContext) (catalog after : Catalog)
    (query : Syntax.Subquery) (subqueries : List Syntax.Subquery) (statement : Resolved.Statement)
    (ok : resolveSelect context catalog query subqueries = .ok (statement, after)) :
    (∃ resolvedQuery resolvedSubqueries, statement = .query resolvedQuery resolvedSubqueries) ∨
      ∃ error, statement = .prepareError error := by
  unfold resolveSelect resolveSelectTraced at ok
  dsimp only [Traced.drop] at ok
  simp only [prepareError, issueResolution] at ok
  repeat' split at ok
  all_goals first
    | (cases ok; exact Or.inl ⟨_, _, rfl⟩)
    | (cases ok; exact Or.inr ⟨_, rfl⟩)
    | (cases ok)

/-- For every resolution of a SELECT statement: the resolved statement is a query or a prepare
error, so it is no INSERT from a query. Proof sketch: the resolution of the statement is that of its
query ({name}`resolveSelect`), whose result has one of the two shapes ({name}`resolveSelect_shape`). -/
theorem resolveStatement_select_shape {context : ResolveContext} {state : ResolveState}
    {columns source joins filter groupBy orderBy limit offset subqueries having distinct compound}
    {resolved : Resolved.Statement} {after : ResolveState}
    (found : resolveStatement context state
      (.select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound) =
      .ok (resolved, after)) :
    ∃ catalog, resolveSelect context state.catalog
      { columns, source, joins, filter, groupBy, orderBy, limit, offset, parent := none, having, distinct,
        compound } subqueries = .ok (resolved, catalog) ∧
      ((∃ query subqueries, resolved = .query query subqueries) ∨ ∃ error, resolved = .prepareError error) := by
  have selected : ∃ catalog, resolveSelect context state.catalog
      { columns, source, joins, filter, groupBy, orderBy, limit, offset, parent := none, having, distinct,
        compound } subqueries = .ok (resolved, catalog) := by
    simp only [statement_arms, ResolveState.withCatalog] at found
    cases resolution : resolveSelect context state.catalog
      { columns, source, joins, filter, groupBy, orderBy, limit, offset, parent := none, having, distinct,
        compound } subqueries with
    | error failure => rw [resolution] at found; simp [Except.map] at found
    | ok result =>
      obtain ⟨statement, catalog⟩ := result
      rw [resolution] at found
      simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at found
      obtain ⟨rfl, -⟩ := found
      exact ⟨catalog, rfl⟩
  obtain ⟨catalog, ok⟩ := selected
  exact ⟨catalog, ok, resolveSelect_shape _ _ _ _ _ _ ok⟩

/-- For every connection and every statement that resolves from a SELECT: if the step of the
statement continues and its output is not an error, the next connection is the connection of the
step. The database, the transaction, the settings and the counters are unchanged. Proof sketch: the
resolved statement is a query or a prepare error ({name}`resolveSelect_shape`); its effect keeps the
database ({name}`runStatement_keeps_database`) and its counts leave the counters
({name}`Counters.apply_default`); {name}`runScriptStep_effect` gives the next connection. -/
theorem runScriptStep_select_connection {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection next : Connection} {columns source joins filter groupBy orderBy limit offset subqueries having
      distinct compound parameters output} {others : List StatementExecution}
    (step : runScriptStep context clock index connection
      (.select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound)
      parameters = .continued output next others)
    (noError : output.isError = false) : next = connection := by
  obtain ⟨resolved, after, value, found, -⟩ := runScriptStep_ran step
  obtain ⟨catalog, ok, shape⟩ := resolveStatement_select_shape found
  have ordinary := (resolveSelect_same _ _ _ _ _ _ ok).2.2
  obtain ⟨value, database, -, effect, nextEq⟩ := runScriptStep_effect found ordinary step noError
  have keeps := runStatement_keeps_database value (connection.state.counters.view resolved.counterReads)
    parameters connection.state.database resolved (by
      rcases shape with ⟨query, subqueries, same⟩ | ⟨error, same⟩
      · exact Or.inl ⟨query, subqueries, same⟩
      · exact Or.inr (Or.inr (Or.inl ⟨error, same⟩)))
  have noCounts : (connection.state.statementRun value parameters resolved).counts = {} := by
    rcases shape with ⟨query, subqueries, same⟩ | ⟨error, same⟩ <;> subst same <;>
      simp [SqlState.statementRun, runStatement]
  simp only [SqlState.statementRun] at effect
  rw [effect] at keeps
  have sameDatabase : database = connection.state.database := keeps
  rw [nextEq, noCounts, sameDatabase, Counters.apply_default]

/-- For every SELECT statement and every step of it that gives rows: the step continues with those
rows and keeps the connection. Plain words: a SELECT that gives rows changes nothing. Proof sketch: the
step does not end the run because its output is rows, and a SELECT step that does not give an error
keeps the connection ({name}`runScriptStep_select_connection`). -/
theorem runScriptStep_select_rows {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value}
    {columns source joins filter groupBy orderBy limit offset subqueries having distinct compound}
    (isSelect : statement =
      .select columns source joins filter groupBy orderBy limit offset subqueries having distinct compound)
    {rows : List (List Value)}
    (output : (runScriptStep context clock index connection statement parameters).output = .rows rows) :
    runScriptStep context clock index connection statement parameters = .continued (.rows rows) connection [] := by
  cases step : runScriptStep context clock index connection statement parameters with
  | ended reason => rw [step] at output; simp [RunStep.output] at output
  | continued out next others =>
    subst isSelect
    obtain ⟨resolved, after, -, found, -⟩ := runScriptStep_ran step
    obtain ⟨-, -, shape⟩ := resolveStatement_select_shape found
    obtain rfl := runScriptStep_others step found (by rcases shape with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ <;> rfl)
    rw [step] at output
    simp only [RunStep.output] at output
    subst output
    rw [runScriptStep_select_connection step rfl]

end Belay.Sqlite.Model
