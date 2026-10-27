import Belay.Sqlite.Model.StepContinues

set_option doc.verso true

/-! Steps that continue without an error (ADR 0017, S6). The laws of {lit}`StepContinues` say that the step of a
schema or transaction statement continues. A proof that a script succeeds also needs that the output of the
step is no error. This module adds that to each of them, under the condition that makes the effect of the
statement succeed. -/

namespace Belay.Sqlite.Model

/-- For every step that continues, of a statement that resolves to a statement other than a query, if the
transition of the run does not halt for any clock value, the output of the step is no error. Proof sketch: the
output is {name}`Output.ofStep` of the run ({name}`runScriptStep_continued_spec`), and
{name}`Output.ofStep_isError_of_noHalt` reads it. -/
theorem runScriptStep_isError_false {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection next : Connection} {statement : Syntax.Statement} {parameters : List Value} {output : Output}
    {others : List StatementExecution} {resolved : Resolved.Statement} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (resolved, after))
    (notQuery : ∀ query subqueries, resolved ≠ .query query subqueries)
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (quiet : ∀ value, haltError (advanceRun index resolved connection.state
      (connection.state.statementRun value parameters resolved)) = none) :
    output.isError = false := by
  obtain ⟨resolved', after', value, same, -, -, -, ofStep, -⟩ := runScriptStep_continued_spec step
  rw [found] at same
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj same)
  rw [← ofStep]
  exact Output.ofStep_isError_of_noHalt _ _ _ _ _ _ _ notQuery (quiet value)

/-- For every connection, statement and values that resolve to a CREATE TABLE at the end of an aligned catalog:
the step continues without further execution, and its output is no error. In plain words, the creation of a
table at the end of the catalog succeeds. Proof sketch: {name}`runScriptStep_createTable_continues`; the
effect succeeds, so the transition does not halt ({name}`runScriptStep_isError_false`). -/
theorem runScriptStep_createTable_ok {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {target : Nat} {name : Identifier} {table : CatalogTable}
    (found : resolveStatement context connection.resolveState statement = .ok (.createTable target name table, after))
    (atEnd : target = connection.state.database.catalog.length)
    (aligned : connection.state.database.rows.length = connection.state.database.catalog.length) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] ∧
      output.isError = false := by
  obtain ⟨output, next, step⟩ := runScriptStep_createTable_continues (parameters := parameters) (clock := clock)
    (index := index) found atEnd aligned
  refine ⟨output, next, step, runScriptStep_isError_false found (by intro _ _ same; cases same) step fun value => ?_⟩
  simp [advanceRun, advanceWith, SqlTransition.counted, SqlState.publish, haltError, SqlState.statementRun, runStatement,
    Model.step, atEnd, aligned]

/-- For every connection, statement and values that resolve to a DROP TABLE without rules: the step continues
without further execution, and its output is no error. In plain words, a drop that no foreign key can cascade
from succeeds. Proof sketch: as {name}`runScriptStep_createTable_ok`, with {name}`runScriptStep_drop_continues`. -/
theorem runScriptStep_drop_ok {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {positions : List Nat}
    (found : resolveStatement context connection.resolveState statement = .ok (.drop positions none, after)) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] ∧
      output.isError = false := by
  obtain ⟨output, next, step⟩ := runScriptStep_drop_continues (parameters := parameters) (clock := clock)
    (index := index) found
  refine ⟨output, next, step, runScriptStep_isError_false found (by intro _ _ same; cases same) step fun value => ?_⟩
  simp [advanceRun, advanceWith, SqlTransition.counted, SqlState.publish, haltError, SqlState.statementRun, runStatement,
    Model.step, StatementRun.withKeys]

/-- For every connection, statement and values that resolve to a rewrite of the catalog that keeps its outline:
the step continues without further execution, and its output is no error. In plain words, a rename that keeps the
outline of the catalog succeeds. Proof sketch: as {name}`runScriptStep_createTable_ok`, with
{name}`runScriptStep_rewrite_continues`. -/
theorem runScriptStep_rewrite_ok {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {renamed : Catalog}
    (found : resolveStatement context connection.resolveState statement = .ok (.rewrite renamed, after))
    (outline : connection.state.database.catalog.sameOutline renamed = true) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] ∧
      output.isError = false := by
  obtain ⟨output, next, step⟩ := runScriptStep_rewrite_continues (parameters := parameters) (clock := clock)
    (index := index) found outline
  refine ⟨output, next, step, runScriptStep_isError_false found (by intro _ _ same; cases same) step fun value => ?_⟩
  simp [advanceRun, advanceWith, SqlTransition.counted, SqlState.publish, haltError, SqlState.statementRun, runStatement,
    Model.step, outline]

/-- For every connection, statement and values that resolve to a setting: the step continues without further
execution, and its output is no error. Proof sketch: as {name}`runScriptStep_createTable_ok`, with
{name}`runScriptStep_setting_continues`. -/
theorem runScriptStep_setting_ok {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {setting : Syntax.PragmaSetting} {on : Bool}
    (found : resolveStatement context connection.resolveState statement = .ok (.setting setting on, after)) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] ∧
      output.isError = false := by
  obtain ⟨output, next, step⟩ := runScriptStep_setting_continues (parameters := parameters) (clock := clock)
    (index := index) found
  refine ⟨output, next, step, runScriptStep_isError_false found (by intro _ _ same; cases same) step fun value => ?_⟩
  simp [advanceRun, advanceWith, SqlTransition.counted, SqlState.publish, haltError, SqlState.statementRun, runStatement,
    Model.step]

/-- For every connection with no open transaction, statement and values that resolve to BEGIN: the step continues
without further execution, and its output is no error. In plain words, BEGIN outside a transaction succeeds.
Proof sketch: as {name}`runScriptStep_createTable_ok`, with {name}`runScriptStep_begin_continues`; with no open
transaction the transition continues. -/
theorem runScriptStep_begin_ok {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    (found : resolveStatement context connection.resolveState statement = .ok (.begin, after))
    (closed : connection.state.snapshot = none) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] ∧
      output.isError = false := by
  obtain ⟨output, next, step⟩ := runScriptStep_begin_continues (parameters := parameters) (clock := clock)
    (index := index) found
  refine ⟨output, next, step, runScriptStep_isError_false found (by intro _ _ same; cases same) step fun value => ?_⟩
  simp [advanceRun, advanceWith, SqlTransition.counted, SqlState.finish, haltError, SqlState.statementRun, runStatement,
    closed]

/-- For every connection with an open transaction, statement and values that resolve to COMMIT: the step
continues without further execution, and its output is no error. In plain words, COMMIT inside a transaction
succeeds. Proof sketch: as {name}`runScriptStep_begin_ok`. -/
theorem runScriptStep_commit_ok {context : ResolveContext} {clock : Option Clock} {index : Nat}
    {connection : Connection} {statement : Syntax.Statement} {parameters : List Value} {after : ResolveState}
    {original : Database}
    (found : resolveStatement context connection.resolveState statement = .ok (.commit, after))
    (open_ : connection.state.snapshot = some original) :
    ∃ output next, runScriptStep context clock index connection statement parameters = .continued output next [] ∧
      output.isError = false := by
  obtain ⟨output, next, step⟩ := runScriptStep_commit_continues (parameters := parameters) (clock := clock)
    (index := index) found
  refine ⟨output, next, step, runScriptStep_isError_false found (by intro _ _ same; cases same) step fun value => ?_⟩
  simp [advanceRun, advanceWith, SqlTransition.counted, haltError, SqlState.statementRun, runStatement, open_]

end Belay.Sqlite.Model
