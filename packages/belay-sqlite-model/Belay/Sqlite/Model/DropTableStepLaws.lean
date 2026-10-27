import Belay.Sqlite.Model.DropTableResolution

set_option doc.verso true

/-! The step laws of DROP TABLE (ADR 0017, S6): what one step of a resolved drop does to the connection.
With foreign keys off the drop is plain: it deletes no rows, so it cannot fail and it keeps every table
that it does not drop. With foreign keys on, DROP TABLE runs an implicit DELETE of the table, and a
foreign-key action can then change a table that the statement does not name; the laws for that case
state what stays true without a premise about the actions. -/

namespace Belay.Sqlite.Model

/-- For every connection and statement that resolves to a drop without rules, and every step that
continues: the step has no error output and no further execution, and the next connection is the
connection with the database after {name}`Database.drop` of the positions and nothing else changed. In
plain words, a plain DROP TABLE never fails (the failure law is empty), and the database after is the
database before without the dropped objects and their row lists (the success law). Proof sketch: the
effect of the drop without rules is always a success ({name}`runScriptStep_effect_of_unmodeled`), and
the run counts nothing ({name}`Counters.apply_default`). -/
theorem runScriptStep_drop_plain {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {positions : List Nat}
    (found : resolveStatement context connection.resolveState statement = .ok (.drop positions none, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others) :
    output.isError = false ∧ others = [] ∧
      next = { connection with state := { connection.state with
        database := connection.state.database.drop positions } } := by
  have unmodeled : ∀ value reason reached,
      (connection.state.statementRun value parameters (.drop positions none)).effect = .error (reason, reached) →
        reason = .unmodeled := by
    intro value reason reached effect
    simp [SqlState.statementRun, runStatement, StatementRun.withKeys, Model.step] at effect
  obtain ⟨noError, value, database, -, effect, nextEq⟩ := runScriptStep_effect_of_unmodeled found rfl
    (by intro _ _ same; cases same) step unmodeled
  simp only [SqlState.statementRun, runStatement, StatementRun.withKeys, Model.step, Except.ok.injEq] at effect
  cases effect
  refine ⟨noError, runScriptStep_others step found rfl, ?_⟩
  rw [nextEq]
  simp [SqlState.statementRun, runStatement, StatementRun.withKeys]

/-- For every connection, statement that resolves to a drop without rules, and step that continues, and
every table that a name finds in the database of the connection at a position that the drop keeps: the
name finds the same table, with the same rows, in the database of the next connection, at the
transported position ({name}`keptBelow`). In plain words, a plain drop keeps every table that it does
not drop, found by name. Proof sketch: {name}`runScriptStep_drop_plain` and
{name}`Database.tableNamed_drop_kept`. -/
theorem runScriptStep_drop_frame {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {positions : List Nat}
    (found : resolveStatement context connection.resolveState statement = .ok (.drop positions none, after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    {name : Identifier} {position : Nat} {table : Table}
    (present : connection.state.database.tableNamed name = some (position, table))
    (kept : !positions.contains position) :
    next.state.database.tableNamed name = some (keptBelow positions position, table) := by
  obtain ⟨-, -, nextEq⟩ := runScriptStep_drop_plain found step
  rw [nextEq]
  exact Database.tableNamed_drop_kept present kept

/-- For every connection with foreign keys off, DROP TABLE of a name, and step that continues: the
statement resolves to a drop without rules, so the step has no error output, no further execution, and
the next connection has the database after {name}`Database.drop` of the positions. And a table that
another name finds in the database of the connection is found by that name in the database of the next
connection with the same rows, at the transported position. In plain words, with foreign keys off
DROP TABLE of one table leaves every table of another name as it was, and this is the premise that
excludes a cascade. Proof sketch: {name}`resolveStatement_dropTable_off` gives the drop without rules and
its positions, {name}`Catalog.tableObjects_not_contains` shows that the other table is kept, and
{name}`runScriptStep_drop_frame` reads the next database. -/
theorem runScriptStep_dropTable_frame {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {positions : List Nat} {rules : Option Resolved.WriteRules}
    {dropped : Identifier} {ifExists : Bool}
    (off : connection.foreignKeys = false)
    (found : resolveStatement context connection.resolveState (.dropTable dropped ifExists) =
      .ok (.drop positions rules, after))
    (step : runScriptStep context clock index connection (.dropTable dropped ifExists) parameters =
      .continued output next others)
    {other : Identifier} {position : Nat} {table : Table}
    (differs : other.folded ≠ dropped.folded)
    (present : connection.state.database.tableNamed other = some (position, table)) :
    next.state.database.tableNamed other = some (keptBelow positions position, table) := by
  obtain ⟨rfl, positionsEq⟩ := resolveStatement_dropTable_off context connection.resolveState after dropped ifExists off found
  refine runScriptStep_drop_frame found step present ?_
  rcases positionsEq with rfl | ⟨droppedAt, droppedTable, droppedFound, rfl⟩
  · rfl
  · obtain ⟨otherFound, -⟩ := Database.tableNamed_some present
    simpa using Catalog.tableObjects_not_contains droppedFound otherFound differs

/-- For every connection and statement that resolves to a drop with rules (foreign keys on, or trigger
programs), and every step that continues without an error output: the database of the next connection is
the success of the key run ({name}`dropKeys`) at some clock value, and it has the catalog without the
dropped objects. In plain words, the catalog after DROP TABLE with foreign keys on is the same as with
them off; the rows depend on the actions of the keys, so the law names them only through the key run, and
nothing else of the connection changes except the counters. Proof sketch: {name}`runScriptStep_effect`
gives the successful effect, which is the effect of {name}`dropKeys`, and {name}`dropKeys_ok_catalog` reads
its catalog. -/
theorem runScriptStep_drop_keys {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {positions : List Nat} {rules : Resolved.WriteRules}
    (found : resolveStatement context connection.resolveState statement = .ok (.drop positions (some rules), after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (noError : output.isError = false) :
    ∃ value counters, (dropKeys rules value positions connection.state.database).effect = .ok next.state.database ∧
      next.state.database.catalog = connection.state.database.catalog.drop positions ∧
      next = { connection with state := { connection.state with database := next.state.database, counters } } := by
  obtain ⟨value, database, -, effect, nextEq⟩ := runScriptStep_effect found rfl step noError
  simp only [SqlState.statementRun, runStatement, StatementRun.withKeys] at effect
  refine ⟨value, connection.state.counters.apply
    (connection.state.statementRun value parameters (.drop positions (some rules))).counts, ?_, ?_, ?_⟩
  · rw [nextEq]
    simpa using effect
  · rw [nextEq]
    exact dropKeys_ok_catalog (by simpa using effect)
  · rw [nextEq]

/-- For every connection and statement that resolves to a drop with rules, and every step that continues
with an error output: if no error of the key run ({name}`dropKeys`) is a stop of the FAIL or ROLLBACK
algorithm, the next connection is the connection with the counters of the run and nothing else changed.
In plain words, a failed DROP TABLE with foreign keys on keeps the database; the premise excludes the
stop of a row by RAISE(FAIL) or RAISE(ROLLBACK) of a trigger, the only way that the key run keeps part
of its work or rolls back. The law does not say that the premise holds: it holds for a drop without
rules, where no step fails ({name}`runScriptStep_drop_plain`). Proof sketch:
{name}`runScriptStep_failed_frame` with the premise as its error frame. -/
theorem runScriptStep_drop_failed {context : ResolveContext}
    {clock : Option Clock} {index : Nat} {connection next : Connection}
    {statement : Syntax.Statement} {parameters : List Value} {output : Output} {others : List StatementExecution}
    {after : ResolveState} {positions : List Nat} {rules : Resolved.WriteRules}
    (found : resolveStatement context connection.resolveState statement = .ok (.drop positions (some rules), after))
    (step : runScriptStep context clock index connection statement parameters = .continued output next others)
    (failed : output.isError = true)
    (noStop : ∀ value reason reached, (dropKeys rules value positions connection.state.database).effect =
      .error (reason, reached) → reason ≠ .constraintFail ∧ reason ≠ .constraintRollback) :
    ∃ value, next = { connection with state := { connection.state with
        counters := connection.state.counters.apply
          (connection.state.statementRun value parameters (.drop positions (some rules))).counts } } := by
  refine runScriptStep_failed_frame found rfl (by intro _ _ same; cases same) step failed fun value reason reached effect => ?_
  simp only [SqlState.statementRun, runStatement, StatementRun.withKeys] at effect
  exact noStop value reason reached (by simpa using effect)

end Belay.Sqlite.Model
