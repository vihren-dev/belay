import Belay.Sqlite.Model.Programs.Claims.QueryOutputOn
import Belay.Sqlite.Model.Programs.Scripts.PrepareErrorOutput
import Belay.Sqlite.Model.Schema.Ddl.CreateIndexSuccessLaws

set_option doc.verso true

namespace Belay.Sqlite.Model

/-- For every connection whose row lists align with its catalog, and every index whose table
exists, creating the index at the end of the catalog gives error 19 exactly when a unique
key has conflicting rows; otherwise it gives done with zero changes. The clock, statement
index, bound values, transaction snapshot and connection counters do not change this output.
Proof sketch: CREATE INDEX is ready and reads no clock or counter; its execution checks
exactly the key condition, and the output follows the resulting transition. -/
theorem resolvedStepOutput_createIndex (clock : Option Clock) (index : Nat) (connection : Connection)
    (parameters : List Value) (name : Identifier) (key : CatalogIndex) (table : Table)
    (aligned : connection.state.database.rows.length = connection.state.database.catalog.length)
    (found : connection.state.database.table key.table = some table) :
    resolvedStepOutput clock index connection parameters
      (.createIndex connection.state.database.catalog.length name key) =
      if key.unique && !LiteralData.uniqueRows key.uniqueKey table.rows then .error 19 else .done 0 := by
  have known : connection.state.counters.firstUnknown
      (Resolved.Statement.createIndex connection.state.database.catalog.length name key).counterReads = none := by
    simp [Resolved.Statement.counterReads, Resolved.Statement.clockExpressions]
  simp only [resolvedStepOutput, statementClock, Resolved.Statement.readsClock,
    Resolved.Statement.clockExpressions, List.any_nil, Bool.false_eq_true, ite_false, known]
  simp only [SqlState.statementRun, runStatement, known, Option.isNone_none, Bool.and_self,
    Bool.not_true, Bool.false_eq_true, ite_false]
  simp only [step, beq_self_eq_true, aligned, Bool.and_self, ite_true, found]
  split
  · simp [Output.ofStep, advanceRun, advanceWith, SqlState.publish, SqlTransition.counted,
      haltError_failed, ExecutionError.primaryCode]
  · simp [Output.ofStep, advanceRun, advanceWith, SqlState.publish, SqlTransition.counted,
      haltError, statementOutput, Resolved.Statement.returnsRows]

/-- A prepare error gives the same error output with any optional clock. -/
private theorem prepareOutput_clock (clock : Option Clock) (index : Nat) (connection : Connection)
    (parameters : List Value) (error : PrepareError) :
    resolvedStepOutput clock index connection parameters (.prepareError error) =
      .error (ExecutionError.prepare error).primaryCode := by
  have clockFree : resolvedStepOutput clock index connection parameters (.prepareError error) =
      resolvedStepOutput none index connection parameters (.prepareError error) := by
    simp [resolvedStepOutput, statementClock, Resolved.Statement.readsClock, Resolved.Statement.clockExpressions]
  rw [clockFree, resolvedStepOutput_prepareError]

/-- For every clock, statement index, connection and bound values, the statement that does
nothing ({lit}`.drop []`, the no-op of a CREATE statement with {lit}`IF NOT EXISTS`) outputs
done with zero changes. Proof sketch: it reads no clock or counter, and its execution
drops no object. -/
theorem resolvedStepOutput_drop_nil (clock : Option Clock) (index : Nat) (connection : Connection)
    (parameters : List Value) :
    resolvedStepOutput clock index connection parameters (.drop []) = .done 0 := by
  simp [resolvedStepOutput, statementClock, Resolved.Statement.readsClock,
    Resolved.Statement.clockExpressions, Resolved.Statement.counterReads, SqlState.statementRun, runStatement, step,
    Output.ofStep, advanceRun, advanceWith, SqlState.publish, SqlTransition.counted, statementOutput,
    Resolved.Statement.returnsRows, Resolved.WriteRules.expressions, StatementRun.withKeys,
    Counters.firstUnknown, haltError]

/-- For every connection whose row lists align with its catalog, clock, statement index and
bound values, CREATE INDEX without {lit}`IF NOT EXISTS` gives neither an error nor an ending
output exactly when {name}`CreateIndexConditions` holds. Proof sketch: split the table and
name lookups and the two expression resolvers; only their successful branch creates an
index, whose output is given by {name}`resolvedStepOutput_createIndex`. -/
private theorem runScriptStep_createIndex_plain_ok_iff (context : ResolveContext) (clock : Option Clock)
    (index : Nat) (connection : Connection) (parameters : List Value) (name tableName : Identifier)
    (unique : Bool) (terms : List Syntax.OrderTerm) (filter : Option Syntax.Expr)
    (aligned : connection.state.database.rows.length = connection.state.database.catalog.length) :
    let output := (runScriptStep context clock index connection (.createIndex name unique tableName terms filter) parameters).output
    output.isError = false ∧ output.endsRun = false ↔
      CreateIndexConditions context connection.state.database name unique tableName terms filter := by
  dsimp only
  rw [runScriptStep_output]
  unfold CreateIndexConditions
  cases found : connection.state.database.catalog.findTable tableName with
  | none =>
    cases view : (connection.state.database.catalog.findView tableName).isSome <;>
      simp [statement_arms, resolveCreateIndex, Connection.resolveState, found, view,
        prepareError, ResolveState.withCatalog, Except.map, prepareOutput_clock, Output.isError, Output.endsRun]
  | some pair =>
    rcases pair with ⟨position, table⟩
    simp only [Option.some.injEq, Prod.mk.injEq, and_assoc, exists_and_left]
    by_cases tableReserved : reservedName tableName = true
    · simp [statement_arms, resolveCreateIndex, Connection.resolveState, found, tableReserved,
        prepareError, ResolveState.withCatalog, Except.map, prepareOutput_clock, Output.isError]
    have tableFree : reservedName tableName = false := Bool.eq_false_iff.mpr tableReserved
    by_cases nameReserved : reservedName name = true
    · simp [statement_arms, resolveCreateIndex, Connection.resolveState, found, tableFree, nameReserved,
        prepareError, ResolveState.withCatalog, Except.map, prepareOutput_clock, Output.isError]
    have nameFree : reservedName name = false := Bool.eq_false_iff.mpr nameReserved
    cases named : connection.state.database.catalog.find name with
    | some pair =>
      rcases pair with ⟨target, objectName, objectEntry⟩
      cases objectEntry with
      | trigger trigger =>
        have := Catalog.find_not_trigger _ _ _ _ named
        simp [CatalogObject.isTrigger, CatalogEntry.isTrigger] at this
      | table shape | view view | index key =>
        simp [statement_arms, resolveCreateIndex, Connection.resolveState, found, tableFree, nameFree,
          named, prepareError, ResolveState.withCatalog, Except.map, prepareOutput_clock, Output.isError]
    | none =>
      simp only [tableFree, nameFree, true_and]
      cases keys : indexKeys context.profile.dqsDdl (Scope.single tableName table.columns !table.withoutRowid)
          table.columns terms with
      | error issue =>
        cases issue <;> simp [statement_arms, resolveCreateIndex, Connection.resolveState, found,
          tableFree, nameFree, named, keys, issueResolution, prepareError, restrict,
          ResolveState.withCatalog, Except.map, prepareOutput_clock, Output.isError, Output.endsRun]
      | ok keyTerms =>
        cases filters : indexFilter context.profile.dqsDdl (Scope.single tableName table.columns !table.withoutRowid) filter with
        | error issue =>
          cases issue <;> simp [statement_arms, resolveCreateIndex, Connection.resolveState, found,
            tableFree, nameFree, named, keys, filters, issueResolution, prepareError, restrict,
            ResolveState.withCatalog, Except.map, prepareOutput_clock, Output.isError, Output.endsRun]
        | ok resolvedFilter =>
          simp [statement_arms, resolveCreateIndex, Connection.resolveState, found, tableFree, nameFree,
            named, keys, filters, ResolveState.withCatalog, Except.map, resolvedStepOutput_createIndex clock index connection parameters name
              { table := position, keys := keyTerms, unique, filter := resolvedFilter,
                exactNames := indexSpelledAsDeclared table.columns terms filter }
              { shape := table, rows := connection.state.database.rows.getD position [] } aligned
              (connection.state.database.table_of_findTable tableName position table found),
            Output.isError, Output.endsRun]
          cases unique <;>
            cases checked : LiteralData.uniqueRows
              ({ table := position, keys := keyTerms, unique := false, filter := resolvedFilter } : CatalogIndex).uniqueKey
              (connection.state.database.rows.getD position []) <;>
            simp_all [CatalogIndex.uniqueKey]

/-- For every connection whose row lists align with its catalog, clock, statement index, bound
values and flag {lit}`ifNotExists`, CREATE INDEX gives neither an error nor an ending output
exactly when one of these holds:

* the flag is true and the statement is a no-op ({name}`createIndexKept`: the table exists,
  no name is reserved, and an index has the name);
* {name}`CreateIndexConditions` holds.

Both prepare errors and model restrictions fail this success test. Without the clause
({lean}`false`) only the second item can hold. Proof sketch: the no-op resolves to
{lit}`.drop []`, whose output {name}`resolvedStepOutput_drop_nil` gives; otherwise the
statement resolves as without the clause. -/
theorem runScriptStep_createIndex_ok_iff (context : ResolveContext) (clock : Option Clock) (index : Nat)
    (connection : Connection) (parameters : List Value) (name tableName : Identifier)
    (unique : Bool) (terms : List Syntax.OrderTerm) (filter : Option Syntax.Expr) (ifNotExists : Bool)
    (aligned : connection.state.database.rows.length = connection.state.database.catalog.length) :
    let output := (runScriptStep context clock index connection
      (.createIndex name unique tableName terms filter ifNotExists) parameters).output
    output.isError = false ∧ output.endsRun = false ↔
      (ifNotExists = true ∧ createIndexKept connection.state.database.catalog name tableName = true) ∨
        CreateIndexConditions context connection.state.database name unique tableName terms filter := by
  dsimp only
  by_cases noOp : ifNotExists = true ∧ createIndexKept connection.state.database.catalog name tableName = true
  · obtain ⟨rfl, kept⟩ := noOp
    rw [runScriptStep_output]
    simp [statement_arms, resolveCreateIndexIf, Connection.resolveState, kept, ResolveState.withCatalog,
      Except.map, resolvedStepOutput_drop_nil,
      Output.isError, Output.endsRun]
  · have plain : resolveStatement context connection.resolveState (.createIndex name unique tableName terms filter ifNotExists) =
        resolveStatement context connection.resolveState (.createIndex name unique tableName terms filter) := by
      have off : (ifNotExists && createIndexKept connection.state.database.catalog name tableName) = false := by
        cases ifNotExists <;> simp_all
      simp only [statement_arms, resolveCreateIndexIf, Connection.resolveState] at off ⊢
      simp [off]
    rw [runScriptStep_output, plain, ← runScriptStep_output]
    simpa only [noOp, false_or] using
      runScriptStep_createIndex_plain_ok_iff context clock index connection parameters name tableName unique terms filter aligned
end Belay.Sqlite.Model
