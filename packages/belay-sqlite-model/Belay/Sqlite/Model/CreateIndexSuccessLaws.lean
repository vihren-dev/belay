import Belay.Sqlite.Model.QueryOutputOn
import Belay.Sqlite.Model.PrepareErrorOutput
import Belay.Sqlite.Model.TableSourceLaws

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


/-- The conditions for CREATE INDEX on this database:

* the catalog finds the named table at some position with some shape;
* neither the table name nor the index name is reserved, and no table or index uses the
  index name ({name}`Catalog.find` ignores triggers);
* the terms and optional filter resolve over that table under the context's DQS setting;
* if the new index is unique, its resolved key has no conflicting pair among that table's
  rows ({name}`LiteralData.uniqueRows`). A nonunique index imposes no row condition.

Use these conditions for a success claim when SQL cannot inspect the index name. -/
def CreateIndexConditions (context : ResolveContext) (database : Database)
    (name : Identifier) (unique : Bool) (tableName : Identifier)
    (terms : List Syntax.OrderTerm) (filter : Option Syntax.Expr) : Prop :=
  ∃ position table keys resolvedFilter,
    database.catalog.findTable tableName = some (position, table) ∧
    reservedName tableName = false ∧ reservedName name = false ∧ database.catalog.find name = none ∧
    indexKeys context.profile.dqsDdl (Scope.single tableName table.columns !table.withoutRowid) table.columns terms = .ok keys ∧
    indexFilter context.profile.dqsDdl (Scope.single tableName table.columns !table.withoutRowid) filter = .ok resolvedFilter ∧
    (unique = true → LiteralData.uniqueRows
      ({ table := position, keys, unique, filter := resolvedFilter } : CatalogIndex).uniqueKey
      (database.rows.getD position []) = true)

/-- A prepare error gives the same error output with any optional clock. -/
private theorem prepareOutput_clock (clock : Option Clock) (index : Nat) (connection : Connection)
    (parameters : List Value) (error : PrepareError) :
    resolvedStepOutput clock index connection parameters (.prepareError error) =
      .error (ExecutionError.prepare error).primaryCode := by
  have clockFree : resolvedStepOutput clock index connection parameters (.prepareError error) =
      resolvedStepOutput none index connection parameters (.prepareError error) := by
    simp [resolvedStepOutput, statementClock, Resolved.Statement.readsClock, Resolved.Statement.clockExpressions]
  rw [clockFree, resolvedStepOutput_prepareError]

/-- For every connection whose row lists align with its catalog, clock, statement index and
bound values, CREATE INDEX gives neither an error nor an ending output exactly when
{name}`CreateIndexConditions` holds. Both prepare errors and model restrictions fail this
success test. Proof sketch: split the table and name lookups and the two expression
resolvers; only their successful branch creates an index, whose output is given by
{name}`resolvedStepOutput_createIndex`. -/
theorem runScriptStep_createIndex_ok_iff (context : ResolveContext) (clock : Option Clock) (index : Nat)
    (connection : Connection) (parameters : List Value) (name tableName : Identifier)
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
      simp [statement_arms, resolveCreateIndex, Connection.resolveState, found, view, restrict,
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
              { table := position, keys := keyTerms, unique, filter := resolvedFilter }
              { shape := table, rows := connection.state.database.rows.getD position [] } aligned
              (connection.state.database.table_of_findTable tableName position table found),
            Output.isError, Output.endsRun]
          cases unique <;>
            cases checked : LiteralData.uniqueRows
              ({ table := position, keys := keyTerms, unique := false, filter := resolvedFilter } : CatalogIndex).uniqueKey
              (connection.state.database.rows.getD position []) <;>
            simp_all [CatalogIndex.uniqueKey]
end Belay.Sqlite.Model
