import Belay.Sqlite.Model.Resolution.StatementPrepareError

set_option doc.verso true

/-! Which errors of a stored view or trigger a rename reports (ADR 0019, D4). SQLite 3.51.0 renames a
name by resolving the definition with its name resolver (the prepare of a SELECT, and the names of the
expressions of a trigger step). It does not check what only the run of a statement checks: the number of
values of an INSERT, the columns of an INSERT list, a function that does not exist, the arguments of a
function, an aggregate in a WHERE, a term of a GROUP BY or ORDER BY of a plain SELECT, or the columns of
an IN subquery. The resolver of the model reports all of these as prepare errors, and then it holds no
complete trace of the names of the definition. A rename of such a definition is a restriction of the
model; a rename reports only the errors below, which the probes of the task show for SQLite 3.51.0. -/

namespace Belay.Sqlite.Model

/-- Whether the rename reports the error of a WITH definition. SQLite reports all of them except a
recursive term with an aggregate, which it accepts until the query runs. -/
def CommonTableError.raisedByRename : CommonTableError → Bool
  | .duplicate _ | .circular _ | .columns .. | .repeatedTable _ | .repeatedReference _ | .functionCall _ => true
  | .recursiveAggregate => false

/-- Whether the rename reports the error of an expression or query inside a definition, as SQLite does. In
plain words: unknown or ambiguous names, bad joins, a HAVING without aggregates, an aggregate in GROUP BY,
the second argument of {lit}`likelihood`, and the shape of a compound SELECT. The terms of ORDER BY and GROUP BY
out of range are checked by SQLite for a compound SELECT only, and the error does not say which, so the
model leaves them to the restriction. -/
def ExprError.raisedByRename : ExprError → Bool
  | .commonTable error => error.raisedByRename
  | .view _ | .noSuchColumn _ | .ambiguousColumn _ | .noSuchSource _ | .joinUsingColumn _
  | .naturalJoinCondition | .ambiguousUsingReference _ | .noTablesSpecified | .havingNonAggregate
  | .aggregateInGroupBy | .likelihoodArgument | .compoundColumns _ | .orderByNoMatch _ => true
  | .reservedName _ | .tooManyColumns _ | .duplicateColumn _ | .multiplePrimaryKeys _ | .defaultNotConstant _
  | .tableHasNoColumn .. | .valueCount .. | .valuesForColumns .. | .valuesDiffer | .tableMayNotBeAltered _
  | .tableMayNotBeIndexed _ | .cannotAddPrimaryKey | .primaryKeyMissing _ | .cannotAddUnique
  | .conflictingAlgorithms | .noSuchCollation _ | .foreignKeyOneColumn .. | .foreignKeyColumnCount
  | .unknownForeignKeyColumn _ | .insertGenerated _ | .updateGenerated _ | .generatedInPrimaryKey
  | .defaultOnGenerated | .errorInGenerated _ | .nondeterministicGenerated | .emptyKeyList | .onlyGeneratedColumns
  | .qualifiedGenerated | .unknownDatatype .. | .missingDatatype .. | .qualifiedIndexTerm
  | .nondeterministicIndex _ | .hexLiteralTooBig _ | .misuseOfAggregate _ | .orderByOutOfRange ..
  | .groupByOutOfRange .. | .wrongArgumentCount _ | .noSuchFunction _ | .tooManyTables | .returningSourceStar
  | .conflictTargetMismatch | .tooManyEachArguments | .subqueryColumns _ | .raiseOutsideTrigger
  | .triggerOnSystemTable | .parameterInCheck | .parameterInGenerated | .parameterInIndex _
  | .triggerVariables => false

/-- Whether the rename reports the prepare error of a definition: a table that does not exist, or an
error of {name}`ExprError.raisedByRename`. -/
def PrepareError.raisedByRename : PrepareError → Bool
  | .noSuchTable _ => true
  | .expression error => error.raisedByRename
  | .viewVariables | .tableExists _ | .viewExists _ | .indexNameUsed _ | .tableNameUsed _ | .indexExists _
  | .noSuchView _ | .useDropTable _ | .useDropView _ | .noSuchIndex _ | .tableMayNotBeDropped _
  | .noSuchReferencedTable _ | .foreignKeyMismatch .. | .noSuchTrigger _ | .triggerExists _ | .viewModify _
  | .viewNotIndexed | .viewAddColumn | .renameTargetTaken _ | .viewNotAltered _ | .viewColumnsNotRenamed _
  | .renameNoSuchColumn _ | .viewTrigger .. | .dependentObject .. | .dropColumn _ => false

end Belay.Sqlite.Model
