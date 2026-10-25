import Belay.Sqlite.Model.Resolution.PrepareErrors

set_option doc.verso true

/-! Which errors of a view's query SQLite reports while it reads the columns of the view. -/

namespace Belay.Sqlite.Model

/-- For every error of a {lit}`WITH` definition, whether SQLite reports it while it prepares
the query for the columns of a view. A duplicate name, a cycle, a column list of the wrong
width and a call with arguments are found while the query is prepared. A recursive term that
repeats its reference or holds an aggregate is found only when the statement runs the query. -/
def CommonTableError.seenWhenViewRead : CommonTableError → Bool
  | .duplicate _ | .circular _ | .columns .. | .functionCall _ => true
  | .repeatedTable _ | .repeatedReference _ | .recursiveAggregate => false

/-- For every prepare error of a query, whether SQLite reports it while it reads the columns
of a view that has the query (the pass that {lit}`PRAGMA table_info` and the write of a
view make), as opposed to when a statement runs the view. Name resolution, the width of
compound terms, ORDER BY and GROUP BY terms, join columns, the arguments of a function and
the view cycle are found at once. A subquery of the wrong width, an aggregate in the wrong
place, a table function with too many arguments and the errors of other statements are not
found by that pass, and a model that cannot tell leaves the question open
({lit}`view-body-check`). The answer is false for every error that no view
query can give. Each case was compared with SQLite 3.51.0. -/
def ExprError.seenWhenViewRead : ExprError → Bool
  | .commonTable error => error.seenWhenViewRead
  | .view _ | .noSuchColumn _ | .aggregateInGroupBy | .orderByOutOfRange .. | .groupByOutOfRange ..
  | .wrongArgumentCount _ | .noSuchFunction _ | .likelihoodArgument | .ambiguousColumn _
  | .noSuchSource _ | .joinUsingColumn _ | .naturalJoinCondition | .noTablesSpecified
  | .havingNonAggregate | .compoundColumns _ | .orderByNoMatch _ => true
  | .misuseOfAggregate _ | .hexLiteralTooBig _ | .tooManyTables | .tooManyEachArguments
  | .subqueryColumns _ | .ambiguousUsingReference _ | .raiseOutsideTrigger => false
  | .reservedName _ | .tooManyColumns _ | .duplicateColumn _ | .multiplePrimaryKeys _
  | .defaultNotConstant _ | .tableHasNoColumn .. | .valueCount .. | .valuesForColumns ..
  | .valuesDiffer | .tableMayNotBeAltered _ | .tableMayNotBeIndexed _ | .cannotAddPrimaryKey
  | .primaryKeyMissing _ | .cannotAddUnique | .conflictingAlgorithms | .noSuchCollation _
  | .foreignKeyOneColumn .. | .foreignKeyColumnCount | .unknownForeignKeyColumn _
  | .insertGenerated _ | .updateGenerated _ | .generatedInPrimaryKey | .defaultOnGenerated
  | .errorInGenerated _ | .nondeterministicGenerated | .emptyKeyList | .onlyGeneratedColumns
  | .qualifiedGenerated | .unknownDatatype .. | .missingDatatype .. | .qualifiedIndexTerm
  | .nondeterministicIndex _ | .returningSourceStar | .conflictTargetMismatch
  | .triggerOnSystemTable | .parameterInCheck | .parameterInGenerated | .parameterInIndex _
  | .triggerVariables => false

end Belay.Sqlite.Model
