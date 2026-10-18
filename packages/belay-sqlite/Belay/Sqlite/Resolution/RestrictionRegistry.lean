import Belay.Sqlite.Resolution.Restrictions

set_option doc.verso true

/-! The three registries of model restrictions (ADR 0013, D4). A restriction is
*unsupported* when its SQL is not yet modeled, *undecided* when SQLite's answer depends on
an internal order that the model does not predict, and *unrepresented* when the resolved
form loses a fact that evaluation would need. The third registry is the model's own
limitation and should shrink. -/

namespace Belay.Sqlite

/-- The registry of a model restriction. Use {lean}`RestrictionRegistry.unsupported` for SQL
that is not yet modeled. -/
inductive RestrictionRegistry where
  /-- SQL that the model does not describe yet. -/
  | unsupported
  /-- SQL whose result depends on an internal order of SQLite, such as the order of its
  indexes or of the rows it reads, which the model does not predict. -/
  | undecided
  /-- SQL that the resolved form cannot express: the evaluator could decide it, but the
  resolved statement loses a fact it needs. The reason is in the docstring of each such
  restriction. -/
  | unrepresented
  deriving Repr, DecidableEq

/-- The registry of each restriction kind. The *unrepresented* kinds and their reasons:
* {lit}`rowidName`: a resolved expression has no read of the physical rowid.
* {lit}`duplicateSource`: the names of a query over two sources with the same name are
  not yet resolved as SQLite resolves them (ADR 0013, D5). -/
def RestrictionKind.registry : RestrictionKind → RestrictionRegistry
  | .rowDependentKey | .conflictWithoutTarget | .mixedConflictAlgorithms | .windowedGroupSum
  | .constantFunctionError => .undecided
  | .rowidName | .duplicateSource => .unrepresented
  | .schemaStatement | .engineTable | .rowidColumnName | .createTableConstraints
  | .unmodeledDefault | .createIndexRuns | .addColumnConstraint | .constraintAlgorithmUpdate
  | .replaceDefault | .insertColumnTwice | .updateColumnTwice | .joinOperator | .systemTable
  | .unmodeledFunction | .aggregateInExpression | .aliasInExpression | .groupByTerm | .bareColumn
  | .aggregateOrderBy | .windowValue | .negativeOffset | .tableFunction | .laterTableInOn | .functionJoin
  | .laterSourceInArguments => .unsupported

end Belay.Sqlite
