import Belay.Sqlite.Model.Shared.Resolved.Restrictions

set_option doc.verso true

/-! The stable ids and the messages of the model restrictions in
{name}`Belay.Sqlite.Model.RestrictionKind`. An id names the restriction in reports and in
{lit}`docs/semantic-subset.md`; it does not change when the message changes. -/

namespace Belay.Sqlite.Model

/-- The stable id of a restriction: lowercase words joined by hyphens. -/
def RestrictionKind.id : RestrictionKind → String
  | .schemaStatement => "schema-statement"
  | .engineTable => "engine-table"
  | .rowidColumnName => "rowid-column-name"
  | .unmodeledDefault => "unmodeled-default"
  | .indexStringTerm => "index-string-term"
  | .indexDateFunction => "index-date-function"
  | .indexJsonFunction => "index-json-function"
  | .unknownCollation => "unknown-collation"
  | .checkFunction => "check-function"
  | .addColumnCheckError => "add-column-check-error"
  | .generatedFunction => "generated-function"
  | .generatedLoop => "generated-loop"
  | .parameterErrorOrder => "parameter-error-order"
  | .upsertGenerated => "upsert-generated"
  | .addColumnGenerated => "add-column-generated"
  | .addColumnStrictType => "add-column-strict-type"
  | .dropConstraintIndex => "drop-constraint-index"
  | .addColumnConstraint => "add-column-constraint"
  | .rowDependentKey => "row-dependent-key"
  | .conflictWithoutTarget => "conflict-without-target"
  | .mixedConflictAlgorithms => "mixed-conflict-algorithms"
  | .constraintAlgorithmUpdate => "constraint-algorithm-update"
  | .replaceDefault => "replace-default"
  | .insertColumnTwice => "insert-column-twice"
  | .updateColumnTwice => "update-column-twice"
  | .rowidName => "rowid-name"
  | .joinOperator => "join-operator"
  | .laterTableInOn => "later-table-in-on"
  | .systemTable => "system-table"
  | .unmodeledFunction => "unmodeled-function"
  | .aggregateInExpression => "aggregate-in-expression"
  | .aliasInExpression => "alias-in-expression"
  | .viewBodyCheck => "view-body-check"
  | .groupByTerm => "group-by-term"
  | .bareColumn => "bare-column"
  | .aggregateOrderBy => "aggregate-order-by"
  | .windowValue => "window-value"
  | .negativeOffset => "negative-offset"
  | .windowedGroupSum => "windowed-group-sum"
  | .constantFunctionError => "constant-function-error"
  | .tableFunction => "table-function"
  | .functionJoin => "function-join"
  | .laterSourceInArguments => "later-source-in-arguments"
  | .jsonSubtype => "json-subtype"
  | .subqueryHere => "subquery-here"
  | .outerAggregate => "outer-aggregate"
  | .subqueryFallibleCall => "subquery-fallible-call"
  | .subqueryReadsTarget => "subquery-reads-target"
  | .distinctOrderBy => "distinct-order-by"
  | .deferredForeignKey => "deferred-foreign-key"
  | .foreignKeyUpsert => "foreign-key-upsert"
  | .raiseForm => "raise-form"
  | .triggerForm => "trigger-form"
  | .triggerWritesOwnTable => "trigger-writes-own-table"
  | .schemaTriggerOrder => "schema-trigger-order"
  | .sourceColumnName => "source-column-name"
  | .recursiveCommonTable => "recursive-common-table"
  | .compoundOrderByTerm => "compound-order-by-term"
  | .foreignKeyMismatchOrder => "foreign-key-mismatch-order"
  | .connectionCounterRead => "connection-counter-read"
  | .nondeterministicErrorOrder => "nondeterministic-error-order"
  | .initialDatabase => "initial-database"
  | .alterRename => "alter-rename"
  | .alterDrop => "alter-drop"

/-- Every restriction, in the order of the registry. -/
def RestrictionKind.all : List RestrictionKind :=
  [.schemaStatement, .engineTable, .rowidColumnName, .unmodeledDefault, .indexStringTerm, .indexDateFunction, .indexJsonFunction, .unknownCollation, .checkFunction, .addColumnCheckError, .generatedFunction, .generatedLoop, .parameterErrorOrder, .upsertGenerated, .addColumnGenerated, .addColumnStrictType, .dropConstraintIndex, .addColumnConstraint, .rowDependentKey, .conflictWithoutTarget, .mixedConflictAlgorithms, .constraintAlgorithmUpdate, .replaceDefault, .insertColumnTwice, .updateColumnTwice, .rowidName, .joinOperator, .laterTableInOn, .systemTable, .unmodeledFunction, .aggregateInExpression, .aliasInExpression, .viewBodyCheck, .groupByTerm, .bareColumn, .aggregateOrderBy, .windowValue, .negativeOffset, .windowedGroupSum, .constantFunctionError, .tableFunction, .functionJoin, .laterSourceInArguments, .jsonSubtype, .subqueryHere, .outerAggregate, .subqueryFallibleCall, .subqueryReadsTarget, .distinctOrderBy, .deferredForeignKey, .foreignKeyUpsert, .raiseForm, .triggerForm, .triggerWritesOwnTable, .schemaTriggerOrder,
    .sourceColumnName, .recursiveCommonTable, .compoundOrderByTerm, .foreignKeyMismatchOrder, .connectionCounterRead, .nondeterministicErrorOrder, .initialDatabase, .alterRename, .alterDrop]

/-- For every restriction, it is in {name}`RestrictionKind.all`. Proof sketch: case
analysis on the restriction. -/
theorem RestrictionKind.mem_all (kind : RestrictionKind) : kind ∈ RestrictionKind.all := by
  cases kind <;> simp [RestrictionKind.all]

-- The ids are distinct.
#guard (RestrictionKind.all.map RestrictionKind.id).eraseDups.length == RestrictionKind.all.length

end Belay.Sqlite.Model
